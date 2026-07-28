#!/usr/bin/env python3
"""Statement-hash baselines: snapshot testing for what the development claims.

Both errors this repository has produced were errors of *statement*, not
of proof. The kernel cannot see them, `Print Assumptions` cannot see
them, and `coqchk` cannot see them: a theorem whose hypothesis quietly
weakened still compiles, still reports `Closed under the global
context`, and still re-typechecks. What catches such a change is
noticing that it happened.

That is what this does. Every entry in `tools/audited.txt` is printed,
canonicalised, and hashed into `tools/statements.txt`. CI regenerates
and diffs. A statement that moves without its baseline moving in the
same commit fails the build, so changing what the development claims
becomes a deliberate act with a reviewable diff, rather than a side
effect of editing a proof.

The baseline stores the canonical statement text as well as its hash.
The hash is what CI compares; the text is what a reviewer reads. In a
pull request, "this line of tools/statements.txt changed" is exactly the
question "did this change what we claim?", separated from the several
hundred lines of tactic churn it would otherwise hide in.

    make statements          check against the baseline
    make statements-accept   rewrite the baseline (then commit it)

Two kinds of entry, because for a definition the body *is* the
statement:

    thm NAME    printed with `Check` -- the type, not the proof term
    def NAME    printed with `Print` -- the body, so that a weakened
                `RaoSpread` shows up here even though every theorem
                naming it still compiles unchanged

What this does not catch: a change in a definition that no audited
entry names, and a change that is genuinely equivalent but printed
differently (Coq's printer is the oracle, so a notation change moves
hashes even when nothing else did). It is a tripwire, not a semantics.
Mutation testing in `tools/mutate.py` is the complementary check --
that asks whether a hypothesis is load-bearing, this asks whether it is
still there.
"""

from __future__ import annotations

import argparse
import hashlib
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
AUDITED = ROOT / "tools" / "audited.txt"
BASELINE = ROOT / "tools" / "statements.txt"

# Wide enough that nothing the development states wraps, so a hash never
# moves because a name grew by a character.
PRINTING_WIDTH = 500


def modules() -> list[str]:
    """The library's modules, in dependency order, from _CoqProject."""
    text = (ROOT / "_CoqProject").read_text()
    return [
        pathlib.PurePath(line.strip()).stem
        for line in text.splitlines()
        if re.fullmatch(r"coq/.*\.v", line.strip())
    ]


def entries() -> list[tuple[str, str]]:
    """The audit list as (kind, name) pairs."""
    out = []
    for lineno, line in enumerate(AUDITED.read_text().splitlines(), 1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split()
        if len(parts) != 2 or parts[0] not in ("thm", "def"):
            sys.exit(f"{AUDITED}:{lineno}: expected 'thm NAME' or 'def NAME', got {line!r}")
        out.append((parts[0], parts[1]))
    if not out:
        sys.exit(f"{AUDITED}: no entries")
    return out


def check_audit_covers_the_audit_file(items: list[tuple[str, str]]) -> None:
    """Every top-level claim in coq/Audit.v must be on the list.

    Audit.v exists to be audited: a theorem there that no target names
    is a check nobody runs. This is not a general completeness check --
    the list is curated for the rest of the library -- but for this one
    file the invariant is exact, and it is the guard that catches an
    entry silently dropped from the list.
    """
    listed = {name.split(".", 1)[1] for kind, name in items
              if kind == "thm" and name.startswith("Audit.")}
    declared = set(
        re.findall(r"^(?:Theorem|Corollary|Example)\s+([A-Za-z_0-9']+)",
                   (ROOT / "coq" / "Audit.v").read_text(), re.M)
    )
    missing = sorted(declared - listed)
    if missing:
        sys.exit(
            "coq/Audit.v declares statements that tools/audited.txt does not name:\n"
            + "".join(f"  {m}\n" for m in missing)
            + "Add them as `thm Audit.<name>` and run `make statements-accept`."
        )


def canonicalise(raw: str) -> str:
    """Collapse whitespace so reindentation is not a statement change."""
    return re.sub(r"\s+", " ", raw).strip()


def collect(items: list[tuple[str, str]]) -> dict[str, str]:
    """Print every entry in one coqtop session, split on markers.

    The marker is a term whose printed form we control exactly, which is
    more robust than trying to recognise where one command's output ends
    and the next begins.
    """
    script = [f"From Sunflower Require Import {' '.join(modules())}."]
    script.append(f"Set Printing Width {PRINTING_WIDTH}.")
    for i, (kind, name) in enumerate(items):
        script.append(f"Check (fun MARK_{i} : nat => MARK_{i}).")
        script.append(f"{'Check' if kind == 'thm' else 'Print'} {name}.")
    script.append(f"Check (fun MARK_{len(items)} : nat => MARK_{len(items)}).")

    proc = subprocess.run(
        ["coqtop", "-q", "-Q", str(ROOT / "coq"), "Sunflower"],
        input="\n".join(script) + "\n",
        capture_output=True,
        text=True,
    )
    out = proc.stdout

    # Anything Coq could not find or print is a broken audit list, and
    # silently hashing an error message would be worse than failing.
    for bad in ("Error:", "Syntax error"):
        if bad in out or bad in proc.stderr:
            detail = "\n".join(
                l for l in (out + proc.stderr).splitlines() if bad in l
            )
            sys.exit(f"coqtop reported an error while printing statements:\n{detail}")

    chunks = re.split(r"^fun MARK_\d+ : nat => MARK_\d+\n {5}: nat -> nat$", out, flags=re.M)
    # One leading chunk (the banner) plus one per entry.
    if len(chunks) != len(items) + 2:
        sys.exit(
            f"expected {len(items) + 2} output chunks, got {len(chunks)}; "
            "the marker split is out of step with the audit list"
        )
    return {name: canonicalise(body) for (_, name), body in zip(items, chunks[1:])}


def render(items: list[tuple[str, str]], statements: dict[str, str]) -> str:
    lines = [
        "# Statement baseline -- generated by tools/statements.py, do not hand-edit.",
        "#",
        "# One block per entry in tools/audited.txt: the sha256 of the",
        "# canonicalised statement, then the statement itself. Regenerate with",
        "# `make statements-accept` and commit the result alongside the change",
        "# that moved it. `make statements` fails if these drift apart.",
        "#",
        f"# Coq printing width: {PRINTING_WIDTH}. Produced by Coq 8.18.",
        "",
    ]
    for kind, name in items:
        body = statements[name]
        digest = hashlib.sha256(f"{name}\n{body}".encode()).hexdigest()
        lines.append(f"{digest[:16]}  {kind} {name}")
        lines.append(f"    {body}")
        lines.append("")
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--accept",
        action="store_true",
        help="rewrite the baseline instead of checking against it",
    )
    args = ap.parse_args()

    items = entries()
    check_audit_covers_the_audit_file(items)
    current = render(items, collect(items))

    if args.accept:
        BASELINE.write_text(current)
        print(f"  wrote {BASELINE.relative_to(ROOT)} ({len(items)} entries)")
        return 0

    if not BASELINE.exists():
        sys.exit(
            f"{BASELINE.relative_to(ROOT)} does not exist; "
            "run `make statements-accept` to create it"
        )

    recorded = BASELINE.read_text()
    if recorded == current:
        print(f"  {len(items)} statements match the baseline")
        return 0

    import difflib

    diff = difflib.unified_diff(
        recorded.splitlines(keepends=True),
        current.splitlines(keepends=True),
        fromfile="tools/statements.txt (recorded)",
        tofile="tools/statements.txt (current)",
    )
    sys.stdout.writelines(diff)
    print()
    print("  A statement changed without the baseline changing with it.")
    print("  If the change is intended, run `make statements-accept` and")
    print("  commit tools/statements.txt in the same commit.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
