#!/usr/bin/env python3
"""Gate the numbers the prose quotes about the development itself.

`tools/statements.txt` stops a *statement* from drifting away from what
was reviewed. This stops the *description* of the development from
drifting away from the development: "builds all 19 Coq files" when there
are 22, "72 audited theorems" when there are 88, "29 mutations" when
there are 32. Every one of those was true when it was written.

Nothing else catches it. The numbers live in prose, in four files, and
each one is a hand-copied consequence of a list somewhere else in the
repository. CI already reports the audited-theorem count in its own
output and gates on it -- that was the fix for the same problem one
level down, where the count used to be hardcoded in the workflow. This
is that fix applied to the documentation.

Each claim names the list it is a count of, so the file that has to
change is never ambiguous. A regex that matches nothing is a failure
too: deleting the sentence must not be a way to pass.

What it does not cover: counts written as words ("the seven mechanisms
added", "one survives"), and any number no entry in CLAIMS names. The
run reports the second case rather than passing over it in silence.

    tools/docnumbers.py            check, exit nonzero on mismatch
    tools/docnumbers.py --list     print the counts and where they are quoted
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def read(rel: str) -> str:
    return (ROOT / rel).read_text(encoding="utf-8")


# ---------------------------------------------------------------------
# The counts, each derived from the list that defines it.
# ---------------------------------------------------------------------


def truths() -> dict[str, tuple[int, str]]:
    """name -> (value, the list it is a count of)."""
    project = read("_CoqProject")
    audited = read("tools/audited.txt")
    manifest = read("tools/mutations.toml")
    ceilings = read("tools/ceiling.py")

    modules = len(re.findall(r"^coq/\S+\.v\s*$", project, re.M))
    thms = len(re.findall(r"^thm \S+", audited, re.M))
    defs = len(re.findall(r"^def \S+", audited, re.M))
    mutations = len(re.findall(r"^\[\[mutation\]\]", manifest, re.M))
    survived = len(re.findall(r'^expect = "survived"', manifest, re.M))
    killed = len(re.findall(r'^expect = "killed"', manifest, re.M))
    controls = len(re.findall(r"^id = \"canary-", manifest, re.M))
    # The route ledger. `routes_losing` is the number of reductions whose
    # own best case is worse than a 1960 bound -- the single most
    # quotable, and most easily stale, fact about where this development
    # has spent its time.
    routes = len(re.findall(r'^        name="', ceilings, re.M))
    routes_losing = len(re.findall(r"^        verdict=LOSES,", ceilings, re.M))

    return {
        "routes": (routes, "tools/ceiling.py (ROUTES entries)"),
        "routes_losing": (routes_losing, "tools/ceiling.py (verdict=LOSES)"),
        "modules": (modules, "_CoqProject"),
        "audited_thms": (thms, "tools/audited.txt (thm lines)"),
        "audited_defs": (defs, "tools/audited.txt (def lines)"),
        "audited_total": (thms + defs, "tools/audited.txt (thm + def lines)"),
        "mutations": (mutations, "tools/mutations.toml"),
        "mutations_killed": (killed, "tools/mutations.toml (expect = killed)"),
        # The genuine survivors are the ones that are not the control.
        "mutations_survived": (
            survived - controls,
            "tools/mutations.toml (expect = survived, minus controls)",
        ),
    }


# ---------------------------------------------------------------------
# Where each count is quoted. One capture group per pattern, and the
# pattern must match at least once.
# ---------------------------------------------------------------------

CLAIMS: list[tuple[str, str, str]] = [
    # `\s+` rather than a literal space: markdown is hard-wrapped, so a
    # reflow moves the line break and would otherwise read as a deleted
    # sentence.
    ("routes", "docs/testing.md", r"of\s+the\s+(\d+)\s+routes\s+this\s+development"),
    ("routes_losing", "docs/testing.md", r"\*\*(\d+)\s+lose\s+to\s+1960"),
    ("modules", "README.md", r"builds all (\d+) Coq files"),
    ("modules", "STATUS.md", r"anywhere\*\* in the (\d+) modules"),
    ("modules", "STATUS.md", r"re-verifies all (\d+) modules"),
    ("audited_thms", "README.md", r"every audited theorem \((\d+) of them"),
    ("audited_thms", "STATUS.md", r"\"Closed\" table \((\d+) of them\)"),
    ("mutations", "README.md", r"Of (\d+) mutations"),
    ("mutations_killed", "README.md", r"Of \d+ mutations, (\d+) are killed outright"),
    ("mutations", "STATUS.md", r"Current mutation results: (\d+) mutations"),
    ("mutations_killed", "STATUS.md", r"declared in `tools/mutations.toml` — (\d+) killed"),
    ("mutations", "docs/testing.md", r"^(\d+) mutations, all with the outcome"),
    ("mutations_killed", "docs/testing.md", r"the manifest declares: (\d+) killed"),
    ("mutations", "docs/roadmap.md", r"mutation testing from (\d+) anecdotes"),
    # The session handover quotes the development's size. It was stale
    # within the same session that wrote it, which is the whole argument
    # for this tool: the count moved when six Examples were audited and
    # the sentence did not.
    ("modules", "docs/roadmap.md", r"development is now (\d+) modules"),
    ("audited_thms", "docs/roadmap.md", r"development is now \d+ modules,\s+(\d+) audited theorems"),
    # Anchored to the handover sentence: earlier sections quote how many
    # definitions a *session* added, which is a different number and a
    # historical record, so a loose pattern would fail on all of them.
    ("audited_defs", "docs/roadmap.md",
     r"development is now \d+ modules,\s+\d+ audited theorems, (\d+) audited"),
]


def check(verbose: bool) -> int:
    table = truths()
    failures: list[str] = []

    for name, path, pattern in CLAIMS:
        expected, source = table[name]
        text = read(path)
        found = re.findall(pattern, text, re.M)
        if not found:
            failures.append(
                f"{path}: the claim about `{name}` is gone\n"
                f"    pattern /{pattern}/ matched nothing.\n"
                f"    Deleting the sentence is not a way to pass; either restore\n"
                f"    it or drop the entry from CLAIMS in tools/docnumbers.py."
            )
            continue
        for got in found:
            if int(got) != expected:
                failures.append(
                    f"{path}: claims {name} = {got}, but {source} says {expected}\n"
                    f"    pattern /{pattern}/"
                )

    if verbose:
        width = max(len(n) for n in table)
        for name, (value, source) in table.items():
            where = sorted({p for n, p, _ in CLAIMS if n == name})
            print(f"  {name:<{width}}  {value:>4}   from {source}")
            for w in where or ["(nowhere -- unchecked)"]:
                print(f"  {'':<{width}}         quoted in {w}")

    # A count with no claim is a count nothing checks. Not a failure --
    # some are here to be read -- but it must not be silent, or the
    # tool's own coverage drifts the way the numbers it watches did.
    unclaimed = sorted(set(table) - {n for n, _, _ in CLAIMS})
    if unclaimed:
        print(f"  note: no prose quotes {', '.join(unclaimed)}")

    if failures:
        print("\nThe prose disagrees with the development:\n", file=sys.stderr)
        for f in failures:
            print(f"  {f}\n", file=sys.stderr)
        print(
            "  Every number above is a count of a list in the repository.\n"
            "  Update the prose (or the list), not this tool.",
            file=sys.stderr,
        )
        return 1

    print(f"  {len(CLAIMS)} quoted numbers match the development")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--list", action="store_true", help="print the counts and where they are quoted"
    )
    args = ap.parse_args()
    return check(args.list)


if __name__ == "__main__":
    sys.exit(main())
