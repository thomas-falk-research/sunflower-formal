#!/usr/bin/env python3
"""Gate a pull request body against the repository it describes.

`tools/statements.py` stops a *theorem* from drifting away from what was
reviewed. `tools/docnumbers.py` stops the *prose* from drifting away from
the lists it counts. This stops a *pull request* from drifting away from
the branch it is about, which is the one place a human forms an opinion
of the work and the one place nothing was checked.

It parses the ```toml block in `.github/pull_request_template.md`'s
"Machine-readable state" section and enforces four things:

1. **The counts are right.** Modules, audited theorems and definitions,
   mutations, killed mutations, Rust suites, and the set of declared
   axioms -- each against the list it is a count of. Same failure this
   repository has already had twice in prose.

2. **Every claim's evidence exists.** `evidence` must resolve to an
   audited Coq name (`tools/audited.txt`), a Rust `#[test]` function
   (`rust/tests/*.rs`), a mutation id (`tools/mutations.toml`), or a
   path in the repository. A pull request that cites a theorem by a name
   nothing carries is the specific failure this catches, and it is not
   hypothetical: names get renamed during a rebase.

3. **A claim of new mathematics carries a search.** `docs/reading.md`
   rule 17: *"'New' without a search is 'new to this repository', and it
   gets written that way."* Here that is mechanical -- `novelty =
   "new-mathematics"` with an empty or "none run" `search` fails.

4. **"What did not move" is present and non-empty.** The section exists
   because a branch that cannot say what it failed to move has not been
   read carefully by its author. Presence is checkable; honesty is not.

What it cannot check: whether the prose is true, whether a claim's
sentence matches the theorem it cites, or whether the verdict is honest.
Those remain the author's, exactly as `statements.py` checks that a
statement did not move rather than that it is the right statement.

    tools/prcheck.py --body FILE     check a body, exit nonzero on failure
    tools/prcheck.py --template      check the template itself parses
"""

from __future__ import annotations

import argparse
import re
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

VALID_KIND = {"theorem", "measurement", "refutation", "correction", "tooling"}
VALID_NOVELTY = {"new-mathematics", "new-to-this-development", "not-new"}
VALID_GATE = {"pass", "fail", "not-run"}
NO_SEARCH = {"", "none", "none run", "none-run", "not run", "n/a", "-"}


# ---------------------------------------------------------------------
# The repository's own truth, recomputed rather than trusted
# ---------------------------------------------------------------------


def read(rel: str) -> str:
    return (ROOT / rel).read_text(encoding="utf-8")


def truths() -> dict[str, object]:
    coqproject = read("_CoqProject")
    audited = read("tools/audited.txt")
    manifest = read("tools/mutations.toml")

    axioms: set[str] = set()
    for vfile in sorted((ROOT / "coq").glob("*.v")):
        module = vfile.stem
        for name in re.findall(r"^Axiom\s+([A-Za-z_][A-Za-z_0-9']*)", vfile.read_text(), re.M):
            axioms.add(f"Sunflower.{module}.{name}")

    return {
        "modules": len(re.findall(r"^coq/.*\.v\s*$", coqproject, re.M)),
        "audited_theorems": len(re.findall(r"^thm \S+", audited, re.M)),
        "audited_definitions": len(re.findall(r"^def \S+", audited, re.M)),
        "mutations": len(re.findall(r"^\[\[mutation\]\]", manifest, re.M)),
        "mutations_killed": len(re.findall(r'^expect = "killed"', manifest, re.M)),
        "rust_suites": len(list((ROOT / "rust" / "tests").glob("*.rs"))),
        "axioms": sorted(axioms),
    }


def audited_names() -> set[str]:
    return set(re.findall(r"^(?:thm|def) (\S+)", read("tools/audited.txt"), re.M))


def rust_test_names() -> set[str]:
    names: set[str] = set()
    for path in (ROOT / "rust" / "tests").glob("*.rs"):
        text = path.read_text(encoding="utf-8")
        for m in re.finditer(r"#\[test\]\s*(?:#\[[^\]]*\]\s*)*fn\s+([A-Za-z_][A-Za-z_0-9]*)", text):
            names.add(m.group(1))
    return names


def mutation_ids() -> set[str]:
    return set(re.findall(r'^id = "([^"]+)"', read("tools/mutations.toml"), re.M))


# ---------------------------------------------------------------------
# Parsing the body
# ---------------------------------------------------------------------


def strip_comments(body: str) -> str:
    """HTML comments are template scaffolding, not content."""
    return re.sub(r"<!--.*?-->", "", body, flags=re.S)


def extract_toml(body: str) -> tuple[dict, list[str]]:
    blocks = re.findall(r"```toml\s*\n(.*?)```", body, re.S)
    if not blocks:
        return {}, ["no ```toml block found; the machine-readable state is required"]
    if len(blocks) > 1:
        return {}, [f"{len(blocks)} ```toml blocks found; exactly one is expected"]
    try:
        return tomllib.loads(blocks[0]), []
    except tomllib.TOMLDecodeError as e:
        return {}, [f"the ```toml block does not parse: {e}"]


def section_body(body: str, heading: str) -> str | None:
    """The prose under `## heading`, comments removed."""
    pattern = rf"^##\s+{re.escape(heading)}\s*$(.*?)(?=^##\s|\Z)"
    m = re.search(pattern, body, re.S | re.M)
    if m is None:
        return None
    return strip_comments(m.group(1)).strip()


# ---------------------------------------------------------------------
# The checks
# ---------------------------------------------------------------------


def check(body: str, template_mode: bool) -> list[str]:
    problems: list[str] = []
    data, errs = extract_toml(body)
    problems += errs
    if not data:
        return problems

    facts = truths()

    # 1. counts
    state = data.get("state")
    if not isinstance(state, dict):
        problems.append("[state] table missing")
    elif not template_mode:
        for key, actual in facts.items():
            if key not in state:
                problems.append(f"[state] is missing `{key}` (the repository says {actual!r})")
                continue
            claimed = state[key]
            if key == "axioms":
                if sorted(claimed) != actual:
                    problems.append(
                        f"[state] axioms = {claimed!r}, but coq/ declares {actual!r}"
                    )
            elif claimed != actual:
                problems.append(f"[state] {key} = {claimed}, but the repository says {actual}")
        for key in state:
            if key not in facts:
                problems.append(f"[state] has an unknown key `{key}`")

    # 2. gates
    gates = data.get("gates")
    if not isinstance(gates, dict):
        problems.append("[gates] table missing")
    else:
        for name, value in gates.items():
            if value not in VALID_GATE:
                problems.append(
                    f"[gates] {name} = {value!r}; expected one of {sorted(VALID_GATE)}"
                )
        if not template_mode:
            failed = [n for n, v in gates.items() if v == "fail"]
            if failed:
                problems.append(
                    "gates reported as failing: " + ", ".join(sorted(failed))
                    + " -- a pull request may declare a failing gate, but it must be"
                    + " explained in the prose, so this is reported rather than ignored"
                )

    # 3. claims
    claims = data.get("claim", [])
    if not isinstance(claims, list):
        problems.append("[[claim]] entries malformed")
        claims = []
    if not template_mode and not claims:
        problems.append("no [[claim]] entries; a pull request asserts at least one thing")

    names, tests, muts = audited_names(), rust_test_names(), mutation_ids()
    seen_ids: set[str] = set()
    for i, c in enumerate(claims):
        where = c.get("id", f"claim #{i + 1}")
        for field in ("id", "statement", "kind", "evidence", "novelty"):
            if not c.get(field):
                problems.append(f"{where}: missing `{field}`")
        if c.get("id") in seen_ids:
            problems.append(f"{where}: duplicate id")
        seen_ids.add(c.get("id"))

        if c.get("kind") and c["kind"] not in VALID_KIND:
            problems.append(f"{where}: kind = {c['kind']!r}; expected one of {sorted(VALID_KIND)}")
        if c.get("novelty") and c["novelty"] not in VALID_NOVELTY:
            problems.append(
                f"{where}: novelty = {c['novelty']!r}; expected one of {sorted(VALID_NOVELTY)}"
            )

        ev = c.get("evidence")
        if ev and not resolves(ev, names, tests, muts):
            problems.append(
                f"{where}: evidence {ev!r} resolves to nothing -- it is not an audited "
                f"Coq name, a Rust #[test], a mutation id, or a path in the repository"
            )

        if c.get("novelty") == "new-mathematics":
            search = str(c.get("search", "")).strip().lower()
            if search in NO_SEARCH:
                problems.append(
                    f"{where}: novelty = \"new-mathematics\" with search = "
                    f"{c.get('search')!r}. docs/reading.md rule 17: \"new\" without a "
                    f"search is \"new to this repository\", and it gets written that way"
                )

    # 4. the mandatory negative space
    if not template_mode:
        did_not = section_body(body, "What did not move")
        if did_not is None:
            problems.append('the "## What did not move" section is missing')
        elif len(did_not) < 40:
            problems.append(
                '"## What did not move" is present but empty or near-empty; '
                "name the bounds, exact values and ledger rows that are unchanged"
            )

    return problems


def resolves(ev: str, names: set[str], tests: set[str], muts: set[str]) -> bool:
    if ev in names or ev in tests or ev in muts:
        return True
    if (ROOT / ev).exists():
        return True
    # a bare Coq name, given without its module
    return any(n.split(".")[-1] == ev for n in names)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--body", type=Path, help="file containing the pull request body")
    ap.add_argument("--template", action="store_true",
                    help="check .github/pull_request_template.md itself parses")
    args = ap.parse_args()

    if args.template:
        body = read(".github/pull_request_template.md")
        label = ".github/pull_request_template.md"
    elif args.body:
        body = args.body.read_text(encoding="utf-8")
        label = str(args.body)
    else:
        ap.error("one of --body or --template is required")

    problems = check(body, template_mode=args.template)
    if problems:
        print(f"{label}: the pull request does not describe this repository:",
              file=sys.stderr)
        for p in problems:
            print(f"  {p}", file=sys.stderr)
        print("\n  See .github/pull_request_template.md and tools/prcheck.py.",
              file=sys.stderr)
        return 1

    facts = truths()
    print(f"{label}: checks out.")
    print(f"  {facts['modules']} modules, {facts['audited_theorems']} audited theorems, "
          f"{facts['mutations']} mutations, {facts['rust_suites']} Rust suites")
    print(f"  axioms declared in coq/: {', '.join(facts['axioms']) or 'none'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
