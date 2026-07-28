#!/usr/bin/env python3
"""Mutation testing for a Coq development.

Mutation testing perturbs a program and asks whether the test suite
notices. For a formalisation the "test suite" is the kernel, and the
thing worth perturbing is not the proofs — a broken proof is caught by
construction — but the *definitions*. A definition can be wrong in a
way no proof can detect: it typechecks, everything downstream still
compiles, and the theorems now say something other than what their
names claim. That is the failure mode this repository has produced
twice.

So: weaken one hypothesis of one definition, rebuild, and see whether
anything breaks.

  * A mutation that is **killed** identifies a hypothesis that is
    load-bearing, and names the file that depends on it.
  * A mutation that **survives** identifies a hypothesis that no
    theorem in the development is sensitive to. Sometimes that is
    benign (the two forms are provably equivalent); sometimes it means
    a condition is decorative, which is exactly the shape of a
    misstatement.

Kills in a proof assistant come in two flavours, and a harness that
cannot tell them apart over-reports. A *semantic* kill means some
theorem is genuinely no longer provable. A *script* kill means only
that a tactic no longer applies -- `apply H` where the goal has become
`<=` rather than `=` -- while every statement remains true. To separate
them, a mutation may declare `repairs`: purely tactical edits that
adapt the proof scripts without touching any statement. If the
development builds again once they are applied, the kill was script
level, and the harness says so rather than crediting the mutation as
evidence that the hypothesis matters.

The manifest in `tools/mutations.toml` records, for each mutation, the
question it asks and the outcome expected. This script checks the
expectations, so the manifest is a regression test on the
load-bearingness of every hypothesis and not merely a report.

Usage:
    tools/mutate.py [--only ID ...] [--jobs N] [--timeout S] [--json PATH]
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import tomllib
from dataclasses import dataclass, asdict
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
MANIFEST = REPO / "tools" / "mutations.toml"

# Copied into each mutant's sandbox. The Rust tree is irrelevant here.
SOURCES = ["coq", "_CoqProject"]

FILE_RE = re.compile(r'File "(?:\./)?([^"]+)", line (\d+)')
COQC_RE = re.compile(r"COQC (\S+)")


@dataclass
class Result:
    id: str
    file: str
    question: str
    expect: str
    control: bool
    outcome: str          # "killed" | "killed-script" | "survived" | "timeout"
    killed_in: str | None  # the .v file whose compilation failed
    detail: str
    seconds: float

    @property
    def ok(self) -> bool:
        return self.outcome == self.expect


def load_manifest() -> list[dict]:
    with MANIFEST.open("rb") as fh:
        return tomllib.load(fh)["mutation"]


def check_manifest(muts: list[dict]) -> None:
    """Every `find` must occur exactly once in its file.

    A manifest that has drifted out of step with the sources would
    otherwise report mutations as run when they were never applied —
    the one failure mode that would make the whole exercise
    meaningless.
    """
    problems = []
    seen_ids = set()
    for m in muts:
        if m["id"] in seen_ids:
            problems.append(f"{m['id']}: duplicate id")
        seen_ids.add(m["id"])
        if m["expect"] not in ("killed", "killed-script", "survived"):
            problems.append(
                f"{m['id']}: expect must be 'killed', 'killed-script' or 'survived'")
        if m["expect"] != "killed" and not m.get("because"):
            problems.append(
                f"{m['id']}: a mutation that is not plainly killed must explain itself "
                f"in `because`")
        if m["expect"] == "killed-script" and not m.get("repairs"):
            problems.append(
                f"{m['id']}: a script-level kill must supply the tactical `repairs` "
                f"that restore the build")
        for edit in [m] + list(m.get("repairs", [])):
            path = REPO / edit["file"]
            if not path.exists():
                problems.append(f"{m['id']}: no such file {edit['file']}")
                continue
            n = path.read_text().count(edit["find"])
            if n != 1:
                problems.append(
                    f"{m['id']}: `find` occurs {n} times in {edit['file']} "
                    f"(must be exactly 1)"
                )
    if problems:
        print("manifest is stale:", file=sys.stderr)
        for p in problems:
            print("  " + p, file=sys.stderr)
        sys.exit(2)


def build(root: Path, timeout: int) -> tuple[bool, str, str | None]:
    """Compile the development in `root`. Returns (ok, detail, failing file)."""
    try:
        subprocess.run(
            ["coq_makefile", "-f", "_CoqProject", "-o", "Makefile.coq"],
            cwd=root, check=True, capture_output=True, timeout=timeout,
        )
    except subprocess.CalledProcessError as e:
        return False, "coq_makefile failed: " + e.stderr.decode()[:200], None

    try:
        proc = subprocess.run(
            ["make", "-f", "Makefile.coq"],
            cwd=root, capture_output=True, timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return False, "timeout", None

    out = (proc.stdout + proc.stderr).decode(errors="replace")
    if proc.returncode == 0:
        return True, "", None

    failing = None
    match = FILE_RE.search(out)
    if match:
        failing = match.group(1)
    else:
        compiled = COQC_RE.findall(out)
        if compiled:
            failing = compiled[-1]

    detail = ""
    for i, line in enumerate(out.splitlines()):
        if line.startswith("Error"):
            detail = " ".join(out.splitlines()[i:i + 3]).strip()
            break
    return False, detail[:300], failing


def sandbox(root: Path) -> None:
    """Lay out a pristine copy of the Coq sources under `root`."""
    for src in SOURCES:
        s = REPO / src
        if s.is_dir():
            shutil.copytree(s, root / src, ignore=shutil.ignore_patterns(
                "*.vo", "*.vok", "*.vos", "*.glob", "*.aux", ".*.aux"))
        else:
            shutil.copy2(s, root / src)


def apply_edit(root: Path, edit: dict) -> None:
    target = root / edit["file"]
    text = target.read_text()
    assert text.count(edit["find"]) == 1, f"{edit['file']}: find is not unique"
    target.write_text(text.replace(edit["find"], edit["replace"]))


def run_one(mut: dict, timeout: int) -> Result:
    start = time.time()
    with tempfile.TemporaryDirectory(prefix="mutant-") as tmp:
        root = Path(tmp)
        sandbox(root)
        apply_edit(root, mut)
        ok, detail, failing = build(root, timeout)

    if detail == "timeout":
        outcome = "timeout"
    elif ok:
        outcome = "survived"
    else:
        outcome = "killed"

    # A declared set of tactical repairs distinguishes a kill that
    # reflects the mathematics from one that reflects only the proof
    # scripts. Statements are never touched by a repair.
    if outcome == "killed" and mut.get("repairs"):
        with tempfile.TemporaryDirectory(prefix="repaired-") as tmp:
            root = Path(tmp)
            sandbox(root)
            apply_edit(root, mut)
            for edit in mut["repairs"]:
                apply_edit(root, edit)
            repaired_ok, repaired_detail, repaired_where = build(root, timeout)
        if repaired_ok:
            outcome = "killed-script"
        else:
            detail = (f"declared repairs did not restore the build "
                      f"({repaired_where}): {repaired_detail}")

    return Result(
        id=mut["id"], file=mut["file"], question=mut["question"],
        expect=mut["expect"], control=bool(mut.get("control", False)),
        outcome=outcome, killed_in=failing,
        detail=detail, seconds=round(time.time() - start, 1),
    )


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--only", nargs="*", metavar="ID", help="run only these mutation ids")
    ap.add_argument("--jobs", type=int, default=min(4, os.cpu_count() or 1))
    ap.add_argument("--timeout", type=int, default=600, help="seconds per mutant build")
    ap.add_argument("--json", type=Path, help="also write results here")
    args = ap.parse_args()

    muts = load_manifest()
    check_manifest(muts)
    if args.only:
        wanted = set(args.only)
        unknown = wanted - {m["id"] for m in muts}
        if unknown:
            print("unknown mutation ids: " + ", ".join(sorted(unknown)), file=sys.stderr)
            return 2
        muts = [m for m in muts if m["id"] in wanted]

    print("=" * 78)
    print("  Mutation testing: does the development notice a weakened definition?")
    print("=" * 78)
    print(f"  {len(muts)} mutations, {args.jobs} parallel builds")
    print()
    print("  baseline ... ", end="", flush=True)
    ok, detail, _ = build_baseline(args.timeout)
    if not ok:
        print("FAILS TO BUILD -- nothing to mutate")
        print("  " + detail)
        return 2
    print("builds clean")
    print()

    results: list[Result] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = {pool.submit(run_one, m, args.timeout): m for m in muts}
        for fut in concurrent.futures.as_completed(futures):
            res = fut.result()
            results.append(res)
            mark = "ok " if res.ok else "BAD"
            print(f"  [{mark}] {res.id:<26} {res.outcome:<13} "
                  f"{(res.killed_in or '-'):<24} {res.seconds:>5.1f}s")

    results.sort(key=lambda r: r.id)
    print()
    print("-" * 78)
    print(f"  {'mutation':<26} {'expected':<13} {'actual':<13} {'first file to break'}")
    print("-" * 78)
    for r in results:
        print(f"  {r.id:<26} {r.expect:<13} {r.outcome:<13} {r.killed_in or '-'}")
    print("-" * 78)

    controls = [r for r in results if r.control]
    survivors = [r for r in results if r.outcome == "survived" and not r.control]
    script_kills = [r for r in results if r.outcome == "killed-script"]
    unexpected = [r for r in results if not r.ok]
    print(f"  killed: {sum(1 for r in results if r.outcome == 'killed')}"
          f"   killed (script only): {len(script_kills)}"
          f"   survived: {len(survivors)}"
          f"   controls passing: {sum(1 for r in controls if r.ok)}/{len(controls)}"
          f"   unexpected: {len(unexpected)}")

    if not controls:
        print()
        print("  WARNING: no control mutation in the manifest. Without one, a "
              "harness that\n  failed to apply its edits would report every "
              "mutation killed and still pass.")

    if survivors:
        print()
        print("  Surviving mutations -- hypotheses no theorem is sensitive to:")
        for r in survivors:
            print(f"    {r.id}: {r.question}")

    if script_kills:
        print()
        print("  Script-level kills -- the tactics noticed, the mathematics did not:")
        for r in script_kills:
            print(f"    {r.id}: {r.question}")

    if unexpected:
        print()
        print("  Mutations whose outcome differs from the manifest:")
        for r in unexpected:
            print(f"    {r.id}: expected {r.expect}, got {r.outcome}")
            if r.detail:
                print(f"      {r.detail}")

    if args.json:
        args.json.write_text(json.dumps([asdict(r) for r in results], indent=2))

    return 1 if unexpected else 0


def build_baseline(timeout: int) -> tuple[bool, str, str | None]:
    with tempfile.TemporaryDirectory(prefix="baseline-") as tmp:
        root = Path(tmp)
        sandbox(root)
        return build(root, timeout)


if __name__ == "__main__":
    sys.exit(main())
