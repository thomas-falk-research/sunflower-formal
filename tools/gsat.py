#!/usr/bin/env python3
"""Independent SAT check of g(m,n): the largest distinct m-uniform
3-sunflower-free family on n points.

Exists as a cross-check on rust/examples/g_small.rs, which computes the
same numbers by branch and bound. Different algorithm, different
implementation, external solver -- the point is that a bug would have to
occur twice, in the same direction, to survive.

The cardinality constraint is a Sinz sequential counter. It is validated
against brute force on every n <= 7 before use, because the first version
of this file had a too-weak counter and reported a family that did not
exist; see docs/papers/nine-points.md section 11.

    python3 tools/gsat.py            # validate, then g(3,8), g(3,6), g(2,6)
    python3 tools/gsat.py 3 9        # a single value
"""
import itertools
import os
import subprocess
import sys
import tempfile


def atmost(k, lits, nxt):
    """Sinz sequential counter for sum(lits) <= k. Returns (clauses, next)."""
    n = len(lits)
    if k < 0:
        return [[nxt], [-nxt]], nxt + 1          # unsatisfiable
    if k >= n:
        return [], nxt
    if k == 0:
        return [[-l] for l in lits], nxt
    s = {}
    for i in range(1, n):
        for j in range(1, k + 1):
            s[(i, j)] = nxt
            nxt += 1
    c = [[-lits[0], s[(1, 1)]]]
    c += [[-s[(1, j)]] for j in range(2, k + 1)]
    for i in range(2, n):
        c.append([-lits[i - 1], s[(i, 1)]])
        c.append([-s[(i - 1, 1)], s[(i, 1)]])
        for j in range(2, k + 1):
            c.append([-lits[i - 1], -s[(i - 1, j - 1)], s[(i, j)]])
            c.append([-s[(i - 1, j)], s[(i, j)]])
        c.append([-lits[i - 1], -s[(i - 1, k)]])
    c.append([-lits[n - 1], -s[(n - 1, k)]])
    return c, nxt


def atleast(k, lits, nxt):
    """sum(lits) >= k, as sum(negated) <= len - k."""
    return atmost(len(lits) - k, [-l for l in lits], nxt)


def solve(nvars, clauses):
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
        f.write(f"p cnf {nvars} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(map(str, c)) + " 0\n")
        path = f.name
    try:
        r = subprocess.run(["cadical", path], capture_output=True, text=True)
    finally:
        os.unlink(path)
    if "s UNSATISFIABLE" in r.stdout:
        return None
    model = set()
    for line in r.stdout.splitlines():
        if line.startswith("v "):
            model.update(v for v in map(int, line[2:].split()) if v > 0)
    return model


def validate_counter():
    """The counter must be right before it is trusted. Exhaustive, small."""
    for n in range(1, 8):
        lits = list(range(1, n + 1))
        for k in range(0, n + 3):
            cls, nv = atleast(k, lits, n + 1)
            m = solve(max(nv - 1, n), cls)
            assert (m is not None) == (k <= n), f"counter wrong at n={n} k={k}"
            if m is not None:
                got = sum(1 for l in lits if l in m)
                assert got >= k, f"counter admitted {got} < {k} at n={n}"
    return True


def is_sunflower(a, b, c):
    ab = a & b
    return ab == (a & c) and ab == (b & c)


def g(m, n):
    """Largest sunflower-free family, by walking the threshold upward."""
    sets = [frozenset(c) for c in itertools.combinations(range(n), m)]
    var = {s: i + 1 for i, s in enumerate(sets)}
    base = [
        [-var[a], -var[b], -var[c]]
        for a, b, c in itertools.combinations(sets, 3)
        if is_sunflower(a, b, c)
    ]
    best = 0
    while True:
        extra, nv = atleast(best + 1, [var[s] for s in sets], len(sets) + 1)
        model = solve(max(nv - 1, len(sets)), base + extra)
        if model is None:
            return best
        chosen = [s for s in sets if var[s] in model]
        # Never trust a model: re-verify it as a family in its own right.
        assert len(chosen) >= best + 1, f"model has {len(chosen)}, wanted {best+1}"
        assert len({frozenset(s) for s in chosen}) == len(chosen), "model has repeats"
        assert all(len(s) == m for s in chosen), "model is not uniform"
        assert not any(
            is_sunflower(a, b, c) for a, b, c in itertools.combinations(chosen, 3)
        ), "model contains a sunflower"
        best = len(chosen)


if __name__ == "__main__":
    print("validating the cardinality counter on all n <= 7 ...", end=" ", flush=True)
    validate_counter()
    print("ok")
    pairs = [(int(sys.argv[1]), int(sys.argv[2]))] if len(sys.argv) == 3 else [
        (3, 8), (3, 6), (2, 6)
    ]
    for m, n in pairs:
        print(f"  g({m},{n}) = {g(m, n)}")
