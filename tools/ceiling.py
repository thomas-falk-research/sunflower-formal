#!/usr/bin/env python3
"""Cost every route in the development, and gate on the answer.

`docs/reading.md` rule 14 says: *a route has a ceiling, and you compute it
in the first hour, not the sixth session.* Sessions N+5 through N+9 did
correct work inside a reduction whose best possible output was worse than
the 1960 bound, for four sections, because nobody multiplied it out. The
arithmetic was already in the repository — `docs/roadmap.md` §21.5 had
done the identical comparison for a neighbouring route — and was not
carried across.

A rule in a prose file does not survive that. This does: every reduction
in the development declares, here, the best `f(n,3)` bound it can
possibly produce, and the tool instantiates it in exact integer
arithmetic against three bars:

    Erdos-Rado 1960     2^n * n! + 1                    the floor to clear
    the record          Bell-Chueluecha-Warnke 2021     (C * 3 * log2 n)^n
    the conjecture      f(n,3) <= C^n                   the target

Each route also records the verdict it is *expected* to get. A mismatch
fails the run, so a route cannot silently be described as a path to a
record once its ceiling says otherwise, and a route added tomorrow gets
costed the day it is written rather than six sessions later.

** Everything is a base **

Every bound here has the shape `base(n)^n`, so the routes are compared by
their base rather than by their value: Erdos-Rado's base is `~2n/e`, the
record's is `~C log n`, the conjecture's is a constant. That single
column is what rule 14 asks for, and it makes the shape of a route -- and
therefore whether it can possibly reach the target -- visible at a glance.

** The sharp constant for a linear route **

A route with `r*(n,3) <= c*n` yields `f(n,3) <= (c*n)^n + 1`, and
Erdos-Rado is `2^n n! + 1 ~ sqrt(2 pi n) (2n/e)^n`. So `(cn)^n` beats it
exactly when `c < 2/e = 0.7357588...`, and every linear route in this
development has `c >= 1`. `--linear` prints that comparison.

    tools/ceiling.py             the table, and the gate
    tools/ceiling.py --linear    the sharp constant for linear routes
    tools/ceiling.py --list      routes and their declared ceilings
"""

from __future__ import annotations

import argparse
import math
import sys
from fractions import Fraction

# --------------------------------------------------------------------------
# The bars
# --------------------------------------------------------------------------


def factorial(n: int) -> int:
    return math.factorial(n)


def erdos_rado(n: int) -> int:
    """Erdos-Rado 1960, at k = 3: f(n,3) <= 2^n * n! + 1.

    `ErdosRado.erdos_rado_upper_bound` / `ErdosRado_Greedy.er_upper_bound`.
    """
    return 2**n * factorial(n) + 1


# The record is Bell-Chueluecha-Warnke 2021, `Sun(p,k) <= (C p log k)^k`
# with `C >= 4` ([BCW21] Thm 1, read in full; docs/reading.md A6). At
# `p = 3` and uniformity `k = n` that is `(3C log n)^n`. The constant is
# not proved here and the instantiation is illustrative -- what matters
# for costing is that the base grows like `log n`, not like `n`.
BCW_C = 4


def record(n: int) -> int:
    if n < 2:
        return 2
    return (3 * BCW_C * max(1, n.bit_length() - 1)) ** n + 1


# --------------------------------------------------------------------------
# Routes
#
# `ceiling(n)` is the best `f(n,3)` bound the route can produce, ever --
# not what it currently produces. Where a route's parameter is pinned by
# a theorem, the pin is what goes here, and the theorem is named.
# --------------------------------------------------------------------------

LOSES = "linear: loses to Erdos-Rado"
EQUALS_ER = "linear: equals Erdos-Rado"
BEATS_ER = "linear: beats Erdos-Rado"
BEATS_RECORD = "sublinear: record shape"
SETTLES = "constant: settles k=3"

ROUTES: list[dict] = [
    dict(
        name="elementary cover, r = 2n+1",
        carrier="SpreadReduction.elementary_spread_disjoint",
        ceiling=lambda n: (2 * n + 1) ** n + 1,
        status="axiom-free",
        verdict=LOSES,
        note="the general-k cover argument with k=3 substituted",
    ),
    dict(
        name="greedy cover, r = 2n",
        carrier="SpreadThreshold.cover_spread_disjoint",
        ceiling=lambda n: (2 * n) ** n + 1,
        status="axiom-free",
        verdict=LOSES,
        note="Profile.greedy_forces_erdos_rado proves this one cannot win",
    ),
    dict(
        name="quadratic split, r = 1+sqrt(3n^2-4n+3)",
        carrier="SpreadThreshold.quadratic_spread_disjoint",
        ceiling=lambda n: (1 + isqrt_ceil(3 * n * n - 4 * n + 3)) ** n + 1,
        status="axiom-free",
        verdict=LOSES,
        note="best axiom-free bound on r*(n,3); ~1.74n",
    ),
    dict(
        name="matching split, method ceiling r = n+1",
        carrier="SpreadThreshold.split_spread_disjoint (best case)",
        ceiling=lambda n: (n + 1) ** n + 1,
        status="method ceiling",
        verdict=LOSES,
        note="2r^(m-1)+m^2 r^(m-2) <= r^m forces r >= 1+sqrt(1+m^2) > m",
    ),
    dict(
        name="star extremality, pinned at r = n+1",
        carrier="HiltonMilner.star_extremal_route_needs_r_above_n",
        ceiling=lambda n: (n + 1) ** n + 1,
        status="axiom-free (barrier)",
        verdict=LOSES,
        note="HM(m,m) makes the hypothesis false for every r <= n",
    ),
    dict(
        name="tau-indexed bound, r = n",
        carrier="docs/roadmap.md section 21.5",
        ceiling=lambda n: n**n + 1,
        status="method ceiling",
        verdict=LOSES,
        note="the b^b of section 21.5; same wall, same constant",
    ),
    dict(
        name="Erdos-Rado profile via the reduction",
        carrier="Profile.erdos_rado_via_profile",
        ceiling=lambda n: 2**n * factorial(n) + 1,
        status="axiom-free",
        verdict=EQUALS_ER,
        note="equals the 1960 bar exactly: the least greedy-closed profile",
    ),
    dict(
        name="spread lemma, r = alpha*3*log2(3n)",
        carrier="ALWZ.sunflower_bound_from_spread_lemma",
        ceiling=lambda n: (3 * max(1, (3 * n).bit_length())) ** n + 1,
        status="axiom (Rao20_lemma2)",
        verdict=BEATS_RECORD,
        note="alpha=1 is a guess; only the log shape is claimed. The live line",
    ),
    dict(
        name="constant threshold (the conjecture)",
        carrier="Conjecture.spread_conjecture",
        ceiling=lambda n: 8**n + 1,
        status="open",
        verdict=SETTLES,
        note="c(3)=8 as in Sharp.sharp_gives_the_constant; any constant does",
    ),
]


def isqrt_ceil(x: int) -> int:
    r = math.isqrt(x)
    return r if r * r == x else r + 1


# --------------------------------------------------------------------------
# Classification
# --------------------------------------------------------------------------

# The tail on which a verdict is judged. Small n says nothing: every
# route agrees with every other at n = 1.
TAIL = list(range(40, 201, 40))


def base(value: int, n: int) -> Fraction:
    """The `b` in `b^n`, as a rational, so the table compares shapes."""
    if n == 0:
        return Fraction(1)
    # integer n-th root, rounded to two decimals for display only
    lo, hi = 1, 1 << ((value.bit_length() // n) + 2)
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid**n <= value:
            lo = mid
        else:
            hi = mid - 1
    return Fraction(lo)


def growth(route: dict) -> float:
    """The exponent `g` in `base(n) ~ n^g`, measured across the tail.

    Linear routes give `g ~ 1`, logarithmic ones `g ~ 0.1`, a constant
    threshold exactly `0`. Classification is by *shape*, deliberately:
    the constants in the logarithmic rows below (Rao's `alpha`, BCW's
    `C`) are not pinned by this development, so a verdict that depended
    on them would be an artefact of the guess. The shape is what decides
    whether a route can reach the target at all, and the shape is what
    the arithmetic here is entitled to say.
    """
    lo, hi = TAIL[0], TAIL[-1]
    b_lo, b_hi = base(route["ceiling"](lo), lo), base(route["ceiling"](hi), hi)
    if b_hi == b_lo:
        return 0.0
    return math.log(float(b_hi) / float(b_lo)) / math.log(hi / lo)


def classify(route: dict) -> str:
    ceil = route["ceiling"]
    g = growth(route)
    if g == 0.0:
        return SETTLES
    if g < 0.5:
        # sublinear base: the shape of the record and of nothing else here
        return BEATS_RECORD
    # linear base: settled exactly against 1960, no asymptotics involved
    if all(ceil(n) == erdos_rado(n) for n in TAIL):
        return EQUALS_ER
    if all(ceil(n) >= erdos_rado(n) for n in TAIL):
        return LOSES
    return BEATS_ER


# --------------------------------------------------------------------------
# Output
# --------------------------------------------------------------------------


def table() -> list[str]:
    ns = [50, 100, 200]
    out = [
        "",
        "  Route ceilings: the best f(n,3) bound each reduction can produce,",
        "  as the base b in b^n. Erdos-Rado's base is ~2n/e; the record's is",
        f"  ~{3 * BCW_C} log2 n; the conjecture's is a constant. `g` is the measured",
        "  exponent in base(n) ~ n^g: 1 is linear, 0 is a constant threshold.",
        "",
        f"  {'route':<44} {'base(50)':>9} {'base(100)':>10} {'base(200)':>10} {'g':>5}  verdict",
        f"  {'-' * 44} {'-' * 9:>9} {'-' * 10:>10} {'-' * 10:>10} {'-' * 5:>5}  {'-' * 26}",
    ]
    for r in ROUTES:
        bs = [base(r["ceiling"](n), n) for n in ns]
        out.append(
            f"  {r['name']:<44} {int(bs[0]):>9} {int(bs[1]):>10} {int(bs[2]):>10}"
            f" {growth(r):>5.2f}  {classify(r)}"
        )
    out += [
        "",
        f"  {'Erdos-Rado 1960 (the bar)':<44} "
        f"{int(base(erdos_rado(50), 50)):>9} {int(base(erdos_rado(100), 100)):>10} "
        f"{int(base(erdos_rado(200), 200)):>10}  1.00  --",
        f"  {'BCW 2021 (the record)':<44} "
        f"{int(base(record(50), 50)):>9} {int(base(record(100), 100)):>10} "
        f"{int(base(record(200), 200)):>10}  0.24  --",
        "",
    ]
    return out


def linear_note() -> list[str]:
    """The sharp constant: `(cn)^n` beats `2^n n!` exactly when c < 2/e."""
    out = [
        "",
        "  A route with r*(n,3) <= c*n yields f(n,3) <= (c n)^n + 1.",
        "  Erdos-Rado is 2^n n! + 1 ~ sqrt(2 pi n) (2n/e)^n, so (c n)^n beats it",
        "  exactly when c < 2/e = 0.7357588823...",
        "",
        f"  {'c':>8}  {'n=200':>10} {'n=2000':>10} {'n=20000':>10}   asymptotic",
        f"  {'-' * 8}  {'-' * 10:>10} {'-' * 10:>10} {'-' * 10:>10}   {'-' * 10}",
    ]
    ns = [200, 2000, 20000]
    for num, den in [(1, 2), (7, 10), (73, 100), (7357, 10000), (74, 100), (1, 1),
                     (174, 100), (2, 1)]:
        c = Fraction(num, den)
        cells = []
        for n in ns:
            cells.append("beats" if (c * n) ** n < erdos_rado(n) else "loses")
        asym = "beats" if c < Fraction(7357588823, 10000000000) else "loses"
        out.append(
            f"  {float(c):>8.4f}  {cells[0]:>10} {cells[1]:>10} {cells[2]:>10}"
            f"   {asym}"
        )
    out += [
        "",
        "  The finite-n columns lag the asymptotic one: the sqrt(2 pi n) in",
        "  Stirling keeps c slightly above 2/e winning until n is large. The",
        "  threshold that matters for a route is the asymptotic column.",
        "",
        "  Every linear route in this development has c >= 1. The smallest is",
        "  the matching-split method ceiling at c = 1, and 1 > 2/e, so no",
        "  refinement of it can beat 1960. Profile.greedy_forces_erdos_rado is",
        "  the same statement for the greedy step, proved exactly rather than",
        "  asymptotically.",
        "",
    ]
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--linear", action="store_true", help="the sharp constant 2/e")
    ap.add_argument("--list", action="store_true", help="routes and carriers")
    args = ap.parse_args()

    if args.list:
        for r in ROUTES:
            print(f"{r['name']}\n    carrier: {r['carrier']}\n"
                  f"    status : {r['status']}\n    note   : {r['note']}")
        return 0

    print("\n".join(table()))
    if args.linear:
        print("\n".join(linear_note()))

    bad = [(r["name"], r["verdict"], classify(r)) for r in ROUTES
           if classify(r) != r["verdict"]]
    if bad:
        print("  MISMATCH between the declared verdict and the arithmetic:")
        for name, declared, got in bad:
            print(f"    {name}\n      declared: {declared}\n      computed: {got}")
        print("\n  Either the ceiling is wrong or the description is. Rule 14.")
        return 1

    n_record = sum(1 for r in ROUTES if classify(r) in (BEATS_RECORD, SETTLES))
    print(f"  {len(ROUTES)} routes costed; {n_record} can reach the record or better.")
    print("  All declared verdicts match the arithmetic.\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
