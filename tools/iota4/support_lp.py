#!/usr/bin/env python3
"""The best support bound for a 28-member intersecting 3-sunflower-free
4-uniform family that local counting alone can give (roadmap §60.8).

LP over member degree-types, using only facts proved or cited here:
  * sum_{x in A} (deg x - 1) = sum_{B != A} |A ∩ B| >= 27 for every member A
  * deg x <= 20 (the link at x is 3-uniform sunflower-free; g(3) = 20)
  * at most 2 points of degree 1 in a support-minimal family (§60.4 merge)
  * 28 members, degree sum 112.
Result: 34.37, attained by 27 members of degree type (2,2,7,20) -- a
one-hub family that global structure rules out but no local count does."""
import itertools
from scipy.optimize import linprog
D = 20
types = [t for t in itertools.combinations_with_replacement(range(1, D + 1), 4)
         if sum(d - 1 for d in t) >= 27]
ny = len(types)
Aeq = [[1] * ny + [0] * D]; beq = [28]
for t in range(1, D + 1):
    row = [tp.count(t) for tp in types] + [0] * D; row[ny + t - 1] = -t
    Aeq.append(row); beq.append(0)
r = linprog([0] * ny + [-1] * D, A_ub=[[0] * ny + [1] + [0] * (D - 1)], b_ub=[2],
            A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * (ny + D), method="highs")
print(f"LP maximum support: {-r.fun:.4f}")
