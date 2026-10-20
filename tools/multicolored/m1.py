#!/usr/bin/env python3
"""M(D,1) >= 3 ?  docs/roadmap.md section 75.2 (F4).

S_D = {(a,b,c) in [D]^3 : a = b = c, or a, b, c pairwise distinct}. An induced
3-matching is three triples t_i in S_D with (x_i, y_j, z_l) not in S_D whenever
(i,j,l) is not constant. A 3-matching uses at most 9 letters and S_D depends only
on the equality pattern, so D = 9 decides every D >= 9. The first triple is taken
to be (0,0,0) or (0,1,2): one permutation of [D], applied to x, y and z alike,
maps S_D onto itself. Usage: python3 -I tools/multicolored/m1.py D
"""
import itertools, sys
D = int(sys.argv[1])
G = {t for t in itertools.product(range(D), repeat=3) if len(set(t)) in (1, 3)}
L = sorted(G)
def ok(c):
    m = len(c)
    return all((c[i][0], c[j][1], c[l][2]) not in G
               for i, j, l in itertools.product(range(m), repeat=3) if not i == j == l)
# symmetry: WLOG first triple is (0,0,0) or (0,1,2)
firsts = [(0, 0, 0), (0, 1, 2)]
found = None; pairs = 0
for a in firsts:
    comp = [b for b in L if b != a and ok([a, b])]
    pairs += len(comp)
    for b, c in itertools.combinations(comp, 2):
        if ok([a, b, c]): found = (a, b, c); break
    if found: break
print("D", D, "compatible partners of the two first-triple types:", pairs, "3-matching:", found)
