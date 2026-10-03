"""Generators for prescribed groups, as lists of images of 0..n-1."""
def perm_from_cycles(n, cycles):
    p = list(range(n))
    for c in cycles:
        for i in range(len(c)): p[c[i]] = c[(i + 1) % len(c)]
    return p
def cyclic(n): return [perm_from_cycles(n, [list(range(n))])]
def affine(p):          # AGL(1,p) on Z_p: x -> x+1, x -> g*x
    g = next(a for a in range(2, p) if all(pow(a, (p - 1) // q, p) != 1 for q in range(2, p) if (p - 1) % q == 0 and all(q % r for r in range(2, q))))
    return [[(x + 1) % p for x in range(p)], [(g * x) % p for x in range(p)]]
def ahs9(off=0, n=9):   # Sym(3) wr Sym(3) on {0..8}+off: triples {0,1,2},{3,4,5},{6,7,8}
    o = off
    return [perm_from_cycles(n, [[o+0, o+1]]), perm_from_cycles(n, [[o+0, o+1, o+2]]),
            perm_from_cycles(n, [[o+0, o+3, o+6], [o+1, o+4, o+7], [o+2, o+5, o+8]]),
            perm_from_cycles(n, [[o+0, o+3], [o+1, o+4], [o+2, o+5]])]
def double_ahs():        # Aut of two disjoint AHS27 on 18 points
    gs = ahs9(0, 18) + ahs9(9, 18)
    gs.append(perm_from_cycles(18, [[i, i + 9] for i in range(9)]))
    return gs
def fmt(gens): return ";".join(" ".join(map(str, g)) for g in gens)
