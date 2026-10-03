/* kmtri.c -- orbit-level sunflower constraints for prescribed-symmetry
 * (Kramer–Mesner) search for large b-uniform 3-sunflower-free families.
 *
 * Input (stdin):  n b ngens, then ngens lines of n integers (a permutation
 *                 of 0..n-1 each).
 * Output (stdout):
 *   O m                       number of orbits of b-subsets
 *   w o size rep_mask         per orbit: its size and a representative
 *   c o1 o2 o3                one line per distinct orbit triple (sorted,
 *                             repeats allowed) realised by a sunflower triple
 * A sunflower triple is three distinct b-sets with equal pairwise
 * intersections K (|K| <= b-1, petals pairwise disjoint).  Every triple is
 * the image under the group of a triple whose first member is an orbit
 * representative, so only those are enumerated.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int n, b, ng, G[64][32];
static int32_t *orb;           /* orbit id per mask (or -1), indexed by mask */
static uint32_t *reps; static int *osz; static int m;

static uint32_t apply(int g, uint32_t x) {
    uint32_t y = 0;
    while (x) { int i = __builtin_ctz(x); x &= x - 1; y |= 1u << G[g][i]; }
    return y;
}

/* hash set of orbit triples */
typedef struct { uint64_t *k; size_t cap, cnt; } hs;
static void hs_init(hs *h) { h->cap = 1 << 20; h->cnt = 0; h->k = calloc(h->cap, 8); }
static void hs_add(hs *h, uint64_t key);
static void hs_grow(hs *h) {
    hs g; g.cap = h->cap * 2; g.cnt = 0; g.k = calloc(g.cap, 8);
    for (size_t i = 0; i < h->cap; i++) if (h->k[i]) hs_add(&g, h->k[i]);
    free(h->k); *h = g;
}
static void hs_add(hs *h, uint64_t key) {
    if (2 * (h->cnt + 1) > h->cap) hs_grow(h);
    size_t i = (key * 0x9E3779B97F4A7C15ULL) >> 20 & (h->cap - 1);
    while (h->k[i]) { if (h->k[i] == key) return; i = (i + 1) & (h->cap - 1); }
    h->k[i] = key; h->cnt++;
}

static hs H;
static void emit(int a, int bb, int c) {
    int t;
    if (a > bb) { t = a; a = bb; bb = t; }
    if (bb > c) { t = bb; bb = c; c = t; }
    if (a > bb) { t = a; a = bb; bb = t; }
    hs_add(&H, ((uint64_t)(a + 1) << 42) | ((uint64_t)(bb + 1) << 21) | (uint64_t)(c + 1));
}

/* enumerate k-subsets of the mask `avail` */
static void subsets(uint32_t avail, int k, uint32_t cur, int from, void (*f)(uint32_t, void *), void *ctx) {
    if (k == 0) { f(cur, ctx); return; }
    for (int i = from; i < n; i++) if (avail >> i & 1) subsets(avail, k - 1, cur | 1u << i, i + 1, f, ctx);
}

typedef struct { uint32_t A, K, PB; int oa; int ps; } ctx_t;
static void pick_c(uint32_t PC, void *vp) {
    ctx_t *c = vp;
    if (PC <= c->PB) return;                       /* unordered {B, C} */
    emit(c->oa, orb[c->K | c->PB], orb[c->K | PC]);
}
static void pick_b(uint32_t PB, void *vp) {
    ctx_t *c = vp; c->PB = PB;
    uint32_t full = (n == 32) ? 0xFFFFFFFFu : ((1u << n) - 1);
    subsets(full & ~c->A & ~PB, c->ps, 0, 0, pick_c, c);
}

int main(void) {
    if (scanf("%d %d %d", &n, &b, &ng) != 3 || n > 26 || b < 2 || ng > 64) return 2;
    for (int g = 0; g < ng; g++) for (int i = 0; i < n; i++) if (scanf("%d", &G[g][i]) != 1) return 2;
    size_t N = (size_t)1 << n;
    orb = malloc(N * sizeof(int32_t)); memset(orb, 0xff, N * sizeof(int32_t));
    reps = malloc(sizeof(uint32_t) * 200000); osz = calloc(200000, sizeof(int));
    uint32_t *queue = malloc(sizeof(uint32_t) * 200000);
    for (uint32_t x = 0; x < N; x++) {
        if (__builtin_popcount(x) != b || orb[x] >= 0) continue;
        int qh = 0, qt = 0; queue[qt++] = x; orb[x] = m;
        while (qh < qt) {
            uint32_t y = queue[qh++]; osz[m]++;
            for (int g = 0; g < ng; g++) { uint32_t z = apply(g, y); if (orb[z] < 0) { orb[z] = m; queue[qt++] = z; } }
        }
        reps[m++] = x;
    }
    printf("O %d\n", m);
    for (int o = 0; o < m; o++) printf("w %d %d %u\n", o, osz[o], reps[o]);
    hs_init(&H);
    uint32_t full = (n == 32) ? 0xFFFFFFFFu : ((1u << n) - 1);
    for (int o = 0; o < m; o++) {
        uint32_t A = reps[o];
        /* every proper subset K of A is a possible core */
        for (uint32_t K = A;; K = (K - 1) & A) {
            if (K != A) {
                ctx_t c = { A, K, 0, o, b - __builtin_popcount(K) };
                subsets(full & ~A, c.ps, 0, 0, pick_b, &c);
            }
            if (K == 0) break;
        }
    }
    for (size_t i = 0; i < H.cap; i++) if (H.k[i]) {
        uint64_t k = H.k[i];
        printf("c %d %d %d\n", (int)((k >> 42) - 1), (int)(((k >> 21) & 0x1FFFFF) - 1), (int)((k & 0x1FFFFF) - 1));
    }
    return 0;
}
