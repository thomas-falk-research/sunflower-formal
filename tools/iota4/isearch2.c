/* isearch.c -- independent isomorph-free exhaustive search for k-uniform,
 * intersecting (optional), 3-sunflower-free families of distinct sets.
 *
 * Written for sunflower-formal as an independent replication of the
 * iota(4) <= 27 claim of arXiv:2609.06175 (Prop. 6.8).  Same framework
 * (McKay canonical augmentation, rows added one at a time, a new row is
 * built from existing points plus fresh ones), different implementation
 * choices at every place a bug could hide:
 *
 *   - candidate rows are enumerated as hitting sets of the existing rows
 *     (each exactly once, by the "first unhit row, smallest chosen point"
 *     rule) instead of all subsets of existing points;
 *   - the canonical deletion row is a row of minimum invariant
 *     inv(row) = (sum of point degrees, sum of squared degrees), ties
 *     broken by the canonical labelling -- so most non-canonical children
 *     are rejected before any nauty call;
 *   - nauty runs on a coloured graph (rows by invariant, columns by
 *     degree); every generator is kept (no cap);
 *   - candidate orbits under Aut(parent) are merged through a hash table.
 *
 * Every accepted node is counted per depth.  Accepted nodes at depth r are
 * in bijection with isomorphism classes of valid r-row families, so the
 * per-depth totals are method-independent invariants that any correct
 * search must reproduce.
 *
 * Usage:
 *   isearch -k 4 -m 28 -I [-C colcap]              whole search
 *   isearch -k 4 -m 28 -I -e 6 -o shards.txt       emit depth-6 frontier
 *   isearch -r shardfile [-l first -n count]       run shards (lines)
 * Exit code 10 = a family of m rows exists (printed), 20 = none.
 */
#include "nauty.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define MAXR 64
#define MAXC 128
#define NMAX (MAXR + MAXC)

typedef unsigned __int128 mask_t;
static int K = 4, M = 28, INTER = 0, COLCAP = MAXC, EMIT = -1;
static long long accepted[MAXR + 1], visited;
static int FOUND;
static mask_t SOL[MAXR];
static FILE *EMIT_OUT;

static inline mask_t mbit(int c) { return ((mask_t)1) << c; }
static inline int popc(mask_t x) {
    return __builtin_popcountll((unsigned long long)x) +
           __builtin_popcountll((unsigned long long)(x >> 64));
}
static inline int lowbit(mask_t x) {
    unsigned long long lo = (unsigned long long)x;
    if (lo) return __builtin_ctzll(lo);
    return 64 + __builtin_ctzll((unsigned long long)(x >> 64));
}

/* ---------- validity of a new row S against rows[0..r-1] ---------- */
/* Pair intersections of the current node's rows, filled by candidates()
   before any valid_new() call on that node. */
static mask_t AB[MAXR][MAXR];

static int valid_new(const mask_t *rows, int r, mask_t S) {
    /* the points of S, in order, index the 16 possible traces a & S */
    int pts[4], np = 0; { mask_t x = S; while (x && np < 4) { int c = lowbit(x); x &= ~mbit(c); pts[np++] = c; } }
    int head[16], next[MAXR];
    for (int t = 0; t < 16; t++) head[t] = -1;
    for (int a = 0; a < r; a++) {
        if (rows[a] == S) return 0;
        mask_t tr = rows[a] & S;
        if (INTER && !tr) return 0;
        int t = 0; for (int j = 0; j < np; j++) if (tr & mbit(pts[j])) t |= 1 << j;
        /* a sunflower {a,b,S} needs a & S == b & S == a & b: only rows with
           the same trace can pair up */
        for (int b = head[t]; b >= 0; b = next[b]) if (AB[a][b] == tr) return 0;
        next[a] = head[t]; head[t] = a;
    }
    return 1;
}

/* ---------- candidate enumeration: hitting sets ---------- */
typedef struct { mask_t *v; size_t n, cap; } cvec;
static void cpush(cvec *c, mask_t S) {
    if (c->n == c->cap) {
        c->cap = c->cap ? 2 * c->cap : 256;
        c->v = realloc(c->v, c->cap * sizeof(mask_t));
        if (!c->v) { fprintf(stderr, "OOM\n"); exit(4); }
    }
    c->v[c->n++] = S;
}

static const mask_t *G_rows; static int G_r, G_C; static cvec *G_out;

/* fill phase: all rows hit; add `need` more points: existing columns > last
   not forbidden, then fresh columns C, C+1, ... */
static void fill(mask_t S, mask_t forb, int need, int from) {
    if (need == 0) { if (valid_new(G_rows, G_r, S)) cpush(G_out, S); return; }
    /* option: all remaining points fresh */
    if (G_C + need <= COLCAP) {
        mask_t T = S;
        for (int t = 0; t < need; t++) T |= mbit(G_C + t);
        if (valid_new(G_rows, G_r, T)) cpush(G_out, T);
    }
    for (int c = from; c < G_C; c++) {
        if ((forb | S) & mbit(c)) continue;
        fill(S | mbit(c), forb, need - 1, c + 1);
    }
}

/* branch phase.  Each hitting set S is produced exactly once: replaying the
   procedure on S, the first row not yet hit is hit by min(S & R) (earlier
   points of R are forbidden, hence not in S), which fixes the path; the
   remaining points of S are added by fill() in increasing order, then a
   block of fresh columns. */
static void branch(mask_t S, mask_t forb, int size) {
    int first = -1;
    for (int a = 0; a < G_r; a++) if (!(G_rows[a] & S)) { first = a; break; }
    if (first < 0) { fill(S, forb, K - size, 0); return; }
    if (size == K) return;
    mask_t R = G_rows[first] & ~forb, done = 0;
    while (R) {
        int c = lowbit(R); R &= ~mbit(c);
        branch(S | mbit(c), forb | done, size + 1);
        done |= mbit(c);
    }
}

/* general enumeration (non-intersecting mode): any K-set of existing
   columns (increasing) followed by a block of fresh columns */
static void gen_all(mask_t S, int size, int from) {
    if (size == K) { if (valid_new(G_rows, G_r, S)) cpush(G_out, S); return; }
    int need = K - size;
    if (G_C + need <= COLCAP) {
        mask_t T = S;
        for (int t = 0; t < need; t++) T |= mbit(G_C + t);
        if (valid_new(G_rows, G_r, T)) cpush(G_out, T);
    }
    for (int c = from; c < G_C; c++) gen_all(S | mbit(c), size + 1, c + 1);
}

static void candidates(const mask_t *rows, int r, int C, cvec *out) {
    G_rows = rows; G_r = r; G_C = C; G_out = out;
    for (int a = 0; a < r; a++) for (int b = 0; b < r; b++) AB[a][b] = rows[a] & rows[b];
    if (r == 0) {
        mask_t S = 0; for (int t = 0; t < K; t++) S |= mbit(t);
        cpush(out, S); return;
    }
    if (INTER) branch(0, 0, 0); else gen_all(0, 0, 0);
}

/* ---------- invariants ---------- */
static void degrees(const mask_t *rows, int r, int C, int *deg) {
    for (int c = 0; c < C; c++) deg[c] = 0;
    for (int a = 0; a < r; a++) { mask_t x = rows[a]; while (x) { int c = lowbit(x); x &= ~mbit(c); deg[c]++; } }
}
static long long row_inv(mask_t row, const int *deg) {
    long long s1 = 0, s2 = 0; mask_t x = row;
    while (x) { int c = lowbit(x); x &= ~mbit(c); s1 += deg[c]; s2 += (long long)deg[c] * deg[c]; }
    return s1 * 100000LL + s2;
}

/* ---------- nauty ---------- */
static int *GENS; static size_t NGENS, GCAP; static int GN;
static void keepgen(int count, int *perm, int *orbits, int numorbits, int stabvertex, int n) {
    (void)count; (void)orbits; (void)numorbits; (void)stabvertex;
    if (NGENS == GCAP) { GCAP = GCAP ? 2 * GCAP : 64; GENS = realloc(GENS, GCAP * NMAX * sizeof(int)); if (!GENS) exit(4); }
    memcpy(GENS + NGENS * NMAX, perm, n * sizeof(int)); NGENS++; GN = n;
}

typedef struct { int v; long long key; } vk;
static int cmp_vk(const void *a, const void *b) {
    long long x = ((const vk *)a)->key, y = ((const vk *)b)->key;
    if (x != y) return x < y ? -1 : 1;
    return ((const vk *)a)->v - ((const vk *)b)->v;
}

/* Runs nauty on the coloured incidence graph.  Rows are vertices 0..r-1,
   columns r..r+C-1.  Colour cells: rows sorted by invariant, then columns
   sorted by degree.  Fills lab (canonical order), orbits, and GENS. */
static void run_nauty(const mask_t *rows, int r, int C, const long long *inv, const int *deg,
                      int *lab, int *orbits) {
    int n = r + C, m = SETWORDSNEEDED(n);
    DYNALLSTAT(graph, g, g_sz); DYNALLSTAT(graph, cg, cg_sz);
    DYNALLOC2(graph, g, g_sz, m, n, "g"); DYNALLOC2(graph, cg, cg_sz, m, n, "cg");
    EMPTYGRAPH(g, m, n);
    for (int a = 0; a < r; a++) { mask_t x = rows[a]; while (x) { int c = lowbit(x); x &= ~mbit(c); ADDONEEDGE(g, a, r + c, m); } }
    vk tmp[NMAX]; int ptn[NMAX];
    for (int a = 0; a < r; a++) { tmp[a].v = a; tmp[a].key = inv[a]; }
    qsort(tmp, r, sizeof(vk), cmp_vk);
    for (int a = 0; a < r; a++) { lab[a] = tmp[a].v; ptn[a] = (a + 1 < r && tmp[a + 1].key == tmp[a].key) ? 1 : 0; }
    for (int c = 0; c < C; c++) { tmp[c].v = r + c; tmp[c].key = deg[c]; }
    qsort(tmp, C, sizeof(vk), cmp_vk);
    for (int c = 0; c < C; c++) { lab[r + c] = tmp[c].v; ptn[r + c] = (c + 1 < C && tmp[c + 1].key == tmp[c].key) ? 1 : 0; }
    static DEFAULTOPTIONS_GRAPH(opt);
    opt.getcanon = TRUE; opt.defaultptn = FALSE; opt.userautomproc = keepgen;
    statsblk st; NGENS = 0;
    densenauty(g, lab, ptn, orbits, &opt, &st, m, n, cg);
    DYNFREE(g, g_sz); DYNFREE(cg, cg_sz);
}

/* ---------- orbit reduction of candidates under Aut(parent) ---------- */
static size_t hslot(mask_t x, size_t hs) {
    unsigned long long h = (unsigned long long)x * 0x9E3779B97F4A7C15ULL ^ (unsigned long long)(x >> 64) * 0xC2B2AE3D27D4EB4FULL;
    return (size_t)(h ^ (h >> 29)) & (hs - 1);
}
static size_t uf_find(size_t *p, size_t x) { while (p[x] != x) { p[x] = p[p[x]]; x = p[x]; } return x; }

/* returns flags keep[i]=1 for one representative per orbit */
static void orbit_reps(const cvec *cand, int r, int C, const int *gens, size_t ngens, char *keep) {
    size_t n = cand->n;
    for (size_t i = 0; i < n; i++) keep[i] = 1;
    if (ngens == 0 || n < 2) return;
    size_t hs = 1; while (hs < 2 * n) hs <<= 1;
    long long *tab = malloc(hs * sizeof(long long)); size_t *par = malloc(n * sizeof(size_t));
    for (size_t i = 0; i < hs; i++) tab[i] = -1;
    for (size_t i = 0; i < n; i++) {
        par[i] = i; size_t h = hslot(cand->v[i], hs);
        while (tab[h] >= 0) h = (h + 1) & (hs - 1);
        tab[h] = (long long)i;
    }
    for (size_t gi = 0; gi < ngens; gi++) {
        const int *pm = gens + gi * NMAX; int pc[MAXC];
        for (int c = 0; c < C; c++) pc[c] = pm[r + c] - r;
        for (size_t i = 0; i < n; i++) {
            mask_t S = cand->v[i], img = 0, x = S;
            while (x) { int c = lowbit(x); x &= ~mbit(c); img |= mbit(c < C ? pc[c] : c); }
            if (img == S) continue;
            size_t h = hslot(img, hs);
            while (tab[h] >= 0 && cand->v[tab[h]] != img) h = (h + 1) & (hs - 1);
            if (tab[h] < 0) { fprintf(stderr, "orbit image missing from candidate list\n"); exit(5); }
            size_t a = uf_find(par, i), b = uf_find(par, (size_t)tab[h]);
            if (a != b) { if (a < b) par[b] = a; else par[a] = b; }
        }
    }
    for (size_t i = 0; i < n; i++) keep[i] = (uf_find(par, i) == i);
    free(tab); free(par);
}

/* ---------- the search ---------- */
static void emit_shard(const mask_t *rows, int r, int C) {
    fprintf(EMIT_OUT, "S %d %d %d %d %d", K, M, INTER, r, C);
    for (int a = 0; a < r; a++) fprintf(EMIT_OUT, " %016llx%016llx",
        (unsigned long long)(rows[a] >> 64), (unsigned long long)rows[a]);
    fputc('\n', EMIT_OUT);
}

/* rows[0..r-1] is an accepted (canonical) node; gens/ngens = Aut(rows) */
static void expand(mask_t *rows, int r, int C, const int *gens, size_t ngens) {
    if (FOUND) return;
    if (r == M) { FOUND = 1; memcpy(SOL, rows, r * sizeof(mask_t)); return; }
    if (EMIT >= 0 && r == EMIT) { emit_shard(rows, r, C); return; }
    cvec cand = {0};
    candidates(rows, r, C, &cand);
    char *keep = malloc(cand.n ? cand.n : 1);
    orbit_reps(&cand, r, C, gens, ngens, keep);
    int deg[MAXC], pdeg[MAXC]; long long inv[MAXR], pinv[MAXR]; int lab[NMAX], orbits[NMAX];
    /* parent degrees and invariants, updated per child incrementally:
       a point of S goes from degree d to d+1, adding 100000 + 2d + 1 */
    degrees(rows, r, C, pdeg);
    for (int a = 0; a < r; a++) pinv[a] = row_inv(rows[a], pdeg);
    for (size_t i = 0; i < cand.n && !FOUND; i++) {
        if (!keep[i]) continue;
        visited++;
        mask_t S = cand.v[i];
        rows[r] = S;
        int C2 = C; { int hi = 127; while (hi >= 0 && !(S & mbit(hi))) hi--; if (hi + 1 > C2) C2 = hi + 1; }
        int r2 = r + 1;
        long long gain[MAXC]; long long invS = 0;
        { mask_t x = S; while (x) { int c = lowbit(x); x &= ~mbit(c); long long d = (c < C ? pdeg[c] : 0) + 1;
            invS += d * 100000LL + d * d; gain[c] = 100000LL + 2 * (d - 1) + 1; } }
        long long mn = invS; int reject = 0, ties = 1;
        for (int a = 0; a < r; a++) {
            long long v = pinv[a]; mask_t x = rows[a] & S;
            while (x) { int c = lowbit(x); x &= ~mbit(c); v += gain[c]; }
            inv[a] = v;
            if (v < invS) { reject = 1; break; }             /* cheap rejection */
            ties += (v == invS);
        }
        if (reject) continue;
        inv[r] = invS;
        for (int c = 0; c < C2; c++) deg[c] = (c < C ? pdeg[c] : 0) + ((S & mbit(c)) ? 1 : 0);
        run_nauty(rows, r2, C2, inv, deg, lab, orbits);
        if (ties > 1) {
            /* canonical deletion row: min invariant, largest canonical position */
            int best = -1, d = -1;
            for (int p = 0; p < r2 + C2; p++) { int v = lab[p]; if (v < r2 && inv[v] == mn) { best = p; d = v; } }
            (void)best;
            if (orbits[d] != orbits[r]) continue;
        }
        accepted[r2]++;
        size_t ng = NGENS; int *gcopy = NULL;
        if (ng) { gcopy = malloc(ng * NMAX * sizeof(int)); memcpy(gcopy, GENS, ng * NMAX * sizeof(int)); }
        expand(rows, r2, C2, gcopy, ng);
        free(gcopy);
    }
    free(keep); free(cand.v);
}

static void run_root(mask_t *rows, int r, int C) {
    /* recompute Aut(rows) for a node given from outside (shard or empty) */
    int deg[MAXC]; long long inv[MAXR]; int lab[NMAX], orbits[NMAX];
    NGENS = 0;
    if (r >= 1) {
        degrees(rows, r, C, deg);
        for (int a = 0; a < r; a++) inv[a] = row_inv(rows[a], deg);
        run_nauty(rows, r, C, inv, deg, lab, orbits);
    }
    size_t ng = NGENS; int *gcopy = NULL;
    if (ng) { gcopy = malloc(ng * NMAX * sizeof(int)); memcpy(gcopy, GENS, ng * NMAX * sizeof(int)); }
    expand(rows, r, C, gcopy, ng);
    free(gcopy);
}

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void report(const char *tag, double t0) {
    printf("%s k=%d m=%d inter=%d colcap=%d: %s visited=%lld time=%.1fs\n", tag, K, M, INTER, COLCAP,
           FOUND ? "FOUND" : "NONE", visited, now() - t0);
    printf("ACCEPTED");
    for (int d = 0; d <= M; d++) printf(" %lld", accepted[d]);
    printf("\n");
    if (FOUND) {
        printf("SOLUTION");
        for (int a = 0; a < M; a++) { printf(" |"); mask_t x = SOL[a]; while (x) { int c = lowbit(x); x &= ~mbit(c); printf(" %d", c); } }
        printf("\n");
    }
    fflush(stdout);
}

int main(int argc, char **argv) {
    int opt, first = 0, count = -1; const char *shards = NULL, *out = NULL;
    while ((opt = getopt(argc, argv, "k:m:IC:e:o:r:l:n:")) != -1) {
        switch (opt) {
        case 'k': K = atoi(optarg); break;
        case 'm': M = atoi(optarg); break;
        case 'I': INTER = 1; break;
        case 'C': COLCAP = atoi(optarg); break;
        case 'e': EMIT = atoi(optarg); break;
        case 'o': out = optarg; break;
        case 'r': shards = optarg; break;
        case 'l': first = atoi(optarg); break;
        case 'n': count = atoi(optarg); break;
        default: return 2;
        }
    }
    if (M > MAXR || COLCAP > MAXC || K < 1) return 2;
    EMIT_OUT = out ? fopen(out, "w") : stdout;
    double t0 = now();
    mask_t rows[MAXR];
    if (!shards) {
        accepted[0] = 1;
        run_root(rows, 0, 0);
        if (EMIT >= 0) { printf("EMITTED depth=%d count=%lld\n", EMIT, accepted[EMIT]); }
        report("RESULT", t0);
        return FOUND ? 10 : 20;
    }
    FILE *f = fopen(shards, "r"); if (!f) { perror(shards); return 2; }
    char line[16384]; int idx = 0, anyfound = 0;
    while (fgets(line, sizeof line, f)) {
        if (line[0] != 'S') continue;
        if (idx++ < first) continue;
        if (count >= 0 && idx > first + count) break;
        int k, mm, inter, r, C, off; char *p = line + 1;
        if (sscanf(p, "%d %d %d %d %d%n", &k, &mm, &inter, &r, &C, &off) != 5) return 2;
        K = k; M = mm; INTER = inter; p += off;
        for (int a = 0; a < r; a++) {
            char hx[33]; int o2; if (sscanf(p, " %32s%n", hx, &o2) != 1) return 2; p += o2;
            char hi[17], lo[17]; memcpy(hi, hx, 16); hi[16] = 0; memcpy(lo, hx + 16, 16); lo[16] = 0;
            rows[a] = ((mask_t)strtoull(hi, NULL, 16) << 64) | strtoull(lo, NULL, 16);
        }
        memset(accepted, 0, sizeof accepted); visited = 0; FOUND = 0; double ts = now();
        run_root(rows, r, C);
        char tag[64]; snprintf(tag, sizeof tag, "SHARD %d", idx - 1);
        report(tag, ts);
        if (FOUND) anyfound = 1;
    }
    return anyfound ? 10 : 20;
}
