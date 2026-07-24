# The Sunflower Conjecture: formal problem statement

## Definitions

Let $\mathcal{F}$ be a finite collection of finite sets.

A **$k$-sunflower** in $\mathcal{F}$ is a sub-collection
$\{A_1, A_2, \dots, A_k\}$ of $k$ distinct sets in $\mathcal{F}$ for
which there exists a "core" set $Y$ such that

$$A_i \cap A_j = Y \quad \text{for all } i \neq j.$$

Equivalently, removing the common core $Y$ from each $A_i$ leaves
$k$ pairwise-disjoint "petals" $A_1 \setminus Y, \dots, A_k \setminus
Y$.

Special cases:
- A 2-sunflower is just two distinct sets (the core is their
  intersection).
- A sunflower with empty core is a collection of pairwise-disjoint
  sets.

$\mathcal{F}$ is **$n$-uniform** if $|A| = n$ for every $A \in
\mathcal{F}$, and **distinct** (or "set-distinct") if no two members
of $\mathcal{F}$ are equal as sets.

## The function $f(n, k)$

Define

$$f(n, k) = \min \{m : \text{every distinct } n\text{-uniform family with at least } m \text{ members contains a } k\text{-sunflower}\}.$$

Erdős and Rado (1960) proved this minimum exists for every $n \geq 1,
k \geq 2$, and is bounded above by $(k-1)^n n! + 1$.

## Erdős–Rado bound (1960)

For every $n \geq 1, k \geq 2$:

$$f(n, k) \leq (k-1)^n \, n! + 1.$$

**Proof.** Induct on $n$.

- *Base case* $n = 1$: distinct singletons are pairwise disjoint, so
  any $k$ of them form a $k$-sunflower with empty core. Hence
  $f(1, k) = k$.

- *Inductive step* $n \geq 2$: given $\mathcal{F}$ with
  $|\mathcal{F}| > (k-1)^n n!$. Take a maximal pairwise-disjoint
  sub-collection $\mathcal{D} \subseteq \mathcal{F}$.

  - If $|\mathcal{D}| \geq k$: any $k$ of $\mathcal{D}$ are a
    $k$-sunflower with empty core, done.

  - Otherwise $|\mathcal{D}| \leq k - 1$. Let $X = \bigcup
    \mathcal{D}$, so $|X| \leq (k-1)n$. By maximality, every $A \in
    \mathcal{F}$ meets $X$. By pigeonhole, some element $x \in X$ is
    in at least $|\mathcal{F}| / |X| > (k-1)^{n-1} (n-1)!$ members of
    $\mathcal{F}$. Apply the induction hypothesis to
    $\{A \setminus \{x\} : x \in A \in \mathcal{F}\}$ (an
    $(n-1)$-uniform family) to extract a $k$-sunflower
    $\{B_1, \dots, B_k\}$; lift back to
    $\{B_1 \cup \{x\}, \dots, B_k \cup \{x\}\}$, a $k$-sunflower in
    $\mathcal{F}$.

Coq formalisation: `coq/ErdosRado.v` theorem `erdos_rado_upper_bound`.

## Lower bound: $f(n, k) \geq k$ (this development)

The trivial lower bound: any $k-1$ pairwise-disjoint $n$-uniform
sets form a distinct family of size $k - 1$ with no $k$-sunflower
(since the family has only $k-1$ members). So $f(n, k) \geq k$.

Coq formalisation: `coq/LowerBound.v` theorem `lower_bound_trivial`.

## Standard exponential lower bound: $f(n, k) \geq (k-1)^n + 1$
(*not formalized in this development*)

Construction. Identify $[0, n(k-1))$ with $[n] \times [k-1]$ via
$(i, c) \mapsto i(k-1) + c$. For each function $\phi : [n] \to
[k-1]$, let $A_\phi = \{(i, \phi(i)) : i \in [n]\}$, a set of size
$n$. There are $(k-1)^n$ such functions, giving $(k-1)^n$ distinct
$n$-uniform sets.

Claim: $\mathcal{F} = \{A_\phi : \phi\}$ contains no $k$-sunflower.

Proof. Suppose $\{A_{\phi_1}, \dots, A_{\phi_k}\}$ is a $k$-sunflower
with core $Y$. At each row $i$:
- if any two $\phi_j(i), \phi_{j'}(i)$ agree, then *all* $\phi_\ell(i)$
  agree at that row (else the pairwise intersection structure varies);
- so at every row, either all $\phi_j$ agree or all $\phi_j(i)$ are
  pairwise distinct.

The "pairwise distinct" case forces $k$ distinct values in an
alphabet of size $k - 1$ — pigeonhole forbids this. So at every row
all $\phi_j$ agree, hence all $A_{\phi_j}$ are equal — contradicting
distinctness of a $k$-sunflower's members.

Computational confirmation: `rust/tests/small_cases.rs` exhaustively
verifies this for $(k, n) \in \{(2, 1), (2, 2), (2, 3), (3, 1),
(3, 2), (3, 3), (4, 2)\}$ via the Rust function
`product_family(k-1, n)`.

This bound is *not* formalized in the Coq layer — the
strict-sortedness bookkeeping required for a fully literal proof
becomes lengthy. We instead formalize the weaker
$f(n, k) \geq k$ and document the $(k-1)^n + 1$ bound in this file.

## The open problem

**Sunflower Conjecture (Erdős–Rado 1960):** There exists a constant
$c_k > 0$ depending only on $k$ such that

$$f(n, k) \leq c_k^n \quad \text{for every } n \geq 1.$$

Equivalently: $f(n, k)^{1/n}$ is bounded above by a constant in $n$.

**Erdős's $1000 prize (1981):** Even the special case $k = 3$, where
the conjecture asks for $f(n, 3) \leq c^n$ for some absolute
constant $c$, is open.

The best known upper bound is

$$f(n, k) \leq (C k \log n)^n$$

for some absolute constant $C$ (Alweiss–Lovett–Wu–Zhang 2020, with
refinements by Rao 2020, Frankston–Kahn–Narayanan–Park 2019, and
Bell–Chueluecha–Warnke 2021; constant $C = 64$ in Stoeckl's
presentation). The conjecture asks to remove the $\log n$ factor.

Coq formalisation: `coq/Conjecture.v` definition
`sunflower_conjecture` (statement only; no proof claimed).
