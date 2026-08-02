(** * IntersectingSpread.v -- what ALWZ's Theorem 4.2 buys at k = 3, and why
      it is not the modern bound.

    [IotaRate.conjecture_k_3_iff_iota_exponential] says the sunflower
    conjecture at [k = 3] is *equivalent* to [iota(b) <= C^b]. [ALWZ20]
    §4.2 is about intersecting families inside the spread framework. The
    two look as though they compose into the ALWZ bound at [k = 3] with
    no spread lemma anywhere. **They do not.** This file is what that
    idea is actually worth, checked rather than sketched.

    ** The theorem, quoted

    [ALWZ20] p. 13, rendered, in full:

    >  **Theorem 4.2.** *If `F` is an intersecting `w`-uniform set system,
    >  and for all `T`, `|F_T| <= κ^{-|T|}|F|, then `κ = O(log w)`.*

    introduced on the same page by *"We note the following corollary of
    Theorem 2.5:"*, and proved there in two sentences:

    >  *Proof.* *If `F` is intersecting then it is not `(1/2,1/2)`-satisfying
    >  (apply Lemma 1.6 for `r = 2`). Thus by the improvement of Theorem
    >  2.5 from [19], it cannot be `(C log w)`-spread for a large enough
    >  constant `C`.*

    and noted to be near-sharp on the same page:

    >  *"An example from [16] shows that for `κ = Ω(log w/ log log w)`,
    >  there are intersecting `κ`-spread `w`-uniform set systems, so the
    >  bound in Theorem 4.2 is close to tight."*

    ** The first reason the chain fails: it is not independent

    Theorem 2.5 **is** the spread lemma, and [19] is Rao — that is,
    [ALWZ.Rao20_lemma2], the single axiom of this development. So
    Theorem 4.2 is a two-line corollary of the axiom, not an alternative
    to it. Formalising 4.2 would consume the axiom rather than demote it.
    The chain was worth checking precisely because that was not obvious
    from the statement; it is obvious from the proof, and the proof is
    four lines long on a page the register had already cited for the
    statement alone.

    ** The second reason, which is fatal on its own: the arithmetic

    Suppose 4.2 were independent. Let [F] be intersecting, [b]-uniform,
    sunflower-free, of size [iota(b)]. By 4.2's contrapositive [F] is not
    [κ]-spread for [κ ≈ C log b], so some [T] with [t = |T| >= 1] has
    [|F| < κ^t * deg T F]. The link at [T] is [(b-t)]-uniform and
    sunflower-free ([link_bounded] below), so

    >  iota(b)  <  κ^t * g(b - t).

    [t] is **existential**, so an upper bound has to survive every [t],
    including [t = 1]. And the link of an intersecting family is not
    intersecting ([link_of_intersecting_not_intersecting] below, on the
    triangle), so recovering an intersecting family at the next level
    costs [Intersecting.sunflower_free_star_bound]'s factor [2(b-t)]:

    >  iota(b)  <  κ * g(b-1)  <=  κ * 2(b-1) * iota(b-1).

    That multiplies by [2(b-1)κ] per level, so over [b] levels it is
    [b! (2κ)^b = b! (2C log b)^b]. Erdős–Rado's own recursion
    [g(b) <= 2b g(b-1)] unrolls to [b! 2^b] — which is
    [(k-1)^b b!] at [k = 3], the classical constant — so the chain is
    Erdős–Rado made **worse** by exactly [(C log b)^b].
    [chain_never_beats_erdos_rado] is that comparison, and
    [rust/tests/alwz_chain.rs] evaluates the recursion numerically with
    the maximum over [t] taken honestly at every level: the ratio to
    Erdős–Rado is exactly 1 at every [b] and every [C], because the
    Erdős–Rado clamp is doing all the work.

    ALWZ's own recursion never pays the [2(b-t)] because their spread
    lemma applies to **general** families. Restricting to intersecting
    ones is what makes 4.2 cheap, and it is the same restriction that
    makes it useless as a recursion step. So the sentence
    [docs/roadmap.md] §21 retires is: *"the entire gap between Erdős–Rado
    and ALWZ, at k = 3, is the gap between [intersecting_not_spread_above_uniformity]
    and Theorem 4.2."* It is not. The gap between those two statements is
    a factor [b/log b] per level, and the re-intersection factor [b] per
    level sits on top of both.

    Zero axioms, zero admits — the 4.2 hypothesis is carried as an
    explicit premise, never assumed. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower Spread Reflect Pigeonhole
     ErdosRado SpreadReduction F23 Intersecting IotaRate Compression.
Import ListNotations.

Set Implicit Arguments.

(** ** The link bound at an arbitrary set

    [PureLink.link_at_point_bounded] is the case [T = [x]]. The general
    version costs nothing beyond it and is what the chain needs, since
    4.2's witness is a set of unknown size. *)

Lemma link_bounded :
  forall b Ng (F : Family) (T : list nat),
    Uniform b F -> Distinct F -> ~ ContainsKSunflower 3 F ->
    NoDup T -> GAtMost (b - length T) Ng ->
    deg T F <= Ng.
Proof.
  intros b Ng F T HU HD Hno HndT Hg.
  rewrite <- length_link; apply Hg.
  - exact (@link_uniform b T F HU HndT).
  - exact (@link_distinct T F HD).
  - intro Hc; exact (Hno (@link_sunflower_lift T F 3 Hc)).
Qed.

(** ** The chain step

    The whole of what Theorem 4.2 contributes, with its witness carried
    as a premise rather than extracted. Extracting it from [~ Spread F κ]
    would need [~ (forall T, P T) -> exists T, ~ P T], which is classical;
    this development has no classical axiom and does not want one, and
    every use of 4.2 hands over a witness anyway. *)

Theorem alwz42_chain_step :
  forall b Ng kappa (F : Family) (T : list nat),
    Uniform b F -> Distinct F -> ~ ContainsKSunflower 3 F ->
    NoDup T -> GAtMost (b - length T) Ng ->
    length F < kappa ^ (length T) * deg T F ->
    length F < kappa ^ (length T) * Ng.
Proof.
  intros b Ng kappa F T HU HD Hno HndT Hg Hwit.
  pose proof (@link_bounded b Ng F T HU HD Hno HndT Hg) as Hdeg.
  assert (Hmono : kappa ^ (length T) * deg T F <= kappa ^ (length T) * Ng)
    by (apply Nat.mul_le_mono_l; exact Hdeg).
  lia.
Qed.

(** ** Why the recursion cannot stay inside the intersecting world

    The link of an intersecting sunflower-free family need not be
    intersecting, so [alwz42_chain_step] cannot be iterated against
    [IotaAtMost]: it lands on [GAtMost] and has to be brought back by
    [Intersecting.sunflower_free_star_bound], at a cost of [2(b-t)].

    The witness is the triangle, which is the smallest one. It is
    intersecting — every two edges share a vertex — and sunflower-free,
    since the three pairwise intersections are three *different* points.
    Its link at any vertex is two disjoint singletons.

    [Compression.triangle] is that family and already carries its
    uniformity, distinctness and sunflower-freeness; only the
    intersecting half is new here. *)

Lemma triangle_is_intersecting : Intersecting triangle.
Proof. apply intersectingb_correct; reflexivity. Qed.

Theorem link_of_intersecting_not_intersecting :
  Uniform 2 triangle /\ Distinct triangle /\ Intersecting triangle /\
  ~ ContainsKSunflower 3 triangle /\
  ~ Intersecting (link [0] triangle).
Proof.
  repeat split;
    [ exact triangle_uniform | exact triangle_distinct
    | exact triangle_is_intersecting | exact triangle_no_sunflower |].
  intro Hi.
  apply (Hi [1] [2]).
  - vm_compute; tauto.
  - vm_compute; tauto.
  - intros z Hz1 Hz2; vm_compute in Hz1, Hz2; intuition congruence.
Qed.

(** ** The recursion the chain yields, and the comparison that kills it

    Instantiated at the worst case [t = 1], which is the one the
    existential is free to hand back at every level. [Ng] bounds
    [g(b-1)]. *)

Theorem chain_recursion_at_one :
  forall b Ng kappa N,
    GAtMost (b - 1) Ng ->
    (forall F : Family,
        Uniform b F -> Distinct F -> Intersecting F ->
        ~ ContainsKSunflower 3 F -> F <> [] ->
        exists x : nat, length F < kappa * deg [x] F) ->
    kappa * Ng <= S N ->
    IotaAtMost b N.
Proof.
  intros b Ng kappa N Hg Hwit Harith F HU HD HI Hno.
  destruct F as [|A F']; [simpl; lia|].
  set (G := A :: F').
  destruct (Hwit G HU HD HI Hno ltac:(discriminate)) as [x Hx].
  assert (Hnd : NoDup [x]) by (constructor; [intros [] | constructor]).
  assert (Hlen : length [x] = 1) by reflexivity.
  pose proof (@alwz42_chain_step b Ng kappa G [x] HU HD Hno Hnd
                ltac:(rewrite Hlen; exact Hg)) as Hstep.
  rewrite Hlen in Hstep; simpl Nat.pow in Hstep.
  lia.
Qed.

(** And back to [g] through the star bound, which is the step that costs
    the factor [b] and the step 4.2 cannot avoid. *)

Corollary chain_g_recursion_at_one :
  forall b Ng kappa N,
    1 <= b ->
    GAtMost (b - 1) Ng ->
    (forall F : Family,
        Uniform b F -> Distinct F -> Intersecting F ->
        ~ ContainsKSunflower 3 F -> F <> [] ->
        exists x : nat, length F < kappa * deg [x] F) ->
    kappa * Ng <= S N ->
    GAtMost b (2 * b * N).
Proof.
  intros b Ng kappa N Hb Hg Hwit Harith.
  apply g_le_iota_scaled; [exact Hb|].
  exact (@chain_recursion_at_one b Ng kappa N Hg Hwit Harith).
Qed.

(** The comparison. Erdős–Rado's step is [g(b) <= 2b * g(b-1)]. The step
    above is [g(b) <= 2b * (κ * g(b-1))] — the same recursion multiplied
    by [κ]. Since 4.2's [κ] is [Θ(log b)], and in particular at least 1,
    the chain is never better, and is worse by a factor [κ] per level.

    Stated as arithmetic on the two bounds because that is what it is:
    there is no set-theoretic content left once the recursion is written
    down, and that is the finding. *)

Theorem chain_never_beats_erdos_rado :
  forall b Ng kappa, 1 <= kappa -> 2 * b * Ng <= 2 * b * (kappa * Ng).
Proof. intros; nia. Qed.

Theorem chain_is_worse_by_kappa_per_level :
  forall b Ng kappa, 2 <= kappa -> 1 <= b -> 1 <= Ng ->
    2 * b * Ng < 2 * b * (kappa * Ng).
Proof. intros; nia. Qed.
