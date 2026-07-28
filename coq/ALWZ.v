(** * ALWZ.v -- The 2020 spread lemma, as the development's only axiom.

    This file contains the single [Axiom] of the whole development, and
    derives the modern sunflower bound from it.

    *** What is assumed, and what is proved

    Previous revisions of this development axiomatised the *conclusion*
    of the 2020 papers directly:

    << f(n,k) <= (C k log n)^n + 1 >>

    That is a large thing to assume: it is the headline theorem, and
    everything about how it follows from the spread machinery was
    outside the kernel's view.

    What is assumed here instead is Rao's Lemma 2 — the genuinely hard
    half of the argument. In the notation of "Coding for sunflowers"
    (sets of size [k], sunflower size [p], spread parameter
    [r(p,k) = α p log(pk)]):

    << Lemma 2. If a sequence of more than r(p,k)^k sets of size k is
       r(p,k)-spread, then the sequence must contain p disjoint sets. >>

    where [r]-spread is Rao's absolute notion: every nonempty [Z] is
    contained in at most [r^{k-|Z|}] members. This is a self-contained
    combinatorial statement about finite families; it mentions no
    sunflowers and no bounds.

    The step from it to the sunflower bound — Rao's Theorem 1, the
    ALWZ §4 "from spread to sunflowers" reduction — is now *proved*, in
    [SpreadReduction.spread_reduction], and is checked by the kernel.

    Translating notation: Rao's [k] (the set size) is our [n], Rao's
    [p] (the sunflower size) is our [k]. The axiom below is stated with
    our names, and is relativised to all set sizes [m ≤ n] at once,
    which is what the induction of the reduction consumes; since the
    threshold [α k log(k m)] is monotone in [m], a single [r] works for
    every level.

    Two respects in which the axiom below is *weaker* than the
    published lemma, deliberately:

    - it is stated only for families of sets of one fixed size [m],
      whereas the source allows sets of size at most [m];
    - [Nat.log2_up (S (k * n))] over-estimates [log(kn)], so more is
      demanded of [r] than the source demands.

    *** Provenance

    - R. Alweiss, S. Lovett, K. Wu, J. Zhang, "Improved bounds for the
      sunflower lemma", STOC 2020 — the original spread lemma, proved
      by a probabilistic argument over a random subset of the ground
      set.
    - A. Rao, "Coding for sunflowers", Discrete Analysis 2020:2 — the
      statement assumed here (his Lemma 2, with
      [r(p,k) = α p log(pk)]), proved by an elementary encoding /
      counting argument rather than a probabilistic one.
    - K. Frankston, J. Kahn, B. Narayanan, J. Park, "Thresholds versus
      fractional expectation-thresholds", Ann. of Math. 194 (2021) —
      the same lemma in the "fractional expectation-threshold"
      formulation.
    - T. Bell, S. Chueluecha, L. Warnke, "Note on sunflowers",
      Discrete Math. 344 (2021) — sharpens the threshold to
      [Θ(k log n)], which by the same reduction gives the often quoted
      [(C k log n)^n].

    Rao's proof is elementary — injections between finite sets and
    binomial estimates, no measure theory — so it is a realistic
    formalisation target; discharging this axiom is the natural next
    step for this development, and is the reason the axiom has been
    reformulated as the spread lemma rather than the final bound. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower Spread Reflect SpreadReduction.
Import ListNotations.

Set Implicit Arguments.

(** ** The axiom: Rao 2020, Lemma 2 *)

Axiom Rao20_lemma2 :
  exists alpha : nat, 1 <= alpha /\
    forall n k r : nat,
      1 <= n -> 2 <= k ->
      alpha * k * Nat.log2_up (S (k * n)) <= r ->
      SpreadYieldsDisjoint n k r.

(** ** Rao 2020, Theorem 1, derived *)

Lemma log2_up_pos : forall a, 2 <= a -> 1 <= Nat.log2_up a.
Proof.
  intros a Ha.
  destruct (Nat.log2_up a) as [|u] eqn:E; [|lia].
  exfalso. apply Nat.log2_up_null in E. lia.
Qed.

Theorem sunflower_bound_from_spread_lemma :
  exists alpha : nat, 1 <= alpha /\
    forall n k : nat, 1 <= n -> 2 <= k ->
      UpperBound n k (S ((alpha * k * Nat.log2_up (S (k * n))) ^ n)).
Proof.
  destruct Rao20_lemma2 as [alpha [Ha Hlem]].
  exists alpha; split; [exact Ha|].
  intros n k Hn Hk.
  set (r := alpha * k * Nat.log2_up (S (k * n))).
  assert (Hlog : 1 <= Nat.log2_up (S (k * n))).
  { apply log2_up_pos. nia. }
  assert (Hr : 1 <= r) by (unfold r; nia).
  apply (@spread_reduction_top n k r Hk Hr).
  apply (Hlem n k r Hn Hk). unfold r; lia.
Qed.

(** *** What an improved spread lemma would buy

    The Bell–Chueluecha–Warnke refinement gives the spread lemma with
    threshold [Θ(k log n)] instead of [Θ(k log(nk))]; substituting it
    into the very same [spread_reduction_top] yields the frequently
    quoted [(C k log n)^n]. Nothing in the reduction changes — only the
    assumed threshold does. That modularity is what the restructuring
    buys: improvements to the spread lemma propagate to the sunflower
    bound without touching any proof here. *)

(** ** Non-vacuity guards

    An axiom is only as good as the satisfiability of its hypotheses.
    Three guards:

    - [SpreadReduction.elementary_spread_disjoint] proves
      [SpreadYieldsDisjoint n k r] outright for [r = n(k-1)+1], so the
      *shape* of the assumed statement is known to be provable (with a
      much worse parameter);
    - [rao_spread_singletons] exhibits a concrete family satisfying
      both hypotheses of the axiom, certified by [vm_compute] through
      the decision procedure;
    - and it is genuinely spread in the fractional (ALWZ / FKNP) sense
      too, via [Spread.RaoSpread_Spread].

    These guards matter here: an earlier definition of spreadness in
    this development *was* degenerate — see
    [Spread.w_spread_legacy_degenerate], which proves that no family
    with a nonempty member satisfies it. *)

Definition four_singletons : Family := [[0]; [1]; [2]; [3]].

Lemma NoDup_singleton : forall a : nat, NoDup [a].
Proof. intros a; constructor; [simpl; tauto | constructor]. Qed.

Lemma singleton_SetEq : forall a b : nat, SetEq [a] [b] -> a = b.
Proof.
  intros a b [Hs _]. specialize (Hs a (or_introl eq_refl)).
  destruct Hs as [E | []]; symmetry; exact E.
Qed.

Lemma four_singletons_NoDup : Forall (fun A : list nat => NoDup A) four_singletons.
Proof.
  apply Forall_forall; intros A HA; simpl in HA.
  destruct HA as [<- | [<- | [<- | [<- | []]]]]; apply NoDup_singleton.
Qed.

Lemma four_singletons_uniform : Uniform 1 four_singletons.
Proof.
  unfold Uniform; apply Forall_forall; intros A HA; simpl in HA.
  destruct HA as [<- | [<- | [<- | [<- | []]]]];
    split; [reflexivity | apply NoDup_singleton | reflexivity
           | apply NoDup_singleton | reflexivity | apply NoDup_singleton
           | reflexivity | apply NoDup_singleton].
Qed.

Lemma four_singletons_distinct : Distinct four_singletons.
Proof.
  unfold Distinct, four_singletons.
  constructor;
    [ intros B HB Hseq; simpl in HB;
      destruct HB as [<- | [<- | [<- | []]]];
      apply singleton_SetEq in Hseq; discriminate |].
  constructor;
    [ intros B HB Hseq; simpl in HB;
      destruct HB as [<- | [<- | []]];
      apply singleton_SetEq in Hseq; discriminate |].
  constructor;
    [ intros B HB Hseq; simpl in HB;
      destruct HB as [<- | []];
      apply singleton_SetEq in Hseq; discriminate |].
  constructor; [intros B HB; inversion HB | constructor].
Qed.

Example rao_spread_singletons : RaoSpread 1 four_singletons 3.
Proof.
  apply (@rao_witness_none 1 four_singletons 3).
  - apply four_singletons_NoDup.
  - vm_compute; reflexivity.
Qed.

Example rao_spread_singletons_big : 3 ^ 1 < length four_singletons.
Proof. vm_compute; lia. Qed.

Example spread_singletons : Spread four_singletons 3.
Proof.
  apply (@RaoSpread_Spread 1 four_singletons 3).
  - apply four_singletons_uniform.
  - apply rao_spread_singletons.
  - apply rao_spread_singletons_big.
Qed.

(** And the elementary spread lemma applies to it: with [n = 1],
    [k = 3] the threshold [n(k-1)+1] is exactly [3], so
    [four_singletons] must contain 3 pairwise disjoint members — as of
    course it does. This closes the loop: hypotheses satisfiable,
    conclusion true, on a concrete instance. *)

Example elementary_applies_to_singletons :
  exists S : list (list nat),
    incl S four_singletons /\ NoDup S /\ length S = 3 /\ PairwiseDisjoint S.
Proof.
  pose proof (elementary_spread_disjoint (n := 1) (k := 3) ltac:(lia)) as H.
  unfold SpreadYieldsDisjoint in H.
  apply (H 1 four_singletons); try lia.
  - apply four_singletons_uniform.
  - apply four_singletons_distinct.
  - apply rao_spread_singletons_big.
  - apply rao_spread_singletons.
Qed.

(** ** Non-vacuity *inside the gap*

    The guard above runs at [n = 1], [k = 3], [r = 3] — parameters
    where [SpreadReduction.spread_disjoint_above_elementary] also
    applies, so it says nothing about the range the axiom exists for.
    The point of the axiom is precisely the range where the elementary
    lemma is silent.

    Take [n = 20], [k = 3], and the most demanding admissible
    [alpha = 1]. The axiom's threshold is
    [1 * 3 * log2_up (S (3 * 20)) = 18], while the elementary lemma
    needs [r > n(k-1) = 40]. So [SpreadYieldsDisjoint 20 3 18] is an
    instance this development cannot prove: it is exactly what is being
    assumed, and not a restatement of something already available.

    Its hypotheses are satisfiable. The circulant graph on 37 vertices
    with connection set [{1,...,9}] is simple and 18-regular, so as a
    2-uniform family it is 18-spread in Rao's absolute sense, and its
    333 edges clear [18^2 = 324].

    And where the assumed instance's prediction *can* be checked
    independently, it holds. [spread_disjoint_above_elementary] at
    [n = 2] covers families of uniformity at most 2 for any [r > 4], so
    the three pairwise disjoint edges the axiom promises for this
    family are produced below without using the axiom.

    None of this verifies Rao's Lemma 2, and nothing here could. What
    it rules out is the failure mode that actually matters for an
    axiom — asserting something with no models — at a parameter where
    the assumption is doing real work. The exhaustive version of the
    same check, over every family on small ground sets, is in
    [rust/tests/spread_axiom.rs]; the definition-level checks it
    belongs to are described in [docs/testing.md]. *)

(** The circulant graph on [n] vertices with connection set
    [{1, ..., d}]: the edges [{i, i+j mod n}]. Simple and [2d]-regular
    when [2d < n], hence [r]-spread for any [r >= 2d]. *)

Definition circulant (n d : nat) : Family :=
  flat_map (fun i => map (fun j => [i; Nat.modulo (i + S j) n]) (seq 0 d))
           (seq 0 n).

(** The threshold the axiom demands, as a function of its parameters. *)

Definition rao_threshold (alpha n k : nat) : nat :=
  alpha * k * Nat.log2_up (S (k * n)).

Definition C37 : Family := circulant 37 9.

Example threshold_is_inside_the_gap :
  rao_threshold 1 20 3 = 18 /\ rao_threshold 1 20 3 < 20 * (3 - 1).
Proof. split; vm_compute; [reflexivity | lia]. Qed.

Lemma C37_uniform : Uniform 2 C37.
Proof. apply uniformb_correct; vm_compute; reflexivity. Qed.

Lemma C37_distinct : Distinct C37.
Proof. apply distinctb_correct; vm_compute; reflexivity. Qed.

Lemma C37_big : rao_threshold 1 20 3 ^ 2 < length C37.
Proof. vm_compute; lia. Qed.

Lemma C37_rao_spread : RaoSpread 2 C37 (rao_threshold 1 20 3).
Proof.
  apply (@rao_witness_none 2 C37 (rao_threshold 1 20 3)).
  - apply (@Uniform_NoDup 2 C37 C37_uniform).
  - vm_compute; reflexivity.
Qed.

Theorem axiom_hypotheses_satisfiable_in_the_gap :
  Uniform 2 C37 /\
  Distinct C37 /\
  rao_threshold 1 20 3 ^ 2 < length C37 /\
  RaoSpread 2 C37 (rao_threshold 1 20 3) /\
  (exists S : list (list nat),
      incl S C37 /\ NoDup S /\ length S = 3 /\ PairwiseDisjoint S).
Proof.
  split; [exact C37_uniform |].
  split; [exact C37_distinct |].
  split; [exact C37_big |].
  split; [exact C37_rao_spread |].
  apply (@spread_disjoint_above_elementary 2 3 (rao_threshold 1 20 3)
           ltac:(lia) ltac:(vm_compute; lia) 2 C37);
    [lia | lia | exact C37_uniform | exact C37_distinct
     | exact C37_big | exact C37_rao_spread].
Qed.
