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

    What is assumed here instead is the *spread lemma* — the genuinely
    hard, analytic half of the argument:

    << an r-spread family of sets of size at most n contains k pairwise
       disjoint members, as soon as r >= C k log(nk) >>

    This is a self-contained combinatorial statement about finite
    families; it mentions no sunflowers and no bounds. The step from it
    to the sunflower bound — the ALWZ §4 / Rao "from spread to
    sunflowers" reduction — is now *proved*, in
    [SpreadReduction.spread_reduction], and is checked by the kernel.

    *** Provenance of the assumed statement

    - R. Alweiss, S. Lovett, K. Wu, J. Zhang, "Improved bounds for the
      sunflower lemma", STOC 2020 — the original spread lemma, proved
      by a probabilistic argument over a random subset of the ground
      set.
    - A. Rao, "Coding for sunflowers", Discrete Analysis 2020:2 — an
      elementary encoding/counting proof of the same lemma, and the
      form of the threshold used here, [r = Θ(k log(nk))].
    - K. Frankston, J. Kahn, B. Narayanan, J. Park, "Thresholds versus
      fractional expectation-thresholds", Ann. of Math. 194 (2021) —
      the same lemma in the "fractional expectation-threshold"
      formulation.
    - T. Bell, S. Chueluecha, L. Warnke, "Note on sunflowers",
      Discrete Math. 344 (2021) — sharpens the threshold to
      [r = Θ(k log n)], which by the same reduction gives the often
      quoted [(C k log n)^n].

    Rao's proof is elementary — injections between finite sets and
    binomial estimates, no measure theory — so it is a realistic
    formalisation target; discharging this axiom is the natural next
    step for this development, and is the reason the axiom has been
    reformulated as the spread lemma rather than the final bound. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower Spread SpreadReduction.
Import ListNotations.

Set Implicit Arguments.

(** ** The axiom *)

Axiom Rao20_spread_lemma :
  exists C : nat, 1 <= C /\
    forall n k r : nat,
      1 <= n -> 2 <= k ->
      C * k * Nat.log2_up (S (n * k)) <= r ->
      SpreadYieldsDisjoint n k r.

(** ** The modern upper bound, derived *)

Lemma log2_up_pos : forall a, 2 <= a -> 1 <= Nat.log2_up a.
Proof.
  intros a Ha.
  destruct (Nat.log2_up a) as [|u] eqn:E; [|lia].
  exfalso. apply Nat.log2_up_null in E. lia.
Qed.

Theorem sunflower_bound_from_spread_lemma :
  exists C : nat, 1 <= C /\
    forall n k : nat, 1 <= n -> 2 <= k ->
      UpperBound n k (S ((C * k * Nat.log2_up (S (n * k))) ^ n)).
Proof.
  destruct Rao20_spread_lemma as [C [HC Hlem]].
  exists C; split; [exact HC|].
  intros n k Hn Hk.
  set (r := C * k * Nat.log2_up (S (n * k))).
  assert (Hlog : 1 <= Nat.log2_up (S (n * k))).
  { apply log2_up_pos. nia. }
  assert (Hr : 1 <= r) by (unfold r; nia).
  apply (@spread_reduction_top n k r Hk Hr).
  apply (Hlem n k r Hn Hk). unfold r; lia.
Qed.

(** *** Relation to the previously assumed statement

    The bound above is Rao's [(C k log(nk))^n]. The Bell–Chueluecha–
    Warnke refinement gives the spread lemma with threshold
    [Θ(k log n)]; substituting it into the very same
    [spread_reduction_top] yields the frequently quoted
    [(C k log n)^n]. Nothing in the reduction changes — only the
    assumed threshold does. This is exactly the modularity the
    restructuring buys: improvements to the spread lemma propagate to
    the sunflower bound without touching any proof here. *)

(** ** Sanity checks on the assumed statement

    An axiom is only as good as its non-vacuity. Two guards:

    - [SpreadReduction.elementary_spread_disjoint] proves
      [SpreadYieldsDisjoint n k r] outright for [r = n(k-1)+1], so the
      shape of the assumed statement is known to be satisfiable (with a
      worse parameter);
    - [Spread.spread_singletons] below exhibits a concrete spread
      family, so [Spread] itself is not degenerate. This guard matters:
      an earlier definition of spreadness in this development *was*
      degenerate, see [Spread.w_spread_legacy_degenerate]. *)

Example spread_singletons : Spread [[0]; [1]; [2]] 3.
Proof.
  apply (@spread_witness_none [[0]; [1]; [2]] 3).
  - repeat (constructor; simpl; try tauto).
  - vm_compute; reflexivity.
Qed.

Example not_spread_singletons_4 : ~ Spread [[0]; [1]; [2]] 4.
Proof.
  intros Hsp.
  assert (Hnd : NoDup [0]) by (constructor; [simpl; tauto | constructor]).
  specialize (Hsp [0] Hnd).
  vm_compute in Hsp. lia.
Qed.
