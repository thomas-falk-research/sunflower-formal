(** * Conjecture.v -- The formal statement of the open Sunflower Conjecture.

    The Sunflower Conjecture (Erdős–Rado, 1960) asks whether [f(n, k)]
    grows at most exponentially in [n]: is there a constant [c_k]
    depending only on [k] such that [f(n, k) ≤ c_k^n] for every [n]?

    The best known upper bound at the time of this writing is
    [f(n, k) ≤ (C k log n)^n] (Alweiss–Lovett–Wu–Zhang 2020 and
    refinements by Rao 2020, Frankston–Kahn–Narayanan–Park 2019, Bell–
    Chueluecha–Warnke 2021, with the constant [C = 64] in Stoeckl's
    presentation). The conjecture would remove the [log n] factor.

    This file pins down what would constitute a Coq proof of the
    conjecture. No proof is claimed here — the conjecture is *open*.
    The matching lower bound from [LowerBound.v] is imported to make
    clear that any [c_k] in a proof must satisfy [c_k ≥ k - 1]. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower ErdosRado LowerBound SpreadReduction.
Import ListNotations.

Set Implicit Arguments.

(** ** The function [f(n, k)]: lower-semi-continuous characterisation

    We work with [UpperBound n k m] as the predicate "every uniform
    distinct family with [≥ m] members contains a [k]-sunflower" and
    [LowerBound n k m] as "exists family with [m] members and no
    [k]-sunflower". A constructive [f n k] is the least [m] such that
    [UpperBound n k m] holds — but we deliberately do not define this
    explicitly, since the conjecture is a quantified upper bound on
    that minimum, not a closed form. *)

(** ** What is proved in this development *)

(** Erdős–Rado upper bound (1960): *)
Theorem theorem_ER_upper :
  forall n k, 1 <= n -> 2 <= k ->
              UpperBound n k (S ((k-1)^n * fact n)).
Proof. apply erdos_rado_upper_bound. Qed.

(** Trivial lower bound (this development): *)
Theorem theorem_trivial_lower :
  forall n k, 1 <= n -> 2 <= k -> LowerBound n k (k - 1).
Proof. apply lower_bound_trivial. Qed.

(** An independent upper bound of the same quality, obtained through
    the *spread framework* of the 2020 proof rather than the 1960
    argument, with the spread lemma replaced by its elementary
    (parameter [n(k-1)+1]) instance. Axiom-free; see
    [SpreadReduction.v]. *)
Theorem theorem_spread_upper :
  forall n k, 2 <= k -> UpperBound n k (S ((n * (k - 1) + 1) ^ n)).
Proof. apply spread_erdos_rado. Qed.

(** ** The conjecture *)

(** The open Erdős–Rado Sunflower Conjecture, stated as a formal Coq
    proposition. A constructive proof of [sunflower_conjecture] in Coq
    would resolve the Erdős–Rado problem (and would, historically,
    have won Erdős's $1000 prize for [k = 3]).

    The conjecture asserts: there exists a sequence [c : nat → nat]
    (depending only on [k]) such that for every [n ≥ 1, k ≥ 2],
    [UpperBound n k ((c k)^n + 1)] holds. The constant function
    [c k = k - 1] would be tight (matching the lower bound), but any
    constant — even [c k = 2^k] or worse — would suffice. *)

Definition sunflower_conjecture : Prop :=
  exists c : nat -> nat,
    (forall k, 2 <= k -> k - 1 <= c k) /\
    (forall n k, 1 <= n -> 2 <= k -> UpperBound n k (S ((c k)^n))).

(** Even the special case [k = 3] is open and was the subject of
    Erdős's specific $1000 prize offer (Erdős 1981). *)

Definition sunflower_conjecture_k_3 : Prop :=
  exists c : nat,
    forall n, 1 <= n -> UpperBound n 3 (S (c ^ n)).

(** [sunflower_conjecture] implies [sunflower_conjecture_k_3]. *)

Theorem k3_corollary :
  sunflower_conjecture -> sunflower_conjecture_k_3.
Proof.
  intros [c [_ Hup]]. exists (c 3).
  intros n Hn. apply Hup; lia.
Qed.

(** ** What this development does NOT do

    The following are *not* theorems of this development; they are
    listed here to make clear what remains:

    - [sunflower_conjecture] itself (the open problem since 1960).

    - The *spread lemma* of Alweiss–Lovett–Wu–Zhang 2020 / Rao 2020:
      "an [r]-spread family of sets of size at most [n] contains [k]
      pairwise disjoint members once [r ≳ k log(nk)]". This is the one
      [Axiom] of the development, stated in [ALWZ.v] with its
      citations. Note what is *not* assumed: the passage from that
      lemma to the bound
      [UpperBound n k (S ((C * k * log (n*k))^n))] is proved, in
      [SpreadReduction.spread_reduction], and the same reduction proves
      the axiom-free [theorem_spread_upper] above. Nothing in
      [ErdosRado.v], [LowerBound.v], [SpreadReduction.v] or this file
      depends on the axiom.

    - Kostochka's [f(n, k) = o(n!)] refinement (1997), again
      unformalised. *)
