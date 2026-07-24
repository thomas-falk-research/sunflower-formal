(** * Spread.v -- The spread-family framework (ALWZ–Rao–FKNP–BCW).

    The 2020 breakthrough on the Sunflower Conjecture replaced the
    [(k-1)^n · n!] Erdős–Rado bound with [(C k log n)^n] via a
    probabilistic argument over a *spread* distribution.

    This file states the spread-family definition and the spread lemma
    *as Coq axioms with literature citations*. The proof requires a
    real-analysis layer (probabilistic concentration over the uniform
    measure on a finite subset of [N]); formalising it is beyond the
    scope of this development.

    Nothing in [ErdosRado.v], [LowerBound.v], or [Conjecture.v]
    depends on the axioms in this file. The axioms are isolated here
    so an audit can recognise them. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower.
Import ListNotations.

Set Implicit Arguments.

(** ** Spread families *)

(** A family [F] is "[w]-spread" if for every set [T ⊆ N], the number
    of members of [F] containing [T] is at most [|F| / w^{|T|}]. The
    spread lemma says a [w]-spread family with [w ≥ C log n] is
    "covered by" a random subset of [[N]] of size [O(n)] with constant
    probability. *)

Definition w_spread (F : Family) (w : nat) : Prop :=
  forall T : list nat,
    w ^ (length T) *
    length (filter (fun A => forallb (fun x => memb x A) T) F)
    <= length F.

(** [w_spread] is downward-monotone in [w]. *)

Lemma w_spread_mono : forall F w w',
    w_spread F w -> w' <= w -> w_spread F w'.
Proof.
  intros F w w' Hs Hle T.
  specialize (Hs T).
  pose proof (Nat.pow_le_mono_l w' w (length T) Hle) as Hpow.
  nia.
Qed.

(** ** The spread lemma (axiomatised)

    Citation: A. Alweiss, S. Lovett, K. Wu, J. Zhang, "Improved
    bounds for the sunflower lemma", STOC 2020. The version below is
    the standard re-statement (FKNP / Rao / BCW give equivalent
    statements with different constants).

    Statement: there is an absolute constant [C] such that for every
    [n, k, w] with [w >= C * Nat.log2 n + 1], every [w]-spread
    [n]-uniform family [F] has a sub-family that is itself "covered"
    by a random set in a way that produces a [k]-sunflower with
    probability ≥ 1/2.

    We axiomatise the *consequence* used to derive the upper bound:
    every distinct [n]-uniform family of size more than
    [(C * k * log n)^n] contains a [k]-sunflower. The proof of this
    statement *from* the spread lemma is a short reduction
    (Alweiss–Lovett–Wu–Zhang §4); the proof of the spread lemma
    itself is the hard part and is the content of the [ALWZ20]
    paper.

    Once a real-analysis layer is available, this axiom can be
    replaced by a proof. Until then, it lives in this file labelled
    as a named hypothesis with citation. *)

Axiom ALWZ20_spread_bound :
  exists C : nat, 1 <= C /\
    forall n k, 1 <= n -> 2 <= k ->
      UpperBound n k (S ((C * k * Nat.log2_up (S n)) ^ n)).

(** *** Provenance

    This [Axiom] represents Theorem 1.1 of:
    "Improved bounds for the sunflower lemma" (STOC 2020) by Alweiss,
    Lovett, Wu, Zhang; with refinements by Rao (2020), Frankston–Kahn–
    Narayanan–Park (2019), Bell–Chueluecha–Warnke (2021). The constant
    [C = 64] was reached in Stoeckl's presentation of the streamlined
    proof. *)

(** A consequence: [ALWZ20_spread_bound] is *consistent with* the
    Sunflower Conjecture but does *not* imply it (the conjecture
    forbids the [Nat.log2_up (S n)] factor). *)

(** ** Why the spread lemma isn't a proof of the Sunflower Conjecture

    The conjecture asks for [c_k^n] with [c_k] independent of [n].
    [ALWZ20_spread_bound] gives [(C k log n)^n] — the [log n] factor
    is genuine and reflects a step in the proof where a random
    subset must cover a [w]-spread family with [w = Θ(log n)] for
    the probabilistic argument to apply. Removing this [log n] is
    open; see [docs/spread_framework.md] for further discussion. *)
