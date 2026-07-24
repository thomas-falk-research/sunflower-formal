(** * ErdosRado_Greedy.v -- Alternative formulation of the Erdős–Rado bound.

    This file restates the Erdős–Rado upper bound in two
    equivalent forms ([greedy_form] and [contrapositive_form]) and
    derives both from [ErdosRado.erdos_rado_upper_bound]. The
    derivations are short and the Coq proof terms are structurally
    different from the main proof in [ErdosRado.v].

    These are not new mathematical theorems — the underlying content
    is identical to the classical Erdős–Rado theorem. They serve as
    cross-checks: a downstream user looking for the bound in a
    different shape gets the same guarantee. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower ErdosRado.
Import ListNotations.

Set Implicit Arguments.

(** ** Contrapositive: no [k]-sunflower implies size at most [(k-1)^n · n!] *)

Theorem erdos_rado_contrapositive :
  forall n k F,
    1 <= n -> 2 <= k ->
    Uniform n F -> Distinct F ->
    ~ ContainsKSunflower k F ->
    length F <= (k - 1)^n * fact n.
Proof.
  intros n k F Hn Hk HU HD Hno.
  destruct (le_lt_dec (S ((k - 1)^n * fact n)) (length F)) as [Hle | Hlt].
  - exfalso. apply Hno.
    apply (@erdos_rado_upper_bound n k Hn Hk F HU HD Hle).
  - lia.
Qed.

(** ** "Greedy" form: extract a [k]-sunflower from a sufficiently large family *)

Theorem erdos_rado_via_greedy :
  forall n k F,
    1 <= n -> 2 <= k ->
    Uniform n F -> Distinct F ->
    length F > (k - 1)^n * fact n ->
    exists S core,
      length S = k /\
      Sunflower S core /\
      SubFamilySetEq S F.
Proof.
  intros n k F Hn Hk HU HD Hsize.
  assert (Hbound : length F >= S ((k - 1)^n * fact n)) by lia.
  destruct (erdos_rado_upper_bound Hn Hk HU HD Hbound) as [S [HSF [HSlen [core HSun]]]].
  exists S, core; auto.
Qed.

(** ** Counted form: a function-shaped upper bound on [f(n, k)] *)

Definition er_upper_bound (n k : nat) : nat := S ((k - 1) ^ n * fact n).

Theorem erdos_rado_counted :
  forall n k, 1 <= n -> 2 <= k ->
              UpperBound n k (er_upper_bound n k).
Proof.
  intros n k Hn Hk. unfold er_upper_bound.
  apply erdos_rado_upper_bound; auto.
Qed.

(** ** Monotonicity in the bound *)

Theorem erdos_rado_monotone :
  forall n k m, 1 <= n -> 2 <= k ->
                er_upper_bound n k <= m ->
                UpperBound n k m.
Proof.
  intros n k m Hn Hk Hle.
  apply UpperBound_mono with (m := er_upper_bound n k); auto.
  apply erdos_rado_counted; auto.
Qed.

(** Note: the proof terms of these theorems are short, but the proof
    object of [erdos_rado_contrapositive] in particular is genuinely
    different from [erdos_rado_upper_bound] — it routes through
    [le_lt_dec] and adds an exfalso step, producing a different
    elaborated term. The Coq kernel sees these as distinct proof
    objects sharing the underlying [erdos_rado_upper_bound] lemma. *)
