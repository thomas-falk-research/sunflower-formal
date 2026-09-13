(** * TightThreshold.v -- the size hypothesis of [SpreadYieldsDisjoint 3 3 3]
      is exactly tight

    [SpreadReduction.SpreadYieldsDisjoint n k r] asks for [k] pairwise
    disjoint members of every [r]-spread [m]-uniform family with *more
    than* [r^m] members.  At [(m, k, r) = (3, 3, 3)] the threshold is 27,
    and this file certifies that it cannot be lowered by even one: there
    is a 3-uniform family of exactly 27 distinct members, on nine points,
    satisfying Rao's absolute spread condition at [r = 3] -- every point
    in at most 9 members, every pair in at most 3, every triple in at
    most 1 -- with no three pairwise disjoint members.

    On nine points that is the counting ceiling [9 * 9 / 3 = 27] met with
    equality: the family is 9-regular.  It was found by an exact
    optimisation (docs/roadmap.md, session N+16) and is re-verified here
    by the kernel through the reflective checkers of [Reflect.v] and
    [Spread.v]; nothing below depends on how it was found.

    What this does and does not say.  It says nothing about whether
    [SpreadYieldsDisjoint 3 3 3] holds -- that needs a 28th member, and
    a 28th member cannot live on nine points.  It does say that any proof
    of [r*(3,3) = 3] must be tight at 27, i.e. must use the strict size
    hypothesis rather than a counting argument with slack. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Sunflower Require Import Sets Sunflower Spread Reflect SpreadReduction
  SpreadThreshold.

(** The family, as found: 27 triples on [{0,...,8}]. *)

Definition nine27 : Family :=
  [ [0;1;2]; [0;1;6]; [0;1;7]; [0;2;8]; [0;3;4]; [0;3;5]; [0;4;5];
    [0;6;7]; [0;7;8]; [1;2;3]; [1;2;5]; [1;3;4]; [1;3;8]; [1;5;6];
    [1;5;8]; [2;3;6]; [2;4;6]; [2;4;7]; [2;4;8]; [2;5;7]; [3;4;5];
    [3;6;7]; [3;6;8]; [4;6;7]; [4;7;8]; [5;6;8]; [5;7;8] ].

Definition nine_ground : list nat := [0;1;2;3;4;5;6;7;8].

Lemma nine27_uniform : Uniform 3 nine27.
Proof. apply uniformb_correct; reflexivity. Qed.

Lemma nine27_distinct : Distinct nine27.
Proof. apply distinctb_correct; reflexivity. Qed.

Lemma nine27_grounded : forall A, In A nine27 -> Subset A nine_ground.
Proof. apply groundedb_correct; reflexivity. Qed.

Lemma nine27_length : length nine27 = 27.
Proof. reflexivity. Qed.

(** Rao's absolute spread condition at [r = 3], by the witness search of
    [Spread.v] ... *)

Lemma nine27_rao_spread : RaoSpread 3 nine27 3.
Proof.
  apply (@rao_witness_none 3 nine27 3).
  - apply (@Uniform_NoDup 3 nine27 nine27_uniform).
  - vm_compute; reflexivity.
Qed.

(** ... and again by the independent ground-set procedure of [Reflect.v]. *)

Lemma nine27_rao_spread_second_opinion :
  rao_spreadb 3 nine27 3 nine_ground = true.
Proof. vm_compute; reflexivity. Qed.

(** Every point is in exactly nine members: the counting ceiling is met. *)

Lemma nine27_regular :
  forallb (fun x => Nat.eqb (deg [x] nine27) 9) nine_ground = true.
Proof. vm_compute; reflexivity. Qed.

(** No three pairwise disjoint members.  The boolean search is the one
    [SpreadThreshold.decide_three_disjoint] is proved complete for. *)

Definition three_disjointb (F : Family) : bool :=
  existsb (fun A => existsb (fun B => existsb
     (fun C => (disjointb A B && disjointb A C && disjointb B C)%bool)
     F) F) F.

Lemma nine27_no_three_disjoint_b : three_disjointb nine27 = false.
Proof. vm_compute; reflexivity. Qed.

Theorem nine27_no_three_disjoint : NoKDisjoint 3 nine27.
Proof.
  destruct (@decide_three_disjoint 3 nine27 ltac:(lia) nine27_uniform)
    as [[S [Hincl [Hnd [Hlen Hpd]]]] | Hno]; [exfalso | exact Hno].
  destruct S as [|A [|B [|C [|D S']]]]; simpl in Hlen; try lia.
  assert (HA : In A nine27) by (apply Hincl; left; reflexivity).
  assert (HB : In B nine27) by (apply Hincl; right; left; reflexivity).
  assert (HC : In C nine27) by (apply Hincl; right; right; left; reflexivity).
  inversion Hnd as [|? ? HAn Hnd1]; subst.
  inversion Hnd1 as [|? ? HBn Hnd2]; subst.
  assert (HAB : Disjoint A B).
  { apply Hpd; [left; reflexivity | right; left; reflexivity
               | intros <-; apply HAn; left; reflexivity]. }
  assert (HAC : Disjoint A C).
  { apply Hpd; [left; reflexivity | right; right; left; reflexivity
               | intros <-; apply HAn; right; left; reflexivity]. }
  assert (HBC : Disjoint B C).
  { apply Hpd; [right; left; reflexivity | right; right; left; reflexivity
               | intros <-; apply HBn; left; reflexivity]. }
  assert (Hb : three_disjointb nine27 = true).
  { unfold three_disjointb.
    apply existsb_exists; exists A; split; [exact HA|].
    apply existsb_exists; exists B; split; [exact HB|].
    apply existsb_exists; exists C; split; [exact HC|].
    repeat (apply Bool.andb_true_iff; split); apply disjointb_correct; assumption. }
  rewrite nine27_no_three_disjoint_b in Hb; discriminate.
Qed.

(** The headline: the size threshold [27] in [SpreadYieldsDisjoint 3 3 3]
    is attained by a family with none of the conclusion.  Weakening the
    strict inequality [r^m < length F] to [r^m <= length F] would make
    the statement false at [(3,3,3)]. *)

Theorem threshold_27_is_attained :
  exists F : Family,
    Uniform 3 F /\ Distinct F /\ length F = 3 ^ 3 /\ RaoSpread 3 F 3 /\
    NoKDisjoint 3 F.
Proof.
  exists nine27.
  refine (conj nine27_uniform (conj nine27_distinct (conj _ (conj nine27_rao_spread nine27_no_three_disjoint)))).
  reflexivity.
Qed.

(** Stated as the failure of the non-strict variant. *)

Definition SpreadYieldsDisjointNonStrict (n k r : nat) : Prop :=
  forall (m : nat) (F : Family),
    1 <= m -> m <= n ->
    Uniform m F -> Distinct F ->
    r ^ m <= length F ->
    RaoSpread m F r ->
    exists S : list (list nat),
      incl S F /\ NoDup S /\ length S = k /\ PairwiseDisjoint S.

Theorem non_strict_threshold_fails_at_3_3_3 :
  ~ SpreadYieldsDisjointNonStrict 3 3 3.
Proof.
  intro H.
  apply nine27_no_three_disjoint.
  apply (H 3 nine27 ltac:(lia) ltac:(lia) nine27_uniform nine27_distinct
           ltac:(rewrite nine27_length; simpl; lia) nine27_rao_spread).
Qed.
