(** * Sunflower.v -- Core combinatorial definitions.

    A [Family] is a list of finite sets (each itself a [list nat] with
    [NoDup]). A family is [Uniform n] when every member has size [n] and
    [Distinct] when no two members are [SetEq] (set-equal) — i.e. it is
    a list of *genuinely distinct* sets, not just literally distinct
    list representations. Using literal [NoDup] alone would allow e.g.
    the list 1::2::nil and the list 2::1::nil as two "members" of the
    same family, which is mathematically wrong.

    A [Sunflower] of width [k] is a sub-family of [k] [SetEq]-distinct
    sets whose pairwise intersections all equal a common [core] (under
    [SetEq]). [SubFamilySetEq] is the natural sub-family relation: every
    member is set-equal to some family member.

    The function [f n k] of the conjecture is captured here as two
    predicates: [UpperBound n k m] (every uniform distinct family of size
    [≥ m] contains a [k]-sunflower) and [LowerBound n k m] (there exists
    a uniform distinct family of size [= m] with no [k]-sunflower).

    No closed-form proofs about [f n k] are made here; the bounds are
    proved in [ErdosRado.v] and [LowerBound.v]. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets.
Import ListNotations.

Set Implicit Arguments.

(** ** Families *)

Definition Family := list (list nat).

Definition UniformSet (n : nat) (A : list nat) : Prop :=
  length A = n /\ NoDup A.

Definition Uniform (n : nat) (F : Family) : Prop :=
  Forall (UniformSet n) F.

Definition Distinct (F : Family) : Prop := SetNoDup F.

(** ** Sunflowers *)

Definition Sunflower (S : list (list nat)) (core : list nat) : Prop :=
  SetNoDup S /\
  forall A B, In A S -> In B S -> A <> B -> SetEq (inter A B) core.

Definition KSunflower (k : nat) (S : list (list nat)) : Prop :=
  length S = k /\ exists core, Sunflower S core.

(** A sublist of [F] up to set-equality of members.

    Mathematically, set families are families of *sets*; in the
    list-encoding used here the same set can be represented by multiple
    permutations. [SubFamilySetEq] is the natural relation: every member
    of [S] is set-equal to some member of [F]. *)

Definition SubFamilySetEq (S : list (list nat)) (F : Family) : Prop :=
  forall A, In A S -> exists B, In B F /\ SetEq A B.

Lemma SubFamilySetEq_incl : forall S F, incl S F -> SubFamilySetEq S F.
Proof.
  intros S F H A HA; exists A; split; [apply H; exact HA | apply SetEq_refl].
Qed.

Definition ContainsKSunflower (k : nat) (F : Family) : Prop :=
  exists S, SubFamilySetEq S F /\ KSunflower k S.

Lemma ContainsKSunflower_of_incl :
  forall k S F core,
    incl S F -> length S = k -> Sunflower S core ->
    ContainsKSunflower k F.
Proof.
  intros k S F core Hincl Hlen HS.
  exists S; split.
  - apply SubFamilySetEq_incl; exact Hincl.
  - split; [exact Hlen | exists core; exact HS].
Qed.

(** ** Bound predicates capturing the function [f n k] *)

Definition UpperBound (n k m : nat) : Prop :=
  forall F : Family,
    Uniform n F -> Distinct F -> length F >= m ->
    ContainsKSunflower k F.

Definition LowerBound (n k m : nat) : Prop :=
  exists F : Family,
    Uniform n F /\ Distinct F /\ length F = m /\ ~ ContainsKSunflower k F.

Lemma UpperBound_mono : forall n k m m',
    UpperBound n k m -> m <= m' -> UpperBound n k m'.
Proof.
  unfold UpperBound; intros n k m m' H Hle F HU HD Hlen.
  apply H; auto; lia.
Qed.

Lemma Uniform_sublist : forall n F S,
    Uniform n F -> incl S F -> Uniform n S.
Proof.
  unfold Uniform, incl; intros n F S HF Hincl.
  apply Forall_forall; intros x Hx.
  rewrite Forall_forall in HF; apply HF, Hincl, Hx.
Qed.

(** ** Lifting and projecting sunflowers by a single element

    If [S = [B_1; ...; B_k]] is a [k]-sunflower with core [Y] in a
    sub-family of sets *not* containing [x], then prepending [x] to each
    [B_i] yields a [k]-sunflower with core [{x} ∪ Y]. *)

Definition map_add (x : nat) (S : list (list nat)) : list (list nat) :=
  map (add_elt x) S.

Lemma in_map_add_iff : forall x S A,
    In A (map_add x S) <-> exists B, In B S /\ A = add_elt x B.
Proof.
  intros x S A; unfold map_add; rewrite in_map_iff.
  split; intros [B [Heq Hin]]; exists B; split; auto.
Qed.

Lemma length_map_add : forall x S, length (map_add x S) = length S.
Proof. intros; unfold map_add; apply map_length. Qed.

(** Pairwise intersection identity used in the lift. *)

Lemma inter_add_notin :
  forall (x : nat) (A B : list nat),
    ~ In x A -> ~ In x B ->
    SetEq (inter (add_elt x A) (add_elt x B))
          (add_elt x (inter A B)).
Proof.
  intros x A B HnA HnB.
  unfold SetEq, Subset; split; intros y Hy.
  - rewrite in_inter_iff in Hy; destruct Hy as [HyA HyB].
    rewrite in_add_iff in HyA, HyB.
    rewrite in_add_iff.
    destruct HyA as [E | HyA]; [left; exact E|].
    destruct HyB as [E | HyB]; [exfalso; subst y; contradiction|].
    right; rewrite in_inter_iff; split; auto.
  - rewrite in_inter_iff. rewrite in_add_iff in Hy.
    destruct Hy as [E | Hy].
    + subst y; split; rewrite in_add_iff; left; reflexivity.
    + rewrite in_inter_iff in Hy; destruct Hy as [HA HB].
      split; rewrite in_add_iff; right; auto.
Qed.

(** Adding x to each member of a SetNoDup family of sets not containing
    x preserves SetNoDup. *)

Lemma SetNoDup_map_add_notin :
  forall x S,
    Forall (fun A : list nat => ~ In x A) S ->
    SetNoDup S ->
    SetNoDup (map_add x S).
Proof.
  intros x S Hnotin Hsnd.
  unfold map_add.
  induction Hsnd as [|A S HniA HsndS IH]; simpl; [constructor|].
  inversion Hnotin as [|? ? HxA Hnotin']; subst.
  constructor.
  - intros B HB. apply in_map_iff in HB as [A' [HBeq HA'in]].
    subst B.
    intros Hseq.
    rewrite Forall_forall in Hnotin'.
    assert (HxA' : ~ In x A') by (apply Hnotin'; exact HA'in).
    (* SetEq (add x A) (add x A') with x ∉ A, A' implies SetEq A A' *)
    assert (HseqAA' : SetEq A A').
    { unfold SetEq, Subset; split; intros y Hy.
      - assert (HyAx : In y (add_elt x A)) by (apply in_add_iff; right; exact Hy).
        destruct Hseq as [Hs1 _]; apply Hs1 in HyAx.
        apply in_add_iff in HyAx as [E | H]; [subst; contradiction | exact H].
      - assert (HyAx : In y (add_elt x A')) by (apply in_add_iff; right; exact Hy).
        destruct Hseq as [_ Hs2]; apply Hs2 in HyAx.
        apply in_add_iff in HyAx as [E | H]; [subst; contradiction | exact H]. }
    apply (HniA A' HA'in); exact HseqAA'.
  - apply IH; exact Hnotin'.
Qed.

Theorem sunflower_lift :
  forall (x : nat) (S : list (list nat)) (core : list nat),
    Forall (fun A : list nat => ~ In x A) S ->
    Sunflower S core ->
    Sunflower (map_add x S) (add_elt x core).
Proof.
  intros x S core Hnotin [Hsnd Hcore].
  split.
  - apply SetNoDup_map_add_notin; auto.
  - intros U V HU HV Hne.
    apply in_map_add_iff in HU as [A [HAin Heq1]].
    apply in_map_add_iff in HV as [B [HBin Heq2]].
    subst U V.
    assert (HnA : ~ In x A) by (rewrite Forall_forall in Hnotin; auto).
    assert (HnB : ~ In x B) by (rewrite Forall_forall in Hnotin; auto).
    assert (HAB : A <> B).
    { intro E; subst B; apply Hne; reflexivity. }
    pose proof (inter_add_notin x A B HnA HnB) as Hinter.
    pose proof (Hcore _ _ HAin HBin HAB) as Hcore'.
    eapply SetEq_trans; [exact Hinter|].
    unfold SetEq, Subset; split; intros y Hy.
    + rewrite in_add_iff in Hy; rewrite in_add_iff; destruct Hy as [E | H].
      * left; exact E.
      * right; apply Hcore', H.
    + rewrite in_add_iff in Hy; rewrite in_add_iff; destruct Hy as [E | H].
      * left; exact E.
      * right; apply Hcore', H.
Qed.

Corollary k_sunflower_lift :
  forall (x : nat) (S : list (list nat)) (k : nat),
    Forall (fun A : list nat => ~ In x A) S ->
    KSunflower k S ->
    KSunflower k (map_add x S).
Proof.
  intros x S k Hnotin [Hlen [core HS]].
  split; [rewrite length_map_add; exact Hlen|].
  exists (add_elt x core); apply sunflower_lift; auto.
Qed.

(** ** Trivial sunflowers from pairwise-disjoint sub-families *)

Definition PairwiseDisjoint (S : list (list nat)) : Prop :=
  forall A B, In A S -> In B S -> A <> B -> Disjoint A B.

(** Pairwise-disjoint nonempty sets have pairwise non-set-equal members. *)

Lemma SetNoDup_of_pairwise_disjoint_nonempty :
  forall S, NoDup S ->
    Forall (fun A : list nat => A <> []) S ->
    PairwiseDisjoint S ->
    SetNoDup S.
Proof.
  intros S Hnd HFne Hpd.
  induction Hnd as [|A S HniA HndS IH]; [constructor|].
  inversion HFne as [|? ? HAne HFne']; subst.
  constructor.
  - intros B HB Hseq.
    assert (HABne : A <> B).
    { intro E; subst B; contradiction. }
    pose proof (Hpd A B (or_introl eq_refl) (or_intror HB) HABne) as Hdis.
    destruct A as [|a A']; [apply HAne; reflexivity|].
    assert (Ha : In a (a :: A')) by (left; reflexivity).
    destruct Hseq as [Hs _]. apply Hs in Ha.
    apply (Hdis a); [left; reflexivity | exact Ha].
  - apply IH; [exact HFne' | unfold PairwiseDisjoint in *; intros C D HC HD HCD;
                apply Hpd; auto; right; auto].
Qed.

Lemma pairwise_disjoint_sunflower :
  forall S,
    NoDup S ->
    Forall (fun A : list nat => A <> []) S ->
    PairwiseDisjoint S ->
    Sunflower S [].
Proof.
  intros S Hnd HFne Hpd; split.
  - apply SetNoDup_of_pairwise_disjoint_nonempty; auto.
  - intros A B HA HB Hne.
    pose proof (Hpd A B HA HB Hne) as Hdis.
    rewrite (Disjoint_inter_empty Hdis).
    apply SetEq_refl.
Qed.

Corollary k_pairwise_disjoint_sunflower :
  forall k S,
    NoDup S -> length S = k ->
    Forall (fun A : list nat => A <> []) S ->
    PairwiseDisjoint S ->
    KSunflower k S.
Proof.
  intros k S Hnd Hlen HFne Hpd; split; [exact Hlen|].
  exists []; apply pairwise_disjoint_sunflower; auto.
Qed.
