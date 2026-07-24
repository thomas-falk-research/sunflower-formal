(** * Sets.v -- Finite-set machinery on [list nat] with [NoDup] invariant.

    We deliberately avoid external set libraries (MSets / FSets / MathComp
    finset) so the entire development depends only on the Coq standard
    library. Sets are represented by lists of natural numbers carrying an
    explicit [NoDup] hypothesis where it matters; set equality is mutual
    inclusion ([SetEq]).

    All lemmas in this file are computational and decidable. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
Import ListNotations.

Set Implicit Arguments.

(** ** Membership decidability *)

Lemma in_dec_nat : forall (x : nat) (l : list nat), {In x l} + {~ In x l}.
Proof. intros; apply in_dec, Nat.eq_dec. Defined.

(** ** Subset (extensional) *)

Definition Subset (A B : list nat) : Prop := forall x, In x A -> In x B.

Lemma Subset_refl : forall A, Subset A A.
Proof. unfold Subset; auto. Qed.

Lemma Subset_trans : forall A B C, Subset A B -> Subset B C -> Subset A C.
Proof. unfold Subset; auto. Qed.

Lemma Subset_nil : forall A, Subset [] A.
Proof. unfold Subset; intros A x H; inversion H. Qed.

(** ** Set equality as mutual inclusion *)

Definition SetEq (A B : list nat) : Prop := Subset A B /\ Subset B A.

Lemma SetEq_refl : forall A, SetEq A A.
Proof. split; apply Subset_refl. Qed.

Lemma SetEq_sym : forall A B, SetEq A B -> SetEq B A.
Proof. unfold SetEq; intros A B [H1 H2]; split; assumption. Qed.

Lemma SetEq_trans : forall A B C, SetEq A B -> SetEq B C -> SetEq A C.
Proof.
  unfold SetEq; intros A B C [H1 H2] [H3 H4]; split;
    eapply Subset_trans; eauto.
Qed.

(** ** Computational intersection *)

Definition inter (A B : list nat) : list nat :=
  filter (fun x => if in_dec_nat x B then true else false) A.

Lemma in_inter_iff : forall x A B,
    In x (inter A B) <-> In x A /\ In x B.
Proof.
  intros x A B; unfold inter; split.
  - intro H; apply filter_In in H as [Ha Hb].
    split; [exact Ha|].
    destruct (in_dec_nat x B); [assumption | discriminate].
  - intros [Ha Hb]; apply filter_In; split; [exact Ha|].
    destruct (in_dec_nat x B); [reflexivity | contradiction].
Qed.

Lemma inter_Subset_l : forall A B, Subset (inter A B) A.
Proof.
  unfold Subset; intros A B x H; rewrite in_inter_iff in H; tauto.
Qed.

Lemma inter_Subset_r : forall A B, Subset (inter A B) B.
Proof.
  unfold Subset; intros A B x H; rewrite in_inter_iff in H; tauto.
Qed.

Lemma inter_NoDup : forall A B, NoDup A -> NoDup (inter A B).
Proof.
  intros A B HA. unfold inter.
  induction HA as [| a l Hnotin Hnd IH]; simpl.
  - constructor.
  - destruct (in_dec_nat a B); simpl; [|exact IH].
    constructor; [|exact IH].
    intro Hin; apply filter_In in Hin as [Hin _]; contradiction.
Qed.

(** ** Disjointness *)

Definition Disjoint (A B : list nat) : Prop :=
  forall x, In x A -> In x B -> False.

Lemma Disjoint_sym : forall A B, Disjoint A B -> Disjoint B A.
Proof. unfold Disjoint; intros A B H x Hb Ha; eapply H; eauto. Qed.

Lemma Disjoint_nil_l : forall A, Disjoint [] A.
Proof. unfold Disjoint; intros A x H; inversion H. Qed.

Lemma Disjoint_inter_empty : forall A B,
    Disjoint A B -> inter A B = [].
Proof.
  intros A B Hd; unfold inter.
  induction A as [|a l IH]; simpl; [reflexivity|].
  destruct (in_dec_nat a B) as [Hin | Hnotin].
  - exfalso; apply (Hd a); simpl; auto.
  - apply IH. unfold Disjoint in *; intros x Hxl HxB.
    apply (Hd x); [right; assumption | assumption].
Qed.

(** ** Insertion-free union (used in lifting sunflowers) *)

Definition add_elt (x : nat) (A : list nat) : list nat :=
  if in_dec_nat x A then A else x :: A.

Lemma in_add_iff : forall x y A, In x (add_elt y A) <-> x = y \/ In x A.
Proof.
  intros x y A; unfold add_elt; destruct (in_dec_nat y A) as [Hin | Hnotin].
  - split; [right; assumption|].
    intros [Hxy | Hxa]; [subst; assumption | assumption].
  - simpl; split.
    + intros [E | H]; [left; symmetry; exact E | right; exact H].
    + intros [E | H]; [left; symmetry; exact E | right; exact H].
Qed.

Lemma add_NoDup : forall x A, NoDup A -> NoDup (add_elt x A).
Proof.
  intros x A HA; unfold add_elt; destruct (in_dec_nat x A); [exact HA|].
  constructor; assumption.
Qed.

Lemma length_add_elt : forall x A,
    NoDup A ->
    length (add_elt x A) = if in_dec_nat x A then length A else S (length A).
Proof.
  intros x A HA; unfold add_elt; destruct (in_dec_nat x A); reflexivity.
Qed.

Lemma length_add_elt_notin : forall x A,
    ~ In x A -> length (add_elt x A) = S (length A).
Proof.
  intros x A H; unfold add_elt; destruct (in_dec_nat x A); [contradiction|].
  reflexivity.
Qed.

(** ** Removing an element *)

Definition rem_elt (x : nat) (A : list nat) : list nat :=
  filter (fun y => negb (Nat.eqb y x)) A.

Lemma in_rem_iff : forall x y A, In x (rem_elt y A) <-> In x A /\ x <> y.
Proof.
  intros x y A; unfold rem_elt; split.
  - intro H; apply filter_In in H as [Ha Hb]; split; [exact Ha|].
    intro E; subst; rewrite Nat.eqb_refl in Hb; discriminate.
  - intros [Ha Hb]; apply filter_In; split; [exact Ha|].
    apply Bool.negb_true_iff, Nat.eqb_neq; exact Hb.
Qed.

Lemma rem_NoDup : forall x A, NoDup A -> NoDup (rem_elt x A).
Proof.
  intros x A HA; unfold rem_elt.
  induction HA as [| a l Hnotin Hnd IH]; simpl; [constructor|].
  destruct (Nat.eqb a x); simpl; [exact IH|].
  constructor; [|exact IH].
  intro H; apply filter_In in H as [H _]; contradiction.
Qed.

Lemma length_rem_elt_in : forall x A,
    NoDup A -> In x A -> length (rem_elt x A) = pred (length A).
Proof.
  intros x A HA Hin; unfold rem_elt.
  induction HA as [| a l Hnotin Hnd IH]; simpl; [inversion Hin|].
  destruct (Nat.eqb_spec a x) as [E | NE]; simpl.
  - subst a. assert (~ In x l) by assumption.
    clear -H.
    induction l as [| b l IH]; simpl; [reflexivity|].
    destruct (Nat.eqb_spec b x) as [E' | NE']; simpl.
    + subst b. exfalso; apply H; left; reflexivity.
    + f_equal. apply IH. intro Hx; apply H; right; exact Hx.
  - destruct Hin as [E' | Hin']; [contradiction|].
    rewrite IH by exact Hin'.
    destruct l as [|c m]; simpl in Hin'; [inversion Hin'|].
    simpl; reflexivity.
Qed.

Lemma length_rem_elt_notin : forall x A,
    ~ In x A -> length (rem_elt x A) = length A.
Proof.
  intros x A H; unfold rem_elt.
  induction A as [|a l IH]; simpl; [reflexivity|].
  destruct (Nat.eqb_spec a x) as [E | NE]; simpl.
  - subst a. exfalso; apply H; left; reflexivity.
  - f_equal. apply IH. intro Hin; apply H; right; exact Hin.
Qed.

Lemma rem_Subset : forall x A, Subset (rem_elt x A) A.
Proof. unfold Subset; intros x A y H; rewrite in_rem_iff in H; tauto. Qed.

(** ** Boolean membership predicate (for filter and partition) *)

Definition memb (x : nat) (A : list nat) : bool :=
  if in_dec_nat x A then true else false.

Lemma memb_true_iff : forall x A, memb x A = true <-> In x A.
Proof.
  intros x A; unfold memb; destruct (in_dec_nat x A) as [Hin | Hnotin].
  - split; intros; [exact Hin | reflexivity].
  - split; intros H; [discriminate | contradiction].
Qed.

Lemma memb_false_iff : forall x A, memb x A = false <-> ~ In x A.
Proof.
  intros x A; unfold memb; destruct (in_dec_nat x A) as [Hin | Hnotin].
  - split; intros H; [discriminate | contradiction].
  - split; intros; [exact Hnotin | reflexivity].
Qed.

(** ** Set-aware NoDup: no two members are set-equal.

    A list of sets that is literally NoDup (no repeated lists) can
    still contain set-equal duplicates (a list 1::2::nil and a list
    2::1::nil represent the same finite set). [SetNoDup] forbids this
    and is what we need for the Sunflower Conjecture. *)

Inductive SetNoDup : list (list nat) -> Prop :=
| SetNoDup_nil : SetNoDup []
| SetNoDup_cons : forall A F,
    (forall B, In B F -> ~ SetEq A B) ->
    SetNoDup F ->
    SetNoDup (A :: F).

Lemma SetNoDup_NoDup : forall F, SetNoDup F -> NoDup F.
Proof.
  intros F H; induction H as [|A F Hni Hsnd IH].
  - constructor.
  - constructor; [intro Hin; apply (Hni A Hin); apply SetEq_refl | exact IH].
Qed.

Lemma SetNoDup_pairwise :
  forall F, SetNoDup F ->
    forall A B, In A F -> In B F -> A <> B -> ~ SetEq A B.
Proof.
  intros F Hsnd; induction Hsnd as [|C F Hni Hsnd IH];
    intros A B HA HB Hne; simpl in HA, HB.
  - inversion HA.
  - destruct HA as [EA | HA]; destruct HB as [EB | HB].
    + subst; contradiction.
    + subst A. intro Hseq. apply (Hni B HB); exact Hseq.
    + subst B. intro Hseq. apply (Hni A HA). apply SetEq_sym; exact Hseq.
    + apply (IH A B HA HB Hne).
Qed.

Lemma SetNoDup_setEq_eq :
  forall F A B, SetNoDup F -> In A F -> In B F -> SetEq A B -> A = B.
Proof.
  intros F A B Hsnd HA HB Hseq.
  destruct (list_eq_dec Nat.eq_dec A B) as [Heq | Hne]; [exact Heq|].
  exfalso.
  pose proof (SetNoDup_pairwise Hsnd HA HB Hne) as Hcontra.
  apply Hcontra; exact Hseq.
Qed.

Lemma SetNoDup_filter :
  forall (P : list nat -> bool) F, SetNoDup F -> SetNoDup (filter P F).
Proof.
  intros P F H; induction H as [|A F Hni Hsnd IH]; simpl; [constructor|].
  destruct (P A); [|exact IH].
  constructor.
  - intros B HB. apply filter_In in HB as [HB _]. apply Hni; exact HB.
  - exact IH.
Qed.

Lemma SetNoDup_incl :
  forall (S F : list (list nat)),
    SetNoDup F -> NoDup S -> incl S F -> SetNoDup S.
Proof.
  intros S F Hsnd Hnd Hincl.
  induction S as [|A S' IH]; [constructor|].
  inversion Hnd as [|? ? HAni Hnd']; subst.
  constructor.
  - intros B HB Hseq.
    assert (HA : In A F) by (apply Hincl; left; reflexivity).
    assert (HBF : In B F) by (apply Hincl; right; exact HB).
    pose proof (SetNoDup_setEq_eq Hsnd HA HBF Hseq) as E.
    subst B; contradiction.
  - apply IH; auto. intros x Hx. apply Hincl; right; exact Hx.
Qed.

Lemma SetNoDup_map_rem_preserves :
  forall x F,
    SetNoDup F ->
    Forall (fun A => In x A) F ->
    SetNoDup (map (rem_elt x) F).
Proof.
  intros x F Hsnd Hcontain.
  induction Hsnd as [|A F Hni Hsnd IH]; simpl; [constructor|].
  inversion Hcontain as [|? ? HxA Hcontain']; subst.
  constructor.
  - intros B HB Hseq.
    apply in_map_iff in HB as [A' [HBeq HA'in]].
    subst B.
    rewrite Forall_forall in Hcontain'.
    pose proof (Hcontain' A' HA'in) as HxA'.
    (* SetEq (rem_x A) (rem_x A') with x in both A, A' implies SetEq A A' *)
    assert (HseqAA' : SetEq A A').
    { unfold SetEq, Subset; split; intros y Hy.
      - destruct (Nat.eq_dec y x) as [E | NE]; [subst; exact HxA'|].
        assert (In y (rem_elt x A)) by (apply in_rem_iff; auto).
        destruct Hseq as [Hs1 _].
        apply Hs1 in H. apply in_rem_iff in H; tauto.
      - destruct (Nat.eq_dec y x) as [E | NE]; [subst; exact HxA|].
        assert (In y (rem_elt x A')) by (apply in_rem_iff; auto).
        destruct Hseq as [_ Hs2].
        apply Hs2 in H. apply in_rem_iff in H; tauto. }
    apply (Hni A' HA'in); exact HseqAA'.
  - apply IH; exact Hcontain'.
Qed.

(** ** Boolean disjointness *)

Definition disjointb (A B : list nat) : bool :=
  forallb (fun x => negb (memb x B)) A.

Lemma disjointb_correct : forall A B,
    disjointb A B = true <-> Disjoint A B.
Proof.
  intros A B; unfold disjointb, Disjoint; split.
  - intros Hall x HA HB.
    rewrite forallb_forall in Hall.
    specialize (Hall x HA).
    apply Bool.negb_true_iff in Hall.
    rewrite memb_false_iff in Hall; contradiction.
  - intros H. apply forallb_forall; intros x HA.
    apply Bool.negb_true_iff. apply memb_false_iff.
    intro HB; apply (H x); auto.
Qed.

Lemma disjointb_false_iff : forall A B,
    disjointb A B = false <-> exists x, In x A /\ In x B.
Proof.
  intros A B; split.
  - intros Hfalse.
    destruct (Bool.bool_dec (disjointb A B) true) as [HT | _]; [rewrite HT in Hfalse; discriminate|].
    unfold disjointb in Hfalse.
    induction A as [|a A IH]; simpl in Hfalse; [discriminate|].
    destruct (Bool.bool_dec (negb (memb a B)) true) as [Hnm | Hm].
    + rewrite Hnm in Hfalse; simpl in Hfalse.
      destruct (IH Hfalse) as [x [Hx HxB]].
      exists x; split; [right; exact Hx | exact HxB].
    + apply Bool.not_true_is_false in Hm.
      apply Bool.negb_false_iff in Hm.
      apply memb_true_iff in Hm.
      exists a; split; [left; reflexivity | exact Hm].
  - intros [x [HxA HxB]].
    destruct (disjointb A B) eqn:E; [|reflexivity].
    apply disjointb_correct in E.
    exfalso; apply (E x); auto.
Qed.

(** ** Useful list lemmas reused throughout *)

Lemma length_pos_iff : forall {A} (l : list A), 0 < length l <-> l <> [].
Proof.
  intros; split.
  - intros H Heq; subst; simpl in H; lia.
  - destruct l; [intro H; exfalso; apply H; reflexivity | simpl; lia].
Qed.

Lemma in_split_first :
  forall (x : nat) (l : list nat),
    In x l -> exists l1 l2, l = l1 ++ x :: l2 /\ ~ In x l1.
Proof.
  induction l as [|a l IH]; intros H; simpl in H.
  - inversion H.
  - destruct (Nat.eqb_spec a x) as [E | NE].
    + subst a. exists [], l; simpl; split; auto.
    + destruct H as [E | H]; [exfalso; apply NE; exact E|].
      destruct (IH H) as [l1 [l2 [Hl Hnotin]]].
      exists (a :: l1), l2; simpl; split.
      * rewrite Hl; reflexivity.
      * intros [E' | H']; [apply NE; exact E' | contradiction].
Qed.
