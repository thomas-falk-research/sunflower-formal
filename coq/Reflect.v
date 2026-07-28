(** * Reflect.v -- Boolean certificates, and a second opinion on spreadness.

    Two jobs, both of them testing infrastructure rather than
    mathematics.

    *** 1. Decidable certificates for every family predicate

    Each predicate used to state the sunflower bounds — [NoDup],
    [UniformSet], [Uniform], [SetNoDup] / [Distinct], [Subset],
    [PairwiseDisjoint] — is decidable on concrete data, and gets a
    boolean counterpart here together with an *if and only if*
    correctness lemma.

    The [iff] is the point. Soundness ([b = true -> P]) is all a proof
    needs, and is all the certificates scattered through [F23.v]
    previously claimed. Completeness ([P -> b = true]) is what makes a
    [vm_compute] returning [false] count as evidence *against* [P]. A
    check that can only ever succeed is not a check, so every
    certificate here is proved in both directions; the concrete
    refutations in [Audit.v] rest on the completeness half.

    *** 2. An independent decision procedure for [RaoSpread]

    [Spread.rao_witness] decides spreadness by searching the sublists
    of the *members* of [F] — a choice made to keep the reduction
    constructive, and justified by [Spread.rao_witness_none]. That
    justification is a proof about [Spread.cands]; if [cands] enumerated
    too few candidate violators, the procedure would silently report
    "spread" for families that are not, and the reduction would be
    weakened rather than broken. Nothing else in the development would
    notice.

    [rao_spreadb] below is a second implementation that shares no code
    with the first: it enumerates the subsets of an explicitly supplied
    ground set [U]. [rao_witness_agrees] proves the two always give the
    same verdict. That is a differential test between two independent
    search strategies, discharged by the kernel rather than by
    sampling. *)

From Coq Require Import List Arith Lia Bool.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower LowerBound Spread.
Import ListNotations.

Set Implicit Arguments.

(** ** Certificates for the finite-set predicates *)

Fixpoint nodupb (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: r => negb (memb x r) && nodupb r
  end.

Lemma nodupb_correct : forall l, nodupb l = true <-> NoDup l.
Proof.
  induction l as [|x r IH]; simpl; split; intro H.
  - constructor.
  - reflexivity.
  - apply andb_true_iff in H as [H1 H2].
    constructor; [| apply IH; exact H2].
    apply negb_true_iff, memb_false_iff in H1; exact H1.
  - inversion H as [|? ? Hni Hnd]; subst.
    apply andb_true_iff; split.
    + apply negb_true_iff, memb_false_iff; exact Hni.
    + apply IH; exact Hnd.
Qed.

Definition subsetb (A B : list nat) : bool := forallb (fun x => memb x B) A.

Lemma subsetb_correct : forall A B, subsetb A B = true <-> Subset A B.
Proof.
  intros A B; unfold subsetb, Subset; split.
  - intros H x Hx; rewrite forallb_forall in H.
    apply memb_true_iff, H, Hx.
  - intros H; apply forallb_forall; intros x Hx.
    apply memb_true_iff, H, Hx.
Qed.

(** ** Certificates for the family predicates *)

Definition uniform_setb (n : nat) (A : list nat) : bool :=
  (length A =? n) && nodupb A.

Lemma uniform_setb_correct :
  forall n A, uniform_setb n A = true <-> UniformSet n A.
Proof.
  intros n A; unfold uniform_setb, UniformSet; split.
  - intro H; apply andb_true_iff in H as [H1 H2].
    split; [apply Nat.eqb_eq; exact H1 | apply nodupb_correct; exact H2].
  - intros [H1 H2]; apply andb_true_iff; split;
      [apply Nat.eqb_eq; exact H1 | apply nodupb_correct; exact H2].
Qed.

Definition uniformb (n : nat) (F : Family) : bool :=
  forallb (uniform_setb n) F.

Lemma uniformb_correct : forall n F, uniformb n F = true <-> Uniform n F.
Proof.
  intros n F; unfold uniformb, Uniform; split.
  - intro H; rewrite forallb_forall in H.
    apply Forall_forall; intros A HA.
    apply uniform_setb_correct, H, HA.
  - intro H; rewrite Forall_forall in H.
    apply forallb_forall; intros A HA.
    apply uniform_setb_correct, H, HA.
Qed.

Fixpoint set_nodupb (F : Family) : bool :=
  match F with
  | [] => true
  | A :: r => forallb (fun B => negb (seteqb A B)) r && set_nodupb r
  end.

Lemma set_nodupb_correct : forall F, set_nodupb F = true <-> SetNoDup F.
Proof.
  induction F as [|A r IH]; simpl; split; intro H.
  - constructor.
  - reflexivity.
  - apply andb_true_iff in H as [H1 H2].
    constructor; [| apply IH; exact H2].
    intros B HB Hseq.
    rewrite forallb_forall in H1; specialize (H1 B HB).
    apply negb_true_iff in H1.
    apply seteqb_correct in Hseq; congruence.
  - inversion H as [|? ? Hni Hsnd]; subst.
    apply andb_true_iff; split; [| apply IH; exact Hsnd].
    apply forallb_forall; intros B HB.
    apply negb_true_iff.
    destruct (seteqb A B) eqn:E; [| reflexivity].
    exfalso; apply (Hni B HB), seteqb_correct; exact E.
Qed.

Definition distinctb (F : Family) : bool := set_nodupb F.

Lemma distinctb_correct : forall F, distinctb F = true <-> Distinct F.
Proof. intros F; unfold distinctb, Distinct; apply set_nodupb_correct. Qed.

Definition list_eqb (A B : list nat) : bool :=
  if list_eq_dec Nat.eq_dec A B then true else false.

Lemma list_eqb_correct : forall A B, list_eqb A B = true <-> A = B.
Proof.
  intros A B; unfold list_eqb.
  destruct (list_eq_dec Nat.eq_dec A B) as [E | NE]; split; intro H.
  - exact E.
  - reflexivity.
  - discriminate.
  - contradiction.
Qed.

Definition pairwise_disjointb (S : list (list nat)) : bool :=
  forallb (fun A => forallb (fun B => list_eqb A B || disjointb A B) S) S.

Lemma pairwise_disjointb_correct :
  forall S, pairwise_disjointb S = true <-> PairwiseDisjoint S.
Proof.
  intros S; unfold pairwise_disjointb, PairwiseDisjoint; split.
  - intros H A B HA HB HAB.
    rewrite forallb_forall in H; specialize (H A HA).
    rewrite forallb_forall in H; specialize (H B HB).
    apply orb_true_iff in H as [H | H].
    + exfalso; apply HAB, list_eqb_correct; exact H.
    + apply disjointb_correct; exact H.
  - intros H; apply forallb_forall; intros A HA.
    apply forallb_forall; intros B HB.
    destruct (list_eq_dec Nat.eq_dec A B) as [E | NE].
    + apply orb_true_iff; left; apply list_eqb_correct; exact E.
    + apply orb_true_iff; right; apply disjointb_correct.
      apply (H A B HA HB NE).
Qed.

(** [groundedb F U] certifies that [U] is a ground set for [F]. *)

Definition groundedb (F : Family) (U : list nat) : bool :=
  forallb (fun A => subsetb A U) F.

Lemma groundedb_correct :
  forall F U, groundedb F U = true <-> (forall A, In A F -> Subset A U).
Proof.
  intros F U; unfold groundedb; split.
  - intros H A HA; rewrite forallb_forall in H.
    apply subsetb_correct, H, HA.
  - intros H; apply forallb_forall; intros A HA.
    apply subsetb_correct, H, HA.
Qed.

(** ** A second opinion on spreadness

    [rao_spreadb m F r U] checks the spread inequality at every
    nonempty subset of the ground set [U]. Where [Spread.rao_witness]
    searches [concat (map subsets F)] — the sublists of the members —
    this searches [subsets U]. Neither enumeration contains the other:
    [subsets U] misses nothing about [U] but knows nothing about [F],
    and [cands F] is generally much smaller. *)

Definition nonemptyb (T : list nat) : bool :=
  match T with [] => false | _ :: _ => true end.

Definition ne_subsets (U : list nat) : list (list nat) :=
  filter nonemptyb (subsets U).

Lemma in_ne_subsets_iff :
  forall U T, In T (ne_subsets U) <-> In T (subsets U) /\ T <> [].
Proof.
  intros U T; unfold ne_subsets; split.
  - intro H; apply filter_In in H as [H1 H2]; split; [exact H1|].
    destruct T; [discriminate | discriminate].
  - intros [H1 H2]; apply filter_In; split; [exact H1|].
    destruct T; [contradiction | reflexivity].
Qed.

Definition rao_spreadb (m : nat) (F : Family) (r : nat) (U : list nat) : bool :=
  forallb (fun T => Nat.leb (deg T F) (r ^ (m - length T))) (ne_subsets U).

(** Canonicalising an arbitrary [T] into the ground-set enumeration:
    [filter (fun x => memb x T) U] has the same elements as [T]
    whenever [T ⊆ U], hence the same length and the same degree, and
    it is literally a sublist of [U]. *)

Lemma ground_canonical :
  forall (U T : list nat),
    NoDup U -> NoDup T -> Subset T U ->
    exists T',
      In T' (subsets U) /\ Subset T T' /\ Subset T' T /\
      length T' = length T.
Proof.
  intros U T HU HT HTU.
  exists (filter (fun x => memb x T) U); repeat split.
  - apply filter_in_subsets.
  - intros x Hx; apply filter_In; split;
      [apply HTU, Hx | apply memb_true_iff; exact Hx].
  - intros x Hx; apply filter_In in Hx as [_ Hm]; apply memb_true_iff; exact Hm.
  - assert (Hnd : NoDup (filter (fun x => memb x T) U)) by (apply NoDup_filter; exact HU).
    assert (H1 : Subset T (filter (fun x => memb x T) U)).
    { intros x Hx; apply filter_In; split;
        [apply HTU, Hx | apply memb_true_iff; exact Hx]. }
    assert (H2 : Subset (filter (fun x => memb x T) U) T).
    { intros x Hx; apply filter_In in Hx as [_ Hm]; apply memb_true_iff; exact Hm. }
    assert (L1 : length T <= length (filter (fun x => memb x T) U))
      by (apply NoDup_incl_length; assumption).
    assert (L2 : length (filter (fun x => memb x T) U) <= length T)
      by (apply NoDup_incl_length; assumption).
    lia.
Qed.

Theorem rao_spreadb_correct :
  forall m F r U,
    NoDup U ->
    Forall (fun A : list nat => NoDup A) F ->
    (forall A, In A F -> Subset A U) ->
    (rao_spreadb m F r U = true <-> RaoSpread m F r).
Proof.
  intros m F r U HU Hnd Hgr; unfold rao_spreadb, RaoSpread; split.
  - intros H T HT Hne.
    rewrite forallb_forall in H.
    destruct (deg T F) as [|d] eqn:Hdeg; [lia|].
    (* positive degree forces [T] into the ground set *)
    destruct (@deg_pos_inv T F ltac:(lia)) as [A [HAF HTA]].
    assert (HTU : Subset T U)
      by (intros x Hx; apply (Hgr A HAF), HTA, Hx).
    destruct (ground_canonical HU HT HTU) as [T' [Hin [H1 [H2 Hlen]]]].
    assert (HT'ne : T' <> []).
    { destruct T as [|t T0]; [contradiction|].
      intro E; assert (Hin' : In t T') by (apply H1; left; reflexivity).
      rewrite E in Hin'; inversion Hin'. }
    assert (Hdeq : deg T' F = deg T F) by (apply deg_setEq; assumption).
    specialize (H T' (proj2 (in_ne_subsets_iff U T') (conj Hin HT'ne))).
    apply Nat.leb_le in H.
    rewrite Hlen, Hdeq in H; lia.
  - intros H; apply forallb_forall; intros T HT.
    apply in_ne_subsets_iff in HT as [Hin Hne].
    apply Nat.leb_le, H; [apply (@subsets_NoDup U T HU Hin) | exact Hne].
Qed.

(** ** The differential theorem

    Two searches, no shared enumeration, always the same verdict. *)

Theorem rao_witness_agrees :
  forall m F r U,
    NoDup U ->
    Forall (fun A : list nat => NoDup A) F ->
    (forall A, In A F -> Subset A U) ->
    (rao_witness m F r = None <-> rao_spreadb m F r U = true).
Proof.
  intros m F r U HU Hnd Hgr.
  rewrite (@rao_spreadb_correct m F r U HU Hnd Hgr).
  split.
  - intro H; apply (@rao_witness_none m F r Hnd H).
  - intros Hsp.
    destruct (rao_witness m F r) as [T|] eqn:E; [exfalso | reflexivity].
    apply rao_witness_some in E as [Hcand [Hne Hviol]].
    destruct (@in_cands_inv F T Hcand) as [A [HAF Hsub]].
    assert (HAnd : NoDup A) by (rewrite Forall_forall in Hnd; apply Hnd, HAF).
    assert (HTnd : NoDup T) by (apply (@subsets_NoDup A T HAnd Hsub)).
    specialize (Hsp T HTnd Hne); lia.
Qed.

(** Restating the half that matters for soundness: if *any* finite set
    at all violates the spread inequality, [rao_witness] finds one. A
    [None] verdict is therefore never a false negative — which is the
    property an under-sized [cands] would break. *)

Corollary rao_witness_complete :
  forall m F r T,
    Forall (fun A : list nat => NoDup A) F ->
    NoDup T -> T <> [] ->
    r ^ (m - length T) < deg T F ->
    exists T', rao_witness m F r = Some T'.
Proof.
  intros m F r T Hnd HT Hne Hviol.
  destruct (rao_witness m F r) as [T'|] eqn:E; [exists T'; reflexivity | exfalso].
  pose proof (@rao_witness_none m F r Hnd E T HT Hne) as Hle; lia.
Qed.

(** ** Worked agreement checks

    The theorem above says the two procedures agree on every input;
    these run both of them on concrete families so that the agreement
    is also exercised by [vm_compute] rather than only asserted. The
    third family is *not* spread, so the [Some]/[false] branch is
    covered too. *)

Definition three_pairs : Family := [[0; 1]; [2; 3]; [4; 5]].

Example agree_three_pairs :
  rao_witness 2 three_pairs 2 = None
  /\ rao_spreadb 2 three_pairs 2 [0; 1; 2; 3; 4; 5] = true.
Proof. split; vm_compute; reflexivity. Qed.

Definition star3 : Family := [[0; 1]; [0; 2]; [0; 3]].

Example agree_star3_not_spread :
  rao_witness 2 star3 2 = Some [0]
  /\ rao_spreadb 2 star3 2 [0; 1; 2; 3] = false.
Proof. split; vm_compute; reflexivity. Qed.
