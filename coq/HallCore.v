(**
 * HallCore.v - Hall's marriage theorem, abstract list form
 *
 * Constructive proof of Hall's 1935 marriage theorem over an
 * abstract adjacency [adj : nat -> nat -> bool] and two [NoDup]
 * vertex lists [A] (left) and [B] (right), by strong induction on
 * [length A] following the Halmos-Vaughan argument:
 *
 *   - if some nonempty proper [S0] of [A] is critical
 *     ([|N(S0)| = |S0|]), split into [(S0, N(S0))] and
 *     [(A minus S0, B minus N(S0))] and recurse on both halves;
 *   - otherwise every nonempty proper subset has slack
 *     ([|N(S)| >= |S| + 1]), so match the head [a] of [A] to any
 *     neighbour [b], delete both, and recurse.
 *
 * The result is a [Pairing]: a list of (left, right) pairs with
 * [NoDup] projections that saturates [A] and respects [adj].
 * [KoenigHall.v] converts pairings into graph
 * matchings, derives Hall's theorem in its original graph form, and
 * uses the deficiency version to prove König's minimax theorem.
 *
 * Criticality is decided by brute-force search over [sublists A]
 * (all subsequences) - exponential, but computability is incidental
 * here; only the statement matters.
 *
 * Citation:
 *   P. Hall. "On Representatives of Subsets." J. London Math. Soc.
 *   10 (1935), 26-30. Proof shape: Halmos-Vaughan (1950).
 *
 * VERIFICATION STATUS: Machine-checked, zero admits, zero axioms.
 *)

Require Import List.
Require Import Arith.
Require Import Lia.
Require Import Bool.
Require Import PeanoNat.
From Sunflower Require Import Sets.

Import ListNotations.

(** ** Generic list / boolean helpers *)

Lemma existsb_ext_in :
  forall (X : Type) (f g : X -> bool) (l : list X),
    (forall x, In x l -> f x = g x) -> existsb f l = existsb g l.
Proof.
  intros X f g l H; induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite (H x (or_introl eq_refl)).
  rewrite IH; [reflexivity | intros y Hy; apply H; right; exact Hy].
Qed.

Lemma existsb_set_eq :
  forall (X : Type) (f : X -> bool) (l1 l2 : list X),
    (forall x, In x l1 <-> In x l2) ->
    existsb f l1 = existsb f l2.
Proof.
  intros X f l1 l2 H.
  destruct (existsb f l1) eqn:E1; destruct (existsb f l2) eqn:E2;
    try reflexivity.
  - apply existsb_exists in E1 as [x [Hx Hf]].
    assert (Hx2 : In x l2) by (apply H; exact Hx).
    assert (E : existsb f l2 = true) by (apply existsb_exists; eauto).
    congruence.
  - apply existsb_exists in E2 as [x [Hx Hf]].
    assert (Hx1 : In x l1) by (apply H; exact Hx).
    assert (E : existsb f l1 = true) by (apply existsb_exists; eauto).
    congruence.
Qed.

Lemma filter_ext_in_local :
  forall (X : Type) (f g : X -> bool) (l : list X),
    (forall x, In x l -> f x = g x) -> filter f l = filter g l.
Proof.
  intros X f g l H; induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite (H x (or_introl eq_refl)).
  rewrite IH; [reflexivity | intros y Hy; apply H; right; exact Hy].
Qed.

Lemma filter_and :
  forall (X : Type) (f g : X -> bool) (l : list X),
    filter f (filter g l) = filter (fun x => andb (g x) (f x)) l.
Proof.
  intros X f g l; induction l as [|x l IH]; simpl; [reflexivity|].
  destruct (g x) eqn:Eg; simpl.
  - destruct (f x); simpl; rewrite IH; reflexivity.
  - exact IH.
Qed.

Lemma filter_length_le :
  forall (X : Type) (f : X -> bool) (l : list X),
    length (filter f l) <= length l.
Proof.
  intros X f l; induction l as [|x l IH]; simpl; [lia|].
  destruct (f x); simpl; lia.
Qed.

Lemma filter_length_lt :
  forall (X : Type) (f : X -> bool) (l : list X) (x : X),
    In x l -> f x = false -> length (filter f l) < length l.
Proof.
  intros X f l; induction l as [|y l IH]; intros x Hin Hf; [inversion Hin|].
  simpl in Hin; destruct Hin as [E | Hin].
  - subst y. simpl. rewrite Hf.
    pose proof (filter_length_le X f l); lia.
  - simpl. destruct (f y); simpl; pose proof (IH x Hin Hf); lia.
Qed.

Lemma filter_length_split :
  forall (X : Type) (f : X -> bool) (l : list X),
    length (filter f l) + length (filter (fun x => negb (f x)) l) = length l.
Proof.
  intros X f l; induction l as [|x l IH]; simpl; [reflexivity|].
  destruct (f x); simpl; lia.
Qed.

Lemma NoDup_app_intro :
  forall (X : Type) (l1 l2 : list X),
    NoDup l1 -> NoDup l2 ->
    (forall x, In x l1 -> ~ In x l2) ->
    NoDup (l1 ++ l2).
Proof.
  intros X l1 l2 H1 H2 Hdis;
    induction H1 as [|x l1 Hni H1 IH]; simpl; [exact H2|].
  constructor.
  - rewrite in_app_iff. intros [Hx | Hx]; [exact (Hni Hx)|].
    apply (Hdis x); [left; reflexivity | exact Hx].
  - apply IH. intros y Hy; apply Hdis; right; exact Hy.
Qed.

Lemma NoDup_set_eq_length :
  forall (l1 l2 : list nat),
    NoDup l1 -> NoDup l2 -> (forall x, In x l1 <-> In x l2) ->
    length l1 = length l2.
Proof.
  intros l1 l2 H1 H2 Hiff.
  apply Nat.le_antisymm; apply NoDup_incl_length; auto;
    intros x Hx; apply Hiff; exact Hx.
Qed.

(** ** All subsequences of a list *)

Fixpoint sublists (l : list nat) : list (list nat) :=
  match l with
  | [] => [[]]
  | x :: l' => map (cons x) (sublists l') ++ sublists l'
  end.

Lemma sublists_incl : forall l S, In S (sublists l) -> incl S l.
Proof.
  induction l as [|x l IH]; simpl; intros S HS.
  - destruct HS as [E | []]; subst S. intros y Hy; inversion Hy.
  - apply in_app_or in HS. destruct HS as [HS | HS].
    + apply in_map_iff in HS as [S' [E HS']]; subst S.
      intros y Hy. destruct Hy as [E | Hy]; [subst y; left; reflexivity|].
      right. apply (IH S' HS'); exact Hy.
    + intros y Hy. right. apply (IH S HS); exact Hy.
Qed.

Lemma sublists_NoDup_members :
  forall l S, NoDup l -> In S (sublists l) -> NoDup S.
Proof.
  induction l as [|x l IH]; simpl; intros S Hnd HS.
  - destruct HS as [E | []]; subst S; constructor.
  - inversion Hnd as [|? ? Hni Hnd']; subst.
    apply in_app_or in HS. destruct HS as [HS | HS].
    + apply in_map_iff in HS as [S' [E HS']]; subst S.
      constructor; [|apply IH; auto].
      intro Hx. apply (sublists_incl l S' HS') in Hx. contradiction.
    + apply IH; auto.
Qed.

Lemma filter_in_sublists :
  forall (f : nat -> bool) (l : list nat), In (filter f l) (sublists l).
Proof.
  intros f l; induction l as [|x l IH]; simpl; [left; reflexivity|].
  destruct (f x); apply in_or_app.
  - left. apply in_map. exact IH.
  - right. exact IH.
Qed.

(** ** Neighbourhoods, the Hall condition, and pairings *)

Definition nbhd (adj : nat -> nat -> bool) (S B : list nat) : list nat :=
  filter (fun b => existsb (fun a => adj a b) S) B.

Lemma in_nbhd_iff :
  forall adj S B b,
    In b (nbhd adj S B) <->
    In b B /\ (exists a, In a S /\ adj a b = true).
Proof.
  intros adj S B b; unfold nbhd; rewrite filter_In.
  split; intros [H1 H2]; split; auto.
  - apply existsb_exists in H2. exact H2.
  - apply existsb_exists. exact H2.
Qed.

Lemma nbhd_incl : forall adj S B, incl (nbhd adj S B) B.
Proof.
  intros adj S B b Hb; unfold nbhd in Hb; apply filter_In in Hb; tauto.
Qed.

Lemma nbhd_NoDup : forall adj S B, NoDup B -> NoDup (nbhd adj S B).
Proof. intros; apply NoDup_filter; auto. Qed.

Lemma nbhd_set_eq :
  forall adj S S' B,
    (forall x, In x S <-> In x S') ->
    nbhd adj S B = nbhd adj S' B.
Proof.
  intros adj S S' B H; unfold nbhd.
  apply filter_ext_in_local; intros b _.
  apply existsb_set_eq; exact H.
Qed.

(** Restricting the right side to the neighbourhood of a superset
    does not change a neighbourhood. *)

Lemma nbhd_nbhd_absorb :
  forall adj S S0 B,
    incl S S0 ->
    nbhd adj S (nbhd adj S0 B) = nbhd adj S B.
Proof.
  intros adj S S0 B Hincl; unfold nbhd.
  rewrite filter_and. apply filter_ext_in_local.
  intros b _.
  destruct (existsb (fun a => adj a b) S) eqn:ES.
  - apply existsb_exists in ES as [x [HxS Hx]].
    assert (E0 : existsb (fun a => adj a b) S0 = true)
      by (apply existsb_exists; exists x; split; [apply Hincl; auto | auto]).
    rewrite E0. reflexivity.
  - apply andb_false_r.
Qed.

Definition HallCond (adj : nat -> nat -> bool) (A B : list nat) : Prop :=
  forall S, incl S A -> NoDup S -> length S <= length (nbhd adj S B).

Definition Pairing (adj : nat -> nat -> bool) (A B : list nat)
                   (M : list (nat * nat)) : Prop :=
  NoDup (map fst M) /\
  NoDup (map snd M) /\
  (forall a, In a A -> In a (map fst M)) /\
  Forall (fun p => In (fst p) A /\ In (snd p) B /\ adj (fst p) (snd p) = true) M.

Lemma Pairing_nil : forall adj B, Pairing adj [] B [].
Proof.
  intros adj B. split; [constructor|]. split; [constructor|].
  split; [intros a Ha; inversion Ha | constructor].
Qed.

Lemma Pairing_fst_incl :
  forall adj A B M, Pairing adj A B M -> incl (map fst M) A.
Proof.
  intros adj A B M [_ [_ [_ Hall]]] x Hx.
  apply in_map_iff in Hx as [p [E Hp]]; subst x.
  rewrite Forall_forall in Hall. apply Hall in Hp. tauto.
Qed.

Lemma Pairing_snd_incl :
  forall adj A B M, Pairing adj A B M -> incl (map snd M) B.
Proof.
  intros adj A B M [_ [_ [_ Hall]]] x Hx.
  apply in_map_iff in Hx as [p [E Hp]]; subst x.
  rewrite Forall_forall in Hall. apply Hall in Hp. tauto.
Qed.

Lemma Pairing_length :
  forall adj A B M, NoDup A -> Pairing adj A B M -> length M = length A.
Proof.
  intros adj A B M HndA HP.
  pose proof HP as [Hf [_ [Hsat _]]].
  rewrite <- (map_length fst M).
  apply NoDup_set_eq_length; auto.
  intros x; split; intro Hx.
  - eapply Pairing_fst_incl; eauto.
  - apply Hsat; exact Hx.
Qed.

(** ** Upgrading "no critical subsequence" to all NoDup subsets

    The search for a critical set enumerates only subsequences of
    [A]; an arbitrary [NoDup] subset [S] is transferred through its
    canonical form [filter (memb-in-S) A], which is a subsequence
    with the same element set, the same length and the same
    neighbourhood. *)

Lemma no_critical_strong :
  forall adj (A B : list nat),
    NoDup A ->
    (forall S, In S (sublists A) -> S <> [] -> length S < length A ->
               length S < length (nbhd adj S B)) ->
    forall S, incl S A -> NoDup S -> S <> [] -> length S < length A ->
              length S < length (nbhd adj S B).
Proof.
  intros adj A B HndA Hsub S HinclS HndS Hne Hlt.
  set (S' := filter (fun x => memb x S) A).
  assert (Hiff : forall x, In x S' <-> In x S).
  { intros x; unfold S'; rewrite filter_In.
    split.
    - intros [_ Hm]. apply memb_true_iff; exact Hm.
    - intros Hx. split; [apply HinclS; exact Hx | apply memb_true_iff; exact Hx]. }
  assert (HndS' : NoDup S') by (apply NoDup_filter; exact HndA).
  assert (Hlen : length S' = length S)
    by (apply NoDup_set_eq_length; auto).
  assert (Hnbhd : nbhd adj S' B = nbhd adj S B)
    by (apply nbhd_set_eq; exact Hiff).
  assert (Hne' : S' <> []).
  { destruct S as [|s S1]; [congruence|].
    intro E.
    assert (Hs : In s S') by (apply Hiff; left; reflexivity).
    rewrite E in Hs; inversion Hs. }
  specialize (Hsub S' (filter_in_sublists _ _) Hne').
  rewrite Hlen, Hnbhd in Hsub. apply Hsub. exact Hlt.
Qed.

(** ** The induction: critical and non-critical steps *)

Section HallInduction.
  Variable adj : nat -> nat -> bool.
  Variable n : nat.
  Hypothesis IH : forall (A B : list nat),
      length A <= n -> NoDup A -> NoDup B ->
      HallCond adj A B ->
      exists M, Pairing adj A B M.

  (** Critical case: a nonempty proper [S0] with [|N(S0)| = |S0|].
      Recurse on [(S0, N(S0))] and on the complements. *)

  Lemma hall_critical :
    forall (A B S0 : list nat),
      length A <= S n -> NoDup A -> NoDup B -> HallCond adj A B ->
      incl S0 A -> NoDup S0 -> S0 <> [] -> length S0 < length A ->
      length (nbhd adj S0 B) <= length S0 ->
      exists M, Pairing adj A B M.
  Proof.
    intros A B S0 HAn HndA HndB Hhall HinclS0 HndS0 Hne0 Hprop Hcritle.
    assert (Hcrit : length (nbhd adj S0 B) = length S0)
      by (apply Nat.le_antisymm; [exact Hcritle | apply Hhall; auto]).
    set (B1 := nbhd adj S0 B).
    set (A2 := filter (fun x => negb (memb x S0)) A).
    set (B2 := filter (fun b => negb (memb b B1)) B).
    assert (HinclA2 : incl A2 A).
    { intros x Hx; unfold A2 in Hx; apply filter_In in Hx; tauto. }
    assert (HinclB2 : incl B2 B).
    { intros x Hx; unfold B2 in Hx; apply filter_In in Hx; tauto. }
    assert (HdisA2S0 : forall x, In x A2 -> ~ In x S0).
    { intros x Hx Hx0. unfold A2 in Hx. apply filter_In in Hx as [_ Hm].
      apply negb_true_iff in Hm. rewrite memb_false_iff in Hm. contradiction. }
    assert (HdisB2B1 : forall b, In b B2 -> ~ In b B1).
    { intros b Hb Hb1. unfold B2 in Hb. apply filter_In in Hb as [_ Hm].
      apply negb_true_iff in Hm. rewrite memb_false_iff in Hm. contradiction. }
    (* Recursion 1: (S0, B1). *)
    assert (Hhall1 : HallCond adj S0 B1).
    { intros S HinclS HndS.
      unfold B1. rewrite (nbhd_nbhd_absorb adj S S0 B HinclS).
      apply Hhall; [eapply incl_tran; eauto | exact HndS]. }
    assert (HlenS0 : length S0 <= n) by lia.
    destruct (IH S0 B1 HlenS0 HndS0 (nbhd_NoDup adj S0 B HndB) Hhall1)
      as [M1 HP1].
    (* Recursion 2: (A2, B2). *)
    assert (HndA2 : NoDup A2) by (apply NoDup_filter; exact HndA).
    assert (HndB2 : NoDup B2) by (apply NoDup_filter; exact HndB).
    assert (HA2lt : length A2 < length A).
    { destruct S0 as [|s S0']; [congruence|].
      apply (filter_length_lt _ _ A s); [apply HinclS0; left; reflexivity|].
      assert (Hm : memb s (s :: S0') = true)
        by (apply memb_true_iff; left; reflexivity).
      rewrite Hm. reflexivity. }
    assert (Hhall2 : HallCond adj A2 B2).
    { intros S HinclS HndS.
      destruct S as [|s1 S1]; [simpl; lia|].
      set (S' := s1 :: S1).
      set (T := S' ++ S0).
      assert (HndT : NoDup T).
      { unfold T. apply NoDup_app_intro;
          [ exact HndS | exact HndS0
          | intros x Hx Hx0; eapply HdisA2S0;
            [apply HinclS; exact Hx | exact Hx0] ]. }
      assert (HinclT : incl T A).
      { unfold T. intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx | Hx].
        - apply HinclA2. apply HinclS. exact Hx.
        - apply HinclS0. exact Hx. }
      pose proof (Hhall T HinclT HndT) as HTle.
      (* Split |N(T)| by membership in B1. *)
      pose proof (filter_length_split nat (fun b => memb b B1) (nbhd adj T B))
        as Hsplit.
      cbv beta in Hsplit.
      (* The part inside B1 is at most |B1|. *)
      assert (Hpart1 : length (filter (fun b => memb b B1) (nbhd adj T B))
                       <= length B1).
      { apply NoDup_incl_length.
        - apply NoDup_filter. apply nbhd_NoDup; exact HndB.
        - intros b Hb. apply filter_In in Hb as [_ Hm].
          apply memb_true_iff; exact Hm. }
      (* The part outside B1 is exactly N_{B2}(S'). *)
      assert (Hpart2 : filter (fun b => negb (memb b B1)) (nbhd adj T B)
                       = nbhd adj S' B2).
      { unfold nbhd, B2. rewrite !filter_and.
        apply filter_ext_in_local. intros b HbB.
        destruct (memb b B1) eqn:Em; simpl.
        - rewrite andb_false_r. reflexivity.
        - rewrite andb_true_r.
          unfold T. rewrite existsb_app.
          assert (E0 : existsb (fun a => adj a b) S0 = false).
          { destruct (existsb (fun a => adj a b) S0) eqn:E0; [|reflexivity].
            exfalso.
            assert (Hb1 : In b B1).
            { unfold B1, nbhd. apply filter_In. split; auto. }
            rewrite memb_false_iff in Em. contradiction. }
          rewrite E0. rewrite orb_false_r. reflexivity. }
      assert (HlenT : length T = length S' + length S0)
        by (unfold T; apply app_length).
      rewrite Hpart2 in Hsplit.
      assert (HlenB1 : length B1 = length S0) by (unfold B1; exact Hcrit).
      lia. }
    assert (HlenA2 : length A2 <= n) by lia.
    destruct (IH A2 B2 HlenA2 HndA2 HndB2 Hhall2) as [M2 HP2].
    (* Assemble the two pairings. *)
    pose proof HP1 as [Hf1 [Hs1 [Hsat1 Hall1]]].
    pose proof HP2 as [Hf2 [Hs2 [Hsat2 Hall2]]].
    exists (M1 ++ M2).
    split; [|split; [|split]].
    - rewrite map_app. apply NoDup_app_intro; auto.
      intros x Hx1 Hx2.
      apply (Pairing_fst_incl adj S0 B1 M1 HP1) in Hx1.
      apply (Pairing_fst_incl adj A2 B2 M2 HP2) in Hx2.
      exact (HdisA2S0 x Hx2 Hx1).
    - rewrite map_app. apply NoDup_app_intro; auto.
      intros x Hx1 Hx2.
      apply (Pairing_snd_incl adj S0 B1 M1 HP1) in Hx1.
      apply (Pairing_snd_incl adj A2 B2 M2 HP2) in Hx2.
      exact (HdisB2B1 x Hx2 Hx1).
    - intros a Ha. rewrite map_app. apply in_or_app.
      destruct (memb a S0) eqn:Em.
      + left. apply Hsat1. apply memb_true_iff; exact Em.
      + right. apply Hsat2. unfold A2. apply filter_In.
        split; [exact Ha | rewrite Em; reflexivity].
    - apply Forall_app. split.
      + eapply Forall_impl; [|exact Hall1].
        intros p [HpA [HpB Hpadj]].
        split; [apply HinclS0; exact HpA|].
        split; [|exact Hpadj].
        apply (nbhd_incl adj S0 B). exact HpB.
      + eapply Forall_impl; [|exact Hall2].
        intros p [HpA [HpB Hpadj]].
        split; [apply HinclA2; exact HpA|].
        split; [|exact Hpadj].
        apply HinclB2; exact HpB.
  Qed.

  (** Non-critical case: every nonempty proper subset has slack, so
      matching the head to any neighbour keeps Hall's condition. *)

  Lemma hall_noncritical :
    forall (a : nat) (A' B : list nat),
      length (a :: A') <= S n -> NoDup (a :: A') -> NoDup B ->
      HallCond adj (a :: A') B ->
      (forall S, incl S (a :: A') -> NoDup S -> S <> [] ->
                 length S < length (a :: A') ->
                 length S < length (nbhd adj S B)) ->
      exists M, Pairing adj (a :: A') B M.
  Proof.
    intros a A' B HAn HndA HndB Hhall Hstrong.
    assert (H1 : 1 <= length (nbhd adj [a] B)).
    { apply (Hhall [a]).
      - intros x [E | []]; subst; left; reflexivity.
      - constructor; [intros [] | constructor]. }
    destruct (nbhd adj [a] B) as [|b rest] eqn:En; [simpl in H1; lia|].
    assert (Hbb : In b (nbhd adj [a] B)) by (rewrite En; left; reflexivity).
    apply in_nbhd_iff in Hbb as [HbB [a' [Ha' Hadjab]]].
    destruct Ha' as [E | []]; subst a'.
    inversion HndA as [|? ? HaA' HndA']; subst.
    set (B' := rem_elt b B).
    assert (HndB' : NoDup B') by (apply rem_NoDup; exact HndB).
    assert (Hhall' : HallCond adj A' B').
    { intros S HinclS HndS.
      destruct S as [|s1 S1]; [simpl; lia|].
      assert (HinclSA : incl (s1 :: S1) (a :: A'))
        by (intros x Hx; right; apply HinclS; exact Hx).
      assert (HlenS : length (s1 :: S1) < length (a :: A')).
      { pose proof (NoDup_incl_length HndS HinclS). simpl in *. lia. }
      assert (Hne : s1 :: S1 <> []) by discriminate.
      pose proof (Hstrong (s1 :: S1) HinclSA HndS Hne HlenS) as Hgt.
      assert (Heq : nbhd adj (s1 :: S1) B'
                    = rem_elt b (nbhd adj (s1 :: S1) B)).
      { unfold B', rem_elt, nbhd. rewrite !filter_and.
        apply filter_ext_in_local. intros x _. apply andb_comm. }
      rewrite Heq.
      destruct (in_dec Nat.eq_dec b (nbhd adj (s1 :: S1) B)) as [Hin | Hnotin].
      - rewrite (@length_rem_elt_in b _ (nbhd_NoDup adj _ B HndB) Hin). lia.
      - rewrite (@length_rem_elt_notin b _ Hnotin). lia. }
    assert (HlenA' : length A' <= n) by (simpl in HAn; lia).
    destruct (IH A' B' HlenA' HndA' HndB' Hhall') as [M' HP'].
    pose proof HP' as [Hf' [Hs' [Hsat' Hall']]].
    exists ((a, b) :: M').
    split; [|split; [|split]].
    - simpl. constructor; [|exact Hf'].
      intro Hx. apply in_map_iff in Hx as [p [E Hp]].
      rewrite Forall_forall in Hall'.
      destruct (Hall' p Hp) as [HpA [_ _]].
      rewrite E in HpA. contradiction.
    - simpl. constructor; [|exact Hs'].
      intro Hx. apply in_map_iff in Hx as [p [E Hp]].
      rewrite Forall_forall in Hall'.
      destruct (Hall' p Hp) as [_ [HpB _]].
      rewrite E in HpB. unfold B' in HpB.
      apply in_rem_iff in HpB as [_ Hne]. apply Hne; reflexivity.
    - intros a0 Ha0. simpl. destruct Ha0 as [E | Ha0].
      + left; exact E.
      + right. apply Hsat'; exact Ha0.
    - constructor.
      + simpl. split; [left; reflexivity | split; [exact HbB | exact Hadjab]].
      + eapply Forall_impl; [|exact Hall'].
        intros p [HpA [HpB Hpadj]].
        split; [right; exact HpA|].
        split; [|exact Hpadj].
        apply (rem_Subset b B). exact HpB.
  Qed.

End HallInduction.

(** ** The abstract Hall theorem *)

Lemma hall_abstract_aux :
  forall (adj : nat -> nat -> bool) (n : nat) (A B : list nat),
    length A <= n -> NoDup A -> NoDup B -> HallCond adj A B ->
    exists M, Pairing adj A B M.
Proof.
  intros adj n; induction n as [|n IHn]; intros A B Hlen HndA HndB Hhall.
  - destruct A as [|a A'];
      [exists []; apply Pairing_nil | simpl in Hlen; lia].
  - destruct A as [|a A']; [exists []; apply Pairing_nil|].
    destruct (find (fun S => (1 <=? length S)
                             && (length S <? length (a :: A'))
                             && (length (nbhd adj S B) <=? length S))
                   (sublists (a :: A'))) as [S0|] eqn:Efind.
    + apply find_some in Efind. destruct Efind as [HS0in Hb].
      apply andb_true_iff in Hb as [Hb12 Hb3].
      apply andb_true_iff in Hb12 as [Hb1 Hb2].
      apply Nat.leb_le in Hb1. apply Nat.ltb_lt in Hb2. apply Nat.leb_le in Hb3.
      apply (hall_critical adj n IHn (a :: A') B S0); auto.
      * apply sublists_incl; exact HS0in.
      * eapply sublists_NoDup_members; [exact HndA | exact HS0in].
      * destruct S0; [simpl in Hb1; lia | discriminate].
    + pose proof (find_none _ _ Efind) as Hnone.
      assert (Hsub : forall S, In S (sublists (a :: A')) -> S <> [] ->
                               length S < length (a :: A') ->
                               length S < length (nbhd adj S B)).
      { intros S HS Hne Hlt. specialize (Hnone S HS).
        apply andb_false_iff in Hnone. destruct Hnone as [H12 | H3].
        - apply andb_false_iff in H12 as [Hf1 | Hf2].
          + apply Nat.leb_nle in Hf1. destruct S; [congruence | simpl in Hf1; lia].
          + apply Nat.ltb_nlt in Hf2. lia.
        - apply Nat.leb_nle in H3. lia. }
      pose proof (no_critical_strong adj (a :: A') B HndA Hsub) as Hstrong.
      apply (hall_noncritical adj n IHn a A' B); auto.
Qed.

Theorem hall_abstract :
  forall (adj : nat -> nat -> bool) (A B : list nat),
    NoDup A -> NoDup B -> HallCond adj A B ->
    exists M, Pairing adj A B M.
Proof.
  intros adj A B HndA HndB Hhall.
  apply (hall_abstract_aux adj (length A) A B); auto.
Qed.
