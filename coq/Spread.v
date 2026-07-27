(** * Spread.v -- The spread framework: definitions and machinery.

    The 2020 breakthrough on the Sunflower Conjecture (Alweiss–Lovett–
    Wu–Zhang, with the Rao / Frankston–Kahn–Narayanan–Park /
    Bell–Chueluecha–Warnke refinements) replaced the
    [(k-1)^n · n!] Erdős–Rado bound with [(C k log n)^n]. The argument
    has two clearly separated halves:

    - a *deterministic* reduction: "every [r]-spread family of small
      sets contains [k] pairwise disjoint members" implies
      "[f(n,k) ≤ r^n + 1]";
    - the *spread lemma* itself, which supplies the hypothesis of that
      reduction with [r = Θ(k log n)].

    This file develops the machinery for the first half — the notion of
    an [r]-spread family, a decision procedure that either certifies
    spreadness or produces a violating set, the *link* construction
    that strips a violating set out of a family, and a set-indexed
    generalisation of [Sunflower.sunflower_lift]. Everything here is
    axiom-free.

    [SpreadReduction.v] assembles these into the reduction theorem and
    instantiates it with an elementary, fully proved spread lemma.
    [ALWZ.v] instantiates it with the published 2020 spread lemma,
    which is the development's only axiom.

    *** A correctness note on the previous version of this file

    Earlier revisions defined spreadness by quantifying over *all*
    lists [T], including lists with repeated entries. That definition
    is degenerate: [w_spread_legacy_degenerate] below shows that for
    any [w ≥ 2] it forces every member of the family to be empty, so no
    interesting family is ever "spread" in that sense. The fix —
    quantifying over [NoDup] lists, i.e. over genuine finite sets — is
    what [Spread] does. The degenerate definition is kept here, with
    its refutation, as a record of the defect. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower Pigeonhole.
Import ListNotations.

Set Implicit Arguments.

(** ** Containment and degree *)

(** [containsb T A] decides [T ⊆ A]. *)

Definition containsb (T A : list nat) : bool :=
  forallb (fun x => memb x A) T.

Lemma containsb_true_iff : forall T A, containsb T A = true <-> Subset T A.
Proof.
  intros T A; unfold containsb, Subset; split.
  - intros H x Hx. rewrite forallb_forall in H.
    apply memb_true_iff, H, Hx.
  - intros H. apply forallb_forall. intros x Hx.
    apply memb_true_iff, H, Hx.
Qed.

Lemma containsb_nil : forall A, containsb [] A = true.
Proof. reflexivity. Qed.

(** [deg T F] is the number of members of [F] that contain [T] — the
    quantity the spread condition bounds. *)

Definition deg (T : list nat) (F : Family) : nat :=
  length (filter (containsb T) F).

Lemma filter_ext_eq :
  forall {A : Type} (f g : A -> bool) (l : list A),
    (forall a, f a = g a) -> filter f l = filter g l.
Proof.
  intros A f g l H; induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite H, IH; reflexivity.
Qed.

Lemma deg_nil : forall F, deg [] F = length F.
Proof.
  intros F; unfold deg.
  induction F as [|A F IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma deg_le : forall T F, deg T F <= length F.
Proof. intros T F; unfold deg; apply length_filter_le. Qed.

(** [deg] depends on [T] only through its underlying set. *)

Lemma deg_setEq : forall T T' F,
    Subset T T' -> Subset T' T -> deg T F = deg T' F.
Proof.
  intros T T' F H1 H2; unfold deg; f_equal.
  apply filter_ext_eq; intros A.
  destruct (containsb T A) eqn:E1; destruct (containsb T' A) eqn:E2;
    try reflexivity.
  - exfalso.
    rewrite containsb_true_iff in E1.
    assert (E3 : containsb T' A = true)
        by (apply containsb_true_iff; intros x Hx; apply E1, H2, Hx).
    congruence.
  - exfalso.
    rewrite containsb_true_iff in E2.
    assert (E3 : containsb T A = true)
        by (apply containsb_true_iff; intros x Hx; apply E2, H1, Hx).
    congruence.
Qed.

Lemma deg_single : forall x F,
    deg [x] F = length (filter (fun A => memb x A) F).
Proof.
  intros x F; unfold deg; f_equal; apply filter_ext_eq; intros A.
  unfold containsb; simpl; apply Bool.andb_true_r.
Qed.

Lemma deg_pos_of_in : forall T A F,
    In A F -> Subset T A -> 1 <= deg T F.
Proof.
  intros T A F HA HTA; unfold deg.
  assert (Hin : In A (filter (containsb T) F)).
  { apply filter_In; split; [exact HA | apply containsb_true_iff; exact HTA]. }
  destruct (filter (containsb T) F) as [|B L]; simpl; [inversion Hin | lia].
Qed.

(** ** Spread families

    [F] is [r]-spread when no finite set [T] is contained in more than
    a [r^{-|T|}] fraction of the members of [F]. *)

Definition Spread (F : Family) (r : nat) : Prop :=
  forall T : list nat, NoDup T -> r ^ (length T) * deg T F <= length F.

Lemma Spread_mono : forall F r r',
    Spread F r -> r' <= r -> Spread F r'.
Proof.
  intros F r r' Hs Hle T HT.
  specialize (Hs T HT).
  pose proof (Nat.pow_le_mono_l r' r (length T) Hle) as Hpow.
  nia.
Qed.

(** *** The degenerate definition, and its refutation

    Dropping the [NoDup] requirement makes the definition vacuous: the
    lists [x; x; ...; x] force [r^t · deg{x} ≤ |F|] for every [t], so
    no member may contain any element at all. *)

Definition w_spread_legacy (F : Family) (w : nat) : Prop :=
  forall T : list nat, w ^ (length T) * deg T F <= length F.

Lemma deg_repeat : forall x t F,
    deg (repeat x (S t)) F = deg [x] F.
Proof.
  intros x t F; apply deg_setEq; intros y Hy.
  - apply repeat_spec in Hy; subst y; left; reflexivity.
  - destruct Hy as [E | []]; subst y.
    simpl; left; reflexivity.
Qed.

Theorem w_spread_legacy_degenerate :
  forall F w, 2 <= w -> w_spread_legacy F w ->
    Forall (fun A : list nat => A = []) F.
Proof.
  intros F w Hw Hleg.
  apply Forall_forall; intros A HA.
  destruct A as [|x A']; [reflexivity|].
  exfalso.
  (* [x] lies in at least one member, so deg [x] F >= 1 *)
  assert (Hdeg : 1 <= deg [x] F).
  { apply deg_pos_of_in with (A := x :: A'); [exact HA|].
    intros y Hy; destruct Hy as [E | []]; subst y; left; reflexivity. }
  assert (HFpos : 1 <= length F).
  { destruct F as [|B L]; simpl; [inversion HA | lia]. }
  destruct (length F) as [|t'] eqn:Ht; [lia|].
  specialize (Hleg (repeat x (S t'))).
  rewrite repeat_length, deg_repeat, Ht in Hleg.
  assert (H2 : 2 ^ (S t') <= w ^ (S t')) by (apply Nat.pow_le_mono_l; lia).
  assert (Hlin : S t' < 2 ^ (S t')) by (apply Nat.pow_gt_lin_r; lia).
  nia.
Qed.

(** ** Enumerating candidate violators

    To decide spreadness constructively we need a finite list of
    candidate sets [T]. Only sets contained in some member of [F] can
    have positive degree, so the sublists of members suffice. *)

Fixpoint subsets (l : list nat) : list (list nat) :=
  match l with
  | [] => [[]]
  | x :: l' => map (cons x) (subsets l') ++ subsets l'
  end.

Lemma filter_in_subsets :
  forall (p : nat -> bool) (l : list nat), In (filter p l) (subsets l).
Proof.
  intros p l; induction l as [|x l IH]; simpl; [left; reflexivity|].
  destruct (p x).
  - apply in_or_app; left. apply in_map; exact IH.
  - apply in_or_app; right; exact IH.
Qed.

Lemma subsets_incl :
  forall (l T : list nat), In T (subsets l) -> Subset T l.
Proof.
  intros l; induction l as [|x l IH]; intros T HT; simpl in HT.
  - destruct HT as [E | []]; subst T; apply Subset_nil.
  - apply in_app_or in HT as [HT | HT].
    + apply in_map_iff in HT as [T0 [E HT0]]; subst T.
      intros y Hy; simpl in Hy; destruct Hy as [E | Hy].
      * left; exact E.
      * right; apply (IH T0 HT0); exact Hy.
    + intros y Hy; right; apply (IH T HT); exact Hy.
Qed.

Lemma subsets_NoDup :
  forall (l T : list nat), NoDup l -> In T (subsets l) -> NoDup T.
Proof.
  intros l; induction l as [|x l IH]; intros T Hnd HT; simpl in HT.
  - destruct HT as [E | []]; subst T; constructor.
  - inversion Hnd as [|? ? Hxni Hnd']; subst.
    apply in_app_or in HT as [HT | HT].
    + apply in_map_iff in HT as [T0 [E HT0]]; subst T.
      constructor.
      * intro Hin. apply Hxni. apply (@subsets_incl l T0 HT0); exact Hin.
      * apply (IH T0 Hnd' HT0).
    + apply (IH T Hnd' HT).
Qed.

Definition cands (F : Family) : list (list nat) := concat (map subsets F).

Lemma in_cands_filter :
  forall (F : Family) (A : list nat) (p : nat -> bool),
    In A F -> In (filter p A) (cands F).
Proof.
  intros F A p HA; unfold cands.
  apply in_concat. exists (subsets A); split.
  - apply in_map; exact HA.
  - apply filter_in_subsets.
Qed.

Lemma in_cands_inv :
  forall (F : Family) (T : list nat),
    In T (cands F) -> exists A, In A F /\ In T (subsets A).
Proof.
  intros F T HT; unfold cands in HT.
  apply in_concat in HT as [L [HL HT]].
  apply in_map_iff in HL as [A [E HA]]; subst L.
  exists A; split; assumption.
Qed.

(** ** The spread decision procedure *)

Definition violatesb (F : Family) (r : nat) (T : list nat) : bool :=
  Nat.ltb (length F) (r ^ (length T) * deg T F).

Definition spread_witness (F : Family) (r : nat) : option (list nat) :=
  find (violatesb F r) (cands F).

Lemma spread_witness_some :
  forall F r T, spread_witness F r = Some T ->
    In T (cands F) /\ length F < r ^ (length T) * deg T F.
Proof.
  intros F r T H; unfold spread_witness in H.
  apply find_some in H as [Hin Hv].
  split; [exact Hin|].
  unfold violatesb in Hv; apply Nat.ltb_lt in Hv; exact Hv.
Qed.

(** The key completeness step: if no *sublist of a member* violates the
    spread condition, then no finite set does. Given an arbitrary
    [NoDup] set [T] of positive degree and a member [A] containing it,
    [filter (fun x => memb x T) A] is a sublist of [A] with exactly the
    same elements — hence the same length and the same degree. *)

Lemma spread_witness_none :
  forall F r,
    Forall (fun A : list nat => NoDup A) F ->
    spread_witness F r = None ->
    Spread F r.
Proof.
  intros F r Hnd Hnone T HT.
  unfold spread_witness in Hnone.
  destruct (deg T F) as [|d] eqn:Hdeg; [lia|].
  assert (Hex : exists A, In A F /\ Subset T A).
  { unfold deg in Hdeg.
    destruct (filter (containsb T) F) as [|A L] eqn:Ef; [simpl in Hdeg; lia|].
    assert (HA : In A (filter (containsb T) F))
      by (rewrite Ef; left; reflexivity).
    apply filter_In in HA as [HAF Hc].
    exists A; split; [exact HAF | apply containsb_true_iff; exact Hc]. }
  destruct Hex as [A [HAF HTA]].
  assert (HAnd : NoDup A) by (rewrite Forall_forall in Hnd; apply Hnd, HAF).
  set (T' := filter (fun x => memb x T) A).
  assert (HTT' : Subset T T').
  { intros x Hx; unfold T'; apply filter_In; split;
      [apply HTA, Hx | apply memb_true_iff; exact Hx]. }
  assert (HT'T : Subset T' T).
  { intros x Hx; unfold T' in Hx; apply filter_In in Hx as [_ Hm].
    apply memb_true_iff; exact Hm. }
  assert (HT'nd : NoDup T') by (unfold T'; apply NoDup_filter; exact HAnd).
  assert (Hlen : length T' = length T).
  { assert (H1 : length T <= length T') by (apply NoDup_incl_length; assumption).
    assert (H2 : length T' <= length T) by (apply NoDup_incl_length; assumption).
    lia. }
  assert (Hdegeq : deg T' F = deg T F) by (apply deg_setEq; assumption).
  assert (HT'cand : In T' (cands F))
    by (unfold T'; apply in_cands_filter; exact HAF).
  pose proof (find_none _ _ Hnone T' HT'cand) as Hv.
  unfold violatesb in Hv.
  apply Nat.ltb_ge in Hv.
  rewrite Hlen, Hdegeq, Hdeg in Hv.
  exact Hv.
Qed.

(** A violating set is necessarily nonempty: the empty set never
    violates, since [deg [] F = |F|]. *)

Lemma violator_nonempty :
  forall F r T, length F < r ^ (length T) * deg T F -> T <> [].
Proof.
  intros F r T H E; subst T; simpl in H.
  rewrite deg_nil in H; lia.
Qed.

(** ** The link construction

    [link T F] strips [T] out of the members of [F] that contain it.
    It is [(m - |T|)]-uniform when [F] is [m]-uniform, has exactly
    [deg T F] members, and stays distinct. *)

Definition setminus (A T : list nat) : list nat :=
  filter (fun x => negb (memb x T)) A.

Lemma in_setminus_iff : forall x A T,
    In x (setminus A T) <-> In x A /\ ~ In x T.
Proof.
  intros x A T; unfold setminus; split.
  - intro H; apply filter_In in H as [HA Hn].
    apply Bool.negb_true_iff, memb_false_iff in Hn; split; assumption.
  - intros [HA Hn]; apply filter_In; split;
      [exact HA | apply Bool.negb_true_iff, memb_false_iff; exact Hn].
Qed.

Lemma setminus_NoDup : forall A T, NoDup A -> NoDup (setminus A T).
Proof. intros A T H; unfold setminus; apply NoDup_filter; exact H. Qed.

Lemma setminus_disjoint : forall A T, Disjoint (setminus A T) T.
Proof.
  intros A T x Hx HT; apply in_setminus_iff in Hx as [_ Hn]; contradiction.
Qed.

(** The elements of [A] that lie in [T] number exactly [|T|]. *)

Lemma length_filter_memb :
  forall A T, NoDup A -> NoDup T -> Subset T A ->
    length (filter (fun x => memb x T) A) = length T.
Proof.
  intros A T HA HT HTA.
  set (T' := filter (fun x => memb x T) A).
  assert (HTT' : Subset T T').
  { intros x Hx; unfold T'; apply filter_In; split;
      [apply HTA, Hx | apply memb_true_iff; exact Hx]. }
  assert (HT'T : Subset T' T).
  { intros x Hx; unfold T' in Hx; apply filter_In in Hx as [_ Hm].
    apply memb_true_iff; exact Hm. }
  assert (HT'nd : NoDup T') by (unfold T'; apply NoDup_filter; exact HA).
  assert (H1 : length T <= length T') by (apply NoDup_incl_length; assumption).
  assert (H2 : length T' <= length T) by (apply NoDup_incl_length; assumption).
  lia.
Qed.

Lemma length_setminus :
  forall A T, NoDup A -> NoDup T -> Subset T A ->
    length (setminus A T) = length A - length T.
Proof.
  intros A T HA HT HTA.
  pose proof (length_filter_partition (fun x => memb x T) A) as Hpart.
  pose proof (length_filter_memb HA HT HTA) as Hin.
  unfold setminus; lia.
Qed.

Definition link (T : list nat) (F : Family) : Family :=
  map (fun A => setminus A T) (filter (containsb T) F).

Lemma length_link : forall T F, length (link T F) = deg T F.
Proof. intros T F; unfold link, deg; apply map_length. Qed.

Lemma in_link_inv :
  forall T F B, In B (link T F) ->
    exists A, In A F /\ Subset T A /\ B = setminus A T.
Proof.
  intros T F B HB; unfold link in HB.
  apply in_map_iff in HB as [A [E HA]].
  apply filter_In in HA as [HAF Hc].
  exists A; repeat split;
    [exact HAF | apply containsb_true_iff; exact Hc | symmetry; exact E].
Qed.

Lemma link_uniform :
  forall m T F, Uniform m F -> NoDup T ->
    Uniform (m - length T) (link T F).
Proof.
  intros m T F HU HT; unfold Uniform in *.
  apply Forall_forall; intros B HB.
  apply in_link_inv in HB as [A [HAF [HTA E]]]; subst B.
  rewrite Forall_forall in HU.
  destruct (HU A HAF) as [HAlen HAnd].
  unfold UniformSet; split.
  - rewrite (length_setminus HAnd HT HTA), HAlen; reflexivity.
  - apply setminus_NoDup; exact HAnd.
Qed.

(** Distinctness survives: two members containing [T] that agree after
    removing [T] are set-equal. *)

Lemma link_distinct :
  forall T F, Distinct F -> Distinct (link T F).
Proof.
  intros T F HD; unfold Distinct, link in *.
  induction HD as [|A F HniA HD IH]; simpl; [constructor|].
  destruct (containsb T A) eqn:EA; simpl; [|exact IH].
  constructor; [|exact IH].
  intros B HB Hseq.
  apply in_map_iff in HB as [A' [E HA']].
  apply filter_In in HA' as [HA'F HcA'].
  subst B.
  apply containsb_true_iff in EA, HcA'.
  apply (HniA A' HA'F).
  unfold SetEq, Subset; split; intros y Hy.
  - destruct (in_dec_nat y T) as [HyT | HyT]; [apply HcA'; exact HyT|].
    assert (Hin : In y (setminus A T))
      by (apply in_setminus_iff; split; assumption).
    destruct Hseq as [Hs _]; apply Hs in Hin.
    apply in_setminus_iff in Hin; tauto.
  - destruct (in_dec_nat y T) as [HyT | HyT]; [apply EA; exact HyT|].
    assert (Hin : In y (setminus A' T))
      by (apply in_setminus_iff; split; assumption).
    destruct Hseq as [_ Hs]; apply Hs in Hin.
    apply in_setminus_iff in Hin; tauto.
Qed.

(** ** Lifting a sunflower across a link

    This generalises [Sunflower.sunflower_lift] from a single element
    to an arbitrary finite set [T]. *)

Definition add_set (T B : list nat) : list nat := T ++ setminus B T.

Lemma in_add_set_iff : forall x T B,
    In x (add_set T B) <-> In x T \/ In x B.
Proof.
  intros x T B; unfold add_set; split.
  - intro H; apply in_app_or in H as [H | H]; [left; exact H|].
    right; apply in_setminus_iff in H; tauto.
  - intros [H | H]; apply in_or_app; [left; exact H|].
    destruct (in_dec_nat x T) as [HT | HT]; [left; exact HT|].
    right; apply in_setminus_iff; split; assumption.
Qed.

(** Set algebra: [(T ∪ A) ∩ (T ∪ B) = T ∪ (A ∩ B)]. *)

Lemma inter_add_set : forall T A B,
    SetEq (inter (add_set T A) (add_set T B)) (add_set T (inter A B)).
Proof.
  intros T A B; unfold SetEq, Subset; split; intros y Hy.
  - apply in_inter_iff in Hy as [H1 H2].
    apply in_add_set_iff in H1, H2.
    apply in_add_set_iff.
    destruct H1 as [HT | HA]; [left; exact HT|].
    destruct H2 as [HT | HB]; [left; exact HT|].
    right; apply in_inter_iff; split; assumption.
  - apply in_add_set_iff in Hy.
    apply in_inter_iff.
    destruct Hy as [HT | Hi].
    + split; apply in_add_set_iff; left; exact HT.
    + apply in_inter_iff in Hi as [HA HB].
      split; apply in_add_set_iff; right; assumption.
Qed.

Lemma SetNoDup_map_add_set :
  forall T S,
    Forall (fun B : list nat => Disjoint B T) S ->
    SetNoDup S ->
    SetNoDup (map (add_set T) S).
Proof.
  intros T S Hdis Hsnd.
  induction Hsnd as [|A S HniA HsndS IH]; simpl; [constructor|].
  inversion Hdis as [|? ? HdisA Hdis']; subst.
  constructor.
  - intros B HB Hseq.
    apply in_map_iff in HB as [A' [E HA']]; subst B.
    rewrite Forall_forall in Hdis'.
    pose proof (Hdis' A' HA') as HdisA'.
    apply (HniA A' HA').
    unfold SetEq, Subset; split; intros y Hy.
    + assert (Hin : In y (add_set T A))
        by (apply in_add_set_iff; right; exact Hy).
      destruct Hseq as [Hs _]; apply Hs in Hin.
      apply in_add_set_iff in Hin as [HT | HA'y]; [|exact HA'y].
      exfalso; apply (HdisA y); assumption.
    + assert (Hin : In y (add_set T A'))
        by (apply in_add_set_iff; right; exact Hy).
      destruct Hseq as [_ Hs]; apply Hs in Hin.
      apply in_add_set_iff in Hin as [HT | HAy]; [|exact HAy].
      exfalso; apply (HdisA' y); assumption.
  - apply IH; exact Hdis'.
Qed.

Theorem sunflower_lift_set :
  forall (T : list nat) (S : list (list nat)) (core : list nat),
    Forall (fun B : list nat => Disjoint B T) S ->
    Sunflower S core ->
    Sunflower (map (add_set T) S) (add_set T core).
Proof.
  intros T S core Hdis [Hsnd Hcore].
  split; [apply SetNoDup_map_add_set; assumption|].
  intros U V HU HV Hne.
  apply in_map_iff in HU as [A [EA HA]].
  apply in_map_iff in HV as [B [EB HB]].
  subst U V.
  assert (HAB : A <> B) by (intro E; subst B; apply Hne; reflexivity).
  eapply SetEq_trans; [apply inter_add_set|].
  pose proof (Hcore _ _ HA HB HAB) as Hc.
  unfold SetEq, Subset; split; intros y Hy;
    apply in_add_set_iff in Hy; apply in_add_set_iff;
    destruct Hy as [HT | Hi]; try (left; exact HT); right;
    apply Hc; exact Hi.
Qed.

(** A [k]-sunflower in the link yields a [k]-sunflower in the original
    family, with [T] merged into the core. *)

Theorem link_sunflower_lift :
  forall T F k,
    ContainsKSunflower k (link T F) ->
    ContainsKSunflower k F.
Proof.
  intros T F k [S [Hsub [Hlen [core Hsun]]]].
  assert (Hdis : Forall (fun B : list nat => Disjoint B T) S).
  { apply Forall_forall; intros B HB.
    destruct (Hsub B HB) as [B' [HB' Hseq]].
    apply in_link_inv in HB' as [A [HAF [HTA E]]]; subst B'.
    intros y HyB HyT.
    destruct Hseq as [Hs _]; apply Hs in HyB.
    apply in_setminus_iff in HyB; tauto. }
  exists (map (add_set T) S); split.
  - intros W HW.
    apply in_map_iff in HW as [B [E HB]]; subst W.
    destruct (Hsub B HB) as [B' [HB' Hseq]].
    apply in_link_inv in HB' as [A [HAF [HTA EA]]]; subst B'.
    exists A; split; [exact HAF|].
    unfold SetEq, Subset; split; intros y Hy.
    + apply in_add_set_iff in Hy as [HT | HyB].
      * apply HTA; exact HT.
      * destruct Hseq as [Hs _]; apply Hs in HyB.
        apply in_setminus_iff in HyB; tauto.
    + apply in_add_set_iff.
      destruct (in_dec_nat y T) as [HT | HT]; [left; exact HT|].
      right. destruct Hseq as [_ Hs]; apply Hs.
      apply in_setminus_iff; split; assumption.
  - split.
    + rewrite map_length; exact Hlen.
    + exists (add_set T core); apply sunflower_lift_set; assumption.
Qed.
