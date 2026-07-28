(** * F23.v -- The exact small case f(2, 3) = 7.

    The first nontrivial exact sunflower number:

        [UpperBound 2 3 7]  and  [~ UpperBound 2 3 6],

    i.e. every family of 7 distinct 2-element sets contains a
    3-sunflower and some family of 6 does not ([k = 3] is the case
    Erdős singled out as containing "the whole difficulty" of the
    conjecture; compare the boundary cases in [SmallCases.v]).

    Upper bound, by counting: a 2-uniform family without a
    3-sunflower has no vertex in three members (sunflower with core
    [[v]]) and no three pairwise-disjoint members (empty-core
    sunflower).  Pick a member [e1]; if some member [e2] avoids it,
    every member meets the 4-vertex set [e1 ++ e2], and double
    counting incidences (at most 2 per vertex, at least 1 per member
    and 2 each for [e1], [e2]) gives [|F| + 2 <= 8], so [|F| <= 6].
    If no member avoids [e1], the same count over [e1]'s 2 vertices
    gives [|F| <= 3].

    Lower bound: two disjoint triangles
    [{0,1}, {1,2}, {0,2}, {3,4}, {4,5}, {3,5}], verified by a
    reflective boolean 3-sunflower detector ([sunflower3b], complete
    w.r.t. [ContainsKSunflower 3] via the witness canonicalisation
    of [ProductLowerBound.v]) evaluating to [false] by [vm_compute].

    The value f(2,3) = 7 is classical (folklore; cf. Abbott-Hanson,
    "On finite Delta-systems", Discrete Math. 8 (1974)).

    Zero axioms, zero admits; [Print Assumptions f_2_3_eq_7] reports
    "Closed under the global context". *)

From Coq Require Import List Arith Lia Bool.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower LowerBound ProductLowerBound Reflect
     TwoUniform.
Import ListNotations.

(** ** Boolean certificates

    The generic certificates ([nodupb], [uniformb], [distinctb], and
    their [iff] correctness lemmas) live in [Reflect.v]; only the
    3-sunflower detector, which is specific to this file, is defined
    here. *)

(** A boolean 3-sunflower detector, complete with respect to
    [ContainsKSunflower 3]: any abstract 3-sunflower canonicalises
    (via [contains_sunflower_literal]) to a literal triple of
    pairwise non-set-equal members whose pairwise intersections are
    mutually set-equal, which the detector finds. *)

Definition sunflower_tripleb (A B C : list nat) : bool :=
  negb (seteqb A B) && negb (seteqb A C) && negb (seteqb B C)
  && seteqb (inter A B) (inter A C) && seteqb (inter A B) (inter B C).

Definition sunflower3b (F : Family) : bool :=
  existsb (fun A =>
    existsb (fun B =>
      existsb (fun C => sunflower_tripleb A B C) F) F) F.

Lemma sunflower3b_sound :
  forall F, ContainsKSunflower 3 F -> sunflower3b F = true.
Proof.
  intros F Hc.
  destruct (contains_sunflower_literal 3 F Hc)
    as [S [core [Hincl [Hnd [Hlen Hsun]]]]].
  destruct S as [|A [|B [|C [|D S']]]]; simpl in Hlen; try discriminate.
  assert (HA : In A F) by (apply Hincl; left; reflexivity).
  assert (HB : In B F) by (apply Hincl; right; left; reflexivity).
  assert (HC : In C F) by (apply Hincl; right; right; left; reflexivity).
  inversion Hnd as [|? ? HniA HndBC]; subst.
  inversion HndBC as [|? ? HniB HndC]; subst.
  assert (HAB : A <> B) by (intro E; subst; apply HniA; left; reflexivity).
  assert (HAC : A <> C)
    by (intro E; subst; apply HniA; right; left; reflexivity).
  assert (HBC : B <> C) by (intro E; subst; apply HniB; left; reflexivity).
  destruct Hsun as [Hsnd Hcore].
  assert (inA : In A [A; B; C]) by (left; reflexivity).
  assert (inB : In B [A; B; C]) by (right; left; reflexivity).
  assert (inC : In C [A; B; C]) by (right; right; left; reflexivity).
  pose proof (Hcore A B inA inB HAB) as HcAB.
  pose proof (Hcore A C inA inC HAC) as HcAC.
  pose proof (Hcore B C inB inC HBC) as HcBC.
  pose proof (@SetNoDup_pairwise _ Hsnd A B inA inB HAB) as HnsAB.
  pose proof (@SetNoDup_pairwise _ Hsnd A C inA inC HAC) as HnsAC.
  pose proof (@SetNoDup_pairwise _ Hsnd B C inB inC HBC) as HnsBC.
  apply existsb_exists. exists A. split; [exact HA|].
  apply existsb_exists. exists B. split; [exact HB|].
  apply existsb_exists. exists C. split; [exact HC|].
  unfold sunflower_tripleb.
  assert (E1 : seteqb A B = false).
  { destruct (seteqb A B) eqn:E; [|reflexivity].
    exfalso; apply HnsAB; apply seteqb_correct; exact E. }
  assert (E2 : seteqb A C = false).
  { destruct (seteqb A C) eqn:E; [|reflexivity].
    exfalso; apply HnsAC; apply seteqb_correct; exact E. }
  assert (E3 : seteqb B C = false).
  { destruct (seteqb B C) eqn:E; [|reflexivity].
    exfalso; apply HnsBC; apply seteqb_correct; exact E. }
  assert (E4 : seteqb (inter A B) (inter A C) = true).
  { apply seteqb_correct.
    eapply SetEq_trans; [exact HcAB | apply SetEq_sym; exact HcAC]. }
  assert (E5 : seteqb (inter A B) (inter B C) = true).
  { apply seteqb_correct.
    eapply SetEq_trans; [exact HcAB | apply SetEq_sym; exact HcBC]. }
  rewrite E1, E2, E3, E4, E5. reflexivity.
Qed.

(** ** Structure of 2-element sets

    [two_set_shape], [two_set_other] and [inter_two_sets_common] were
    local to this file; they are the general shape lemmas at uniformity
    2, so they now live in [TwoUniform.v] alongside the sunflower
    characterisation that uses them. *)

(** ** Three members through one vertex give a sunflower

    An instance of [TwoUniform.star_sunflower]: any number of distinct
    2-sets through a common point are a sunflower with that point as
    core. Before that lemma existed this was sixty lines of pairwise
    case analysis, all of it the [k = 3] special case of one general
    argument. *)

Lemma three_through_vertex_sunflower :
  forall (F : Family) (v : nat) (g1 g2 g3 : list nat),
    Uniform 2 F -> Distinct F ->
    In g1 F -> In g2 F -> In g3 F ->
    g1 <> g2 -> g1 <> g3 -> g2 <> g3 ->
    In v g1 -> In v g2 -> In v g3 ->
    ContainsKSunflower 3 F.
Proof.
  intros F v g1 g2 g3 HU HD H1 H2 H3 H12 H13 H23 Hv1 Hv2 Hv3.
  assert (Hincl : incl [g1; g2; g3] F).
  { intros x [E | [E | [E | []]]]; subst x; assumption. }
  assert (Hnd : NoDup [g1; g2; g3]).
  { constructor; [intros [E | [E | []]]; congruence |].
    constructor; [intros [E | []]; congruence |].
    constructor; [intros [] | constructor]. }
  eapply ContainsKSunflower_of_incl; [exact Hincl | reflexivity |].
  apply star_sunflower.
  - apply Forall_forall; intros A HA.
    unfold Uniform in HU; rewrite Forall_forall in HU.
    apply HU, Hincl, HA.
  - exact (SetNoDup_incl HD Hnd Hincl).
  - constructor; [exact Hv1|]. constructor; [exact Hv2|].
    constructor; [exact Hv3 | constructor].
Qed.

(** ** Three pairwise-disjoint members give a sunflower *)

Lemma three_disjoint_sunflower :
  forall (F : Family) (e1 e2 e3 : list nat),
    Uniform 2 F ->
    In e1 F -> In e2 F -> In e3 F ->
    Disjoint e1 e2 -> Disjoint e1 e3 -> Disjoint e2 e3 ->
    ContainsKSunflower 3 F.
Proof.
  intros F e1 e2 e3 HU H1 H2 H3 D12 D13 D23.
  assert (HUm : forall g, In g F -> length g = 2 /\ NoDup g).
  { unfold Uniform in HU. rewrite Forall_forall in HU.
    intros g Hg. exact (HU g Hg). }
  destruct (HUm e1 H1) as [Hl1 _].
  destruct (HUm e2 H2) as [Hl2 _].
  destruct (HUm e3 H3) as [Hl3 _].
  assert (Hne1 : e1 <> [])
    by (intro E; rewrite E in Hl1; simpl in Hl1; discriminate).
  assert (Hne2 : e2 <> [])
    by (intro E; rewrite E in Hl2; simpl in Hl2; discriminate).
  assert (Hne3 : e3 <> [])
    by (intro E; rewrite E in Hl3; simpl in Hl3; discriminate).
  assert (He12 : e1 <> e2).
  { intro E. destruct e1 as [|x r]; [apply Hne1; reflexivity|].
    apply (D12 x); [left; reflexivity | rewrite <- E; left; reflexivity]. }
  assert (He13 : e1 <> e3).
  { intro E. destruct e1 as [|x r]; [apply Hne1; reflexivity|].
    apply (D13 x); [left; reflexivity | rewrite <- E; left; reflexivity]. }
  assert (He23 : e2 <> e3).
  { intro E. destruct e2 as [|x r]; [apply Hne2; reflexivity|].
    apply (D23 x); [left; reflexivity | rewrite <- E; left; reflexivity]. }
  exists [e1; e2; e3]. split.
  - apply SubFamilySetEq_incl. intros x Hx.
    destruct Hx as [E | [E | [E | []]]]; subst x; assumption.
  - apply k_pairwise_disjoint_sunflower.
    + constructor.
      * intro HxIn. destruct HxIn as [E | [E | []]];
          [apply He12; symmetry; exact E | apply He13; symmetry; exact E].
      * constructor.
        -- intro HxIn. destruct HxIn as [E | []].
           apply He23; symmetry; exact E.
        -- constructor; [intros [] | constructor].
    + reflexivity.
    + intros A B HA HB Hne.
      destruct HA as [EA | [EA | [EA | []]]];
        destruct HB as [EB | [EB | [EB | []]]]; subst A B;
        try (exfalso; apply Hne; reflexivity);
        [ exact D12 | exact D13
        | exact (@Disjoint_sym _ _ D12) | exact D23
        | exact (@Disjoint_sym _ _ D13) | exact (@Disjoint_sym _ _ D23) ].
Qed.

(** ** Counting helpers *)

Lemma list_sum_map_add :
  forall (X : Type) (f g : X -> nat) (l : list X),
    list_sum (map (fun x => f x + g x) l)
    = list_sum (map f l) + list_sum (map g l).
Proof.
  intros X f g l; induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite IH; lia.
Qed.

Lemma sum_indicator :
  forall (v : nat) (F : Family),
    list_sum (map (fun g => if memb v g then 1 else 0) F)
    = length (filter (fun g => memb v g) F).
Proof.
  intros v F; induction F as [|g F IH]; simpl; [reflexivity|].
  destruct (memb v g); simpl; rewrite IH; reflexivity.
Qed.

Lemma double_count :
  forall (vs : list nat) (F : Family),
    list_sum (map (fun v => length (filter (fun g => memb v g) F)) vs)
    = list_sum (map (fun g => length (filter (fun v => memb v g) vs)) F).
Proof.
  induction vs as [|v vs IH]; intros F; simpl.
  - induction F as [|g F IHF]; simpl; [reflexivity | rewrite <- IHF; reflexivity].
  - rewrite IH.
    rewrite <- sum_indicator.
    rewrite <- list_sum_map_add.
    f_equal. apply map_ext_in.
    intros g _. simpl. destruct (memb v g); simpl; reflexivity.
Qed.

Lemma list_sum_bounded :
  forall (X : Type) (f : X -> nat) (l : list X) (c : nat),
    (forall x, In x l -> f x <= c) ->
    list_sum (map f l) <= c * length l.
Proof.
  intros X f l c H; induction l as [|x l IH]; simpl; [lia|].
  pose proof (H x (or_introl eq_refl)).
  assert (list_sum (map f l) <= c * length l)
    by (apply IH; intros y Hy; apply H; right; exact Hy).
  lia.
Qed.

Lemma list_sum_all_ge_1 :
  forall (f : list nat -> nat) (F : Family),
    (forall g, In g F -> 1 <= f g) ->
    length F <= list_sum (map f F).
Proof.
  intros f F H; induction F as [|g F IH]; simpl; [lia|].
  pose proof (H g (or_introl eq_refl)).
  assert (length F <= list_sum (map f F))
    by (apply IH; intros h Hh; apply H; right; exact Hh).
  lia.
Qed.

Lemma list_sum_split_at :
  forall (f : list nat -> nat) (F1 F2 : Family) (g : list nat),
    list_sum (map f (F1 ++ g :: F2))
    = f g + list_sum (map f (F1 ++ F2)).
Proof.
  intros f F1 F2 g.
  rewrite !map_app. simpl. rewrite !list_sum_app. simpl. lia.
Qed.

Lemma list_sum_one_heavy :
  forall (f : list nat -> nat) (F : Family) (g1 : list nat),
    In g1 F ->
    (forall g, In g F -> 1 <= f g) ->
    2 <= f g1 ->
    length F + 1 <= list_sum (map f F).
Proof.
  intros f F g1 Hin Hall H2.
  destruct (in_split g1 F Hin) as [F1 [F2 E]]. subst F.
  rewrite list_sum_split_at.
  assert (Hge : length (F1 ++ F2) <= list_sum (map f (F1 ++ F2))).
  { apply list_sum_all_ge_1. intros g Hg. apply Hall.
    apply in_app_or in Hg as [Hg | Hg]; apply in_or_app;
      [left; exact Hg | right; right; exact Hg]. }
  rewrite !app_length in *. simpl. lia.
Qed.

Lemma list_sum_two_heavy :
  forall (f : list nat -> nat) (F : Family) (g1 g2 : list nat),
    In g1 F -> In g2 F -> g1 <> g2 ->
    (forall g, In g F -> 1 <= f g) ->
    2 <= f g1 -> 2 <= f g2 ->
    length F + 2 <= list_sum (map f F).
Proof.
  intros f F g1 g2 H1 H2 Hne Hall Hf1 Hf2.
  destruct (in_split g1 F H1) as [F1 [F2 E]]. subst F.
  rewrite list_sum_split_at.
  assert (H2' : In g2 (F1 ++ F2)).
  { apply in_app_or in H2 as [Hg | Hg]; [apply in_or_app; left; exact Hg|].
    destruct Hg as [E | Hg];
      [exfalso; apply Hne; exact E
      | apply in_or_app; right; exact Hg]. }
  assert (Hrest : length (F1 ++ F2) + 1 <= list_sum (map f (F1 ++ F2))).
  { apply (list_sum_one_heavy f (F1 ++ F2) g2); auto.
    intros g Hg. apply Hall.
    apply in_app_or in Hg as [Hg | Hg]; apply in_or_app;
      [left; exact Hg | right; right; exact Hg]. }
  rewrite !app_length in *. simpl. lia.
Qed.

Lemma filter_length_ge1 :
  forall (f : nat -> bool) (vs : list nat) (a : nat),
    In a vs -> f a = true -> 1 <= length (filter f vs).
Proof.
  intros f vs a Hin Hf.
  assert (Ha : In a (filter f vs)) by (apply filter_In; auto).
  destruct (filter f vs); [inversion Ha | simpl; lia].
Qed.

Lemma filter_length_ge2 :
  forall (f : nat -> bool) (vs : list nat) (a b : nat),
    NoDup vs -> In a vs -> In b vs -> a <> b ->
    f a = true -> f b = true ->
    2 <= length (filter f vs).
Proof.
  intros f vs a b Hnd Ha Hb Hab Hfa Hfb.
  assert (Hincl : incl [a; b] (filter f vs)).
  { intros x [E | [E | []]]; subst; apply filter_In; auto. }
  assert (Hnd2 : NoDup [a; b]).
  { constructor.
    - intro Hx. destruct Hx as [E | []]. apply Hab; symmetry; exact E.
    - constructor; [intros [] | constructor]. }
  pose proof (NoDup_incl_length Hnd2 Hincl) as Hle.
  simpl in Hle. lia.
Qed.

(** ** The upper bound: [f(2, 3) <= 7] *)

Theorem f_2_3_upper : UpperBound 2 3 7.
Proof.
  intros F HU HD Hlen.
  assert (HUm : forall g, In g F -> length g = 2 /\ NoDup g).
  { unfold Uniform in HU. rewrite Forall_forall in HU.
    intros g Hg. exact (HU g Hg). }
  assert (HndF : NoDup F) by (apply SetNoDup_NoDup; exact HD).
  (* Case split: some vertex lies in three members. *)
  destruct (existsb (fun v => 3 <=? length (filter (fun g => memb v g) F))
                    (concat F)) eqn:Edeg.
  { apply existsb_exists in Edeg as [v [Hvin Hvdeg]].
    apply Nat.leb_le in Hvdeg.
    assert (Hnfil : NoDup (filter (fun g => memb v g) F))
      by (apply NoDup_filter; exact HndF).
    destruct (filter (fun g => memb v g) F) as [|g1 [|g2 [|g3 rest]]] eqn:Efil;
      simpl in Hvdeg; try lia.
    inversion Hnfil as [|? ? Hni1 Hnd1]; subst.
    inversion Hnd1 as [|? ? Hni2 Hnd2]; subst.
    assert (Hg1' : In g1 (filter (fun g => memb v g) F))
      by (rewrite Efil; left; reflexivity).
    assert (Hg2' : In g2 (filter (fun g => memb v g) F))
      by (rewrite Efil; right; left; reflexivity).
    assert (Hg3' : In g3 (filter (fun g => memb v g) F))
      by (rewrite Efil; right; right; left; reflexivity).
    apply filter_In in Hg1' as [Hg1F Hg1v].
    apply filter_In in Hg2' as [Hg2F Hg2v].
    apply filter_In in Hg3' as [Hg3F Hg3v].
    assert (H12 : g1 <> g2)
      by (intro E; subst; apply Hni1; left; reflexivity).
    assert (H13 : g1 <> g3)
      by (intro E; subst; apply Hni1; right; left; reflexivity).
    assert (H23 : g2 <> g3)
      by (intro E; subst; apply Hni2; left; reflexivity).
    apply (three_through_vertex_sunflower F v g1 g2 g3); auto;
      apply memb_true_iff; assumption. }
  (* Every vertex lies in at most two members. *)
  assert (Hdeg2 : forall v, In v (concat F) ->
                  length (filter (fun g => memb v g) F) <= 2).
  { intros v Hv.
    destruct (3 <=? length (filter (fun g => memb v g) F)) eqn:E3.
    - exfalso.
      assert (Et : existsb (fun v => 3 <=? length (filter (fun g => memb v g) F))
                           (concat F) = true)
        by (apply existsb_exists; exists v; auto).
      congruence.
    - apply Nat.leb_gt in E3. lia. }
  destruct F as [|e1 F0]; [simpl in Hlen; lia|].
  assert (He1 : In e1 (e1 :: F0)) by (left; reflexivity).
  destruct (HUm e1 He1) as [Hle1 Hnde1].
  destruct (two_set_shape e1 Hle1 Hnde1) as [a [b [Hab Ee1]]].
  destruct (find (fun g => disjointb e1 g) (e1 :: F0)) as [e2|] eqn:Efind2.
  - (* A member disjoint from e1 exists. *)
    apply find_some in Efind2 as [He2 Hdisb].
    apply disjointb_correct in Hdisb.
    destruct (HUm e2 He2) as [Hle2 Hnde2].
    destruct (two_set_shape e2 Hle2 Hnde2) as [c [d [Hcd Ee2]]].
    destruct (find (fun g => disjointb e1 g && disjointb e2 g) (e1 :: F0))
      as [e3|] eqn:Efind3.
    + apply find_some in Efind3 as [He3 Hb3].
      apply andb_true_iff in Hb3 as [Hb31 Hb32].
      apply disjointb_correct in Hb31. apply disjointb_correct in Hb32.
      apply (three_disjoint_sunflower (e1 :: F0) e1 e2 e3); auto.
    + (* No third disjoint member: count incidences on e1 ++ e2. *)
      exfalso.
      pose proof (find_none _ _ Efind3) as Hmeet.
      set (vs := e1 ++ e2).
      assert (Hndvs : NoDup vs).
      { unfold vs.
        apply NoDup_app_intro; [exact Hnde1 | exact Hnde2 | exact Hdisb]. }
      assert (Hg_meets : forall g, In g (e1 :: F0) ->
                         exists x, In x vs /\ In x g).
      { intros g Hg. specialize (Hmeet g Hg).
        apply andb_false_iff in Hmeet.
        destruct Hmeet as [Hf | Hf]; apply disjointb_false_iff in Hf;
          destruct Hf as [x [Hx1 Hx2]]; exists x;
          (split; [unfold vs; apply in_or_app | exact Hx2]);
          [left; exact Hx1 | right; exact Hx1]. }
      set (contrib := fun g => length (filter (fun x => memb x g) vs)).
      assert (Hc1 : forall g, In g (e1 :: F0) -> 1 <= contrib g).
      { intros g Hg. destruct (Hg_meets g Hg) as [x [Hxvs Hxg]].
        unfold contrib. apply (filter_length_ge1 _ vs x); auto.
        apply memb_true_iff; exact Hxg. }
      assert (Hc_e1 : 2 <= contrib e1).
      { unfold contrib. apply (filter_length_ge2 _ vs a b); auto.
        - unfold vs; apply in_or_app; left; rewrite Ee1; left; reflexivity.
        - unfold vs; apply in_or_app; left; rewrite Ee1;
            right; left; reflexivity.
        - apply memb_true_iff; rewrite Ee1; left; reflexivity.
        - apply memb_true_iff; rewrite Ee1; right; left; reflexivity. }
      assert (Hc_e2 : 2 <= contrib e2).
      { unfold contrib. apply (filter_length_ge2 _ vs c d); auto.
        - unfold vs; apply in_or_app; right; rewrite Ee2; left; reflexivity.
        - unfold vs; apply in_or_app; right; rewrite Ee2;
            right; left; reflexivity.
        - apply memb_true_iff; rewrite Ee2; left; reflexivity.
        - apply memb_true_iff; rewrite Ee2; right; left; reflexivity. }
      assert (He12 : e1 <> e2).
      { intro E. apply (Hdisb a).
        - rewrite Ee1; left; reflexivity.
        - rewrite <- E, Ee1; left; reflexivity. }
      pose proof (list_sum_two_heavy contrib (e1 :: F0) e1 e2
                    He1 He2 He12 Hc1 Hc_e1 Hc_e2) as Hlow.
      pose proof (double_count vs (e1 :: F0)) as Hdc.
      assert (Hhigh : list_sum
                        (map (fun v => length (filter (fun g => memb v g)
                                                      (e1 :: F0))) vs)
                      <= 2 * length vs).
      { apply (list_sum_bounded nat _ vs 2).
        intros v Hv. apply Hdeg2.
        unfold vs in Hv. apply in_app_or in Hv as [Hv | Hv];
          apply in_concat; [exists e1 | exists e2]; split; auto. }
      assert (Hvslen : length vs = 4).
      { unfold vs. rewrite app_length, Ee1, Ee2. reflexivity. }
      unfold contrib in Hlow. rewrite <- Hdc in Hlow. lia.
  - (* Every member meets e1: count incidences on e1 alone. *)
    exfalso.
    pose proof (find_none _ _ Efind2) as Hmeet.
    assert (Hg_meets : forall g, In g (e1 :: F0) ->
                       exists x, In x e1 /\ In x g).
    { intros g Hg. specialize (Hmeet g Hg).
      apply disjointb_false_iff in Hmeet. exact Hmeet. }
    set (contrib := fun g => length (filter (fun x => memb x g) e1)).
    assert (Hc1 : forall g, In g (e1 :: F0) -> 1 <= contrib g).
    { intros g Hg. destruct (Hg_meets g Hg) as [x [Hxe Hxg]].
      unfold contrib. apply (filter_length_ge1 _ e1 x); auto.
      apply memb_true_iff; exact Hxg. }
    assert (Hc_e1 : 2 <= contrib e1).
    { unfold contrib. apply (filter_length_ge2 _ e1 a b); auto.
      - rewrite Ee1; left; reflexivity.
      - rewrite Ee1; right; left; reflexivity.
      - apply memb_true_iff; rewrite Ee1; left; reflexivity.
      - apply memb_true_iff; rewrite Ee1; right; left; reflexivity. }
    pose proof (list_sum_one_heavy contrib (e1 :: F0) e1 He1 Hc1 Hc_e1)
      as Hlow.
    pose proof (double_count e1 (e1 :: F0)) as Hdc.
    assert (Hhigh : list_sum
                      (map (fun v => length (filter (fun g => memb v g)
                                                    (e1 :: F0))) e1)
                    <= 2 * length e1).
    { apply (list_sum_bounded nat _ e1 2).
      intros v Hv. apply Hdeg2.
      apply in_concat; exists e1; split; auto. }
    unfold contrib in Hlow. rewrite <- Hdc in Hlow. lia.
Qed.

(** ** The lower bound: two disjoint triangles *)

Definition two_triangles : Family :=
  [[0; 1]; [1; 2]; [0; 2]; [3; 4]; [4; 5]; [3; 5]].

Lemma two_triangles_uniform : Uniform 2 two_triangles.
Proof. apply uniformb_correct. reflexivity. Qed.

Lemma two_triangles_distinct : Distinct two_triangles.
Proof. apply distinctb_correct. reflexivity. Qed.

Lemma two_triangles_no_sunflower : ~ ContainsKSunflower 3 two_triangles.
Proof.
  intro Hc. apply sunflower3b_sound in Hc.
  vm_compute in Hc. discriminate.
Qed.

Theorem f_2_3_lower : LowerBound 2 3 6.
Proof.
  exists two_triangles.
  split; [exact two_triangles_uniform|].
  split; [exact two_triangles_distinct|].
  split; [simpl; lia | exact two_triangles_no_sunflower].
Qed.

Theorem not_upper_bound_2_3_6 : ~ UpperBound 2 3 6.
Proof.
  intro H. apply two_triangles_no_sunflower.
  apply H;
    [exact two_triangles_uniform | exact two_triangles_distinct | simpl; lia].
Qed.

(** ** The exact value: [f(2, 3) = 7] *)

Theorem f_2_3_eq_7 : UpperBound 2 3 7 /\ ~ UpperBound 2 3 6.
Proof. split; [exact f_2_3_upper | exact not_upper_bound_2_3_6]. Qed.
