(**
 * KoenigHall.v - Hall's and König's theorems for graphs
 *
 * Converts the abstract pairings of [HallCore.v] into
 * [Matching]s of [Matching.v] and proves, with zero
 * axioms:
 *
 *   - [hall_marriage_theorem]: a bipartite-split graph whose left
 *     part satisfies Hall's condition has a matching saturating the
 *     left part.  NOTE: the earlier axiomatised statement (in
 *     [Matching.v] prior to this file) quantified the
 *     Hall condition over all [incl S partA] lists WITHOUT [NoDup];
 *     duplicated-element lists make that hypothesis unsatisfiable
 *     for any nonempty [partA], so the axiom was degenerate.  The
 *     statement proved here adds the intended [NoDup S] guard and is
 *     otherwise identical.
 *
 *   - [koenig_theorem]: in a simple bipartite graph a maximum
 *     matching and a minimum vertex cover exist and have equal size.
 *     Proof via the deficiency version of Hall's theorem: with
 *     [d = max (|S| - |N(S)|)] over subsets of the left part, [d]
 *     fresh dummy right-vertices adjacent to everything restore
 *     Hall's condition, giving a matching of size [|A| - d] after
 *     deleting dummy edges; the cover [(A minus Sstar) ++ N(Sstar)]
 *     for a deficiency-maximising [Sstar] has the same size, and
 *     [matching_le_cover] (the easy direction, already proved in
 *     [Matching.v]) upgrades the pair to
 *     maximum-matching / minimum-cover.
 *
 * Citations:
 *   P. Hall. "On Representatives of Subsets." J. London Math. Soc.
 *   10 (1935), 26-30.
 *   D. König. "Gráfok és mátrixok." Matematikai és Fizikai Lapok 38
 *   (1931), 116-119.  Modern exposition: West, "Introduction to
 *   Graph Theory" (2001), §3.1.
 *
 * VERIFICATION STATUS: Machine-checked, zero admits, zero axioms.
 *)

Require Import List.
Require Import Arith.
Require Import Lia.
Require Import Bool.
Require Import PeanoNat.
From Sunflower Require Import Sets.
From Sunflower Require Import Graph.
From Sunflower Require Import Matching.
From Sunflower Require Import HallCore.

Import ListNotations.

(** ** Small helpers *)

Lemma filter_all_true :
  forall (X : Type) (f : X -> bool) (l : list X),
    (forall x, In x l -> f x = true) -> filter f l = l.
Proof.
  intros X f l H; induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite (H x (or_introl eq_refl)). f_equal.
  apply IH. intros y Hy; apply H; right; exact Hy.
Qed.

Lemma nbhd_nil_left : forall adj B, nbhd adj [] B = [].
Proof.
  intros adj B; unfold nbhd; induction B as [|b B IH]; simpl; auto.
Qed.

Lemma NoDup_map_filter :
  forall (X Y : Type) (f : X -> Y) (g : X -> bool) (l : list X),
    NoDup (map f l) -> NoDup (map f (filter g l)).
Proof.
  intros X Y f g l H; induction l as [|x l IH]; simpl; [constructor|].
  simpl in H. inversion H as [|? ? Hni Hnd]; subst.
  destruct (g x); simpl.
  - constructor; [|apply IH; exact Hnd].
    intro Hin. apply Hni.
    apply in_map_iff in Hin as [y [E Hy]].
    apply filter_In in Hy as [Hy _].
    apply in_map_iff. exists y; auto.
  - apply IH; exact Hnd.
Qed.

(** ** From pairings to graph matchings *)

Lemma in_concat_pairs :
  forall (M : list Edge) (x : nat),
    In x (concat (map edge_vertices M)) <->
    exists p, In p M /\ (x = fst p \/ x = snd p).
Proof.
  intros M x; split.
  - intro H. apply in_concat in H as [l [Hl Hx]].
    apply in_map_iff in Hl as [p [E Hp]]. subst l.
    destruct p as [u v]; simpl in Hx.
    exists (u, v); split; [exact Hp|].
    destruct Hx as [E | [E | []]]; subst; simpl; auto.
  - intros [p [Hp Hx]].
    apply (in_concat_map_edge p M); [exact Hp|].
    destruct p as [u v]; simpl in Hx.
    destruct Hx as [E | E]; subst; simpl; auto.
Qed.

Lemma pairing_matching :
  forall (G : Graph) (LA LB : list nat) (M : list (nat * nat)),
    (forall x, In x LA -> In x LB -> False) ->
    incl LA (vertices G) -> incl LB (vertices G) ->
    NoDup (map fst M) -> NoDup (map snd M) ->
    Forall (fun p => In (fst p) LA /\ In (snd p) LB /\
                     adjb G (fst p) (snd p) = true) M ->
    Matching G M.
Proof.
  intros G LA LB M Hdis HinclA HinclB Hf Hs Hall.
  split.
  - eapply Forall_impl; [|exact Hall].
    intros [u v] [HuA [HvB Hadj]]; simpl in *.
    unfold edge_in_graph, EdgeOf, VertexOf; simpl.
    split; [apply HinclA; exact HuA|].
    split; [apply HinclB; exact HvB | exact Hadj].
  - induction M as [|p M IH]; simpl; [constructor|].
    destruct p as [u v]; simpl.
    inversion Hall as [|? ? Hp Hall']; subst.
    destruct Hp as [HuA [HvB Hadj]]; simpl in HuA, HvB, Hadj.
    simpl in Hf, Hs.
    inversion Hf as [|? ? Hfu Hf']; subst.
    inversion Hs as [|? ? Hsv Hs']; subst.
    constructor.
    + intro H. destruct H as [E | H].
      * subst v. exact (Hdis u HuA HvB).
      * apply in_concat_pairs in H as [p [Hp Hx]].
        rewrite Forall_forall in Hall'.
        destruct (Hall' p Hp) as [HpA [HpB _]].
        destruct Hx as [E | E].
        -- apply Hfu. rewrite E. apply in_map; exact Hp.
        -- rewrite E in HuA. exact (Hdis (snd p) HuA HpB).
    + constructor.
      * intro H. apply in_concat_pairs in H as [p [Hp Hx]].
        rewrite Forall_forall in Hall'.
        destruct (Hall' p Hp) as [HpA [HpB _]].
        destruct Hx as [E | E].
        -- rewrite E in HvB. exact (Hdis (fst p) HpA HvB).
        -- apply Hsv. rewrite E. apply in_map; exact Hp.
      * apply IH; auto.
Qed.

(** ** Hall's marriage theorem in graph form

    Identical to the previously axiomatised statement except for the
    added [NoDup S] guard on the Hall condition (see the header NOTE:
    without it the hypothesis is unsatisfiable for nonempty [partA],
    so the axiom was vacuous). [Bipartite G] is kept for interface
    fidelity although the proof does not need it: the Hall condition
    itself only counts neighbours across the [partA]/[partB] split. *)

Theorem hall_marriage_theorem :
  forall G : Graph,
    Simple G -> Bipartite G ->
    forall partA partB,
      vertices G = partA ++ partB ->
      NoDup partA -> NoDup partB ->
      (forall S, incl S partA -> NoDup S ->
                 length S <= length (filter (fun v =>
                                              existsb (fun u =>
                                                         andb (adjb G u v) (memb u S))
                                                      partA) partB)) ->
      exists M, Matching G M /\
                forall a, In a partA -> In a (concat (map edge_vertices M)).
Proof.
  intros G HSimple HBip partA partB Hsplit HndA HndB Hhallhyp.
  destruct HSimple as [Hsym [Hirr HndV]].
  assert (HinclA : incl partA (vertices G)).
  { intros x Hx; rewrite Hsplit; apply in_or_app; left; exact Hx. }
  assert (HinclB : incl partB (vertices G)).
  { intros x Hx; rewrite Hsplit; apply in_or_app; right; exact Hx. }
  assert (Hdis : forall x, In x partA -> In x partB -> False).
  { rewrite Hsplit in HndV.
    apply (proj1 (NoDup_app_iff_alt partA partB)) in HndV as [_ [_ Hd]].
    intros x Hx1 Hx2. exact (Hd x Hx1 Hx2). }
  assert (Hhall : HallCond (fun a b => adjb G a b) partA partB).
  { intros S HinclS HndS.
    specialize (Hhallhyp S HinclS HndS).
    assert (E : filter (fun v => existsb (fun u => adjb G u v && memb u S) partA)
                       partB
                = nbhd (fun a b => adjb G a b) S partB).
    { unfold nbhd. apply filter_ext_in_local. intros b _.
      destruct (existsb (fun a => adjb G a b) S) eqn:ES.
      - apply existsb_exists in ES as [x [HxS Hx]].
        apply existsb_exists. exists x.
        split; [apply HinclS; exact HxS|].
        rewrite Hx. simpl. apply memb_true_iff; exact HxS.
      - destruct (existsb (fun u => adjb G u b && memb u S) partA) eqn:EA;
          [|reflexivity].
        exfalso. apply existsb_exists in EA as [u [HuA Hu]].
        apply andb_true_iff in Hu as [Hadj Hmem].
        apply memb_true_iff in Hmem.
        assert (E1 : existsb (fun a => adjb G a b) S = true)
          by (apply existsb_exists; exists u; auto).
        congruence. }
    rewrite E in Hhallhyp. exact Hhallhyp. }
  destruct (hall_abstract (fun a b => adjb G a b) partA partB HndA HndB Hhall)
    as [M HP].
  pose proof HP as [Hf [Hs [Hsat Hall]]].
  exists M. split.
  - apply (pairing_matching G partA partB); auto.
  - intros a Ha. specialize (Hsat a Ha).
    apply in_map_iff in Hsat as [p [E Hp]].
    apply (in_concat_map_edge p M); [exact Hp|].
    destruct p as [u v]; simpl in E; subst u; simpl; left; reflexivity.
Qed.

(** ** Deficiency machinery for König's theorem *)

Definition defic (adj : nat -> nat -> bool) (B S : list nat) : nat :=
  length S - length (nbhd adj S B).

Definition max_defic (adj : nat -> nat -> bool) (A B : list nat) : nat :=
  fold_right Nat.max 0 (map (defic adj B) (sublists A)).

Lemma fold_max_ge :
  forall (l : list nat) (x : nat), In x l -> x <= fold_right Nat.max 0 l.
Proof.
  induction l as [|y l IH]; intros x Hx; [inversion Hx|].
  destruct Hx as [E | Hx]; simpl.
  - subst y; lia.
  - specialize (IH x Hx); lia.
Qed.

Lemma fold_max_zero_or_in :
  forall l : list nat,
    fold_right Nat.max 0 l = 0 \/ In (fold_right Nat.max 0 l) l.
Proof.
  induction l as [|x l IH]; simpl; [left; reflexivity|].
  destruct (Nat.max_spec x (fold_right Nat.max 0 l)) as [[Hlt E] | [Hle E]];
    rewrite E.
  - destruct IH as [E0 | Hin]; [left; exact E0 | right; right; exact Hin].
  - right; left; reflexivity.
Qed.

(** Canonical subsequence representative of an arbitrary NoDup subset. *)

Lemma canon_subset :
  forall (A S : list nat),
    NoDup A -> incl S A -> NoDup S ->
    exists S', In S' (sublists A) /\ length S' = length S /\
               (forall x, In x S' <-> In x S).
Proof.
  intros A S HndA Hincl HndS.
  exists (filter (fun x => memb x S) A).
  split; [apply filter_in_sublists|].
  assert (Hiff : forall x, In x (filter (fun x => memb x S) A) <-> In x S).
  { intros x; rewrite filter_In; split.
    - intros [_ Hm]; apply memb_true_iff; exact Hm.
    - intros Hx; split; [apply Hincl; exact Hx | apply memb_true_iff; exact Hx]. }
  split; [|exact Hiff].
  apply NoDup_set_eq_length; auto.
  apply NoDup_filter; exact HndA.
Qed.

Lemma defic_le_max_general :
  forall adj (A B S : list nat),
    NoDup A -> incl S A -> NoDup S ->
    length S - length (nbhd adj S B) <= max_defic adj A B.
Proof.
  intros adj A B S HndA Hincl HndS.
  destruct (canon_subset A S HndA Hincl HndS) as [S' [HS' [Hlen Hiff]]].
  assert (Hnb : nbhd adj S' B = nbhd adj S B) by (apply nbhd_set_eq; exact Hiff).
  unfold max_defic.
  assert (Hin : In (defic adj B S') (map (defic adj B) (sublists A)))
    by (apply in_map; exact HS').
  pose proof (fold_max_ge _ _ Hin) as Hge.
  unfold defic in Hge. rewrite Hlen, Hnb in Hge. exact Hge.
Qed.

(** A deficiency-maximising subset with a controlled neighbourhood:
    the empty set when the maximum deficiency is [0], otherwise an
    attaining subsequence (whose neighbourhood is then strictly
    smaller than itself). *)

Lemma max_defic_witness :
  forall adj (A B : list nat),
    NoDup A ->
    exists S, incl S A /\ NoDup S /\
              length S - length (nbhd adj S B) = max_defic adj A B /\
              length (nbhd adj S B) <= length S.
Proof.
  intros adj A B HndA.
  destruct (Nat.eq_dec (max_defic adj A B) 0) as [E | NE].
  - exists []. split; [intros x Hx; inversion Hx|].
    split; [constructor|].
    rewrite nbhd_nil_left. simpl. split; [symmetry; exact E | lia].
  - destruct (fold_max_zero_or_in (map (defic adj B) (sublists A))) as [E | Hin].
    + exfalso. apply NE. exact E.
    + apply in_map_iff in Hin as [S [Hdef HS]].
      exists S.
      split; [apply sublists_incl; exact HS|].
      split; [eapply sublists_NoDup_members; [exact HndA | exact HS]|].
      unfold max_defic. unfold max_defic in NE.
      assert (Hd2 : length S - length (nbhd adj S B)
                    = fold_right Nat.max 0 (map (defic adj B) (sublists A))).
      { rewrite <- Hdef. reflexivity. }
      split; [exact Hd2 | lia].
Qed.

(** ** König's minimax theorem *)

Theorem koenig_theorem :
  forall G,
    Simple G -> Bipartite G ->
    exists M C,
      Matching G M /\ VertexCover G C /\ length M = length C
      /\ (forall M', Matching G M' -> length M' <= length M)
      /\ (forall C', VertexCover G C' -> length C <= length C').
Proof.
  intros G HSimple HBip.
  destruct HBip as [color Hcolor].
  pose proof HSimple as [Hsym [Hirr HndV]].
  set (partA := filter color (vertices G)).
  set (partB := filter (fun v => negb (color v)) (vertices G)).
  set (adjF := fun a b : nat => adjb G a b).
  assert (HndA : NoDup partA) by (apply NoDup_filter; exact HndV).
  assert (HndB : NoDup partB) by (apply NoDup_filter; exact HndV).
  assert (HinclAV : incl partA (vertices G)).
  { intros x Hx; unfold partA in Hx; apply filter_In in Hx; tauto. }
  assert (HinclBV : incl partB (vertices G)).
  { intros x Hx; unfold partB in Hx; apply filter_In in Hx; tauto. }
  assert (HdisAB : forall x, In x partA -> In x partB -> False).
  { intros x Hx1 Hx2.
    unfold partA in Hx1; apply filter_In in Hx1 as [_ E1].
    unfold partB in Hx2; apply filter_In in Hx2 as [_ E2].
    rewrite E1 in E2. discriminate. }
  destruct (max_defic_witness adjF partA partB HndA)
    as [Sstar [HinclS [HndS [Hdefic Hnble]]]].
  set (dcount := max_defic adjF partA partB) in *.
  (* ----- the vertex cover ----- *)
  set (C := filter (fun x => negb (memb x Sstar)) partA
            ++ nbhd adjF Sstar partB).
  assert (HlenSstar_le : length Sstar <= length partA)
    by (apply NoDup_incl_length; auto).
  assert (Hfilter_memb :
            length (filter (fun x => memb x Sstar) partA) = length Sstar).
  { apply NoDup_set_eq_length.
    - apply NoDup_filter; exact HndA.
    - exact HndS.
    - intros x; rewrite filter_In; split.
      + intros [_ Hm]; apply memb_true_iff; exact Hm.
      + intros Hx; split;
          [apply HinclS; exact Hx | apply memb_true_iff; exact Hx]. }
  pose proof (filter_length_split nat (fun x => memb x Sstar) partA) as HsplitA.
  cbv beta in HsplitA.
  assert (HlenC : length C = length partA - dcount).
  { unfold C. rewrite app_length. lia. }
  assert (HCcover : VertexCover G C).
  { split.
    - apply Forall_forall. intros x Hx. unfold C in Hx.
      apply in_app_or in Hx. destruct Hx as [Hx | Hx].
      + apply filter_In in Hx as [Hx _]. exact (HinclAV x Hx).
      + pose proof (nbhd_incl adjF Sstar partB x Hx) as HxB.
        exact (HinclBV x HxB).
    - intros u v Hedge. destruct Hedge as [Hu [Hv Hadj]].
      assert (Hne : color u <> color v) by (apply Hcolor; auto).
      destruct (color u) eqn:Ecu.
      + assert (HuA : In u partA)
          by (unfold partA; apply filter_In; split; auto).
        destruct (color v) eqn:Ecv; [congruence|].
        assert (HvB : In v partB).
        { unfold partB; apply filter_In; split;
            [exact Hv | rewrite Ecv; reflexivity]. }
        destruct (memb u Sstar) eqn:Emu.
        * right. unfold C. apply in_or_app. right.
          unfold nbhd. apply filter_In. split; [exact HvB|].
          apply existsb_exists. exists u.
          split; [apply memb_true_iff; exact Emu | exact Hadj].
        * left. unfold C. apply in_or_app. left.
          apply filter_In. split; [exact HuA | rewrite Emu; reflexivity].
      + destruct (color v) eqn:Ecv; [|congruence].
        assert (HvA : In v partA)
          by (unfold partA; apply filter_In; split; auto).
        assert (HuB : In u partB).
        { unfold partB; apply filter_In; split;
            [exact Hu | rewrite Ecu; reflexivity]. }
        assert (Hadj' : adjb G v u = true) by (rewrite <- (Hsym u v); exact Hadj).
        destruct (memb v Sstar) eqn:Emv.
        * left. unfold C. apply in_or_app. right.
          unfold nbhd. apply filter_In. split; [exact HuB|].
          apply existsb_exists. exists v.
          split; [apply memb_true_iff; exact Emv | exact Hadj'].
        * right. unfold C. apply in_or_app. left.
          apply filter_In. split; [exact HvA | rewrite Emv; reflexivity]. }
  (* ----- the matching, via the augmented graph ----- *)
  set (base := S (list_max (vertices G))).
  set (dummies := seq base dcount).
  set (Bplus := partB ++ dummies).
  set (adjP := fun a b : nat => adjb G a b || memb b dummies).
  assert (Hfresh : forall x, In x (vertices G) -> ~ In x dummies).
  { intros x Hx Hdx. unfold dummies in Hdx. apply in_seq in Hdx.
    assert (Hmax : Forall (fun k => k <= list_max (vertices G)) (vertices G))
      by (apply list_max_le; apply Nat.le_refl).
    rewrite Forall_forall in Hmax. specialize (Hmax x Hx).
    unfold base in Hdx. lia. }
  assert (HndBplus : NoDup Bplus).
  { unfold Bplus. apply NoDup_app_intro; [exact HndB | apply seq_NoDup |].
    intros x Hx. apply Hfresh. apply HinclBV. exact Hx. }
  assert (HdisBdum : forall b, In b partB -> memb b dummies = false).
  { intros b Hb. apply memb_false_iff. apply Hfresh. apply HinclBV. exact Hb. }
  assert (HhallP : HallCond adjP partA Bplus).
  { intros Ssub HinclSs HndSs.
    destruct Ssub as [|s0 Ss']; [simpl; lia|].
    unfold Bplus, nbhd. rewrite filter_app, app_length.
    assert (E1 : filter (fun b => existsb (fun a => adjP a b) (s0 :: Ss')) partB
                 = nbhd adjF (s0 :: Ss') partB).
    { unfold nbhd. apply filter_ext_in_local. intros b Hb.
      apply existsb_ext_in. intros a Ha.
      unfold adjP, adjF. rewrite (HdisBdum b Hb). apply orb_false_r. }
    assert (E2 : filter (fun b => existsb (fun a => adjP a b) (s0 :: Ss'))
                        dummies
                 = dummies).
    { apply filter_all_true. intros b Hb.
      simpl. unfold adjP.
      assert (Em : memb b dummies = true) by (apply memb_true_iff; exact Hb).
      rewrite Em, orb_true_r. reflexivity. }
    rewrite E1, E2.
    assert (Hd : length (s0 :: Ss') - length (nbhd adjF (s0 :: Ss') partB)
                 <= dcount).
    { unfold dcount. apply defic_le_max_general; auto. }
    unfold dummies. rewrite seq_length. lia. }
  destruct (hall_abstract adjP partA Bplus HndA HndBplus HhallP)
    as [Mplus HPplus].
  assert (HlenMplus : length Mplus = length partA)
    by (apply (Pairing_length adjP partA Bplus); auto).
  pose proof HPplus as [Hfp [Hsp [Hsatp Hallp]]].
  pose proof (filter_length_split (nat * nat)
                (fun p => memb (snd p) partB) Mplus) as HsplitM.
  cbv beta in HsplitM.
  set (M := filter (fun p => memb (snd p) partB) Mplus) in *.
  set (D := filter (fun p => negb (memb (snd p) partB)) Mplus) in *.
  assert (HM : Matching G M).
  { apply (pairing_matching G partA partB M); auto.
    - apply NoDup_map_filter; exact Hfp.
    - apply NoDup_map_filter; exact Hsp.
    - apply Forall_forall. intros p Hp.
      unfold M in Hp. apply filter_In in Hp as [HpM Hmemb].
      rewrite Forall_forall in Hallp.
      destruct (Hallp p HpM) as [HpA [HpB HpAdj]].
      split; [exact HpA|].
      split; [apply memb_true_iff; exact Hmemb|].
      unfold adjP in HpAdj.
      assert (Hdum : memb (snd p) dummies = false)
        by (apply HdisBdum; apply memb_true_iff; exact Hmemb).
      rewrite Hdum, orb_false_r in HpAdj. exact HpAdj. }
  assert (HlenD : length D <= dcount).
  { rewrite <- (map_length snd D).
    assert (Hincl : incl (map snd D) dummies).
    { intros x Hx. apply in_map_iff in Hx as [p [E Hp]]. subst x.
      unfold D in Hp. apply filter_In in Hp as [HpM Hneg].
      apply negb_true_iff in Hneg.
      rewrite Forall_forall in Hallp.
      destruct (Hallp p HpM) as [_ [HpB _]].
      unfold Bplus in HpB. apply in_app_or in HpB.
      destruct HpB as [HpB | HpB]; [|exact HpB].
      rewrite memb_false_iff in Hneg. contradiction. }
    assert (HndD : NoDup (map snd D))
      by (unfold D; apply NoDup_map_filter; exact Hsp).
    pose proof (NoDup_incl_length HndD Hincl) as Hle.
    unfold dummies in Hle. rewrite seq_length in Hle. exact Hle. }
  (* ----- assembly ----- *)
  assert (HMC_le : length M <= length C)
    by (apply (matching_le_cover G M C); auto).
  assert (HMeqC : length M = length C) by lia.
  (* Recast at type [Edge] so rewriting matches the goal, in which the
     existential binder lives in [list Edge]. *)
  assert (HMeqC2 : @length Edge M = length C) by exact HMeqC.
  exists M, C.
  split; [exact HM|]. split; [exact HCcover|]. split; [exact HMeqC|].
  split.
  - intros M' HM'.
    pose proof (matching_le_cover G M' C HM' HCcover) as Hx.
    rewrite HMeqC2. exact Hx.
  - intros C' HC'.
    pose proof (matching_le_cover G M C' HM HC') as Hx.
    rewrite <- HMeqC2. exact Hx.
Qed.
