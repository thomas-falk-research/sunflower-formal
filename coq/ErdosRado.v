(** * ErdosRado.v -- Erdős–Rado 1960 sunflower upper bound.

    Theorem [erdos_rado_upper_bound]: for [n ≥ 1] and [k ≥ 2], every
    Distinct [n]-uniform family with more than [(k-1)^n · n!] members
    contains a [k]-sunflower.

    Proof: strong induction on [n], with a maximal-disjoint cover
    followed by [Pigeonhole.pigeonhole_family]. The base case [n = 1]
    is handled directly using [firstn] to extract [k] distinct
    singletons. The induction step removes a popular element [x] from
    every set in the "high-degree" subfamily and applies the IH to the
    resulting [(n-1)]-uniform family, then lifts the sunflower back via
    [sunflower_lift]. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat Wf_nat.
From Sunflower Require Import Sets Sunflower Pigeonhole.
Import ListNotations.

Set Implicit Arguments.

(** ** Maximal pairwise-disjoint covering subfamily exists *)

Lemma max_disjoint_cover :
  forall F : Family,
    Forall (fun A : list nat => A <> []) F ->
    exists S : list (list nat),
      incl S F /\
      NoDup S /\
      PairwiseDisjoint S /\
      (forall A, In A F -> exists B, In B S /\ ~ Disjoint A B).
Proof.
  intros F.
  remember (length F) as n eqn:Heqn.
  revert F Heqn.
  induction n as [n IH] using lt_wf_ind.
  intros F Hn HF.
  destruct F as [|A F']; simpl in Hn.
  - exists []. repeat split.
    + apply incl_refl.
    + constructor.
    + unfold PairwiseDisjoint; intros C D HC HD HCD; inversion HC.
    + intros B HB; inversion HB.
  - inversion HF as [|? ? HAne HF'rest]; subst.
    pose (F1 := filter (fun B => disjointb A B) F').
    assert (Hlen : length F1 < S (length F')).
    { unfold F1.
      pose proof (length_filter_le (fun B => disjointb A B) F') as Hp.
      lia. }
    assert (HF1 : Forall (fun B : list nat => B <> []) F1).
    { unfold F1. apply Forall_forall. intros B HB.
      apply filter_In in HB as [HBin _].
      rewrite Forall_forall in HF'rest. apply HF'rest; exact HBin. }
    destruct (IH (length F1) Hlen F1 eq_refl HF1) as
        [S1 [Hincl1 [Hnd1 [Hpd1 Hcover1]]]].
    exists (A :: S1).
    split; [|split; [|split]].
    + intros B HB; simpl in HB; destruct HB as [E | HB].
      * left; exact E.
      * right. apply Hincl1 in HB.
        unfold F1 in HB; apply filter_In in HB; tauto.
    + constructor.
      * intro Hin. apply Hincl1 in Hin.
        unfold F1 in Hin. apply filter_In in Hin as [_ Hd].
        apply disjointb_correct in Hd.
        destruct A as [|a A']; [apply HAne; reflexivity|].
        apply (Hd a); simpl; auto.
      * exact Hnd1.
    + unfold PairwiseDisjoint.
      intros C D HC HD HCD.
      simpl in HC, HD.
      destruct HC as [EC | HC]; destruct HD as [ED | HD].
      * subst; contradiction.
      * subst C.
        apply Hincl1 in HD; unfold F1 in HD.
        apply filter_In in HD as [_ Hd]; apply disjointb_correct in Hd.
        exact Hd.
      * subst D.
        apply Hincl1 in HC; unfold F1 in HC.
        apply filter_In in HC as [_ Hd]; apply disjointb_correct in Hd.
        apply Disjoint_sym; exact Hd.
      * apply Hpd1; auto.
    + intros B HB; simpl in HB; destruct HB as [E | HB].
      * subst B. exists A; split; [left; reflexivity|].
        intro Hd; destruct A as [|a A']; [apply HAne; reflexivity|].
        apply (Hd a); simpl; auto.
      * destruct (disjointb A B) eqn:Eq.
        -- apply disjointb_correct in Eq.
           assert (HBF1 : In B F1).
           { unfold F1; apply filter_In; split; [exact HB|].
             apply disjointb_correct; exact Eq. }
           destruct (Hcover1 B HBF1) as [C [HCS HnDis]].
           exists C; split; [right; exact HCS | exact HnDis].
        -- apply disjointb_false_iff in Eq as [x [HxA HxB]].
           exists A; split; [left; reflexivity|].
           intro Hd. apply (Hd x); auto.
Qed.

(** ** Length bound on concat-of-uniform sublist *)

Lemma concat_uniform_length :
  forall n S,
    Forall (UniformSet n) S ->
    length (concat S) <= length S * n.
Proof.
  intros n S; induction S as [|A S' IH]; simpl; intros HF; [lia|].
  inversion HF as [|? ? HUA HF']; clear HF.
  destruct HUA as [HAlen HAnd].
  rewrite app_length, HAlen.
  specialize (IH HF'). lia.
Qed.

(** ** Every cover element provides a "witness" element shared with [A] *)

Lemma cover_provides_element :
  forall (F : Family) (S : list (list nat)) (A : list nat),
    (forall B, In B F -> exists C, In C S /\ ~ Disjoint B C) ->
    In A F ->
    exists x, In x A /\ In x (concat S).
Proof.
  intros F S A Hcov HA.
  destruct (Hcov A HA) as [C [HCS HnDis]].
  (* ~ Disjoint A C means there is x in both A and C. *)
  destruct (disjointb A C) eqn:E.
  - apply disjointb_correct in E. contradiction.
  - apply disjointb_false_iff in E as [x [HxA HxC]].
    exists x; split; [exact HxA|].
    apply in_concat. exists C; split; auto.
Qed.

(** ** Filtering for "contains [x]" preserves family properties *)

Lemma uniform_contains_x :
  forall n F x,
    Uniform n F ->
    Uniform n (filter (fun A => memb x A) F).
Proof.
  intros n F x HU; unfold Uniform in *.
  apply Forall_forall; intros A HA.
  apply filter_In in HA as [HA _].
  rewrite Forall_forall in HU; apply HU; exact HA.
Qed.

Lemma contains_x_all_have_x :
  forall x F, Forall (fun A => In x A) (filter (fun A => memb x A) F).
Proof.
  intros x F; apply Forall_forall; intros A HA.
  apply filter_In in HA as [_ Hm]; apply memb_true_iff; exact Hm.
Qed.

(** ** Reducing the family by removing [x] from every member *)

Lemma rem_elt_length :
  forall x n A,
    UniformSet n A -> In x A -> UniformSet (pred n) (rem_elt x A).
Proof.
  intros x n A [Hlen Hnd] Hin.
  unfold UniformSet; split.
  - pose proof (@length_rem_elt_in x A Hnd Hin) as Heq.
    rewrite Heq, Hlen. reflexivity.
  - apply rem_NoDup; exact Hnd.
Qed.

Lemma reduce_uniform :
  forall n F x,
    1 <= n ->
    Uniform n F ->
    Forall (fun A : list nat => In x A) F ->
    Uniform (pred n) (map (rem_elt x) F).
Proof.
  intros n F x Hn HU Hcontain.
  unfold Uniform in *.
  apply Forall_forall; intros B HB.
  apply in_map_iff in HB as [A [Heq HA]].
  subst B.
  rewrite Forall_forall in HU, Hcontain.
  apply rem_elt_length; auto.
Qed.

Lemma length_map_rem :
  forall x F, length (map (rem_elt x) F) = length F.
Proof. intros; apply map_length. Qed.

(** ** The Erdős–Rado theorem *)

Theorem erdos_rado_upper_bound :
  forall n k, 1 <= n -> 2 <= k ->
    UpperBound n k (S ((k-1)^n * fact n)).
Proof.
  intros n. induction n as [n IH] using lt_wf_ind.
  intros k Hn Hk F HU HD Hsize.
  destruct n as [|n']; [lia|].
  (* Hypothesis: F is (S n')-uniform, Distinct, length F >= S ((k-1)^(S n') * fact (S n')). *)
  (* Step 1: All sets in F are nonempty. *)
  assert (HFne : Forall (fun A : list nat => A <> []) F).
  { unfold Uniform in HU.
    apply Forall_forall; intros A HA.
    rewrite Forall_forall in HU; destruct (HU A HA) as [Hlen _].
    destruct A; [simpl in Hlen; lia | discriminate]. }
  (* Step 2: Get maximal pairwise-disjoint cover. *)
  destruct (max_disjoint_cover HFne) as [Scov [Hincl [Hnd [Hpd Hcov]]]].
  (* Step 3: Case split on |Scov| >= k vs < k. *)
  destruct (le_lt_dec k (length Scov)) as [Hkge | Hklt].
  - (* Case A: |Scov| >= k. Take first k of Scov as k disjoint sets. *)
    pose (Sk := firstn k Scov).
    assert (HSklen : length Sk = k).
    { unfold Sk; apply firstn_length_le; lia. }
    assert (HSkincl_cov : incl Sk Scov).
    { unfold Sk; intros B HB.
      rewrite <- (firstn_skipn k Scov). apply in_or_app; left; exact HB. }
    assert (HSkincl : incl Sk F).
    { unfold incl. intros B HB. apply Hincl, HSkincl_cov, HB. }
    assert (HSknd : NoDup Sk).
    { unfold Sk. clear -Hnd. revert Hnd. generalize Scov as L; clear Scov.
      intros L. revert k. induction L as [|a L IH']; intros k Hnd; simpl.
      - destruct k; constructor.
      - destruct k as [|k']; [constructor|].
        simpl. inversion Hnd as [|? ? HniA Hnd']; subst.
        constructor.
        + intro Hin. apply HniA.
          rewrite <- (firstn_skipn k' L). apply in_or_app; left; exact Hin.
        + apply IH'; exact Hnd'. }
    assert (HSkpd : PairwiseDisjoint Sk).
    { unfold PairwiseDisjoint. intros B C HB HC HBC.
      apply Hpd; [apply HSkincl_cov; exact HB | apply HSkincl_cov; exact HC | exact HBC]. }
    assert (HSkne : Forall (fun A : list nat => A <> []) Sk).
    { apply Forall_forall; intros A HA.
      assert (HAF : In A F) by (apply HSkincl; exact HA).
      rewrite Forall_forall in HFne; apply HFne; exact HAF. }
    exists Sk; split.
    + apply SubFamilySetEq_incl; exact HSkincl.
    + apply k_pairwise_disjoint_sunflower; auto.
  - (* Case B: |Scov| < k, i.e., |Scov| <= k - 1. *)
    pose (X := concat Scov).
    (* Every A in F intersects X. *)
    assert (HXcov : forall A, In A F -> exists x, In x A /\ In x X).
    { intros A HA. apply (cover_provides_element F Scov A); auto. }
    (* |X| <= |Scov| * (S n') <= (k-1) * (S n') *)
    assert (HXlen_le : length X <= length Scov * S n').
    { unfold X. apply concat_uniform_length.
      apply Forall_forall; intros B HB.
      apply Hincl in HB. unfold Uniform in HU.
      rewrite Forall_forall in HU; apply HU; exact HB. }
    assert (HX_le_kn : length X <= (k - 1) * S n') by (assert (length Scov <= k - 1) by lia; nia).
    (* Apply pigeonhole with K = (k-1)^n' * fact n'. *)
    set (K := (k-1)^n' * fact n').
    assert (HpigSize : length F > length X * K).
    { assert (HsizeF : length F > (k-1)^(S n') * fact (S n')) by lia.
      assert (Hpow : (k-1)^(S n') = (k-1) * (k-1)^n') by reflexivity.
      assert (Hfact : fact (S n') = (S n') * fact n') by reflexivity.
      unfold K. nia. }
    destruct (pigeonhole_family F X K HXcov HpigSize) as [x [HxX Hcountx]].
    (* So filter (memb x) F has length > K. *)
    set (Fx := filter (fun A => memb x A) F).
    assert (HFxlen : length Fx > K) by exact Hcountx.
    assert (HFxU : Uniform (S n') Fx) by (unfold Fx; apply uniform_contains_x; exact HU).
    assert (HFxC : Forall (fun A : list nat => In x A) Fx).
    { unfold Fx; apply contains_x_all_have_x. }
    assert (HFxD : Distinct Fx).
    { unfold Distinct, Fx; apply SetNoDup_filter; exact HD. }
    (* Reduce: F' = map (rem_elt x) Fx, which is n'-uniform. *)
    set (F' := map (rem_elt x) Fx).
    assert (HF'U : Uniform n' F').
    { unfold F'. replace n' with (pred (S n')) by reflexivity.
      apply reduce_uniform; auto; lia. }
    assert (HF'len : length F' > K) by (unfold F'; rewrite length_map_rem; exact HFxlen).
    assert (HF'D : Distinct F').
    { unfold Distinct, F'. apply SetNoDup_map_rem_preserves; auto. }
    (* Apply IH to F' with n = n'. *)
    destruct n' as [|n''].
    + (* n' = 0: K = 1 * 1 = 1, so |F'| > 1, i.e., |F'| >= 2.
         But every set in F' has length 0, i.e., is the empty list.
         F' is Distinct, so has at most 1 element. Contradiction. *)
      unfold K in HF'len. simpl in HF'len.
      assert (HF'unif : Uniform 0 F') by exact HF'U.
      (* All sets in F' are empty *)
      assert (Hallempty : Forall (eq []) F').
      { unfold Uniform in HF'unif.
        apply Forall_forall; intros A HA.
        rewrite Forall_forall in HF'unif. destruct (HF'unif A HA) as [Hlen _].
        destruct A; [reflexivity | simpl in Hlen; lia]. }
      (* F' Distinct, all empty: at most 1 element *)
      destruct F' as [|A1 [|A2 F'rest]]; simpl in HF'len; try lia.
      exfalso.
      inversion Hallempty as [|? ? E1 Hrest]. subst.
      inversion Hrest as [|? ? E2 _]. subst.
      (* Now A1 = [] and A2 = []. So they are equal. *)
      inversion HF'D as [|? ? Hni _]. subst.
      apply (Hni [] (or_introl eq_refl)). apply SetEq_refl.
    + (* n' = S n'' >= 1: apply IH. *)
      assert (Hlt : S n'' < S (S n'')) by lia.
      assert (HRecBound : length F' >= S ((k - 1) ^ S n'' * fact (S n''))).
      { unfold K in HF'len; lia. }
      destruct (IH (S n'') Hlt k (le_n_S _ _ (Nat.le_0_l _)) Hk F' HF'U HF'D HRecBound)
        as [Sinner [HSinSF HKS]].
      destruct HKS as [HSinLen [coreInner HSinSun]].
      (* Now lift the inner sunflower back to F via add_elt x. *)
      assert (HSinNotIn : Forall (fun B : list nat => ~ In x B) Sinner).
      { apply Forall_forall; intros B HB.
        destruct (HSinSF B HB) as [B' [HB'F' HseqBB']].
        unfold F' in HB'F'. apply in_map_iff in HB'F' as [A [HArem HAFx]].
        subst B'.
        (* x ∉ rem_x A *)
        intro Hin.
        destruct HseqBB' as [Hs _]. apply Hs in Hin.
        apply in_rem_iff in Hin as [_ Hxne]; apply Hxne; reflexivity. }
      (* Apply sunflower_lift. *)
      pose proof (@sunflower_lift x Sinner coreInner HSinNotIn HSinSun) as HSlift.
      (* The lifted sunflower has the right properties. *)
      exists (map_add x Sinner); split.
      * (* SubFamilySetEq (map_add x Sinner) F *)
        intros W HW. apply in_map_add_iff in HW as [B [HBin HWeq]].
        subst W.
        destruct (HSinSF B HBin) as [B' [HB'F' HseqBB']].
        unfold F' in HB'F'. apply in_map_iff in HB'F' as [A [HArem HAFx]].
        unfold Fx in HAFx. apply filter_In in HAFx as [HAF Hxin].
        apply memb_true_iff in Hxin.
        exists A. split; [exact HAF|].
        subst B'.
        (* Show SetEq (add_elt x B) A *)
        rewrite Forall_forall in HSinNotIn.
        pose proof (HSinNotIn B HBin) as HxB.
        unfold SetEq, Subset; split; intros y Hy.
        -- apply in_add_iff in Hy. destruct Hy as [E | Hy].
           ++ subst y; exact Hxin.
           ++ destruct HseqBB' as [Hs _]; apply Hs in Hy.
              apply in_rem_iff in Hy; tauto.
        -- apply in_add_iff. destruct (Nat.eq_dec y x) as [E | NE]; [left; exact E|].
           right. destruct HseqBB' as [_ Hs].
           apply Hs. apply in_rem_iff; auto.
      * (* KSunflower k (map_add x Sinner) *)
        split.
        -- rewrite length_map_add; exact HSinLen.
        -- exists (add_elt x coreInner); exact HSlift.
Qed.
