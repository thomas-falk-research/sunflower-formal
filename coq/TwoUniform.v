(** * TwoUniform.v -- At uniformity 2, sunflowers are degrees and matchings.

    Everything the sunflower problem asks at uniformity 2 is a question
    about two graph parameters. This file proves that, in three steps.

    First, *shape*: a sunflower on at least two members is either
    pairwise disjoint or passes through a common point
    ([sunflower_shape]). This needs no uniformity at all — it is just
    the observation that the core is empty or it is not.

    Second, the *converse*, which does need uniformity 2
    ([star_sunflower]): distinct 2-sets through a common point are a
    sunflower with that point as core. In a 3-uniform family the
    corresponding statement is false — [{1,2,3}], [{1,2,4}], [{1,3,5}]
    all contain 1 and are not a sunflower — which is the whole reason
    the problem is hard above uniformity 2.

    Together they give the characterisation
    ([two_uniform_sunflower_free_iff]):

    >  a distinct 2-uniform family has no [k]-sunflower
    >  <-> it has no [k] pairwise disjoint members
    >      and every vertex lies in fewer than [k] members,

    i.e. exactly when its matching number and its maximum degree are
    both at most [k-1]. So [f(2,k)] *is* the Chvátal–Hanson extremal
    problem at [D = nu = k-1], and not merely bounded by it.

    That identification is what this file proves. The extremal function
    itself is not proved here and nothing below depends on it: [ChHa76]
    evaluates it, and taking that on citation gives
    [f(2,k) = CH(k-1,k-1) + 1] and a sharp spread threshold
    [r*(2,k) = k]. What the repository proves outright is the lower half
    at odd [k] ([CliqueLowerBound.two_cliques_lower_bound]). See
    [docs/references.md] for which results are used and which are
    merely cited.

    Third, the same two parameters govern the *spread* hypothesis
    ([rao_spread_two_iff_degree]): at uniformity 2 the spread condition
    [RaoSpread 2 F r] is precisely the maximum-degree bound
    [deg [v] F <= r] for every [v]. The [|T| = 2] clause asks
    [deg T F <= r ^ 0 = 1], which [Distinct] already gives, and larger
    [T] have degree 0.

    So [SpreadReduction.SpreadYieldsDisjoint 2 k r] says:

    >  a simple graph with maximum degree at most [r] and more than
    >  [r ^ 2] edges has [k] pairwise disjoint edges,

    which is the *same* extremal problem
    ([spread_yields_disjoint_two_is_a_graph_statement]). The roadmap
    listed the two as alternative campaigns; they are one function seen
    twice. See `rust/src/chvatal_hanson.rs` for the numbers this
    identification predicts and the exhaustive searches that check
    them.

    Zero axioms, zero admits. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower ProductLowerBound Spread SpreadReduction.
Import ListNotations.

(** ** Structure of 2-element sets

    These were local to [F23.v]; they are the general shape lemmas for
    uniformity 2, so they live here and [F23.v] imports them. *)

Lemma two_set_shape :
  forall g, length g = 2 -> NoDup g ->
            exists (a b : nat), a <> b /\ g = [a; b].
Proof.
  intros g Hlen Hnd.
  destruct g as [|a [|b [|? ?]]]; simpl in Hlen; try discriminate.
  inversion Hnd as [|? ? Hna Hnd']; subst.
  exists a, b. split; [|reflexivity].
  intro E; subst; apply Hna; left; reflexivity.
Qed.

(** A 2-set containing [v] is [{v, w}] for one other point [w]. *)

Lemma two_set_other :
  forall (g : list nat) (v : nat),
    length g = 2 -> NoDup g -> In v g ->
    exists w, w <> v /\ (forall z, In z g <-> z = v \/ z = w).
Proof.
  intros g v Hlen Hnd Hv.
  destruct g as [|x [|y [|? ?]]]; simpl in Hlen; try discriminate.
  inversion Hnd as [|? ? Hnx Hnd']; subst.
  simpl in Hv. destruct Hv as [E | [E | []]].
  - subst x. exists y. split.
    + intro E; subst y. apply Hnx; left; reflexivity.
    + intros z; simpl; split.
      * intros [E | [E | []]]; [left | right]; symmetry; exact E.
      * intros [E | E]; subst z;
          [left; reflexivity | right; left; reflexivity].
  - subst y. exists x. split.
    + intro E; subst x. apply Hnx; left; reflexivity.
    + intros z; simpl; split.
      * intros [E | [E | []]]; [right | left]; symmetry; exact E.
      * intros [E | E]; subst z;
          [right; left; reflexivity | left; reflexivity].
Qed.

(** Two 2-sets sharing [v] and differing in their other point meet in
    exactly [{v}]. *)

Lemma inter_two_sets_common :
  forall g h v wg wh,
    (forall z, In z g <-> z = v \/ z = wg) -> wg <> v ->
    (forall z, In z h <-> z = v \/ z = wh) ->
    wg <> wh ->
    SetEq (inter g h) [v].
Proof.
  intros g h v wg wh Hg Hwgv Hh Hne.
  split; intros z Hz.
  - apply in_inter_iff in Hz as [Hzg Hzh].
    apply Hg in Hzg. apply Hh in Hzh.
    destruct Hzh as [E' | E']; [subst z; left; reflexivity|].
    destruct Hzg as [E | E]; [subst z; left; reflexivity|].
    exfalso. subst z. exact (Hne E').
  - destruct Hz as [E | []]. subst z.
    apply in_inter_iff.
    split; [apply Hg; left; reflexivity | apply Hh; left; reflexivity].
Qed.

(** ** Shape: every sunflower is a matching or a star

    No uniformity hypothesis. Either the core is empty, in which case
    the members are pairwise disjoint, or it has a point, in which case
    every member contains that point — because every member's
    intersection with *some other* member is the core. *)

Lemma exists_other_member :
  forall (S : list (list nat)) (X : list nat),
    NoDup S -> 2 <= length S -> In X S ->
    exists Y, In Y S /\ Y <> X.
Proof.
  intros S X Hnd Hlen HX.
  destruct S as [|a [|b rest]]; simpl in Hlen; try lia.
  inversion Hnd as [|? ? Hnia Hnd']; subst.
  destruct (list_eq_dec Nat.eq_dec X a) as [E | Hne].
  - exists b. split; [right; left; reflexivity|].
    subst X. intro E'. apply Hnia. left. exact E'.
  - exists a. split; [left; reflexivity|].
    intro E'. apply Hne. symmetry. exact E'.
Qed.

Theorem sunflower_shape :
  forall (S : list (list nat)) (core : list nat),
    2 <= length S ->
    Sunflower S core ->
    PairwiseDisjoint S \/ (exists v, Forall (fun A => In v A) S).
Proof.
  intros S core Hlen [Hsnd Hcore].
  destruct core as [|v core'].
  - (* Empty core: the members are pairwise disjoint. *)
    left. unfold PairwiseDisjoint, Disjoint.
    intros A B HA HB Hne z HzA HzB.
    destruct (Hcore A B HA HB Hne) as [Hs1 _].
    assert (Hz : In z (inter A B))
      by (apply in_inter_iff; split; assumption).
    exact (Hs1 z Hz).
  - (* Nonempty core: every member contains its first point. *)
    right. exists v.
    apply Forall_forall. intros X HX.
    destruct (exists_other_member S X (SetNoDup_NoDup Hsnd) Hlen HX)
      as [Y [HY Hne]].
    assert (HXY : X <> Y) by (intro E; apply Hne; symmetry; exact E).
    destruct (Hcore X Y HX HY HXY) as [_ Hs2].
    assert (Hv : In v (inter X Y)) by (apply Hs2; left; reflexivity).
    apply in_inter_iff in Hv; tauto.
Qed.

(** ** The converse at uniformity 2

    Distinct 2-sets through a common point are a sunflower with core
    [{v}]. This is where uniformity 2 is used, and it is exactly what
    fails above it. *)

Theorem star_sunflower :
  forall (S : list (list nat)) (v : nat),
    Forall (UniformSet 2) S ->
    SetNoDup S ->
    Forall (fun A => In v A) S ->
    Sunflower S [v].
Proof.
  intros S v HU Hsnd Hstar.
  split; [exact Hsnd|].
  intros A B HA HB Hne.
  rewrite Forall_forall in HU, Hstar.
  destruct (HU A HA) as [HlA HnA].
  destruct (HU B HB) as [HlB HnB].
  destruct (two_set_other A v HlA HnA (Hstar A HA)) as [wA [HwAv HchA]].
  destruct (two_set_other B v HlB HnB (Hstar B HB)) as [wB [_ HchB]].
  assert (HwAB : wA <> wB).
  { intro E; subst wB.
    apply (SetNoDup_pairwise Hsnd HA HB Hne).
    split; intros z Hz; [apply HchB, HchA, Hz | apply HchA, HchB, Hz]. }
  exact (inter_two_sets_common A B v wA wB HchA HwAv HchB HwAB).
Qed.

(** ** The two parameters

    [HasKDisjoint] is the matching number as a predicate — the
    conclusion of [SpreadReduction.SpreadYieldsDisjoint], verbatim. The
    degree is [Spread.deg [v] F], the same function the spread
    condition bounds. *)

Definition HasKDisjoint (k : nat) (F : Family) : Prop :=
  exists S : list (list nat),
    incl S F /\ NoDup S /\ length S = k /\ PairwiseDisjoint S.

(** A star of size [k] inside [F] is [k] of the members counted by
    [deg [v] F], and conversely. *)

Lemma star_le_deg :
  forall (S : list (list nat)) (F : Family) (v : nat),
    NoDup S -> incl S F -> Forall (fun A => In v A) S ->
    length S <= deg [v] F.
Proof.
  intros S F v Hnd Hincl Hstar; unfold deg.
  apply NoDup_incl_length; [exact Hnd|].
  intros A HA. apply filter_In. split; [apply Hincl; exact HA|].
  apply containsb_true_iff. intros z [E | []]; subst z.
  rewrite Forall_forall in Hstar; apply Hstar; exact HA.
Qed.

Lemma deg_gives_star :
  forall (F : Family) (v k : nat),
    NoDup F -> k <= deg [v] F ->
    exists S : list (list nat),
      incl S F /\ NoDup S /\ length S = k /\ Forall (fun A => In v A) S.
Proof.
  intros F v k HndF Hk; unfold deg in Hk.
  assert (Hsub : forall A, In A (firstn k (filter (containsb [v]) F)) ->
                           In A (filter (containsb [v]) F))
    by (intros A HA; exact (incl_firstn k _ A HA)).
  exists (firstn k (filter (containsb [v]) F)).
  split; [|split; [|split]].
  - intros A HA. apply Hsub, filter_In in HA; tauto.
  - apply NoDup_firstn, NoDup_filter; exact HndF.
  - apply firstn_length_le; exact Hk.
  - apply Forall_forall. intros A HA.
    apply Hsub, filter_In in HA as [_ Hc].
    apply containsb_true_iff in Hc. apply Hc; left; reflexivity.
Qed.

(** ** The characterisation *)

Theorem two_uniform_sunflower_iff :
  forall (k : nat) (F : Family),
    2 <= k -> Uniform 2 F -> Distinct F ->
    (ContainsKSunflower k F
     <-> HasKDisjoint k F \/ (exists v, k <= deg [v] F)).
Proof.
  intros k F Hk HU HD.
  assert (HUm : forall A, In A F -> length A = 2 /\ NoDup A).
  { unfold Uniform in HU; rewrite Forall_forall in HU; exact HU. }
  split.
  - (* A sunflower is a matching or a star. *)
    intros Hc.
    destruct (contains_sunflower_literal k F Hc)
      as [S [core [Hincl [Hnd [Hlen Hsun]]]]].
    assert (Hlen2 : 2 <= length S) by lia.
    destruct (sunflower_shape S core Hlen2 Hsun) as [Hpd | [v Hstar]].
    + left. exists S; repeat split; assumption.
    + right. exists v. rewrite <- Hlen.
      apply star_le_deg; assumption.
  - (* Both shapes are sunflowers. *)
    intros [[S [Hincl [Hnd [Hlen Hpd]]]] | [v Hv]].
    + (* Pairwise disjoint 2-sets: a sunflower with empty core. *)
      eapply ContainsKSunflower_of_incl; [exact Hincl | exact Hlen |].
      apply pairwise_disjoint_sunflower; [exact Hnd | | exact Hpd].
      apply Forall_forall. intros A HA.
      destruct (HUm A (Hincl A HA)) as [Hl _].
      intro E; rewrite E in Hl; discriminate.
    + (* A star: a sunflower with core [v]. *)
      assert (HndF : NoDup F) by (apply SetNoDup_NoDup; exact HD).
      destruct (deg_gives_star F v k HndF Hv)
        as [S [Hincl [Hnd [Hlen Hstar]]]].
      eapply ContainsKSunflower_of_incl; [exact Hincl | exact Hlen |].
      apply star_sunflower;
        [| apply (SetNoDup_incl HD Hnd Hincl) | exact Hstar].
      apply Forall_forall. intros A HA.
      unfold Uniform in HU; rewrite Forall_forall in HU.
      apply HU, Hincl, HA.
Qed.

(** The form the extremal problem is usually stated in: a distinct
    2-uniform family avoids [k]-sunflowers exactly when its matching
    number and its maximum degree are both at most [k-1].

    This is what makes [f(2,k)] the Chvátal–Hanson extremal problem
    rather than something merely bounded by it. The value
    [f(2,k) = CH(k-1,k-1) + 1] then follows from [ChHa76], which is
    cited rather than formalised — no theorem in this development
    depends on it. *)

Corollary two_uniform_sunflower_free_iff :
  forall (k : nat) (F : Family),
    2 <= k -> Uniform 2 F -> Distinct F ->
    (~ ContainsKSunflower k F
     <-> ~ HasKDisjoint k F /\ (forall v, deg [v] F < k)).
Proof.
  intros k F Hk HU HD.
  rewrite (two_uniform_sunflower_iff k F Hk HU HD).
  split.
  - intros Hno. split.
    + intro Hd; apply Hno; left; exact Hd.
    + intros v. destruct (Nat.lt_ge_cases (deg [v] F) k) as [Hlt | Hge];
        [exact Hlt|].
      exfalso; apply Hno; right; exists v; exact Hge.
  - intros [Hnd Hdeg] [Hd | [v Hv]]; [exact (Hnd Hd)|].
    specialize (Hdeg v); lia.
Qed.

(** ** The spread condition at uniformity 2 is a maximum-degree bound

    The formal content of the identification. [RaoSpread 2 F r] asks
    [deg T F <= r ^ (2 - |T|)] for every nonempty [T]. Only [|T| = 1]
    says anything: at [|T| >= 2] the bound is [r ^ 0 = 1], and a
    distinct family of 2-sets has at most one member containing a given
    set of two or more points. *)

Theorem rao_spread_two_iff_degree :
  forall (F : Family) (r : nat),
    Uniform 2 F -> Distinct F ->
    (RaoSpread 2 F r <-> forall v, deg [v] F <= r).
Proof.
  intros F r HU HD.
  assert (HUm : forall A, In A F -> length A = 2 /\ NoDup A).
  { unfold Uniform in HU; rewrite Forall_forall in HU; exact HU. }
  split.
  - intros Hspread v.
    assert (HndT : NoDup [v]) by (constructor; [intros [] | constructor]).
    assert (Hne : [v] <> []) by discriminate.
    specialize (Hspread [v] HndT Hne).
    replace (2 - length [v]) with 1 in Hspread by reflexivity.
    rewrite Nat.pow_1_r in Hspread. exact Hspread.
  - intros Hdeg T HndT HTne.
    destruct T as [|a T']; [exfalso; apply HTne; reflexivity|].
    destruct T' as [|b T''].
    + (* |T| = 1: exactly the degree bound. *)
      replace (2 - length [a]) with 1 by reflexivity.
      rewrite Nat.pow_1_r. apply Hdeg.
    + (* |T| >= 2: at most one member of a distinct family contains T. *)
      replace (2 - length (a :: b :: T'')) with 0 by (simpl; lia).
      rewrite Nat.pow_0_r.
      (* Two members containing [T] would both be set-equal to [T]. *)
      assert (Hcover : forall C, In C F -> Subset (a :: b :: T'') C ->
                                 SetEq (a :: b :: T'') C).
      { intros C HC HSub.
        destruct (HUm C HC) as [HlC _].
        split; [exact HSub|].
        unfold Subset in *.
        apply (NoDup_length_incl (l := a :: b :: T'') (l' := C));
          [exact HndT | rewrite HlC; simpl; lia | exact HSub]. }
      unfold deg.
      destruct (filter (containsb (a :: b :: T'')) F) as [|A [|B rest]] eqn:E;
        simpl; try lia.
      exfalso.
      assert (HndFil : NoDup (A :: B :: rest))
        by (rewrite <- E; apply NoDup_filter, SetNoDup_NoDup; exact HD).
      assert (HAin : In A (filter (containsb (a :: b :: T'')) F))
        by (rewrite E; left; reflexivity).
      assert (HBin : In B (filter (containsb (a :: b :: T'')) F))
        by (rewrite E; right; left; reflexivity).
      apply filter_In in HAin as [HAF HAc].
      apply filter_In in HBin as [HBF HBc].
      apply containsb_true_iff in HAc, HBc.
      assert (HAB : A <> B).
      { inversion HndFil as [|? ? Hni ?]; subst.
        intro Eq; apply Hni; left; symmetry; exact Eq. }
      apply (SetNoDup_pairwise HD HAF HBF HAB).
      apply SetEq_trans with (B := a :: b :: T'');
        [apply SetEq_sym; apply Hcover; assumption
        | apply Hcover; assumption].
Qed.

(** So the spread hypothesis at uniformity 2 *is* the graph statement:
    a simple graph with maximum degree at most [r] and more than [r^2]
    edges has [k] pairwise disjoint edges.

    That is the Chvátal–Hanson extremal problem at [D = r], [nu = k-1]:
    the hypothesis is refutable at [r] exactly when [CH(r, k-1)]
    exceeds [r ^ 2]. *)

Corollary spread_yields_disjoint_two_is_a_graph_statement :
  forall (k r : nat) (F : Family),
    SpreadYieldsDisjoint 2 k r ->
    Uniform 2 F -> Distinct F ->
    r ^ 2 < length F ->
    (forall v, deg [v] F <= r) ->
    HasKDisjoint k F.
Proof.
  intros k r F Hsyd HU HD Hsize Hdeg.
  destruct (Hsyd 2 F (Nat.le_succ_diag_r 1) (le_n 2) HU HD Hsize
              (proj2 (rao_spread_two_iff_degree F r HU HD) Hdeg))
    as [S [Hincl [Hnd [Hlen Hpd]]]].
  exists S; repeat split; assumption.
Qed.
