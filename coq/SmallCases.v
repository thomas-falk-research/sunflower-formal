(** * SmallCases.v -- Exact values of f(n, k) for small parameters.

    Theorems proved here:

    - [f_n_2_eq_2]: every two distinct sets are a 2-sunflower, so
      [UpperBound n 2 2] holds for every [n ≥ 1]. Combined with the
      trivial fact that [UpperBound n 2 1] does *not* hold, we get
      [f(n, 2) = 2].

    - [f_1_k_eq_k]: every [k] distinct 1-uniform (singleton) sets are
      pairwise disjoint, so they form a [k]-sunflower with empty core.
      [UpperBound 1 k k] holds. Combined with the lower bound proving
      [UpperBound 1 k (k-1)] does *not* hold (from [LowerBound.v]), we
      get [f(1, k) = k].

    These two theorems pin down [f] on the boundary of its domain. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower LowerBound.
Import ListNotations.

Set Implicit Arguments.

(** ** [f(n, 2) = 2]: any two distinct sets form a 2-sunflower

    The 2-sunflower with core [A ∩ B] is automatic: pairwise
    intersection condition has exactly one constraint (A, B), which
    asks SetEq(A ∩ B)(A ∩ B), trivially true. *)

Theorem upper_bound_n_2 :
  forall n, 1 <= n -> UpperBound n 2 2.
Proof.
  intros n Hn F HU HD Hsize.
  destruct F as [|A [|B F']]; simpl in Hsize; try lia.
  exists [A; B]. split.
  - apply SubFamilySetEq_incl. intros X HX; simpl in HX.
    destruct HX as [E | [E | F0]]; subst; [left; reflexivity | right; left; reflexivity | inversion F0].
  - split; [reflexivity|]. exists (inter A B).
    split.
    + (* SetNoDup [A; B] *)
      inversion HD as [|? ? HniA HD']; subst.
      constructor.
      * intros C HC Hseq. simpl in HC. destruct HC as [E | F0]; [|inversion F0].
        subst C. apply (HniA B); [left; reflexivity | exact Hseq].
      * inversion HD' as [|? ? HniB HD'']; subst.
        constructor; [intros C HC; inversion HC | constructor].
    + intros X Y HX HY HXY.
      simpl in HX, HY.
      assert (Hcase : (X = A /\ Y = B) \/ (X = B /\ Y = A)).
      { destruct HX as [EX | [EX | []]]; destruct HY as [EY | [EY | []]];
          try (exfalso; apply HXY; rewrite <- EX, <- EY; reflexivity).
        - left; split; symmetry; assumption.
        - right; split; symmetry; assumption. }
      destruct Hcase as [[-> ->] | [-> ->]].
      * apply SetEq_refl.
      * apply SetEq_sym.
        unfold SetEq, Subset; split; intros y Hy;
          apply in_inter_iff in Hy as [Hy1 Hy2]; apply in_inter_iff; tauto.
Qed.

(** And the matching lower bound: [UpperBound n 2 1] cannot hold,
    because a singleton family has no 2-sunflower. *)

Theorem not_upper_bound_n_2_1 : forall n, 1 <= n -> ~ UpperBound n 2 1.
Proof.
  intros n Hn Hup.
  pose proof (lower_bound_trivial Hn (le_n 2)) as [F [HU [HD [Hlen Hno]]]].
  simpl in Hlen.
  apply Hno. apply Hup; auto; lia.
Qed.

Theorem f_n_2_eq_2 :
  forall n, 1 <= n -> UpperBound n 2 2 /\ ~ UpperBound n 2 1.
Proof.
  intros n Hn; split; [apply upper_bound_n_2 | apply not_upper_bound_n_2_1]; exact Hn.
Qed.

(** ** [f(1, k) = k]: k distinct singletons form a k-sunflower

    Each 1-uniform set is a singleton with one element. Distinct
    singletons are pairwise disjoint, hence form a sunflower with
    empty core. *)

Lemma uniform_1_singleton :
  forall A, UniformSet 1 A -> exists a, A = [a].
Proof.
  intros A [Hlen Hnd].
  destruct A as [|a [|b A']]; simpl in Hlen; try lia.
  exists a; reflexivity.
Qed.

Lemma singleton_pairwise_disjoint :
  forall (F : Family),
    Uniform 1 F -> Distinct F ->
    PairwiseDisjoint F.
Proof.
  intros F HU HD. unfold PairwiseDisjoint.
  intros A B HA HB HAB.
  unfold Uniform in HU; rewrite Forall_forall in HU.
  pose proof (uniform_1_singleton (HU A HA)) as [a Ea].
  pose proof (uniform_1_singleton (HU B HB)) as [b Eb].
  subst A B.
  assert (Hab : a <> b) by (intro E; subst; apply HAB; reflexivity).
  intros x HxA HxB; simpl in HxA, HxB.
  destruct HxA as [E1 | []]; destruct HxB as [E2 | []]; subst; contradiction.
Qed.

Theorem upper_bound_1_k :
  forall k, 2 <= k -> UpperBound 1 k k.
Proof.
  intros k Hk F HU HD Hsize.
  set (Sk := firstn k F).
  assert (HSklen : length Sk = k).
  { unfold Sk; apply firstn_length_le; lia. }
  assert (HSkincl : incl Sk F).
  { unfold incl, Sk. intros B HB.
    rewrite <- (firstn_skipn k F). apply in_or_app; left; exact HB. }
  assert (HSknd : NoDup Sk).
  { unfold Sk. apply SetNoDup_NoDup in HD.
    clear Hk Hsize HSklen HSkincl Sk HU.
    revert k HD. revert F.
    intros L. induction L as [|a L IH]; intros k Hnd; simpl.
    - destruct k; constructor.
    - destruct k as [|k']; [constructor|].
      inversion Hnd as [|? ? HniA Hnd']; subst.
      constructor.
      + intro Hin. apply HniA. rewrite <- (firstn_skipn k' L).
        apply in_or_app; left; exact Hin.
      + apply IH; exact Hnd'. }
  assert (HSkne : Forall (fun A : list nat => A <> []) Sk).
  { apply Forall_forall; intros A HA. apply HSkincl in HA.
    unfold Uniform in HU; rewrite Forall_forall in HU.
    pose proof (uniform_1_singleton (HU A HA)) as [a E]; subst A; discriminate. }
  assert (HSkpd : PairwiseDisjoint Sk).
  { unfold PairwiseDisjoint. intros A B HA HB HAB.
    apply HSkincl in HA; apply HSkincl in HB.
    pose proof (singleton_pairwise_disjoint HU HD) as Hpd.
    apply Hpd; auto. }
  exists Sk. split.
  - apply SubFamilySetEq_incl; exact HSkincl.
  - apply k_pairwise_disjoint_sunflower; auto.
Qed.

Theorem not_upper_bound_1_k :
  forall k, 2 <= k -> ~ UpperBound 1 k (k - 1).
Proof.
  intros k Hk Hup.
  pose proof (lower_bound_trivial (le_n 1) Hk) as [F [HU [HD [Hlen Hno]]]].
  apply Hno. apply Hup; auto; lia.
Qed.

Theorem f_1_k_eq_k :
  forall k, 2 <= k -> UpperBound 1 k k /\ ~ UpperBound 1 k (k - 1).
Proof.
  intros k Hk; split; [apply upper_bound_1_k | apply not_upper_bound_1_k]; exact Hk.
Qed.
