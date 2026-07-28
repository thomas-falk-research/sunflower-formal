(** * LinkCharacterisation.v -- A sunflower is a matching in a link.

    [TwoUniform.v] shows that at uniformity 2 a family has a
    [k]-sunflower exactly when it has [k] pairwise disjoint members or
    a vertex of degree [k]. That statement is about graphs, and it
    fails at uniformity 3: [{1,2,3}], [{1,2,4}], [{1,3,5}] share the
    point 1 and are not a sunflower.

    This file proves the statement the two-uniform one is a shadow of,
    at every uniformity and with no hypotheses at all:

    >  ContainsKSunflower k F  <->  exists Y, HasKDisjoint k (link Y F).

    The mathematics is one line of set algebra. For [Y ⊆ A, B],

    >  A ∩ B = Y   <->   (A \ Y) ∩ (B \ Y) = ∅,

    so a [k]-sunflower with core [Y] is exactly [k] members through [Y]
    whose petals are pairwise disjoint — and the petals through [Y] are
    what [Spread.link Y F] is. Both halves of the definition of a
    sunflower turn into one matching condition in one derived family.

    Three things this buys.

    **[Spread.link_sunflower_lift] becomes a characterisation.** That
    theorem lifts a sunflower out of a link; it has no converse in the
    file where it lives, so the link was a one-way reduction. Here it
    is one direction of an equivalence ([link_matching_gives_sunflower]
    is a two-line consequence of it), and the content added is the
    other direction: every sunflower *comes from* a link, over its own
    core.

    **The two-uniform characterisation is the case [|Y| <= 1].**
    [two_uniform_sunflower_iff_via_link] re-derives
    [TwoUniform.two_uniform_sunflower_iff] from the general statement
    plus one counting fact ([two_uniform_link_matching_iff]): in a
    distinct 2-uniform family, a link over a set of two or more points
    has at most one member, and a link over a single point is a family
    of singletons, whose matching number is just its size. That is the
    whole of the uniformity-2 theorem, and it is exactly what stops
    being true at uniformity 3 — where [{0,1}] is a core no singleton
    can stand in for.

    **The problem is re-indexed.** Sunflower-freeness at width [k] is
    the assertion that a family of matching problems — one per
    candidate core, all of them in derived families of strictly smaller
    uniformity — has no solution. [sunflower_core_lies_in_a_member]
    bounds which cores need checking.

    What it does not buy: nothing here bears on the conjecture's bound.
    The equivalence is a restatement, and the [log n] gap is not in the
    statement.

    Before any of this was proved, the equivalence was enumerated
    against a brute-force sunflower detector over every family on five
    and six points at uniformities 2 and 3, over every family of
    arbitrary sets on four points, and over a sample at ground 7 — see
    [rust/tests/link_characterisation.rs]. Two of the tests there earn
    their keep by killing readings of this statement that no uniform
    family distinguishes; see [SetNoDup_of_pairwise_disjoint] and
    [core_of_size_two_is_needed] for the two cases they found.

    Zero axioms, zero admits. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower ProductLowerBound Spread
                              SpreadReduction TwoUniform.
Import ListNotations.

(** ** Set algebra of petals *)

(** The identity the whole file rests on, in the direction that is
    used: if two members meet in [Y], their petals are disjoint. *)

Lemma disjoint_petals_of_inter :
  forall A B Y,
    SetEq (inter A B) Y -> Disjoint (setminus A Y) (setminus B Y).
Proof.
  intros A B Y [Hs _] x HA HB.
  apply in_setminus_iff in HA as [HxA HxY].
  apply in_setminus_iff in HB as [HxB _].
  apply HxY, Hs, in_inter_iff; split; assumption.
Qed.

(** ... and the converse, which is what makes the lifted family a
    sunflower rather than merely a family through [Y]. It is
    [Spread.inter_add_set] seen from the other side, and is recorded
    here because the equivalence is only as good as this direction. *)

Lemma inter_of_disjoint_petals :
  forall A B Y,
    Subset Y A -> Subset Y B ->
    Disjoint (setminus A Y) (setminus B Y) ->
    SetEq (inter A B) Y.
Proof.
  intros A B Y HYA HYB Hdis; split; intros x Hx.
  - apply in_inter_iff in Hx as [HxA HxB].
    destruct (in_dec_nat x Y) as [HxY | HxY]; [exact HxY|].
    exfalso; apply (Hdis x); apply in_setminus_iff; split; assumption.
  - apply in_inter_iff; split; [apply HYA | apply HYB]; exact Hx.
Qed.

(** Two disjoint sets that are equal *as sets* are both empty — and the
    only list with no elements is [[]], so they are literally equal.
    This is what makes the petal map injective. *)

Lemma Disjoint_SetEq_nil :
  forall A B, Disjoint A B -> SetEq A B -> A = [] /\ B = [].
Proof.
  intros A B Hdis [Hab Hba].
  destruct A as [|a A']; destruct B as [|b B'].
  - split; reflexivity.
  - exfalso; exact (Hba b (or_introl eq_refl)).
  - exfalso; exact (Hab a (or_introl eq_refl)).
  - exfalso; exact (Hdis a (or_introl eq_refl) (Hab a (or_introl eq_refl))).
Qed.

(** A member whose petal is empty *is* the core. This is the case a
    uniform family cannot exhibit twice, which is why it went unnoticed
    until the non-uniform enumeration. *)

Lemma setminus_nil_SetEq :
  forall A Y, Subset Y A -> setminus A Y = [] -> SetEq A Y.
Proof.
  intros A Y HYA Hnil; split; [|exact HYA].
  intros x Hx.
  destruct (in_dec_nat x Y) as [HxY | HxY]; [exact HxY|].
  exfalso.
  assert (Hin : In x (setminus A Y))
    by (apply in_setminus_iff; split; assumption).
  rewrite Hnil in Hin; exact Hin.
Qed.

(** ** Membership in a link *)

Lemma in_link_of_member :
  forall Y F A, In A F -> Subset Y A -> In (setminus A Y) (link Y F).
Proof.
  intros Y F A HA HY; unfold link.
  apply in_map_iff; exists A; split; [reflexivity|].
  apply filter_In; split; [exact HA | apply containsb_true_iff; exact HY].
Qed.

(** ** The core contains nothing a member does not

    Every member of a sunflower on at least two sets contains the core,
    because its intersection with *some other* member is the core.
    [TwoUniform.sunflower_shape] is the [|core| = 0] versus
    [|core| >= 1] case split of this. *)

Lemma sunflower_core_subset :
  forall S core,
    2 <= length S -> Sunflower S core ->
    Forall (fun A => Subset core A) S.
Proof.
  intros S core Hlen [Hsnd Hcore].
  apply Forall_forall; intros A HA.
  destruct (exists_other_member S A (SetNoDup_NoDup Hsnd) Hlen HA)
    as [B [HB Hne]].
  assert (HAB : A <> B) by (intro E; apply Hne; symmetry; exact E).
  destruct (Hcore A B HA HB HAB) as [_ Hs2].
  intros x Hx. apply Hs2, in_inter_iff in Hx; tauto.
Qed.

(** A [map] over a [NoDup] list stays [NoDup] when the function is
    injective on that list. *)

Lemma NoDup_map_inj :
  forall (f : list nat -> list nat) (l : list (list nat)),
    NoDup l ->
    (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
    NoDup (map f l).
Proof.
  intros f l Hnd; induction Hnd as [|a l Hni Hnd IH]; intros Hinj;
    simpl; [constructor|].
  constructor.
  - intro Hin. apply in_map_iff in Hin as [b [E Hb]].
    apply Hni.
    rewrite <- (Hinj a b (or_introl eq_refl) (or_intror Hb) (eq_sym E)) in Hb.
    exact Hb.
  - apply IH; intros x y Hx Hy; apply Hinj; right; assumption.
Qed.

(** ** A sunflower is a matching in the link over its core *)

Theorem sunflower_gives_link_matching :
  forall k F,
    2 <= k -> ContainsKSunflower k F ->
    exists Y, (exists A, In A F /\ Subset Y A) /\ HasKDisjoint k (link Y F).
Proof.
  intros k F Hk Hc.
  destruct (contains_sunflower_literal k F Hc)
    as [S [core [Hincl [Hnd [Hlen Hsun]]]]].
  assert (Hlen2 : 2 <= length S) by lia.
  pose proof (sunflower_core_subset S core Hlen2 Hsun) as Hsub.
  rewrite Forall_forall in Hsub.
  destruct Hsun as [Hsnd Hcore].
  (* Distinct members have disjoint petals: their intersection is the
     core, so nothing outside the core survives in both. *)
  assert (Hdis : forall A B, In A S -> In B S -> A <> B ->
                             Disjoint (setminus A core) (setminus B core)).
  { intros A B HA HB Hne.
    apply disjoint_petals_of_inter, (Hcore A B HA HB Hne). }
  (* Distinct members have *distinct* petals: two equal petals would be
     disjoint from each other, hence both empty, hence both members
     equal to the core and so to each other. *)
  assert (Hinj : forall A B, In A S -> In B S ->
                   setminus A core = setminus B core -> A = B).
  { intros A B HA HB Heq.
    destruct (list_eq_dec Nat.eq_dec A B) as [E | Hne]; [exact E|].
    exfalso.
    pose proof (Hdis A B HA HB Hne) as Hd.
    rewrite Heq in Hd.
    destruct (Disjoint_SetEq_nil _ _ Hd (SetEq_refl _)) as [_ Hnil].
    rewrite <- Heq in Hnil.
    pose proof (setminus_nil_SetEq A core (Hsub A HA) Hnil) as HAc.
    rewrite Heq in Hnil.
    pose proof (setminus_nil_SetEq B core (Hsub B HB) Hnil) as HBc.
    apply (SetNoDup_pairwise Hsnd HA HB Hne).
    apply SetEq_trans with (B := core); [exact HAc | apply SetEq_sym; exact HBc]. }
  exists core; split.
  - (* The core lies inside a member: [S] is nonempty because k >= 2. *)
    destruct S as [|A S']; [simpl in Hlen2; lia|].
    exists A; split;
      [apply Hincl; left; reflexivity | apply Hsub; left; reflexivity].
  - exists (map (fun A => setminus A core) S).
    split; [|split; [|split]].
    + intros B HB. apply in_map_iff in HB as [A [E HA]]; subst B.
      apply in_link_of_member; [apply Hincl; exact HA | apply Hsub; exact HA].
    + apply NoDup_map_inj; assumption.
    + rewrite map_length; exact Hlen.
    + intros B C HB HC Hne.
      apply in_map_iff in HB as [A [EA HA]].
      apply in_map_iff in HC as [A' [EA' HA']].
      subst B C.
      apply Hdis; [exact HA | exact HA' |].
      intro E; subst A'; apply Hne; reflexivity.
Qed.

(** ** A matching in a link is a sunflower

    This direction needs no hypothesis on [k] and none on [F]: it is
    [Spread.link_sunflower_lift] applied to the empty-core sunflower
    that [k] pairwise disjoint sets already are.

    The empty core is where the strengthening of
    [Sunflower.pairwise_disjoint_sunflower] is used. If that lemma
    still required nonempty members, this proof would need every petal
    to be nonempty — which excludes exactly the families containing
    their own core, and breaks the equivalence. *)

Theorem link_matching_gives_sunflower :
  forall k F Y, HasKDisjoint k (link Y F) -> ContainsKSunflower k F.
Proof.
  intros k F Y [S [Hincl [Hnd [Hlen Hpd]]]].
  apply (@link_sunflower_lift Y F k).
  exists S; split; [apply SubFamilySetEq_incl; exact Hincl|].
  split; [exact Hlen|].
  exists []; apply pairwise_disjoint_sunflower; assumption.
Qed.

(** ** The degenerate widths

    [k <= 1] is not interesting but it is not excluded either, and the
    equivalence should not need a side condition a reader has to check.
    A [0]-sunflower is the empty sub-family and a [1]-sunflower is any
    single member, so both are decided by whether [F] is empty — as is
    the link over the empty core. *)

Lemma setminus_nil : forall A, setminus A [] = A.
Proof.
  induction A as [|a A IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma link_nil : forall F, link [] F = F.
Proof.
  induction F as [|A F IH]; simpl; [reflexivity|].
  unfold link in *; simpl; rewrite setminus_nil, IH; reflexivity.
Qed.

Lemma small_sunflower_gives_link_matching :
  forall k F, k <= 1 -> ContainsKSunflower k F -> HasKDisjoint k (link [] F).
Proof.
  intros k F Hk [S [Hsub [Hlen _]]].
  rewrite link_nil.
  destruct k as [|k'].
  - exists []; split; [apply incl_nil_l | split; [constructor | split; [reflexivity|]]].
    intros A B [] _ _.
  - assert (Hk' : k' = 0) by lia; subst k'.
    destruct S as [|A S']; [discriminate|].
    destruct (Hsub A (or_introl eq_refl)) as [B [HB _]].
    exists [B]; split; [|split; [|split]].
    + intros C [E | []]; subst C; exact HB.
    + constructor; [intros [] | constructor].
    + reflexivity.
    + intros C D [E | []] [E' | []] Hne; subst C D; contradiction.
Qed.

(** ** The characterisation *)

Theorem sunflower_iff_link_matching :
  forall k F,
    ContainsKSunflower k F <-> exists Y, HasKDisjoint k (link Y F).
Proof.
  intros k F; split.
  - intros Hc.
    destruct (Nat.le_gt_cases k 1) as [Hk | Hk].
    + exists []; apply small_sunflower_gives_link_matching; assumption.
    + destruct (sunflower_gives_link_matching k F ltac:(lia) Hc) as [Y [_ HY]].
      exists Y; exact HY.
  - intros [Y HY]; exact (link_matching_gives_sunflower k F Y HY).
Qed.

(** Which cores need checking: only the subsets of members. A [Y]
    contained in no member has an empty link, which carries a matching
    only at [k = 0]. *)

Corollary sunflower_core_lies_in_a_member :
  forall k F,
    2 <= k -> ContainsKSunflower k F ->
    exists Y A, In A F /\ Subset Y A /\ HasKDisjoint k (link Y F).
Proof.
  intros k F Hk Hc.
  destruct (sunflower_gives_link_matching k F Hk Hc) as [Y [[A [HA HYA]] HY]].
  exists Y, A; repeat split; assumption.
Qed.

(** The empty core is the plain disjointness question, so
    [Audit.no_k_disjoint_of_no_sunflower] is the [Y = []] instance of
    the right-hand side rather than an unrelated fact. *)

Corollary k_disjoint_gives_sunflower :
  forall k F, HasKDisjoint k F -> ContainsKSunflower k F.
Proof.
  intros k F H.
  apply (link_matching_gives_sunflower k F []); rewrite link_nil; exact H.
Qed.

(** ** Degree monotonicity

    A bigger set is contained in fewer members. Used to turn a matching
    in a link over [Y] into a degree bound at any point of [Y]. *)

Lemma deg_mono : forall T T' F, Subset T T' -> deg T' F <= deg T F.
Proof.
  intros T T' F Hsub; unfold deg.
  induction F as [|A F IH]; simpl; [lia|].
  destruct (containsb T' A) eqn:E1; destruct (containsb T A) eqn:E2;
    simpl; try lia.
  exfalso.
  apply containsb_true_iff in E1.
  assert (E3 : containsb T A = true)
    by (apply containsb_true_iff; intros x Hx; apply E1, Hsub, Hx).
  congruence.
Qed.

(** A matching of size [k] in a link over [Y] forces every point of [Y]
    to have degree at least [k]. No uniformity: the members counted by
    the link all contain [Y], hence all contain each of its points. *)

Lemma link_matching_bounds_degree :
  forall k F Y v,
    In v Y -> HasKDisjoint k (link Y F) -> k <= deg [v] F.
Proof.
  intros k F Y v Hv [S [Hincl [Hnd [Hlen _]]]].
  assert (Hle : length S <= deg Y F)
    by (rewrite <- (length_link Y F); apply NoDup_incl_length; assumption).
  assert (Hmono : deg Y F <= deg [v] F)
    by (apply deg_mono; intros x [E | []]; subst x; exact Hv).
  lia.
Qed.

(** ** The two-uniform characterisation as the case [|Y| <= 1]

    Two counting facts, and then [TwoUniform.two_uniform_sunflower_iff]
    falls out of the general statement. *)

(** A link over a single point in a 2-uniform family is a family of
    *singletons*. Distinct singletons are automatically disjoint, so
    the matching number of that link is its size, which is
    [deg [v] F]. *)

Lemma two_uniform_link_singleton_matching :
  forall F v k,
    Uniform 2 F -> Distinct F ->
    (HasKDisjoint k (link [v] F) <-> k <= deg [v] F).
Proof.
  intros F v k HU HD.
  assert (HndT : NoDup [v]) by (constructor; [intros [] | constructor]).
  pose proof (@link_uniform 2 [v] F HU HndT) as HLU.
  replace (2 - length [v]) with 1 in HLU by reflexivity.
  pose proof (@link_distinct [v] F HD) as HLD.
  split.
  - intros H. apply (link_matching_bounds_degree k F [v] v);
      [left; reflexivity | exact H].
  - intros Hk.
    (* The first [k] members of the link are pairwise disjoint. *)
    exists (firstn k (link [v] F)).
    assert (Hsub : incl (firstn k (link [v] F)) (link [v] F))
      by (apply incl_firstn).
    split; [exact Hsub | split; [|split]].
    + apply NoDup_firstn, SetNoDup_NoDup; exact HLD.
    + apply firstn_length_le; rewrite length_link; exact Hk.
    + intros A B HA HB Hne.
      pose proof (Hsub A HA) as HAL; pose proof (Hsub B HB) as HBL.
      (* Two literally distinct singletons are disjoint outright. *)
      unfold Uniform in HLU; rewrite Forall_forall in HLU.
      destruct (HLU A HAL) as [HlA _]; destruct (HLU B HBL) as [HlB _].
      destruct A as [|a [|? ?]]; simpl in HlA; try discriminate.
      destruct B as [|b [|? ?]]; simpl in HlB; try discriminate.
      intros x [E | []] [E' | []]; apply Hne; subst; reflexivity.
Qed.

(** A link over a core containing two distinct points has at most one
    member, because a distinct 2-uniform family has at most one member
    containing a given pair. So no such core can carry a matching of
    size 2 or more.

    This is the fact that stops being true at uniformity 3: there
    [{0,1}] is a core no singleton can stand in for, which
    [Audit.core_of_size_two_is_needed] exhibits. *)

Lemma two_uniform_deg_of_pair :
  forall F Y u v,
    Uniform 2 F -> Distinct F -> In u Y -> In v Y -> u <> v ->
    deg Y F <= 1.
Proof.
  intros F Y u v HU HD Hu Hv Huv.
  assert (HUm : forall A, In A F -> length A = 2 /\ NoDup A).
  { unfold Uniform in HU; rewrite Forall_forall in HU; exact HU. }
  assert (Hnd : NoDup [u; v]).
  { constructor.
    - intros [E | []]; apply Huv; symmetry; exact E.
    - constructor; [intros [] | constructor]. }
  (* Every member containing the pair is set-equal to it, by size. *)
  assert (Hcover : forall C, In C F -> Subset [u; v] C -> SetEq [u; v] C).
  { intros C HC HSub.
    destruct (HUm C HC) as [HlC _].
    split; [exact HSub|].
    apply (NoDup_length_incl (l := [u; v]) (l' := C));
      [exact Hnd | rewrite HlC; simpl; lia | exact HSub]. }
  assert (Hpair : deg [u; v] F <= 1).
  { unfold deg.
    destruct (filter (containsb [u; v]) F) as [|A [|B rest]] eqn:E;
      simpl; try lia.
    exfalso.
    assert (HndFil : NoDup (A :: B :: rest))
      by (rewrite <- E; apply NoDup_filter, SetNoDup_NoDup; exact HD).
    assert (HAin : In A (filter (containsb [u; v]) F))
      by (rewrite E; left; reflexivity).
    assert (HBin : In B (filter (containsb [u; v]) F))
      by (rewrite E; right; left; reflexivity).
    apply filter_In in HAin as [HAF HAc].
    apply filter_In in HBin as [HBF HBc].
    apply containsb_true_iff in HAc, HBc.
    assert (HAB : A <> B).
    { inversion HndFil as [|? ? Hni ?]; subst.
      intro Eq; apply Hni; left; symmetry; exact Eq. }
    apply (SetNoDup_pairwise HD HAF HBF HAB).
    apply SetEq_trans with (B := [u; v]);
      [apply SetEq_sym; apply Hcover; assumption | apply Hcover; assumption]. }
  assert (Hmono : deg Y F <= deg [u; v] F).
  { apply deg_mono; intros x [E | [E | []]]; subst x; assumption. }
  lia.
Qed.

Corollary two_uniform_link_big_core :
  forall F Y u v k,
    Uniform 2 F -> Distinct F -> In u Y -> In v Y -> u <> v -> 2 <= k ->
    ~ HasKDisjoint k (link Y F).
Proof.
  intros F Y u v k HU HD Hu Hv Huv Hk [S [Hincl [Hnd [Hlen _]]]].
  pose proof (two_uniform_deg_of_pair F Y u v HU HD Hu Hv Huv) as Hdeg.
  assert (Hle : length S <= deg Y F)
    by (rewrite <- (length_link Y F); apply NoDup_incl_length; assumption).
  lia.
Qed.

(** So at uniformity 2 the search over candidate cores collapses: any
    core that carries a matching of size [>= 2] has at most one point.
    This is the exact sense in which [TwoUniform.v] is the case
    [|Y| <= 1] of this file. *)

Corollary two_uniform_only_small_cores :
  forall k F Y,
    2 <= k -> Uniform 2 F -> Distinct F ->
    HasKDisjoint k (link Y F) ->
    forall u v, In u Y -> In v Y -> u = v.
Proof.
  intros k F Y Hk HU HD Hm u v Hu Hv.
  destruct (Nat.eq_dec u v) as [E | Hne]; [exact E|].
  exfalso; exact (two_uniform_link_big_core F Y u v k HU HD Hu Hv Hne Hk Hm).
Qed.

(** ** Above uniformity 2, small cores do not suffice

    [two_uniform_only_small_cores] is the whole reason the sunflower
    problem is a graph problem at uniformity 2. It is false at every
    higher uniformity, and this is why: a family whose members all
    share two distinct points has *no* core of size at most one that
    works, because a link over such a core still passes through one of
    the two shared points.

    So the [exists Y] in the characterisation is quantifying over
    something: at uniformity 2 it collapses to a search over [∅] and
    the vertices, and above it does not. [Audit.core_of_size_two_is_
    needed] gives the smallest 3-uniform witness. *)

Lemma no_matching_of_common_point :
  forall k F v,
    2 <= k -> Forall (fun A => In v A) F -> ~ HasKDisjoint k F.
Proof.
  intros k F v Hk Hcom [S [Hincl [Hnd [Hlen Hpd]]]].
  assert (Hlen2 : 2 <= length S) by lia.
  destruct S as [|A S']; [simpl in Hlen2; lia|].
  destruct (exists_other_member (A :: S') A Hnd Hlen2 (or_introl eq_refl))
    as [B [HB Hne]].
  rewrite Forall_forall in Hcom.
  apply (Hpd A B (or_introl eq_refl) HB
             ltac:(intro E; apply Hne; symmetry; exact E) v);
    apply Hcom, Hincl; [left; reflexivity | exact HB].
Qed.

(** A point shared by every member and missing from the core is shared
    by every member of the link. *)

Lemma link_preserves_common_point :
  forall Y F v,
    ~ In v Y -> Forall (fun A => In v A) F ->
    Forall (fun B => In v B) (link Y F).
Proof.
  intros Y F v HvY Hcom; apply Forall_forall; intros B HB.
  apply in_link_inv in HB as [A [HAF [_ E]]]; subst B.
  rewrite Forall_forall in Hcom.
  apply in_setminus_iff; split; [apply Hcom; exact HAF | exact HvY].
Qed.

Theorem two_common_points_force_a_big_core :
  forall k F u v Y,
    2 <= k -> u <> v ->
    Forall (fun A => In u A) F -> Forall (fun A => In v A) F ->
    HasKDisjoint k (link Y F) ->
    exists a b, In a Y /\ In b Y /\ a <> b.
Proof.
  intros k F u v Y Hk Huv Hu Hv Hm.
  (* [Y] cannot contain both [u] and [v] without containing two
     distinct points; whichever it misses is shared by the whole link. *)
  destruct (in_dec_nat u Y) as [HuY | HuY];
    [destruct (in_dec_nat v Y) as [HvY | HvY]|].
  - exists u, v; repeat split; assumption.
  - exfalso; apply (no_matching_of_common_point k (link Y F) v Hk);
      [apply link_preserves_common_point; assumption | exact Hm].
  - exfalso; apply (no_matching_of_common_point k (link Y F) u Hk);
      [apply link_preserves_common_point; assumption | exact Hm].
Qed.

Corollary sunflower_core_of_two_common_points :
  forall k F u v,
    2 <= k -> u <> v ->
    Forall (fun A => In u A) F -> Forall (fun A => In v A) F ->
    ContainsKSunflower k F ->
    exists Y, (exists a b, In a Y /\ In b Y /\ a <> b)
              /\ HasKDisjoint k (link Y F).
Proof.
  intros k F u v Hk Huv Hu Hv Hc.
  destruct (proj1 (sunflower_iff_link_matching k F) Hc) as [Y HY].
  exists Y; split;
    [exact (two_common_points_force_a_big_core k F u v Y Hk Huv Hu Hv HY) | exact HY].
Qed.

(** ** The core matters only up to set equality

    [Spread.deg_setEq] says the degree does; this says the whole link
    does, and literally so. Without it the [exists Y] would be
    quantifying over list representations rather than over sets, and
    the characterisation would be a statement about the encoding. *)

Lemma memb_ext_setEq :
  forall Y Y', Subset Y Y' -> Subset Y' Y ->
    forall x, memb x Y = memb x Y'.
Proof.
  intros Y Y' H1 H2 x.
  destruct (memb x Y) eqn:E1; destruct (memb x Y') eqn:E2; try reflexivity.
  - apply memb_true_iff in E1; apply memb_false_iff in E2.
    exfalso; apply E2, H1, E1.
  - apply memb_true_iff in E2; apply memb_false_iff in E1.
    exfalso; apply E1, H2, E2.
Qed.

Lemma link_setEq :
  forall Y Y' F, Subset Y Y' -> Subset Y' Y -> link Y F = link Y' F.
Proof.
  intros Y Y' F H1 H2.
  pose proof (memb_ext_setEq Y Y' H1 H2) as Hmemb.
  unfold link.
  rewrite (filter_ext_eq (containsb Y) (containsb Y') F).
  - apply map_ext; intros A; unfold setminus.
    apply filter_ext_eq; intros x; rewrite Hmemb; reflexivity.
  - intros A.
    destruct (containsb Y A) eqn:EA; destruct (containsb Y' A) eqn:EB;
      try reflexivity; exfalso.
    + rewrite containsb_true_iff in EA.
      assert (E : containsb Y' A = true)
        by (apply containsb_true_iff; intros x Hx; apply EA, H2, Hx).
      congruence.
    + rewrite containsb_true_iff in EB.
      assert (E : containsb Y A = true)
        by (apply containsb_true_iff; intros x Hx; apply EB, H1, Hx).
      congruence.
Qed.

(** ** [TwoUniform.two_uniform_sunflower_iff], re-derived

    The general characterisation plus the two counting facts. The
    original proof goes through [sunflower_shape] and
    [star_sunflower]; this one never mentions either, and the agreement
    of two independent routes to the same statement is the point of
    writing it twice. *)

Theorem two_uniform_sunflower_iff_via_link :
  forall (k : nat) (F : Family),
    2 <= k -> Uniform 2 F -> Distinct F ->
    (ContainsKSunflower k F
     <-> HasKDisjoint k F \/ (exists v, k <= deg [v] F)).
Proof.
  intros k F Hk HU HD; split.
  - intros Hc.
    destruct (sunflower_gives_link_matching k F Hk Hc) as [Y [_ HY]].
    (* Either the core is empty -- plain disjointness -- or it has a
       point, whose degree the matching bounds below. *)
    destruct Y as [|v Y'].
    + left; rewrite link_nil in HY; exact HY.
    + right; exists v.
      apply (link_matching_bounds_degree k F (v :: Y') v);
        [left; reflexivity | exact HY].
  - intros [Hd | [v Hv]].
    + apply k_disjoint_gives_sunflower; exact Hd.
    + apply (link_matching_gives_sunflower k F [v]).
      apply (proj2 (two_uniform_link_singleton_matching F v k HU HD)); exact Hv.
Qed.
