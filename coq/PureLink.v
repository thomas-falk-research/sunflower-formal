(** * PureLink.v -- the pure link is intersecting, and the recursion that buys.

    [Intersecting.sunflower_free_star_bound] proves [g(b) <= 2b*iota(b)]
    and [Intersecting.intersecting_link_bound] proves
    [iota(b) <= b*g(b-1)]. Both throw away the same thing: they take a
    cover [T] of the family, find *one* popular point of it by
    pigeonhole, and forget the other points of [T] entirely.

    This file counts over all of [T] at once, and adds the observation
    that makes the count worth doing.

    ** The observation

    Let [F] be [b]-uniform and 3-sunflower-free, let [M] be a maximal
    pairwise-disjoint subfamily — at most two members, since three would
    be a sunflower with empty core — and let [T = concat M], so every
    member of [F] meets [T]. Call a member *pure at [x]* when it meets
    [T] in [x] and in nothing else. Then:

    >  the pure members through [x], with [x] removed, form an
    >  **intersecting** family.

    Because if [A] and [B] are pure at [x] and [A \ x] misses [B \ x],
    then [A \ x], [B \ x] and [A_0 \ x] — where [A_0] is the member of
    [M] through [x] — are three pairwise disjoint members of the link at
    [x]: the first two miss [A_0 \ x] precisely because [A_0 ⊆ T] and
    purity says [A ∩ T = B ∩ T = {x}]. Three pairwise disjoint sets are
    a sunflower with empty core, and [Spread.link_sunflower_lift] carries
    it back to a sunflower in [F] with core [x].

    So the pure part of the link is bounded by [iota(b-1)], not merely by
    [g(b-1)] — and the pure members are exactly the ones the degree count
    charges only once.

    ** The recursion

    Writing [Ng] for a bound on [g(b-1)] and [Ni] for one on [iota(b-1)],
    double counting [sum over x in T of deg(x) = sum over A of |A ∩ T|]
    against [2|F| <= |pure| + sum over A of |A ∩ T|] gives

    >  2 * |F|  <=  |T| * (Ng + Ni).

    With [|T| <= 2b] that is [g(b) <= b * (g(b-1) + iota(b-1))], and for
    an intersecting [F] — where [T] is a single member and [|T| = b] —
    it is [2 * iota(b) <= b * (g(b-1) + iota(b-1))].

    ** What it gives

    Erdős–Rado's recursion is [g(b) <= 2b * g(b-1)]. Since
    [g(m) >= 2 iota(m)] ([Intersecting.doubling_lower_bound]), the
    recursion here is never worse and is a factor [4/3] better whenever
    the doubling is tight. At the values this development knows exactly
    it is sharp at both ends:

    <<
      b     this recursion            Erdős–Rado      truth
      1     iota(1) <= 1, g(1) <= 2       -           1, 2     exact
      2     iota(2) <= 3, g(2) <= 6      g(2) <= 12   3, 6     exact
      3     iota(3) <= 13, g(3) <= 27    g(3) <= 36   10, >= 20
    >>

    [g(3) <= 27] is [f(3,3) <= 28], where this development previously
    had only Erdős–Rado's 49 and where [Sharp.sharp_beats_erdos_rado_at_three]
    reaches 32 *conditionally*. [iota(3) <= 13] replaces
    [Intersecting.iota_three_at_most_eighteen].

    No novelty is claimed for the recursion. It is elementary, and both
    [AHS72] and [Sp77] are index-confirmed closed access
    ([docs/reading.md]); a search of the open corpus under "sunflower",
    "delta-system", "strong delta-system", "Erdős–Rado bound",
    "intersecting" and "link" did not turn it up, which given rule 5 of
    [docs/roadmap.md] §18.6 is worth very little.

    ** The support bound, and why [iota(3) = 10] is now decided

    [iota_support_bound] is the other half of the file and is three lines:
    in an intersecting family every member meets a fixed member, so
    contributes at most [b-1] new points, and an [n]-member intersecting
    [b]-uniform family therefore has support at most [b + (b-1)(n-1)].

    That turns [IotaAtMost b N] — a statement quantified over every
    ground set — into a search on [b + (b-1)N] points. At [b = 3] and
    [N = 10] the bound is 23, and `wide::tests::iota_three_is_exactly_ten`
    reports the ground-23 search exhaustively empty at eleven members. So [iota(3)]
    is exactly 10, where the development previously had [[10, 18]]. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower Spread Pigeonhole ErdosRado
                             SpreadReduction F23 Intersecting IotaRate IotaGround Product.
Import ListNotations.

Set Implicit Arguments.

(** ** Counting a family against a point set

    [IotaGround] already has this layer and it is reused rather than
    rebuilt: [degsum U F] sums the degree over the points of [U],
    [sizesum U F] sums [|A ∩ U|] over the members, [degsum_eq_sizesum] is
    the identity between them, and [degsum_le] bounds the first by
    [|U| * N]. Rule 1 of [docs/roadmap.md] §18.6, applied to this file
    after it had been written the other way.

    The one thing added is a name for [sizesum]'s summand, because the
    partition below filters on it. *)

Definition meets (X A : list nat) : nat :=
  length (filter (fun x => memb x A) X).

Lemma sizesum_cons : forall X A F, sizesum X (A :: F) = meets X A + sizesum X F.
Proof. reflexivity. Qed.

(** ** The pure part

    [purefam X F] is the members meeting [X] exactly once. *)

Definition purefam (X : list nat) (F : Family) : Family :=
  filter (fun A => Nat.eqb (meets X A) 1) F.

Lemma purefam_incl : forall X F, incl (purefam X F) F.
Proof. intros X F A HA; apply filter_In in HA; tauto. Qed.

Lemma purefam_meets_one :
  forall X F A, In A (purefam X F) -> meets X A = 1.
Proof.
  intros X F A HA; apply filter_In in HA as [_ E].
  apply Nat.eqb_eq in E; exact E.
Qed.

(** Every member meets [X], so a member outside the pure part meets it at
    least twice. That is the whole content of the count: the pure members
    are charged once and everything else twice. *)

Lemma sizesum_lower :
  forall X F,
    (forall A, In A F -> 1 <= meets X A) ->
    2 * length F <= length (purefam X F) + sizesum X F.
Proof.
  intros X F; induction F as [|A F IH]; intros H; [simpl; lia|].
  assert (HA : 1 <= meets X A) by (apply H; left; reflexivity).
  assert (Hrest : 2 * length F <= length (purefam X F) + sizesum X F)
    by (apply IH; intros B HB; apply H; right; exact HB).
  rewrite sizesum_cons.
  change (purefam X (A :: F)) with
    (if Nat.eqb (meets X A) 1 then A :: purefam X F else purefam X F).
  destruct (Nat.eqb (meets X A) 1) eqn:E.
  - apply Nat.eqb_eq in E; simpl length; lia.
  - apply Nat.eqb_neq in E; simpl length; lia.
Qed.

Lemma sizesum_pure :
  forall X G, (forall A, In A G -> meets X A = 1) -> sizesum X G = length G.
Proof.
  intros X G; induction G as [|A G IH]; intros H; [reflexivity|].
  rewrite sizesum_cons, (H A (or_introl eq_refl)), IH; [reflexivity|].
  intros B HB; apply H; right; exact HB.
Qed.

Lemma purefam_degsum :
  forall X F, length (purefam X F) = degsum X (purefam X F).
Proof.
  intros X F; rewrite degsum_eq_sizesum, sizesum_pure; [reflexivity|].
  intros A HA; exact (purefam_meets_one X F A HA).
Qed.

(** ** The pure link is intersecting

    The one new thing in the file. *)

Lemma meets_one_forces :
  forall X A x y,
    meets X A = 1 -> In x X -> In x A -> In y X -> In y A -> y = x.
Proof.
  intros X A x y Hm Hx HxA Hy HyA.
  destruct (Nat.eq_dec y x) as [E | Hne]; [exact E | exfalso].
  (* Both [x] and [y] survive the filter. [X] may repeat, so read off a
     two-element prefix rather than counting. *)
  assert (Hin : forall z, In z X -> In z A -> In z (filter (fun w => memb w A) X))
    by (intros z Hz HzA; apply filter_In; split;
        [exact Hz | apply memb_true_iff; exact HzA]).
  pose proof (Hin x Hx HxA) as HxF.
  pose proof (Hin y Hy HyA) as HyF.
  unfold meets in Hm.
  destruct (filter (fun w => memb w A) X) as [|a [|c L']] eqn:HL;
    simpl in Hm; try lia.
  destruct HxF as [E1 | []]; destruct HyF as [E2 | []]; subst; contradiction.
Qed.

Lemma setminus_singleton_nonempty :
  forall b A x, 2 <= b -> length A = b -> NoDup A -> setminus A [x] <> [].
Proof.
  intros b A x Hb Hlen Hnd Hemp.
  pose proof (length_filter_partition (fun z => memb z [x]) A) as Hpart.
  assert (Hz : length (filter (fun z => negb (memb z [x])) A) = 0)
    by (unfold setminus in Hemp; rewrite Hemp; reflexivity).
  assert (Hone : length (filter (fun z => memb z [x]) A) <= 1).
  { assert (Hsub : incl (filter (fun z => memb z [x]) A) [x]).
    { intros z Hz'; apply filter_In in Hz' as [_ Hm].
      apply memb_true_iff in Hm; exact Hm. }
    pose proof (NoDup_incl_length (NoDup_filter _ Hnd) Hsub) as H.
    simpl in H; exact H. }
  lia.
Qed.

Lemma disjoint_nonempty_neq :
  forall P Q : list nat, Disjoint P Q -> P <> [] -> P <> Q.
Proof.
  intros P Q Hd Hne E; subst Q.
  destruct P as [|z P]; [contradiction|].
  apply (Hd z); left; reflexivity.
Qed.

Lemma nodup_three :
  forall P Q R : list nat, P <> Q -> P <> R -> Q <> R -> NoDup [P; Q; R].
Proof.
  intros P Q R H1 H2 H3.
  constructor; [simpl; intros [E | [E | []]]; congruence|].
  constructor; [simpl; intros [E | []]; congruence|].
  constructor; [simpl; tauto | constructor].
Qed.

Lemma pairwise_disjoint_three :
  forall P Q R : list nat,
    Disjoint P Q -> Disjoint P R -> Disjoint Q R ->
    PairwiseDisjoint [P; Q; R].
Proof.
  intros P Q R H1 H2 H3 U V HU HV Hne.
  simpl in HU, HV.
  destruct HU as [<- | [<- | [<- | []]]];
    destruct HV as [<- | [<- | [<- | []]]];
    try (exfalso; apply Hne; reflexivity);
    auto using Disjoint_sym.
Qed.

(** [A0] is the member of the maximal disjoint subfamily through [x]. It
    lies inside [X], and that is exactly what makes the pure members
    through [x] miss it. *)

Theorem pure_link_intersecting :
  forall b (F : Family) (X A0 : list nat) (x : nat),
    2 <= b -> Uniform b F -> ~ ContainsKSunflower 3 F ->
    In A0 F -> In x A0 -> In x X -> Subset A0 X ->
    Intersecting (link [x] (purefam X F)).
Proof.
  intros b F X A0 x Hb HU Hno HA0 HxA0 HxX HA0X.
  intros B1 B2 HB1 HB2 Hdis.
  apply in_link_inv in HB1 as [A [HAp [HxA E1]]].
  apply in_link_inv in HB2 as [B [HBp [HxB E2]]].
  assert (HAF : In A F) by (apply (purefam_incl X F); exact HAp).
  assert (HBF : In B F) by (apply (purefam_incl X F); exact HBp).
  assert (HmA : meets X A = 1) by exact (purefam_meets_one X F A HAp).
  assert (HmB : meets X B = 1) by exact (purefam_meets_one X F B HBp).
  assert (HxA' : In x A) by (apply HxA; left; reflexivity).
  assert (HxB' : In x B) by (apply HxB; left; reflexivity).
  subst B1 B2.
  set (C := setminus A0 [x]).
  assert (HinL : forall D, In D F -> In x D -> In (setminus D [x]) (link [x] F)).
  { intros D HD HxD; unfold link; apply in_map_iff.
    exists D; split; [reflexivity|].
    apply filter_In; split; [exact HD|].
    apply containsb_true_iff; intros z [Hz | []]; subst z; exact HxD. }
  (* Purity: a point of a pure member other than [x] is outside [X],
     hence outside [A0]. *)
  assert (Hcross : forall D, In D F -> meets X D = 1 -> In x D ->
                             Disjoint (setminus D [x]) C).
  { intros D HD HmD HxD z HzD HzC.
    apply in_setminus_iff in HzD as [HzD Hnz].
    unfold C in HzC; apply in_setminus_iff in HzC as [HzA0 _].
    assert (HzX : In z X) by (apply HA0X; exact HzA0).
    pose proof (meets_one_forces X D x z HmD HxX HxD HzX HzD) as Hzx.
    apply Hnz; subst z; left; reflexivity. }
  assert (HdisAC : Disjoint (setminus A [x]) C) by (apply Hcross; assumption).
  assert (HdisBC : Disjoint (setminus B [x]) C) by (apply Hcross; assumption).
  assert (Hnonempty : forall D, In D F -> setminus D [x] <> []).
  { intros D HD; apply (@setminus_singleton_nonempty b D x Hb).
    - exact (@Uniform_length b F D HU HD).
    - pose proof (@Uniform_NoDup b F HU) as HN; rewrite Forall_forall in HN.
      exact (HN D HD). }
  assert (HCne : C <> []) by (unfold C; apply Hnonempty; exact HA0).
  apply Hno.
  apply (@link_sunflower_lift [x] F 3).
  apply (@ContainsKSunflower_of_incl 3
           [setminus A [x]; setminus B [x]; C] (link [x] F) []).
  - intros D HD; simpl in HD.
    destruct HD as [<- | [<- | [<- | []]]].
    + apply HinL; assumption.
    + apply HinL; assumption.
    + unfold C; apply HinL; assumption.
  - reflexivity.
  - apply pairwise_disjoint_sunflower.
    + apply nodup_three.
      * apply (disjoint_nonempty_neq Hdis); apply Hnonempty; exact HAF.
      * apply (disjoint_nonempty_neq HdisAC); apply Hnonempty; exact HAF.
      * apply (disjoint_nonempty_neq HdisBC); apply Hnonempty; exact HBF.
    + apply pairwise_disjoint_three; assumption.
Qed.

(** ** The recursion

    Everything above, put together. [M] is any pairwise-disjoint
    subfamily whose union meets every member; the two hypotheses [Ng] and
    [Ni] bound [g(b-1)] and [iota(b-1)] the way this development always
    carries extremal values, as bounds rather than as functions. *)

Lemma star_length_is_link_length :
  forall x F, length (filter (fun A => memb x A) F) = length (link [x] F).
Proof.
  intros x F; rewrite length_link; unfold deg.
  f_equal; symmetry; apply filter_ext_eq; intros B; apply containsb_singleton.
Qed.

Lemma link_at_point_bounded :
  forall b Ng (F : Family) (x : nat),
    1 <= b -> Uniform b F -> Distinct F -> ~ ContainsKSunflower 3 F ->
    GAtMost (b - 1) Ng ->
    length (filter (fun A => memb x A) F) <= Ng.
Proof.
  intros b Ng F x Hb HU HD Hno Hg.
  rewrite star_length_is_link_length; apply Hg.
  - replace (b - 1) with (b - length [x]) by (simpl; lia).
    apply (@link_uniform b [x] F HU).
    constructor; [intros [] | constructor].
  - exact (@link_distinct [x] F HD).
  - intro Hc; exact (Hno (@link_sunflower_lift [x] F 3 Hc)).
Qed.

Lemma pure_link_at_point_bounded :
  forall b Ni (F : Family) (X A0 : list nat) (x : nat),
    2 <= b -> Uniform b F -> Distinct F -> ~ ContainsKSunflower 3 F ->
    In A0 F -> In x A0 -> In x X -> Subset A0 X ->
    IotaAtMost (b - 1) Ni ->
    length (filter (fun A => memb x A) (purefam X F)) <= Ni.
Proof.
  intros b Ni F X A0 x Hb HU HD Hno HA0 HxA0 HxX HA0X Hi.
  assert (HUp : Uniform b (purefam X F))
    by (apply (@Uniform_sublist b F); [exact HU | apply purefam_incl]).
  assert (HDp : Distinct (purefam X F))
    by (unfold Distinct, purefam; apply SetNoDup_filter; exact HD).
  assert (Hnop : ~ ContainsKSunflower 3 (purefam X F)).
  { intro Hc; apply Hno.
    destruct Hc as [S [Hsub Hks]]; exists S; split; [|exact Hks].
    intros D HD'; destruct (Hsub D HD') as [E [HE Hseq]].
    exists E; split; [apply (purefam_incl X F); exact HE | exact Hseq]. }
  rewrite star_length_is_link_length; apply Hi.
  - replace (b - 1) with (b - length [x]) by (simpl; lia).
    apply (@link_uniform b [x] (purefam X F) HUp).
    constructor; [intros [] | constructor].
  - exact (@link_distinct [x] (purefam X F) HDp).
  - exact (@pure_link_intersecting b F X A0 x Hb HU Hno HA0 HxA0 HxX HA0X).
  - intro Hc; exact (Hnop (@link_sunflower_lift [x] (purefam X F) 3 Hc)).
Qed.

(** The count. *)

Theorem cover_recursion :
  forall b Ng Ni (F : Family) (M : list (list nat)),
    2 <= b -> Uniform b F -> Distinct F -> ~ ContainsKSunflower 3 F ->
    incl M F ->
    (forall A, In A F -> exists B, In B M /\ ~ Disjoint A B) ->
    GAtMost (b - 1) Ng -> IotaAtMost (b - 1) Ni ->
    2 * length F <= length (concat M) * (Ng + Ni).
Proof.
  intros b Ng Ni F M Hb HU HD Hno HMF Hcov Hg Hi.
  set (X := concat M).
  (* Every member meets [X]. *)
  assert (Hmeet : forall A, In A F -> 1 <= meets X A).
  { intros A HA.
    destruct (@cover_provides_element F M A Hcov HA) as [z [HzA HzX]].
    unfold meets.
    assert (Hin : In z (filter (fun w => memb w A) X))
      by (apply filter_In; split; [exact HzX | apply memb_true_iff; exact HzA]).
    destruct (filter (fun w => memb w A) X); [destruct Hin | simpl; lia]. }
  pose proof (sizesum_lower X F Hmeet) as Hlow.
  rewrite <- degsum_eq_sizesum in Hlow.
  (* The two halves of the sum. *)
  assert (Hall : degsum X F <= length X * Ng).
  { apply degsum_le; intros x _.
    exact (@link_at_point_bounded b Ng F x ltac:(lia) HU HD Hno Hg). }
  assert (Hpure : length (purefam X F) <= length X * Ni).
  { rewrite purefam_degsum; apply degsum_le; intros x HxX.
    (* [x] lies in a member of [M], which lies in [F] and inside [X]. *)
    apply in_concat in HxX as [A0 [HA0M HxA0]].
    apply (@pure_link_at_point_bounded b Ni F X A0 x Hb HU HD Hno).
    - apply HMF; exact HA0M.
    - exact HxA0.
    - unfold X; apply in_concat; exists A0; split; assumption.
    - intros z HzA0; unfold X; apply in_concat; exists A0; split; assumption.
    - exact Hi. }
  lia.
Qed.

(** ** The two corollaries

    The intersecting case takes [M] to be a single member — every member
    meets it, so it covers — and the general case takes a maximal
    pairwise-disjoint subfamily, which has at most two members because
    three would be a sunflower with empty core.

    Both are stated against an [N] satisfying an inequality rather than
    against a quotient, so nothing leaves [nat] and the halving is
    exact: [2 * length F <= 2 * N + 1] gives [length F <= N]. *)

Theorem iota_recursion :
  forall b Ng Ni N,
    2 <= b -> GAtMost (b - 1) Ng -> IotaAtMost (b - 1) Ni ->
    b * (Ng + Ni) <= 2 * N + 1 ->
    IotaAtMost b N.
Proof.
  intros b Ng Ni N Hb Hg Hi Harith H HU HD HI Hno.
  destruct H as [|A0 H']; [simpl; lia|].
  set (F := A0 :: H').
  assert (HA0 : In A0 F) by (left; reflexivity).
  assert (Hcov : forall A, In A F -> exists B, In B [A0] /\ ~ Disjoint A B).
  { intros A HA; exists A0; split; [left; reflexivity|].
    exact (HI A A0 HA HA0). }
  assert (Hincl : incl [A0] F)
    by (intros A HA; destruct HA as [E | []]; subst A; exact HA0).
  pose proof (@cover_recursion b Ng Ni F [A0] Hb HU HD Hno Hincl Hcov Hg Hi)
    as Hcount.
  assert (Hlen : length (concat [A0]) = b).
  { simpl; rewrite app_nil_r; exact (@Uniform_length b F A0 HU HA0). }
  rewrite Hlen in Hcount; lia.
Qed.

Theorem g_recursion :
  forall b Ng Ni N,
    2 <= b -> GAtMost (b - 1) Ng -> IotaAtMost (b - 1) Ni ->
    2 * b * (Ng + Ni) <= 2 * N + 1 ->
    GAtMost b N.
Proof.
  intros b Ng Ni N Hb Hg Hi Harith F HU HD Hno.
  assert (HFne : Forall (fun A : list nat => A <> []) F).
  { apply Forall_forall; intros A HA.
    unfold Uniform in HU; rewrite Forall_forall in HU.
    destruct (HU A HA) as [HAlen _].
    destruct A; [simpl in HAlen; lia | discriminate]. }
  destruct (max_disjoint_cover HFne) as [M [Hincl [Hnd [Hpd Hcov]]]].
  (* Three pairwise disjoint members would be a sunflower with empty
     core, so [M] has at most two. *)
  assert (Hcov2 : length M <= 2).
  { destruct (le_lt_dec (length M) 2) as [H2 | H3]; [exact H2 | exfalso].
    apply Hno.
    apply (@ContainsKSunflower_of_incl 3 (firstn 3 M) F []).
    - intros B HB; apply Hincl, (incl_firstn 3 M); exact HB.
    - apply firstn_length_le; lia.
    - apply pairwise_disjoint_sunflower;
        [ apply NoDup_firstn; exact Hnd
        | intros B C HB HC HBC; apply Hpd;
          try (apply (incl_firstn 3 M); assumption); exact HBC ]. }
  assert (HXlen : length (concat M) <= 2 * b).
  { assert (H1 : length (concat M) <= length M * b).
    { apply concat_uniform_length.
      apply Forall_forall; intros B HB; apply Hincl in HB.
      unfold Uniform in HU; rewrite Forall_forall in HU; apply HU; exact HB. }
    nia. }
  pose proof (@cover_recursion b Ng Ni F M Hb HU HD Hno Hincl Hcov Hg Hi) as Hcount.
  nia.
Qed.

(** ** The values, bottom up

    Each rung feeds the next, and the two rungs the development knows
    exactly come out exactly: [iota(2) = 3] and [g(2) = 6] are *reproduced*
    by the recursion, not assumed by it. That is the only check available
    on it, and it is worth the two lines. *)

Corollary iota_two_at_most_three : IotaAtMost 2 3.
Proof.
  apply (@iota_recursion 2 2 1 3);
    [lia | exact g_one_at_most_two | exact iota_one_at_most_one | lia].
Qed.

Corollary g_two_at_most_six : GAtMost 2 6.
Proof.
  apply (@g_recursion 2 2 1 6);
    [lia | exact g_one_at_most_two | exact iota_one_at_most_one | lia].
Qed.

(** [Intersecting.iota_three_at_most_eighteen] is the previous bound; the
    measured value is 10, and `wide::tests::iota_three_is_exactly_ten`
    now decides it. *)

Corollary iota_three_at_most_thirteen : IotaAtMost 3 13.
Proof.
  apply (@iota_recursion 3 6 3 13);
    [lia | exact g_two_at_most_six | exact iota_two_at_most_three | lia].
Qed.

(** The headline. Erdős–Rado's recursion gives [g(3) <= 36] from
    [g(2) = 6], and [f(3,3) <= 49] from its closed form. *)

Corollary g_three_at_most_27 : GAtMost 3 27.
Proof.
  apply (@g_recursion 3 6 3 27);
    [lia | exact g_two_at_most_six | exact iota_two_at_most_three | lia].
Qed.

Corollary f_3_3_at_most_28 : UpperBound 3 3 28.
Proof.
  replace 28 with (S 27) by reflexivity.
  apply (upper_bound_of_sunflower_free_bound 3 27).
  exact g_three_at_most_27.
Qed.

(** Stated against what the development had, so a later session does not
    have to reconstruct which number moved. [Intersecting.lower_bound_3_3_20]
    is [f(3,3) >= 21], and [Sharp.sharp_beats_erdos_rado_at_three] reaches
    28 only from a hypothesis about uniformity 4. *)

Corollary f_3_3_between_21_and_28 :
  UpperBound 3 3 28 /\ ~ UpperBound 3 3 20 /\ 28 < 49.
Proof.
  split; [exact f_3_3_at_most_28 | split; [exact no_upper_bound_3_3_20 | lia]].
Qed.

(** ** The support bound

    [IotaAtMost b N] quantifies over every ground set, so no single search
    decides it. This is what makes one search enough: in an intersecting
    family every member meets a fixed member, so contributes at most
    [b - 1] points beyond it.

    [P] is any set of points covered by the family — the statement is
    about an arbitrary such set rather than about a [support] function, so
    nothing new has to be defined and the bound applies to the ground set
    of any embedding. *)

Lemma concat_length_le :
  forall (n : nat) (S : list (list nat)),
    Forall (fun A => length A <= n) S ->
    length (concat S) <= length S * n.
Proof.
  induction S as [|A S IH]; simpl; intros HF; [lia|].
  inversion HF as [|? ? HA HF']; subst.
  rewrite app_length; specialize (IH HF'); lia.
Qed.

Theorem intersecting_support_bound :
  forall b (H : Family) (P : list nat),
    1 <= b -> Uniform b H -> Intersecting H -> NoDup P ->
    (forall x, In x P -> exists A, In A H /\ In x A) ->
    length P <= b + (b - 1) * (length H - 1).
Proof.
  intros b H P Hb HU HI HP Hcov.
  destruct H as [|A0 H'].
  { destruct P as [|x P]; simpl; [lia|].
    destruct (Hcov x (or_introl eq_refl)) as [A [HA _]]; destruct HA. }
  set (H := A0 :: H').
  assert (HA0 : In A0 H) by (left; reflexivity).
  assert (HA0len : length A0 = b) by exact (@Uniform_length b H A0 HU HA0).
  (* Every point is in [A0], or in some later member minus [A0]. *)
  set (L := A0 ++ concat (map (fun A => setminus A A0) H')).
  assert (Hincl : incl P L).
  { intros x Hx; destruct (Hcov x Hx) as [A [HA HxA]].
    apply in_or_app.
    destruct (in_dec_nat x A0) as [Hin | Hout]; [left; exact Hin|].
    right; apply in_concat.
    destruct HA as [E | HA']; [subst A; contradiction|].
    exists (setminus A A0); split.
    - apply in_map_iff; exists A; split; [reflexivity | exact HA'].
    - apply in_setminus_iff; split; assumption. }
  (* Each later member meets [A0], so loses at least one point to it. *)
  assert (Hlen : length (concat (map (fun A => setminus A A0) H'))
                 <= length H' * (b - 1)).
  { rewrite <- (map_length (fun A => setminus A A0) H').
    apply (@concat_length_le (b - 1)).
    apply Forall_forall; intros S HS.
    apply in_map_iff in HS as [A [E HA']]; subst S.
    assert (HAH : In A H) by (right; exact HA').
    assert (HAlen : length A = b) by exact (@Uniform_length b H A HU HAH).
    assert (Hmeet : exists z, In z A /\ In z A0).
    { destruct (disjointb A A0) eqn:E.
      - exfalso; apply (HI A A0 HAH HA0); apply disjointb_correct; exact E.
      - apply disjointb_false_iff; exact E. }
    destruct Hmeet as [z [HzA HzA0]].
    assert (Hsub : incl (setminus A A0) (rem_elt z A)).
    { intros w Hw; apply in_setminus_iff in Hw as [HwA HwA0].
      apply in_rem_iff; split; [exact HwA|].
      intro E'; subst w; contradiction. }
    pose proof (@Uniform_NoDup b H HU) as HND; rewrite Forall_forall in HND.
    pose proof (HND A HAH) as HAnd.
    pose proof (NoDup_incl_length (@setminus_NoDup A A0 HAnd) Hsub) as Hle.
    rewrite (@length_rem_elt_in z A HAnd HzA) in Hle.
    lia. }
  pose proof (NoDup_incl_length HP Hincl) as Hle.
  unfold L in Hle; rewrite app_length, HA0len in Hle.
  assert (Hlen' : length H = S (length H')) by reflexivity.
  nia.
Qed.

(** At [b = 3]: an eleven-member intersecting 3-uniform family lives on at
    most [3 + 2*10 = 23] points. That is the number
    `wide::support_bound(3, 11)` computes and the ground set
    `iota_three_is_exactly_ten` searches.

    What this does *not* formalise is the relabelling: from "the support
    has at most 23 points" to "the family may be taken to live on
    [{0,...,22}]" is an injection from the support onto an initial
    segment, and [DirectSum.relabel_preserves] wants a globally invertible
    map rather than one invertible on the support. It is the same step the
    Rust search already leans on when it forces the anchor to be
    [{0,...,b-1}], and it is argued there. So [iota(3) = 10] is
    "support bound proved here, relabelling standard, search exhaustive"
    — not a single machine-checked chain. *)

Corollary iota_three_eleven_needs_only_23_points :
  forall (H : Family) (P : list nat),
    Uniform 3 H -> Intersecting H -> NoDup P -> length H = 11 ->
    (forall x, In x P -> exists A, In A H /\ In x A) ->
    length P <= 23.
Proof.
  intros H P HU HI HP Hlen Hcov.
  pose proof (@intersecting_support_bound 3 H P ltac:(lia) HU HI HP Hcov) as Hle.
  rewrite Hlen in Hle; simpl in Hle; lia.
Qed.

(** ** The recursion never loses to Erdős–Rado

    Erdős–Rado's step is [g(b) <= 2b * g(b-1)]. The step here replaces one
    of the two [g(b-1)] factors by [iota(b-1)], and
    [Intersecting.doubling_lower_bound] says [2 * iota(m) <= g(m)] — so the
    substitution is never worse, and is a factor [4/3] better exactly when
    the doubling is tight. Stated as arithmetic on the two bounds, since
    the extremal values are hypotheses here. *)

Theorem recursion_dominates_erdos_rado :
  forall b Ng Ni,
    Ni <= Ng -> b * (Ng + Ni) <= 2 * b * Ng.
Proof. intros; nia. Qed.

Corollary iota_le_g_bound :
  forall b Ng Ni, IotaAtMost b Ni -> GAtMost b Ng ->
    (exists H : Family,
        Uniform b H /\ Distinct H /\ Intersecting H /\
        ~ ContainsKSunflower 3 H /\ length H = Ni) ->
    Ni <= Ng.
Proof.
  intros b Ng Ni _ Hg [H [HU [HD [_ [Hno Hlen]]]]].
  pose proof (Hg H HU HD Hno) as Hle; lia.
Qed.

(** ** One rung further, where the development had a much weaker bound

    [Audit.the_sharp_bound_narrows_iota_four] records [iota(4)] as lying
    in [[27, 192]], the upper end being
    [Intersecting.intersecting_link_bound] fed the Erdős–Rado value for
    [g(3)]. With [g(3) <= 27] and [iota(3) <= 13] the same recursion gives
    80, and [g(4) <= 160] against Erdős–Rado's 8 * 47.

    Neither reaches [Sharp.AHSOptimal]'s [iota(4) <= 31], which is what a
    proof of the sharp conjecture at uniformity 4 would need. *)

Corollary iota_four_at_most_80 : IotaAtMost 4 80.
Proof.
  apply (@iota_recursion 4 27 13 80);
    [lia | exact g_three_at_most_27 | exact iota_three_at_most_thirteen | lia].
Qed.

Corollary g_four_at_most_160 : GAtMost 4 160.
Proof.
  apply (@g_recursion 4 27 13 160);
    [lia | exact g_three_at_most_27 | exact iota_three_at_most_thirteen | lia].
Qed.

(** And with the measured value rather than the proved bound. `rust`'s
    [iota_three_is_exactly_ten] closes [IotaAtMost 3 10] by exhaustive
    search on the ground set [intersecting_support_bound] licenses; the
    hypothesis is stated rather than assumed so the dependence is
    visible. *)

Corollary iota_four_at_most_74_if_iota_three_is_ten :
  IotaAtMost 3 10 -> IotaAtMost 4 74.
Proof.
  intro H10.
  apply (@iota_recursion 4 27 10 74);
    [lia | exact g_three_at_most_27 | exact H10 | lia].
Qed.

Corollary g_four_at_most_148_if_iota_three_is_ten :
  IotaAtMost 3 10 -> GAtMost 4 148.
Proof.
  intro H10.
  apply (@g_recursion 4 27 10 148);
    [lia | exact g_three_at_most_27 | exact H10 | lia].
Qed.
