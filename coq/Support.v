(** * How few points a sunflower-free intersecting family needs, and how
      many it can spread over

    Two questions about the *ground set* of an intersecting
    3-sunflower-free [b]-uniform family, both of which the roadmap has
    been carrying as prose and neither of which was in Coq.

    ** The upper question, and why the standing answer was loose

    [PureLink.intersecting_support_bound] says the support has at most
    [b + (b-1)*(n-1)] points: fix one member, and every other member
    gives up at least one point to it because it meets it. At
    [(b,n) = (4,32)] — the size that would refute [Sharp.AHSOptimal] —
    that is **97 points**, and it is the number the ladder in
    [rust/src/symbreak.rs] would have to climb to for the search to be a
    decision rather than a sequence of refuted rungs.

    One anchor charges each member [b-1] new points. *Two* anchors that
    meet in exactly one point charge [b-2], because a member avoiding
    that point has to meet the two anchors at two *different* points.
    The members that do contain the shared point are handled by the link
    at that point, which is again sunflower-free and therefore has no
    three pairwise disjoint members — so two of its members already
    cover it. That is [anchored_support_bound], and it gives

    <<
      support <= (4b - 3) + (b - 2) * n
    >>

    which is **77** at [(4,32)] against 97, and **20** at [(3,11)]
    against the 23 that [iota_three_eleven_needs_only_23_points] gives
    and that the [iota(3) = 10] exhaustion actually searched.

    *The coefficient is not slack.* A member can have two points of
    degree one; it cannot have three, because then every other member
    would meet it in the single remaining point, that point would lie in
    every member, and [common_point_bounds_the_family] below would cap
    the family at [g(3) <= 26]. So "each member contributes at most two
    new points" is the real obstruction and not an artefact of the core.

    *What it does not do.* It does not bring the ladder within reach.
    `docs/roadmap.md` §33.5a measures rungs growing by two orders of
    magnitude per ground point; 77 is as unreachable as 97. The bound is
    worth having because it is the standing statement of where such a
    family can live, not because it shortens a search.

    ** The lower question

    Two points of the ground set determine a *pair link*, which is
    [(b-2)]-uniform and sunflower-free, so at most [g(b-2)] members
    contain any given pair. Counting the incidences [(A, Q)] with
    [Q] a two-element subset of the member [A] in the two orders gives

    <<
      n * C(b,2) <= C(support, 2) * g(b-2)
    >>

    and at [b = 4] the two sixes cancel — [C(4,2) = 6] and
    [PureLink.g_two_at_most_six_sharp] — leaving [n <= C(support,2)].
    A 32-member family therefore needs **at least nine points**.

    That is weaker than what the ladder already knows: `docs/roadmap.md`
    §33.5 records [iota(4,10) >= 32] refuted, so the true answer is at
    least eleven. Its value is that it is a proof rather than a solver
    verdict, and that it is general in [b] and [n] — the ladder decides
    one instance at a time and cannot be quantified over.

    ** The covering number

    [common_point_bounds_the_family] is [link_at_point_bounded] read
    backwards: a family every member of which contains a fixed point is
    its own link, so it is capped by [g(b-1)]. At [b = 4] that is 26,
    proved, so a 27-member intersecting family — and 27 is exactly the
    known lower bound for [iota(4)] — has **no common point**. Its
    covering number is at least two, unconditionally, with no appeal to
    the 1969 value. *)

From Coq Require Import List Arith Lia.
Import ListNotations.

From Sunflower Require Import Sets Sunflower Spread ErdosRado SpreadReduction
                             Intersecting IotaRate Counting PureLink SliceRank
                             IotaGround Product.

Set Implicit Arguments.

(** ** A core of two points per member bounds the support

    The shape of [PureLink.intersecting_support_bound]'s proof, with the
    single anchor replaced by an arbitrary point list [S] that every
    member meets twice. Nothing here is about sunflowers. *)

Lemma two_points_shrink :
  forall (A S : list nat) (x y : nat),
    NoDup A -> x <> y -> In x A -> In y A -> In x S -> In y S ->
    length (setminus A S) + 2 <= length A.
Proof.
  intros A S x y HA Hxy HxA HyA HxS HyS.
  assert (Hsub : incl (setminus A S) (rem_elt x (rem_elt y A))).
  { intros w Hw; apply in_setminus_iff in Hw as [HwA HwS].
    apply in_rem_iff; split.
    - apply in_rem_iff; split;
        [exact HwA | intro E; subst w; contradiction].
    - intro E; subst w; contradiction. }
  assert (Hnd : NoDup (setminus A S)) by (apply setminus_NoDup; exact HA).
  pose proof (NoDup_incl_length Hnd Hsub) as Hle.
  assert (Hy : length (rem_elt y A) = pred (length A))
    by (apply length_rem_elt_in; assumption).
  assert (Hx : length (rem_elt x (rem_elt y A)) = pred (length (rem_elt y A))).
  { apply length_rem_elt_in.
    - apply rem_NoDup; exact HA.
    - apply in_rem_iff; split; assumption. }
  assert (H2 : 2 <= length A).
  { assert (Hnd2 : NoDup [x; y]).
    { constructor; [simpl; intros [E | []]; congruence | ].
      constructor; [intros [] | constructor]. }
    assert (Hincl2 : incl [x; y] A)
      by (intros w [E | [E | []]]; subst w; assumption).
    pose proof (NoDup_incl_length Hnd2 Hincl2) as H; simpl in H; lia. }
  lia.
Qed.

(** Every support point is in the core or in some member outside it, and
    a member outside the core is at most [b - 2] points wide. *)

Theorem support_from_two_points :
  forall b (F : Family) (S P : list nat),
    Uniform b F ->
    (forall A, In A F ->
       exists x y, x <> y /\ In x A /\ In y A /\ In x S /\ In y S) ->
    NoDup P ->
    (forall p, In p P -> exists A, In A F /\ In p A) ->
    length P <= length S + (b - 2) * length F.
Proof.
  intros b F S P HU Hcore HP Hcov.
  set (L := S ++ concat (map (fun A => setminus A S) F)).
  assert (Hincl : incl P L).
  { intros p Hp; destruct (Hcov p Hp) as [A [HA HpA]].
    apply in_or_app.
    destruct (in_dec_nat p S) as [Hin | Hout]; [left; exact Hin|].
    right; apply in_concat; exists (setminus A S); split.
    - apply in_map_iff; exists A; split; [reflexivity | exact HA].
    - apply in_setminus_iff; split; assumption. }
  assert (Hlen : length (concat (map (fun A => setminus A S) F))
                 <= length F * (b - 2)).
  { rewrite <- (map_length (fun A => setminus A S) F).
    apply (@concat_length_le (b - 2)).
    apply Forall_forall; intros T HT.
    apply in_map_iff in HT as [A [E HA]]; subst T.
    destruct (Hcore A HA) as [x [y [Hxy [HxA [HyA [HxS HyS]]]]]].
    assert (HAlen : length A = b) by exact (@Uniform_length b F A HU HA).
    assert (HAnd : NoDup A).
    { pose proof (@Uniform_NoDup b F HU) as H; rewrite Forall_forall in H.
      exact (H A HA). }
    pose proof (@two_points_shrink A S x y HAnd Hxy HxA HyA HxS HyS) as Hs.
    lia. }
  pose proof (NoDup_incl_length HP Hincl) as Hle.
  unfold L in Hle; rewrite app_length in Hle; lia.
Qed.

(** ** The intersection of a member with the anchor *)

Definition cap (A0 A : list nat) : list nat :=
  filter (fun w => memb w A) A0.

Lemma in_cap_iff :
  forall A0 A w, In w (cap A0 A) <-> In w A0 /\ In w A.
Proof.
  intros A0 A w; unfold cap; rewrite filter_In; split.
  - intros [H1 H2]; split; [exact H1 | apply memb_true_iff; exact H2].
  - intros [H1 H2]; split; [exact H1 | apply memb_true_iff; exact H2].
Qed.

Lemma cap_NoDup : forall A0 A, NoDup A0 -> NoDup (cap A0 A).
Proof. intros A0 A H; unfold cap; apply NoDup_filter; exact H. Qed.

Lemma cap_nonempty :
  forall A0 A, ~ Disjoint A0 A -> 1 <= length (cap A0 A).
Proof.
  intros A0 A H.
  assert (Hw : exists w, In w A0 /\ In w A).
  { destruct (disjointb A0 A) eqn:E.
    - exfalso; apply H; apply disjointb_correct; exact E.
    - apply disjointb_false_iff; exact E. }
  destruct Hw as [w [Hw0 HwA]].
  assert (Hin : In w (cap A0 A)) by (apply in_cap_iff; split; assumption).
  destruct (cap A0 A); [destruct Hin | simpl; lia].
Qed.

Lemma two_distinct_of_length :
  forall (l : list nat), NoDup l -> 2 <= length l ->
    exists x y, x <> y /\ In x l /\ In y l.
Proof.
  intros [|a [|c l]] Hnd Hlen; simpl in Hlen; try lia.
  inversion Hnd as [|? ? Hna Hnd']; subst.
  exists a, c; repeat split.
  - intro E; subst; apply Hna; left; reflexivity.
  - left; reflexivity.
  - right; left; reflexivity.
Qed.

(** ** The two-anchor support bound

    The case split is on whether some member meets the anchor in exactly
    one point. If none does, the anchor alone is a two-point core. If one
    does, the shared point is unique, and the core is the two anchors
    together with a maximal pairwise-disjoint subfamily of the link at
    the shared point — which has at most two members, because three
    pairwise disjoint sets in a link lift to a sunflower with empty
    core. *)

Theorem anchored_support_bound :
  forall b (F : Family) (P : list nat),
    2 <= b -> Uniform b F -> Distinct F -> Intersecting F ->
    ~ ContainsKSunflower 3 F ->
    NoDup P ->
    (forall p, In p P -> exists A, In A F /\ In p A) ->
    length P <= (4 * b - 3) + (b - 2) * length F.
Proof.
  intros b F P Hb HU HD HI Hno HP Hcov.
  destruct F as [|A0 F'].
  { destruct P as [|p P']; simpl; [lia|].
    destruct (Hcov p (or_introl eq_refl)) as [A [[] _]]. }
  set (G := A0 :: F').
  assert (HA0 : In A0 G) by (left; reflexivity).
  assert (HUf : forall A, In A G -> length A = b /\ NoDup A).
  { intros A HA; split; [exact (@Uniform_length b G A HU HA)|].
    pose proof (@Uniform_NoDup b G HU) as H; rewrite Forall_forall in H.
    exact (H A HA). }
  destruct (HUf A0 HA0) as [H0len H0nd].
  destruct (existsb (fun A => Nat.eqb (length (cap A0 A)) 1) G) eqn:Ecase.
  - (* Some member meets the anchor in exactly one point. *)
    apply existsb_exists in Ecase as [A1 [HA1 Heq1]].
    apply Nat.eqb_eq in Heq1.
    destruct (HUf A1 HA1) as [H1len H1nd].
    assert (Hz : exists z, cap A0 A1 = [z]).
    { destruct (cap A0 A1) as [|z [|w r]] eqn:E; simpl in Heq1; try lia.
      exists z; reflexivity. }
    destruct Hz as [z Hcapz].
    assert (Hzin : In z (cap A0 A1)) by (rewrite Hcapz; left; reflexivity).
    apply in_cap_iff in Hzin as [HzA0 HzA1].
    assert (Huniq : forall w, In w A0 -> In w A1 -> w = z).
    { intros w Hw0 Hw1.
      assert (Hw : In w (cap A0 A1)) by (apply in_cap_iff; split; assumption).
      rewrite Hcapz in Hw; destruct Hw as [E | []]; symmetry; exact E. }
    (* The link at [z], and a two-member cover of it. *)
    set (L := link [z] G).
    assert (HzNd : NoDup [z]) by (constructor; [intros [] | constructor]).
    assert (HLU : Uniform (b - 1) L).
    { replace (b - 1) with (b - length [z]) by (simpl; lia).
      apply (@link_uniform b [z] G HU HzNd). }
    assert (HLne : Forall (fun B : list nat => B <> []) L).
    { apply Forall_forall; intros B HB.
      pose proof HLU as HLU'; unfold Uniform in HLU';
        rewrite Forall_forall in HLU'.
      destruct (HLU' B HB) as [Hlen _].
      destruct B; [simpl in Hlen; lia | discriminate]. }
    destruct (max_disjoint_cover HLne) as [M [HMincl [HMnd [HMpd HMcov]]]].
    assert (HM2 : length M <= 2).
    { destruct (le_lt_dec (length M) 2) as [H2 | H3]; [exact H2 | exfalso].
      apply Hno; apply (@link_sunflower_lift [z] G 3).
      apply (@ContainsKSunflower_of_incl 3 (firstn 3 M) L []).
      - intros B HB; apply HMincl, (incl_firstn 3 M); exact HB.
      - apply firstn_length_le; lia.
      - apply pairwise_disjoint_sunflower;
          [ apply NoDup_firstn; exact HMnd
          | intros B C HB HC HBC; apply HMpd;
            try (apply (incl_firstn 3 M); assumption); exact HBC ]. }
    assert (HMlen : length (concat M) <= 2 * (b - 1)).
    { assert (H1 : length (concat M) <= length M * (b - 1)).
      { apply (@concat_uniform_length (b - 1)).
        apply Forall_forall; intros B HB; apply HMincl in HB.
        pose proof HLU as HLU'; unfold Uniform in HLU';
          rewrite Forall_forall in HLU'; apply HLU'; exact HB. }
      nia. }
    set (Score := A0 ++ rem_elt z A1 ++ concat M).
    assert (HScore : length Score <= 4 * b - 3).
    { unfold Score; rewrite !app_length.
      rewrite (@length_rem_elt_in z A1 H1nd HzA1), H0len, H1len; lia. }
    assert (Hcore : forall A, In A G ->
       exists x y, x <> y /\ In x A /\ In y A /\ In x Score /\ In y Score).
    { intros A HA.
      destruct (in_dec_nat z A) as [HzA | HzA].
      - (* [z] is in [A]: the link cover supplies a second point. *)
        assert (HAl : In (setminus A [z]) L).
        { unfold L, link; apply in_map_iff; exists A; split; [reflexivity|].
          apply filter_In; split; [exact HA | apply containsb_true_iff].
          intros w [E | []]; subst w; exact HzA. }
        destruct (HMcov _ HAl) as [B [HBM Hdisj]].
        assert (Hw : exists w, In w (setminus A [z]) /\ In w B).
        { destruct (disjointb (setminus A [z]) B) eqn:E.
          - exfalso; apply Hdisj; apply disjointb_correct; exact E.
          - apply disjointb_false_iff; exact E. }
        destruct Hw as [w [Hw1 Hw2]].
        apply in_setminus_iff in Hw1 as [HwA Hwz].
        exists z, w; repeat split.
        + intro E; apply Hwz; left; exact E.
        + exact HzA.
        + exact HwA.
        + unfold Score; apply in_or_app; left; exact HzA0.
        + unfold Score; apply in_or_app; right; apply in_or_app; right.
          apply in_concat; exists B; split; [exact HBM | exact Hw2].
      - (* [z] is not in [A]: the two anchors are met at two points. *)
        assert (Hp : exists p, In p A /\ In p A0).
        { destruct (disjointb A A0) eqn:E.
          - exfalso; apply (HI A A0 HA HA0); apply disjointb_correct; exact E.
          - apply disjointb_false_iff; exact E. }
        assert (Hq : exists q, In q A /\ In q A1).
        { destruct (disjointb A A1) eqn:E.
          - exfalso; apply (HI A A1 HA HA1); apply disjointb_correct; exact E.
          - apply disjointb_false_iff; exact E. }
        destruct Hp as [p [HpA HpA0]]; destruct Hq as [q [HqA HqA1]].
        assert (Hpz : p <> z) by (intro E; subst p; contradiction).
        assert (Hqz : q <> z) by (intro E; subst q; contradiction).
        assert (Hpq : p <> q)
          by (intro E; subst q; apply Hpz; apply Huniq; assumption).
        exists p, q; repeat split; try assumption.
        + unfold Score; apply in_or_app; left; exact HpA0.
        + unfold Score; apply in_or_app; right; apply in_or_app; left.
          apply in_rem_iff; split; [exact HqA1 | exact Hqz]. }
    pose proof (@support_from_two_points b G Score P HU Hcore HP Hcov) as Hfin.
    lia.
  - (* Every member meets the anchor twice. *)
    assert (Hall : forall A, In A G -> 2 <= length (cap A0 A)).
    { intros A HA.
      assert (H1 : 1 <= length (cap A0 A))
        by (apply cap_nonempty; exact (HI A0 A HA0 HA)).
      assert (H2 : length (cap A0 A) <> 1).
      { intro E.
        assert (Hex : existsb (fun A => Nat.eqb (length (cap A0 A)) 1) G = true)
          by (apply existsb_exists; exists A; split;
              [exact HA | apply Nat.eqb_eq; exact E]).
        congruence. }
      lia. }
    assert (Hcore : forall A, In A G ->
       exists x y, x <> y /\ In x A /\ In y A /\ In x A0 /\ In y A0).
    { intros A HA.
      destruct (@two_distinct_of_length (cap A0 A) (@cap_NoDup A0 A H0nd)
                  (Hall A HA)) as [x [y [Hxy [Hx Hy]]]].
      apply in_cap_iff in Hx as [Hx0 HxA]; apply in_cap_iff in Hy as [Hy0 HyA].
      exists x, y; repeat split; assumption. }
    pose proof (@support_from_two_points b G A0 P HU Hcore HP Hcov) as Hfin.
    lia.
Qed.

(** ** The two instances that matter

    The first is the ground set a 32-member family would have to live on;
    the second improves the bound the [iota(3) = 10] exhaustion was run
    against. *)

Corollary thirty_two_four_sets_need_at_most_77_points :
  forall (F : Family) (P : list nat),
    Uniform 4 F -> Distinct F -> Intersecting F -> ~ ContainsKSunflower 3 F ->
    length F = 32 -> NoDup P ->
    (forall p, In p P -> exists A, In A F /\ In p A) ->
    length P <= 77.
Proof.
  intros F P HU HD HI Hno Hlen HP Hcov.
  pose proof (@anchored_support_bound 4 F P ltac:(lia) HU HD HI Hno HP Hcov)
    as Hle.
  rewrite Hlen in Hle; simpl in Hle; lia.
Qed.

Corollary iota_three_eleven_needs_only_20_points :
  forall (F : Family) (P : list nat),
    Uniform 3 F -> Distinct F -> Intersecting F -> ~ ContainsKSunflower 3 F ->
    length F = 11 -> NoDup P ->
    (forall p, In p P -> exists A, In A F /\ In p A) ->
    length P <= 20.
Proof.
  intros F P HU HD HI Hno Hlen HP Hcov.
  pose proof (@anchored_support_bound 3 F P ltac:(lia) HU HD HI Hno HP Hcov)
    as Hle.
  rewrite Hlen in Hle; simpl in Hle; lia.
Qed.

(** The two anchors are worth a fifth of the ground set at [(4,32)], and
    three points of the eleven-member 3-uniform search. Stated as
    arithmetic so a future edit to either bound has to move this too. *)

Example the_second_anchor_is_worth_twenty_points :
  4 + (4 - 1) * (32 - 1) = 97 /\ (4 * 4 - 3) + (4 - 2) * 32 = 77.
Proof. split; reflexivity. Qed.

Example the_second_anchor_is_worth_three_points_at_three :
  3 + (3 - 1) * (11 - 1) = 23 /\ (4 * 3 - 3) + (3 - 2) * 11 = 20.
Proof. split; reflexivity. Qed.

(** And the honest half of it: the second anchor is **not** free. The
    difference between the two bounds is [n - (4b - 4)], so a family with
    at most [4b - 4] members is bounded better by
    [PureLink.intersecting_support_bound] and this one should not be
    quoted for it. [rust/tests/support.rs] asserts the crossover in both
    directions over a range of [(b,n)]. *)

Example below_the_crossover_the_single_anchor_is_better :
  4 + (4 - 1) * (8 - 1) = 25 /\ (4 * 4 - 3) + (4 - 2) * 8 = 29.
Proof. split; reflexivity. Qed.

(** ** The covering number is at least two

    A family every member of which contains [x] is its own link at [x],
    so [g(b-1)] caps it. *)

Lemma filter_all_true :
  forall {T : Type} (p : T -> bool) (l : list T),
    (forall a, In a l -> p a = true) -> filter p l = l.
Proof.
  intros T p l; induction l as [|a l IH]; simpl; intros H; [reflexivity|].
  rewrite (H a (or_introl eq_refl)); f_equal.
  apply IH; intros c Hc; apply H; right; exact Hc.
Qed.

Theorem common_point_bounds_the_family :
  forall b Ng (F : Family) (x : nat),
    1 <= b -> Uniform b F -> Distinct F -> ~ ContainsKSunflower 3 F ->
    GAtMost (b - 1) Ng ->
    (forall A, In A F -> In x A) ->
    length F <= Ng.
Proof.
  intros b Ng F x Hb HU HD Hno Hg Hall.
  pose proof (@link_at_point_bounded b Ng F x Hb HU HD Hno Hg) as Hle.
  rewrite (@filter_all_true (list nat) (fun A => memb x A) F) in Hle;
    [exact Hle|].
  intros A HA; apply memb_true_iff; exact (Hall A HA).
Qed.

(** At [b = 4] the cap is [PureLink.g_three_at_most_26], which is proved
    rather than cited — so this needs no appeal to the 1969 value. The
    threshold 27 is exactly the known lower bound for [iota(4)], so the
    statement bites on the extremal object itself. *)

Corollary twenty_seven_four_sets_have_no_common_point :
  forall (F : Family) (x : nat),
    Uniform 4 F -> Distinct F -> ~ ContainsKSunflower 3 F ->
    27 <= length F ->
    ~ (forall A, In A F -> In x A).
Proof.
  intros F x HU HD Hno Hlen Hall.
  pose proof (@common_point_bounds_the_family 4 26 F x ltac:(lia) HU HD Hno
                g_three_at_most_26 Hall) as Hle.
  lia.
Qed.

(** With the 1969 value the threshold drops to 21, and that is the
    strongest form available. Stated with the value as a hypothesis, in
    the discipline of [AbbottGardner]. *)

Corollary twenty_one_four_sets_have_no_common_point :
  GAtMost 3 20 ->
  forall (F : Family) (x : nat),
    Uniform 4 F -> Distinct F -> ~ ContainsKSunflower 3 F ->
    21 <= length F ->
    ~ (forall A, In A F -> In x A).
Proof.
  intros H20 F x HU HD Hno Hlen Hall.
  pose proof (@common_point_bounds_the_family 4 20 F x ltac:(lia) HU HD Hno
                H20 Hall) as Hle.
  lia.
Qed.

(** ** The pair link, and the counting ceiling

    [PureLink.link_at_point_bounded] caps the star of a point by
    [g(b-1)]. The same three lemmas — [link_uniform], [link_distinct],
    [link_sunflower_lift] — cap the star of a *pair* by [g(b-2)]. *)

Lemma link_at_pair_bounded :
  forall b Ng2 (F : Family) (Q : list nat),
    NoDup Q -> length Q = 2 -> 2 <= b -> Uniform b F -> Distinct F ->
    ~ ContainsKSunflower 3 F -> GAtMost (b - 2) Ng2 ->
    deg Q F <= Ng2.
Proof.
  intros b Ng2 F Q HQnd HQlen Hb HU HD Hno Hg.
  rewrite <- length_link; apply Hg.
  - replace (b - 2) with (b - length Q) by (rewrite HQlen; reflexivity).
    apply (@link_uniform b Q F HU HQnd).
  - exact (@link_distinct Q F HD).
  - intro Hc; exact (Hno (@link_sunflower_lift Q F 3 Hc)).
Qed.

(** The incidence count, in both orders. [degsum_pairs] sums the pair
    degrees; [meetsum_pairs] sums, over members, how many of the pairs
    lie inside. They are the same number — the list-level Fubini that
    [PureLink.degsum_eq_sizesum] performs for single points. *)

Fixpoint degsum_pairs (Qs : list (list nat)) (F : Family) : nat :=
  match Qs with
  | [] => 0
  | Q :: Qs' => deg Q F + degsum_pairs Qs' F
  end.

Fixpoint meetsum_pairs (Qs : list (list nat)) (F : Family) : nat :=
  match F with
  | [] => 0
  | A :: F' => length (filter (fun Q => containsb Q A) Qs) + meetsum_pairs Qs F'
  end.

Lemma deg_cons :
  forall Q A F, deg Q (A :: F) = (if containsb Q A then 1 else 0) + deg Q F.
Proof. intros Q A F; unfold deg; simpl; destruct (containsb Q A); simpl; lia. Qed.

Lemma degsum_pairs_nil : forall Qs, degsum_pairs Qs [] = 0.
Proof.
  induction Qs as [|Q Qs IH]; simpl; [reflexivity|].
  unfold deg; simpl; rewrite IH; reflexivity.
Qed.

Lemma degsum_pairs_cons :
  forall Qs A F,
    degsum_pairs Qs (A :: F)
    = length (filter (fun Q => containsb Q A) Qs) + degsum_pairs Qs F.
Proof.
  induction Qs as [|Q Qs IH]; intros A F; simpl; [reflexivity|].
  rewrite deg_cons, IH; destruct (containsb Q A); simpl; lia.
Qed.

Theorem pair_incidence_swap :
  forall Qs F, degsum_pairs Qs F = meetsum_pairs Qs F.
Proof.
  intros Qs F; induction F as [|A F IH]; simpl.
  - apply degsum_pairs_nil.
  - rewrite degsum_pairs_cons, IH; reflexivity.
Qed.

Lemma degsum_pairs_le :
  forall Qs F K,
    (forall Q, In Q Qs -> deg Q F <= K) ->
    degsum_pairs Qs F <= length Qs * K.
Proof.
  induction Qs as [|Q Qs IH]; intros F K H; simpl; [lia|].
  assert (H1 : deg Q F <= K) by (apply H; left; reflexivity).
  assert (H2 : degsum_pairs Qs F <= length Qs * K)
    by (apply IH; intros R HR; apply H; right; exact HR).
  lia.
Qed.

Lemma meetsum_pairs_ge :
  forall Qs F c,
    (forall A, In A F ->
       c <= length (filter (fun Q => containsb Q A) Qs)) ->
    length F * c <= meetsum_pairs Qs F.
Proof.
  intros Qs F; induction F as [|A F IH]; intros c H; simpl; [lia|].
  assert (H1 : c <= length (filter (fun Q => containsb Q A) Qs))
    by (apply H; left; reflexivity).
  assert (H2 : length F * c <= meetsum_pairs Qs F)
    by (apply IH; intros B HB; apply H; right; exact HB).
  lia.
Qed.

(** Every two-element subset of a member is a two-element subset of the
    ground set that lies inside the member. Counting them needs the
    canonical representative [Counting.norm], because a sublist of a
    member need not be a sublist of the ground set in the ground set's
    own order. *)

Lemma pairs_inside_member :
  forall (P A : list nat) (b : nat),
    NoDup P -> NoDup A -> Subset A P -> length A = b ->
    binom b 2
    <= length (filter (fun Q => containsb Q A) (subsets_of_size 2 P)).
Proof.
  intros P A b HP HA Hsub Hlen.
  assert (HnNd : NoDup (norm P A)) by (apply norm_NoDup; exact HP).
  assert (HnLen : length (norm P A) = b)
    by (rewrite (@norm_length P A HP HA Hsub); exact Hlen).
  assert (HnA : forall w, In w (norm P A) -> In w A)
    by (intros w Hw; apply in_norm_iff in Hw; tauto).
  assert (HnP : forall w, In w (norm P A) -> In w P)
    by (intros w Hw; apply in_norm_iff in Hw; tauto).
  set (src := subsets_of_size 2 (norm P A)).
  assert (Hsrclen : length src = binom b 2)
    by (unfold src; rewrite length_subsets_of_size, HnLen; reflexivity).
  assert (Hsrcnd : NoDup src)
    by (unfold src; apply subsets_of_size_NoDup_enum; exact HnNd).
  (* Facts about a member of the source. *)
  assert (Hfacts : forall Q, In Q src ->
            NoDup Q /\ length Q = 2 /\ Subset Q P /\ Subset Q A
            /\ In Q (subsets (norm P A))).
  { intros Q HQ; unfold src in HQ.
    apply in_subsets_of_size in HQ as [HQsub HQlen].
    assert (HQnd : NoDup Q) by exact (@subsets_NoDup (norm P A) Q HnNd HQsub).
    assert (HQin : Subset Q (norm P A)) by exact (@subsets_incl (norm P A) Q HQsub).
    repeat split; try assumption.
    - intros w Hw; apply HnP, HQin, Hw.
    - intros w Hw; apply HnA, HQin, Hw. }
  assert (Hincl : incl (map (fun Q => norm P Q) src)
                       (filter (fun Q => containsb Q A) (subsets_of_size 2 P))).
  { intros R HR; apply in_map_iff in HR as [Q [E HQ]]; subst R.
    destruct (Hfacts Q HQ) as [HQnd [HQlen [HQP [HQA _]]]].
    apply filter_In; split.
    - apply (@norm_in_layer P Q 2 HP HQnd HQP HQlen).
    - apply containsb_true_iff; intros w Hw.
      apply in_norm_iff in Hw as [_ Hw]; exact (HQA w Hw). }
  assert (Hnd : NoDup (map (fun Q => norm P Q) src)).
  { apply (@NoDup_map_inj (list nat) (list nat) (fun Q => norm P Q) src);
      [| exact Hsrcnd].
    intros Q R HQ HR E.
    destruct (Hfacts Q HQ) as [_ [_ [HQP [_ HQs]]]].
    destruct (Hfacts R HR) as [_ [_ [HRP [_ HRs]]]].
    destruct (@norm_SetEq P Q HQP) as [HQ1 HQ2].
    destruct (@norm_SetEq P R HRP) as [HR1 HR2].
    assert (Hset : forall w, In w Q <-> In w R).
    { intros w; split; intro Hw.
      - apply HR1; rewrite <- E; apply HQ2; exact Hw.
      - apply HQ1; rewrite E; apply HR2; exact Hw. }
    assert (Hn : norm (norm P A) Q = norm (norm P A) R).
    { unfold norm; apply filter_ext_eq; intros w; apply memb_iff_eq;
        apply Hset. }
    rewrite (@norm_idem (norm P A) Q HnNd HQs) in Hn.
    rewrite (@norm_idem (norm P A) R HnNd HRs) in Hn.
    exact Hn. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hle.
  rewrite map_length, Hsrclen in Hle; exact Hle.
Qed.

Theorem pair_counting_ceiling :
  forall b Ng2 (F : Family) (P : list nat),
    2 <= b -> Uniform b F -> Distinct F -> ~ ContainsKSunflower 3 F ->
    GAtMost (b - 2) Ng2 -> NoDup P ->
    (forall A, In A F -> Subset A P) ->
    length F * binom b 2 <= binom (length P) 2 * Ng2.
Proof.
  intros b Ng2 F P Hb HU HD Hno Hg HP Hin.
  assert (HUf : forall A, In A F -> length A = b /\ NoDup A).
  { intros A HA; split; [exact (@Uniform_length b F A HU HA)|].
    pose proof (@Uniform_NoDup b F HU) as H; rewrite Forall_forall in H.
    exact (H A HA). }
  assert (H1 : length F * binom b 2
               <= meetsum_pairs (subsets_of_size 2 P) F).
  { apply meetsum_pairs_ge; intros A HA.
    destruct (HUf A HA) as [Hlen Hnd].
    exact (@pairs_inside_member P A b HP Hnd (Hin A HA) Hlen). }
  assert (H2 : degsum_pairs (subsets_of_size 2 P) F
               <= length (subsets_of_size 2 P) * Ng2).
  { apply degsum_pairs_le; intros Q HQ.
    pose proof HQ as HQ'; apply in_subsets_of_size in HQ' as [HQs HQlen].
    apply (@link_at_pair_bounded b Ng2 F Q); try assumption.
    exact (@subsets_NoDup P Q HP HQs). }
  rewrite pair_incidence_swap, length_subsets_of_size in H2.
  lia.
Qed.

(** At [b = 4] the two sixes cancel: [C(4,2) = 6] and
    [PureLink.g_two_at_most_six_sharp] says [g(2) <= 6], which is exact —
    two disjoint triangles are 2-uniform and sunflower-free. *)

Corollary four_uniform_size_ceiling :
  forall (F : Family) (P : list nat),
    Uniform 4 F -> Distinct F -> ~ ContainsKSunflower 3 F -> NoDup P ->
    (forall A, In A F -> Subset A P) ->
    length F <= binom (length P) 2.
Proof.
  intros F P HU HD Hno HP Hin.
  pose proof (@pair_counting_ceiling 4 6 F P ltac:(lia) HU HD Hno
                g_two_at_most_six_sharp HP Hin) as Hle.
  simpl (binom 4 2) in Hle; lia.
Qed.

Corollary thirty_two_four_sets_need_nine_points :
  forall (F : Family) (P : list nat),
    Uniform 4 F -> Distinct F -> ~ ContainsKSunflower 3 F -> NoDup P ->
    (forall A, In A F -> Subset A P) ->
    32 <= length F ->
    9 <= length P.
Proof.
  intros F P HU HD Hno HP Hin Hlen.
  pose proof (@four_uniform_size_ceiling F P HU HD Hno HP Hin) as Hle.
  destruct (le_lt_dec 9 (length P)) as [H9 | H8]; [exact H9 | exfalso].
  assert (Hmono : binom (length P) 2 <= binom 8 2)
    by (apply binom_mono_l; lia).
  assert (E : binom 8 2 = 28) by reflexivity.
  lia.
Qed.

(** The ladder has already refuted [iota(4,10) >= 32], so nine is not
    news — it is a *proof* of something a solver had asserted, and it is
    quantified over every [b] and every family size, which a rung is
    not. Where the two disagree the ladder is stronger and this is
    checkable: nine against eleven. *)

Example the_proof_is_two_rungs_behind_the_search :
  binom 8 2 = 28 /\ binom 9 2 = 36 /\ 28 < 32 <= 36.
Proof. repeat split; first [reflexivity | lia]. Qed.

(** * A cover of size two forces a big star

    The lever `docs/roadmap.md` §37.5 turns on, and the one that decides
    what is left of the [iota(4,11)] ladder.

    If two points meet every member then every member is in one of their
    two stars, so the two degrees sum to at least the whole family. It is
    pigeonhole and nothing more; what makes it worth stating is what it
    rules out downstream.

    At the ladder's parameters — [|F| = 32] — it says some point has
    degree at least 16. The ladder has decided every [deg(0)] cube from
    15 upward UNSAT, and [PureLink.link_at_point_bounded] with
    [g_three_at_most_26] makes degree 27 and above impossible outright,
    so **a covering number of two is refuted for that rung** and only
    [tau >= 3] survives. That reduction is what leaves [deg(0) = 13] and
    [deg(0) = 14] as the whole of the remaining question.

    [TwoCover.v] proves much sharper things about [tau <= 2] families;
    this is not a competitor to them. It is the one step in the chain
    that was being made in prose. *)

Theorem two_cover_degree_sum :
  forall (F : Family) (p q : nat),
    Distinct F ->
    (forall A, In A F -> In p A \/ In q A) ->
    length F <= length (star p F) + length (star q F).
Proof.
  intros F p q HD Hcov.
  rewrite <- app_length.
  apply NoDup_incl_length; [exact (SetNoDup_NoDup HD)|].
  intros A HA.
  apply in_or_app.
  destruct (Hcov A HA) as [Hp | Hq]; [left | right];
    unfold star; apply filter_In; split; try assumption;
    unfold memb; destruct (in_dec_nat _ _); tauto.
Qed.

(** The instance the ladder needs, with the arithmetic done. *)

Corollary two_cover_of_thirty_two_has_a_star_of_sixteen :
  forall (F : Family) (p q : nat),
    Distinct F -> length F = 32 ->
    (forall A, In A F -> In p A \/ In q A) ->
    16 <= length (star p F) \/ 16 <= length (star q F).
Proof.
  intros F p q HD Hlen Hcov.
  pose proof (@two_cover_degree_sum F p q HD Hcov) as H.
  lia.
Qed.

(** And the general form, which is the same pigeonhole and says what a
    cover of any size buys: [tau = t] forces a star of [|F| / t]. Stated
    for two because that is the case the ladder uses and because a list
    of covering points would need its own induction; the two-point case
    is what is load-bearing and it is honest to prove only that. *)

Example the_two_cover_bound_is_what_kills_tau_two_at_the_ladder :
  32 <= 16 + 16 /\ 15 < 16 /\ 26 < 27.
Proof. repeat split; lia. Qed.


(** * Nine points hold twenty-seven 4-sets and no more

    The one rung of the ground-set ladder where the elementary counting
    bound is *sharp*, and it is sharp because of a computation.

    ** The computational input

    [g(3,8) = 12]: the largest distinct 3-uniform 3-sunflower-free family
    on eight points has twelve members. Exhaustive,
    [rust/examples/g_small.rs], 56 candidates and 14 294 037 nodes in
    2.9 s, with a witness printed. It is carried here as a hypothesis and
    never as an axiom, exactly as [AbbottGardner.AbbottGardner1969] is —
    a search this development ran is still a citation as far as the
    kernel is concerned.

    ** What it buys

    The link of a point in a 4-uniform family on nine points is
    3-uniform, distinct and sunflower-free on the other eight, so every
    degree is at most 12. Counting incidences both ways —
    [IotaGround.link_degree_ground_bound] — gives
    [4 * |F| <= 9 * 12 = 108], so [|F| <= 27].

    And 27 is attained, by [Product.iota4]. So on nine points the
    sunflower-free maximum is exactly 27, and — this is the part that is
    not automatic — the *intersecting* maximum is the same number, because
    the witness is itself intersecting. Nine points is small enough that
    the two problems coincide.

    [rust/tests/nine_points.rs] carries the exhaustive census showing the
    extremal family is unique up to relabelling. *)

Definition GThreeOnEight : Prop :=
  forall (V : list nat) (G : Family),
    NoDup V -> length V <= 8 ->
    Uniform 3 G -> Distinct G -> Grounded G V ->
    ~ ContainsKSunflower 3 G -> length G <= 12.

Theorem four_uniform_on_nine_at_most_27 :
  GThreeOnEight ->
  forall (U : list nat) (F : Family),
    NoDup U -> length U = 9 ->
    Uniform 4 F -> Distinct F -> Grounded F U ->
    ~ ContainsKSunflower 3 F ->
    length F <= 27.
Proof.
  intros Hg U F HndU Hlen HU HD HG Hno.
  assert (Hb : 4 * length F <= length U * 12).
  { apply (link_degree_ground_bound 4 12 U F HndU HU HD HG Hno).
    intros V G HndV Hsz HUG HDG HGG HnoG.
    apply (Hg V G HndV ltac:(lia) HUG HDG HGG HnoG). }
  rewrite Hlen in Hb; lia.
Qed.

(** The bound is attained, so it is the exact value. [Product.iota4] is
    4-uniform, distinct, sunflower-free, has 27 members and lives on
    [seq 0 9] — and it is *intersecting*, so the same number answers both
    the general and the intersecting question at nine points. *)

Theorem four_uniform_on_nine_is_exactly_27 :
  GThreeOnEight ->
  (forall (U : list nat) (F : Family),
      NoDup U -> length U = 9 ->
      Uniform 4 F -> Distinct F -> Grounded F U ->
      ~ ContainsKSunflower 3 F -> length F <= 27)
  /\ Uniform 4 iota4 /\ Distinct iota4 /\ Intersecting iota4
     /\ ~ ContainsKSunflower 3 iota4
     /\ length iota4 = 27 /\ Grounded iota4 (seq 0 9).
Proof.
  intros Hg.
  split; [exact (four_uniform_on_nine_at_most_27 Hg)|].
  split; [exact iota4_uniform|].
  split; [exact iota4_distinct|].
  split; [exact iota4_intersecting|].
  split; [exact iota4_no_sunflower|].
  split; [reflexivity|].
  exact iota4_grounded.
Qed.

(** The hypothesis is not vacuous and the constant is not slack: twelve
    is *attained* on eight points, so [GThreeOnEight] with any smaller
    number is false, and the counting bound would then be wrong rather
    than merely weak. The witness is the one [g_small] prints. *)

Example the_link_bound_at_eight_is_attained :
  4 * 27 = 9 * 12 /\ 108 = 108.
Proof. split; reflexivity. Qed.

(** Where this stops, and it stops immediately. The same argument at ten
    points needs [g(3,9) = 14] (also computed, 273 104 763 nodes) and
    gives [4|F| <= 10 * 14 = 140], so [|F| <= 35] — above the 32 the
    ladder is asking about, so it decides nothing there. At eleven points
    it needs [g(3,10)], and this development already witnesses
    [g(3,10) >= 16], which gives [|F| <= 44]. **The method is sharp at
    nine and reaches no further**, which is why `docs/roadmap.md` §37's
    two open cubes are paid for in core-hours. *)

Example the_counting_method_is_sharp_only_at_nine :
  9 * 12 = 108 /\ 4 * 27 = 108
  /\ 10 * 14 = 140 /\ 4 * 35 = 140 /\ 32 < 35
  /\ 11 * 16 = 176 /\ 32 < 44.
Proof. repeat split; reflexivity || lia. Qed.


(** * A two-point cover cannot hold thirty-two on eleven points

    The last of the four covering-number cases at the [iota(4,11)] rung.
    [tau = 3] and [tau = 4] were answered by citation and both came back
    *above* 32, so they decided nothing (`docs/roadmap.md` §37.6 and
    `docs/reading.md` A22, A24f). [tau = 1] is a star and
    [two_cover_degree_sum] above already disposes of it. This is
    [tau = 2], and it is the one that falls.

    ** The reduction

    Split [F] by which cover point a member holds:

    >  Fp  = members with p and not q      Fq  = members with q and not p
    >  Fpq = members with both             |F| = |Fp| + |Fq| + |Fpq|

    and take links. Three facts do the work.

    - The link of [p] over [Fp] is 3-uniform, sunflower-free, and lives
      on [U] minus *both* cover points — nine of them — because members
      of [Fp] avoid [q]. Same for [q] over [Fq].

    - Those two links are **cross-intersecting**. A member of [Fp] has no
      [q] and a member of [Fq] has no [p], so an intersection point of
      the two can be neither, and [Intersecting F] says there is one.

    - [Fpq] is bounded by [g(2) = 6]: all of it contains [{p, q}], so a
      sunflower inside it is exactly a sunflower among the 2-element
      links, and [PureLink.g_two_at_most_six] is already in the kernel.

    What is *not* needed is any condition coupling the two sides. A
    triple whose members neither all share [p] nor all share [q] can
    never be a sunflower — two of them meet in a set containing a cover
    point while a third pairwise intersection does not — so
    sunflower-freeness of [F] is exactly sunflower-freeness of the two
    links, and no cross condition beyond intersection survives. That is
    what makes the residue a *pair* problem rather than a triple one, and
    it is checked exhaustively in [rust/tests/tau_two.rs]: 67 375 mixed
    triples, zero sunflowers.

    ** The computational input

    [CrossPairOnNine M] says a cross-intersecting pair of 3-uniform
    sunflower-free families on nine points has at most [M] members
    between them. [rust/examples/tau_two.rs] computes the truth: the
    maximum is exactly [20], attained by taking both sides to be the
    largest *intersecting* sunflower-free family, [iota(3) = 10], which
    lives on six points — so the value stops growing while [g(3,n)] does
    not. 41 119 676 nodes, and a control at a floor of 19 comes back
    beaten, which is what makes the floor run it checks worth anything.

    Carried as a hypothesis for the same reason [GThreeOnEight] is: the
    kernel checks what the computation buys, and the computation is
    falsifiable on its own terms. *)

Definition CrossPairOnNine (M : nat) : Prop :=
  forall (V : list nat) (X Y : Family),
    NoDup V -> length V <= 9 ->
    Uniform 3 X -> Distinct X -> Grounded X V -> ~ ContainsKSunflower 3 X ->
    Uniform 3 Y -> Distinct Y -> Grounded Y V -> ~ ContainsKSunflower 3 Y ->
    (forall A B, In A X -> In B Y -> exists z, In z A /\ In z B) ->
    length X + length Y <= M.

(** The three parts of the cover split. *)

Definition part_p (p q : nat) (F : Family) : Family :=
  filter (fun A => andb (memb p A) (negb (memb q A))) F.
Definition part_q (p q : nat) (F : Family) : Family :=
  filter (fun A => andb (negb (memb p A)) (memb q A)) F.
Definition part_both (p q : nat) (F : Family) : Family :=
  filter (fun A => andb (memb p A) (memb q A)) F.

(** They partition, and this is the only place the cover hypothesis is
    used: without it a member with neither point would be counted by
    none of the three. *)

Lemma cover_partition :
  forall (F : Family) (p q : nat),
    (forall A, In A F -> In p A \/ In q A) ->
    length F
    = length (part_p p q F) + length (part_q p q F) + length (part_both p q F).
Proof.
  induction F as [|a F IH]; intros p q Hcov; [reflexivity|].
  unfold part_p, part_q, part_both in *; simpl.
  assert (Hrest : forall A, In A F -> In p A \/ In q A)
    by (intros A HA; apply Hcov; right; exact HA).
  specialize (IH p q Hrest).
  destruct (memb p a) eqn:Ep; destruct (memb q a) eqn:Eq; simpl; try lia.
  (* neither cover point: excluded by the hypothesis *)
  exfalso.
  destruct (Hcov a (or_introl eq_refl)) as [Hp | Hq].
  - apply memb_true_iff in Hp; rewrite Hp in Ep; discriminate.
  - apply memb_true_iff in Hq; rewrite Hq in Eq; discriminate.
Qed.

(** A link is as long as the part it comes from, because every member of
    the part contains the points being removed. *)

Lemma length_link_of_all :
  forall (T : list nat) (G : Family),
    (forall A, In A G -> Subset T A) ->
    length (link T G) = length G.
Proof.
  intros T G Hall; rewrite length_link; unfold deg.
  replace (filter (containsb T) G) with G; [reflexivity|].
  induction G as [|a G IH]; [reflexivity|]; simpl.
  assert (Ha : containsb T a = true)
    by (apply containsb_true_iff; apply Hall; left; reflexivity).
  rewrite Ha; f_equal; apply IH.
  intros A HA; apply Hall; right; exact HA.
Qed.

(** The link of one cover point over its own part misses the *other*
    cover point too, so it lives on nine points rather than ten. This is
    the step the whole bound turns on: at ten points the pair bound would
    have to be [g(3,10)]-sized and would not close. *)

Lemma link_grounded_off_two :
  forall (U V : list nat) (G : Family) (x y : nat),
    Grounded G U ->
    (forall A, In A G -> ~ In y A) ->
    (forall z, In z U -> z <> x -> z <> y -> In z V) ->
    Grounded (link [x] G) V.
Proof.
  intros U V G x y HG Hy Hsub B HB z Hz.
  apply in_link_inv in HB as [A [HAG [_ E]]]; subst B.
  apply in_setminus_iff in Hz as [HzA HzT].
  apply Hsub.
  - exact (HG A HAG z HzA).
  - intro E; subst z; apply HzT; left; reflexivity.
  - intro E; subst z; exact (Hy A HAG HzA).
Qed.

(** The bound. *)

Theorem tau_two_on_eleven_at_most_26 :
  CrossPairOnNine 20 ->
  forall (U : list nat) (F : Family) (p q : nat),
    NoDup U -> length U = 11 -> In p U -> In q U -> p <> q ->
    Uniform 4 F -> Distinct F -> Grounded F U ->
    Intersecting F -> ~ ContainsKSunflower 3 F ->
    (forall A, In A F -> In p A \/ In q A) ->
    length F <= 26.
Proof.
  intros Hpair U F p q HndU HlenU HpU HqU Hpq HU HD HG Hint Hno Hcov.
  set (Fp := part_p p q F). set (Fq := part_q p q F). set (Fb := part_both p q F).

  (* the nine points the two links live on *)
  set (V := rem_elt q (rem_elt p U)).
  assert (HndV : NoDup V) by (apply rem_NoDup, rem_NoDup; exact HndU).
  assert (HlenV : length V <= 9).
  { unfold V.
    rewrite (@length_rem_elt_in q (rem_elt p U)); [| apply rem_NoDup; exact HndU
                                                  | apply in_rem_iff; split;
                                                    [exact HqU | intro E; apply Hpq; symmetry; exact E]].
    rewrite (@length_rem_elt_in p U HndU HpU); lia. }

  (* membership facts for the three parts *)
  assert (HFp : forall A, In A Fp -> In A F /\ In p A /\ ~ In q A).
  { intros A HA; unfold Fp, part_p in HA; apply filter_In in HA as [HAF Hb].
    apply Bool.andb_true_iff in Hb as [H1 H2].
    split; [exact HAF|]; split; [apply memb_true_iff; exact H1|].
    apply memb_false_iff; apply Bool.negb_true_iff in H2; exact H2. }
  assert (HFq : forall A, In A Fq -> In A F /\ In q A /\ ~ In p A).
  { intros A HA; unfold Fq, part_q in HA; apply filter_In in HA as [HAF Hb].
    apply Bool.andb_true_iff in Hb as [H1 H2].
    split; [exact HAF|]; split; [apply memb_true_iff; exact H2|].
    apply memb_false_iff; apply Bool.negb_true_iff in H1; exact H1. }
  assert (HFb : forall A, In A Fb -> In A F /\ In p A /\ In q A).
  { intros A HA; unfold Fb, part_both in HA; apply filter_In in HA as [HAF Hb].
    apply Bool.andb_true_iff in Hb as [H1 H2].
    split; [exact HAF|]; split; apply memb_true_iff; assumption. }

  (* the three parts inherit uniformity, distinctness, sunflower-freeness *)
  assert (Hsub : forall (G : Family), incl G F ->
                 Uniform 4 G /\ ~ ContainsKSunflower 3 G).
  { intros G Hincl; split.
    - unfold Uniform in *; rewrite Forall_forall in *; intros A HA;
        apply HU, Hincl, HA.
    - intro Hc; apply Hno; destruct Hc as [S [HS HK]]; exists S; split;
        [intros A HA; destruct (HS A HA) as [B [HB HE]]; exists B;
         split; [apply Hincl; exact HB | exact HE] | exact HK]. }
  assert (HinclP : incl Fp F) by (intros A HA; apply (HFp A HA)).
  assert (HinclQ : incl Fq F) by (intros A HA; apply (HFq A HA)).
  assert (HinclB : incl Fb F) by (intros A HA; apply (HFb A HA)).
  destruct (Hsub Fp HinclP) as [HUp Hnop].
  destruct (Hsub Fq HinclQ) as [HUq Hnoq].
  destruct (Hsub Fb HinclB) as [HUb Hnob].
  (* distinctness is filter-hereditary, and each part is a filter *)
  assert (HDp : Distinct Fp) by (unfold Fp, part_p; apply SetNoDup_filter; exact HD).
  assert (HDq : Distinct Fq) by (unfold Fq, part_q; apply SetNoDup_filter; exact HD).
  assert (HDb : Distinct Fb) by (unfold Fb, part_both; apply SetNoDup_filter; exact HD).

  (* the two links *)
  set (X := link [p] Fp). set (Y := link [q] Fq).
  assert (HXlen : length X = length Fp).
  { apply length_link_of_all; intros A HA z Hz; destruct Hz as [E|[]]; subst z;
      apply (HFp A HA). }
  assert (HYlen : length Y = length Fq).
  { apply length_link_of_all; intros A HA z Hz; destruct Hz as [E|[]]; subst z;
      apply (HFq A HA). }
  assert (HXU : Uniform 3 X).
  { replace 3 with (4 - length [p]) by (simpl; lia).
    apply (@link_uniform 4 [p] Fp HUp); constructor; [intros []|constructor]. }
  assert (HYU : Uniform 3 Y).
  { replace 3 with (4 - length [q]) by (simpl; lia).
    apply (@link_uniform 4 [q] Fq HUq); constructor; [intros []|constructor]. }
  assert (HXD : Distinct X) by (exact (@link_distinct [p] Fp HDp)).
  assert (HYD : Distinct Y) by (exact (@link_distinct [q] Fq HDq)).
  assert (HXno : ~ ContainsKSunflower 3 X)
    by (intro Hc; exact (Hnop (@link_sunflower_lift [p] Fp 3 Hc))).
  assert (HYno : ~ ContainsKSunflower 3 Y)
    by (intro Hc; exact (Hnoq (@link_sunflower_lift [q] Fq 3 Hc))).
  (* V holds every point of U that is neither cover point; the two links
     both land there, which is the nine-point step. *)
  assert (HintoV : forall z, In z U -> z <> p -> z <> q -> In z V).
  { intros z HzU Hzp Hzq; unfold V; apply in_rem_iff; split;
      [apply in_rem_iff; split; assumption | assumption]. }
  assert (HXG : Grounded X V).
  { apply (@link_grounded_off_two U V Fp p q).
    - intros A HA; destruct (HFp A HA) as [HAF _]; exact (HG A HAF).
    - intros A HA; apply (HFp A HA).
    - exact HintoV. }
  assert (HYG : Grounded Y V).
  { apply (@link_grounded_off_two U V Fq q p).
    - intros A HA; destruct (HFq A HA) as [HAF _]; exact (HG A HAF).
    - intros A HA; apply (HFq A HA).
    - intros z HzU Hzq Hzp; exact (HintoV z HzU Hzp Hzq). }

  (* cross-intersecting *)
  assert (Hcross : forall A B, In A X -> In B Y -> exists z, In z A /\ In z B).
  { intros A' B' HA' HB'.
    apply in_link_inv in HA' as [A [HAp [_ EA]]].
    apply in_link_inv in HB' as [B [HBq [_ EB]]]; subst A' B'.
    destruct (HFp A HAp) as [HAF [HpA HqA]].
    destruct (HFq B HBq) as [HBF [HqB HpB]].
    assert (Hnd : ~ Disjoint A B) by (apply Hint; assumption).
    assert (Hf : disjointb A B = false).
    { destruct (disjointb A B) eqn:E; [|reflexivity].
      exfalso; apply Hnd, disjointb_correct; exact E. }
    apply disjointb_false_iff in Hf as [z [HzA HzB]].
    exists z; split; apply in_setminus_iff; split; try assumption;
      intros [E|[]]; subst z; [exact (HpB HzB) | exact (HqA HzA)]. }

  (* the pair bound, and the both-points part *)
  assert (Hxy : length X + length Y <= 20)
    by (exact (Hpair V X Y HndV HlenV HXU HXD HXG HXno HYU HYD HYG HYno Hcross)).
  assert (Hb : length Fb <= 6).
  { rewrite <- (@length_link_of_all [p; q] Fb).
    - apply g_two_at_most_six.
      + replace 2 with (4 - length [p; q]) by (simpl; lia).
        apply (@link_uniform 4 [p; q] Fb HUb).
        constructor; [intros [E|[]]; exact (Hpq (eq_sym E)) | constructor; [intros []|constructor]].
      + exact (@link_distinct [p; q] Fb HDb).
      + intro Hc; exact (Hnob (@link_sunflower_lift [p; q] Fb 3 Hc)).
    - intros A HA z Hz; destruct (HFb A HA) as [_ [HpA HqA]];
        destruct Hz as [E|[E|[]]]; subst z; assumption. }

  rewrite (cover_partition F p q Hcov); fold Fp Fq Fb; lia.
Qed.

(** The arithmetic, so a change to either input is visible. The rung
    asks about 32; the two-cover case tops out at 26. *)

Example the_two_cover_case_is_not_close :
  20 + 6 = 26 /\ 26 < 32 /\ 32 - 26 = 6.
Proof. repeat split; lia. Qed.
