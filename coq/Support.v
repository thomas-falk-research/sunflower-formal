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
                             Intersecting IotaRate Counting PureLink.

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
