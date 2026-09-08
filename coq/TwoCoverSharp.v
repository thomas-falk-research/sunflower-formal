(** * TwoCoverSharp.v -- the two-point cover case of the intersecting
      piece, exactly: [tau(G) = 2  =>  |G| <= 3r + 1] for [r >= 3]

    [TwoCover.two_cover_bound] proves [|G| <= max(4r, 3r + 4)] for a
    3-uniform intersecting family [G] satisfying Rao's condition at [r]
    and covered by two points, neither of which covers alone.  At
    [r = 3] that is 13; the truth, measured by exhaustive search on
    every ground set up to eleven points, is 10.  This file closes the
    gap for every [r >= 3]:

<<
      tau(G) = 2   =>   |G| <= 3r + 1,
>>

    and [3r + 1] is attained -- see [hm_family] below -- so this is the
    exact value of the two-point-cover row of the extremal problem
    [I(m,r)] of docs/roadmap.md §24.13 at [m = 3].

    ** The argument

    Write [Pa] for the members through [a] but not [b], for [{a,b} =
    {p,q}] in either order, and [Ppq] for those through both, which the
    pair degree caps at [r].  Everything else is the sum
    [|Pp| + |Pq| <= 2r + 1], proved by cases on whether a piece has a
    *common point*: a point other than its anchor lying in every one
    of its members.

    - **[Pp] has a common point [u].**  Then [Pp] is capped by the pair
      [{p,u}] at [r].  If every member of [Pq] holds [u] too, [Pq] is
      capped by [{q,u}] and the sum is [2r].  Otherwise some [D in Pq]
      misses [u]; every member of [Pp] holds [{p,u}] and meets [D], so
      [Pp] is pinned to two triples, [|Pp| <= 2], and then a member of
      [Pq] either holds [u] or holds both third points of [Pp] -- one
      pair and one triple, [|Pq| <= r + 1].  The finer count is exactly
      what [max(4r, 3r+4)] lacked.

    - **Neither piece has a common point.**  Each piece is pinned to
      four triples by the other ([TwoCover.no_common_point_bound]'s
      device), so both are at most 4 -- and they cannot both be 4.  If
      [|Pp| >= 4] then two of its members have disjoint tails
      [{x1,x2}], [{y1,y2}], because a family of pairwise-meeting tails
      with no common point has at most three members (the triangle).
      Every member of [Pq] then holds one [x_i] and one [y_j]; if all
      four such triples occur, every member of [Pp] must meet all four,
      which forces its tail to be [{x1,x2}] or [{y1,y2}], so
      [|Pp| <= 2].  Hence [|Pp| + |Pq| <= 7 <= 2r + 1] once [r >= 3].

    No graph theory is used: each step names finitely many pairs or
    triples that every member of a piece must contain and counts them
    under Rao's caps, which is the discipline of [TwoCover.v] and
    [TauThree.v]. *)

From Coq Require Import List Arith Lia Bool.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower Pigeonhole Spread SpreadReduction
     DirectSum SpreadThreshold TwoCover Reflect.
Import ListNotations.

Set Implicit Arguments.

(** ** Counting members against a list of covering sets, with the
    degrees summed rather than capped uniformly *)

Fixpoint degsum (Ts : list (list nat)) (F : Family) : nat :=
  match Ts with
  | [] => 0
  | T :: Ts' => deg T F + degsum Ts' F
  end.

Lemma degsum_filter_le :
  forall Ts (f : list nat -> bool) (F : Family),
    degsum Ts (filter f F) <= degsum Ts F.
Proof.
  induction Ts as [|T Ts IH]; intros f F; simpl; [lia|].
  pose proof (deg_filter_le T f F); pose proof (IH f F); lia.
Qed.

Lemma cover_degsum :
  forall (Ts : list (list nat)) (F : Family),
    (forall A, In A F -> exists T, In T Ts /\ Subset T A) ->
    length F <= degsum Ts F.
Proof.
  induction Ts as [|T Ts IH]; intros F Hcov.
  - destruct F as [|A F']; simpl; [lia|].
    destruct (Hcov A (or_introl eq_refl)) as [T [HT _]]; destruct HT.
  - simpl.
    assert (Hlen : length F
                   = deg T F + length (filter (fun A => negb (containsb T A)) F)).
    { unfold deg; apply length_filter_partition. }
    assert (HG : length (filter (fun A => negb (containsb T A)) F)
                 <= degsum Ts (filter (fun A => negb (containsb T A)) F)).
    { apply IH; intros A HA.
      apply filter_In in HA as [HAF Hnot].
      destruct (Hcov A HAF) as [T' [HT' Hsub]].
      destruct HT' as [<- | HT'].
      - exfalso; apply Bool.negb_true_iff in Hnot.
        assert (containsb T A = true) by (apply containsb_true_iff; exact Hsub).
        congruence.
      - exists T'; split; assumption. }
    pose proof (degsum_filter_le Ts (fun A => negb (containsb T A)) F).
    lia.
Qed.

(** ** Small list facts *)

Lemma NoDup3 : forall x y z : nat, x <> y -> x <> z -> y <> z -> NoDup [x; y; z].
Proof.
  intros x y z Hxy Hxz Hyz.
  constructor; [intros [<-|[<-|[]]]; congruence|].
  constructor; [intros [<-|[]]; congruence|].
  constructor; [intros []|constructor].
Qed.

Lemma NoDup2 : forall x y : nat, x <> y -> NoDup [x; y].
Proof.
  intros x y Hxy.
  constructor; [intros [<-|[]]; congruence|].
  constructor; [intros []|constructor].
Qed.

(** A 3-set containing three distinct named points is exactly them. *)

Lemma three_of_three :
  forall (C : list nat) x y z,
    length C = 3 -> NoDup C -> x <> y -> x <> z -> y <> z ->
    In x C -> In y C -> In z C ->
    forall t, In t C -> t = x \/ t = y \/ t = z.
Proof.
  intros C x y z Hlen Hnd Hxy Hxz Hyz Hx Hy Hz t Ht.
  assert (Hincl : incl [x; y; z] C) by (intros w [<-|[<-|[<-|[]]]]; assumption).
  assert (Hback : incl C [x; y; z]).
  { apply (@NoDup_length_incl nat [x; y; z] C); [apply NoDup3; assumption | simpl; lia | exact Hincl]. }
  destruct (Hback t Ht) as [<-|[<-|[<-|[]]]]; tauto.
Qed.

(** Four distinct points do not fit in a 3-set. *)

Lemma four_in_three :
  forall (C : list nat) w x y z,
    length C = 3 -> NoDup C ->
    w <> x -> w <> y -> w <> z -> x <> y -> x <> z -> y <> z ->
    In w C -> In x C -> In y C -> In z C -> False.
Proof.
  intros C w x y z Hlen Hnd Hwx Hwy Hwz Hxy Hxz Hyz Hw Hx Hy Hz.
  assert (Hnd4 : NoDup [w; x; y; z]).
  { constructor; [intros [<-|[<-|[<-|[]]]]; congruence|]. apply NoDup3; assumption. }
  assert (Hincl : incl [w; x; y; z] C) by (intros t [<-|[<-|[<-|[<-|[]]]]]; assumption).
  pose proof (@NoDup_incl_length nat [w; x; y; z] C Hnd4 Hincl) as H; simpl in H; lia.
Qed.

(** Two filters compose into one. *)

Lemma filter_filter_and :
  forall (f g : list nat -> bool) (L : Family),
    filter g (filter f L) = filter (fun C => f C && g C) L.
Proof.
  intros f g L; induction L as [|C L IH]; simpl; [reflexivity|].
  destruct (f C) eqn:Ef; simpl; destruct (g C) eqn:Eg; simpl; rewrite IH; reflexivity.
Qed.

Section Sharp.

Variable r : nat.
Variable G : Family.

Hypothesis HU : Uniform 3 G.
Hypothesis HR : RaoSpread 3 G r.
Hypothesis Hint : forall C D, In C G -> In D G -> exists x, In x C /\ In x D.

(** Rao's condition at a full triple: degree at most one. *)

Lemma rao_full : forall T, NoDup T -> length T = 3 -> deg T G <= 1.
Proof.
  intros T Hnd Hlen.
  assert (Hne : T <> []) by (destruct T; [discriminate | discriminate]).
  pose proof (HR Hnd Hne) as H; rewrite Hlen in H; simpl in H; exact H.
Qed.

(** ** The pieces, parametrised by anchor and excluded point *)

Definition piece (a b : nat) : Family :=
  filter (fun C => memb a C && negb (memb b C)) G.

Lemma in_piece : forall a b C,
    In C (piece a b) <-> In C G /\ In a C /\ ~ In b C.
Proof.
  intros a b C; unfold piece; rewrite filter_In.
  rewrite Bool.andb_true_iff, Bool.negb_true_iff, memb_true_iff, memb_false_iff.
  tauto.
Qed.

Lemma deg_piece_le : forall a b T, deg T (piece a b) <= deg T G.
Proof. intros; unfold piece; apply deg_filter_le. Qed.

Lemma piece_member : forall a b C, In C (piece a b) -> length C = 3 /\ NoDup C.
Proof.
  intros a b C HC; apply in_piece in HC as [HCG _]; exact (@uniform_mem 3 G C HU HCG).
Qed.

(** A member of [piece a b] is [a] and two other points, neither [a]
    nor [b]. *)

Lemma piece_split : forall a b C, In C (piece a b) ->
  exists u v,
    u <> v /\ a <> u /\ a <> v /\ b <> u /\ b <> v /\ In u C /\ In v C /\
    (forall y, In y C -> y = a \/ y = u \/ y = v).
Proof.
  intros a b C HC.
  pose proof HC as HC'; apply in_piece in HC' as [HCG [HaC HbC]].
  destruct (@uniform_mem 3 G C HU HCG) as [Hlen Hnd].
  destruct (@three_uniform_split C a Hlen Hnd HaC)
    as [u [v [Huv [Hau [Hav [HuC [HvC Hall]]]]]]].
  exists u, v.
  split; [exact Huv|]. split; [exact Hau|]. split; [exact Hav|].
  split; [intros <-; contradiction|]. split; [intros <-; contradiction|].
  split; [exact HuC|]. split; [exact HvC|]. exact Hall.
Qed.

(** Members of opposite pieces meet away from both anchors. *)

Lemma cross_meet : forall a b C D,
    In C (piece a b) -> In D (piece b a) ->
    exists x, In x C /\ In x D /\ x <> a /\ x <> b.
Proof.
  intros a b C D HC HD.
  apply in_piece in HC as [HCG [HaC HbC]]; apply in_piece in HD as [HDG [HbD HaD]].
  destruct (Hint C D HCG HDG) as [x [HxC HxD]].
  exists x. split; [exact HxC|]. split; [exact HxD|].
  split; intros <-; contradiction.
Qed.

(** ** Counting a piece against pairs and triples *)

Lemma piece_pair_bound : forall a b w,
    a <> w -> (forall C, In C (piece a b) -> In w C) ->
    length (piece a b) <= r.
Proof.
  intros a b w Haw Hall.
  assert (H : length (piece a b) <= length [[a; w]] * r).
  { apply cover_by_sets.
    - intros C HC; exists [a; w]; split; [left; reflexivity|].
      intros z [<-|[<-|[]]]; [apply in_piece in HC; tauto | apply Hall; exact HC].
    - intros T [<-|[]].
      eapply Nat.le_trans; [apply deg_piece_le | apply (rao_pair HR Haw)]. }
  simpl in H; lia.
Qed.

Lemma piece_two_pairs_bound : forall a b u v,
    a <> u -> a <> v ->
    (forall C, In C (piece a b) -> In u C \/ In v C) ->
    length (piece a b) <= 2 * r.
Proof.
  intros a b u v Hau Hav Hall.
  assert (H : length (piece a b) <= length [[a; u]; [a; v]] * r).
  { apply cover_by_sets.
    - intros C HC.
      assert (HaC : In a C) by (apply in_piece in HC; tauto).
      destruct (Hall C HC) as [HuC | HvC].
      + exists [a; u]; split; [left; reflexivity|]; intros z [<-|[<-|[]]]; assumption.
      + exists [a; v]; split; [right; left; reflexivity|]; intros z [<-|[<-|[]]]; assumption.
    - intros T [<-|[<-|[]]];
        (eapply Nat.le_trans; [apply deg_piece_le | apply (rao_pair HR); assumption]). }
  simpl in H; lia.
Qed.

(** Triples: every listed triple has degree at most one. *)

Lemma piece_triples_bound : forall a b (Ts : list (list nat)),
    (forall T, In T Ts -> NoDup T /\ length T = 3) ->
    (forall C, In C (piece a b) -> exists T, In T Ts /\ Subset T C) ->
    length (piece a b) <= length Ts.
Proof.
  intros a b Ts Hnd Hcov.
  assert (H : length (piece a b) <= length Ts * 1).
  { apply cover_by_sets; [exact Hcov|].
    intros T HT; destruct (Hnd T HT) as [H1 H2].
    eapply Nat.le_trans; [apply deg_piece_le | apply rao_full; assumption]. }
  lia.
Qed.

(** ** Case: [piece a b] has a common point *)

Lemma common_point_case : forall a b u,
    a <> b -> a <> u ->
    (forall C, In C (piece a b) -> In u C) ->
    piece a b <> [] ->
    length (piece a b) + length (piece b a) <= 2 * r + 1.
Proof.
  intros a b u Hab Hau Hall Hne.
  destruct (member_of_nonempty Hne) as [C0 HC0].
  assert (Hbu : b <> u).
  { intros <-; pose proof HC0 as HC0'; apply in_piece in HC0' as [_ [_ HbC]]; apply HbC, Hall, HC0. }
  pose proof (@piece_pair_bound a b u Hau Hall) as Ha_r.
  destruct (existsb (fun D => negb (memb u D)) (piece b a)) eqn:Eu.
  - (* some member of the other piece misses u *)
    apply existsb_exists in Eu as [D [HD HuDb]].
    apply Bool.negb_true_iff, memb_false_iff in HuDb.
    destruct (@piece_split b a D HD)
      as [d1 [d2 [Hd12 [Hbd1 [Hbd2 [Had1 [Had2 [Hd1D [Hd2D HallD]]]]]]]]].
    assert (Hud1 : u <> d1) by (intros <-; contradiction).
    assert (Hud2 : u <> d2) by (intros <-; contradiction).
    (* every member of piece a b is {a,u,d1} or {a,u,d2} *)
    assert (Hpin : forall C, In C (piece a b) ->
                     Subset [a; u; d1] C \/ Subset [a; u; d2] C).
    { intros C HC.
      assert (HaC : In a C) by (apply in_piece in HC; tauto).
      pose proof (Hall C HC) as HuC.
      destruct (@cross_meet a b C D HC HD) as [x [HxC [HxD [Hxa Hxb]]]].
      destruct (HallD x HxD) as [<- | [<- | <-]]; [exfalso; auto | left | right];
        intros z [<-|[<-|[<-|[]]]]; assumption. }
    assert (Ha_2 : length (piece a b) <= 2).
    { assert (H : length (piece a b) <= length [[a; u; d1]; [a; u; d2]]).
      { apply piece_triples_bound.
        - intros T [<-|[<-|[]]]; split; [apply NoDup3; assumption | reflexivity
                                        | apply NoDup3; assumption | reflexivity].
        - intros C HC; destruct (Hpin C HC) as [H1 | H2];
            [exists [a; u; d1]; split; [left; reflexivity | exact H1]
            | exists [a; u; d2]; split; [right; left; reflexivity | exact H2]]. }
      simpl in H; lia. }
    (* which of the two triples actually occur? *)
    destruct (existsb (fun C => memb d1 C) (piece a b)) eqn:E1;
    destruct (existsb (fun C => memb d2 C) (piece a b)) eqn:E2.
    + (* both occur: the other piece holds u, or holds both d1 and d2 *)
      apply existsb_exists in E1 as [C1 [HC1 Hd1C1]]; apply memb_true_iff in Hd1C1.
      apply existsb_exists in E2 as [C2 [HC2 Hd2C2]]; apply memb_true_iff in Hd2C2.
      destruct (piece_member _ _ _ HC1) as [Hlen1 Hnd1].
      destruct (piece_member _ _ _ HC2) as [Hlen2 Hnd2].
      assert (HallC1 : forall t, In t C1 -> t = a \/ t = u \/ t = d1).
      { apply three_of_three; try assumption; [pose proof HC1 as HC1'; apply in_piece in HC1'; tauto | apply Hall; exact HC1]. }
      assert (HallC2 : forall t, In t C2 -> t = a \/ t = u \/ t = d2).
      { apply three_of_three; try assumption; [pose proof HC2 as HC2'; apply in_piece in HC2'; tauto | apply Hall; exact HC2]. }
      assert (Hb : length (piece b a) <= degsum [[b; u]; [b; d1; d2]] (piece b a)).
      { apply cover_degsum; intros D' HD'.
        assert (HbD' : In b D') by (apply in_piece in HD'; tauto).
        destruct (@cross_meet b a D' C1 HD' HC1) as [x [HxD' [HxC1 [Hxb Hxa]]]].
        destruct (HallC1 x HxC1) as [<- | [<- | <-]]; [exfalso; auto | |].
        - exists [b; x]; split; [left; reflexivity|]; intros z [<-|[<-|[]]]; assumption.
        - destruct (@cross_meet b a D' C2 HD' HC2) as [y [HyD' [HyC2 [Hyb Hya]]]].
          destruct (HallC2 y HyC2) as [<- | [<- | <-]]; [exfalso; auto | |].
          + exists [b; y]; split; [left; reflexivity|]; intros z [<-|[<-|[]]]; assumption.
          + exists [b; x; y]; split; [right; left; reflexivity|];
              intros z [<-|[<-|[<-|[]]]]; assumption. }
      simpl in Hb.
      pose proof (@deg_piece_le b a [b; u]) as D1.
      pose proof (rao_pair HR Hbu) as D2.
      pose proof (@deg_piece_le b a [b; d1; d2]) as D3.
      pose proof (@rao_full [b; d1; d2] (NoDup3 Hbd1 Hbd2 Hd12) eq_refl) as D4.
      lia.
    + (* only d1 occurs: piece a b is a single triple; the other piece
         holds u or d1 *)
      assert (Hall1 : forall C, In C (piece a b) -> Subset [a; u; d1] C).
      { intros C HC; destruct (Hpin C HC) as [H1 | H2]; [exact H1 | exfalso].
        pose proof (existsb_false_forall _ _ _ E2 C HC) as E.
        apply memb_false_iff in E; apply E, H2; right; right; left; reflexivity. }
      assert (Ha_1 : length (piece a b) <= 1).
      { assert (H : length (piece a b) <= length [[a; u; d1]]).
        { apply piece_triples_bound.
          - intros T [<-|[]]; split; [apply NoDup3; assumption | reflexivity].
          - intros C HC; exists [a; u; d1]; split; [left; reflexivity | apply Hall1; exact HC]. }
        simpl in H; lia. }
      assert (Hb : length (piece b a) <= 2 * r).
      { apply (@piece_two_pairs_bound b a u d1 Hbu Hbd1).
        intros D' HD'.
        destruct (@cross_meet b a D' C0 HD' HC0) as [x [HxD' [HxC0 [Hxb Hxa]]]].
        destruct (piece_member _ _ _ HC0) as [Hlen0 Hnd0].
        pose proof (Hall1 C0 HC0) as HS.
        assert (HallC0 : forall t, In t C0 -> t = a \/ t = u \/ t = d1).
        { apply three_of_three; try assumption; apply HS;
            [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity]. }
        destruct (HallC0 x HxC0) as [<- | [<- | <-]]; [exfalso; auto | left | right]; assumption. }
      lia.
    + (* only d2 occurs: symmetric *)
      assert (Hall2 : forall C, In C (piece a b) -> Subset [a; u; d2] C).
      { intros C HC; destruct (Hpin C HC) as [H1 | H2]; [exfalso | exact H2].
        pose proof (existsb_false_forall _ _ _ E1 C HC) as E.
        apply memb_false_iff in E; apply E, H1; right; right; left; reflexivity. }
      assert (Ha_1 : length (piece a b) <= 1).
      { assert (H : length (piece a b) <= length [[a; u; d2]]).
        { apply piece_triples_bound.
          - intros T [<-|[]]; split; [apply NoDup3; assumption | reflexivity].
          - intros C HC; exists [a; u; d2]; split; [left; reflexivity | apply Hall2; exact HC]. }
        simpl in H; lia. }
      assert (Hb : length (piece b a) <= 2 * r).
      { apply (@piece_two_pairs_bound b a u d2 Hbu Hbd2).
        intros D' HD'.
        destruct (@cross_meet b a D' C0 HD' HC0) as [x [HxD' [HxC0 [Hxb Hxa]]]].
        destruct (piece_member _ _ _ HC0) as [Hlen0 Hnd0].
        pose proof (Hall2 C0 HC0) as HS.
        assert (HallC0 : forall t, In t C0 -> t = a \/ t = u \/ t = d2).
        { apply three_of_three; try assumption; apply HS;
            [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity]. }
        destruct (HallC0 x HxC0) as [<- | [<- | <-]]; [exfalso; auto | left | right]; assumption. }
      lia.
    + (* neither occurs: impossible, C0 is one of them *)
      exfalso.
      destruct (Hpin C0 HC0) as [H1 | H2].
      * pose proof (existsb_false_forall _ _ _ E1 C0 HC0) as E.
        apply memb_false_iff in E; apply E, H1; right; right; left; reflexivity.
      * pose proof (existsb_false_forall _ _ _ E2 C0 HC0) as E.
        apply memb_false_iff in E; apply E, H2; right; right; left; reflexivity.
  - (* every member of the other piece holds u too *)
    assert (Hallb : forall D, In D (piece b a) -> In u D).
    { intros D HD; pose proof (existsb_false_forall _ _ _ Eu D HD) as E.
      apply Bool.negb_false_iff, memb_true_iff in E; exact E. }
    pose proof (@piece_pair_bound b a u Hbu Hallb); lia.
Qed.

(** ** Case: no common point on either side *)

(** Pairwise-meeting tails with no common point: at most three members
    (the triangle). *)

Lemma tails_meet_no_common_point : forall a b,
    a <> b ->
    (forall C C', In C (piece a b) -> In C' (piece a b) ->
                  exists x, In x C /\ In x C' /\ x <> a) ->
    (forall w, w <> a -> exists C, In C (piece a b) /\ ~ In w C) ->
    piece a b <> [] ->
    length (piece a b) <= 3.
Proof.
  intros a b Hab Hmeet Hnoc Hne.
  destruct (member_of_nonempty Hne) as [C1 HC1].
  destruct (@piece_split a b C1 HC1)
    as [u [v [Huv [Hau [Hav [Hbu [Hbv [HuC1 [HvC1 Hall1]]]]]]]]].
  destruct (Hnoc u (not_eq_sym Hau)) as [C2 [HC2 HuC2]].
  destruct (Hnoc v (not_eq_sym Hav)) as [C3 [HC3 HvC3]].
  (* C2 holds v *)
  assert (HvC2 : In v C2).
  { destruct (Hmeet C2 C1 HC2 HC1) as [x [HxC2 [HxC1 Hxa]]].
    destruct (Hall1 x HxC1) as [<- | [<- | <-]]; [exfalso; auto | exfalso; auto | exact HxC2]. }
  destruct (@piece_split a b C2 HC2)
    as [s [t [Hst [Has [Hat [Hbs [Hbt [HsC2 [HtC2 Hall2]]]]]]]]].
  (* name w, the point of C2 other than a and v *)
  assert (Hw : exists w, In w C2 /\ w <> a /\ w <> v /\
                         (forall y, In y C2 -> y = a \/ y = v \/ y = w)).
  { destruct (Hall2 v HvC2) as [E | [E | E]].
    - exfalso; apply Hav; symmetry; exact E.
    - exists t. subst s. split; [exact HtC2|]. split; [exact (not_eq_sym Hat)|].
      split; [exact (not_eq_sym Hst)|].
      intros y Hy; destruct (Hall2 y Hy) as [E' | [E' | E']]; tauto.
    - exists s. subst t. split; [exact HsC2|]. split; [exact (not_eq_sym Has)|].
      split; [exact Hst|].
      intros y Hy; destruct (Hall2 y Hy) as [E' | [E' | E']]; tauto. }
  destruct Hw as [w [HwC2 [Hwa [Hwv Hall2']]]].
  assert (Hwu : w <> u) by (intros ->; contradiction).
  (* C3 holds u, and holds w *)
  assert (HuC3 : In u C3).
  { destruct (Hmeet C3 C1 HC3 HC1) as [x [HxC3 [HxC1 Hxa]]].
    destruct (Hall1 x HxC1) as [<- | [<- | <-]]; [exfalso; auto | exact HxC3 | exfalso; auto]. }
  assert (HwC3 : In w C3).
  { destruct (Hmeet C3 C2 HC3 HC2) as [x [HxC3 [HxC2 Hxa]]].
    destruct (Hall2' x HxC2) as [<- | [<- | <-]]; [exfalso; auto | exfalso; auto | exact HxC3]. }
  destruct (piece_member _ _ _ HC3) as [Hlen3 Hnd3].
  assert (HaC3 : In a C3) by (apply in_piece in HC3; tauto).
  assert (Hall3 : forall y, In y C3 -> y = a \/ y = u \/ y = w).
  { apply three_of_three; try assumption; try (apply not_eq_sym; assumption). }
  (* every member holds two of u, v, w *)
  assert (H : length (piece a b) <= length [[a; u; v]; [a; v; w]; [a; u; w]]).
  { apply piece_triples_bound.
    - intros T [<-|[<-|[<-|[]]]]; split; try reflexivity; apply NoDup3; auto.
    - intros C HC.
      assert (HaC : In a C) by (apply in_piece in HC; tauto).
      destruct (Hmeet C C1 HC HC1) as [x [HxC [HxC1 Hxa]]].
      destruct (Hmeet C C2 HC HC2) as [y [HyC [HyC2 Hya]]].
      destruct (Hmeet C C3 HC HC3) as [z [HzC [HzC3 Hza]]].
      destruct (Hall1 x HxC1) as [<- | [<- | <-]]; [exfalso; auto | |].
      + (* u in C *)
        destruct (Hall2' y HyC2) as [<- | [<- | <-]]; [exfalso; auto | |].
        * exists [a; x; y]; split; [left; reflexivity|]; intros q' [<-|[<-|[<-|[]]]]; assumption.
        * exists [a; x; y]; split; [right; right; left; reflexivity|]; intros q' [<-|[<-|[<-|[]]]]; assumption.
      + (* v in C *)
        destruct (Hall3 z HzC3) as [<- | [<- | <-]]; [exfalso; auto | |].
        * exists [a; z; x]; split; [left; reflexivity|]; intros q' [<-|[<-|[<-|[]]]]; assumption.
        * exists [a; x; z]; split; [right; left; reflexivity|]; intros q' [<-|[<-|[<-|[]]]]; assumption. }
  simpl in H; lia.
Qed.

(** Two members with disjoint tails pin the other piece to four
    triples; and if all four occur, they pin this piece to two.  Split
    into three lemmas to keep each proof term small. *)

Lemma disjoint_tails_pin : forall a b C C' x1 x2 y1 y2,
    In C (piece a b) -> In C' (piece a b) ->
    (forall y, In y C -> y = a \/ y = x1 \/ y = x2) ->
    (forall y, In y C' -> y = a \/ y = y1 \/ y = y2) ->
    forall D, In D (piece b a) ->
      exists T, In T [[b; x1; y1]; [b; x1; y2]; [b; x2; y1]; [b; x2; y2]] /\ Subset T D.
Proof.
  intros a b C C' x1 x2 y1 y2 HC HC' HallC HallC' D HD.
  assert (HbD : In b D) by (apply in_piece in HD; tauto).
  destruct (@cross_meet b a D C HD HC) as [x [HxD [HxC [Hxb Hxa]]]].
  destruct (@cross_meet b a D C' HD HC') as [y [HyD [HyC' [Hyb Hya]]]].
  destruct (HallC x HxC) as [<- | [<- | <-]]; [exfalso; auto | |];
    destruct (HallC' y HyC') as [<- | [<- | <-]]; try (exfalso; auto; fail).
  - exists [b; x; y]; split; [left; reflexivity|]; intros z [<-|[<-|[<-|[]]]]; assumption.
  - exists [b; x; y]; split; [right; left; reflexivity|]; intros z [<-|[<-|[<-|[]]]]; assumption.
  - exists [b; x; y]; split; [right; right; left; reflexivity|]; intros z [<-|[<-|[<-|[]]]]; assumption.
  - exists [b; x; y]; split; [right; right; right; left; reflexivity|]; intros z [<-|[<-|[<-|[]]]]; assumption.
Qed.

(** If a piece pinned to four triples has four members, every one of
    the four triples is a member. *)

Lemma four_pinned_all_present : forall a b T1 T2 T3 T4,
    (forall T, In T [T1; T2; T3; T4] -> NoDup T /\ length T = 3) ->
    (forall D, In D (piece b a) -> exists T, In T [T1; T2; T3; T4] /\ Subset T D) ->
    4 <= length (piece b a) ->
    (exists D, In D (piece b a) /\ Subset T1 D) /\
    (exists D, In D (piece b a) /\ Subset T2 D) /\
    (exists D, In D (piece b a) /\ Subset T3 D) /\
    (exists D, In D (piece b a) /\ Subset T4 D).
Proof.
  intros a b T1 T2 T3 T4 HTs Hpin Hge.
  pose proof (@cover_degsum [T1; T2; T3; T4] (piece b a) Hpin) as Hsum; cbn [degsum] in Hsum.
  assert (Hle : forall T, In T [T1; T2; T3; T4] -> deg T (piece b a) <= 1).
  { intros T HT; destruct (HTs T HT) as [H1 H2].
    eapply Nat.le_trans; [apply deg_piece_le | apply rao_full; assumption]. }
  pose proof (Hle T1 ltac:(left; reflexivity)).
  pose proof (Hle T2 ltac:(right; left; reflexivity)).
  pose proof (Hle T3 ltac:(right; right; left; reflexivity)).
  pose proof (Hle T4 ltac:(right; right; right; left; reflexivity)).
  clear Hle Hpin HTs.
  repeat split; apply deg_pos_inv; lia.
Qed.

(** Every member of [piece a b] meeting the four cross triples has
    tail [{x1,x2}] or [{y1,y2}]. *)

Lemma four_present_force_tails : forall a b x1 x2 y1 y2 D11 D12 D21 D22,
    a <> b ->
    a <> x1 -> a <> x2 -> a <> y1 -> a <> y2 ->
    x1 <> x2 -> y1 <> y2 -> x1 <> y1 -> x1 <> y2 -> x2 <> y1 -> x2 <> y2 ->
    In D11 (piece b a) -> In D12 (piece b a) -> In D21 (piece b a) -> In D22 (piece b a) ->
    (forall t, In t D11 -> t = b \/ t = x1 \/ t = y1) ->
    (forall t, In t D12 -> t = b \/ t = x1 \/ t = y2) ->
    (forall t, In t D21 -> t = b \/ t = x2 \/ t = y1) ->
    (forall t, In t D22 -> t = b \/ t = x2 \/ t = y2) ->
    forall E, In E (piece a b) ->
      exists T, In T [[a; x1; x2]; [a; y1; y2]] /\ Subset T E.
Proof.
  intros a b x1 x2 y1 y2 D11 D12 D21 D22 Hab Hax1 Hax2 Hay1 Hay2 Hx12 Hy12
         Hx1y1 Hx1y2 Hx2y1 Hx2y2 HD11 HD12 HD21 HD22 Hall11 Hall12 Hall21 Hall22 E HE.
  assert (HaE : In a E) by (apply in_piece in HE; tauto).
  destruct (piece_member _ _ _ HE) as [HlenE HndE].
  destruct (@cross_meet a b E D11 HE HD11) as [p11 [Hp11E [Hp11D [Hp11a Hp11b]]]].
  destruct (@cross_meet a b E D12 HE HD12) as [p12 [Hp12E [Hp12D [Hp12a Hp12b]]]].
  destruct (@cross_meet a b E D21 HE HD21) as [p21 [Hp21E [Hp21D [Hp21a Hp21b]]]].
  destruct (@cross_meet a b E D22 HE HD22) as [p22 [Hp22E [Hp22D [Hp22a Hp22b]]]].
  clear HD11 HD12 HD21 HD22.
  destruct (Hall11 p11 Hp11D) as [-> | [-> | ->]]; [exfalso; auto | |].
  - (* x1 in E *)
    destruct (Hall21 p21 Hp21D) as [-> | [-> | ->]]; [exfalso; auto | |].
    + exists [a; x1; x2]; split; [left; reflexivity|]; intros z [<-|[<-|[<-|[]]]]; assumption.
    + destruct (Hall22 p22 Hp22D) as [-> | [-> | ->]]; [exfalso; auto | |].
      * exists [a; x1; x2]; split; [left; reflexivity|]; intros z [<-|[<-|[<-|[]]]]; assumption.
      * exfalso; apply (@four_in_three E a x1 y1 y2); auto.
  - (* y1 in E *)
    destruct (Hall12 p12 Hp12D) as [-> | [-> | ->]]; [exfalso; auto | |].
    + destruct (Hall22 p22 Hp22D) as [-> | [-> | ->]]; [exfalso; auto | |].
      * exfalso; apply (@four_in_three E a x1 y1 x2); auto.
      * exists [a; y1; y2]; split; [right; left; reflexivity|]; intros z [<-|[<-|[<-|[]]]]; assumption.
    + exists [a; y1; y2]; split; [right; left; reflexivity|]; intros z [<-|[<-|[<-|[]]]]; assumption.
Qed.

Lemma disjoint_tails_case : forall a b C C',
    a <> b ->
    In C (piece a b) -> In C' (piece a b) ->
    (forall x, In x C -> In x C' -> x = a) ->
    length (piece b a) <= 4 /\
    (4 <= length (piece b a) -> length (piece a b) <= 2).
Proof.
  intros a b C C' Hab HC HC' Hdis.
  destruct (@piece_split a b C HC)
    as [x1 [x2 [Hx12 [Hax1 [Hax2 [Hbx1 [Hbx2 [Hx1C [Hx2C HallC]]]]]]]]].
  destruct (@piece_split a b C' HC')
    as [y1 [y2 [Hy12 [Hay1 [Hay2 [Hby1 [Hby2 [Hy1C [Hy2C HallC']]]]]]]]].
  assert (Hx1y1 : x1 <> y1) by (intros <-; apply Hax1; symmetry; apply Hdis; assumption).
  assert (Hx1y2 : x1 <> y2) by (intros <-; apply Hax1; symmetry; apply Hdis; assumption).
  assert (Hx2y1 : x2 <> y1) by (intros <-; apply Hax2; symmetry; apply Hdis; assumption).
  assert (Hx2y2 : x2 <> y2) by (intros <-; apply Hax2; symmetry; apply Hdis; assumption).
  pose proof (@disjoint_tails_pin a b C C' x1 x2 y1 y2 HC HC' HallC HallC') as Hpin.
  assert (HTs : forall T, In T [[b; x1; y1]; [b; x1; y2]; [b; x2; y1]; [b; x2; y2]] ->
                  NoDup T /\ length T = 3).
  { intros T [<-|[<-|[<-|[<-|[]]]]]; split; try reflexivity; apply NoDup3; auto. }
  pose proof (@piece_triples_bound b a _ HTs Hpin) as H4; simpl in H4.
  split; [exact H4|].
  intro Hge.
  destruct (@four_pinned_all_present a b _ _ _ _ HTs Hpin Hge)
    as [[D11 [HD11 HS11]] [[D12 [HD12 HS12]] [[D21 [HD21 HS21]] [D22 [HD22 HS22]]]]].
  assert (Hex : forall D x y, In D (piece b a) -> Subset [b; x; y] D ->
                  b <> x -> b <> y -> x <> y ->
                  forall t, In t D -> t = b \/ t = x \/ t = y).
  { intros D x y HD HS Hbx Hby Hxy.
    destruct (piece_member _ _ _ HD) as [Hlen Hnd].
    apply three_of_three; try assumption; apply HS;
      [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity]. }
  pose proof (Hex D11 x1 y1 HD11 HS11 Hbx1 Hby1 Hx1y1) as Hall11.
  pose proof (Hex D12 x1 y2 HD12 HS12 Hbx1 Hby2 Hx1y2) as Hall12.
  pose proof (Hex D21 x2 y1 HD21 HS21 Hbx2 Hby1 Hx2y1) as Hall21.
  pose proof (Hex D22 x2 y2 HD22 HS22 Hbx2 Hby2 Hx2y2) as Hall22.
  clear Hex HS11 HS12 HS21 HS22 Hpin HTs H4 Hge.
  assert (H : length (piece a b) <= length [[a; x1; x2]; [a; y1; y2]]).
  { apply piece_triples_bound.
    - intros T [<-|[<-|[]]]; split; try reflexivity; apply NoDup3; auto.
    - apply (@four_present_force_tails a b x1 x2 y1 y2 D11 D12 D21 D22); assumption. }
  simpl in H; exact H.
Qed.

(** No common point on either side: the sum is at most seven. *)

Lemma no_common_point_case : forall a b,
    a <> b ->
    piece a b <> [] -> piece b a <> [] ->
    (forall w, w <> a -> exists C, In C (piece a b) /\ ~ In w C) ->
    (forall w, w <> b -> exists D, In D (piece b a) /\ ~ In w D) ->
    length (piece a b) + length (piece b a) <= 7.
Proof.
  intros a b Hab Hne Hne' Hnoc Hnoc'.
  (* a piece with >= 4 members has two members with disjoint tails *)
  assert (Hsplit : forall c d,
             c <> d -> piece c d <> [] ->
             (forall w, w <> c -> exists C, In C (piece c d) /\ ~ In w C) ->
             4 <= length (piece c d) ->
             exists C C', In C (piece c d) /\ In C' (piece c d) /\
                          (forall x, In x C -> In x C' -> x = c)).
  { intros c d Hcd Hne0 Hnoc0 H4.
    destruct (existsb (fun C => existsb (fun C' =>
                negb (existsb (fun x => memb x C' && negb (Nat.eqb x c)) C))
                (piece c d)) (piece c d)) eqn:E.
    - apply existsb_exists in E as [C [HC E']].
      apply existsb_exists in E' as [C' [HC' E'']].
      apply Bool.negb_true_iff in E''.
      exists C, C'; split; [exact HC|]; split; [exact HC'|].
      intros x HxC HxC'.
      pose proof (existsb_false_forall _ _ _ E'' x HxC) as Hx.
      apply Bool.andb_false_iff in Hx as [Hx | Hx].
      + apply memb_false_iff in Hx; contradiction.
      + apply Bool.negb_false_iff, Nat.eqb_eq in Hx; exact Hx.
    - exfalso.
      assert (Hmeet : forall C C', In C (piece c d) -> In C' (piece c d) ->
                        exists x, In x C /\ In x C' /\ x <> c).
      { intros C C' HC HC'.
        pose proof (existsb_false_forall _ _ _ E C HC) as E1.
        pose proof (existsb_false_forall _ _ _ E1 C' HC') as E2.
        apply Bool.negb_false_iff, existsb_exists in E2 as [x [HxC Hx]].
        apply Bool.andb_true_iff in Hx as [Hx1 Hx2].
        apply memb_true_iff in Hx1; apply Bool.negb_true_iff, Nat.eqb_neq in Hx2.
        exists x; tauto. }
      pose proof (@tails_meet_no_common_point c d Hcd Hmeet Hnoc0 Hne0); lia. }
  (* bound each side by 4, via a disjoint-tailed pair on the other *)
  destruct (le_lt_dec 4 (length (piece a b))) as [H4a | H3a];
  destruct (le_lt_dec 4 (length (piece b a))) as [H4b | H3b].
  - (* both >= 4: impossible *)
    destruct (Hsplit a b Hab Hne Hnoc H4a) as [C [C' [HC [HC' Hdis]]]].
    destruct (@disjoint_tails_case a b C C' Hab HC HC' Hdis) as [_ Hpin].
    pose proof (Hpin H4b) as H2; clear - H2 H4a; lia.
  - destruct (Hsplit a b Hab Hne Hnoc H4a) as [C [C' [HC [HC' Hdis]]]].
    destruct (@disjoint_tails_case a b C C' Hab HC HC' Hdis) as [Hb4 _].
    (* piece a b <= 4 too, from the other side? use the same device on b *)
    destruct (le_lt_dec 5 (length (piece a b))) as [H5 | H5]; [|clear - H5 H3b; lia].
    (* piece b a has at most 3, and piece a b >= 5: need piece a b <= 4 *)
    assert (Hba : b <> a) by (intros ->; apply Hab; reflexivity).
    (* piece b a nonempty with no common point: pin piece a b to 4 triples *)
    destruct (member_of_nonempty Hne') as [D1 HD1].
    destruct (@piece_split b a D1 HD1)
      as [u [v [Huv [Hbu [Hbv [Hau [Hav [HuD1 [HvD1 HallD1]]]]]]]]].
    destruct (Hnoc' u (not_eq_sym Hbu)) as [D2 [HD2 HuD2]].
    destruct (Hnoc' v (not_eq_sym Hbv)) as [D3 [HD3 HvD3]].
    destruct (@piece_split b a D2 HD2)
      as [a2 [b2 [Ha2b2 [Hba2 [Hbb2 [Haa2 [Hab2 [Ha2D2 [Hb2D2 HallD2]]]]]]]]].
    destruct (@piece_split b a D3 HD3)
      as [a3 [b3 [Ha3b3 [Hba3 [Hbb3 [Haa3 [Hab3 [Ha3D3 [Hb3D3 HallD3]]]]]]]]].
    assert (Hua2 : u <> a2) by (intros <-; contradiction).
    assert (Hub2 : u <> b2) by (intros <-; contradiction).
    assert (Hva3 : v <> a3) by (intros <-; contradiction).
    assert (Hvb3 : v <> b3) by (intros <-; contradiction).
    assert (H : length (piece a b) <= length [[a; u; a2]; [a; u; b2]; [a; v; a3]; [a; v; b3]]).
    { apply piece_triples_bound.
      - intros T [<-|[<-|[<-|[<-|[]]]]]; split; try reflexivity; apply NoDup3; auto.
      - intros C0 HC0.
        assert (HaC0 : In a C0) by (apply in_piece in HC0; tauto).
        destruct (@cross_meet a b C0 D1 HC0 HD1) as [x [HxC0 [HxD1 [Hxa Hxb]]]].
        destruct (HallD1 x HxD1) as [<- | [<- | <-]]; [exfalso; auto | |].
        + destruct (@cross_meet a b C0 D2 HC0 HD2) as [y [HyC0 [HyD2 [Hya Hyb]]]].
          destruct (HallD2 y HyD2) as [<- | [<- | <-]]; [exfalso; auto | |].
          * exists [a; x; y]; split; [left; reflexivity|]; intros z [<-|[<-|[<-|[]]]]; assumption.
          * exists [a; x; y]; split; [right; left; reflexivity|]; intros z [<-|[<-|[<-|[]]]]; assumption.
        + destruct (@cross_meet a b C0 D3 HC0 HD3) as [y [HyC0 [HyD3 [Hya Hyb]]]].
          destruct (HallD3 y HyD3) as [<- | [<- | <-]]; [exfalso; auto | |].
          * exists [a; x; y]; split; [right; right; left; reflexivity|]; intros z [<-|[<-|[<-|[]]]]; assumption.
          * exists [a; x; y]; split; [right; right; right; left; reflexivity|]; intros z [<-|[<-|[<-|[]]]]; assumption. }
    simpl in H; clear - H H3b; lia.
  - (* piece a b <= 3, piece b a >= 4: bound piece b a by 4 *)
    assert (Hba : b <> a) by (intros ->; apply Hab; reflexivity).
    destruct (Hsplit b a Hba Hne' Hnoc' H4b) as [D [D' [HD [HD' Hdis]]]].
    destruct (@disjoint_tails_case b a D D' Hba HD HD' Hdis) as [Ha4 _].
    destruct (le_lt_dec 5 (length (piece b a))) as [H5 | H5]; [|clear - H5 H3a; lia].
    destruct (member_of_nonempty Hne) as [C1 HC1].
    destruct (@piece_split a b C1 HC1)
      as [u [v [Huv [Hau [Hav [Hbu [Hbv [HuC1 [HvC1 HallC1]]]]]]]]].
    destruct (Hnoc u (not_eq_sym Hau)) as [C2 [HC2 HuC2]].
    destruct (Hnoc v (not_eq_sym Hav)) as [C3 [HC3 HvC3]].
    destruct (@piece_split a b C2 HC2)
      as [a2 [b2 [Ha2b2 [Haa2 [Hab2 [Hba2 [Hbb2 [Ha2C2 [Hb2C2 HallC2]]]]]]]]].
    destruct (@piece_split a b C3 HC3)
      as [a3 [b3 [Ha3b3 [Haa3 [Hab3 [Hba3 [Hbb3 [Ha3C3 [Hb3C3 HallC3]]]]]]]]].
    assert (Hua2 : u <> a2) by (intros <-; contradiction).
    assert (Hub2 : u <> b2) by (intros <-; contradiction).
    assert (Hva3 : v <> a3) by (intros <-; contradiction).
    assert (Hvb3 : v <> b3) by (intros <-; contradiction).
    assert (H : length (piece b a) <= length [[b; u; a2]; [b; u; b2]; [b; v; a3]; [b; v; b3]]).
    { apply piece_triples_bound.
      - intros T [<-|[<-|[<-|[<-|[]]]]]; split; try reflexivity; apply NoDup3; auto.
      - intros D0 HD0.
        assert (HbD0 : In b D0) by (apply in_piece in HD0; tauto).
        destruct (@cross_meet b a D0 C1 HD0 HC1) as [x [HxD0 [HxC1 [Hxb Hxa]]]].
        destruct (HallC1 x HxC1) as [<- | [<- | <-]]; [exfalso; auto | |].
        + destruct (@cross_meet b a D0 C2 HD0 HC2) as [y [HyD0 [HyC2 [Hyb Hya]]]].
          destruct (HallC2 y HyC2) as [<- | [<- | <-]]; [exfalso; auto | |].
          * exists [b; x; y]; split; [left; reflexivity|]; intros z [<-|[<-|[<-|[]]]]; assumption.
          * exists [b; x; y]; split; [right; left; reflexivity|]; intros z [<-|[<-|[<-|[]]]]; assumption.
        + destruct (@cross_meet b a D0 C3 HD0 HC3) as [y [HyD0 [HyC3 [Hyb Hya]]]].
          destruct (HallC3 y HyC3) as [<- | [<- | <-]]; [exfalso; auto | |].
          * exists [b; x; y]; split; [right; right; left; reflexivity|]; intros z [<-|[<-|[<-|[]]]]; assumption.
          * exists [b; x; y]; split; [right; right; right; left; reflexivity|]; intros z [<-|[<-|[<-|[]]]]; assumption. }
    simpl in H; clear - H H3a; lia.
  - clear - H3a H3b; lia.
Qed.

(** ** The partition of [G] under a two-point cover *)

Lemma pieces_sum : forall p q,
    p <> q ->
    (forall C, In C G -> In p C \/ In q C) ->
    length G = length (piece p q) + length (piece q p)
               + length (filter (fun C => memb p C && memb q C) G).
Proof.
  intros p q Hpq Hcov.
  pose proof (length_filter_partition (fun C => memb p C) G) as H1; cbv beta in H1.
  pose proof (length_filter_partition (fun C => memb q C) (filter (fun C => memb p C) G)) as H2; cbv beta in H2.
  assert (E1 : filter (fun C => memb q C) (filter (fun C => memb p C) G)
               = filter (fun C => memb p C && memb q C) G)
    by apply filter_filter_and.
  assert (E2 : filter (fun C => negb (memb q C)) (filter (fun C => memb p C) G)
               = piece p q)
    by apply filter_filter_and.
  assert (E3 : filter (fun C => negb (memb p C)) G = piece q p).
  { unfold piece; apply filter_ext_in; intros C HC.
    destruct (memb p C) eqn:Ep; simpl.
    - rewrite Bool.andb_false_r; reflexivity.
    - apply memb_false_iff in Ep.
      destruct (Hcov C HC) as [Hp | Hq]; [contradiction|].
      apply memb_true_iff in Hq; rewrite Hq; reflexivity. }
  rewrite E1, E2 in H2. rewrite E3 in H1. lia.
Qed.

Lemma both_bound : forall p q,
    p <> q ->
    length (filter (fun C => memb p C && memb q C) G) <= r.
Proof.
  intros p q Hpq.
  assert (H : length (filter (fun C => memb p C && memb q C) G) <= length [[p; q]] * r).
  { apply cover_by_sets.
    - intros C HC; apply filter_In in HC as [_ Hb].
      apply Bool.andb_true_iff in Hb as [Hp Hq]; apply memb_true_iff in Hp, Hq.
      exists [p; q]; split; [left; reflexivity|]; intros z [<-|[<-|[]]]; assumption.
    - intros T [<-|[]].
      eapply Nat.le_trans; [apply deg_filter_le | apply (rao_pair HR Hpq)]. }
  simpl in H; lia.
Qed.

(** ** The theorem *)

Theorem two_cover_sharp : forall p q,
    p <> q ->
    (forall C, In C G -> In p C \/ In q C) ->
    piece p q <> [] -> piece q p <> [] ->
    3 <= r ->
    length G <= 3 * r + 1.
Proof.
  intros p q Hpq Hcov Hne Hne' Hr.
  pose proof (pieces_sum Hpq Hcov) as Hsum.
  pose proof (both_bound Hpq) as Hboth.
  assert (Hqp : q <> p) by (intros ->; apply Hpq; reflexivity).
  (* decide whether piece p q has a common point *)
  destruct (member_of_nonempty Hne) as [C1 HC1].
  destruct (@piece_split p q C1 HC1)
    as [u [v [Huv [Hpu [Hpv [Hqu [Hqv [HuC1 [HvC1 HallC1]]]]]]]]].
  destruct (existsb (fun C => negb (memb u C)) (piece p q)) eqn:Eu.
  2: { assert (Hall : forall C, In C (piece p q) -> In u C).
       { intros C HC; pose proof (existsb_false_forall _ _ _ Eu C HC) as E.
         apply Bool.negb_false_iff, memb_true_iff in E; exact E. }
       pose proof (@common_point_case p q u Hpq Hpu Hall Hne); lia. }
  destruct (existsb (fun C => negb (memb v C)) (piece p q)) eqn:Ev.
  2: { assert (Hall : forall C, In C (piece p q) -> In v C).
       { intros C HC; pose proof (existsb_false_forall _ _ _ Ev C HC) as E.
         apply Bool.negb_false_iff, memb_true_iff in E; exact E. }
       pose proof (@common_point_case p q v Hpq Hpv Hall Hne); lia. }
  apply existsb_exists in Eu as [C2 [HC2 Hu2]].
  apply Bool.negb_true_iff, memb_false_iff in Hu2.
  apply existsb_exists in Ev as [C3 [HC3 Hv3]].
  apply Bool.negb_true_iff, memb_false_iff in Hv3.
  assert (Hnoc : forall w, w <> p -> exists C, In C (piece p q) /\ ~ In w C).
  { intros w Hwp.
    destruct (in_dec_nat w C1) as [HwC1 | HwC1].
    - destruct (HallC1 w HwC1) as [-> | [-> | ->]]; [contradiction | exists C2; tauto | exists C3; tauto].
    - exists C1; tauto. }
  (* the same for piece q p *)
  destruct (member_of_nonempty Hne') as [D1 HD1].
  destruct (@piece_split q p D1 HD1)
    as [u' [v' [Huv' [Hqu' [Hqv' [Hpu' [Hpv' [HuD1 [HvD1 HallD1]]]]]]]]].
  destruct (existsb (fun D => negb (memb u' D)) (piece q p)) eqn:Eu'.
  2: { assert (Hall : forall D, In D (piece q p) -> In u' D).
       { intros D HD; pose proof (existsb_false_forall _ _ _ Eu' D HD) as E.
         apply Bool.negb_false_iff, memb_true_iff in E; exact E. }
       pose proof (@common_point_case q p u' Hqp Hqu' Hall Hne'); lia. }
  destruct (existsb (fun D => negb (memb v' D)) (piece q p)) eqn:Ev'.
  2: { assert (Hall : forall D, In D (piece q p) -> In v' D).
       { intros D HD; pose proof (existsb_false_forall _ _ _ Ev' D HD) as E.
         apply Bool.negb_false_iff, memb_true_iff in E; exact E. }
       pose proof (@common_point_case q p v' Hqp Hqv' Hall Hne'); lia. }
  apply existsb_exists in Eu' as [D2 [HD2 Hu2']].
  apply Bool.negb_true_iff, memb_false_iff in Hu2'.
  apply existsb_exists in Ev' as [D3 [HD3 Hv3']].
  apply Bool.negb_true_iff, memb_false_iff in Hv3'.
  assert (Hnoc' : forall w, w <> q -> exists D, In D (piece q p) /\ ~ In w D).
  { intros w Hwq.
    destruct (in_dec_nat w D1) as [HwD1 | HwD1].
    - destruct (HallD1 w HwD1) as [-> | [-> | ->]]; [contradiction | exists D2; tauto | exists D3; tauto].
    - exists D1; tauto. }
  pose proof (@no_common_point_case p q Hpq Hne Hne' Hnoc Hnoc'); lia.
Qed.

End Sharp.

(** ** Stated without the filters, in the form [TwoCover.two_cover_bound] uses *)

Theorem two_cover_at_most_3r_plus_1 :
  forall r (G : Family) p q,
    Uniform 3 G -> RaoSpread 3 G r ->
    (forall C D, In C G -> In D G -> exists x, In x C /\ In x D) ->
    (forall C, In C G -> In p C \/ In q C) ->
    p <> q -> 3 <= r ->
    (exists C, In C G /\ ~ In q C) ->
    (exists D, In D G /\ ~ In p D) ->
    length G <= 3 * r + 1.
Proof.
  intros r G p q HU HR Hint Hcov Hpq Hr [C [HCG HCq]] [D [HDG HDp]].
  apply (@two_cover_sharp r G HU HR Hint p q Hpq Hcov); [| | exact Hr].
  - intro E.
    assert (HC : In C (piece G p q)).
    { apply in_piece; split; [exact HCG|]. split; [|exact HCq].
      destruct (Hcov C HCG); [assumption | contradiction]. }
    rewrite E in HC; destruct HC.
  - intro E.
    assert (HD : In D (piece G q p)).
    { apply in_piece; split; [exact HDG|]. split; [|exact HDp].
      destruct (Hcov D HDG); [contradiction | assumption]. }
    rewrite E in HD; destruct HD.
Qed.

(** ** Sharpness: the bound is attained at every [r >= 3]

    The family with anchors [p = 0], [q = 1], and [u = 2], [w = 3]:
    [r] members [{p,u,x_i}], [r] members [{p,w,y_i}], the one member
    [{q,u,w}], and [r] members [{p,q,z_j}].  Intersecting, covered by
    [{p,q}] with neither point alone, and [3r + 1] members.  At [r = 3]
    it is checked by computation; the point degree [3r <= r^2] is what
    needs [r >= 3]. *)

Definition hm_family : Family :=
  [ [0; 2; 4]; [0; 2; 5]; [0; 2; 6];
    [0; 3; 7]; [0; 3; 8]; [0; 3; 9];
    [1; 2; 3];
    [0; 1; 10]; [0; 1; 11]; [0; 1; 12] ].

Definition two_covered_intersectingb (F : Family) : bool :=
  forallb (fun C => forallb (fun D => negb (disjointb C D)) F) F.

Lemma two_covered_intersectingb_correct : forall F,
    two_covered_intersectingb F = true ->
    forall C D, In C F -> In D F -> exists x, In x C /\ In x D.
Proof.
  intros F H C D HC HD.
  unfold two_covered_intersectingb in H; rewrite forallb_forall in H.
  specialize (H C HC); rewrite forallb_forall in H; specialize (H D HD).
  apply Bool.negb_true_iff in H.
  destruct (existsb (fun x => memb x D) C) eqn:E.
  - apply existsb_exists in E as [x [HxC HxD]]; apply memb_true_iff in HxD; exists x; tauto.
  - exfalso.
    assert (disjointb C D = true).
    { apply disjointb_correct; intros x HxC HxD.
      pose proof (existsb_false_forall _ _ _ E x HxC) as Hx.
      apply memb_false_iff in Hx; contradiction. }
    congruence.
Qed.

Lemma hm_family_uniform : Uniform 3 hm_family.
Proof. apply uniformb_correct; reflexivity. Qed.

Lemma hm_family_rao_spread : RaoSpread 3 hm_family 3.
Proof.
  apply (@rao_witness_none 3 hm_family 3).
  - apply (@Uniform_NoDup 3 hm_family hm_family_uniform).
  - vm_compute; reflexivity.
Qed.

Lemma hm_family_intersecting :
  forall C D, In C hm_family -> In D hm_family -> exists x, In x C /\ In x D.
Proof. apply two_covered_intersectingb_correct; vm_compute; reflexivity. Qed.

Lemma hm_family_covered : forall C, In C hm_family -> In 0 C \/ In 1 C.
Proof.
  intros C HC; simpl in HC.
  repeat (destruct HC as [<- | HC]; [simpl; tauto|]); destruct HC.
Qed.

(** The bound [3r + 1 = 10] is met with equality at [r = 3]. *)

Theorem two_cover_sharp_at_three_is_tight :
  length hm_family = 3 * 3 + 1 /\
  (exists C, In C hm_family /\ ~ In 1 C) /\
  (exists D, In D hm_family /\ ~ In 0 D).
Proof.
  split; [reflexivity|]. split.
  - exists [0; 2; 4]; split; [left; reflexivity | simpl; lia].
  - exists [1; 2; 3]; split; [do 6 right; left; reflexivity | simpl; lia].
Qed.
