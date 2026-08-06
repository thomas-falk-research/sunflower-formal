(** * TwoCover.v -- the two-point cover case of the intersecting piece,
      sharply.

    `docs/roadmap.md` §24.9 measures the quantity the spread threshold
    turns on:

<<
      I(m,r)  =  max |G|  over m-uniform *intersecting* G with
                 deg T <= r^(m - |T|) for every nonempty T,
>>

    and finds it a factor of two below what
    [SpreadThreshold.intersecting_piece_bound] proves. At [(m,r) = (3,3)]
    the truth is 10 against a bound of 21; at [(3,4)] it is 16, which is
    exactly the value that would give [r*(3,3) <= 4].

    An intersecting 3-uniform family has covering number at most 3, so
    the measurement splits into three cases. This file proves the second:

<<
      tau(G) = 2   =>   |G| <= max(4r, 3r + 4).
>>

    At [r = 4] both branches are 16, which is the value needed. The
    first case ([tau = 1], a star) is immediate from the point-degree
    cap. The third ([tau = 3]) is Frankl's theorem and is *not* proved
    here — see §24.9.

    ** Why the bound has two branches

    Write [G_p] for the members through [p] but not [q], [G_q] for the
    mirror, and [G_pq] for those through both. [G_pq] is capped by the
    pair degree at once. For the other two:

    - **Any member of [G_q] bounds [G_p] by [2r].** A member [C'] of
      [G_q] misses [p], so a member [C] of [G_p] can only meet it in one
      of the two points of [C'] other than [q] — and [C] contains [p], so
      [C] contains one of two *pairs*. Two pairs, each capped at [r].

    - **Either [G_p] has a common point besides [p], or [G_q] has at most
      four members.** If some [w <> p] lies in every member of [G_p] then
      [G_p] is capped by the single pair [{p,w}], at [r]. Otherwise pick
      [C1 = {p,u,v}] in [G_p]; some [C2] misses [u] and some [C3] misses
      [v]. A member of [G_q] must meet [C1] away from [p], so it contains
      [u] or [v]; if it contains [u] it must still meet [C2], which has
      neither [p] nor [u], so it contains one of [C2]'s two other points.
      That pins it to a *triple*, and a triple has degree at most one in
      a 3-uniform family with Rao's condition. Four triples, four
      members.

    The second branch is where the sharpness comes from, and it is why
    this argument needs no classification of graphs with matching number
    one — the usual route through "a star or a triangle" is replaced by
    naming two members that miss [u] and [v] respectively. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower Pigeonhole Spread SpreadReduction
     DirectSum SpreadThreshold.
Import ListNotations.

Set Implicit Arguments.

(** ** A 3-set through a known point is that point and two others *)

Lemma three_uniform_split :
  forall (C : list nat) (x : nat),
    length C = 3 -> NoDup C -> In x C ->
    exists a b,
      a <> b /\ x <> a /\ x <> b /\ In a C /\ In b C /\
      (forall y, In y C -> y = x \/ y = a \/ y = b).
Proof.
  intros C x Hlen Hnd Hx.
  destruct C as [|c1 [|c2 [|c3 [|c4 C']]]]; simpl in Hlen; try discriminate.
  inversion Hnd as [|z1 l1 H1 Hnd1]; subst.
  inversion Hnd1 as [|z2 l2 H2 Hnd2]; subst.
  assert (E12 : c1 <> c2) by (intros <-; apply H1; left; reflexivity).
  assert (E13 : c1 <> c3) by (intros <-; apply H1; right; left; reflexivity).
  assert (E23 : c2 <> c3) by (intros <-; apply H2; left; reflexivity).
  destruct Hx as [<-|[<-|[<-|[]]]].
  - exists c2, c3; repeat split; try assumption.
    + right; left; reflexivity.
    + right; right; left; reflexivity.
    + intros y [<-|[<-|[<-|[]]]]; tauto.
  - exists c1, c3; repeat split; try (intros <-; congruence).
    + left; reflexivity.
    + right; right; left; reflexivity.
    + intros y [<-|[<-|[<-|[]]]]; tauto.
  - exists c1, c2; repeat split; try (intros <-; congruence).
    + left; reflexivity.
    + right; left; reflexivity.
    + intros y [<-|[<-|[<-|[]]]]; tauto.
Qed.

(** ** Reading Rao's condition at pairs and at triples *)

Lemma rao_pair : forall r (G : Family) x y,
    RaoSpread 3 G r -> x <> y -> deg [x; y] G <= r.
Proof.
  intros r G x y HR Hxy.
  assert (Hnd : NoDup [x; y]).
  { constructor; [intros [<-|[]]; contradiction | constructor; [intros []|constructor]]. }
  specialize (HR [x; y] Hnd ltac:(discriminate)); simpl in HR; lia.
Qed.

Lemma rao_triple : forall r (G : Family) x y z,
    RaoSpread 3 G r -> x <> y -> x <> z -> y <> z -> deg [x; y; z] G <= 1.
Proof.
  intros r G x y z HR Hxy Hxz Hyz.
  assert (Hnd : NoDup [x; y; z]).
  { constructor; [intros [<-|[<-|[]]]; contradiction|].
    constructor; [intros [<-|[]]; contradiction|].
    constructor; [intros []|constructor]. }
  specialize (HR [x; y; z] Hnd ltac:(discriminate)); simpl in HR.
  exact HR.
Qed.

(** ** The pieces

    [Gp] is the part missing [q]; every member of it contains [p]
    because [{p,q}] covers. *)

Section TwoCover.

Variable r : nat.
Variable G : Family.
Variable p q : nat.

Hypothesis HU : Uniform 3 G.
Hypothesis HR : RaoSpread 3 G r.
Hypothesis Hint : forall C D, In C G -> In D G -> exists x, In x C /\ In x D.
Hypothesis Hcov : forall C, In C G -> In p C \/ In q C.
Hypothesis Hpq : p <> q.

Let Gp := filter (fun C => negb (memb q C)) G.
Let Gqq := filter (fun C => memb q C) G.
Let Gq := filter (fun C => negb (memb p C)) Gqq.
Let Gpq := filter (fun C => memb p C) Gqq.

Lemma in_Gp : forall C, In C Gp -> In C G /\ In p C /\ ~ In q C.
Proof.
  intros C HC; unfold Gp in HC; apply filter_In in HC as [HCG Hne].
  apply Bool.negb_true_iff in Hne.
  assert (Hq : ~ In q C) by (intros Hin; apply memb_true_iff in Hin; congruence).
  destruct (Hcov C HCG) as [Hp | Hq']; [tauto | contradiction].
Qed.

Lemma in_Gq : forall C, In C Gq -> In C G /\ In q C /\ ~ In p C.
Proof.
  intros C HC; unfold Gq in HC; apply filter_In in HC as [HCq Hne].
  unfold Gqq in HCq; apply filter_In in HCq as [HCG Hq].
  apply Bool.negb_true_iff in Hne.
  split; [exact HCG | split].
  - apply memb_true_iff; exact Hq.
  - intros Hin; apply memb_true_iff in Hin; congruence.
Qed.

Lemma in_Gpq : forall C, In C Gpq -> In C G /\ In p C /\ In q C.
Proof.
  intros C HC; unfold Gpq in HC; apply filter_In in HC as [HCq Hp].
  unfold Gqq in HCq; apply filter_In in HCq as [HCG Hq].
  split; [exact HCG | split; apply memb_true_iff; assumption].
Qed.

Lemma deg_Gp_le : forall T, deg T Gp <= deg T G.
Proof. intros T; unfold Gp; apply deg_filter_le. Qed.

Lemma deg_Gq_le : forall T, deg T Gq <= deg T G.
Proof.
  intros T; unfold Gq, Gqq.
  eapply Nat.le_trans; [apply deg_filter_le | apply deg_filter_le].
Qed.

Lemma deg_Gpq_le : forall T, deg T Gpq <= deg T G.
Proof.
  intros T; unfold Gpq, Gqq.
  eapply Nat.le_trans; [apply deg_filter_le | apply deg_filter_le].
Qed.

(** The three pieces partition [G]. *)

Lemma pieces_partition :
  length G = length Gpq + length Gq + length Gp.
Proof.
  unfold Gp, Gq, Gpq, Gqq.
  pose proof (length_filter_partition (fun C => memb q C) G) as H1.
  pose proof (length_filter_partition (fun C => memb p C)
                (filter (fun C => memb q C) G)) as H2.
  lia.
Qed.

(** The piece through both points is capped by the pair degree. *)

Lemma Gpq_bound : length Gpq <= r.
Proof.
  assert (H : length Gpq <= length [[p; q]] * r).
  { apply cover_by_sets.
    - intros C HC; destruct (in_Gpq C HC) as [_ [Hp Hq]].
      exists [p; q]; split; [left; reflexivity|].
      intros z [<-|[<-|[]]]; assumption.
    - intros T [<-|[]].
      eapply Nat.le_trans; [apply deg_Gpq_le | apply (rao_pair HR Hpq)]. }
  simpl in H; lia.
Qed.

(** ** Each side bounds the other by [2r]

    A member of [Gq] misses [p], so it meets a member of [Gp] in one of
    its two points other than [q]. *)

Lemma cross_bound_Gp : Gq <> [] -> length Gp <= 2 * r.
Proof.
  intros Hne.
  destruct Gq as [|C' Gq'] eqn:EGq; [contradiction|].
  assert (HC' : In C' Gq) by (rewrite EGq; left; reflexivity).
  destruct (in_Gq C' HC') as [HC'G [HC'q HC'p]].
  destruct (@uniform_mem 3 G C' HU HC'G) as [Hlen Hnd].
  destruct (@three_uniform_split C' q Hlen Hnd HC'q) as [a [b [Hab [Hqa [Hqb [HaC [HbC Hall]]]]]]].
  assert (Hpa : p <> a) by (intros <-; contradiction).
  assert (Hpb : p <> b) by (intros <-; contradiction).
  assert (H : length Gp <= length [[p; a]; [p; b]] * r).
  { apply cover_by_sets.
    - intros C HC; destruct (in_Gp C HC) as [HCG [HCp HCq]].
      destruct (Hint C C' HCG HC'G) as [x [HxC HxC']].
      destruct (Hall x HxC') as [<- | [<- | <-]]; [contradiction| |].
      + exists [p; x]; split; [left; reflexivity|].
        intros z [<-|[<-|[]]]; assumption.
      + exists [p; x]; split; [right; left; reflexivity|].
        intros z [<-|[<-|[]]]; assumption.
    - intros T [<-|[<-|[]]];
        (eapply Nat.le_trans; [apply deg_Gp_le | apply (rao_pair HR); assumption]). }
  simpl in H; lia.
Qed.

Lemma cross_bound_Gq : Gp <> [] -> length Gq <= 2 * r.
Proof.
  intros Hne.
  destruct Gp as [|C' Gp'] eqn:EGp; [contradiction|].
  assert (HC' : In C' Gp) by (rewrite EGp; left; reflexivity).
  destruct (in_Gp C' HC') as [HC'G [HC'p HC'q]].
  destruct (@uniform_mem 3 G C' HU HC'G) as [Hlen Hnd].
  destruct (@three_uniform_split C' p Hlen Hnd HC'p) as [a [b [Hab [Hpa [Hpb [HaC [HbC Hall]]]]]]].
  assert (Hqa : q <> a) by (intros <-; contradiction).
  assert (Hqb : q <> b) by (intros <-; contradiction).
  assert (H : length Gq <= length [[q; a]; [q; b]] * r).
  { apply cover_by_sets.
    - intros C HC; destruct (in_Gq C HC) as [HCG [HCq HCp]].
      destruct (Hint C C' HCG HC'G) as [x [HxC HxC']].
      destruct (Hall x HxC') as [<- | [<- | <-]]; [contradiction| |].
      + exists [q; x]; split; [left; reflexivity|].
        intros z [<-|[<-|[]]]; assumption.
      + exists [q; x]; split; [right; left; reflexivity|].
        intros z [<-|[<-|[]]]; assumption.
    - intros T [<-|[<-|[]]];
        (eapply Nat.le_trans; [apply deg_Gq_le | apply (rao_pair HR); assumption]). }
  simpl in H; lia.
Qed.

(** ** A common point caps [Gp] at [r] *)

Lemma common_point_bound :
  forall w, p <> w -> (forall C, In C Gp -> In w C) -> length Gp <= r.
Proof.
  intros w Hpw Hall.
  assert (H : length Gp <= length [[p; w]] * r).
  { apply cover_by_sets.
    - intros C HC; destruct (in_Gp C HC) as [_ [HCp _]].
      exists [p; w]; split; [left; reflexivity|].
      intros z [<-|[<-|[]]]; [exact HCp | apply Hall; exact HC].
    - intros T [<-|[]].
      eapply Nat.le_trans; [apply deg_Gp_le | apply (rao_pair HR Hpw)]. }
  simpl in H; lia.
Qed.

(** ** No common point caps [Gq] at four

    This is the branch that makes the bound sharp, and the point of it is
    that it needs no classification of graphs with matching number one.
    Naming a member that misses [u] and one that misses [v] is enough:
    every member of [Gq] is then pinned to one of four *triples*, and a
    triple has degree at most one. *)

Lemma no_common_point_bound :
  forall C1 C2 C3 u v,
    In C1 Gp -> In C2 Gp -> In C3 Gp ->
    In u C1 -> In v C1 -> u <> v -> p <> u -> p <> v ->
    (forall y, In y C1 -> y = p \/ y = u \/ y = v) ->
    ~ In u C2 -> ~ In v C3 ->
    length Gq <= 4.
Proof.
  intros C1 C2 C3 u v HC1 HC2 HC3 HuC1 HvC1 Huv Hpu Hpv Hall1 Hu2 Hv3.
  destruct (in_Gp C1 HC1) as [HC1G [HC1p HC1q]].
  destruct (in_Gp C2 HC2) as [HC2G [HC2p HC2q]].
  destruct (in_Gp C3 HC3) as [HC3G [HC3p HC3q]].
  destruct (@uniform_mem 3 G C2 HU HC2G) as [Hlen2 Hnd2].
  destruct (@uniform_mem 3 G C3 HU HC3G) as [Hlen3 Hnd3].
  destruct (@three_uniform_split C2 p Hlen2 Hnd2 HC2p)
    as [a2 [b2 [Ha2b2 [Hpa2 [Hpb2 [Ha2C [Hb2C Hall2]]]]]]].
  destruct (@three_uniform_split C3 p Hlen3 Hnd3 HC3p)
    as [a3 [b3 [Ha3b3 [Hpa3 [Hpb3 [Ha3C [Hb3C Hall3]]]]]]].
  (* the four triples *)
  assert (Hqu : q <> u) by (intros <-; contradiction).
  assert (Hqv : q <> v) by (intros <-; contradiction).
  assert (Hqa2 : q <> a2) by (intros <-; contradiction).
  assert (Hqb2 : q <> b2) by (intros <-; contradiction).
  assert (Hqa3 : q <> a3) by (intros <-; contradiction).
  assert (Hqb3 : q <> b3) by (intros <-; contradiction).
  assert (Hua2 : u <> a2) by (intros <-; contradiction).
  assert (Hub2 : u <> b2) by (intros <-; contradiction).
  assert (Hva3 : v <> a3) by (intros <-; contradiction).
  assert (Hvb3 : v <> b3) by (intros <-; contradiction).
  assert (H : length Gq
              <= length [[q; u; a2]; [q; u; b2]; [q; v; a3]; [q; v; b3]] * 1).
  { apply cover_by_sets.
    - intros C HC; destruct (in_Gq C HC) as [HCG [HCq HCp]].
      (* C meets C1 away from p, so it holds u or v *)
      destruct (Hint C C1 HCG HC1G) as [x [HxC HxC1]].
      destruct (Hall1 x HxC1) as [<- | [<- | <-]]; [contradiction| |].
      + (* x = u: C must still meet C2, which has neither p nor u *)
        destruct (Hint C C2 HCG HC2G) as [y [HyC HyC2]].
        destruct (Hall2 y HyC2) as [<- | [<- | <-]]; [contradiction | | ].
        * exists [q; x; y]; split; [left; reflexivity|].
          intros z [<-|[<-|[<-|[]]]]; assumption.
        * exists [q; x; y]; split; [right; left; reflexivity|].
          intros z [<-|[<-|[<-|[]]]]; assumption.
      + (* x = v: C must still meet C3, which has neither p nor v *)
        destruct (Hint C C3 HCG HC3G) as [y [HyC HyC3]].
        destruct (Hall3 y HyC3) as [<- | [<- | <-]]; [contradiction | | ].
        * exists [q; x; y]; split; [right; right; left; reflexivity|].
          intros z [<-|[<-|[<-|[]]]]; assumption.
        * exists [q; x; y]; split; [right; right; right; left; reflexivity|].
          intros z [<-|[<-|[<-|[]]]]; assumption.
    - intros T [<-|[<-|[<-|[<-|[]]]]];
        (eapply Nat.le_trans;
         [apply deg_Gq_le | eapply rao_triple; eauto]). }
  simpl in H; lia.
Qed.

(** ** The two-point cover bound

    [tau(G) = 2] is exactly "[{p,q}] covers and neither point covers
    alone", which is [Gp <> []] and [Gq <> []]. Then

<<
      |G|  <=  max(4r, 3r + 4),
>>

    and at [r = 4] both branches are 16 — the value §24.9 measures and
    the value that would give [r*(3,3) <= 4]. *)

Lemma member_of_nonempty : forall (L : Family), L <> [] -> exists C, In C L.
Proof. intros [|C t] H; [contradiction | exists C; left; reflexivity]. Qed.

Theorem two_cover_bound :
  Gp <> [] -> Gq <> [] ->
  length G <= Nat.max (4 * r) (3 * r + 4).
Proof.
  intros HGp HGq.
  pose proof pieces_partition as Hpart.
  pose proof Gpq_bound as Hboth.
  destruct (member_of_nonempty HGp) as [C1 HC1].
  destruct (in_Gp C1 HC1) as [HC1G [HC1p HC1q]].
  destruct (@uniform_mem 3 G C1 HU HC1G) as [Hlen1 Hnd1].
  destruct (@three_uniform_split C1 p Hlen1 Hnd1 HC1p)
    as [u [v [Huv [Hpu [Hpv [HuC1 [HvC1 Hall1]]]]]]].
  destruct (existsb (fun C => negb (memb u C)) Gp) eqn:Eu.
  - apply existsb_exists in Eu as [C2 [HC2 Hu2b]].
    apply Bool.negb_true_iff in Hu2b.
    assert (Hu2 : ~ In u C2)
      by (intros Hin; apply memb_true_iff in Hin; congruence).
    destruct (existsb (fun C => negb (memb v C)) Gp) eqn:Ev.
    + (* no point besides p is common to all of Gp: Gq has at most four *)
      apply existsb_exists in Ev as [C3 [HC3 Hv3b]].
      apply Bool.negb_true_iff in Hv3b.
      assert (Hv3 : ~ In v C3)
        by (intros Hin; apply memb_true_iff in Hin; congruence).
      pose proof (@no_common_point_bound C1 C2 C3 u v HC1 HC2 HC3
                    HuC1 HvC1 Huv Hpu Hpv Hall1 Hu2 Hv3) as Hq4.
      pose proof (cross_bound_Gp HGq) as Hp2r.
      lia.
    + (* v lies in every member of Gp *)
      assert (Hallv : forall C, In C Gp -> In v C).
      { intros C HC.
        pose proof (existsb_false_forall _ _ _ Ev C HC) as E.
        apply Bool.negb_false_iff in E; apply memb_true_iff; exact E. }
      pose proof (@common_point_bound v Hpv Hallv) as Hpr.
      pose proof (cross_bound_Gq HGp) as Hq2r.
      lia.
  - (* u lies in every member of Gp *)
    assert (Hallu : forall C, In C Gp -> In u C).
    { intros C HC.
      pose proof (existsb_false_forall _ _ _ Eu C HC) as E.
      apply Bool.negb_false_iff in E; apply memb_true_iff; exact E. }
    pose proof (@common_point_bound u Hpu Hallu) as Hpr.
    pose proof (cross_bound_Gq HGp) as Hq2r.
    lia.
Qed.

End TwoCover.

(** ** The cases, stated without the filters

    [tau(G) <= 2] says some pair of points covers [G]. Splitting on
    whether one of them does it alone: *)

Theorem one_cover_bound :
  forall r (G : Family) w,
    RaoSpread 3 G r ->
    (forall C, In C G -> In w C) ->
    length G <= r * r.
Proof.
  intros r G w HR Hall.
  assert (H : length G <= length [[w]] * (r ^ (3 - 1))).
  { apply cover_by_sets.
    - intros C HC; exists [w]; split; [left; reflexivity|].
      intros z [<-|[]]; apply Hall; exact HC.
    - intros T [<-|[]]; eapply rao_point; exact HR. }
  simpl in H; nia.
Qed.

Theorem two_cover_bound_members :
  forall r (G : Family) p q,
    Uniform 3 G -> RaoSpread 3 G r ->
    (forall C D, In C G -> In D G -> exists x, In x C /\ In x D) ->
    (forall C, In C G -> In p C \/ In q C) ->
    p <> q ->
    (exists C, In C G /\ ~ In q C) ->
    (exists C, In C G /\ ~ In p C) ->
    length G <= Nat.max (4 * r) (3 * r + 4).
Proof.
  intros r G p q HU HR Hint Hcov Hpq [C1 [HC1G HC1q]] [C2 [HC2G HC2p]].
  apply (@two_cover_bound r G p q HU HR Hint Hcov Hpq).
  - intros E.
    assert (Hin : In C1 (filter (fun C => negb (memb q C)) G)).
    { apply filter_In; split; [exact HC1G|].
      apply Bool.negb_true_iff.
      destruct (memb q C1) eqn:Em; [exfalso; apply HC1q, memb_true_iff; exact Em
                                   | reflexivity]. }
    rewrite E in Hin; exact Hin.
  - intros E.
    assert (HC2q : In q C2)
      by (destruct (Hcov C2 HC2G) as [H|H]; [contradiction | exact H]).
    assert (Hin : In C2 (filter (fun C => negb (memb p C))
                           (filter (fun C => memb q C) G))).
    { apply filter_In; split.
      - apply filter_In; split; [exact HC2G | apply memb_true_iff; exact HC2q].
      - apply Bool.negb_true_iff.
        destruct (memb p C2) eqn:Em; [exfalso; apply HC2p, memb_true_iff; exact Em
                                     | reflexivity]. }
    rewrite E in Hin; exact Hin.
Qed.

(** ** The value that matters

    At [r = 4] every branch is 16, which is exactly [r^(m-1)] — the star
    — and exactly the value §24.9 measures for [I(3,4)] by exhaustive
    search to nine points. So the [tau <= 2] half of "the star is
    extremal at [(3,4)]" is now a theorem rather than a measurement.

    What that would buy if the remaining case followed: [I(3,4) <= 16]
    gives [3*16 + 16 = 64 = 4^3], hence [r*(3,3) <= 4]. The missing case
    is [tau = 3], where the elementary greedy bound is [3^3 = 27] and
    Frankl's theorem gives 10. Neither is here. *)

Corollary two_cover_bound_at_four :
  forall (G : Family) p q,
    Uniform 3 G -> RaoSpread 3 G 4 ->
    (forall C D, In C G -> In D G -> exists x, In x C /\ In x D) ->
    (forall C, In C G -> In p C \/ In q C) ->
    p <> q ->
    (exists C, In C G /\ ~ In q C) ->
    (exists C, In C G /\ ~ In p C) ->
    length G <= 16.
Proof.
  intros G p q HU HR Hint Hcov Hpq H1 H2.
  pose proof (@two_cover_bound_members 4 G p q HU HR Hint Hcov Hpq H1 H2) as H.
  simpl in H; lia.
Qed.

Corollary one_cover_bound_at_four :
  forall (G : Family) w,
    RaoSpread 3 G 4 ->
    (forall C, In C G -> In w C) ->
    length G <= 16.
Proof. intros G w HR Hall; exact (@one_cover_bound 4 G w HR Hall). Qed.

(** ** The general form: for [r >= 4] the star is extremal among the
       two-covered families

    [max(4r, 3r+4) <= r^2] exactly when [r >= 4] — both branches meet
    [r^2] at [r = 4] and fall behind it after — so the two cases collapse
    into one statement with no maximum in it:

<<
      tau(G) <= 2  and  r >= 4   =>   |G| <= r^(3-1),
>>

    which is the size of a star, and a star is achievable. So among
    3-uniform intersecting Rao-spread families with a two-point cover,
    **the star is extremal for every [r >= 4]** — and [r = 4] is sharp
    for the statement, since at [r = 3] the bound is 13 while [r^2] is 9
    and the true maximum is 10 (§24.9's measurement, `C([5],3)`, which
    has [tau = 3] and so is not covered by this theorem — it is the case
    that is missing). *)

Theorem two_cover_star_extremal :
  forall r (G : Family) p q,
    4 <= r ->
    Uniform 3 G -> RaoSpread 3 G r ->
    (forall C D, In C G -> In D G -> exists x, In x C /\ In x D) ->
    (forall C, In C G -> In p C \/ In q C) ->
    p <> q ->
    (exists C, In C G /\ ~ In q C) ->
    (exists C, In C G /\ ~ In p C) ->
    length G <= r * r.
Proof.
  intros r G p q Hr HU HR Hint Hcov Hpq H1 H2.
  pose proof (@two_cover_bound_members r G p q HU HR Hint Hcov Hpq H1 H2) as H.
  assert (Hmax : Nat.max (4 * r) (3 * r + 4) <= r * r).
  { apply Nat.max_lub; nia. }
  lia.
Qed.

(** Both covering-number cases below three, in one statement: a
    3-uniform intersecting Rao-spread family covered by two points has at
    most as many members as a star, once [r >= 4]. The [tau = 3] case is
    not here. *)

Corollary covered_by_two_at_most_star :
  forall r (G : Family) p q,
    4 <= r ->
    Uniform 3 G -> RaoSpread 3 G r ->
    (forall C D, In C G -> In D G -> exists x, In x C /\ In x D) ->
    (forall C, In C G -> In p C \/ In q C) ->
    p <> q ->
    length G <= r * r.
Proof.
  intros r G p q Hr HU HR Hint Hcov Hpq.
  (* Either one of the two points covers on its own -- a star -- or
     neither does, which is the two-cover case proper. *)
  destruct (existsb (fun C => negb (memb q C)) G) eqn:Eq.
  - destruct (existsb (fun C => negb (memb p C)) G) eqn:Ep.
    + apply existsb_exists in Eq as [C1 [HC1G Hb1]].
      apply existsb_exists in Ep as [C2 [HC2G Hb2]].
      apply Bool.negb_true_iff in Hb1; apply Bool.negb_true_iff in Hb2.
      apply (@two_cover_star_extremal r G p q Hr HU HR Hint Hcov Hpq).
      * exists C1; split;
          [exact HC1G | intros Hin; apply memb_true_iff in Hin; congruence].
      * exists C2; split;
          [exact HC2G | intros Hin; apply memb_true_iff in Hin; congruence].
    + (* p lies in every member: a star at p *)
      apply (@one_cover_bound r G p HR).
      intros C HC.
      pose proof (existsb_false_forall _ _ _ Ep C HC) as E.
      apply Bool.negb_false_iff in E; apply memb_true_iff; exact E.
  - (* q lies in every member: a star at q *)
    apply (@one_cover_bound r G q HR).
    intros C HC.
    pose proof (existsb_false_forall _ _ _ Eq C HC) as E.
    apply Bool.negb_false_iff in E; apply memb_true_iff; exact E.
Qed.

(** * The third case, and what it closes

    §24.9's target is [I(3,4) <= 16], where [I(m,r)] is the largest
    [m]-uniform intersecting family satisfying Rao's condition. The
    covering number of a 3-uniform intersecting family is at most 3, and
    [tau <= 2] is [covered_by_two_at_most_star] above. What remains is
    [tau = 3], and that is Frankl's theorem — a classical result this
    development does not have.

    It is taken here as an explicit **hypothesis**, not an axiom: the
    repository has exactly one axiom ([Sunflower.ALWZ.Rao20_lemma2]) and
    is not gaining a second. Everything below is an implication with
    [FranklTauThree] to the left of the arrow, so [make axiom-audit] is
    unchanged and [Print Assumptions] on every name here still reports
    "closed under the global context".

    **Only 16 is needed, not 10.** The split bound reads
    [|F| <= 3*r^2 + I(3,r)], and at [r = 4] that is [48 + I <= 64] exactly
    when [I <= 16]. Frankl's bound of 10 is comfortably stronger than
    required; the elementary greedy bound for [tau = 3] is [3^3 = 27],
    which is not. So the gap this hypothesis fills is the interval
    [[16, 27]], and any bound of 16 or better closes it. *)

Definition FranklTauThree : Prop :=
  forall (G : Family),
    Uniform 3 G ->
    (forall C D, In C G -> In D G -> exists x, In x C /\ In x D) ->
    (* covering number at least 3: no two points meet every member *)
    (forall p q, exists C, In C G /\ ~ In p C /\ ~ In q C) ->
    length G <= 10.

(** [TauThreeAtMost K] is the same statement with the constant left
    open. Frankl gives [K = 10]; everything below needs only [K = 16], so
    that is the hypothesis the theorems actually take. *)

Definition TauThreeAtMost (K : nat) : Prop :=
  forall (G : Family),
    Uniform 3 G ->
    (forall C D, In C G -> In D G -> exists x, In x C /\ In x D) ->
    (forall p q, exists C, In C G /\ ~ In p C /\ ~ In q C) ->
    length G <= K.

Lemma frankl_is_stronger_than_needed : FranklTauThree -> TauThreeAtMost 16.
Proof. intros HF G HU Hint Htau; pose proof (HF G HU Hint Htau); lia. Qed.

(** ** The covering-number case split

    Deciding "some two points cover [G]" is a finite search, because a
    cover point that lies in no member is useless: the candidates can be
    taken from [concat G]. *)

Lemma covers_dec_search :
  forall (G : Family) p q,
    existsb (fun a => existsb
       (fun b => forallb (fun C => orb (memb a C) (memb b C)) G) (concat G))
       (concat G) = false ->
    G <> [] ->
    exists C, In C G /\ ~ In p C /\ ~ In q C.
Proof.
  intros G p q Hsearch HGne.
  (* a point in no member constrains nothing *)
  assert (Hmiss : forall a, ~ In a (concat G) -> forall C, In C G -> ~ In a C).
  { intros a Ha C HC Hin.
    apply Ha, (proj2 (in_concat G a)); exists C; split; assumption. }
  (* for points that do occur, the failed search hands back a witness *)
  assert (Hpair : forall a b, In a (concat G) -> In b (concat G) ->
                    exists C, In C G /\ ~ In a C /\ ~ In b C).
  { intros a b Ha Hb.
    pose proof (existsb_false_forall _ _ _ Hsearch a Ha) as E1.
    pose proof (existsb_false_forall _ _ _ E1 b Hb) as E2.
    destruct (existsb (fun C => negb (orb (memb a C) (memb b C))) G) eqn:Ex.
    - apply existsb_exists in Ex as [C [HC Hneg]].
      apply Bool.negb_true_iff, Bool.orb_false_iff in Hneg as [Ea Eb].
      exists C; repeat split;
        [exact HC | intros Hin; apply memb_true_iff in Hin; congruence
         | intros Hin; apply memb_true_iff in Hin; congruence].
    - exfalso.
      assert (Hall : forallb (fun C => orb (memb a C) (memb b C)) G = true).
      { apply forallb_forall; intros C HC.
        pose proof (existsb_false_forall _ _ _ Ex C HC) as E.
        apply Bool.negb_false_iff in E; exact E. }
      congruence. }
  destruct (in_dec Nat.eq_dec p (concat G)) as [Hp|Hp];
    destruct (in_dec Nat.eq_dec q (concat G)) as [Hq|Hq].
  - exact (Hpair p q Hp Hq).
  - destruct (Hpair p p Hp Hp) as [C [HC [Hnp _]]].
    exists C; repeat split; [exact HC | exact Hnp | apply (Hmiss q Hq C HC)].
  - destruct (Hpair q q Hq Hq) as [C [HC [Hnq _]]].
    exists C; repeat split; [exact HC | apply (Hmiss p Hp C HC) | exact Hnq].
  - destruct G as [|M G0]; [contradiction|].
    exists M; repeat split; [left; reflexivity | | ].
    + apply (Hmiss p Hp M (or_introl eq_refl)).
    + apply (Hmiss q Hq M (or_introl eq_refl)).
Qed.

(** ** [I(3,r) <= r^2] for [r >= 4], given Frankl

    The star is extremal among *all* 3-uniform intersecting Rao-spread
    families once [r >= 4] — the [tau <= 2] half proved above, the
    [tau = 3] half assumed. *)

Theorem intersecting_at_most_star :
  forall K, TauThreeAtMost K ->
  forall r (G : Family),
    K <= r * r -> 4 <= r ->
    Uniform 3 G -> RaoSpread 3 G r ->
    (forall C D, In C G -> In D G -> exists x, In x C /\ In x D) ->
    length G <= r * r.
Proof.
  intros K HF r G HKr Hr HU HR Hint.
  destruct (existsb (fun a => existsb
     (fun b => forallb (fun C => orb (memb a C) (memb b C)) G) (concat G)) (concat G))
    eqn:Esearch.
  - (* two points cover: the case proved above *)
    apply existsb_exists in Esearch as [a [Ha Hb']].
    apply existsb_exists in Hb' as [b [Hb Hall]].
    assert (Hcov : forall C, In C G -> In a C \/ In b C).
    { intros C HC.
      pose proof (proj1 (forallb_forall _ G) Hall C HC) as E.
      apply Bool.orb_true_iff in E as [E|E];
        [left | right]; apply memb_true_iff; exact E. }
    destruct (Nat.eq_dec a b) as [<-|Hab].
    + (* one point covers: a star *)
      apply (@one_cover_bound r G a HR).
      intros C HC; destruct (Hcov C HC); assumption.
    + exact (@covered_by_two_at_most_star r G a b Hr HU HR Hint Hcov Hab).
  - (* no two points cover: Frankl's case *)
    destruct G as [|M G0] eqn:EG; [simpl; lia | rewrite <- EG in *].
    assert (HGne : G <> []) by (rewrite EG; discriminate).
    assert (Htau : forall p q, exists C, In C G /\ ~ In p C /\ ~ In q C)
      by (intros p q; exact (@covers_dec_search G p q Esearch HGne)).
    eapply Nat.le_trans; [exact (HF G HU Hint Htau) | exact HKr].
Qed.

(** ** The split, with the piece bound supplied

    [SpreadThreshold.split_no_three_disjoint_bound] uses
    [intersecting_piece_bound] for the part missing [A]. Parameterising
    that part is what lets a *measured* or *assumed* bound be plugged in,
    and at [(3,4)] it is the difference between 32 and 16 — which is the
    difference between not closing and closing. *)

Theorem split_with_piece :
  forall r (F : Family) (K : nat),
    Uniform 3 F -> RaoSpread 3 F r ->
    NoKDisjoint 3 F ->
    (forall H, Uniform 3 H -> RaoSpread 3 H r ->
       (forall C D, In C H -> In D H -> exists x, In x C /\ In x D) ->
       length H <= K) ->
    length F <= 3 * (r * r) + K.
Proof.
  intros r F K HU HR Hno Hpiece.
  assert (Hne : forall A, In A F -> A <> []).
  { intros A HA; destruct (@uniform_mem 3 F A HU HA) as [Hlen _].
    destruct A as [|a A']; [simpl in Hlen; lia | discriminate]. }
  destruct (existsb (fun A => existsb (fun B => disjointb A B) F) F) eqn:Hex.
  - apply existsb_exists in Hex as [A [HA HB']].
    apply existsb_exists in HB' as [B [HB HABb]].
    apply disjointb_correct in HABb.
    destruct (@uniform_mem 3 F A HU HA) as [HAlen HAnd].
    set (f := fun C : list nat => disjointb C A).
    assert (Hsplit : length F = length (filter f F)
                                + length (filter (fun C => negb (f C)) F))
      by apply length_filter_partition.
    (* the part meeting A: covered by the three points of A *)
    assert (HM : length (filter (fun C => negb (f C)) F) <= 3 * (r * r)).
    { assert (HMA : length (filter (fun C => negb (f C)) F)
                    <= length A * (r ^ (3 - 1))).
      { apply cover_by_points.
        - intros C HC; apply filter_In in HC as [_ HCf].
          apply Bool.negb_true_iff in HCf; unfold f in HCf.
          apply meets_of_not_disjointb; exact HCf.
        - intros x _.
          eapply Nat.le_trans; [apply deg_filter_le | eapply rao_point; exact HR]. }
      rewrite HAlen in HMA; simpl in HMA; nia. }
    (* the part missing A: intersecting, so the supplied bound applies *)
    assert (HP : length (filter f F) <= K).
    { apply Hpiece.
      - apply uniform_filter; exact HU.
      - intros T HT HTn.
        eapply Nat.le_trans; [apply deg_filter_le | apply HR; assumption].
      - intros C D HC HD.
        apply filter_In in HC as [HCF HCf]; apply filter_In in HD as [HDF HDf].
        unfold f in HCf, HDf.
        apply disjointb_correct in HCf; apply disjointb_correct in HDf.
        destruct (disjointb C D) eqn:ECD.
        + exfalso; apply disjointb_correct in ECD.
          exact (@miss_member_intersecting 3 F A C D ltac:(lia) HU Hno
                   HA HCF HDF HCf HDf ECD).
        + apply disjointb_false_iff in ECD as [x [HxC HxD]].
          exists x; split; assumption. }
    lia.
  - (* F is intersecting: it is its own piece *)
    assert (Hint : forall C D, In C F -> In D F -> exists x, In x C /\ In x D).
    { intros C D HC HD.
      destruct (disjointb C D) eqn:ECD.
      - exfalso.
        assert (Hcontra : existsb
                  (fun A => existsb (fun B => disjointb A B) F) F = true).
        { apply existsb_exists; exists C; split; [exact HC|].
          apply existsb_exists; exists D; split; [exact HD | exact ECD]. }
        congruence.
      - apply disjointb_false_iff in ECD as [x [HxC HxD]].
        exists x; split; assumption. }
    pose proof (Hpiece F HU HR Hint); lia.
Qed.

(** ** The first open term of the sequence, conditionally

    [docs/roadmap.md] §22.2 records [r*(3,3)] in [[3,6]]; §24.2 narrowed
    it to [[3,5]] unconditionally. This closes it to [[3,4]] on Frankl's
    theorem alone.

    The arithmetic is exact and has no slack:

<<
      |F|  <=  3 * r^2   +   I(3,r)          (split_with_piece)
           <=  3 * 16    +   16      =  64   =  4^3      at r = 4.
>>

    So [4^3 < |F|] is impossible, which is [SpreadYieldsDisjoint 3 3 4].
    The two smaller uniformities come from the cover bound directly:
    at [m = 1] it gives 2 against [4], and at [m = 2] it gives
    [2*2*4 = 16] against [4^2 = 16] — equality, so that row is as tight
    as this one. *)

Corollary intersecting_at_most_star_from_frankl :
  FranklTauThree ->
  forall r (G : Family),
    4 <= r ->
    Uniform 3 G -> RaoSpread 3 G r ->
    (forall C D, In C G -> In D G -> exists x, In x C /\ In x D) ->
    length G <= r * r.
Proof.
  intros HF r G Hr HU HR Hint.
  apply (@intersecting_at_most_star 10 (fun G' a b c => HF G' a b c) r G);
    [nia | exact Hr | exact HU | exact HR | exact Hint].
Qed.

Theorem r_star_three_three_at_most_four :
  TauThreeAtMost 16 -> SpreadYieldsDisjoint 3 3 4.
Proof.
  intros HK m F Hm Hmn HU HD Hsize HR.
  destruct (@decide_three_disjoint m F ltac:(lia) HU) as [Hyes|Hno];
    [exact Hyes | exfalso].
  destruct m as [|[|[|[|m']]]]; try lia.
  - pose proof (@no_three_disjoint_cover_bound 1 4 F ltac:(lia) HU HR Hno) as Hb.
    simpl in Hb, Hsize; lia.
  - pose proof (@no_three_disjoint_cover_bound 2 4 F ltac:(lia) HU HR Hno) as Hb.
    simpl in Hb, Hsize; lia.
  - pose proof (@split_with_piece 4 F 16 HU HR Hno
                  (fun H HUh HRh Hinth =>
                     @intersecting_at_most_star 16 HK 4 H
                       ltac:(lia) ltac:(lia) HUh HRh Hinth)) as Hb.
    simpl in Hsize; lia.
Qed.

(** The sunflower number this yields, and where it stands: through
    [spread_reduction], [f(3,3) <= 4^3 + 1 = 65]. Erdős–Rado 1960 gives
    [3!*2^3 + 1 = 49] unconditionally, so this is still the worse bound
    on [f] — as §24.2 says, the content is the threshold, not the
    number. *)

Corollary f_three_three_from_frankl :
  TauThreeAtMost 16 -> UpperBound 3 3 65.
Proof.
  intros HK.
  replace 65 with (S (4 ^ 3)) by reflexivity.
  apply (@spread_reduction 3 3 4);
    [lia | lia | apply r_star_three_three_at_most_four; exact HK | lia].
Qed.

(** And the same on Frankl's theorem as classically stated. *)

Corollary r_star_three_three_at_most_four_from_frankl :
  FranklTauThree -> SpreadYieldsDisjoint 3 3 4.
Proof.
  intros HF; apply r_star_three_three_at_most_four,
    frankl_is_stronger_than_needed; exact HF.
Qed.

(** ** What is assumed, isolated

    [FranklTauThree] is the *only* thing between the development and
    [r*(3,3) <= 4]. It is a hypothesis, not an axiom: [make axiom-audit]
    is unchanged and every name in this file is closed under the global
    context. Two things worth recording about how much of it is used.

    - **Only 16 is needed, not 10.** [split_with_piece] at [r = 4] wants
      [I(3,4) <= 16], and [intersecting_at_most_star_from_frankl] would
      go through with any bound up to 16 in place of Frankl's 10.
      [frankl_is_stronger_than_needed] below is that statement.
    - **Only the [tau = 3] case is assumed.** [tau <= 2] is
      [covered_by_two_at_most_star], proved. So what is missing is one
      classical theorem about one covering number, and the interval it
      has to beat is [[16, 27]] — 27 being the elementary greedy bound
      that this development could prove but which is not enough. *)



(** * [I(m,r)] as an extremal problem in its own right

    Everything above is about [m = 3]. The quantity behind it is not:

<<
      I(m,r)  =  max |G|  over G m-uniform, distinct, *intersecting*,
                 with deg T <= r^(m - |T|) for every nonempty T.
>>

    §24.2's split reads [|F| <= m*r^(m-1) + I(m,r)], so
    [SpreadYieldsDisjoint m 3 r] follows as soon as

<<
      [dagger]     I(m,r)  <=  r^m - m*r^(m-1)  =  r^(m-1) * (r - m).
>>

    Two readings, and the first is a limitation of the method rather than
    of any bound on [I].

    - **[r = m] is a hard floor.** There the right side of [dagger] is
      zero while [I >= 1] always, since a one-member family is
      intersecting. So this split can never give [r*(m,3) <= m], whatever
      is proved about the piece. That is [split_cannot_reach_r_equals_m].
    - **At [r = m+1] the requirement is exactly "the star is
      extremal"**: the right side is [(m+1)^(m-1)], the size of a star
      under the point cap. Hence [star_extremal_gives_m_plus_one].

    That is an **implication, not an equivalence** — [r*(m,3) <= m+1]
    might hold for reasons this split cannot see. [m+1] is linear with
    constant 1, against the [phi*m = 1.618 m] of §24.2.

    ** The measured crossover

<<
      m = 2   r        2   3   4   5        star = r
              I(2,r)   3   3   4   5
      m = 3   r        3   4               star = r^2
              I(3,r)  10  16
>>

    Both crossovers land at exactly [r = m+1]: below it the star loses to
    a small design (the triangle at [m = 2], [C([5],3)] at [m = 3]), and
    from it on the star is extremal. The [m = 2] row is proved outright
    below; the [m = 3] row is exhaustive search
    (`the_intersecting_piece_bound_has_a_factor_of_two_of_slack`). *)

Theorem split_cannot_reach_r_equals_m :
  forall m, 1 <= m -> m * m ^ (m - 1) = m ^ m.
Proof.
  intros m Hm; destruct m as [|m']; [lia|].
  replace (S m' - 1) with m' by lia.
  reflexivity.
Qed.

(** The split at any uniformity, with the piece bound supplied.
    [split_with_piece] is the [m = 3] instance and is kept because that
    is what §24.12 uses. *)

Theorem split_with_piece_general :
  forall m r (F : Family) (K : nat),
    1 <= m ->
    Uniform m F -> RaoSpread m F r ->
    NoKDisjoint 3 F ->
    (forall H, Uniform m H -> RaoSpread m H r ->
       (forall C D, In C H -> In D H -> exists x, In x C /\ In x D) ->
       length H <= K) ->
    length F <= m * r ^ (m - 1) + K.
Proof.
  intros m r F K Hm HU HR Hno Hpiece.
  assert (Hne : forall A, In A F -> A <> []).
  { intros A HA; destruct (@uniform_mem m F A HU HA) as [Hlen _].
    destruct A as [|a A']; [simpl in Hlen; lia | discriminate]. }
  destruct (existsb (fun A => existsb (fun B => disjointb A B) F) F) eqn:Hex.
  - apply existsb_exists in Hex as [A [HA HB']].
    apply existsb_exists in HB' as [B [HB HABb]].
    apply disjointb_correct in HABb.
    destruct (@uniform_mem m F A HU HA) as [HAlen HAnd].
    set (f := fun C : list nat => disjointb C A).
    assert (Hsplit : length F = length (filter f F)
                                + length (filter (fun C => negb (f C)) F))
      by apply length_filter_partition.
    assert (HM : length (filter (fun C => negb (f C)) F) <= m * r ^ (m - 1)).
    { assert (HMA : length (filter (fun C => negb (f C)) F)
                    <= length A * (r ^ (m - 1))).
      { apply cover_by_points.
        - intros C HC; apply filter_In in HC as [_ HCf].
          apply Bool.negb_true_iff in HCf; unfold f in HCf.
          apply meets_of_not_disjointb; exact HCf.
        - intros x _.
          eapply Nat.le_trans; [apply deg_filter_le | eapply rao_point; exact HR]. }
      rewrite HAlen in HMA; exact HMA. }
    assert (HP : length (filter f F) <= K).
    { apply Hpiece.
      - apply uniform_filter; exact HU.
      - intros T HT HTn.
        eapply Nat.le_trans; [apply deg_filter_le | apply HR; assumption].
      - intros C D HC HD.
        apply filter_In in HC as [HCF HCf]; apply filter_In in HD as [HDF HDf].
        unfold f in HCf, HDf.
        apply disjointb_correct in HCf; apply disjointb_correct in HDf.
        destruct (disjointb C D) eqn:ECD.
        + exfalso; apply disjointb_correct in ECD.
          exact (@miss_member_intersecting m F A C D Hm HU Hno
                   HA HCF HDF HCf HDf ECD).
        + apply disjointb_false_iff in ECD as [x [HxC HxD]].
          exists x; split; assumption. }
    lia.
  - assert (Hint : forall C D, In C F -> In D F -> exists x, In x C /\ In x D).
    { intros C D HC HD.
      destruct (disjointb C D) eqn:ECD.
      - exfalso.
        assert (Hcontra : existsb
                  (fun A => existsb (fun B => disjointb A B) F) F = true).
        { apply existsb_exists; exists C; split; [exact HC|].
          apply existsb_exists; exists D; split; [exact HD | exact ECD]. }
        congruence.
      - apply disjointb_false_iff in ECD as [x [HxC HxD]].
        exists x; split; assumption. }
    pose proof (Hpiece F HU HR Hint); lia.
Qed.

(** ** "The star is extremal" gives [r*(m,3) <= m+1]

    [StarExtremalAt m r] is [I(m,r) <= r^(m-1)]: no intersecting
    [m]-uniform Rao-spread family beats a star. Assuming it at every
    uniformity up to [n], with [r = n+1], closes the whole row. *)

Definition StarExtremalAt (m r : nat) : Prop :=
  forall (H : Family),
    Uniform m H -> RaoSpread m H r ->
    (forall C D, In C H -> In D H -> exists x, In x C /\ In x D) ->
    length H <= r ^ (m - 1).

Theorem star_extremal_gives_m_plus_one :
  forall n, 1 <= n ->
    (forall m, 1 <= m -> m <= n -> StarExtremalAt m (n + 1)) ->
    SpreadYieldsDisjoint n 3 (n + 1).
Proof.
  intros n Hn HS m F Hm Hmn HU HD Hsize HR.
  destruct (@decide_three_disjoint m F ltac:(lia) HU) as [Hyes|Hno];
    [exact Hyes | exfalso].
  pose proof (@split_with_piece_general m (n + 1) F ((n + 1) ^ (m - 1))
                Hm HU HR Hno (HS m Hm Hmn)) as Hb.
  (* |F| <= (m+1) * (n+1)^(m-1) <= (n+1) * (n+1)^(m-1) = (n+1)^m *)
  assert (Hpow : (n + 1) ^ m = (n + 1) * (n + 1) ^ (m - 1)).
  { replace m with (S (m - 1)) at 1 by lia; reflexivity. }
  assert (Hmono : (m + 1) * (n + 1) ^ (m - 1)
                  <= (n + 1) * (n + 1) ^ (m - 1))
    by (apply Nat.mul_le_mono_r; lia).
  lia.
Qed.

(** At [n = 2] the hypothesis is a theorem — [two_uniform_star_extremal]
    below — and the conclusion is the known exact value [r*(2,3) = 3].
    So the route is verified and tight at the largest uniformity where
    [I] is known in closed form. *)

(** ** [I(2,r) <= max(r,3)], and the star is extremal from [r = 3]

    An intersecting 2-uniform family is a graph in which every two edges
    meet. The textbook fact is that such a graph is a star or a triangle;
    as in §24.10 that classification is not needed. Take [e1 = {a,b}]; if
    no vertex is in every edge, **name an edge [e3] that misses [a]**.
    Then [e3] meets [e1] at [b], and it meets any [e2 = {a,c}] at [c], so
    [e3 = {b,c}] — and every further edge must meet all three, which
    confines it to [{ab, ac, bc}].

    Four lines, and it gives [I(2,r) = max(r,3)] on the nose: the star
    at a point has [deg <= r] members, the triangle has 3, and nothing
    else occurs. So the crossover is at [r = 3 = m + 1]. *)

Lemma two_uniform_split :
  forall (C : list nat),
    length C = 2 -> NoDup C ->
    exists a b, a <> b /\ In a C /\ In b C /\
                (forall y, In y C -> y = a \/ y = b).
Proof.
  intros C Hlen Hnd.
  destruct C as [|c1 [|c2 [|c3 C']]]; simpl in Hlen; try discriminate.
  inversion Hnd as [|z1 l1 H1 _]; subst.
  exists c1, c2; repeat split.
  - intros <-; apply H1; left; reflexivity.
  - left; reflexivity.
  - right; left; reflexivity.
  - intros y [<-|[<-|[]]]; tauto.
Qed.

Lemma two_uniform_pair :
  forall (C : list nat) a c,
    length C = 2 -> NoDup C -> In a C -> In c C -> a <> c ->
    forall y, In y C -> y = a \/ y = c.
Proof.
  intros C a c Hlen Hnd Ha Hc Hac y Hy.
  destruct C as [|c1 [|c2 [|c3 C']]]; simpl in Hlen; try discriminate.
  simpl in Ha, Hc, Hy.
  destruct Ha as [<-|[<-|[]]]; destruct Hc as [<-|[<-|[]]];
    try contradiction; destruct Hy as [<-|[<-|[]]]; tauto.
Qed.

Theorem two_uniform_intersecting_bound :
  forall r (G : Family),
    Uniform 2 G -> RaoSpread 2 G r ->
    (forall C D, In C G -> In D G -> exists x, In x C /\ In x D) ->
    length G <= Nat.max r 3.
Proof.
  intros r G HU HR Hint.
  (* the pair degree is 1: a 2-set has degree at most r^0 in a distinct
     2-uniform family *)
  assert (Hpairdeg : forall T, NoDup T -> length T = 2 -> deg T G <= 1).
  { intros T Hnd Hlen.
    specialize (HR T Hnd ltac:(destruct T; [simpl in Hlen; lia | discriminate])).
    rewrite Hlen in HR; simpl in HR; exact HR. }
  (* a star at a point is capped by the point degree *)
  assert (Hstar : forall w, (forall C, In C G -> In w C) -> length G <= r).
  { intros w Hw.
    assert (H : length G <= length [[w]] * (r ^ (2 - 1))).
    { apply cover_by_sets.
      - intros C HC; exists [w]; split;
          [left; reflexivity | intros z [<-|[]]; apply Hw; exact HC].
      - intros T [<-|[]]; eapply rao_point; exact HR. }
    simpl in H; lia. }
  destruct G as [|e1 G0] eqn:EG; [simpl; lia | rewrite <- EG in *].
  assert (He1 : In e1 G) by (rewrite EG; left; reflexivity).
  destruct (@uniform_mem 2 G e1 HU He1) as [Hlen1 Hnd1].
  destruct (@two_uniform_split e1 Hlen1 Hnd1) as [a [b [Hab [HaE [HbE Hall1]]]]].
  destruct (existsb (fun C => negb (memb a C)) G) eqn:Ea; cycle 1.
  { (* a lies in every edge: a star at a *)
    assert (Halla : forall C, In C G -> In a C).
    { intros C HC.
      pose proof (existsb_false_forall _ _ _ Ea C HC) as E.
      apply Bool.negb_false_iff in E; apply memb_true_iff; exact E. }
    pose proof (Hstar a Halla); lia. }
  destruct (existsb (fun C => negb (memb b C)) G) eqn:Eb; cycle 1.
  { (* b lies in every edge: a star at b *)
    assert (Hallb : forall C, In C G -> In b C).
    { intros C HC.
      pose proof (existsb_false_forall _ _ _ Eb C HC) as E.
      apply Bool.negb_false_iff in E; apply memb_true_iff; exact E. }
    pose proof (Hstar b Hallb); lia. }
  (* neither point of e1 is universal: name an edge missing each *)
  apply existsb_exists in Ea as [e3 [He3 Hna]].
  apply existsb_exists in Eb as [e4 [He4 Hnb]].
  apply Bool.negb_true_iff in Hna; apply Bool.negb_true_iff in Hnb.
  assert (Ha3 : ~ In a e3)
    by (intros Hin; apply memb_true_iff in Hin; congruence).
  assert (Hb4 : ~ In b e4)
    by (intros Hin; apply memb_true_iff in Hin; congruence).
  destruct (@uniform_mem 2 G e3 HU He3) as [Hlen3 Hnd3].
  destruct (@uniform_mem 2 G e4 HU He4) as [Hlen4 Hnd4].
  (* e3 misses a, so it meets e1 at b *)
  assert (Hb3 : In b e3).
  { destruct (Hint e3 e1 He3 He1) as [x [Hx3 Hx1]].
    destruct (Hall1 x Hx1) as [<-|<-]; [contradiction | exact Hx3]. }
  (* call the other point of e3 c *)
  destruct (@two_uniform_split e3 Hlen3 Hnd3) as [u [v [Huv [HuE [HvE Hall3]]]]].
  assert (Hc : exists c, c <> b /\ c <> a /\ In c e3 /\
                         (forall y, In y e3 -> y = b \/ y = c)).
  { destruct (Hall3 b Hb3) as [<-|<-].
    - exists v; repeat split;
        [ intros <-; contradiction
        | intros <-; contradiction
        | exact HvE | exact Hall3 ].
    - exists u; repeat split;
        [ intros <-; contradiction
        | intros <-; contradiction
        | exact HuE
        | intros y Hy; destruct (Hall3 y Hy) as [<-|<-]; tauto ]. }
  destruct Hc as [c [Hcb [Hca [Hc3 Hall3']]]].
  (* e4 misses b, so it meets e1 at a and e3 at c *)
  assert (Ha4 : In a e4).
  { destruct (Hint e4 e1 He4 He1) as [x [Hx4 Hx1]].
    destruct (Hall1 x Hx1) as [<-|<-]; [exact Hx4 | contradiction]. }
  assert (Hc4 : In c e4).
  { destruct (Hint e4 e3 He4 He3) as [x [Hx4 Hx3]].
    destruct (Hall3' x Hx3) as [<-|<-]; [contradiction | exact Hx4]. }
  assert (Hall4 : forall y, In y e4 -> y = a \/ y = c)
    by (apply (@two_uniform_pair e4 a c Hlen4 Hnd4 Ha4 Hc4);
        intros <-; contradiction).
  (* every edge is one of the three sides of the triangle abc *)
  assert (H : length G <= length [[a; b]; [a; c]; [b; c]] * 1).
  { apply cover_by_sets.
    - intros C HC.
      destruct (Hint C e1 HC He1) as [x [HxC Hx1]].
      destruct (Hint C e3 HC He3) as [y [HyC Hy3]].
      destruct (Hall1 x Hx1) as [Ex|Ex]; subst x;
        destruct (Hall3' y Hy3) as [Ey|Ey]; subst y.
      + exists [a; b]; split;
          [left; reflexivity | intros w [<-|[<-|[]]]; assumption].
      + exists [a; c]; split;
          [right; left; reflexivity | intros w [<-|[<-|[]]]; assumption].
      + destruct (Hint C e4 HC He4) as [z [HzC Hz4]].
        destruct (Hall4 z Hz4) as [Ez|Ez]; subst z.
        * exists [a; b]; split;
            [left; reflexivity | intros w [<-|[<-|[]]]; assumption].
        * exists [b; c]; split;
            [right; right; left; reflexivity
             | intros w [<-|[<-|[]]]; assumption].
      + exists [b; c]; split;
          [right; right; left; reflexivity | intros w [<-|[<-|[]]]; assumption].
    - assert (Hnd2 : forall x y : nat, x <> y -> NoDup [x; y]).
      { intros x y Hxy; constructor;
          [ simpl; intros [E|[]]; apply Hxy; symmetry; exact E
          | constructor; [intros []|constructor]]. }
      intros T HT; destruct HT as [<-|[<-|[<-|[]]]];
        apply Hpairdeg; solve [apply Hnd2; congruence | reflexivity]. }
  simpl in H; lia.
Qed.

(** ** The conjecture, verified at [m = 1] and [m = 2]

    [StarExtremalAt 1 r] is immediate and [StarExtremalAt 2 r] holds for
    [r >= 3], which is [r >= m + 1]. Feeding both into
    [star_extremal_gives_m_plus_one] gives [r*(2,3) <= 3] — the **exact**
    value, where every general bound the development has gives 4:
    [cover_spread_disjoint] gives [2n = 4], [quadratic_spread_disjoint]
    gives 4, and §24.2's split gives 4. So on the one row where [I] is
    known in closed form, the star-extremal route is not merely better,
    it is sharp. *)

Lemma one_uniform_star_extremal : forall r, StarExtremalAt 1 r.
Proof.
  intros r F HU HR Hint.
  destruct F as [|A F0] eqn:EF; [simpl; lia | rewrite <- EF in *].
  assert (HA : In A F) by (rewrite EF; left; reflexivity).
  destruct (@uniform_mem 1 F A HU HA) as [Hlen _].
  destruct A as [|x [|? ?]]; simpl in Hlen; try discriminate.
  (* every member meets [x], so every member contains it *)
  assert (Hall : forall C, In C F -> In x C).
  { intros C HC.
    destruct (Hint C [x] HC HA) as [z [HzC HzA]].
    destruct HzA as [<-|[]]; exact HzC. }
  assert (Hb : length F <= length [[x]] * (r ^ (1 - 1))).
  { apply cover_by_sets.
    - intros C HC; exists [x]; split;
        [left; reflexivity | intros z [<-|[]]; apply Hall; exact HC].
    - intros T [<-|[]]; eapply rao_point; exact HR. }
  simpl in Hb |- *; lia.
Qed.

Theorem two_uniform_star_extremal : forall r, 3 <= r -> StarExtremalAt 2 r.
Proof.
  intros r Hr H HU HR Hint.
  pose proof (@two_uniform_intersecting_bound r H HU HR Hint) as Hb.
  simpl; lia.
Qed.

Theorem r_star_two_three_at_most_three : SpreadYieldsDisjoint 2 3 3.
Proof.
  replace 3 with (2 + 1) at 2 by reflexivity.
  apply star_extremal_gives_m_plus_one; [lia|].
  intros m Hm Hmn.
  destruct m as [|[|m']]; try lia.
  - apply one_uniform_star_extremal.
  - assert (m' = 0) by lia; subst m'.
    apply two_uniform_star_extremal; lia.
Qed.

(** Combined with [Audit.no_spread_yields_disjoint_2_3_2], which refutes
    [r = 2], this pins the second term of the sequence in Coq:

<<
      r*(2,3) = 3 = m + 1.
>>

    §22.3 records that value as certified by exhaustive search; it is now
    a theorem of the development as well, and it comes out of the same
    machine that gives [r*(3,3) <= 4] on Frankl. *)
