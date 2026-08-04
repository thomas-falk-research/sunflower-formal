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
