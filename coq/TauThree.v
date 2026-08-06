(** * TauThree.v -- the covering-number-three case, elementary and
      unconditional, and the false hypothesis it replaces.

    §24.12 closes [r*(3,3) <= 4] "conditional on one classical theorem and
    no new axiom", the theorem being Frankl's bound for 3-uniform
    intersecting families of covering number 3, entered as

<<
      TauThreeAtMost K :=
        forall G, Uniform 3 G -> (G intersecting) -> (tau(G) >= 3) ->
          length G <= K.
>>

    That statement is **false for every [K]**, and the reason is that
    [Uniform 3 G] says each *member* has three distinct points, not that
    the *members* are distinct. Take the Fano plane -- seven 3-sets on
    seven points, pairwise intersecting, and of covering number 3 because
    each point lies on only three of the seven lines -- and concatenate it
    with itself. Every hypothesis is preserved (they are all conditions on
    pairs of members, or on which sets occur, never on how often), and the
    length doubles. [tau_three_at_most_unguarded_is_false] below is that
    argument in Coq.

    So the conditional theorem had a false antecedent and established
    nothing. The repair is to add [Distinct G], which is exactly what the
    one consumer of the hypothesis can supply: it applies the hypothesis
    to a family carrying [RaoSpread 3 G r], and a 3-uniform Rao-spread
    family is automatically distinct, since [deg T G <= r ^ 0 = 1] at
    every triple.

    And once the statement is true, it is provable here without Frankl,
    which is what the rest of the file does.

    ** The argument

    Fix a member [M = {x,y,z}]. Covering number at least 3 gives, for
    every pair of points, a member missing both; so any member containing
    a given pair [{a,b}] meets that witness in a third point, and there
    are only three of those:

<<
      deg({a,b}) <= 3        for every pair                          (P)
>>

    Split [G] by how much of [M] a member meets. Exactly one member
    contains all of [M], namely [M]. The members meeting [M] in two points
    are capped by (P) at 3 for the first pair and at 3 - 1 = 2 for each of
    the other two, since [M] itself occupies one slot of each: at most 7 in
    the two layers together. The members meeting [M] in exactly one point
    split into three families [T_x], [T_y], [T_z] whose *tails* -- the two
    points outside [M] -- are graphs that

      - have maximum degree at most 3, by (P) again;
      - are pairwise cross-intersecting, because a member of [T_x] and a
        member of [T_y] meet, and not at [x], [y] or [z];
      - are all nonempty, since [T_z] empty makes [{x,y}] a cover.

    [lemma_L] below bounds the sum of three such graphs by 9, so

<<
      |G| <= 7 + 9 = 16,
>>

    which is exactly the constant [split_with_piece] needs at [r = 4].
    Frankl's theorem gives 10 and the elementary greedy bound gives 27;
    16 sits in between, and is the first bound in that interval this
    development can prove. `rust/tests/tau_three.rs` measures the truth at
    10, so the 6 of slack is real, and is not needed. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower Pigeonhole Spread SpreadReduction
     DirectSum Reflect SpreadThreshold TwoCover.
Import ListNotations.

Set Implicit Arguments.

(** ** Generic counting lemmas *)

(** [cover_by_sets] pays [length Ts * K] for a uniform bound [K]. Several
    counts below need the individual degrees instead, because the keys are
    not equally loaded. *)

Fixpoint degsum (Ts : list (list nat)) (F : Family) : nat :=
  match Ts with
  | [] => 0
  | T :: Ts' => deg T F + degsum Ts' F
  end.

Lemma degsum_mono :
  forall Ts (F : Family) (p : list nat -> bool),
    degsum Ts (filter p F) <= degsum Ts F.
Proof.
  induction Ts as [|T Ts IH]; intros F p; simpl; [lia|].
  pose proof (deg_filter_le T p F); pose proof (IH F p); lia.
Qed.

Theorem cover_by_sets_sum :
  forall (Ts : list (list nat)) (F : Family),
    (forall A, In A F -> exists T, In T Ts /\ Subset T A) ->
    length F <= degsum Ts F.
Proof.
  induction Ts as [|T Ts IH]; intros F Hcov.
  - destruct F as [|A F']; simpl; [lia|].
    destruct (Hcov A (or_introl eq_refl)) as [T [HT _]]; destruct HT.
  - simpl.
    assert (Hlen : length F
                   = deg T F
                     + length (filter (fun A => negb (containsb T A)) F))
      by (unfold deg; apply length_filter_partition).
    assert (HG : length (filter (fun A => negb (containsb T A)) F)
                 <= degsum Ts (filter (fun A => negb (containsb T A)) F)).
    { apply IH.
      intros A HA; apply filter_In in HA as [HAF Hneg].
      destruct (Hcov A HAF) as [T' [HT' Hsub]].
      destruct HT' as [<-|HT'].
      - exfalso; apply Bool.negb_true_iff in Hneg.
        apply containsb_true_iff in Hsub; congruence.
      - exists T'; split; assumption. }
    pose proof (degsum_mono Ts F (fun A => negb (containsb T A))); lia.
Qed.

(** Monotonicity of a filter count under implication of the predicates,
    on the members that actually occur. *)

Lemma filter_length_mono :
  forall {A : Type} (p q : A -> bool) (l : list A),
    (forall a, In a l -> p a = true -> q a = true) ->
    length (filter p l) <= length (filter q l).
Proof.
  intros A p q l; induction l as [|a l IH]; intros Himp; simpl; [lia|].
  assert (IH' : length (filter p l) <= length (filter q l))
    by (apply IH; intros b Hb; apply Himp; right; exact Hb).
  destruct (p a) eqn:Ep; destruct (q a) eqn:Eq; simpl; try lia.
  rewrite (Himp a (or_introl eq_refl) Ep) in Eq; discriminate.
Qed.

Lemma filter_filter :
  forall {A : Type} (p q : A -> bool) (l : list A),
    filter p (filter q l) = filter (fun a => andb (q a) (p a)) l.
Proof.
  intros A p q l; induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (q a); simpl; [destruct (p a); simpl; rewrite IH; reflexivity
                         | exact IH].
Qed.

Lemma length_filter_map :
  forall {A B : Type} (f : A -> B) (p : B -> bool) (l : list A),
    length (filter p (map f l)) = length (filter (fun a => p (f a)) l).
Proof.
  intros A B f p l; induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (p (f a)); simpl; [rewrite IH; reflexivity | exact IH].
Qed.

(** A list with no duplicates all of whose elements are equal is short. *)

Lemma nodup_all_eq_le_one :
  forall {A : Type} (l : list A),
    NoDup l -> (forall a b, In a l -> In b l -> a = b) -> length l <= 1.
Proof.
  intros A l Hnd Heq.
  destruct l as [|a [|b l']]; simpl; [lia|lia|].
  exfalso; inversion Hnd as [|? ? Hni _]; subst.
  apply Hni; left.
  apply (Heq b a); [right; left; reflexivity | left; reflexivity].
Qed.

(** ** A distinct uniform family has degree at most one at a full-size set *)

Lemma deg_full_le_one :
  forall k (F : Family) (T : list nat),
    Uniform k F -> Distinct F -> NoDup T -> length T = k ->
    deg T F <= 1.
Proof.
  intros k F T HU HD Hnd Hlen; unfold deg.
  assert (Hall : forall A, In A (filter (containsb T) F) -> SetEq T A).
  { intros A HA; apply filter_In in HA as [HAF Hc].
    apply containsb_true_iff in Hc.
    destruct (@uniform_mem k F A HU HAF) as [HlA HndA].
    split; [exact Hc|].
    apply (NoDup_length_incl Hnd); [rewrite HlA, Hlen; lia | exact Hc]. }
  apply nodup_all_eq_le_one.
  - apply SetNoDup_NoDup, SetNoDup_filter; exact HD.
  - intros A B HA HB.
    assert (HAF : In A F) by (apply filter_In in HA; tauto).
    assert (HBF : In B F) by (apply filter_In in HB; tauto).
    apply (SetNoDup_setEq_eq HD HAF HBF).
    apply SetEq_trans with T; [apply SetEq_sym; apply Hall; exact HA
                              | apply Hall; exact HB].
Qed.

(** ** Lemma L: three cross-intersecting graphs of maximum degree 3

    [CapGraph A] is "[A] is a graph -- 2-uniform with no repeated edge --
    of maximum degree at most 3". The repeated-edge condition is the
    [length T = 2] instance of [deg T A <= 1]; in the application it comes
    from distinctness of the family [A] is a tail of. *)

Definition CapGraph (A : Family) : Prop :=
  Uniform 2 A
  /\ (forall v, deg [v] A <= 3)
  /\ (forall T, NoDup T -> length T = 2 -> deg T A <= 1).

Definition CrossInt (A B : Family) : Prop :=
  forall e f, In e A -> In f B -> exists w, In w e /\ In w f.

Lemma CrossInt_sym : forall A B, CrossInt A B -> CrossInt B A.
Proof.
  intros A B H e f He Hf; destruct (H f e Hf He) as [w [H1 H2]];
    exists w; tauto.
Qed.

Lemma pair_nodup : forall a b : nat, a <> b -> NoDup [a; b].
Proof.
  intros a b Hab; constructor;
    [simpl; intros [E|[]]; apply Hab; symmetry; exact E
     | constructor; [intros []|constructor]].
Qed.

Lemma nodup3 : forall x y z : nat, NoDup [x;y;z] -> x <> y /\ x <> z /\ y <> z.
Proof.
  intros x y z H.
  inversion H as [|? ? H1 H2]; subst.
  inversion H2 as [|? ? H3 _]; subst.
  repeat split.
  - intros <-; apply H1; left; reflexivity.
  - intros <-; apply H1; right; left; reflexivity.
  - intros <-; apply H3; left; reflexivity.
Qed.

Lemma triple_nodup :
  forall a b c : nat, a <> b -> a <> c -> b <> c -> NoDup [a; b; c].
Proof.
  intros a b c Hab Hac Hbc; constructor.
  - simpl; intros [E|[E|[]]]; congruence.
  - apply pair_nodup; exact Hbc.
Qed.

(** Every edge of [A] meets a fixed pair, so [A] is covered by two points
    and has at most six edges. *)

Lemma cap_two_point_cover :
  forall (A : Family) u v,
    (forall w, deg [w] A <= 3) ->
    (forall e, In e A -> In u e \/ In v e) ->
    length A <= 6.
Proof.
  intros A u v Hd Hcov.
  assert (H : length A <= length [[u];[v]] * 3).
  { apply cover_by_sets.
    - intros e He; destruct (Hcov e He) as [Hu|Hv].
      + exists [u]; split; [left; reflexivity | intros y [<-|[]]; exact Hu].
      + exists [v]; split; [right; left; reflexivity
                           | intros y [<-|[]]; exact Hv].
    - intros T [<-|[<-|[]]]; apply Hd. }
  simpl in H; lia.
Qed.

(** An edge of the other graph supplies the pair. *)

Lemma cross_gives_cover :
  forall (A B : Family) f,
    Uniform 2 B -> In f B -> CrossInt A B ->
    exists u v, u <> v /\ In u f /\ In v f /\
                (forall e, In e A -> In u e \/ In v e).
Proof.
  intros A B f HUB Hf HAB.
  destruct (@uniform_mem 2 B f HUB Hf) as [Hlen Hnd].
  destruct (@two_uniform_split f Hlen Hnd) as [u [v [Huv [Hu [Hv Hall]]]]].
  exists u, v; repeat split; try assumption.
  intros e He; destruct (HAB e f He Hf) as [w [Hwe Hwf]].
  destruct (Hall w Hwf) as [<-|<-]; tauto.
Qed.

(** ** L1: an intersecting graph of maximum degree 3 has at most 3 edges

    §24.10's device: instead of classifying graphs of matching number one
    as "a star or a triangle", name an edge missing [a] and then an edge
    containing [a] but not [b]. *)

Lemma internally_intersecting_bound :
  forall (A : Family),
    CapGraph A ->
    (forall e f, In e A -> In f A -> exists w, In w e /\ In w f) ->
    length A <= 3.
Proof.
  intros A [HU [Hd Hpair]] Hint.
  destruct A as [|e1 A0] eqn:EA; [simpl; lia | rewrite <- EA in *].
  assert (He1 : In e1 A) by (rewrite EA; left; reflexivity).
  destruct (@uniform_mem 2 A e1 HU He1) as [Hlen1 Hnd1].
  destruct (@two_uniform_split e1 Hlen1 Hnd1) as [a [b [Hab [Ha1 [Hb1 Hall1]]]]].
  destruct (existsb (fun e => negb (memb a e)) A) eqn:Ea; cycle 1.
  { assert (Halla : forall e, In e A -> In a e).
    { intros e He.
      pose proof (existsb_false_forall _ _ _ Ea e He) as E.
      apply Bool.negb_false_iff in E; apply memb_true_iff; exact E. }
    assert (H : length A <= length [[a]] * 3).
    { apply cover_by_sets.
      - intros e He; exists [a]; split;
          [left; reflexivity | intros y [<-|[]]; apply Halla; exact He].
      - intros T [<-|[]]; apply Hd. }
    simpl in H; lia. }
  apply existsb_exists in Ea as [e2 [He2 Hna2]].
  apply Bool.negb_true_iff in Hna2.
  assert (Ha2 : ~ In a e2)
    by (intros Hin; apply memb_true_iff in Hin; congruence).
  assert (Hb2 : In b e2).
  { destruct (Hint e2 e1 He2 He1) as [w [Hw2 Hw1]].
    destruct (Hall1 w Hw1) as [<-|<-]; [contradiction | exact Hw2]. }
  destruct (@uniform_mem 2 A e2 HU He2) as [Hlen2 Hnd2].
  destruct (@two_uniform_split e2 Hlen2 Hnd2) as [p [q [Hpq [Hp2 [Hq2 Hall2]]]]].
  assert (Hc : exists c, c <> a /\ c <> b /\ In c e2 /\
                         (forall y, In y e2 -> y = b \/ y = c)).
  { destruct (Hall2 b Hb2) as [<-|<-].
    - exists q; repeat split;
        [ intros <-; contradiction | intros <-; contradiction
        | exact Hq2 | exact Hall2 ].
    - exists p; repeat split;
        [ intros <-; contradiction | intros <-; contradiction | exact Hp2
        | intros y Hy; destruct (Hall2 y Hy) as [<-|<-]; tauto ]. }
  destruct Hc as [c [Hca [Hcb [Hc2 Hall2']]]].
  assert (Hmeet1 : forall e, In e A -> In a e \/ In b e).
  { intros e He; destruct (Hint e e1 He He1) as [w [Hwe Hw1]].
    destruct (Hall1 w Hw1) as [<-|<-]; tauto. }
  assert (Hmeet2 : forall e, In e A -> In b e \/ In c e).
  { intros e He; destruct (Hint e e2 He He2) as [w [Hwe Hw2]].
    destruct (Hall2' w Hw2) as [<-|<-]; tauto. }
  destruct (existsb (fun e => andb (memb a e) (negb (memb b e))) A) eqn:Eab;
    cycle 1.
  { assert (Hallb : forall e, In e A -> In b e).
    { intros e He.
      pose proof (existsb_false_forall _ _ _ Eab e He) as E.
      apply Bool.andb_false_iff in E as [E|E].
      - destruct (Hmeet1 e He) as [Hae|Hbe]; [|exact Hbe].
        exfalso; apply memb_true_iff in Hae; congruence.
      - apply Bool.negb_false_iff in E; apply memb_true_iff; exact E. }
    assert (H : length A <= length [[b]] * 3).
    { apply cover_by_sets.
      - intros e He; exists [b]; split;
          [left; reflexivity | intros y [<-|[]]; apply Hallb; exact He].
      - intros T [<-|[]]; apply Hd. }
    simpl in H; lia. }
  apply existsb_exists in Eab as [e3 [He3 Hab3]].
  apply Bool.andb_true_iff in Hab3 as [Ha3b Hb3b].
  apply Bool.negb_true_iff in Hb3b.
  assert (Ha3 : In a e3) by (apply memb_true_iff; exact Ha3b).
  assert (Hb3 : ~ In b e3)
    by (intros Hin; apply memb_true_iff in Hin; congruence).
  assert (Hc3 : In c e3)
    by (destruct (Hmeet2 e3 He3) as [H|H]; [contradiction | exact H]).
  assert (Hmeet3 : forall e, In e A -> In a e \/ In c e).
  { intros e He; destruct (Hint e e3 He He3) as [w [Hwe Hw3]].
    destruct (@uniform_mem 2 A e3 HU He3) as [Hlen3 Hnd3].
    destruct (@two_uniform_pair e3 a c Hlen3 Hnd3 Ha3 Hc3
                ltac:(intros <-; contradiction) w Hw3) as [<-|<-]; tauto. }
  assert (H : length A <= length [[a;b];[b;c];[a;c]] * 1).
  { apply cover_by_sets.
    - intros e He.
      destruct (in_dec Nat.eq_dec b e) as [Hbe|Hbe].
      + destruct (Hmeet3 e He) as [Hae|Hce].
        * exists [a;b]; split;
            [left; reflexivity | intros y [<-|[<-|[]]]; assumption].
        * exists [b;c]; split;
            [right; left; reflexivity | intros y [<-|[<-|[]]]; assumption].
      + assert (Hae : In a e)
          by (destruct (Hmeet1 e He) as [H|H]; [exact H | contradiction]).
        assert (Hce : In c e)
          by (destruct (Hmeet2 e He) as [H|H]; [contradiction | exact H]).
        exists [a;c]; split;
          [right; right; left; reflexivity
           | intros y [<-|[<-|[]]]; assumption].
    - intros T [<-|[<-|[<-|[]]]]; apply Hpair;
        solve [apply pair_nodup; congruence | reflexivity]. }
  simpl in H; lia.
Qed.

(** ** L2: six edges force the other two graphs down to one edge each

    If every edge of [A] meets [{u,v}] and [A] has six edges, then [u]
    carries three [A]-edges and so does [v]. An edge missing [u] and
    meeting all three of [u]'s edges would need one of two points to serve
    three distinct pairs at [u], and each pair has degree at most one. *)

Lemma six_forces_degree :
  forall (A : Family) u v,
    (forall w, deg [w] A <= 3) ->
    (forall e, In e A -> In u e \/ In v e) ->
    6 <= length A ->
    3 <= deg [u] A.
Proof.
  intros A u v Hd Hcov Hlen.
  assert (Hpart : length A
                  = length (filter (containsb [u]) A)
                    + length (filter (fun e => negb (containsb [u] e)) A))
    by apply length_filter_partition.
  assert (Hrest : length (filter (fun e => negb (containsb [u] e)) A)
                  <= length (filter (containsb [v]) A)).
  { apply filter_length_mono.
    intros e He Hne; apply Bool.negb_true_iff in Hne.
    apply containsb_true_iff; intros y [<-|[]].
    destruct (Hcov e He) as [Hu|Hv]; [|exact Hv].
    exfalso; assert (Hct : containsb [u] e = true)
      by (apply containsb_true_iff; intros y' [<-|[]]; exact Hu).
    congruence. }
  pose proof (Hd u) as Hu3; pose proof (Hd v) as Hv3; unfold deg in *; lia.
Qed.

Lemma three_at_point_forces :
  forall (A : Family) u h,
    (forall T, NoDup T -> length T = 2 -> deg T A <= 1) ->
    3 <= deg [u] A ->
    length h = 2 -> NoDup h ->
    (forall e, In e A -> exists w, In w e /\ In w h) ->
    In u h.
Proof.
  intros A u h Hpair Hdeg Hlen Hnd Hmeet.
  destruct (in_dec Nat.eq_dec u h) as [Hin|Hin]; [exact Hin | exfalso].
  destruct (@two_uniform_split h Hlen Hnd) as [p [q [Hpq [Hp [Hq Hall]]]]].
  assert (Hup : u <> p) by (intros <-; contradiction).
  assert (Huq : u <> q) by (intros <-; contradiction).
  set (Au := filter (containsb [u]) A).
  assert (Hcov : forall e, In e Au -> exists T, In T [[u;p];[u;q]] /\ Subset T e).
  { intros e He; apply filter_In in He as [HeA Hc].
    apply containsb_true_iff in Hc.
    assert (Hue : In u e) by (apply Hc; left; reflexivity).
    destruct (Hmeet e HeA) as [w [Hwe Hwh]].
    destruct (Hall w Hwh) as [<-|<-].
    - exists [u;w]; split; [left; reflexivity | intros y [<-|[<-|[]]]; assumption].
    - exists [u;w]; split;
        [right; left; reflexivity | intros y [<-|[<-|[]]]; assumption]. }
  pose proof (cover_by_sets_sum _ _ Hcov) as Hb.
  simpl in Hb.
  assert (Hp1 : deg [u;p] Au <= 1).
  { eapply Nat.le_trans; [apply deg_filter_le|].
    apply Hpair; [apply pair_nodup; exact Hup | reflexivity]. }
  assert (Hq1 : deg [u;q] Au <= 1).
  { eapply Nat.le_trans; [apply deg_filter_le|].
    apply Hpair; [apply pair_nodup; exact Huq | reflexivity]. }
  assert (Hlen' : length Au = deg [u] A) by reflexivity.
  lia.
Qed.

(** ** L3: two disjoint edges cap the other two graphs together at four *)

Lemma disjoint_pair_bounds :
  forall (A B C : Family) e1 e2,
    Uniform 2 A -> Uniform 2 B -> Uniform 2 C ->
    (forall T, NoDup T -> length T = 2 -> deg T B <= 1) ->
    (forall T, NoDup T -> length T = 2 -> deg T C <= 1) ->
    CrossInt A B -> CrossInt A C -> CrossInt B C ->
    In e1 A -> In e2 A -> (forall w, In w e1 -> ~ In w e2) ->
    length B + length C <= 4.
Proof.
  intros A B C e1 e2 HUA HUB HUC HpB HpC HAB HAC HBC He1 He2 Hdis.
  destruct (@uniform_mem 2 A e1 HUA He1) as [Hl1 Hn1].
  destruct (@uniform_mem 2 A e2 HUA He2) as [Hl2 Hn2].
  destruct (@two_uniform_split e1 Hl1 Hn1) as [a [b [Hab [Ha1 [Hb1 Hall1]]]]].
  destruct (@two_uniform_split e2 Hl2 Hn2) as [c [d [Hcd [Hc2 [Hd2 Hall2]]]]].
  assert (Hac : a <> c) by (intros <-; apply (Hdis a Ha1 Hc2)).
  assert (Had : a <> d) by (intros <-; apply (Hdis a Ha1 Hd2)).
  assert (Hbc : b <> c) by (intros <-; apply (Hdis b Hb1 Hc2)).
  assert (Hbd : b <> d) by (intros <-; apply (Hdis b Hb1 Hd2)).
  (* every edge of B, and of C, contains one of a,b and one of c,d *)
  assert (Hcover : forall (X : Family), CrossInt A X ->
            forall f, In f X ->
              exists T, In T [[a;c];[a;d];[b;c];[b;d]] /\ Subset T f).
  { intros X HAX f Hf.
    destruct (HAX e1 f He1 Hf) as [w1 [Hw1e Hw1f]].
    destruct (HAX e2 f He2 Hf) as [w2 [Hw2e Hw2f]].
    destruct (Hall1 w1 Hw1e) as [<-|<-]; destruct (Hall2 w2 Hw2e) as [<-|<-].
    - exists [w1;w2]; split;
        [left; reflexivity | intros y [<-|[<-|[]]]; assumption].
    - exists [w1;w2]; split;
        [right; left; reflexivity | intros y [<-|[<-|[]]]; assumption].
    - exists [w1;w2]; split;
        [right; right; left; reflexivity
         | intros y [<-|[<-|[]]]; assumption].
    - exists [w1;w2]; split;
        [right; right; right; left; reflexivity
         | intros y [<-|[<-|[]]]; assumption]. }
  pose proof (cover_by_sets_sum _ _ (Hcover B HAB)) as HBb.
  pose proof (cover_by_sets_sum _ _ (Hcover C HAC)) as HCb.
  simpl in HBb, HCb.
  (* a conflicting pair of keys cannot both be occupied *)
  assert (Hconf : forall p1 p2 q1 q2,
             p1 <> p2 -> q1 <> q2 ->
             p1 <> q1 -> p1 <> q2 -> p2 <> q1 -> p2 <> q2 ->
             deg [p1;p2] B + deg [q1;q2] C <= 1).
  { intros p1 p2 q1 q2 H12 Hq12 E1 E2 E3 E4.
    assert (HB1 : deg [p1;p2] B <= 1)
      by (apply HpB; [apply pair_nodup; exact H12 | reflexivity]).
    assert (HC1 : deg [q1;q2] C <= 1)
      by (apply HpC; [apply pair_nodup; exact Hq12 | reflexivity]).
    destruct (Nat.eq_dec (deg [p1;p2] B) 0) as [E|E]; [lia|].
    destruct (Nat.eq_dec (deg [q1;q2] C) 0) as [E'|E']; [lia|].
    exfalso.
    destruct (@deg_pos_inv [p1;p2] B ltac:(lia)) as [f [HfB Hsf]].
    destruct (@deg_pos_inv [q1;q2] C ltac:(lia)) as [g [HgC Hsg]].
    destruct (HBC f g HfB HgC) as [w [Hwf Hwg]].
    destruct (@uniform_mem 2 B f HUB HfB) as [Hlf Hndf].
    destruct (@uniform_mem 2 C g HUC HgC) as [Hlg Hndg].
    assert (Hfall : forall y, In y f -> y = p1 \/ y = p2).
    { apply (@two_uniform_pair f p1 p2 Hlf Hndf); try assumption;
        [ apply Hsf; left; reflexivity | apply Hsf; right; left; reflexivity ]. }
    assert (Hgall : forall y, In y g -> y = q1 \/ y = q2).
    { apply (@two_uniform_pair g q1 q2 Hlg Hndg); try assumption;
        [ apply Hsg; left; reflexivity | apply Hsg; right; left; reflexivity ]. }
    destruct (Hfall w Hwf) as [<-|<-]; destruct (Hgall w Hwg) as [E0|E0];
      congruence. }
  assert (H1 : deg [a;c] B + deg [b;d] C <= 1) by (apply Hconf; congruence).
  assert (H2 : deg [a;d] B + deg [b;c] C <= 1) by (apply Hconf; congruence).
  assert (H3 : deg [b;c] B + deg [a;d] C <= 1) by (apply Hconf; congruence).
  assert (H4 : deg [b;d] B + deg [a;c] C <= 1) by (apply Hconf; congruence).
  lia.
Qed.

(** ** Lemma L, for a graph with four or more edges *)

Lemma lemma_L_big :
  forall (A B C : Family),
    CapGraph A -> CapGraph B -> CapGraph C ->
    CrossInt A B -> CrossInt A C -> CrossInt B C ->
    B <> [] -> C <> [] -> 4 <= length A ->
    length A + length B + length C <= 9.
Proof.
  intros A B C HA HB HC HAB HAC HBC HBne HCne H4.
  destruct HA as [HUA [HdA HpA]].
  destruct HB as [HUB [HdB HpB]].
  destruct HC as [HUC [HdC HpC]].
  destruct B as [|f B0] eqn:EB; [contradiction | rewrite <- EB in *].
  assert (HfB : In f B) by (rewrite EB; left; reflexivity).
  destruct (@cross_gives_cover A B f HUB HfB HAB)
    as [u [v [Huv [Huf [Hvf Hcov]]]]].
  assert (HA6 : length A <= 6) by (apply (@cap_two_point_cover A u v HdA Hcov)).
  (* four edges and maximum degree 3 rule out an intersecting graph *)
  destruct (existsb (fun e => existsb (fun e' => disjointb e e') A) A) eqn:Edis;
    cycle 1.
  { exfalso.
    assert (Hint : forall e e', In e A -> In e' A -> exists w, In w e /\ In w e').
    { intros e e' He He'.
      pose proof (existsb_false_forall _ _ _ Edis e He) as E1.
      pose proof (existsb_false_forall _ _ _ E1 e' He') as E2.
      apply disjointb_false_iff in E2; exact E2. }
    pose proof (@internally_intersecting_bound A
                  (conj HUA (conj HdA HpA)) Hint); lia. }
  apply existsb_exists in Edis as [e1 [He1 Hex]].
  apply existsb_exists in Hex as [e2 [He2 Hdb]].
  apply disjointb_correct in Hdb.
  assert (HBC4 : length B + length C <= 4).
  { apply (@disjoint_pair_bounds A B C e1 e2 HUA HUB HUC HpB HpC
             HAB HAC HBC He1 He2 Hdb). }
  destruct (le_lt_dec (length A) 5) as [H5|H5]; [lia|].
  (* six edges: every edge of B and of C is the pair {u,v} *)
  assert (HA6' : 6 <= length A) by lia.
  assert (Hdu : 3 <= deg [u] A) by (apply (@six_forces_degree A u v HdA Hcov HA6')).
  assert (Hcov' : forall e, In e A -> In v e \/ In u e)
    by (intros e He; destruct (Hcov e He); tauto).
  assert (Hdv : 3 <= deg [v] A) by (apply (@six_forces_degree A v u HdA Hcov' HA6')).
  assert (Hsingle : forall (X : Family), Uniform 2 X ->
             (forall T, NoDup T -> length T = 2 -> deg T X <= 1) ->
             CrossInt A X -> length X <= 1).
  { intros X HUX HpX HAX.
    assert (Hb : length X <= length [[u;v]] * 1).
    { apply cover_by_sets.
      - intros g Hg.
        destruct (@uniform_mem 2 X g HUX Hg) as [Hlg Hndg].
        assert (Hmeet : forall e, In e A -> exists w, In w e /\ In w g)
          by (intros e He; apply (HAX e g He Hg)).
        assert (Hug : In u g)
          by (apply (@three_at_point_forces A u g HpA Hdu Hlg Hndg Hmeet)).
        assert (Hvg : In v g)
          by (apply (@three_at_point_forces A v g HpA Hdv Hlg Hndg Hmeet)).
        exists [u;v]; split;
          [left; reflexivity | intros y [<-|[<-|[]]]; assumption].
      - intros T [<-|[]]; apply HpX;
          [apply pair_nodup; exact Huv | reflexivity]. }
    simpl in Hb; lia. }
  pose proof (Hsingle B HUB HpB HAB).
  pose proof (Hsingle C HUC HpC HAC).
  lia.
Qed.

Theorem lemma_L :
  forall (A B C : Family),
    CapGraph A -> CapGraph B -> CapGraph C ->
    CrossInt A B -> CrossInt A C -> CrossInt B C ->
    A <> [] -> B <> [] -> C <> [] ->
    length A + length B + length C <= 9.
Proof.
  intros A B C HA HB HC HAB HAC HBC HAne HBne HCne.
  destruct (le_lt_dec 4 (length A)) as [H|HA3].
  { apply (@lemma_L_big A B C HA HB HC HAB HAC HBC HBne HCne H). }
  destruct (le_lt_dec 4 (length B)) as [H|HB3].
  { pose proof (@lemma_L_big B A C HB HA HC (CrossInt_sym HAB) HBC HAC
                  HAne HCne H); lia. }
  destruct (le_lt_dec 4 (length C)) as [H|HC3].
  { pose proof (@lemma_L_big C A B HC HA HB (CrossInt_sym HAC)
                  (CrossInt_sym HBC) HAB HAne HBne H); lia. }
  lia.
Qed.

(** ** Removing a point from a member *)

Definition rem (x : nat) (C : list nat) : list nat :=
  filter (fun y => negb (Nat.eqb y x)) C.

Lemma in_rem : forall x C y, In y (rem x C) <-> (In y C /\ y <> x).
Proof.
  intros x C y; unfold rem; rewrite filter_In; split.
  - intros [H1 H2]; split;
      [exact H1 | apply Bool.negb_true_iff, Nat.eqb_neq in H2; exact H2].
  - intros [H1 H2]; split;
      [exact H1 | apply Bool.negb_true_iff, Nat.eqb_neq; exact H2].
Qed.

Lemma rem_nodup : forall x C, NoDup C -> NoDup (rem x C).
Proof. intros x C H; apply NoDup_filter; exact H. Qed.

Lemma rem_length :
  forall x C, NoDup C -> In x C -> length (rem x C) + 1 = length C.
Proof.
  intros x C Hnd Hin.
  assert (Hpart : length C = length (filter (fun y => Nat.eqb y x) C)
                             + length (rem x C))
    by apply length_filter_partition.
  assert (Hone : length (filter (fun y => Nat.eqb y x) C) <= 1).
  { apply nodup_all_eq_le_one; [apply NoDup_filter; exact Hnd|].
    intros a b Ha Hb; apply filter_In in Ha as [_ Ea];
      apply filter_In in Hb as [_ Eb].
    apply Nat.eqb_eq in Ea; apply Nat.eqb_eq in Eb; congruence. }
  assert (Hge : 1 <= length (filter (fun y => Nat.eqb y x) C)).
  { assert (Hx : In x (filter (fun y => Nat.eqb y x) C))
      by (apply filter_In; split; [exact Hin | apply Nat.eqb_refl]).
    destruct (filter (fun y => Nat.eqb y x) C); [contradiction | simpl; lia]. }
  lia.
Qed.

(** ** The layer that loses a slot to [M] itself *)

Lemma minus_one_bound :
  forall (P Q : list nat -> bool) (F : Family) (M0 : list nat) K,
    In M0 F -> P M0 = true -> Q M0 = true ->
    length (filter P F) <= K ->
    length (filter (fun A => andb (P A) (negb (Q A))) F) + 1 <= K.
Proof.
  intros P Q F M0 K HM HP HQ HK.
  assert (Hpart : length (filter P F)
                  = length (filter Q (filter P F))
                    + length (filter (fun A => negb (Q A)) (filter P F)))
    by apply length_filter_partition.
  assert (Heq : filter (fun A => negb (Q A)) (filter P F)
                = filter (fun A => andb (P A) (negb (Q A))) F)
    by apply filter_filter.
  rewrite Heq in Hpart.
  assert (H1 : 1 <= length (filter Q (filter P F))).
  { assert (Hin : In M0 (filter Q (filter P F)))
      by (apply filter_In; split;
          [apply filter_In; split; assumption | assumption]).
    destruct (filter Q (filter P F)); [contradiction | simpl; lia]. }
  lia.
Qed.

(** ** The bound *)

Section TauThreeBound.

Variable G : Family.
Hypothesis HU : Uniform 3 G.
Hypothesis HD : Distinct G.
Hypothesis Hint : forall C D, In C G -> In D G -> exists w, In w C /\ In w D.
Hypothesis Htau : forall p q, exists C, In C G /\ ~ In p C /\ ~ In q C.

Lemma tt_triple : forall T, NoDup T -> length T = 3 -> deg T G <= 1.
Proof. intros T H1 H2; apply (@deg_full_le_one 3 G T HU HD H1 H2). Qed.

(** (P): covering number at least 3 caps every pair degree at 3. *)

Lemma tt_pair : forall a b, a <> b -> deg [a; b] G <= 3.
Proof.
  intros a b Hab.
  destruct (Htau a b) as [D [HDG [Hna Hnb]]].
  destruct (@uniform_mem 3 G D HU HDG) as [Hl3 Hnd3].
  destruct D as [|d1 [|d2 [|d3 [|d4 D']]]]; simpl in Hl3; try discriminate.
  assert (Hd1 : In d1 [d1;d2;d3]) by (left; reflexivity).
  assert (Hd2 : In d2 [d1;d2;d3]) by (right; left; reflexivity).
  assert (Hd3 : In d3 [d1;d2;d3]) by (right; right; left; reflexivity).
  assert (Hnd : forall w, In w [d1;d2;d3] -> a <> w /\ b <> w).
  { intros w Hw; split; intros <-; contradiction. }
  assert (Hb : length (filter (containsb [a;b]) G)
               <= length [[a;b;d1];[a;b;d2];[a;b;d3]] * 1).
  { apply cover_by_sets.
    - intros A HA; apply filter_In in HA as [HAG Hc].
      apply containsb_true_iff in Hc.
      assert (HaA : In a A) by (apply Hc; left; reflexivity).
      assert (HbA : In b A) by (apply Hc; right; left; reflexivity).
      destruct (Hint A [d1;d2;d3] HAG HDG) as [w [HwA HwD]].
      exists [a;b;w]; split.
      + destruct HwD as [<-|[<-|[<-|[]]]];
          [left | right; left | right; right; left]; reflexivity.
      + intros t [<-|[<-|[<-|[]]]]; assumption.
    - intros T HT.
      eapply Nat.le_trans; [apply deg_filter_le|].
      destruct HT as [<-|[<-|[<-|[]]]]; apply tt_triple;
        solve [ apply triple_nodup;
                solve [ exact Hab
                      | apply (Hnd _ Hd1) | apply (Hnd _ Hd2) | apply (Hnd _ Hd3) ]
              | reflexivity ]. }
  unfold deg; simpl in Hb; lia.
Qed.

(** ** The three one-point layers, through their tail graphs *)

Lemma tails_bound :
  forall x y z (Tx Ty Tz : Family),
    x <> y -> x <> z -> y <> z ->
    (forall A, In A Tx -> In A G /\ In x A /\ ~ In y A /\ ~ In z A) ->
    (forall A, In A Ty -> In A G /\ In y A /\ ~ In x A /\ ~ In z A) ->
    (forall A, In A Tz -> In A G /\ In z A /\ ~ In x A /\ ~ In y A) ->
    (forall T, deg T Tx <= deg T G) ->
    (forall T, deg T Ty <= deg T G) ->
    (forall T, deg T Tz <= deg T G) ->
    Tx <> [] -> Ty <> [] -> Tz <> [] ->
    length Tx + length Ty + length Tz <= 9.
Proof.
  intros x y z Tx Ty Tz Hxy Hxz Hyz HTx HTy HTz HdTx HdTy HdTz Hnx Hny Hnz.
  (* the generic facts about one anchor, proved once and used three times *)
  assert (Hcap : forall a (T : Family),
             (forall A, In A T -> In A G /\ In a A) ->
             (forall S, deg S T <= deg S G) ->
             CapGraph (map (rem a) T)).
  { intros a T Hmem Hdsub; repeat split.
    - apply Forall_forall; intros e He.
      apply in_map_iff in He as [A [<- HA]].
      destruct (Hmem A HA) as [HAG HaA].
      destruct (@uniform_mem 3 G A HU HAG) as [Hl Hnd].
      unfold UniformSet; split;
        [ pose proof (@rem_length a A Hnd HaA); lia | apply rem_nodup; exact Hnd ].
    - intros v; unfold deg; rewrite length_filter_map.
      destruct (Nat.eq_dec v a) as [<-|Hva].
      + assert (Hz : forall A, containsb [v] (rem v A) = false).
        { intros A; destruct (containsb [v] (rem v A)) eqn:E; [|reflexivity].
          exfalso; apply containsb_true_iff in E.
          assert (Hin : In v (rem v A)) by (apply E; left; reflexivity).
          apply in_rem in Hin as [_ Hne]; apply Hne; reflexivity. }
        rewrite (filter_ext_eq _ (fun _ => false) T (fun A => Hz A)).
        assert (Hnil : forall (l : Family), filter (fun _ => false) l = []).
        { induction l; simpl; [reflexivity | assumption]. }
        rewrite Hnil; simpl; lia.
      + eapply Nat.le_trans.
        * apply (@filter_length_mono _ _ (containsb [a; v])).
          intros A HA Hc; apply containsb_true_iff in Hc.
          assert (Hin : In v (rem a A)) by (apply Hc; left; reflexivity).
          apply in_rem in Hin as [HvA _].
          destruct (Hmem A HA) as [_ HaA].
          apply containsb_true_iff; intros t [<-|[<-|[]]]; assumption.
        * eapply Nat.le_trans; [apply (Hdsub [a;v])|].
          apply tt_pair; intros <-; apply Hva; reflexivity.
    - intros S Hnd Hlen; unfold deg; rewrite length_filter_map.
      destruct S as [|s1 [|s2 [|s3 S']]]; simpl in Hlen; try discriminate.
      assert (Hs12 : s1 <> s2)
        by (inversion Hnd as [|? ? Hni _]; subst;
            intros <-; apply Hni; left; reflexivity).
      destruct (Nat.eq_dec s1 a) as [<-|H1a].
      { assert (Hz : forall A, containsb [s1; s2] (rem s1 A) = false).
        { intros A; destruct (containsb [s1;s2] (rem s1 A)) eqn:E;
            [|reflexivity].
          exfalso; apply containsb_true_iff in E.
          assert (Hin : In s1 (rem s1 A)) by (apply E; left; reflexivity).
          apply in_rem in Hin as [_ Hne]; apply Hne; reflexivity. }
        rewrite (filter_ext_eq _ (fun _ => false) T (fun A => Hz A)).
        assert (Hnil : forall (l : Family), filter (fun _ => false) l = []).
        { induction l; simpl; [reflexivity | assumption]. }
        rewrite Hnil; simpl; lia. }
      destruct (Nat.eq_dec s2 a) as [<-|H2a].
      { assert (Hz : forall A, containsb [s1; s2] (rem s2 A) = false).
        { intros A; destruct (containsb [s1;s2] (rem s2 A)) eqn:E;
            [|reflexivity].
          exfalso; apply containsb_true_iff in E.
          assert (Hin : In s2 (rem s2 A))
            by (apply E; right; left; reflexivity).
          apply in_rem in Hin as [_ Hne]; apply Hne; reflexivity. }
        rewrite (filter_ext_eq _ (fun _ => false) T (fun A => Hz A)).
        assert (Hnil : forall (l : Family), filter (fun _ => false) l = []).
        { induction l; simpl; [reflexivity | assumption]. }
        rewrite Hnil; simpl; lia. }
      eapply Nat.le_trans.
      * apply (@filter_length_mono _ _ (containsb [a; s1; s2])).
        intros A HA Hc; apply containsb_true_iff in Hc.
        assert (H1 : In s1 (rem a A)) by (apply Hc; left; reflexivity).
        assert (H2 : In s2 (rem a A)) by (apply Hc; right; left; reflexivity).
        apply in_rem in H1 as [H1A _]; apply in_rem in H2 as [H2A _].
        destruct (Hmem A HA) as [_ HaA].
        apply containsb_true_iff; intros t [<-|[<-|[<-|[]]]]; assumption.
      * eapply Nat.le_trans; [apply (Hdsub [a;s1;s2])|].
        apply tt_triple; [| reflexivity].
        apply triple_nodup; [congruence | congruence | exact Hs12]. }
  (* cross-intersection, likewise once *)
  assert (Hcross : forall a b (S T : Family),
             a <> b ->
             (forall A, In A S -> In A G /\ ~ In b A) ->
             (forall A, In A T -> In A G /\ ~ In a A) ->
             CrossInt (map (rem a) S) (map (rem b) T)).
  { intros a b S T Hab HS HT e f He Hf.
    apply in_map_iff in He as [A [<- HA]].
    apply in_map_iff in Hf as [B0 [<- HB]].
    destruct (HS A HA) as [HAG HbA].
    destruct (HT B0 HB) as [HBG HaB].
    destruct (Hint A B0 HAG HBG) as [w [HwA HwB]].
    exists w; split; apply in_rem; split; try assumption.
    - intros <-; contradiction.
    - intros <-; contradiction. }
  assert (HmapA : forall a (T : Family), T <> [] -> map (rem a) T <> []).
  { intros a T HT; destruct T; [contradiction | simpl; discriminate]. }
  pose proof (@lemma_L (map (rem x) Tx) (map (rem y) Ty) (map (rem z) Tz)
    (Hcap x Tx ltac:(intros A HA; destruct (HTx A HA); tauto) HdTx)
    (Hcap y Ty ltac:(intros A HA; destruct (HTy A HA); tauto) HdTy)
    (Hcap z Tz ltac:(intros A HA; destruct (HTz A HA); tauto) HdTz)
    (Hcross x y Tx Ty Hxy
       ltac:(intros A HA; destruct (HTx A HA) as [? [? [? ?]]]; tauto)
       ltac:(intros A HA; destruct (HTy A HA) as [? [? [? ?]]]; tauto))
    (Hcross x z Tx Tz Hxz
       ltac:(intros A HA; destruct (HTx A HA) as [? [? [? ?]]]; tauto)
       ltac:(intros A HA; destruct (HTz A HA) as [? [? [? ?]]]; tauto))
    (Hcross y z Ty Tz Hyz
       ltac:(intros A HA; destruct (HTy A HA) as [? [? [? ?]]]; tauto)
       ltac:(intros A HA; destruct (HTz A HA) as [? [? [? ?]]]; tauto))
    (HmapA x Tx Hnx) (HmapA y Ty Hny) (HmapA z Tz Hnz)) as Hb.
  rewrite !map_length in Hb; exact Hb.
Qed.

(** ** The layer decomposition against a single member

    Every member meets [M = {x,y,z}]. Peel off the members containing
    [{x,y}] (at most 3, by (P)), then those containing [{x,z}] (at most 2,
    since [M] already used a slot and is gone), then those containing
    [{y,z}] (at most 2, likewise). What survives meets [M] in exactly one
    point. *)

Lemma tau_three_core :
  forall x y z, In [x;y;z] G -> x <> y -> x <> z -> y <> z -> length G <= 16.
Proof.
  intros x y z HMG Hxy Hxz Hyz.
  pose (R1 := filter (fun A => negb (containsb [x;y] A)) G).
  pose (R2 := filter (fun A => negb (containsb [x;z] A)) R1).
  pose (R3 := filter (fun A => negb (containsb [y;z] A)) R2).
  pose (R4 := filter (fun A => negb (memb x A)) R3).
  pose (Tx := filter (fun A => memb x A) R3).
  pose (Ty := filter (fun A => memb y A) R4).
  pose (Tz := filter (fun A => negb (memb y A)) R4).
  assert (ER1 : R1 = filter (fun A => negb (containsb [x;y] A)) G) by reflexivity.
  assert (ER2 : R2 = filter (fun A => negb (containsb [x;z] A)) R1) by reflexivity.
  assert (ER3 : R3 = filter (fun A => negb (containsb [y;z] A)) R2) by reflexivity.
  assert (ER4 : R4 = filter (fun A => negb (memb x A)) R3) by reflexivity.
  assert (ETx : Tx = filter (fun A => memb x A) R3) by reflexivity.
  assert (ETy : Ty = filter (fun A => memb y A) R4) by reflexivity.
  assert (ETz : Tz = filter (fun A => negb (memb y A)) R4) by reflexivity.
  (* the partition *)
  assert (E1 : length G = length (filter (containsb [x;y]) G) + length R1)
    by (rewrite ER1; apply length_filter_partition).
  assert (E2 : length R1 = length (filter (containsb [x;z]) R1) + length R2)
    by (rewrite ER2; apply length_filter_partition).
  assert (E3 : length R2 = length (filter (containsb [y;z]) R2) + length R3)
    by (rewrite ER3; apply length_filter_partition).
  assert (E4 : length R3 = length Tx + length R4)
    by (rewrite ER4, ETx; apply length_filter_partition).
  assert (E5 : length R4 = length Ty + length Tz)
    by (rewrite ETy, ETz; apply length_filter_partition).
  (* the three layer bounds *)
  assert (B1 : length (filter (containsb [x;y]) G) <= 3) by (apply (tt_pair Hxy)).
  assert (Hcxy : containsb [x;y] [x;y;z] = true)
    by (apply containsb_true_iff; intros t [<-|[<-|[]]]; simpl; tauto).
  assert (Hcxz : containsb [x;z] [x;y;z] = true)
    by (apply containsb_true_iff; intros t [<-|[<-|[]]]; simpl; tauto).
  assert (Hcyz : containsb [y;z] [x;y;z] = true)
    by (apply containsb_true_iff; intros t [<-|[<-|[]]]; simpl; tauto).
  assert (B2 : length (filter (containsb [x;z]) R1) + 1 <= 3).
  { rewrite ER1, filter_filter.
    eapply Nat.le_trans;
      [ apply Nat.add_le_mono_r;
        apply (@filter_length_mono _ _
                 (fun A => andb (containsb [x;z] A) (negb (containsb [x;y] A))));
        intros A HA H; apply Bool.andb_true_iff in H as [H1 H2];
        apply Bool.andb_true_iff; split; assumption |].
    apply (@minus_one_bound (containsb [x;z]) (containsb [x;y]) G [x;y;z] 3
             HMG Hcxz Hcxy (tt_pair Hxz)). }
  assert (B3 : length (filter (containsb [y;z]) R2) + 1 <= 3).
  { rewrite ER2, ER1, !filter_filter.
    eapply Nat.le_trans;
      [ apply Nat.add_le_mono_r;
        apply (@filter_length_mono _ _
                 (fun A => andb (containsb [y;z] A) (negb (containsb [x;y] A))));
        intros A HA H;
        apply Bool.andb_true_iff in H as [H1 H2];
        apply Bool.andb_true_iff in H2 as [H3 H4];
        apply Bool.andb_true_iff; split; assumption |].
    apply (@minus_one_bound (containsb [y;z]) (containsb [x;y]) G [x;y;z] 3
             HMG Hcyz Hcxy (tt_pair Hyz)). }
  (* what survives all three peels meets M in exactly one point *)
  assert (HR3 : forall A, In A R3 ->
            In A G /\ ~ Subset [x;y] A /\ ~ Subset [x;z] A /\ ~ Subset [y;z] A).
  { intros A HA; rewrite ER3 in HA; apply filter_In in HA as [HA2 Hn3].
    rewrite ER2 in HA2; apply filter_In in HA2 as [HA1 Hn2].
    rewrite ER1 in HA1; apply filter_In in HA1 as [HAG Hn1].
    apply Bool.negb_true_iff in Hn1, Hn2, Hn3.
    repeat split; try assumption;
      intros Hs; apply containsb_true_iff in Hs; congruence. }
  assert (HTx : forall A, In A Tx -> In A G /\ In x A /\ ~ In y A /\ ~ In z A).
  { intros A HA; rewrite ETx in HA; apply filter_In in HA as [HA3 Hx].
    apply memb_true_iff in Hx.
    destruct (HR3 A HA3) as [HAG [N1 [N2 _]]].
    repeat split; try assumption.
    - intros Hy; apply N1; intros t [<-|[<-|[]]]; assumption.
    - intros Hz; apply N2; intros t [<-|[<-|[]]]; assumption. }
  assert (HTy : forall A, In A Ty -> In A G /\ In y A /\ ~ In x A /\ ~ In z A).
  { intros A HA; rewrite ETy in HA; apply filter_In in HA as [HA4 Hy].
    apply memb_true_iff in Hy.
    rewrite ER4 in HA4; apply filter_In in HA4 as [HA3 Hnx].
    apply Bool.negb_true_iff in Hnx.
    assert (Hxn : ~ In x A)
      by (intros Hin; apply memb_true_iff in Hin; congruence).
    destruct (HR3 A HA3) as [HAG [_ [_ N3]]].
    repeat split; try assumption.
    intros Hz; apply N3; intros t [<-|[<-|[]]]; assumption. }
  assert (HTz : forall A, In A Tz -> In A G /\ In z A /\ ~ In x A /\ ~ In y A).
  { intros A HA; rewrite ETz in HA; apply filter_In in HA as [HA4 Hny].
    apply Bool.negb_true_iff in Hny.
    assert (Hyn : ~ In y A)
      by (intros Hin; apply memb_true_iff in Hin; congruence).
    rewrite ER4 in HA4; apply filter_In in HA4 as [HA3 Hnx].
    apply Bool.negb_true_iff in Hnx.
    assert (Hxn : ~ In x A)
      by (intros Hin; apply memb_true_iff in Hin; congruence).
    destruct (HR3 A HA3) as [HAG _].
    repeat split; try assumption.
    destruct (Hint A [x;y;z] HAG HMG) as [w [HwA Hw]].
    destruct Hw as [<-|[<-|[<-|[]]]]; [contradiction | contradiction | exact HwA]. }
  (* degrees only drop under filtering *)
  assert (HdTx : forall T, deg T Tx <= deg T G).
  { intros T; rewrite ETx, ER3, ER2, ER1.
    repeat (eapply Nat.le_trans; [apply deg_filter_le|]); apply Nat.le_refl. }
  assert (HdTy : forall T, deg T Ty <= deg T G).
  { intros T; rewrite ETy, ER4, ER3, ER2, ER1.
    repeat (eapply Nat.le_trans; [apply deg_filter_le|]); apply Nat.le_refl. }
  assert (HdTz : forall T, deg T Tz <= deg T G).
  { intros T; rewrite ETz, ER4, ER3, ER2, ER1.
    repeat (eapply Nat.le_trans; [apply deg_filter_le|]); apply Nat.le_refl. }
  (* all three are nonempty, else two points cover *)
  assert (Hnotc : forall (T C : list nat) (a : nat),
             In a T -> ~ In a C -> containsb T C = false).
  { intros T C a HaT HaC.
    destruct (containsb T C) eqn:E; [|reflexivity].
    exfalso; apply containsb_true_iff in E; apply HaC; apply E; exact HaT. }
  assert (Hpeel : forall C, In C G -> ~ In y C -> ~ In z C -> In C R3 /\ In x C).
  { intros C HCG Hny Hnz.
    assert (HxC : In x C).
    { destruct (Hint C [x;y;z] HCG HMG) as [w [HwC Hw]].
      destruct Hw as [<-|[<-|[<-|[]]]];
        [exact HwC | contradiction | contradiction]. }
    split; [|exact HxC].
    rewrite ER3, ER2, ER1; apply filter_In; split.
    - apply filter_In; split.
      + apply filter_In; split; [exact HCG|].
        apply Bool.negb_true_iff.
        apply (Hnotc [x;y] C y); [right; left; reflexivity | exact Hny].
      + apply Bool.negb_true_iff.
        apply (Hnotc [x;z] C z); [right; left; reflexivity | exact Hnz].
    - apply Bool.negb_true_iff.
      apply (Hnotc [y;z] C y); [left; reflexivity | exact Hny]. }
  assert (HnTx : Tx <> []).
  { destruct (Htau y z) as [C [HCG [Hny Hnz]]].
    destruct (Hpeel C HCG Hny Hnz) as [HC3 HxC].
    assert (HC : In C Tx)
      by (rewrite ETx; apply filter_In; split;
          [exact HC3 | apply memb_true_iff; exact HxC]).
    intros HE; rewrite HE in HC; exact HC. }
  assert (Hpeel' : forall C, In C G -> ~ In x C -> ~ In z C -> In C R3).
  { intros C HCG Hnx Hnz.
    rewrite ER3, ER2, ER1; apply filter_In; split.
    - apply filter_In; split.
      + apply filter_In; split; [exact HCG|].
        apply Bool.negb_true_iff.
        apply (Hnotc [x;y] C x); [left; reflexivity | exact Hnx].
      + apply Bool.negb_true_iff.
        apply (Hnotc [x;z] C x); [left; reflexivity | exact Hnx].
    - apply Bool.negb_true_iff.
      apply (Hnotc [y;z] C z); [right; left; reflexivity | exact Hnz]. }
  assert (Hpeel'' : forall C, In C G -> ~ In x C -> ~ In y C -> In C R3).
  { intros C HCG Hnx Hny.
    rewrite ER3, ER2, ER1; apply filter_In; split.
    - apply filter_In; split.
      + apply filter_In; split; [exact HCG|].
        apply Bool.negb_true_iff.
        apply (Hnotc [x;y] C x); [left; reflexivity | exact Hnx].
      + apply Bool.negb_true_iff.
        apply (Hnotc [x;z] C x); [left; reflexivity | exact Hnx].
    - apply Bool.negb_true_iff.
      apply (Hnotc [y;z] C y); [left; reflexivity | exact Hny]. }
  assert (Hin4 : forall C, In C R3 -> ~ In x C -> In C R4).
  { intros C HC3 Hnx.
    rewrite ER4; apply filter_In; split; [exact HC3|].
    apply Bool.negb_true_iff.
    destruct (memb x C) eqn:E;
      [exfalso; apply Hnx, memb_true_iff; exact E | reflexivity]. }
  assert (HnTy : Ty <> []).
  { destruct (Htau x z) as [C [HCG [Hnx Hnz]]].
    assert (HyC : In y C).
    { destruct (Hint C [x;y;z] HCG HMG) as [w [HwC Hw]].
      destruct Hw as [<-|[<-|[<-|[]]]];
        [contradiction | exact HwC | contradiction]. }
    pose proof (Hin4 C (Hpeel' C HCG Hnx Hnz) Hnx) as HC4.
    assert (HC : In C Ty)
      by (rewrite ETy; apply filter_In; split;
          [exact HC4 | apply memb_true_iff; exact HyC]).
    intros HE; rewrite HE in HC; exact HC. }
  assert (HnTz : Tz <> []).
  { destruct (Htau x y) as [C [HCG [Hnx Hny]]].
    pose proof (Hin4 C (Hpeel'' C HCG Hnx Hny) Hnx) as HC4.
    assert (HC : In C Tz)
      by (rewrite ETz; apply filter_In; split;
          [exact HC4 | apply Bool.negb_true_iff;
                       destruct (memb y C) eqn:E;
                       [exfalso; apply Hny, memb_true_iff; exact E
                        | reflexivity]]).
    intros HE; rewrite HE in HC; exact HC. }
  pose proof (@tails_bound x y z Tx Ty Tz Hxy Hxz Hyz HTx HTy HTz
                HdTx HdTy HdTz HnTx HnTy HnTz) as HL.
  lia.
Qed.

End TauThreeBound.

(** ** The theorem

    3-uniform, distinct, intersecting, covering number at least 3: at most
    16 members. No Rao condition, no Frankl, no axiom. *)

Theorem tau_three_bound :
  forall (G : Family),
    Uniform 3 G -> Distinct G ->
    (forall C D, In C G -> In D G -> exists w, In w C /\ In w D) ->
    (forall p q, exists C, In C G /\ ~ In p C /\ ~ In q C) ->
    length G <= 16.
Proof.
  intros G HU HD Hint Htau.
  destruct G as [|M G0] eqn:EG; [simpl; lia | rewrite <- EG in *].
  assert (HM : In M G) by (rewrite EG; left; reflexivity).
  destruct (@uniform_mem 3 G M HU HM) as [Hl Hnd].
  destruct M as [|x [|y [|z [|w M']]]]; simpl in Hl; try discriminate.
  destruct (nodup3 Hnd) as [Hxy [Hxz Hyz]].
  exact (@tau_three_core G HU HD Hint Htau x y z HM Hxy Hxz Hyz).
Qed.

(** ** The hypothesis, discharged *)

Theorem tau_three_at_most_sixteen : TauThreeAtMost 16.
Proof.
  intros G HU HD Hint Htau; exact (@tau_three_bound G HU HD Hint Htau).
Qed.

(** Frankl's theorem is no longer needed for any of what depended on it. *)

Theorem r_star_three_three_at_most_four_unconditional :
  SpreadYieldsDisjoint 3 3 4.
Proof.
  apply r_star_three_three_at_most_four, tau_three_at_most_sixteen.
Qed.

Corollary f_three_three_unconditional : UpperBound 3 3 65.
Proof. apply f_three_three_from_frankl, tau_three_at_most_sixteen. Qed.

(** [I(3,r) <= r^2] for every [r >= 4]: the star is extremal at [m = 3]
    from [r = m+1] on. This is the [m = 3] row of §24.13's conjecture,
    proved -- [tau <= 2] in [TwoCover.covered_by_two_at_most_star] and
    [tau = 3] here. *)

Theorem intersecting_at_most_star_unconditional :
  forall r (G : Family),
    4 <= r ->
    Uniform 3 G -> RaoSpread 3 G r ->
    (forall C D, In C G -> In D G -> exists x, In x C /\ In x D) ->
    length G <= r * r.
Proof.
  intros r G Hr HU HR Hint.
  apply (@intersecting_at_most_star 16 tau_three_at_most_sixteen r G);
    [nia | exact Hr | exact HU | exact HR | exact Hint].
Qed.

Theorem three_uniform_star_extremal : forall r, 4 <= r -> StarExtremalAt 3 r.
Proof.
  intros r Hr H HU HR Hint.
  pose proof (@intersecting_at_most_star_unconditional r H Hr HU HR Hint).
  simpl; lia.
Qed.

(** ** Sharp: a 16-member witness at [(m,r) = (3,4)]

    The upper bound above is attained, so [I(3,4) = 16] exactly. The
    witness is the "grid star": a common point [0] together with one point
    from each of two blocks of size 4. Rao's condition holds with equality
    at [{0}] and at every pair through [0]. *)

Definition star34 : Family :=
  [ [0;1;5];[0;1;6];[0;1;7];[0;1;8];
    [0;2;5];[0;2;6];[0;2;7];[0;2;8];
    [0;3;5];[0;3;6];[0;3;7];[0;3;8];
    [0;4;5];[0;4;6];[0;4;7];[0;4;8] ].

Definition int_b (F : Family) : bool :=
  forallb (fun C => forallb (fun D => negb (disjointb C D)) F) F.

Lemma int_b_correct :
  forall F, int_b F = true ->
    forall C D, In C F -> In D F -> exists x, In x C /\ In x D.
Proof.
  intros F H C D HC HD; unfold int_b in H.
  rewrite forallb_forall in H; specialize (H C HC).
  rewrite forallb_forall in H; specialize (H D HD).
  apply Bool.negb_true_iff in H; apply disjointb_false_iff in H; exact H.
Qed.

Theorem star34_attains_sixteen :
  Uniform 3 star34 /\ Distinct star34 /\ RaoSpread 3 star34 4 /\
  (forall C D, In C star34 -> In D star34 -> exists x, In x C /\ In x D) /\
  length star34 = 16.
Proof.
  assert (HUst : Uniform 3 star34)
    by (apply uniformb_correct; vm_compute; reflexivity).
  assert (HDst : Distinct star34)
    by (apply distinctb_correct; vm_compute; reflexivity).
  assert (HRst : RaoSpread 3 star34 4).
  { apply (@rao_spreadb_correct 3 star34 4 [0;1;2;3;4;5;6;7;8]).
    - apply nodupb_correct; vm_compute; reflexivity.
    - apply Forall_forall; intros A HA.
      destruct (@uniform_mem 3 star34 A HUst HA) as [_ Hnd]; exact Hnd.
    - intros A HA; apply subsetb_correct; unfold star34 in HA; simpl in HA.
      repeat (destruct HA as [<-|HA]; [vm_compute; reflexivity|]); contradiction.
    - vm_compute; reflexivity. }
  assert (HIst : forall C D, In C star34 -> In D star34 ->
                   exists x, In x C /\ In x D)
    by (apply int_b_correct; vm_compute; reflexivity).
  exact (conj HUst (conj HDst (conj HRst (conj HIst eq_refl)))).
Qed.

(** ** The old hypothesis, refuted

    Without [Distinct], the statement is false for every constant. Every
    hypothesis it carries is preserved by repeating a family, and the
    length is not. *)

Definition fano : Family :=
  [[0;1;2];[0;3;4];[0;5;6];[1;3;5];[1;4;6];[2;3;6];[2;4;5]].

Fixpoint repeatf (n : nat) (F : Family) : Family :=
  match n with 0 => [] | S n' => F ++ repeatf n' F end.

Lemma repeatf_in : forall n F C, In C (repeatf n F) -> In C F.
Proof.
  induction n as [|n IH]; intros F C H; simpl in H; [contradiction|].
  apply in_app_or in H as [H|H]; [exact H | apply (IH F C H)].
Qed.

Lemma repeatf_in_rev : forall n F C, In C F -> 1 <= n -> In C (repeatf n F).
Proof.
  intros n F C H Hn; destruct n; [lia|].
  simpl; apply in_or_app; left; exact H.
Qed.

Lemma repeatf_length : forall n F, length (repeatf n F) = n * length F.
Proof.
  induction n as [|n IH]; intros F; simpl; [reflexivity|].
  rewrite app_length, IH; reflexivity.
Qed.

Lemma repeatf_uniform : forall n k F, Uniform k F -> Uniform k (repeatf n F).
Proof.
  induction n as [|n IH]; intros k F H; simpl; [constructor|].
  apply Forall_app; split; [exact H | apply (IH k F H)].
Qed.

Lemma fano_bounded : forall C, In C fano -> forall x, In x C -> x < 7.
Proof.
  intros C HC x Hx; unfold fano in HC; simpl in HC.
  repeat (destruct HC as [<-|HC];
          [destruct Hx as [<-|[<-|[<-|[]]]]; lia |]); contradiction.
Qed.

Lemma fano_exists_missing :
  forall a b, a < 8 -> b < 8 ->
    existsb (fun C => andb (negb (memb a C)) (negb (memb b C))) fano = true.
Proof.
  intros a b Ha Hb.
  do 8 (destruct a as [|a];
        [ do 8 (destruct b as [|b]; [vm_compute; reflexivity|]); exfalso; lia |]);
    exfalso; lia.
Qed.

Lemma fano_memb_min :
  forall p C, In C fano -> memb p C = memb (Nat.min p 7) C.
Proof.
  intros p C HC; destruct (le_lt_dec 7 p) as [Hle|Hlt].
  - rewrite Nat.min_r by lia.
    assert (E1 : memb p C = false).
    { destruct (memb p C) eqn:E; [|reflexivity].
      exfalso; apply memb_true_iff in E; pose proof (@fano_bounded C HC p E); lia. }
    assert (E2 : memb 7 C = false).
    { destruct (memb 7 C) eqn:E; [|reflexivity].
      exfalso; apply memb_true_iff in E; pose proof (@fano_bounded C HC 7 E); lia. }
    rewrite E1, E2; reflexivity.
  - rewrite Nat.min_l by lia; reflexivity.
Qed.

Lemma fano_tau_three :
  forall p q, exists C, In C fano /\ ~ In p C /\ ~ In q C.
Proof.
  intros p q.
  pose proof (fano_exists_missing (a := Nat.min p 7) (b := Nat.min q 7)
                ltac:(pose proof (Nat.le_min_r p 7); lia)
                ltac:(pose proof (Nat.le_min_r q 7); lia)) as Hex.
  apply existsb_exists in Hex as [C [HC Hcond]].
  apply Bool.andb_true_iff in Hcond as [H1 H2].
  apply Bool.negb_true_iff in H1; apply Bool.negb_true_iff in H2.
  exists C; repeat split; [exact HC | | ];
    intros Hin; apply memb_true_iff in Hin;
    rewrite (fano_memb_min _ HC) in Hin; congruence.
Qed.

Definition TauThreeAtMostUnguarded (K : nat) : Prop :=
  forall (G : Family),
    Uniform 3 G ->
    (forall C D, In C G -> In D G -> exists x, In x C /\ In x D) ->
    (forall p q, exists C, In C G /\ ~ In p C /\ ~ In q C) ->
    length G <= K.

Theorem tau_three_at_most_unguarded_is_false :
  forall K, ~ TauThreeAtMostUnguarded K.
Proof.
  intros K H.
  assert (Hb : length (repeatf (S K) fano) <= K).
  { apply H.
    - apply repeatf_uniform; apply uniformb_correct; vm_compute; reflexivity.
    - intros C D HC HD.
      apply (@int_b_correct fano ltac:(vm_compute; reflexivity));
        [apply (@repeatf_in (S K) fano C HC) | apply (@repeatf_in (S K) fano D HD)].
    - intros p q; destruct (fano_tau_three p q) as [C [HC [H1 H2]]].
      exists C; repeat split; try assumption.
      apply (@repeatf_in_rev (S K) fano C HC); lia. }
  rewrite repeatf_length in Hb; simpl in Hb; lia.
Qed.
