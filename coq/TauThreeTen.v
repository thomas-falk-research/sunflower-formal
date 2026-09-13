(** * TauThreeTen.v -- the covering-number-three case, tight: ten

    [TauThree.tau_three_bound] gives sixteen for a 3-uniform intersecting
    family of distinct members with covering number at least 3, with no
    appeal to Frankl. The truth is ten (Frankl; attained by the ten
    3-subsets of a 5-set), and ten is what the [r*(3,3)] chain of
    docs/roadmap.md section 56 assumes as "Frankl's value" -- the one
    cited, unformalised ingredient of the conditional decision there.
    This file proves ten, elementary and unconditional, so that the
    condition becomes a theorem.

    ** The argument

    Fix a member [M = {x,y,z}]. Every member meets [M]; distinctness says
    only [M] contains all three points. The members containing exactly
    two points of [M], say [{x,y,w}], have their third point [w] in
    *every* tail of the [z]-layer [T_z] (the tails being the two points
    outside [M] of the members meeting [M] only in [z]), since [{x,y,w}]
    must meet each [{z} ∪ f] outside [M]. So the two-point layers are
    counted by the *cores* of the three tail graphs -- the points common
    to all edges -- and

<<
      |G| <= 1 + Σ_i (|T_i| + core(T_i)).
>>

    The tail graphs are nonempty (covering number 3) and pairwise
    cross-intersecting (the family is intersecting). The graph lemma
    [nine] bounds the sum by nine:

    - if no tail graph has two disjoint edges, each is a star or a
      triangle; a star with three or more edges at [c] forces every edge
      of the other two graphs through [c], and then no member avoids
      both [x] and [c], against covering number 3; otherwise each graph
      has [|T| + core(T) <= 3] (an edge with core 2, a two-edge star with
      core 1, a triangle with core 0);
    - if some tail graph, say [T_x], has two disjoint edges [{a,a'}] and
      [{b,b'}], every edge of [T_y], [T_z] is a cross edge [{a or a', b or b'}];
      if [T_y] and [T_z] have no disjoint edges between them they share a
      vertex [c], and again nothing avoids [x] and [c]; if [T_y] has the
      disjoint edges [{a,b}], [{a',b'}] then [T_x ⊆ {aa', ab', a'b, bb'}],
      [T_z ⊆ {ab', a'b}], the two candidates for [T_z] are disjoint so at
      most one kind appears outside [T_z], and the sum is at most nine.

    No degree cap is used anywhere: the theorem is exactly Frankl's
    statement for [k = 3]. *)

From Coq Require Import List Arith Lia Bool.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower Pigeonhole Spread SpreadReduction
     DirectSum Reflect SpreadThreshold TwoCover TwoCoverSharp TauThree.
Import ListNotations.

Set Implicit Arguments.

(** ** Graphs: lists of 2-sets with no repeated edge *)

Definition Simple (T : Family) : Prop :=
  Uniform 2 T /\ forall S, NoDup S -> length S = 2 -> deg S T <= 1.

(** The points of [e] lying in every edge of [T]. *)

Definition core_count (e : list nat) (T : Family) : nat :=
  length (filter (fun v => forallb (memb v) T) e).

(** Covering number 3, seen from the tail graph of one point: for every
    [c], some member avoids [x] and [c] -- either a member of another
    layer whose tail avoids [c], or a two-point member [{y,z,w}] with
    [w <> c], whose [w] lies in every tail of [T_x] (and so in [ex]). *)

Definition Tau2 (Tx : Family) (ex : list nat) (Ty Tz : Family) : Prop :=
  forall c,
    (exists e, (In e Ty \/ In e Tz) /\ ~ In c e)
    \/ (exists w, In w ex /\ (forall f, In f Tx -> In w f) /\ w <> c).

Lemma Tau2_swap : forall Tx ex Ty Tz, Tau2 Tx ex Ty Tz -> Tau2 Tx ex Tz Ty.
Proof.
  intros Tx ex Ty Tz H c; destruct (H c) as [[e [[He|He] Hc]] | H2];
    [left; exists e; tauto | left; exists e; tauto | right; exact H2].
Qed.

(** ** Facts about 2-sets *)

Lemma edge_points :
  forall (T : Family) f, Uniform 2 T -> In f T ->
    exists a b, a <> b /\ In a f /\ In b f /\ (forall y, In y f -> y = a \/ y = b).
Proof.
  intros T f HU Hf.
  destruct (@uniform_mem 2 T f HU Hf) as [Hl Hnd].
  exact (@two_uniform_split f Hl Hnd).
Qed.

Lemma edge_pin :
  forall (T : Family) f a b, Uniform 2 T -> In f T -> In a f -> In b f -> a <> b ->
    forall y, In y f -> y = a \/ y = b.
Proof.
  intros T f a b HU Hf Ha Hb Hab.
  destruct (@uniform_mem 2 T f HU Hf) as [Hl Hnd].
  exact (@two_uniform_pair f a b Hl Hnd Ha Hb Hab).
Qed.

(** Every edge of [T] is one of the 2-sets listed in [L]: at most
    [length L] edges. *)

Lemma edges_among :
  forall (T : Family) (L : list (list nat)),
    Simple T ->
    (forall S, In S L -> NoDup S /\ length S = 2) ->
    (forall f, In f T -> exists S, In S L /\ Subset S f) ->
    length T <= length L.
Proof.
  intros T L [HU Hsimp] HL Hcov.
  assert (H : length T <= length L * 1).
  { apply cover_by_sets; [exact Hcov|].
    intros S HS; destruct (HL S HS) as [Hnd Hl]; apply Hsimp; assumption. }
  lia.
Qed.

Lemma subset2 : forall a b (f : list nat), In a f -> In b f -> Subset [a; b] f.
Proof. intros a b f Ha Hb y [<-|[<-|[]]]; assumption. Qed.

(** ** Core counts *)

Lemma filter_le : forall (X : Type) (p : X -> bool) (l : list X),
    length (filter p l) <= length l.
Proof.
  intros X p l; induction l as [|a l IH]; simpl; [lia | destruct (p a); simpl; lia].
Qed.

Lemma core_count_le_two :
  forall e (T : Family), length e = 2 -> core_count e T <= 2.
Proof.
  intros e T Hl; unfold core_count.
  pose proof (filter_le (fun v => forallb (memb v) T) e) as H.
  lia.
Qed.

Lemma forallb_memb_true :
  forall v (T : Family), forallb (memb v) T = true <-> forall f, In f T -> In v f.
Proof.
  intros v T; rewrite forallb_forall; split; intros H f Hf;
    [apply memb_true_iff; exact (H f Hf) | apply memb_true_iff; exact (H f Hf)].
Qed.

(** A point outside some edge is not in the core. *)

Lemma core_count_drop :
  forall e (T : Family) a b f,
    length e = 2 -> NoDup e -> (forall y, In y e -> y = a \/ y = b) ->
    In f T -> ~ In a f ->
    core_count e T <= (if forallb (memb b) T then 1 else 0).
Proof.
  intros e T a b f Hl Hnd Hab Hf Hna; unfold core_count.
  assert (Ha : forallb (memb a) T = false).
  { destruct (forallb (memb a) T) eqn:E; [|reflexivity].
    exfalso; apply Hna; rewrite forallb_memb_true in E; exact (E f Hf). }
  destruct e as [|v [|w [|? ?]]]; simpl in Hl; try discriminate.
  assert (Hvw : v <> w)
    by (inversion Hnd as [|? ? Hni _]; subst; intros <-; apply Hni; left; reflexivity).
  simpl.
  destruct (Hab v (or_introl eq_refl)) as [Ev|Ev];
    destruct (Hab w (or_intror (or_introl eq_refl))) as [Ew|Ew]; subst;
    try (exfalso; apply Hvw; reflexivity);
    rewrite ?Ha; destruct (forallb (memb b) T); simpl; lia.
Qed.

Lemma core_count_zero :
  forall e (T : Family) f g,
    length e = 2 -> In f T -> In g T ->
    (forall w, In w f -> ~ In w g) ->
    core_count e T = 0.
Proof.
  intros e T f g Hl Hf Hg Hdis; unfold core_count.
  assert (Hall : forall v, forallb (memb v) T = false).
  { intros v; destruct (forallb (memb v) T) eqn:E; [|reflexivity].
    exfalso; rewrite forallb_memb_true in E.
    exact (Hdis v (E f Hf) (E g Hg)). }
  destruct e as [|v [|w [|? ?]]]; simpl in Hl; try discriminate.
  simpl; rewrite !Hall; reflexivity.
Qed.

(** ** Two disjoint edges in one graph pin the other graphs to cross edges *)

Definition Disjoint (f g : list nat) : Prop := forall w, In w f -> ~ In w g.

(** [f] meets both [{a,a'}] and [{b,b'}] (which are disjoint): its two
    points are one from each. *)

Lemma cross_edge :
  forall (T : Family) f a a' b b',
    Uniform 2 T -> In f T ->
    a <> a' -> b <> b' -> a <> b -> a <> b' -> a' <> b -> a' <> b' ->
    (exists w, In w f /\ (w = a \/ w = a')) ->
    (exists w, In w f /\ (w = b \/ w = b')) ->
    (In a f \/ In a' f) /\ (In b f \/ In b' f)
    /\ ~ (In a f /\ In a' f) /\ ~ (In b f /\ In b' f).
Proof.
  intros T f a a' b b' HU Hf Haa Hbb Hab Hab' Ha'b Ha'b' [u [Hu Hu2]] [v [Hv Hv2]].
  repeat split.
  - destruct Hu2 as [<-|<-]; tauto.
  - destruct Hv2 as [<-|<-]; tauto.
  - intros [H1 H2].
    pose proof (@edge_pin T f a a' HU Hf H1 H2 Haa v Hv) as Hv3.
    destruct Hv2 as [<-|<-]; destruct Hv3; congruence.
  - intros [H1 H2].
    pose proof (@edge_pin T f b b' HU Hf H1 H2 Hbb u Hu) as Hu3.
    destruct Hu2 as [<-|<-]; destruct Hu3; congruence.
Qed.

Lemma core_count_drop2 :
  forall e (T : Family) a b f g,
    length e = 2 -> NoDup e -> (forall y, In y e -> y = a \/ y = b) ->
    In f T -> ~ In a f -> In g T -> ~ In b g ->
    core_count e T = 0.
Proof.
  intros e T a b f g Hl Hnd Hab Hf Hna Hg Hnb.
  pose proof (@core_count_drop e T a b f Hl Hnd Hab Hf Hna) as H.
  assert (Hb : forallb (memb b) T = false).
  { destruct (forallb (memb b) T) eqn:E; [|reflexivity].
    exfalso; apply Hnb; rewrite forallb_memb_true in E; exact (E g Hg). }
  rewrite Hb in H; lia.
Qed.

(** ** Internally intersecting graphs *)

Definition IntGraph (T : Family) : Prop :=
  forall f g, In f T -> In g T -> exists w, In w f /\ In w g.

Definition meetb (f g : list nat) : bool := existsb (fun w => memb w g) f.

Lemma meetb_true_iff : forall f g, meetb f g = true <-> exists w, In w f /\ In w g.
Proof.
  intros f g; unfold meetb; rewrite existsb_exists; split;
    intros [w [H1 H2]]; exists w; split; try assumption;
    [apply memb_true_iff; exact H2 | apply memb_true_iff; exact H2].
Qed.

Definition has_disj (T : Family) : bool :=
  existsb (fun f => existsb (fun g => negb (meetb f g)) T) T.

Lemma has_disj_true :
  forall T, has_disj T = true -> exists f g, In f T /\ In g T /\ Disjoint f g.
Proof.
  intros T H; unfold has_disj in H.
  apply existsb_exists in H as [f [Hf H]].
  apply existsb_exists in H as [g [Hg H]].
  exists f, g; repeat split; try assumption.
  intros w Hwf Hwg; apply Bool.negb_true_iff in H.
  assert (E : meetb f g = true) by (apply meetb_true_iff; exists w; tauto).
  congruence.
Qed.

Lemma has_disj_false : forall T, has_disj T = false -> IntGraph T.
Proof.
  intros T H f g Hf Hg.
  pose proof (existsb_false_forall _ _ _ H f Hf) as H1.
  pose proof (existsb_false_forall _ _ _ H1 g Hg) as H2.
  apply Bool.negb_false_iff in H2; apply meetb_true_iff in H2; exact H2.
Qed.

(** ** Case A: an intersecting graph is small, or a star with three leaves *)

Lemma star_or_small :
  forall (T : Family) e a b,
    Simple T -> In e T -> In a e -> In b e -> a <> b ->
    (forall y, In y e -> y = a \/ y = b) ->
    (forall f, In f T -> In a f) ->
    length T + core_count e T <= 3
    \/ exists u1 u2, u1 <> u2 /\ u1 <> a /\ u2 <> a /\ u1 <> b /\ u2 <> b /\
         (exists f1, In f1 T /\ In u1 f1) /\ (exists f2, In f2 T /\ In u2 f2).
Proof.
  intros T e a b HS He Ha Hb Hab Hpin Halla.
  pose proof HS as [HU _].
  destruct (@uniform_mem 2 T e HU He) as [Hle Hnde].
  destruct (existsb (fun f => negb (memb b f)) T) eqn:Eb.
  - apply existsb_exists in Eb as [f1 [Hf1 Hnb1]].
    apply Bool.negb_true_iff, memb_false_iff in Hnb1.
    destruct (@edge_points T f1 HU Hf1) as [p [q [Hpq [Hp [Hq Hpin1]]]]].
    pose proof (Halla f1 Hf1) as Ha1.
    (* the leaf of f1: the point of f1 other than a *)
    assert (Hleaf : exists u1, In u1 f1 /\ u1 <> a /\ u1 <> b).
    { destruct (Hpin1 a Ha1) as [<-|<-].
      - exists q; repeat split; [exact Hq | intros <-; apply Hpq; reflexivity
                                | intros <-; exact (Hnb1 Hq)].
      - exists p; repeat split; [exact Hp | intros <-; apply Hpq; reflexivity
                                | intros <-; exact (Hnb1 Hp)]. }
    destruct Hleaf as [u1 [Hu1 [Hu1a Hu1b]]].
    destruct (existsb (fun f => andb (negb (memb b f)) (negb (memb u1 f))) T) eqn:Eu.
    + apply existsb_exists in Eu as [f2 [Hf2 H2]].
      apply Bool.andb_true_iff in H2 as [Hnb2 Hnu2].
      apply Bool.negb_true_iff, memb_false_iff in Hnb2, Hnu2.
      destruct (@edge_points T f2 HU Hf2) as [p2 [q2 [Hpq2 [Hp2 [Hq2 Hpin2]]]]].
      pose proof (Halla f2 Hf2) as Ha2.
      assert (Hleaf2 : exists u2, In u2 f2 /\ u2 <> a /\ u2 <> b /\ u2 <> u1).
      { destruct (Hpin2 a Ha2) as [<-|<-].
        - exists q2; repeat split;
            [exact Hq2 | intros <-; apply Hpq2; reflexivity
             | intros <-; exact (Hnb2 Hq2) | intros <-; exact (Hnu2 Hq2)].
        - exists p2; repeat split;
            [exact Hp2 | intros <-; apply Hpq2; reflexivity
             | intros <-; exact (Hnb2 Hp2) | intros <-; exact (Hnu2 Hp2)]. }
      destruct Hleaf2 as [u2 [Hu2 [Hu2a [Hu2b Hu21]]]].
      right; exists u1, u2; repeat split; try assumption.
      * intros E; apply Hu21; symmetry; exact E.
      * exists f1; tauto.
      * exists f2; tauto.
    + (* every edge contains b or u1, and a: T ⊆ {ab, au1} *)
      left.
      assert (HT : length T <= 2).
      { change 2 with (length [[a;b];[a;u1]]).
        apply edges_among; [exact HS| |].
        - intros S [<-|[<-|[]]]; split; try reflexivity;
            apply pair_nodup; [exact Hab | intros E; apply Hu1a; symmetry; exact E].
        - intros f Hf.
          pose proof (existsb_false_forall _ _ _ Eu f Hf) as E.
          apply Bool.andb_false_iff in E.
          destruct E as [E|E]; apply Bool.negb_false_iff, memb_true_iff in E.
          + exists [a;b]; split; [left; reflexivity | apply subset2; [apply Halla; exact Hf | exact E]].
          + exists [a;u1]; split; [right; left; reflexivity | apply subset2; [apply Halla; exact Hf | exact E]]. }
      assert (Hc : core_count e T <= 1).
      { pose proof (@core_count_drop e T b a f1 Hle Hnde
                      ltac:(intros y Hy; destruct (Hpin y Hy); tauto) Hf1 Hnb1) as H.
        destruct (forallb (memb a) T); lia. }
      lia.
  - (* every edge contains both a and b: T ⊆ {ab} *)
    left.
    assert (HT : length T <= 1).
    { change 1 with (length [[a;b]]).
      apply edges_among; [exact HS| |].
      - intros S [<-|[]]; split; [apply pair_nodup; exact Hab | reflexivity].
      - intros f Hf; exists [a;b]; split; [left; reflexivity|].
        pose proof (existsb_false_forall _ _ _ Eb f Hf) as E.
        apply Bool.negb_false_iff, memb_true_iff in E.
        apply subset2; [apply Halla; exact Hf | exact E]. }
    pose proof (@core_count_le_two e T Hle); lia.
Qed.

Lemma int_graph_bound :
  forall (T : Family) e,
    Simple T -> IntGraph T -> In e T ->
    length T + core_count e T <= 3
    \/ exists c u1 u2 u3,
         (forall f, In f T -> In c f) /\
         u1 <> u2 /\ u1 <> u3 /\ u2 <> u3 /\ u1 <> c /\ u2 <> c /\ u3 <> c /\
         (exists f, In f T /\ In u1 f) /\ (exists f, In f T /\ In u2 f) /\
         (exists f, In f T /\ In u3 f).
Proof.
  intros T e HS HI He.
  pose proof HS as [HU _].
  destruct (@edge_points T e HU He) as [a [b [Hab [Ha [Hb Hpin]]]]].
  destruct (@uniform_mem 2 T e HU He) as [Hle Hnde].
  destruct (existsb (fun f => negb (memb a f)) T) eqn:Ea.
  - apply existsb_exists in Ea as [f0 [Hf0 Hna0]].
    apply Bool.negb_true_iff, memb_false_iff in Hna0.
    assert (Hb0 : In b f0).
    { destruct (HI f0 e Hf0 He) as [w [Hw0 Hwe]].
      destruct (Hpin w Hwe) as [<-|<-]; [contradiction | exact Hw0]. }
    destruct (existsb (fun f => negb (memb b f)) T) eqn:Eb.
    + apply existsb_exists in Eb as [g0 [Hg0 Hnb0]].
      apply Bool.negb_true_iff, memb_false_iff in Hnb0.
      assert (Ha0' : In a g0).
      { destruct (HI g0 e Hg0 He) as [w [Hw0 Hwe]].
        destruct (Hpin w Hwe) as [<-|<-]; [exact Hw0 | contradiction]. }
      (* f0 = {b,u}, g0 = {a,v}, and they meet, so u = v *)
      destruct (@edge_points T f0 HU Hf0) as [p [q [Hpq [Hp [Hq Hpin0]]]]].
      assert (Hu : exists u, In u f0 /\ u <> b /\ u <> a).
      { destruct (Hpin0 b Hb0) as [<-|<-].
        - exists q; repeat split; [exact Hq | intros <-; apply Hpq; reflexivity | intros <-; exact (Hna0 Hq)].
        - exists p; repeat split; [exact Hp | intros <-; apply Hpq; reflexivity | intros <-; exact (Hna0 Hp)]. }
      destruct Hu as [u [Hu [Hub Hua]]].
      assert (Hug : In u g0).
      { destruct (HI f0 g0 Hf0 Hg0) as [w [Hw0 Hwg]].
        pose proof (@edge_pin T f0 b u HU Hf0 Hb0 Hu ltac:(intros E; apply Hub; symmetry; exact E) w Hw0) as Hw.
        destruct Hw as [<-|<-]; [contradiction | exact Hwg]. }
      left.
      assert (HT : length T <= 3).
      { change 3 with (length [[a;b];[a;u];[b;u]]).
        apply edges_among; [exact HS| |].
        - intros S [<-|[<-|[<-|[]]]]; split; try reflexivity; apply pair_nodup;
            [exact Hab | intros E; apply Hua; symmetry; exact E
             | intros E; apply Hub; symmetry; exact E].
        - intros h Hh.
          destruct (HI h e Hh He) as [w [Hwh Hwe]].
          destruct (memb a h) eqn:Eah; destruct (memb b h) eqn:Ebh.
          + apply memb_true_iff in Eah, Ebh.
            exists [a;b]; split; [left; reflexivity | apply subset2; assumption].
          + apply memb_true_iff in Eah; apply memb_false_iff in Ebh.
            (* h meets f0 = {b,u} not at b *)
            destruct (HI h f0 Hh Hf0) as [w' [Hw'h Hw'0]].
            pose proof (@edge_pin T f0 b u HU Hf0 Hb0 Hu ltac:(intros E; apply Hub; symmetry; exact E) w' Hw'0) as Hw'.
            destruct Hw' as [<-|<-]; [contradiction|].
            exists [a;w']; split; [right; left; reflexivity | apply subset2; assumption].
          + apply memb_false_iff in Eah; apply memb_true_iff in Ebh.
            destruct (HI h g0 Hh Hg0) as [w' [Hw'h Hw'0]].
            pose proof (@edge_pin T g0 a u HU Hg0 Ha0' Hug ltac:(intros E; apply Hua; symmetry; exact E) w' Hw'0) as Hw'.
            destruct Hw' as [<-|<-]; [contradiction|].
            exists [b;w']; split; [right; right; left; reflexivity | apply subset2; assumption].
          + apply memb_false_iff in Eah, Ebh.
            destruct (Hpin w Hwe) as [<-|<-]; contradiction. }
      pose proof (@core_count_drop2 e T a b f0 g0 Hle Hnde Hpin Hf0 Hna0 Hg0 Hnb0); lia.
    + (* every edge contains b *)
      assert (Hallb : forall f, In f T -> In b f).
      { intros f Hf; pose proof (existsb_false_forall _ _ _ Eb f Hf) as E.
        apply Bool.negb_false_iff, memb_true_iff in E; exact E. }
      destruct (@star_or_small T e b a HS He Hb Ha ltac:(intros E; apply Hab; symmetry; exact E)
                  ltac:(intros y Hy; destruct (Hpin y Hy); tauto) Hallb) as [Hsmall | [u1 [u2 [H12 [H1b [H2b [H1a [H2a [Hf1 Hf2]]]]]]]]].
      * left; exact Hsmall.
      * right; exists b, u1, u2, a; repeat split; try assumption; try congruence;
          try (exists e; tauto).
  - (* every edge contains a *)
    assert (Halla : forall f, In f T -> In a f).
    { intros f Hf; pose proof (existsb_false_forall _ _ _ Ea f Hf) as E.
      apply Bool.negb_false_iff, memb_true_iff in E; exact E. }
    destruct (@star_or_small T e a b HS He Ha Hb Hab Hpin Halla) as [Hsmall | [u1 [u2 [H12 [H1a [H2a [H1b [H2b [Hf1 Hf2]]]]]]]]].
    + left; exact Hsmall.
    + right; exists a, u1, u2, b; repeat split; try assumption; try congruence;
        try (exists e; tauto).
Qed.

(** A three-leaf star at [c] forces the other graphs through [c], and
    covering number 3 then fails at the pair [{x, c}]. *)

Lemma star_contra :
  forall (Tx Ty Tz : Family) ex c u1 u2 u3,
    Uniform 2 Tx -> Uniform 2 Ty -> Uniform 2 Tz ->
    CrossInt Tx Ty -> CrossInt Tx Tz ->
    Tau2 Tx ex Ty Tz ->
    (forall f, In f Tx -> In c f) ->
    u1 <> u2 -> u1 <> u3 -> u2 <> u3 -> u1 <> c -> u2 <> c -> u3 <> c ->
    (exists f, In f Tx /\ In u1 f) -> (exists f, In f Tx /\ In u2 f) ->
    (exists f, In f Tx /\ In u3 f) ->
    False.
Proof.
  intros Tx Ty Tz ex c u1 u2 u3 HUx HUy HUz Hxy Hxz H2 Hallc
         H12 H13 H23 H1c H2c H3c [f1 [Hf1 Hu1]] [f2 [Hf2 Hu2]] [f3 [Hf3 Hu3]].
  (* an edge of another graph meeting f_i off c contains u_i *)
  assert (Hleaf : forall f u, In f Tx -> In u f -> u <> c ->
                  forall e, (exists w, In w e /\ In w f) -> ~ In c e -> In u e).
  { intros f u Hf Hu Huc e [w [Hwe Hwf]] Hce.
    pose proof (@edge_pin Tx f c u HUx Hf (Hallc f Hf) Hu
                  ltac:(intros E; apply Huc; symmetry; exact E) w Hwf) as Hw.
    destruct Hw as [<-|<-]; [contradiction | exact Hwe]. }
  destruct (H2 c) as [[e [He Hce]] | [w [Hwex [Hwall Hwc]]]].
  - assert (Hmeet : forall f, In f Tx -> exists w, In w e /\ In w f).
    { intros f Hf; destruct He as [He|He].
      - destruct (Hxy f e Hf He) as [w [H1 H2']]; exists w; tauto.
      - destruct (Hxz f e Hf He) as [w [H1 H2']]; exists w; tauto. }
    assert (HUe : Uniform 2 (e :: nil)).
    { destruct He as [He|He].
      - destruct (@uniform_mem 2 Ty e HUy He) as [Hl Hnd]; constructor; [split; assumption | constructor].
      - destruct (@uniform_mem 2 Tz e HUz He) as [Hl Hnd]; constructor; [split; assumption | constructor]. }
    destruct (@edge_points (e :: nil) e HUe (or_introl eq_refl)) as [p [q [Hpq [Hp [Hq Hpin]]]]].
    pose proof (Hleaf f1 u1 Hf1 Hu1 H1c e (Hmeet f1 Hf1) Hce) as E1.
    pose proof (Hleaf f2 u2 Hf2 Hu2 H2c e (Hmeet f2 Hf2) Hce) as E2.
    pose proof (Hleaf f3 u3 Hf3 Hu3 H3c e (Hmeet f3 Hf3) Hce) as E3.
    destruct (Hpin u1 E1) as [<-|<-]; destruct (Hpin u2 E2) as [E|E];
      destruct (Hpin u3 E3) as [E'|E']; congruence.
  - pose proof (Hwall f1 Hf1) as Hw1; pose proof (Hwall f2 Hf2) as Hw2.
    pose proof (@edge_pin Tx f1 c u1 HUx Hf1 (Hallc f1 Hf1) Hu1
                  ltac:(intros E; apply H1c; symmetry; exact E) w Hw1) as E1.
    pose proof (@edge_pin Tx f2 c u2 HUx Hf2 (Hallc f2 Hf2) Hu2
                  ltac:(intros E; apply H2c; symmetry; exact E) w Hw2) as E2.
    destruct E1 as [<-|<-]; [apply Hwc; reflexivity|].
    destruct E2 as [E|E]; [apply H1c; exact E | apply H12; exact E].
Qed.

(** ** Case B: some tail graph has two disjoint edges *)

(** Two disjoint edges [{a,a'}] and [{b,b'}] of [Tx]: the four points are
    distinct, and every edge of a graph cross-intersecting [Tx] is a cross
    edge, one point from each. *)

Lemma disjoint_four :
  forall (T : Family) e1 e2 a a' b b',
    Uniform 2 T -> In e1 T -> In e2 T -> Disjoint e1 e2 ->
    In a e1 -> In a' e1 -> In b e2 -> In b' e2 -> a <> a' -> b <> b' ->
    a <> b /\ a <> b' /\ a' <> b /\ a' <> b'.
Proof.
  intros T e1 e2 a a' b b' HU H1 H2 Hd Ha Ha' Hb Hb' Haa Hbb.
  repeat split; intros <-; [exact (Hd _ Ha Hb) | exact (Hd _ Ha Hb')
                            | exact (Hd _ Ha' Hb) | exact (Hd _ Ha' Hb')].
Qed.

Lemma cross_of :
  forall (Tx T : Family) e1 e2 a a' b b' f,
    Uniform 2 Tx -> Uniform 2 T -> CrossInt Tx T ->
    In e1 Tx -> In e2 Tx -> In f T ->
    In a e1 -> In a' e1 -> a <> a' -> In b e2 -> In b' e2 -> b <> b' ->
    a <> b -> a <> b' -> a' <> b -> a' <> b' ->
    (In a f \/ In a' f) /\ (In b f \/ In b' f)
    /\ ~ (In a f /\ In a' f) /\ ~ (In b f /\ In b' f).
Proof.
  intros Tx T e1 e2 a a' b b' f HUx HUT HC H1 H2 Hf Ha Ha' Haa Hb Hb' Hbb Hab Hab' Ha'b Ha'b'.
  apply (@cross_edge T f a a' b b' HUT Hf Haa Hbb Hab Hab' Ha'b Ha'b').
  - destruct (HC e1 f H1 Hf) as [w [Hw1 Hwf]]; exists w; split; [exact Hwf|].
    exact (@edge_pin Tx e1 a a' HUx H1 Ha Ha' Haa w Hw1).
  - destruct (HC e2 f H2 Hf) as [w [Hw2 Hwf]]; exists w; split; [exact Hwf|].
    exact (@edge_pin Tx e2 b b' HUx H2 Hb Hb' Hbb w Hw2).
Qed.

(** An intersecting family of cross edges through a fixed cross edge
    [{p,q}] has a common vertex, [p] or [q]. Here [p'] and [q'] are the
    other two points. *)

Lemma c4_common :
  forall (L : Family) g0 p p' q q',
    Uniform 2 L -> IntGraph L -> In g0 L -> In p g0 -> In q g0 ->
    p <> p' -> q <> q' -> p <> q -> p <> q' -> p' <> q -> p' <> q' ->
    (forall g, In g L -> (In p g \/ In p' g) /\ (In q g \/ In q' g)
                         /\ ~ (In p g /\ In p' g) /\ ~ (In q g /\ In q' g)) ->
    (forall g, In g L -> In p g) \/ (forall g, In g L -> In q g).
Proof.
  intros L g0 p p' q q' HU HI Hg0 Hp0 Hq0 Hpp Hqq Hpq Hpq' Hp'q Hp'q' Hcross.
  destruct (existsb (memb p') L) eqn:Ep'; cycle 1.
  { left; intros g Hg.
    pose proof (existsb_false_forall _ _ _ Ep' g Hg) as E; apply memb_false_iff in E.
    destruct (Hcross g Hg) as [[H|H] _]; [exact H | contradiction]. }
  destruct (existsb (memb q') L) eqn:Eq'; cycle 1.
  { right; intros g Hg.
    pose proof (existsb_false_forall _ _ _ Eq' g Hg) as E; apply memb_false_iff in E.
    destruct (Hcross g Hg) as [_ [[H|H] _]]; [exact H | contradiction]. }
  exfalso.
  apply existsb_exists in Ep' as [g [Hg Hp'g]]; apply memb_true_iff in Hp'g.
  apply existsb_exists in Eq' as [g' [Hg' Hq'g']]; apply memb_true_iff in Hq'g'.
  destruct (Hcross g Hg) as [_ [_ [Hnp _]]].
  destruct (Hcross g' Hg') as [_ [_ [_ Hnq]]].
  (* g = {p', q}: it avoids p and meets g0 = {p,q} *)
  assert (Hqg : In q g).
  { destruct (HI g g0 Hg Hg0) as [w [Hwg Hw0]].
    destruct (@edge_pin L g0 p q HU Hg0 Hp0 Hq0 Hpq w Hw0) as [<-|<-];
      [exfalso; apply Hnp; tauto | exact Hwg]. }
  assert (Hpg' : In p g').
  { destruct (HI g' g0 Hg' Hg0) as [w [Hwg Hw0]].
    destruct (@edge_pin L g0 p q HU Hg0 Hp0 Hq0 Hpq w Hw0) as [<-|<-];
      [exact Hwg | exfalso; apply Hnq; tauto]. }
  (* g and g' must meet, but {p',q} and {p,q'} are disjoint *)
  destruct (HI g g' Hg Hg') as [w [Hwg Hwg']].
  destruct (@edge_pin L g p' q HU Hg Hp'g Hqg Hp'q w Hwg) as [<-|<-].
  - destruct (@edge_pin L g' p q' HU Hg' Hpg' Hq'g' Hpq' w Hwg') as [E|E]; congruence.
  - destruct (@edge_pin L g' p q' HU Hg' Hpg' Hq'g' Hpq' w Hwg') as [E|E]; congruence.
Qed.

(** B2: [Tx] has two disjoint edges and [Ty], [Tz] are each intersecting:
    contradiction with covering number 3. *)

Lemma caseB2 :
  forall (Tx Ty Tz : Family) ex ey e1 e2,
    Uniform 2 Tx -> Uniform 2 Ty -> Uniform 2 Tz ->
    CrossInt Tx Ty -> CrossInt Tx Tz -> CrossInt Ty Tz ->
    IntGraph Ty -> IntGraph Tz ->
    In e1 Tx -> In e2 Tx -> Disjoint e1 e2 -> In ey Ty ->
    Tau2 Tx ex Ty Tz -> False.
Proof.
  intros Tx Ty Tz ex ey e1 e2 HUx HUy HUz Hxy Hxz Hyz HIy HIz H1 H2 Hd Hey H2x.
  destruct (@edge_points Tx e1 HUx H1) as [a [a' [Haa [Ha [Ha' Hpin1]]]]].
  destruct (@edge_points Tx e2 HUx H2) as [b [b' [Hbb [Hb [Hb' Hpin2]]]]].
  destruct (@disjoint_four Tx e1 e2 a a' b b' HUx H1 H2 Hd Ha Ha' Hb Hb' Haa Hbb)
    as [Hab [Hab' [Ha'b Ha'b']]].
  (* L = Ty ++ Tz is an intersecting graph of cross edges *)
  set (L := Ty ++ Tz).
  assert (HUL : Uniform 2 L) by (unfold L, Uniform; apply Forall_app; split; assumption).
  assert (HIL : IntGraph L).
  { intros f g Hf Hg; unfold L in Hf, Hg; apply in_app_or in Hf, Hg.
    destruct Hf as [Hf|Hf]; destruct Hg as [Hg|Hg].
    - exact (HIy f g Hf Hg).
    - exact (Hyz f g Hf Hg).
    - destruct (Hyz g f Hg Hf) as [w [H1' H2']]; exists w; tauto.
    - exact (HIz f g Hf Hg). }
  assert (HcrossL : forall g, In g L ->
            (In a g \/ In a' g) /\ (In b g \/ In b' g)
            /\ ~ (In a g /\ In a' g) /\ ~ (In b g /\ In b' g)).
  { intros g Hg; unfold L in Hg; apply in_app_or in Hg; destruct Hg as [Hg|Hg].
    - exact (@cross_of Tx Ty e1 e2 a a' b b' g HUx HUy Hxy H1 H2 Hg Ha Ha' Haa Hb Hb' Hbb Hab Hab' Ha'b Ha'b').
    - exact (@cross_of Tx Tz e1 e2 a a' b b' g HUx HUz Hxz H1 H2 Hg Ha Ha' Haa Hb Hb' Hbb Hab Hab' Ha'b Ha'b'). }
  assert (HeyL : In ey L) by (unfold L; apply in_or_app; left; exact Hey).
  (* a common vertex c of all edges of L *)
  assert (Hc : exists c, forall g, In g L -> In c g).
  { destruct (HcrossL ey HeyL) as [[Hp|Hp] [[Hq|Hq] _]].
    - destruct (@c4_common L ey a a' b b' HUL HIL HeyL Hp Hq Haa Hbb Hab Hab' Ha'b Ha'b' HcrossL) as [H|H];
        [exists a | exists b]; exact H.
    - destruct (@c4_common L ey a a' b' b HUL HIL HeyL Hp Hq Haa ltac:(congruence) Hab' Hab Ha'b' Ha'b
                  ltac:(intros g Hg; destruct (HcrossL g Hg) as [A [B [C D]]]; repeat split; tauto)) as [H|H];
        [exists a | exists b']; exact H.
    - destruct (@c4_common L ey a' a b b' HUL HIL HeyL Hp Hq ltac:(congruence) Hbb Ha'b Ha'b' Hab Hab'
                  ltac:(intros g Hg; destruct (HcrossL g Hg) as [A [B [C D]]]; repeat split; tauto)) as [H|H];
        [exists a' | exists b]; exact H.
    - destruct (@c4_common L ey a' a b' b HUL HIL HeyL Hp Hq ltac:(congruence) ltac:(congruence) Ha'b' Ha'b Hab' Hab
                  ltac:(intros g Hg; destruct (HcrossL g Hg) as [A [B [C D]]]; repeat split; tauto)) as [H|H];
        [exists a' | exists b']; exact H. }
  destruct Hc as [c Hc].
  destruct (H2x c) as [[e [He Hce]] | [w [Hwex [Hwall Hwc]]]].
  - apply Hce, Hc; unfold L; apply in_or_app; exact He.
  - exact (Hd w (Hwall e1 H1) (Hwall e2 H2)).
Qed.

(** Edges all of one of two disjoint kinds [{p,q}], [{r,s}]: at most three
    counting the core. *)

Lemma two_kinds_bound :
  forall (T : Family) e p q r s,
    Simple T -> In e T ->
    p <> q -> r <> s -> p <> r -> p <> s -> q <> r -> q <> s ->
    (forall f, In f T -> (In p f /\ In q f) \/ (In r f /\ In s f)) ->
    length T + core_count e T <= 3.
Proof.
  intros T e p q r s HS He Hpq Hrs Hpr Hps Hqr Hqs Hkind.
  pose proof HS as [HU _].
  destruct (@uniform_mem 2 T e HU He) as [Hle Hnde].
  destruct (existsb (fun f => andb (memb p f) (memb q f)) T) eqn:Epq;
    destruct (existsb (fun f => andb (memb r f) (memb s f)) T) eqn:Ers.
  - (* both kinds: two disjoint edges, core 0, at most two edges *)
    apply existsb_exists in Epq as [f [Hf Hpqf]]; apply Bool.andb_true_iff in Hpqf as [Hpf Hqf].
    apply existsb_exists in Ers as [g [Hg Hrsg]]; apply Bool.andb_true_iff in Hrsg as [Hrg Hsg].
    apply memb_true_iff in Hpf, Hqf, Hrg, Hsg.
    assert (H0 : core_count e T = 0).
    { apply (@core_count_zero e T f g Hle Hf Hg).
      intros w Hwf Hwg.
      destruct (@edge_pin T f p q HU Hf Hpf Hqf Hpq w Hwf) as [<-|<-];
        destruct (@edge_pin T g r s HU Hg Hrg Hsg Hrs w Hwg) as [E|E]; congruence. }
    assert (HT : length T <= 2).
    { change 2 with (length [[p;q];[r;s]]).
      apply edges_among; [exact HS| |].
      - intros S [<-|[<-|[]]]; split; try reflexivity; apply pair_nodup; assumption.
      - intros h Hh; destruct (Hkind h Hh) as [[H1 H2]|[H1 H2]];
          [exists [p;q]; split; [left; reflexivity | apply subset2; assumption]
          | exists [r;s]; split; [right; left; reflexivity | apply subset2; assumption]]. }
    lia.
  - (* only the {p,q} kind *)
    assert (HT : length T <= 1).
    { change 1 with (length [[p;q]]).
      apply edges_among; [exact HS| |].
      - intros S [<-|[]]; split; [apply pair_nodup; assumption | reflexivity].
      - intros h Hh; exists [p;q]; split; [left; reflexivity|].
        destruct (Hkind h Hh) as [[H1 H2]|[H1 H2]]; [apply subset2; assumption|].
        exfalso; pose proof (existsb_false_forall _ _ _ Ers h Hh) as E.
        apply Bool.andb_false_iff in E; destruct E as [E|E]; apply memb_false_iff in E; contradiction. }
    pose proof (@core_count_le_two e T Hle); lia.
  - assert (HT : length T <= 1).
    { change 1 with (length [[r;s]]).
      apply edges_among; [exact HS| |].
      - intros S [<-|[]]; split; [apply pair_nodup; assumption | reflexivity].
      - intros h Hh; exists [r;s]; split; [left; reflexivity|].
        destruct (Hkind h Hh) as [[H1 H2]|[H1 H2]]; [|apply subset2; assumption].
        exfalso; pose proof (existsb_false_forall _ _ _ Epq h Hh) as E.
        apply Bool.andb_false_iff in E; destruct E as [E|E]; apply memb_false_iff in E; contradiction. }
    pose proof (@core_count_le_two e T Hle); lia.
  - (* no edge at all, against In e T *)
    exfalso; destruct (Hkind e He) as [[H1 H2]|[H1 H2]].
    + pose proof (existsb_false_forall _ _ _ Epq e He) as E.
      apply Bool.andb_false_iff in E; destruct E as [E|E]; apply memb_false_iff in E; contradiction.
    + pose proof (existsb_false_forall _ _ _ Ers e He) as E.
      apply Bool.andb_false_iff in E; destruct E as [E|E]; apply memb_false_iff in E; contradiction.
Qed.

(** An edge of [T] cannot be [{u',v'}] when [T] cross-intersects a graph
    containing the edge [{u,v}] disjoint from it. *)

Lemma no_disjoint_edge :
  forall (T T' : Family) h e u v u' v',
    Uniform 2 T -> In h T -> CrossInt T T' -> In e T' ->
    (forall y, In y e -> y = u \/ y = v) ->
    u' <> u -> u' <> v -> v' <> u -> v' <> v -> u' <> v' ->
    ~ (In u' h /\ In v' h).
Proof.
  intros T T' h e u v u' v' HU Hh HC He Hpin Hu'u Hu'v Hv'u Hv'v Huv [Hu' Hv'].
  destruct (HC h e Hh He) as [w [Hwh Hwe]].
  destruct (@edge_pin T h u' v' HU Hh Hu' Hv' Huv w Hwh) as [<-|<-];
    destruct (Hpin w Hwe) as [E|E]; congruence.
Qed.

(** B1, with the labelling fixed: [Tx] has the disjoint edges [{α,α'}],
    [{β,β'}] and [Ty] the disjoint edges [{α,β}], [{α',β'}]. *)

Lemma caseB1_core :
  forall (Tx Ty Tz : Family) ex ey ez E1 E2 G1 G2 al al' be be',
    Simple Tx -> Simple Ty -> Simple Tz ->
    CrossInt Tx Ty -> CrossInt Tx Tz -> CrossInt Ty Tz ->
    In E1 Tx -> In al E1 -> In al' E1 ->
    In E2 Tx -> In be E2 -> In be' E2 ->
    In G1 Ty -> In al G1 -> In be G1 ->
    In G2 Ty -> In al' G2 -> In be' G2 ->
    al <> al' -> be <> be' -> al <> be -> al <> be' -> al' <> be -> al' <> be' ->
    In ex Tx -> In ey Ty -> In ez Tz ->
    length Tx + length Ty + length Tz
      + core_count ex Tx + core_count ey Ty + core_count ez Tz <= 9.
Proof.
  intros Tx Ty Tz ex ey ez E1 E2 G1 G2 al al' be be' HSx HSy HSz Hxy Hxz Hyz
         HE1 Hal1 Hal'1 HE2 Hbe2 Hbe'2 HG1 HalG1 HbeG1 HG2 Hal'G2 Hbe'G2
         Haa Hbb Hab Hab' Ha'b Ha'b' Hex Hey Hez.
  pose proof HSx as [HUx _]; pose proof HSy as [HUy _]; pose proof HSz as [HUz _].
  pose proof (CrossInt_sym Hxy) as Hyx.
  pose proof (CrossInt_sym Hxz) as Hzx.
  pose proof (CrossInt_sym Hyz) as Hzy.
  (* pins *)
  pose proof (@edge_pin Tx E1 al al' HUx HE1 Hal1 Hal'1 Haa) as PE1.
  pose proof (@edge_pin Tx E2 be be' HUx HE2 Hbe2 Hbe'2 Hbb) as PE2.
  pose proof (@edge_pin Ty G1 al be HUy HG1 HalG1 HbeG1 Hab) as PG1.
  pose proof (@edge_pin Ty G2 al' be' HUy HG2 Hal'G2 Hbe'G2 Ha'b') as PG2.
  (* shapes *)
  assert (Hx : forall h, In h Tx ->
            (In al h \/ In be h) /\ (In al' h \/ In be' h)
            /\ ~ (In al h /\ In be h) /\ ~ (In al' h /\ In be' h)).
  { intros h Hh.
    exact (@cross_of Ty Tx G1 G2 al be al' be' h HUy HUx Hyx HG1 HG2 Hh
             HalG1 HbeG1 Hab Hal'G2 Hbe'G2 Ha'b' Haa Hab' ltac:(congruence) Hbb). }
  assert (Hy : forall g, In g Ty ->
            (In al g \/ In al' g) /\ (In be g \/ In be' g)
            /\ ~ (In al g /\ In al' g) /\ ~ (In be g /\ In be' g)).
  { intros g Hg.
    exact (@cross_of Tx Ty E1 E2 al al' be be' g HUx HUy Hxy HE1 HE2 Hg
             Hal1 Hal'1 Haa Hbe2 Hbe'2 Hbb Hab Hab' Ha'b Ha'b'). }
  assert (Hz : forall k, In k Tz -> (In al k /\ In be' k) \/ (In al' k /\ In be k)).
  { intros k Hk.
    pose proof (@cross_of Tx Tz E1 E2 al al' be be' k HUx HUz Hxz HE1 HE2 Hk
                  Hal1 Hal'1 Haa Hbe2 Hbe'2 Hbb Hab Hab' Ha'b Ha'b') as A.
    pose proof (@cross_of Ty Tz G1 G2 al be al' be' k HUy HUz Hyz HG1 HG2 Hk
                  HalG1 HbeG1 Hab Hal'G2 Hbe'G2 Ha'b' Haa Hab' ltac:(congruence) Hbb) as B.
    tauto. }
  (* cores of Tx and Ty vanish *)
  destruct (@uniform_mem 2 Tx ex HUx Hex) as [Hlex _].
  destruct (@uniform_mem 2 Ty ey HUy Hey) as [Hley _].
  assert (Hcx : core_count ex Tx = 0).
  { apply (@core_count_zero ex Tx E1 E2 Hlex HE1 HE2).
    intros w H1 H2; destruct (PE1 w H1) as [<-|<-]; destruct (PE2 w H2) as [E|E]; congruence. }
  assert (Hcy : core_count ey Ty = 0).
  { apply (@core_count_zero ey Ty G1 G2 Hley HG1 HG2).
    intros w H1 H2; destruct (PG1 w H1) as [<-|<-]; destruct (PG2 w H2) as [E|E]; congruence. }
  (* Tz with its core *)
  assert (Hzb : length Tz + core_count ez Tz <= 3).
  { apply (@two_kinds_bound Tz ez al be' al' be HSz Hez); try assumption; try congruence. }
  (* the edge ez decides which cross edge is excluded elsewhere *)
  destruct (Hz ez Hez) as [[Hal_ez Hbe'_ez] | [Hal'_ez Hbe_ez]].
  - pose proof (@edge_pin Tz ez al be' HUz Hez Hal_ez Hbe'_ez Hab') as Pez.
    assert (HTx : length Tx <= 3).
    { change 3 with (length [[al;al'];[al;be'];[be;be']]).
      apply edges_among; [exact HSx| |].
      - intros S [<-|[<-|[<-|[]]]]; split; try reflexivity; apply pair_nodup; assumption.
      - intros h Hh.
        pose proof (@no_disjoint_edge Tx Tz h ez al be' al' be HUx Hh Hxz Hez Pez
                      ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence)) as Hno.
        destruct (Hx h Hh) as [[H1|H1] [[H2|H2] [H3 H4]]].
        + exists [al;al']; split; [left; reflexivity | apply subset2; assumption].
        + exists [al;be']; split; [right; left; reflexivity | apply subset2; assumption].
        + exfalso; apply Hno; tauto.
        + exists [be;be']; split; [right; right; left; reflexivity | apply subset2; assumption]. }
    assert (HTy : length Ty <= 3).
    { change 3 with (length [[al;be];[al;be'];[al';be']]).
      apply edges_among; [exact HSy| |].
      - intros S [<-|[<-|[<-|[]]]]; split; try reflexivity; apply pair_nodup; assumption.
      - intros g Hg.
        pose proof (@no_disjoint_edge Ty Tz g ez al be' al' be HUy Hg Hyz Hez Pez
                      ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence)) as Hno.
        destruct (Hy g Hg) as [[H1|H1] [[H2|H2] [H3 H4]]].
        + exists [al;be]; split; [left; reflexivity | apply subset2; assumption].
        + exists [al;be']; split; [right; left; reflexivity | apply subset2; assumption].
        + exfalso; apply Hno; tauto.
        + exists [al';be']; split; [right; right; left; reflexivity | apply subset2; assumption]. }
    lia.
  - pose proof (@edge_pin Tz ez al' be HUz Hez Hal'_ez Hbe_ez Ha'b) as Pez.
    assert (HTx : length Tx <= 3).
    { change 3 with (length [[al;al'];[al';be];[be;be']]).
      apply edges_among; [exact HSx| |].
      - intros S [<-|[<-|[<-|[]]]]; split; try reflexivity; apply pair_nodup; try assumption; congruence.
      - intros h Hh.
        pose proof (@no_disjoint_edge Tx Tz h ez al' be al be' HUx Hh Hxz Hez Pez
                      ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence)) as Hno.
        destruct (Hx h Hh) as [[H1|H1] [[H2|H2] [H3 H4]]].
        + exists [al;al']; split; [left; reflexivity | apply subset2; assumption].
        + exfalso; apply Hno; tauto.
        + exists [al';be]; split; [right; left; reflexivity | apply subset2; assumption].
        + exists [be;be']; split; [right; right; left; reflexivity | apply subset2; assumption]. }
    assert (HTy : length Ty <= 3).
    { change 3 with (length [[al;be];[al';be];[al';be']]).
      apply edges_among; [exact HSy| |].
      - intros S [<-|[<-|[<-|[]]]]; split; try reflexivity; apply pair_nodup; assumption.
      - intros g Hg.
        pose proof (@no_disjoint_edge Ty Tz g ez al' be al be' HUy Hg Hyz Hez Pez
                      ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence)) as Hno.
        destruct (Hy g Hg) as [[H1|H1] [[H2|H2] [H3 H4]]].
        + exists [al;be]; split; [left; reflexivity | apply subset2; assumption].
        + exfalso; apply Hno; tauto.
        + exists [al';be]; split; [right; left; reflexivity | apply subset2; assumption].
        + exists [al';be']; split; [right; right; left; reflexivity | apply subset2; assumption]. }
    lia.
Qed.

(** B: [Tx] has two disjoint edges. Either [Ty] or [Tz] also has two
    (B1, the bound), or neither (B2, contradiction). *)

Lemma caseB :
  forall (Tx Ty Tz : Family) ex ey ez e1 e2,
    Simple Tx -> Simple Ty -> Simple Tz ->
    CrossInt Tx Ty -> CrossInt Tx Tz -> CrossInt Ty Tz ->
    In e1 Tx -> In e2 Tx -> Disjoint e1 e2 ->
    In ex Tx -> In ey Ty -> In ez Tz ->
    Tau2 Tx ex Ty Tz ->
    length Tx + length Ty + length Tz
      + core_count ex Tx + core_count ey Ty + core_count ez Tz <= 9.
Proof.
  intros Tx Ty Tz ex ey ez e1 e2 HSx HSy HSz Hxy Hxz Hyz H1 H2 Hd Hex Hey Hez H2x.
  pose proof HSx as [HUx _]; pose proof HSy as [HUy _]; pose proof HSz as [HUz _].
  destruct (@edge_points Tx e1 HUx H1) as [a [a' [Haa [Ha [Ha' Hpin1]]]]].
  destruct (@edge_points Tx e2 HUx H2) as [b [b' [Hbb [Hb [Hb' Hpin2]]]]].
  destruct (@disjoint_four Tx e1 e2 a a' b b' HUx H1 H2 Hd Ha Ha' Hb Hb' Haa Hbb)
    as [Hab [Hab' [Ha'b Ha'b']]].
  (* a second graph with two disjoint edges: they are the two cross edges
     of a perfect matching of the four points *)
  assert (HB1 : forall (Ty' Tz' : Family) ey' ez' g1 g2,
             Simple Ty' -> Simple Tz' -> CrossInt Tx Ty' -> CrossInt Tx Tz' -> CrossInt Ty' Tz' ->
             In g1 Ty' -> In g2 Ty' -> Disjoint g1 g2 -> In ey' Ty' -> In ez' Tz' ->
             length Tx + length Ty' + length Tz'
               + core_count ex Tx + core_count ey' Ty' + core_count ez' Tz' <= 9).
  { intros Ty' Tz' ey' ez' g1 g2 HSy' HSz' Hxy' Hxz' Hyz' Hg1 Hg2 Hdg Hey' Hez'.
    pose proof HSy' as [HUy' _].
    pose proof (@cross_of Tx Ty' e1 e2 a a' b b' g1 HUx HUy' Hxy' H1 H2 Hg1
                  Ha Ha' Haa Hb Hb' Hbb Hab Hab' Ha'b Ha'b') as C1.
    pose proof (@cross_of Tx Ty' e1 e2 a a' b b' g2 HUx HUy' Hxy' H1 H2 Hg2
                  Ha Ha' Haa Hb Hb' Hbb Hab Hab' Ha'b Ha'b') as C2.
    destruct C1 as [[Hp|Hp] [[Hq|Hq] _]].
    - (* g1 = {a,b}: g2 = {a',b'} *)
      assert (Ha'2 : In a' g2) by (destruct C2 as [[H|H] _]; [exfalso; exact (Hdg a Hp H) | exact H]).
      assert (Hb'2 : In b' g2) by (destruct C2 as [_ [[H|H] _]]; [exfalso; exact (Hdg b Hq H) | exact H]).
      exact (@caseB1_core Tx Ty' Tz' ex ey' ez' e1 e2 g1 g2 a a' b b' HSx HSy' HSz' Hxy' Hxz' Hyz'
               H1 Ha Ha' H2 Hb Hb' Hg1 Hp Hq Hg2 Ha'2 Hb'2 Haa Hbb Hab Hab' Ha'b Ha'b' Hex Hey' Hez').
    - (* g1 = {a,b'}: g2 = {a',b} *)
      assert (Ha'2 : In a' g2) by (destruct C2 as [[H|H] _]; [exfalso; exact (Hdg a Hp H) | exact H]).
      assert (Hb2 : In b g2) by (destruct C2 as [_ [[H|H] _]]; [exact H | exfalso; exact (Hdg b' Hq H)]).
      exact (@caseB1_core Tx Ty' Tz' ex ey' ez' e1 e2 g1 g2 a a' b' b HSx HSy' HSz' Hxy' Hxz' Hyz'
               H1 Ha Ha' H2 Hb' Hb Hg1 Hp Hq Hg2 Ha'2 Hb2 Haa ltac:(congruence) Hab' Hab Ha'b' Ha'b Hex Hey' Hez').
    - (* g1 = {a',b}: g2 = {a,b'} *)
      assert (Ha2 : In a g2) by (destruct C2 as [[H|H] _]; [exact H | exfalso; exact (Hdg a' Hp H)]).
      assert (Hb'2 : In b' g2) by (destruct C2 as [_ [[H|H] _]]; [exfalso; exact (Hdg b Hq H) | exact H]).
      exact (@caseB1_core Tx Ty' Tz' ex ey' ez' e1 e2 g1 g2 a' a b b' HSx HSy' HSz' Hxy' Hxz' Hyz'
               H1 Ha' Ha H2 Hb Hb' Hg1 Hp Hq Hg2 Ha2 Hb'2 ltac:(congruence) Hbb Ha'b Ha'b' Hab Hab' Hex Hey' Hez').
    - (* g1 = {a',b'}: g2 = {a,b} *)
      assert (Ha2 : In a g2) by (destruct C2 as [[H|H] _]; [exact H | exfalso; exact (Hdg a' Hp H)]).
      assert (Hb2 : In b g2) by (destruct C2 as [_ [[H|H] _]]; [exact H | exfalso; exact (Hdg b' Hq H)]).
      exact (@caseB1_core Tx Ty' Tz' ex ey' ez' e1 e2 g1 g2 a' a b' b HSx HSy' HSz' Hxy' Hxz' Hyz'
               H1 Ha' Ha H2 Hb' Hb Hg1 Hp Hq Hg2 Ha2 Hb2 ltac:(congruence) ltac:(congruence) Ha'b' Ha'b Hab' Hab Hex Hey' Hez'). }
  destruct (has_disj Ty) eqn:Ey.
  { destruct (has_disj_true _ Ey) as [g1 [g2 [Hg1 [Hg2 Hdg]]]].
    exact (HB1 Ty Tz ey ez g1 g2 HSy HSz Hxy Hxz Hyz Hg1 Hg2 Hdg Hey Hez). }
  destruct (has_disj Tz) eqn:Ez.
  { destruct (has_disj_true _ Ez) as [g1 [g2 [Hg1 [Hg2 Hdg]]]].
    pose proof (HB1 Tz Ty ez ey g1 g2 HSz HSy Hxz Hxy (CrossInt_sym Hyz) Hg1 Hg2 Hdg Hez Hey); lia. }
  exfalso.
  exact (@caseB2 Tx Ty Tz ex ey e1 e2 HUx HUy HUz Hxy Hxz Hyz
           (has_disj_false _ Ey) (has_disj_false _ Ez) H1 H2 Hd Hey H2x).
Qed.

(** ** The graph lemma: nine *)

Theorem nine :
  forall (Tx Ty Tz : Family) ex ey ez,
    Simple Tx -> Simple Ty -> Simple Tz ->
    CrossInt Tx Ty -> CrossInt Tx Tz -> CrossInt Ty Tz ->
    In ex Tx -> In ey Ty -> In ez Tz ->
    Tau2 Tx ex Ty Tz -> Tau2 Ty ey Tx Tz -> Tau2 Tz ez Tx Ty ->
    length Tx + length Ty + length Tz
      + core_count ex Tx + core_count ey Ty + core_count ez Tz <= 9.
Proof.
  intros Tx Ty Tz ex ey ez HSx HSy HSz Hxy Hxz Hyz Hex Hey Hez H2x H2y H2z.
  pose proof HSx as [HUx _]; pose proof HSy as [HUy _]; pose proof HSz as [HUz _].
  destruct (has_disj Tx) eqn:Ex.
  { destruct (has_disj_true _ Ex) as [e1 [e2 [H1 [H2 Hd]]]].
    exact (@caseB Tx Ty Tz ex ey ez e1 e2 HSx HSy HSz Hxy Hxz Hyz H1 H2 Hd Hex Hey Hez H2x). }
  destruct (has_disj Ty) eqn:Ey.
  { destruct (has_disj_true _ Ey) as [e1 [e2 [H1 [H2 Hd]]]].
    pose proof (@caseB Ty Tx Tz ey ex ez e1 e2 HSy HSx HSz (CrossInt_sym Hxy) Hyz Hxz
                  H1 H2 Hd Hey Hex Hez H2y); lia. }
  destruct (has_disj Tz) eqn:Ez.
  { destruct (has_disj_true _ Ez) as [e1 [e2 [H1 [H2 Hd]]]].
    pose proof (@caseB Tz Tx Ty ez ex ey e1 e2 HSz HSx HSy (CrossInt_sym Hxz) (CrossInt_sym Hyz) Hxy
                  H1 H2 Hd Hez Hex Hey H2z); lia. }
  (* Case A: all three intersecting *)
  pose proof (has_disj_false _ Ex) as HIx.
  pose proof (has_disj_false _ Ey) as HIy.
  pose proof (has_disj_false _ Ez) as HIz.
  destruct (@int_graph_bound Tx ex HSx HIx Hex) as [Bx | Hstar];
    [| destruct Hstar as (c & u1 & u2 & u3 & Hc & H12 & H13 & H23 & H1c & H2c & H3c & F1 & F2 & F3)].
  2: { exfalso; exact (@star_contra Tx Ty Tz ex c u1 u2 u3 HUx HUy HUz Hxy Hxz H2x Hc H12 H13 H23 H1c H2c H3c F1 F2 F3). }
  destruct (@int_graph_bound Ty ey HSy HIy Hey) as [By | Hstar];
    [| destruct Hstar as (c & u1 & u2 & u3 & Hc & H12 & H13 & H23 & H1c & H2c & H3c & F1 & F2 & F3)].
  2: { exfalso; exact (@star_contra Ty Tx Tz ey c u1 u2 u3 HUy HUx HUz (CrossInt_sym Hxy) Hyz H2y Hc H12 H13 H23 H1c H2c H3c F1 F2 F3). }
  destruct (@int_graph_bound Tz ez HSz HIz Hez) as [Bz | Hstar];
    [| destruct Hstar as (c & u1 & u2 & u3 & Hc & H12 & H13 & H23 & H1c & H2c & H3c & F1 & F2 & F3)].
  2: { exfalso; exact (@star_contra Tz Tx Ty ez c u1 u2 u3 HUz HUx HUy (CrossInt_sym Hxz) (CrossInt_sym Hyz) H2z Hc H12 H13 H23 H1c H2c H3c F1 F2 F3). }
  lia.
Qed.

(** ** From the family to its tail graphs *)

(** The third point of a 3-set containing two given distinct points. *)

Lemma third_point :
  forall (A : list nat) x y,
    length A = 3 -> NoDup A -> In x A -> In y A -> x <> y ->
    exists w, In w A /\ w <> x /\ w <> y /\ (forall t, In t A -> t = x \/ t = y \/ t = w).
Proof.
  intros A x y Hl Hnd Hx Hy Hxy.
  pose proof (@rem_length x A Hnd Hx) as L1.
  assert (Hy1 : In y (rem x A)) by (apply in_rem; split; [exact Hy | intros E; apply Hxy; symmetry; exact E]).
  pose proof (@rem_nodup x A Hnd) as N1.
  pose proof (@rem_length y (rem x A) N1 Hy1) as L2.
  destruct (rem y (rem x A)) as [|w [|? ?]] eqn:E; simpl in L2; try lia.
  assert (Hw : In w (rem y (rem x A))) by (rewrite E; left; reflexivity).
  apply in_rem in Hw as [Hw1 Hwy]; apply in_rem in Hw1 as [HwA Hwx].
  exists w; repeat split; try assumption.
  intros t Ht.
  destruct (Nat.eq_dec t x) as [->|Htx]; [left; reflexivity|].
  destruct (Nat.eq_dec t y) as [->|Hty]; [right; left; reflexivity|].
  right; right.
  assert (Ht2 : In t (rem y (rem x A))) by (apply in_rem; split; [apply in_rem; split; assumption | exact Hty]).
  rewrite E in Ht2; destruct Ht2 as [<-|[]]; reflexivity.
Qed.

Lemma degsum_le_length :
  forall (Ts : list (list nat)) (F : Family),
    (forall T, In T Ts -> deg T F <= 1) -> degsum Ts F <= length Ts.
Proof.
  induction Ts as [|T Ts IH]; intros F H; simpl; [lia|].
  pose proof (H T (or_introl eq_refl)); pose proof (IH F (fun T' HT' => H T' (or_intror HT'))); lia.
Qed.

(** Tails of a layer through [a] form a simple graph, and layers of
    different points have cross-intersecting tails. *)

Lemma tail_simple :
  forall (G T : Family) a,
    Uniform 3 G -> Distinct G ->
    (forall A, In A T -> In A G /\ In a A) ->
    (forall S, deg S T <= deg S G) ->
    Simple (map (rem a) T).
Proof.
  intros G T a HU HD Hmem Hdsub; split.
  - apply Forall_forall; intros e He.
    apply in_map_iff in He as [A [<- HA]].
    destruct (Hmem A HA) as [HAG HaA].
    destruct (@uniform_mem 3 G A HU HAG) as [Hl Hnd].
    unfold UniformSet; split;
      [ pose proof (@rem_length a A Hnd HaA); lia | apply rem_nodup; exact Hnd ].
  - intros S Hnd Hlen; unfold deg; rewrite length_filter_map.
    destruct S as [|s1 [|s2 [|s3 S']]]; simpl in Hlen; try discriminate.
    assert (Hs12 : s1 <> s2)
      by (inversion Hnd as [|? ? Hni _]; subst; intros <-; apply Hni; left; reflexivity).
    assert (Hnil : forall (l : Family), filter (fun _ => false) l = [])
      by (induction l; simpl; [reflexivity | assumption]).
    destruct (Nat.eq_dec s1 a) as [<-|H1a].
    { assert (Hz : forall A, containsb [s1; s2] (rem s1 A) = false).
      { intros A; destruct (containsb [s1;s2] (rem s1 A)) eqn:E; [|reflexivity].
        exfalso; apply containsb_true_iff in E.
        assert (Hin : In s1 (rem s1 A)) by (apply E; left; reflexivity).
        apply in_rem in Hin as [_ Hne]; apply Hne; reflexivity. }
      rewrite (filter_ext_eq _ (fun _ => false) T (fun A => Hz A)), Hnil; simpl; lia. }
    destruct (Nat.eq_dec s2 a) as [<-|H2a].
    { assert (Hz : forall A, containsb [s1; s2] (rem s2 A) = false).
      { intros A; destruct (containsb [s1;s2] (rem s2 A)) eqn:E; [|reflexivity].
        exfalso; apply containsb_true_iff in E.
        assert (Hin : In s2 (rem s2 A)) by (apply E; right; left; reflexivity).
        apply in_rem in Hin as [_ Hne]; apply Hne; reflexivity. }
      rewrite (filter_ext_eq _ (fun _ => false) T (fun A => Hz A)), Hnil; simpl; lia. }
    eapply Nat.le_trans.
    + apply (@filter_length_mono _ _ (containsb [a; s1; s2])).
      intros A HA Hc; apply containsb_true_iff in Hc.
      assert (H1 : In s1 (rem a A)) by (apply Hc; left; reflexivity).
      assert (H2 : In s2 (rem a A)) by (apply Hc; right; left; reflexivity).
      apply in_rem in H1 as [H1A _]; apply in_rem in H2 as [H2A _].
      destruct (Hmem A HA) as [_ HaA].
      apply containsb_true_iff; intros t [<-|[<-|[<-|[]]]]; assumption.
    + eapply Nat.le_trans; [apply (Hdsub [a;s1;s2])|].
      apply (@tt_triple G HU HD); [| reflexivity].
      apply triple_nodup; [congruence | congruence | exact Hs12].
Qed.

Lemma tail_cross :
  forall (G S T : Family) a b,
    (forall C D, In C G -> In D G -> exists w, In w C /\ In w D) ->
    a <> b ->
    (forall A, In A S -> In A G /\ ~ In b A) ->
    (forall A, In A T -> In A G /\ ~ In a A) ->
    CrossInt (map (rem a) S) (map (rem b) T).
Proof.
  intros G S T a b Hint Hab HS HT e f He Hf.
  apply in_map_iff in He as [A [<- HA]].
  apply in_map_iff in Hf as [B0 [<- HB]].
  destruct (HS A HA) as [HAG HbA].
  destruct (HT B0 HB) as [HBG HaB].
  destruct (Hint A B0 HAG HBG) as [w [HwA HwB]].
  exists w; split; apply in_rem; split; try assumption.
  - intros <-; contradiction.
  - intros <-; contradiction.
Qed.

Section TauThreeTenBound.

Variable G : Family.
Hypothesis HU : Uniform 3 G.
Hypothesis HD : Distinct G.
Hypothesis Hint : forall C D, In C G -> In D G -> exists w, In w C /\ In w D.
Hypothesis Htau : forall p q, exists C, In C G /\ ~ In p C /\ ~ In q C.

(** A two-point layer [{p,q,·}] avoiding [r] is counted by the core of the
    [r]-layer's tail graph, against any fixed tail [rem r Ar]. *)

Lemma two_layer_bound :
  forall p q r (C T : Family) (Ar : list nat),
    p <> q -> p <> r -> q <> r ->
    (forall A, In A C -> In A G /\ In p A /\ In q A /\ ~ In r A) ->
    (forall S, deg S C <= deg S G) ->
    (forall B, In B T -> In B G /\ In r B /\ ~ In p B /\ ~ In q B) ->
    In Ar T ->
    length C <= core_count (rem r Ar) (map (rem r) T).
Proof.
  intros p q r C T Ar Hpq Hpr Hqr HC HdC HT HAr.
  set (Gr := map (rem r) T).
  set (Ts := map (fun v => [p;q;v]) (filter (fun v => forallb (memb v) Gr) (rem r Ar))).
  assert (Hlen : length Ts = core_count (rem r Ar) Gr)
    by (unfold Ts, core_count; apply map_length).
  rewrite <- Hlen.
  eapply Nat.le_trans; [apply cover_by_sets_sum | apply degsum_le_length].
  - intros A HA.
    destruct (HC A HA) as [HAG [HpA [HqA HrA]]].
    destruct (@uniform_mem 3 G A HU HAG) as [Hl Hnd].
    destruct (@third_point A p q Hl Hnd HpA HqA Hpq) as [w [HwA [Hwp [Hwq Hall]]]].
    assert (Hwr : w <> r) by (intros <-; exact (HrA HwA)).
    (* w lies in every tail of T *)
    assert (Hcore : forall B, In B T -> In w (rem r B)).
    { intros B HB; destruct (HT B HB) as [HBG [HrB [HpB HqB]]].
      destruct (Hint A B HAG HBG) as [t [HtA HtB]].
      destruct (Hall t HtA) as [<-|[<-|<-]]; [contradiction | contradiction |].
      apply in_rem; split; assumption. }
    exists [p;q;w]; split.
    + unfold Ts; apply in_map_iff; exists w; split; [reflexivity|].
      apply filter_In; split; [apply Hcore; exact HAr|].
      apply forallb_forall; intros f Hf; unfold Gr in Hf.
      apply in_map_iff in Hf as [B [<- HB]]; apply memb_true_iff; apply Hcore; exact HB.
    + intros t [<-|[<-|[<-|[]]]]; assumption.
  - intros S HS; unfold Ts in HS; apply in_map_iff in HS as [v [<- Hv]].
    apply filter_In in Hv as [Hv _]; apply in_rem in Hv as [HvAr Hvr].
    destruct (HT Ar HAr) as [_ [_ [HpAr HqAr]]].
    eapply Nat.le_trans; [apply HdC|].
    apply (@tt_triple G HU HD); [|reflexivity].
    apply triple_nodup; [exact Hpq | intros <-; exact (HpAr HvAr) | intros <-; exact (HqAr HvAr)].
Qed.

(** Covering number 3 at the pair [{x, c}], read on the tail graphs. *)

Lemma tau2_of :
  forall x y z (Tx Ty Tz : Family) (Ax : list nat),
    (forall A, In A G -> In x A \/ In y A \/ In z A) -> x <> y -> x <> z -> y <> z ->
    (forall A, In A Tx -> In A G /\ In x A /\ ~ In y A /\ ~ In z A) ->
    (forall A, In A G -> In y A -> ~ In x A -> ~ In z A -> In A Ty) ->
    (forall A, In A G -> In z A -> ~ In x A -> ~ In y A -> In A Tz) ->
    In Ax Tx ->
    Tau2 (map (rem x) Tx) (rem x Ax) (map (rem y) Ty) (map (rem z) Tz).
Proof.
  intros x y z Tx Ty Tz Ax Hmeet Hxy Hxz Hyz HTx HTy HTz HAx c.
  destruct (Htau x c) as [D [HDG [HxD HcD]]].
  destruct (memb y D) eqn:Ey; destruct (memb z D) eqn:Ez.
  - (* D contains y and z: its third point is a core point of Tx *)
    apply memb_true_iff in Ey, Ez.
    destruct (@uniform_mem 3 G D HU HDG) as [Hl Hnd].
    destruct (@third_point D y z Hl Hnd Ey Ez Hyz) as [w [HwD [Hwy [Hwz Hall]]]].
    right; exists w; repeat split.
    + apply in_rem; split; [| intros <-; exact (HxD HwD)].
      destruct (HTx Ax HAx) as [HAG [_ [HyA HzA]]].
      destruct (Hint D Ax HDG HAG) as [t [HtD HtA]].
      destruct (Hall t HtD) as [<-|[<-|<-]]; [contradiction | contradiction | exact HtA].
    + intros f Hf; apply in_map_iff in Hf as [B [<- HB]].
      destruct (HTx B HB) as [HBG [_ [HyB HzB]]].
      destruct (Hint D B HDG HBG) as [t [HtD HtB]].
      destruct (Hall t HtD) as [<-|[<-|<-]]; [contradiction | contradiction |].
      apply in_rem; split; [exact HtB | intros <-; exact (HxD HwD)].
    + intros <-; exact (HcD HwD).
  - apply memb_true_iff in Ey; apply memb_false_iff in Ez.
    left; exists (rem y D); split.
    + left; apply in_map_iff; exists D; split; [reflexivity | apply HTy; assumption].
    + intros Hc; apply in_rem in Hc as [Hc _]; exact (HcD Hc).
  - apply memb_false_iff in Ey; apply memb_true_iff in Ez.
    left; exists (rem z D); split.
    + right; apply in_map_iff; exists D; split; [reflexivity | apply HTz; assumption].
    + intros Hc; apply in_rem in Hc as [Hc _]; exact (HcD Hc).
  - apply memb_false_iff in Ey, Ez.
    exfalso; destruct (Hmeet D HDG) as [H|[H|H]]; contradiction.
Qed.

(** ** The bound *)

Lemma ten_core :
  forall x y z, In [x;y;z] G -> x <> y -> x <> z -> y <> z -> length G <= 10.
Proof.
  intros x y z HMG Hxy Hxz Hyz.
  pose (Cxy := filter (containsb [x;y]) G).
  pose (R1 := filter (fun A => negb (containsb [x;y] A)) G).
  pose (Cxz := filter (containsb [x;z]) R1).
  pose (R2 := filter (fun A => negb (containsb [x;z] A)) R1).
  pose (Cyz := filter (containsb [y;z]) R2).
  pose (R3 := filter (fun A => negb (containsb [y;z] A)) R2).
  pose (R4 := filter (fun A => negb (memb x A)) R3).
  pose (Tx := filter (fun A => memb x A) R3).
  pose (Ty := filter (fun A => memb y A) R4).
  pose (Tz := filter (fun A => negb (memb y A)) R4).
  assert (ECxy : Cxy = filter (containsb [x;y]) G) by reflexivity.
  assert (ER1 : R1 = filter (fun A => negb (containsb [x;y] A)) G) by reflexivity.
  assert (ECxz : Cxz = filter (containsb [x;z]) R1) by reflexivity.
  assert (ER2 : R2 = filter (fun A => negb (containsb [x;z] A)) R1) by reflexivity.
  assert (ECyz : Cyz = filter (containsb [y;z]) R2) by reflexivity.
  assert (ER3 : R3 = filter (fun A => negb (containsb [y;z] A)) R2) by reflexivity.
  assert (ER4 : R4 = filter (fun A => negb (memb x A)) R3) by reflexivity.
  assert (ETx : Tx = filter (fun A => memb x A) R3) by reflexivity.
  assert (ETy : Ty = filter (fun A => memb y A) R4) by reflexivity.
  assert (ETz : Tz = filter (fun A => negb (memb y A)) R4) by reflexivity.
  (* the partition *)
  assert (E1 : length G = length Cxy + length R1)
    by (rewrite ECxy, ER1; apply length_filter_partition).
  assert (E2 : length R1 = length Cxz + length R2)
    by (rewrite ECxz, ER2; apply length_filter_partition).
  assert (E3 : length R2 = length Cyz + length R3)
    by (rewrite ECyz, ER3; apply length_filter_partition).
  assert (E4 : length R3 = length Tx + length R4)
    by (rewrite ER4, ETx; apply length_filter_partition).
  assert (E5 : length R4 = length Ty + length Tz)
    by (rewrite ETy, ETz; apply length_filter_partition).
  (* membership in the layers *)
  assert (Hnotc : forall (T C : list nat) (a : nat),
             In a T -> ~ In a C -> containsb T C = false).
  { intros T C a HaT HaC.
    destruct (containsb T C) eqn:E; [|reflexivity].
    exfalso; apply containsb_true_iff in E; apply HaC; apply E; exact HaT. }
  assert (HR1 : forall A, In A R1 -> In A G /\ ~ (In x A /\ In y A)).
  { intros A HA; rewrite ER1 in HA; apply filter_In in HA as [HAG Hn].
    apply Bool.negb_true_iff in Hn; split; [exact HAG|].
    intros [H1 H2]; assert (E : containsb [x;y] A = true)
      by (apply containsb_true_iff; intros t [<-|[<-|[]]]; assumption); congruence. }
  assert (HR2 : forall A, In A R2 -> In A R1 /\ ~ (In x A /\ In z A)).
  { intros A HA; rewrite ER2 in HA; apply filter_In in HA as [HA1 Hn].
    apply Bool.negb_true_iff in Hn; split; [exact HA1|].
    intros [H1 H2]; assert (E : containsb [x;z] A = true)
      by (apply containsb_true_iff; intros t [<-|[<-|[]]]; assumption); congruence. }
  assert (HR3 : forall A, In A R3 -> In A R2 /\ ~ (In y A /\ In z A)).
  { intros A HA; rewrite ER3 in HA; apply filter_In in HA as [HA2 Hn].
    apply Bool.negb_true_iff in Hn; split; [exact HA2|].
    intros [H1 H2]; assert (E : containsb [y;z] A = true)
      by (apply containsb_true_iff; intros t [<-|[<-|[]]]; assumption); congruence. }
  assert (HR3G : forall A, In A R3 -> In A G)
    by (intros A HA; apply HR1, HR2, HR3; exact HA).
  assert (HTx : forall A, In A Tx -> In A G /\ In x A /\ ~ In y A /\ ~ In z A).
  { intros A HA; rewrite ETx in HA; apply filter_In in HA as [HA3 Hx].
    apply memb_true_iff in Hx.
    destruct (HR3 A HA3) as [HA2 _]; destruct (HR2 A HA2) as [HA1 N2]; destruct (HR1 A HA1) as [HAG N1].
    repeat split; try assumption; [intros Hy; apply N1; tauto | intros Hz; apply N2; tauto]. }
  assert (HTy : forall A, In A Ty -> In A G /\ In y A /\ ~ In x A /\ ~ In z A).
  { intros A HA; rewrite ETy in HA; apply filter_In in HA as [HA4 Hy].
    apply memb_true_iff in Hy.
    rewrite ER4 in HA4; apply filter_In in HA4 as [HA3 Hnx].
    apply Bool.negb_true_iff, memb_false_iff in Hnx.
    destruct (HR3 A HA3) as [HA2 N3].
    repeat split; try assumption; [apply HR3G; exact HA3 | intros Hz; apply N3; tauto]. }
  assert (HTz : forall A, In A Tz -> In A G /\ In z A /\ ~ In x A /\ ~ In y A).
  { intros A HA; rewrite ETz in HA; apply filter_In in HA as [HA4 Hny].
    apply Bool.negb_true_iff, memb_false_iff in Hny.
    rewrite ER4 in HA4; apply filter_In in HA4 as [HA3 Hnx].
    apply Bool.negb_true_iff, memb_false_iff in Hnx.
    pose proof (HR3G A HA3) as HAG.
    repeat split; try assumption.
    destruct (Hint A [x;y;z] HAG HMG) as [w [HwA Hw]].
    destruct Hw as [<-|[<-|[<-|[]]]]; [contradiction | contradiction | exact HwA]. }
  (* the reverse directions: a member avoiding two of x,y,z lands in its layer *)
  assert (HinTy : forall A, In A G -> In y A -> ~ In x A -> ~ In z A -> In A Ty).
  { intros A HAG Hy Hnx Hnz.
    rewrite ETy; apply filter_In; split; [|apply memb_true_iff; exact Hy].
    rewrite ER4; apply filter_In; split; [|apply Bool.negb_true_iff, memb_false_iff; exact Hnx].
    rewrite ER3; apply filter_In; split; [|apply Bool.negb_true_iff; apply (Hnotc [y;z] A z); [right; left; reflexivity | exact Hnz]].
    rewrite ER2; apply filter_In; split; [|apply Bool.negb_true_iff; apply (Hnotc [x;z] A x); [left; reflexivity | exact Hnx]].
    rewrite ER1; apply filter_In; split; [exact HAG|apply Bool.negb_true_iff; apply (Hnotc [x;y] A x); [left; reflexivity | exact Hnx]]. }
  assert (HinTz : forall A, In A G -> In z A -> ~ In x A -> ~ In y A -> In A Tz).
  { intros A HAG Hz Hnx Hny.
    rewrite ETz; apply filter_In; split; [|apply Bool.negb_true_iff, memb_false_iff; exact Hny].
    rewrite ER4; apply filter_In; split; [|apply Bool.negb_true_iff, memb_false_iff; exact Hnx].
    rewrite ER3; apply filter_In; split; [|apply Bool.negb_true_iff; apply (Hnotc [y;z] A y); [left; reflexivity | exact Hny]].
    rewrite ER2; apply filter_In; split; [|apply Bool.negb_true_iff; apply (Hnotc [x;z] A x); [left; reflexivity | exact Hnx]].
    rewrite ER1; apply filter_In; split; [exact HAG|apply Bool.negb_true_iff; apply (Hnotc [x;y] A x); [left; reflexivity | exact Hnx]]. }
  assert (HinTx : forall A, In A G -> In x A -> ~ In y A -> ~ In z A -> In A Tx).
  { intros A HAG Hx Hny Hnz.
    rewrite ETx; apply filter_In; split; [|apply memb_true_iff; exact Hx].
    rewrite ER3; apply filter_In; split; [|apply Bool.negb_true_iff; apply (Hnotc [y;z] A y); [left; reflexivity | exact Hny]].
    rewrite ER2; apply filter_In; split; [|apply Bool.negb_true_iff; apply (Hnotc [x;z] A z); [right; left; reflexivity | exact Hnz]].
    rewrite ER1; apply filter_In; split; [exact HAG|apply Bool.negb_true_iff; apply (Hnotc [x;y] A y); [right; left; reflexivity | exact Hny]]. }
  (* the three layers are nonempty *)
  assert (Hmeet : forall A, In A G -> In x A \/ In y A \/ In z A).
  { intros A HAG; destruct (Hint A [x;y;z] HAG HMG) as [w [HwA Hw]].
    destruct Hw as [<-|[<-|[<-|[]]]]; tauto. }
  destruct (Htau y z) as [Ax [HAxG [Hny Hnz]]].
  assert (HAx : In Ax Tx) by (apply HinTx; try assumption; destruct (Hmeet Ax HAxG) as [H|[H|H]]; tauto).
  destruct (Htau x z) as [Ay [HAyG [Hnx' Hnz']]].
  assert (HAy : In Ay Ty) by (apply HinTy; try assumption; destruct (Hmeet Ay HAyG) as [H|[H|H]]; tauto).
  destruct (Htau x y) as [Az [HAzG [Hnx'' Hny'']]].
  assert (HAz : In Az Tz) by (apply HinTz; try assumption; destruct (Hmeet Az HAzG) as [H|[H|H]]; tauto).
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
  (* the tail graphs *)
  assert (HSx : Simple (map (rem x) Tx))
    by (apply (@tail_simple G Tx x HU HD); [intros A HA; destruct (HTx A HA); tauto | exact HdTx]).
  assert (HSy : Simple (map (rem y) Ty))
    by (apply (@tail_simple G Ty y HU HD); [intros A HA; destruct (HTy A HA); tauto | exact HdTy]).
  assert (HSz : Simple (map (rem z) Tz))
    by (apply (@tail_simple G Tz z HU HD); [intros A HA; destruct (HTz A HA); tauto | exact HdTz]).
  assert (Hxy' : CrossInt (map (rem x) Tx) (map (rem y) Ty)).
  { apply (@tail_cross G Tx Ty x y Hint Hxy);
      [intros A HA; destruct (HTx A HA) as [? [? [? ?]]]; tauto
      | intros A HA; destruct (HTy A HA) as [? [? [? ?]]]; tauto]. }
  assert (Hxz' : CrossInt (map (rem x) Tx) (map (rem z) Tz)).
  { apply (@tail_cross G Tx Tz x z Hint Hxz);
      [intros A HA; destruct (HTx A HA) as [? [? [? ?]]]; tauto
      | intros A HA; destruct (HTz A HA) as [? [? [? ?]]]; tauto]. }
  assert (Hyz' : CrossInt (map (rem y) Ty) (map (rem z) Tz)).
  { apply (@tail_cross G Ty Tz y z Hint Hyz);
      [intros A HA; destruct (HTy A HA) as [? [? [? ?]]]; tauto
      | intros A HA; destruct (HTz A HA) as [? [? [? ?]]]; tauto]. }
  assert (Hex : In (rem x Ax) (map (rem x) Tx)) by (apply in_map; exact HAx).
  assert (Hey : In (rem y Ay) (map (rem y) Ty)) by (apply in_map; exact HAy).
  assert (Hez : In (rem z Az) (map (rem z) Tz)) by (apply in_map; exact HAz).
  (* covering number 3 on the tails *)
  pose proof (@tau2_of x y z Tx Ty Tz Ax Hmeet Hxy Hxz Hyz HTx HinTy HinTz HAx) as H2x.
  pose proof (@tau2_of y x z Ty Tx Tz Ay
                ltac:(intros A HA; destruct (Hmeet A HA) as [H|[H|H]]; tauto)
                ltac:(congruence) Hyz Hxz HTy HinTx
                ltac:(intros A HA H1 H2 H3; apply HinTz; assumption) HAy) as H2y.
  pose proof (@tau2_of z x y Tz Tx Ty Az
                ltac:(intros A HA; destruct (Hmeet A HA) as [H|[H|H]]; tauto)
                ltac:(congruence) ltac:(congruence) Hxy HTz
                ltac:(intros A HA H1 H2 H3; apply HinTx; assumption)
                ltac:(intros A HA H1 H2 H3; apply HinTy; assumption) HAz) as H2z.
  (* the graph lemma *)
  pose proof (@nine (map (rem x) Tx) (map (rem y) Ty) (map (rem z) Tz)
                (rem x Ax) (rem y Ay) (rem z Az) HSx HSy HSz Hxy' Hxz' Hyz' Hex Hey Hez
                H2x H2y H2z) as HN.
  rewrite !map_length in HN.
  (* the two-point layers *)
  assert (Bxz : length Cxz <= core_count (rem y Ay) (map (rem y) Ty)).
  { apply (@two_layer_bound x z y Cxz Ty Ay Hxz Hxy ltac:(congruence)).
    - intros A HA; rewrite ECxz in HA; apply filter_In in HA as [HA1 Hc].
      apply containsb_true_iff in Hc; destruct (HR1 A HA1) as [HAG N1].
      repeat split; [exact HAG | apply Hc; left; reflexivity | apply Hc; right; left; reflexivity
                     | intros Hy; apply N1; split; [apply Hc; left; reflexivity | exact Hy]].
    - intros S; rewrite ECxz, ER1.
      repeat (eapply Nat.le_trans; [apply deg_filter_le|]); apply Nat.le_refl.
    - intros B HB; destruct (HTy B HB) as [? [? [? ?]]]; tauto.
    - exact HAy. }
  assert (Byz : length Cyz <= core_count (rem x Ax) (map (rem x) Tx)).
  { apply (@two_layer_bound y z x Cyz Tx Ax Hyz ltac:(congruence) ltac:(congruence)).
    - intros A HA; rewrite ECyz in HA; apply filter_In in HA as [HA2 Hc].
      apply containsb_true_iff in Hc; destruct (HR2 A HA2) as [HA1 N2]; destruct (HR1 A HA1) as [HAG N1].
      repeat split; [exact HAG | apply Hc; left; reflexivity | apply Hc; right; left; reflexivity
                     | intros Hx; apply N1; split; [exact Hx | apply Hc; left; reflexivity]].
    - intros S; rewrite ECyz, ER2, ER1.
      repeat (eapply Nat.le_trans; [apply deg_filter_le|]); apply Nat.le_refl.
    - intros B HB; destruct (HTx B HB) as [? [? [? ?]]]; tauto.
    - exact HAx. }
  (* Cxy: M itself plus the members avoiding z *)
  assert (Bxy : length Cxy <= 1 + core_count (rem z Az) (map (rem z) Tz)).
  { assert (Hpart : length Cxy = length (filter (memb z) Cxy)
                                + length (filter (fun A => negb (memb z A)) Cxy))
      by apply length_filter_partition.
    assert (HM1 : length (filter (memb z) Cxy) <= 1).
    { rewrite ECxy, filter_filter.
      eapply Nat.le_trans; [apply (@filter_length_mono _ _ (containsb [x;y;z]))|].
      - intros A HA H; apply Bool.andb_true_iff in H as [H1 H2].
        apply containsb_true_iff in H1; apply memb_true_iff in H2.
        apply containsb_true_iff; intros t [<-|[<-|[<-|[]]]];
          [apply H1; left; reflexivity | apply H1; right; left; reflexivity | exact H2].
      - apply (@tt_triple G HU HD); [apply triple_nodup; assumption | reflexivity]. }
    assert (HM2 : length (filter (fun A => negb (memb z A)) Cxy)
                  <= core_count (rem z Az) (map (rem z) Tz)).
    { apply (@two_layer_bound x y z _ Tz Az Hxy Hxz Hyz).
      - intros A HA; apply filter_In in HA as [HA HnzA].
        apply Bool.negb_true_iff, memb_false_iff in HnzA.
        rewrite ECxy in HA; apply filter_In in HA as [HAG Hc]; apply containsb_true_iff in Hc.
        repeat split; [exact HAG | apply Hc; left; reflexivity | apply Hc; right; left; reflexivity | exact HnzA].
      - intros S; rewrite ECxy.
        repeat (eapply Nat.le_trans; [apply deg_filter_le|]); apply Nat.le_refl.
      - intros B HB; destruct (HTz B HB) as [? [? [? ?]]]; tauto.
      - exact HAz. }
    lia. }
  lia.
Qed.

End TauThreeTenBound.

(** ** The theorem

    3-uniform, distinct, intersecting, covering number at least 3: at most
    ten members. No Rao condition, no Frankl, no axiom. *)

Theorem tau_three_ten :
  forall (G : Family),
    Uniform 3 G -> Distinct G ->
    (forall C D, In C G -> In D G -> exists w, In w C /\ In w D) ->
    (forall p q, exists C, In C G /\ ~ In p C /\ ~ In q C) ->
    length G <= 10.
Proof.
  intros G HU HD Hint Htau.
  destruct G as [|M G0] eqn:EG; [simpl; lia | rewrite <- EG in *].
  assert (HM : In M G) by (rewrite EG; left; reflexivity).
  destruct (@uniform_mem 3 G M HU HM) as [Hl Hnd].
  destruct M as [|x [|y [|z [|w M']]]]; simpl in Hl; try discriminate.
  destruct (nodup3 Hnd) as [Hxy [Hxz Hyz]].
  exact (@ten_core G HU HD Hint Htau x y z HM Hxy Hxz Hyz).
Qed.

Theorem tau_three_at_most_ten : TauThreeAtMost 10.
Proof.
  intros G HU HD Hint Htau; exact (@tau_three_ten G HU HD Hint Htau).
Qed.

(** ** Ten is attained: the 3-subsets of a 5-set *)

Definition k53 : Family :=
  [[0;1;2];[0;1;3];[0;1;4];[0;2;3];[0;2;4];[0;3;4];[1;2;3];[1;2;4];[1;3;4];[2;3;4]].

Lemma k53_uniform : Uniform 3 k53.
Proof. apply uniformb_correct; reflexivity. Qed.

Lemma k53_distinct : Distinct k53.
Proof. apply distinctb_correct; reflexivity. Qed.

Lemma k53_intersecting :
  forall C D, In C k53 -> In D k53 -> exists w, In w C /\ In w D.
Proof. apply int_b_correct; vm_compute; reflexivity. Qed.

Lemma k53_bounded : forall C, In C k53 -> forall x, In x C -> x < 5.
Proof.
  intros C HC x Hx; unfold k53 in HC; simpl in HC.
  repeat (destruct HC as [<-|HC];
          [destruct Hx as [<-|[<-|[<-|[]]]]; lia |]); contradiction.
Qed.

Lemma k53_exists_missing :
  forall a b, a < 6 -> b < 6 ->
    existsb (fun C => andb (negb (memb a C)) (negb (memb b C))) k53 = true.
Proof.
  intros a b Ha Hb.
  do 6 (destruct a as [|a];
        [ do 6 (destruct b as [|b]; [vm_compute; reflexivity|]); exfalso; lia |]);
    exfalso; lia.
Qed.

Lemma k53_memb_min :
  forall p C, In C k53 -> memb p C = memb (Nat.min p 5) C.
Proof.
  intros p C HC; destruct (le_lt_dec 5 p) as [Hle|Hlt].
  - rewrite Nat.min_r by lia.
    assert (E1 : memb p C = false).
    { destruct (memb p C) eqn:E; [|reflexivity].
      exfalso; apply memb_true_iff in E; pose proof (@k53_bounded C HC p E); lia. }
    assert (E2 : memb 5 C = false).
    { destruct (memb 5 C) eqn:E; [|reflexivity].
      exfalso; apply memb_true_iff in E; pose proof (@k53_bounded C HC 5 E); lia. }
    rewrite E1, E2; reflexivity.
  - rewrite Nat.min_l by lia; reflexivity.
Qed.

Lemma k53_tau_three :
  forall p q, exists C, In C k53 /\ ~ In p C /\ ~ In q C.
Proof.
  intros p q.
  pose proof (k53_exists_missing (a := Nat.min p 5) (b := Nat.min q 5)
                ltac:(pose proof (Nat.le_min_r p 5); lia)
                ltac:(pose proof (Nat.le_min_r q 5); lia)) as Hex.
  apply existsb_exists in Hex as [C [HC Hcond]].
  apply Bool.andb_true_iff in Hcond as [H1 H2].
  apply Bool.negb_true_iff in H1; apply Bool.negb_true_iff in H2.
  exists C; repeat split; [exact HC | | ];
    intros Hin; apply memb_true_iff in Hin;
    rewrite (k53_memb_min _ HC) in Hin; congruence.
Qed.

Theorem ten_is_attained :
  Uniform 3 k53 /\ Distinct k53
  /\ (forall C D, In C k53 -> In D k53 -> exists w, In w C /\ In w D)
  /\ (forall p q, exists C, In C k53 /\ ~ In p C /\ ~ In q C)
  /\ length k53 = 10.
Proof.
  split; [exact k53_uniform|]. split; [exact k53_distinct|].
  split; [exact k53_intersecting|]. split; [exact k53_tau_three | reflexivity].
Qed.

(** So [tau_three_ten] is sharp: [TauThreeAtMost 9] is false. *)

Theorem tau_three_at_most_nine_is_false : ~ TauThreeAtMost 9.
Proof.
  intros H.
  pose proof (H k53 k53_uniform k53_distinct k53_intersecting k53_tau_three) as Hb.
  simpl in Hb; lia.
Qed.

(** ** Frankl's theorem, as [TwoCover.v] states it, is now a theorem *)

Theorem frankl_tau_three : FranklTauThree.
Proof. intros G HU HD Hint Htau; exact (@tau_three_ten G HU HD Hint Htau). Qed.

(** Every corollary [TwoCover.v] drew from the hypothesis [FranklTauThree]
    is therefore unconditional; the two it named are restated here. *)

Corollary r_star_three_three_at_most_four_now_from_ten : SpreadYieldsDisjoint 3 3 4.
Proof. apply r_star_three_three_at_most_four_from_frankl, frankl_tau_three. Qed.

(** ** [I(3,3) = 10]: the intersecting bound under Rao's caps at [r = 3]

    An intersecting 3-uniform family with every point in at most 9 members
    and every pair in at most 3 has at most ten members: a star has at
    most [r^2 = 9] ([TwoCover.one_cover_bound]), a family covered by two
    points and by neither alone has at most [3r + 1 = 10]
    ([TwoCoverSharp.two_cover_at_most_3r_plus_1]), and a family of covering
    number three has at most ten ([tau_three_ten]). The 3-subsets of a
    5-set attain it under the caps, so [I(3,3) = 10] exactly -- the value
    docs/roadmap.md section 56 had been citing. *)

Theorem i_three_three_at_most_ten :
  forall (G : Family),
    Uniform 3 G -> RaoSpread 3 G 3 ->
    (forall C D, In C G -> In D G -> exists x, In x C /\ In x D) ->
    length G <= 10.
Proof.
  intros G HU HR Hint.
  destruct (existsb (fun a => existsb
     (fun b => forallb (fun C => orb (memb a C) (memb b C)) G) (concat G)) (concat G))
    eqn:Esearch.
  - apply existsb_exists in Esearch as [a [Ha Hb']].
    apply existsb_exists in Hb' as [b [Hb Hall]].
    assert (Hcov : forall C, In C G -> In a C \/ In b C).
    { intros C HC.
      pose proof (proj1 (forallb_forall _ G) Hall C HC) as E.
      apply Bool.orb_true_iff in E as [E|E];
        [left | right]; apply memb_true_iff; exact E. }
    destruct (Nat.eq_dec a b) as [<-|Hab].
    { pose proof (@one_cover_bound 3 G a HR ltac:(intros C HC; destruct (Hcov C HC); assumption)); lia. }
    (* does one of the two points cover alone? *)
    destruct (existsb (fun C => negb (memb b C)) G) eqn:Eb; cycle 1.
    { pose proof (@one_cover_bound 3 G b HR ltac:(intros C HC;
        pose proof (existsb_false_forall _ _ _ Eb C HC) as E;
        apply Bool.negb_false_iff, memb_true_iff in E; exact E)); lia. }
    destruct (existsb (fun C => negb (memb a C)) G) eqn:Ea; cycle 1.
    { pose proof (@one_cover_bound 3 G a HR ltac:(intros C HC;
        pose proof (existsb_false_forall _ _ _ Ea C HC) as E;
        apply Bool.negb_false_iff, memb_true_iff in E; exact E)); lia. }
    apply existsb_exists in Eb as [C [HC HCb]]; apply Bool.negb_true_iff, memb_false_iff in HCb.
    apply existsb_exists in Ea as [D [HD HDa]]; apply Bool.negb_true_iff, memb_false_iff in HDa.
    pose proof (@two_cover_at_most_3r_plus_1 3 G a b HU HR Hint Hcov Hab ltac:(lia)
                  ltac:(exists C; tauto) ltac:(exists D; tauto)); lia.
  - destruct G as [|M G0] eqn:EG; [simpl; lia | rewrite <- EG in *].
    assert (HGne : G <> []) by (rewrite EG; discriminate).
    assert (Htau : forall p q, exists C, In C G /\ ~ In p C /\ ~ In q C)
      by (intros p q; exact (@covers_dec_search G p q Esearch HGne)).
    assert (HDist : Distinct G) by (apply (@rao_uniform_distinct 3 3 G); [lia | exact HU | exact HR]).
    exact (@tau_three_ten G HU HDist Hint Htau).
Qed.

Lemma k53_rao_spread : RaoSpread 3 k53 3.
Proof.
  apply (@rao_witness_none 3 k53 3).
  - apply (@Uniform_NoDup 3 k53 k53_uniform).
  - vm_compute; reflexivity.
Qed.

Theorem i_three_three_is_ten :
  (forall (G : Family),
     Uniform 3 G -> RaoSpread 3 G 3 ->
     (forall C D, In C G -> In D G -> exists x, In x C /\ In x D) ->
     length G <= 10)
  /\ (Uniform 3 k53 /\ RaoSpread 3 k53 3
      /\ (forall C D, In C k53 -> In D k53 -> exists x, In x C /\ In x D)
      /\ length k53 = 10).
Proof.
  split; [exact i_three_three_at_most_ten|].
  split; [exact k53_uniform|]. split; [exact k53_rao_spread|].
  split; [exact k53_intersecting | reflexivity].
Qed.
