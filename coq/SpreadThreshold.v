(** * SpreadThreshold.v -- upper bounds on the sharp spread threshold
      [r*(m,3)].

    [SpreadReduction.SpreadYieldsDisjoint n k r] says every [r]-spread
    [m]-uniform family ([1 ≤ m ≤ n]) of more than [r^m] distinct sets has
    [k] pairwise disjoint members, and [spread_reduction] turns it into
    [f(m,k) ≤ r^m + 1]. Write [r*(m,k)] for the least [r] that works.
    Then

<<
      r*(m,3) bounded in m   <->   the sunflower conjecture at k = 3
>>

    so the sequence [r*(1,3), r*(2,3), ...] *is* the problem, one finite
    question at a time (docs/roadmap.md §18.5). Two terms are measured,
    [r*(2,3) = r*(3,3) = 3]; the only general upper bound the development
    had is [SpreadReduction.elementary_spread_disjoint], which gives
    [r*(n,3) ≤ 2n + 1] and knows nothing about spreadness beyond the
    number of points in a cover.

    This file proves two better ones from the structure a counterexample
    is forced to have.

    - [cover_spread_disjoint]: [r*(n,3) ≤ 2n]. A family with no three
      pairwise disjoint members has a maximal matching of at most two
      members, so at most [2m] points cover it, and Rao's absolute spread
      condition caps each point at [r^(m-1)] members.

    - [quadratic_spread_disjoint]: [r*(n,3) ≤ 1 + √(3n² - 4n + 3)],
      about [1.74 n], and [r*(4,3) ≤ 7]. This one uses the fact that
      separates the spread route from every restricted-class route
      (docs/roadmap.md §21.7): for [B] *any* member of a family with no
      three pairwise disjoint members, [{C ∈ F : C ∩ B = ∅}] is
      **intersecting** ([miss_member_intersecting]). Splitting [F]
      against a matching [{A, B}] gives two intersecting pieces and a
      cross piece, and the cross piece is covered by *pairs* rather than
      points — a pair has degree [r^(m-2)], and that is where the saving
      is.

    Nothing here is conditional on [ALWZ.Rao20_lemma2]: these are bounds
    on the threshold, not consequences of the spread lemma. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower Pigeonhole ErdosRado Spread
     SpreadReduction Intersecting.
Import ListNotations.

Set Implicit Arguments.

(** [incl_firstn] and [NoDup_firstn] are [SpreadReduction]'s; this file
    imports them rather than restating them. The development already
    carries four copies of the filter-partition identity under four
    names, and rule 1 is to grep before naming. *)

(** ** No [k] pairwise disjoint members

    The negation of [SpreadYieldsDisjoint]'s conclusion, named so the
    counting theorems can take it as a hypothesis. *)

Definition NoKDisjoint (k : nat) (F : Family) : Prop :=
  ~ (exists S : list (list nat),
        incl S F /\ NoDup S /\ length S = k /\ PairwiseDisjoint S).

(** Packaging: three concrete pairwise disjoint members are the
    existential [SpreadYieldsDisjoint] asks for. Distinctness of the
    three *lists* is free — disjoint nonempty sets are unequal. *)

Lemma three_disjoint_witness :
  forall (F : Family) (A B C : list nat),
    In A F -> In B F -> In C F ->
    A <> [] -> B <> [] -> C <> [] ->
    Disjoint A B -> Disjoint A C -> Disjoint B C ->
    exists S : list (list nat),
      incl S F /\ NoDup S /\ length S = 3 /\ PairwiseDisjoint S.
Proof.
  intros F A B C HA HB HC HAn HBn HCn HAB HAC HBC.
  assert (Hne : forall X Y : list nat, X <> [] -> Disjoint X Y -> X <> Y).
  { intros X Y HX HD Heq; subst Y.
    destruct X as [|x X']; [contradiction|].
    exact (HD x (or_introl eq_refl) (or_introl eq_refl)). }
  assert (HBA : Disjoint B A) by (intros x Hx Hx'; exact (HAB x Hx' Hx)).
  assert (HCA : Disjoint C A) by (intros x Hx Hx'; exact (HAC x Hx' Hx)).
  assert (HCB : Disjoint C B) by (intros x Hx Hx'; exact (HBC x Hx' Hx)).
  assert (Hincl : incl [A; B; C] F).
  { intros X HX; simpl in HX; destruct HX as [<-|[<-|[<-|[]]]]; assumption. }
  assert (Hnd : NoDup [A; B; C]).
  { constructor.
    - intros HIn; simpl in HIn; destruct HIn as [Heq|[Heq|[]]].
      + exact (Hne B A HBn HBA Heq).
      + exact (Hne C A HCn HCA Heq).
    - constructor.
      + intros HIn; simpl in HIn; destruct HIn as [Heq|[]].
        exact (Hne C B HCn HCB Heq).
      + constructor; [intros [] | constructor]. }
  assert (Hpd : PairwiseDisjoint [A; B; C]).
  { intros X Y HX HY HXY; simpl in HX, HY.
    destruct HX as [<-|[<-|[<-|[]]]]; destruct HY as [<-|[<-|[<-|[]]]];
      try congruence; assumption. }
  exists [A; B; C]; split; [exact Hincl | split; [exact Hnd | split; [reflexivity | exact Hpd]]].
Qed.

(** ** The cover bound

    If every member of [F] contains one of the sets [Ts], and no member
    of [Ts] has degree above [K], then [|F| ≤ |Ts| * K].

    [Pigeonhole.pigeonhole_family] is the [|T| = 1] case. The general
    form is what the cross piece of the decomposition needs, where the
    covering sets are *pairs*. *)

Lemma deg_filter_le : forall T p F, deg T (filter p F) <= deg T F.
Proof.
  intros T p F; unfold deg.
  induction F as [|A F IH]; simpl; [lia|].
  destruct (p A); simpl.
  - destruct (containsb T A); simpl; lia.
  - destruct (containsb T A); simpl; lia.
Qed.

Theorem cover_by_sets :
  forall (Ts : list (list nat)) (K : nat) (F : Family),
    (forall A, In A F -> exists T, In T Ts /\ Subset T A) ->
    (forall T, In T Ts -> deg T F <= K) ->
    length F <= length Ts * K.
Proof.
  induction Ts as [|T Ts IH]; intros K F Hcov Hdeg.
  - destruct F as [|A F']; simpl; [lia|].
    destruct (Hcov A (or_introl eq_refl)) as [T [HT _]]; destruct HT.
  - simpl.
    assert (Hlen : length F
                   = deg T F
                     + length (filter (fun A => negb (containsb T A)) F)).
    { unfold deg; apply length_filter_partition. }
    assert (HG : length (filter (fun A => negb (containsb T A)) F)
                 <= length Ts * K).
    { apply IH.
      - intros A HA; apply filter_In in HA as [HAF Hneg].
        destruct (Hcov A HAF) as [T' [HT' Hsub]].
        destruct HT' as [<-|HT'].
        + exfalso; apply Bool.negb_true_iff in Hneg.
          apply containsb_true_iff in Hsub; congruence.
        + exists T'; split; assumption.
      - intros T' HT'.
        eapply Nat.le_trans; [apply deg_filter_le | apply Hdeg; right; exact HT']. }
    assert (HT : deg T F <= K) by (apply Hdeg; left; reflexivity).
    lia.
Qed.

Corollary cover_by_points :
  forall (X : list nat) (K : nat) (F : Family),
    (forall A, In A F -> exists x, In x X /\ In x A) ->
    (forall x, In x X -> deg [x] F <= K) ->
    length F <= length X * K.
Proof.
  intros X K F Hcov Hdeg.
  assert (Hlen : length (map (fun x => [x]) X) = length X) by apply map_length.
  rewrite <- Hlen.
  apply cover_by_sets.
  - intros A HA; destruct (Hcov A HA) as [x [HxX HxA]].
    exists [x]; split.
    + apply in_map_iff; exists x; split; [reflexivity | exact HxX].
    + intros y Hy; destruct Hy as [<-|[]]; exact HxA.
  - intros T HT; apply in_map_iff in HT as [x [<- HxX]]; apply Hdeg; exact HxX.
Qed.

(** Rao's spread condition, specialised to a single point. *)

Lemma rao_point : forall m r F x,
    RaoSpread m F r -> deg [x] F <= r ^ (m - 1).
Proof.
  intros m r F x HR.
  specialize (HR [x] ltac:(constructor; [intros [] | constructor])
                 ltac:(discriminate)).
  exact HR.
Qed.

(** ** The matching a counterexample is allowed

    With no three pairwise disjoint members a maximal matching has at
    most two members; its union has at most [2m] points; the family is
    covered by those points. *)

Lemma matching_at_most_two :
  forall (F : Family) (S : list (list nat)),
    NoKDisjoint 3 F -> incl S F -> NoDup S -> PairwiseDisjoint S ->
    length S <= 2.
Proof.
  intros F S Hno Hincl Hnd Hpd.
  destruct (le_lt_dec (length S) 2) as [Hle|Hgt]; [exact Hle|exfalso].
  apply Hno.
  exists (firstn 3 S); repeat split.
  - intros X HX; apply Hincl; eapply incl_firstn; exact HX.
  - apply NoDup_firstn; exact Hnd.
  - rewrite firstn_length; lia.
  - intros X Y HX HY HXY; apply Hpd;
      [eapply incl_firstn; exact HX | eapply incl_firstn; exact HY | exact HXY].
Qed.

Lemma concat_uniform_length :
  forall m (F : Family) (S : list (list nat)),
    Uniform m F -> incl S F -> length S <= 2 -> length (concat S) <= 2 * m.
Proof.
  intros m F S HU Hincl Hlen.
  unfold Uniform in HU; rewrite Forall_forall in HU.
  destruct S as [|A [|B [|C S']]]; simpl in *; try lia.
  - destruct (HU A (Hincl A (or_introl eq_refl))) as [HA _].
    rewrite app_length; simpl; lia.
  - destruct (HU A (Hincl A (or_introl eq_refl))) as [HA _].
    destruct (HU B (Hincl B (or_intror (or_introl eq_refl)))) as [HB _].
    repeat rewrite app_length; simpl; lia.
Qed.

Lemma uniform_nonempty :
  forall m (F : Family), 1 <= m -> Uniform m F ->
    Forall (fun A : list nat => A <> []) F.
Proof.
  intros m F Hm HU.
  unfold Uniform in HU; rewrite Forall_forall in HU |- *.
  intros A HA; destruct (HU A HA) as [Hlen _].
  destruct A as [|a A']; [simpl in Hlen; lia | discriminate].
Qed.

(** ** [|F| ≤ 2m·r^(m-1)] for a family with no three pairwise disjoint
       members. *)

Theorem no_three_disjoint_cover_bound :
  forall m r (F : Family),
    1 <= m -> Uniform m F -> RaoSpread m F r ->
    NoKDisjoint 3 F ->
    length F <= 2 * m * r ^ (m - 1).
Proof.
  intros m r F Hm HU HR Hno.
  destruct (max_disjoint_cover (uniform_nonempty Hm HU))
    as [S [Hincl [Hnd [Hpd Hcov]]]].
  assert (Hle2 : length S <= 2) by (eapply matching_at_most_two; eassumption).
  assert (Hpts : length (concat S) <= 2 * m)
    by (eapply concat_uniform_length; eassumption).
  assert (Hbound : length F <= length (concat S) * r ^ (m - 1)).
  { apply cover_by_points.
    - intros A HA.
      destruct (@cover_provides_element F S A Hcov HA) as [x [HxA Hxc]].
      exists x; split; assumption.
    - intros x _; eapply rao_point; exact HR. }
  assert (Hmul : length (concat S) * r ^ (m - 1) <= 2 * m * r ^ (m - 1))
    by (apply Nat.mul_le_mono_r; exact Hpts).
  lia.
Qed.

(** ** [r*(n,3) ≤ 2n]

    One better than [SpreadReduction.elementary_spread_disjoint]. The
    proof is constructive: [max_disjoint_cover] either hands back three
    pairwise disjoint members, which is the conclusion, or a cover of at
    most [2m] points, which contradicts the size hypothesis. *)

Theorem cover_spread_disjoint :
  forall n, 1 <= n -> SpreadYieldsDisjoint n 3 (2 * n).
Proof.
  intros n Hn m F Hm Hmn HU HD Hsize HR.
  destruct (max_disjoint_cover (uniform_nonempty Hm HU))
    as [M [Hincl [Hnd [Hpd Hcov]]]].
  destruct (le_lt_dec (length M) 2) as [Hle|Hgt].
  - exfalso.
    assert (Hpts : length (concat M) <= 2 * m)
      by (eapply concat_uniform_length; eassumption).
    assert (Hbound : length F <= length (concat M) * (2 * n) ^ (m - 1)).
    { apply cover_by_points.
      - intros A HA.
        destruct (@cover_provides_element F M A Hcov HA) as [x [HxA Hxc]].
        exists x; split; assumption.
      - intros x _; eapply rao_point; exact HR. }
    assert (Hmul : length (concat M) * (2 * n) ^ (m - 1)
                   <= (2 * n) * (2 * n) ^ (m - 1))
      by (apply Nat.mul_le_mono_r; lia).
    assert (Hpow : (2 * n) ^ m = (2 * n) * (2 * n) ^ (m - 1)).
    { replace m with (S (m - 1)) at 1 by lia; reflexivity. }
    lia.
  - exists (firstn 3 M); repeat split.
    + intros X HX; apply Hincl; eapply incl_firstn; exact HX.
    + apply NoDup_firstn; exact Hnd.
    + rewrite firstn_length; lia.
    + intros X Y HX HY HXY; apply Hpd;
        [eapply incl_firstn; exact HX | eapply incl_firstn; exact HY | exact HXY].
Qed.

(** ** Covering by pairs

    The cover bound is only as good as the sets doing the covering, and a
    *pair* has degree [r^(m-2)] where a point has [r^(m-1)]. Everything
    below is the bookkeeping for covering a family by pairs drawn from
    two lists, one point from each. *)

Definition distinct_pairs (X Y : list nat) : list (list nat) :=
  flat_map (fun x => map (fun y => [x; y]) (remove Nat.eq_dec x Y)) X.

Lemma in_distinct_pairs :
  forall X Y x y, In x X -> In y Y -> x <> y -> In [x; y] (distinct_pairs X Y).
Proof.
  intros X Y x y HX HY Hne; unfold distinct_pairs.
  apply in_flat_map; exists x; split; [exact HX|].
  apply in_map_iff; exists y; split; [reflexivity|].
  apply in_in_remove; [exact (fun H => Hne (eq_sym H)) | exact HY].
Qed.

Lemma distinct_pairs_shape :
  forall X Y T, In T (distinct_pairs X Y) -> exists x y, T = [x; y] /\ x <> y.
Proof.
  intros X Y T HT; unfold distinct_pairs in HT.
  apply in_flat_map in HT as [x [_ HT]].
  apply in_map_iff in HT as [y [<- Hy]].
  apply in_remove in Hy as [_ Hne].
  exists x, y; split; [reflexivity | exact (fun H => Hne (eq_sym H))].
Qed.

Lemma remove_length_in :
  forall (a : nat) (l : list nat),
    NoDup l -> In a l -> length (remove Nat.eq_dec a l) = length l - 1.
Proof.
  intros a l; induction l as [|x l IH]; intros Hnd Hin; [inversion Hin|].
  inversion Hnd as [|? ? Hx Hnd']; subst; simpl.
  destruct (Nat.eq_dec a x) as [<-|Hne].
  - rewrite notin_remove by exact Hx; lia.
  - simpl; destruct Hin as [<-|Hin]; [congruence|].
    rewrite (IH Hnd' Hin).
    assert (1 <= length l) by (destruct l; [inversion Hin | simpl; lia]).
    lia.
Qed.

Lemma remove_length_le :
  forall (a : nat) (l : list nat), length (remove Nat.eq_dec a l) <= length l.
Proof.
  intros a l; induction l as [|x l IH]; simpl; [lia|].
  destruct (Nat.eq_dec a x); simpl; lia.
Qed.

Lemma distinct_pairs_length_le :
  forall X Y, length (distinct_pairs X Y) <= length X * length Y.
Proof.
  intros X Y; unfold distinct_pairs.
  induction X as [|x X IH]; simpl; [lia|].
  rewrite app_length, map_length.
  pose proof (remove_length_le x Y); lia.
Qed.

Lemma distinct_pairs_length_self :
  forall X, NoDup X -> length (distinct_pairs X X) <= length X * (length X - 1).
Proof.
  intros X Hnd; unfold distinct_pairs.
  assert (Hgen : forall Z, (forall x, In x Z -> In x X) ->
            length (flat_map (fun x => map (fun y => [x; y]) (remove Nat.eq_dec x X)) Z)
            <= length Z * (length X - 1)).
  { induction Z as [|z Z IH]; intros Hsub; simpl; [lia|].
    rewrite app_length, map_length.
    rewrite (@remove_length_in z X Hnd (Hsub z (or_introl eq_refl))).
    assert (length (flat_map (fun x => map (fun y => [x; y]) (remove Nat.eq_dec x X)) Z)
            <= length Z * (length X - 1))
      by (apply IH; intros y Hy; apply Hsub; right; exact Hy).
    lia. }
  apply Hgen; intros x Hx; exact Hx.
Qed.

(** The pair analogue of [cover_by_points]: every member of [G] contains
    two distinct points, one from [X] and one from [Y]. *)

Theorem cover_by_pairs :
  forall (X Y : list nat) (K : nat) (G : Family),
    (forall C, In C G ->
       exists x y, x <> y /\ In x X /\ In y Y /\ In x C /\ In y C) ->
    (forall T, NoDup T -> length T = 2 -> deg T G <= K) ->
    length G <= length (distinct_pairs X Y) * K.
Proof.
  intros X Y K G Hcov Hdeg.
  apply cover_by_sets.
  - intros C HC; destruct (Hcov C HC) as [x [y [Hne [HxX [HyY [HxC HyC]]]]]].
    exists [x; y]; split.
    + apply in_distinct_pairs; assumption.
    + intros z Hz; simpl in Hz; destruct Hz as [<-|[<-|[]]]; assumption.
  - intros T HT.
    destruct (@distinct_pairs_shape X Y T HT) as [x [y [-> Hne]]].
    apply Hdeg; [| reflexivity].
    constructor;
      [intros [Hz|[]]; exact (Hne (eq_sym Hz))
      | constructor; [intros [] | constructor]].
Qed.

(** Rao's spread condition on a two-point set. *)

Lemma rao_pair : forall m r F x y,
    RaoSpread m F r -> x <> y -> deg [x; y] F <= r ^ (m - 2).
Proof.
  intros m r F x y HR Hne.
  specialize (HR [x; y]
    ltac:(constructor; [intros [Hz|[]]; exact (Hne (eq_sym Hz))
                       | constructor; [intros [] | constructor]])
    ltac:(discriminate)).
  exact HR.
Qed.

(** ** The piece bound

    [G] is intersecting, every member meets the [m]-set [A], and [G]
    inherits the spread condition. Then [G] is much smaller than the
    [m * r^(m-1)] a bare cover argument gives.

    The proof is a two-way split. Either some member of [G] meets [A] in
    exactly one point [a1] — then [G] splits into the members through
    [a1], at most [r^(m-1)] of them, and the rest, which meet both
    [A \ {a1}] and [C0 \ {a1}] and so are covered by [(m-1)^2] *pairs* —
    or every member meets [A] twice, and then [G] is covered by pairs
    from [A] alone. *)

Lemma cap_in : forall A C x, In x (filter (fun z => memb z C) A) <-> In x A /\ In x C.
Proof.
  intros A C x; split.
  - intros H; apply filter_In in H as [HA HC]; split;
      [exact HA | apply memb_true_iff; exact HC].
  - intros [HA HC]; apply filter_In; split;
      [exact HA | apply memb_true_iff; exact HC].
Qed.

Lemma two_distinct_of_length :
  forall (l : list nat), NoDup l -> 2 <= length l ->
    exists x y, x <> y /\ In x l /\ In y l.
Proof.
  intros l Hnd Hlen.
  destruct l as [|x [|y l']]; simpl in Hlen; try lia.
  inversion Hnd as [|? ? Hx _]; subst.
  exists x, y; repeat split.
  - intros <-; apply Hx; left; reflexivity.
  - left; reflexivity.
  - right; left; reflexivity.
Qed.

Lemma deg_single_star : forall x G, deg [x] G = length (filter (fun C => memb x C) G).
Proof. intros x G; apply deg_single. Qed.

Theorem intersecting_piece_bound :
  forall m r (G : Family) (A : list nat),
    2 <= m -> m - 1 <= r ->
    Uniform m G ->
    (forall T, NoDup T -> T <> [] -> deg T G <= r ^ (m - length T)) ->
    NoDup A -> length A = m ->
    (forall C, In C G -> exists x, In x A /\ In x C) ->
    (forall C D, In C G -> In D G -> exists x, In x C /\ In x D) ->
    length G <= r ^ (m - 1) + (m - 1) * (m - 1) * r ^ (m - 2).
Proof.
  intros m r G A Hm Hr HU HGdeg HAnd HAlen HmeetA Hint.
  assert (HUf : forall C, In C G -> length C = m /\ NoDup C).
  { unfold Uniform in HU; rewrite Forall_forall in HU; exact HU. }
  assert (Hpairdeg : forall T, NoDup T -> length T = 2 -> deg T G <= r ^ (m - 2)).
  { intros T HT Hlen2.
    replace (m - 2) with (m - length T) by lia.
    apply HGdeg; [exact HT | destruct T; [simpl in Hlen2; lia | discriminate]]. }
  destruct (existsb (fun C => Nat.eqb (length (filter (fun z => memb z C) A)) 1) G)
    eqn:Hex.
  - (* some member meets A exactly once *)
    apply existsb_exists in Hex as [C0 [HC0 Heq1]].
    apply Nat.eqb_eq in Heq1.
    destruct (filter (fun z => memb z C0) A) as [|a1 tl] eqn:Ecap;
      [simpl in Heq1; lia|].
    destruct tl; [|simpl in Heq1; lia].
    assert (Ha1 : In a1 A /\ In a1 C0).
    { apply cap_in; rewrite Ecap; left; reflexivity. }
    assert (Huniq : forall x, In x A -> In x C0 -> x = a1).
    { intros x HxA HxC.
      assert (Hin : In x (filter (fun z => memb z C0) A)) by (apply cap_in; split; assumption).
      rewrite Ecap in Hin; destruct Hin as [<-|[]]; reflexivity. }
    destruct (HUf C0 HC0) as [HC0len HC0nd].
    (* split G on membership of a1 *)
    assert (Hsplit : length G
                     = length (filter (fun C => memb a1 C) G)
                       + length (filter (fun C => negb (memb a1 C)) G))
      by apply length_filter_partition.
    assert (Hstar : length (filter (fun C => memb a1 C) G) <= r ^ (m - 1)).
    { rewrite <- deg_single_star.
      replace (m - 1) with (m - length [a1]) by (simpl; lia).
      apply HGdeg; [constructor; [intros [] | constructor] | discriminate]. }
    assert (Hrest : length (filter (fun C => negb (memb a1 C)) G)
                    <= (m - 1) * (m - 1) * r ^ (m - 2)).
    { set (Grest := filter (fun C => negb (memb a1 C)) G).
      assert (Hbound : length Grest
                       <= length (distinct_pairs (remove Nat.eq_dec a1 A)
                                                 (remove Nat.eq_dec a1 C0))
                          * r ^ (m - 2)).
      { apply cover_by_pairs.
        - intros C HC; unfold Grest in HC; apply filter_In in HC as [HCG Hno].
          apply Bool.negb_true_iff, memb_false_iff in Hno.
          destruct (HmeetA C HCG) as [x [HxA HxC]].
          destruct (Hint C C0 HCG HC0) as [y [HyC HyC0]].
          assert (Hxa : x <> a1) by (intros <-; contradiction).
          assert (Hya : y <> a1) by (intros <-; contradiction).
          exists x, y; repeat split.
          + intros <-; exact (Hxa (Huniq x HxA HyC0)).
          + apply in_in_remove; [exact Hxa | exact HxA].
          + apply in_in_remove; [exact Hya | exact HyC0].
          + exact HxC.
          + exact HyC.
        - intros T HT Hlen2.
          eapply Nat.le_trans; [apply deg_filter_le | apply Hpairdeg; assumption]. }
      assert (Hlen : length (distinct_pairs (remove Nat.eq_dec a1 A)
                                            (remove Nat.eq_dec a1 C0))
                     <= (m - 1) * (m - 1)).
      { eapply Nat.le_trans; [apply distinct_pairs_length_le|].
        rewrite (@remove_length_in a1 A HAnd (proj1 Ha1)).
        rewrite (@remove_length_in a1 C0 HC0nd (proj2 Ha1)).
        rewrite HAlen, HC0len; lia. }
      assert (Hmul : length (distinct_pairs (remove Nat.eq_dec a1 A)
                                            (remove Nat.eq_dec a1 C0)) * r ^ (m - 2)
                     <= (m - 1) * (m - 1) * r ^ (m - 2))
        by (apply Nat.mul_le_mono_r; exact Hlen).
      lia. }
    lia.
  - (* every member meets A at least twice *)
    assert (Htwo : forall C, In C G ->
              exists x y, x <> y /\ In x A /\ In y A /\ In x C /\ In y C).
    { intros C HC.
      assert (Hne1 : Nat.eqb (length (filter (fun z => memb z C) A)) 1 = false).
      { destruct (Nat.eqb (length (filter (fun z => memb z C) A)) 1) eqn:E;
          [|reflexivity].
        assert (Hcontra : existsb
                  (fun D => Nat.eqb (length (filter (fun z => memb z D) A)) 1) G = true)
          by (apply existsb_exists; exists C; split; assumption).
        congruence. }
      apply Nat.eqb_neq in Hne1.
      destruct (HmeetA C HC) as [x0 [Hx0A Hx0C]].
      assert (Hge1 : 1 <= length (filter (fun z => memb z C) A)).
      { assert (In x0 (filter (fun z => memb z C) A)) by (apply cap_in; split; assumption).
        destruct (filter (fun z => memb z C) A); [contradiction | simpl; lia]. }
      assert (Hnd : NoDup (filter (fun z => memb z C) A)) by (apply NoDup_filter; exact HAnd).
      destruct (two_distinct_of_length Hnd ltac:(lia)) as [x [y [Hxy [Hx Hy]]]].
      apply cap_in in Hx as [HxA HxC]; apply cap_in in Hy as [HyA HyC].
      exists x, y; repeat split; assumption. }
    assert (Hbound : length G <= length (distinct_pairs A A) * r ^ (m - 2)).
    { apply cover_by_pairs; [exact Htwo | intros T HT Hlen2; apply Hpairdeg; assumption]. }
    assert (Hlen : length (distinct_pairs A A) <= m * (m - 1)).
    { pose proof (distinct_pairs_length_self HAnd) as H; rewrite HAlen in H; exact H. }
    assert (Hmul : length (distinct_pairs A A) * r ^ (m - 2) <= m * (m - 1) * r ^ (m - 2))
      by (apply Nat.mul_le_mono_r; exact Hlen).
    (* m*(m-1) <= r + (m-1)*(m-1), since m - 1 <= r *)
    assert (Hcmp : m * (m - 1) <= r + (m - 1) * (m - 1)) by nia.
    assert (Hpow : r ^ (m - 1) = r * r ^ (m - 2)).
    { replace (m - 1) with (S (m - 2)) by lia; reflexivity. }
    nia.
Qed.

(** ** The cross piece

    Members meeting both halves of the matching. Each contains a point of
    [A] and a point of [B], and those are distinct because [A] and [B]
    are, so [m^2] pairs cover the piece — at [r^(m-2)] apiece. *)

Theorem cross_piece_bound :
  forall m r (G : Family) (A B : list nat),
    2 <= m ->
    (forall T, NoDup T -> T <> [] -> deg T G <= r ^ (m - length T)) ->
    length A = m -> length B = m -> Disjoint A B ->
    (forall C, In C G ->
       (exists x, In x A /\ In x C) /\ (exists y, In y B /\ In y C)) ->
    length G <= m * m * r ^ (m - 2).
Proof.
  intros m r G A B Hm HGdeg HAlen HBlen HAB Hmeet.
  assert (Hbound : length G <= length (distinct_pairs A B) * r ^ (m - 2)).
  { apply cover_by_pairs.
    - intros C HC; destruct (Hmeet C HC) as [[x [HxA HxC]] [y [HyB HyC]]].
      exists x, y; repeat split; try assumption.
      intros <-; exact (HAB x HxA HyB).
    - intros T HT Hlen2.
      replace (m - 2) with (m - length T) by lia.
      apply HGdeg; [exact HT | destruct T; [simpl in Hlen2; lia | discriminate]]. }
  assert (Hlen : length (distinct_pairs A B) <= m * m).
  { pose proof (distinct_pairs_length_le A B) as H; rewrite HAlen, HBlen in H; exact H. }
  assert (Hmul : length (distinct_pairs A B) * r ^ (m - 2) <= m * m * r ^ (m - 2))
    by (apply Nat.mul_le_mono_r; exact Hlen).
  lia.
Qed.

(** ** Deciding the conclusion

    Every theorem below is stated constructively: either the three
    pairwise disjoint members exist and are exhibited, or they do not and
    the counting applies. The search over triples is what decides it. *)

Lemma uniform_filter : forall m p (F : Family), Uniform m F -> Uniform m (filter p F).
Proof.
  intros m p F HU; unfold Uniform in HU |- *; rewrite Forall_forall in HU |- *.
  intros A HA; apply filter_In in HA as [HAF _]; exact (HU A HAF).
Qed.

Lemma decide_three_disjoint :
  forall m (F : Family), 1 <= m -> Uniform m F ->
    (exists S : list (list nat),
        incl S F /\ NoDup S /\ length S = 3 /\ PairwiseDisjoint S)
    \/ NoKDisjoint 3 F.
Proof.
  intros m F Hm HU.
  assert (Hne : forall A, In A F -> A <> []).
  { unfold Uniform in HU; rewrite Forall_forall in HU.
    intros A HA; destruct (HU A HA) as [Hlen _].
    destruct A as [|a A']; [simpl in Hlen; lia | discriminate]. }
  destruct (existsb (fun A => existsb (fun B => existsb
              (fun C => (disjointb A B && disjointb A C && disjointb B C)%bool)
              F) F) F)
    eqn:Hex.
  - left.
    apply existsb_exists in Hex as [A [HA HB]].
    apply existsb_exists in HB as [B [HB HC]].
    apply existsb_exists in HC as [C [HC Hall]].
    apply Bool.andb_true_iff in Hall as [Hall HBC].
    apply Bool.andb_true_iff in Hall as [HAB HAC].
    apply disjointb_correct in HAB; apply disjointb_correct in HAC;
      apply disjointb_correct in HBC.
    exact (@three_disjoint_witness F A B C HA HB HC
             (Hne A HA) (Hne B HB) (Hne C HC) HAB HAC HBC).
  - right; intros [S [Hincl [Hnd [Hlen Hpd]]]].
    destruct S as [|A [|B [|C [|D S']]]]; simpl in Hlen; try lia.
    assert (HA : In A F) by (apply Hincl; left; reflexivity).
    assert (HB : In B F) by (apply Hincl; right; left; reflexivity).
    assert (HC : In C F) by (apply Hincl; right; right; left; reflexivity).
    inversion Hnd as [|? ? HAn Hnd1]; subst.
    inversion Hnd1 as [|? ? HBn Hnd2]; subst.
    assert (HAB : Disjoint A B).
    { apply Hpd; [left; reflexivity | right; left; reflexivity
                 | intros <-; apply HAn; left; reflexivity]. }
    assert (HAC : Disjoint A C).
    { apply Hpd; [left; reflexivity | right; right; left; reflexivity
                 | intros <-; apply HAn; right; left; reflexivity]. }
    assert (HBC : Disjoint B C).
    { apply Hpd; [right; left; reflexivity | right; right; left; reflexivity
                 | intros <-; apply HBn; left; reflexivity]. }
    assert (Hcontra : existsb (fun A' => existsb (fun B' => existsb
              (fun C' => (disjointb A' B' && disjointb A' C'
                          && disjointb B' C')%bool) F) F) F
                      = true).
    { apply existsb_exists; exists A; split; [exact HA|].
      apply existsb_exists; exists B; split; [exact HB|].
      apply existsb_exists; exists C; split; [exact HC|].
      repeat (apply Bool.andb_true_iff; split); apply disjointb_correct; assumption. }
    congruence.
Qed.

(** ** The decomposition

    Against a matching [{A, B}] a family with no three pairwise disjoint
    members splits into three pieces:

    - [{C : C ∩ B = ∅}] — intersecting, and every member meets [A];
    - [{C : C ∩ A = ∅}] — intersecting, and every member meets [B];
    - the rest, which meet both.

    The first two are [intersecting_piece_bound], the third is
    [cross_piece_bound]. The intersecting-ness is the point: it is what
    [IntersectingSpread.link_of_intersecting_not_intersecting] says a
    *link* never gives you, and it is available here only because the
    hypothesis is about the family rather than about a link. *)

Lemma uniform_mem : forall m (F : Family) A,
    Uniform m F -> In A F -> length A = m /\ NoDup A.
Proof.
  intros m F A HU HA; unfold Uniform in HU; rewrite Forall_forall in HU.
  exact (HU A HA).
Qed.

(** The fact the whole decomposition turns on.

    For [B] *any* member of a family with no three pairwise disjoint
    members, the subfamily missing [B] is intersecting. The proof is one
    step — two disjoint members missing [B] are three pairwise disjoint
    sets together with [B] — and it is the reason this route does not pay
    the toll [IntersectingSpread.link_of_intersecting_not_intersecting]
    charges every route that works inside a restricted class. There the
    intersecting-ness has to be re-established at each level, and the
    link of an intersecting family is not intersecting; here it is
    produced once, by a hypothesis about the whole family. *)

Lemma miss_member_intersecting :
  forall m (F : Family) (B C D : list nat),
    1 <= m -> Uniform m F -> NoKDisjoint 3 F ->
    In B F -> In C F -> In D F ->
    Disjoint C B -> Disjoint D B ->
    ~ Disjoint C D.
Proof.
  intros m F B C D Hm HU Hno HB HC HD HCB HDB HCD.
  assert (Hne : forall A, In A F -> A <> []).
  { intros A HA; destruct (@uniform_mem m F A HU HA) as [Hlen _].
    destruct A as [|a A']; [simpl in Hlen; lia | discriminate]. }
  apply Hno.
  exact (@three_disjoint_witness F C D B HC HD HB
           (Hne C HC) (Hne D HD) (Hne B HB) HCD HCB HDB).
Qed.

Lemma meets_of_not_disjointb : forall C D,
    disjointb C D = false -> exists x, In x D /\ In x C.
Proof.
  intros C D H; apply disjointb_false_iff in H as [x [HxC HxD]].
  exists x; split; assumption.
Qed.

Theorem quadratic_no_three_disjoint_bound :
  forall m r (F : Family),
    2 <= m -> m - 1 <= r ->
    Uniform m F -> RaoSpread m F r ->
    NoKDisjoint 3 F ->
    length F <= 2 * (r ^ (m - 1) + (m - 1) * (m - 1) * r ^ (m - 2))
                + m * m * r ^ (m - 2).
Proof.
  intros m r F Hm Hr HU HR Hno.
  assert (Hne : forall A, In A F -> A <> []).
  { intros A HA; destruct (@uniform_mem m F A HU HA) as [Hlen _].
    destruct A as [|a A']; [simpl in Hlen; lia | discriminate]. }
  assert (Hpow2 : 0 <= r ^ (m - 2)) by lia.
  destruct (existsb (fun A => existsb (fun B => disjointb A B) F) F) eqn:Hex.
  - (* the family has a matching of size two *)
    apply existsb_exists in Hex as [A [HA HB']].
    apply existsb_exists in HB' as [B [HB HABb]].
    apply disjointb_correct in HABb.
    destruct (@uniform_mem m F A HU HA) as [HAlen HAnd].
    destruct (@uniform_mem m F B HU HB) as [HBlen HBnd].
    set (f := fun C : list nat => disjointb C B).
    set (g := fun C : list nat => disjointb C A).
    set (R := filter (fun C => negb (f C)) F).
    assert (Hsplit1 : length F = length (filter f F) + length R)
      by (unfold R; apply length_filter_partition).
    assert (Hsplit2 : length R = length (filter g R)
                                 + length (filter (fun C => negb (g C)) R))
      by apply length_filter_partition.
    (* piece one: misses B, hence meets A, and is intersecting *)
    assert (HP1 : length (filter f F)
                  <= r ^ (m - 1) + (m - 1) * (m - 1) * r ^ (m - 2)).
    { apply (@intersecting_piece_bound m r (filter f F) A); try assumption.
      - apply uniform_filter; exact HU.
      - intros T HT HTn.
        eapply Nat.le_trans; [apply deg_filter_le | apply HR; assumption].
      - intros C HC; apply filter_In in HC as [HCF HCf].
        unfold f in HCf; apply disjointb_correct in HCf.
        destruct (disjointb C A) eqn:ECA.
        + exfalso; apply disjointb_correct in ECA.
          apply Hno; exact (@three_disjoint_witness F C A B HCF HA HB
                              (Hne C HCF) (Hne A HA) (Hne B HB) ECA HCf HABb).
        + apply meets_of_not_disjointb; exact ECA.
      - intros C D HC HD.
        apply filter_In in HC as [HCF HCf]; apply filter_In in HD as [HDF HDf].
        unfold f in HCf, HDf.
        apply disjointb_correct in HCf; apply disjointb_correct in HDf.
        destruct (disjointb C D) eqn:ECD.
        + exfalso; apply disjointb_correct in ECD.
          exact (@miss_member_intersecting m F B C D ltac:(lia) HU Hno
                   HB HCF HDF HCf HDf ECD).
        + apply disjointb_false_iff in ECD as [x [HxC HxD]].
          exists x; split; assumption. }
    (* piece two: misses A, hence meets B, and is intersecting *)
    assert (HP2 : length (filter g R)
                  <= r ^ (m - 1) + (m - 1) * (m - 1) * r ^ (m - 2)).
    { apply (@intersecting_piece_bound m r (filter g R) B); try assumption.
      - apply uniform_filter; apply uniform_filter; exact HU.
      - intros T HT HTn.
        eapply Nat.le_trans; [apply deg_filter_le|].
        eapply Nat.le_trans; [apply deg_filter_le | apply HR; assumption].
      - intros C HC; apply filter_In in HC as [HCR _].
        apply filter_In in HCR as [_ HCf].
        apply Bool.negb_true_iff in HCf; unfold f in HCf.
        apply meets_of_not_disjointb; exact HCf.
      - intros C D HC HD.
        apply filter_In in HC as [HCR HCg]; apply filter_In in HD as [HDR HDg].
        apply filter_In in HCR as [HCF _]; apply filter_In in HDR as [HDF _].
        unfold g in HCg, HDg.
        apply disjointb_correct in HCg; apply disjointb_correct in HDg.
        destruct (disjointb C D) eqn:ECD.
        + exfalso; apply disjointb_correct in ECD.
          exact (@miss_member_intersecting m F A C D ltac:(lia) HU Hno
                   HA HCF HDF HCg HDg ECD).
        + apply disjointb_false_iff in ECD as [x [HxC HxD]].
          exists x; split; assumption. }
    (* piece three: meets both *)
    assert (HP3 : length (filter (fun C => negb (g C)) R) <= m * m * r ^ (m - 2)).
    { apply (@cross_piece_bound m r (filter (fun C => negb (g C)) R) A B);
        try assumption.
      - intros T HT HTn.
        eapply Nat.le_trans; [apply deg_filter_le|].
        eapply Nat.le_trans; [apply deg_filter_le | apply HR; assumption].
      - intros C HC; apply filter_In in HC as [HCR HCg].
        apply filter_In in HCR as [_ HCf].
        apply Bool.negb_true_iff in HCf; unfold f in HCf.
        apply Bool.negb_true_iff in HCg; unfold g in HCg.
        split; apply meets_of_not_disjointb; assumption. }
    lia.
  - (* the family is intersecting *)
    destruct F as [|A0 F0]; [simpl length; apply Nat.le_0_l|].
    assert (HA0 : In A0 (A0 :: F0)) by (left; reflexivity).
    destruct (@uniform_mem m (A0 :: F0) A0 HU HA0) as [HA0len HA0nd].
    assert (Hint : forall C D, In C (A0 :: F0) -> In D (A0 :: F0) ->
                     exists x, In x C /\ In x D).
    { intros C D HC HD.
      destruct (disjointb C D) eqn:ECD.
      - exfalso.
        assert (Hcontra : existsb
                  (fun A => existsb (fun B => disjointb A B) (A0 :: F0)) (A0 :: F0)
                = true).
        { apply existsb_exists; exists C; split; [exact HC|].
          apply existsb_exists; exists D; split; [exact HD | exact ECD]. }
        congruence.
      - apply disjointb_false_iff in ECD as [x [HxC HxD]].
        exists x; split; assumption. }
    assert (HB : length (A0 :: F0)
                 <= r ^ (m - 1) + (m - 1) * (m - 1) * r ^ (m - 2)).
    { apply (@intersecting_piece_bound m r (A0 :: F0) A0); try assumption.
      intros C HC; destruct (Hint C A0 HC HA0) as [x [HxC HxA0]].
      exists x; split; assumption. }
    lia.
Qed.

(** ** The threshold bound

    The three pieces sum to [r^(m-2) * (2r + 3m² - 4m + 2)], and [r^m] is
    [r^(m-2) * r²]. So a counterexample at uniformity [m] forces

<<
      r² < 2r + 3m² - 4m + 2,      i.e.   r < 1 + √(3m² - 4m + 3),
>>

    and the least [r] failing that is an upper bound for [r*(m,3)]. The
    condition is written without subtraction as
    [2r + 3m² + 2 ≤ r² + 4m]; it is monotone in [m], so asking it at [n]
    covers every [m ≤ n]. *)

Theorem quadratic_spread_disjoint :
  forall n r,
    1 <= n ->
    2 * r + 3 * n * n + 2 <= r * r + 4 * n ->
    SpreadYieldsDisjoint n 3 r.
Proof.
  intros n r Hn Hcond m F Hm Hmn HU HD Hsize HR.
  destruct (@decide_three_disjoint m F ltac:(lia) HU) as [Hyes|Hno];
    [exact Hyes | exfalso].
  (* the condition at n implies the condition at every m <= n *)
  assert (Hmono : 3 * m * m + 4 * n <= 3 * n * n + 4 * m) by nia.
  assert (Hcm : 2 * r + 3 * m * m + 2 <= r * r + 4 * m) by lia.
  assert (Hr1 : m <= r + 1).
  { destruct (le_lt_dec m (r + 1)) as [H|H]; [exact H | exfalso; nia]. }
  destruct (Nat.eq_dec m 1) as [Hm1|Hm2].
  - subst m.
    assert (Hb : length F <= 2 * 1 * r ^ (1 - 1))
      by (eapply no_three_disjoint_cover_bound; eauto).
    simpl in Hb, Hsize.
    assert (3 <= r) by nia.
    lia.
  - assert (Hm2' : 2 <= m) by lia.
    assert (Hr1' : m - 1 <= r) by lia.
    pose proof (@quadratic_no_three_disjoint_bound m r F Hm2' Hr1' HU HR Hno) as Hb.
    (* r^(m-1) = r * r^(m-2) and r^m = r * r * r^(m-2) *)
    assert (E1 : r ^ (m - 1) = r * r ^ (m - 2))
      by (replace (m - 1) with (S (m - 2)) by lia; reflexivity).
    assert (E2 : r ^ m = r * (r * r ^ (m - 2))).
    { replace m with (S (S (m - 2))) at 1 by lia; reflexivity. }
    rewrite E1 in Hb.
    set (p := r ^ (m - 2)) in *.
    (* |F| <= (2r + 3m^2 - 4m + 2) * p <= r^2 * p = r^m *)
    assert (Hle : 2 * (r * p + (m - 1) * (m - 1) * p) + m * m * p
                  <= r * (r * p)) by nia.
    lia.
Qed.

(** [r*(4,3) ≤ 7]: [2·7 + 3·16 + 2 = 64 ≤ 49 + 16 = 65].

    The development's previous best at [n = 4] was
    [SpreadReduction.elementary_spread_disjoint], which gives 9. *)

Corollary r_star_four_at_most_seven : SpreadYieldsDisjoint 4 3 7.
Proof. apply quadratic_spread_disjoint; lia. Qed.

Corollary r_star_three_at_most_six : SpreadYieldsDisjoint 3 3 6.
Proof. apply quadratic_spread_disjoint; lia. Qed.

Corollary r_star_five_at_most_nine : SpreadYieldsDisjoint 5 3 9.
Proof. apply quadratic_spread_disjoint; lia. Qed.

Corollary r_star_six_at_most_eleven : SpreadYieldsDisjoint 6 3 11.
Proof. apply quadratic_spread_disjoint; lia. Qed.

(** The threshold bounds a sunflower number, which is the whole point of
    the sequence: [spread_reduction] turns [r*(4,3) ≤ 7] into
    [f(4,3) ≤ 7^4 + 1]. That number is far worse than what the direct
    theory gives at [m = 4] — the value of the bound is on [r*], not on
    [f], because it is [r*]'s *growth* that is the conjecture. *)

Corollary f_four_three_from_threshold : UpperBound 4 3 2402.
Proof.
  replace 2402 with (S (7 ^ 4)) by reflexivity.
  apply (@spread_reduction 4 3 7); [lia | lia | apply r_star_four_at_most_seven | lia].
Qed.

(** * The degree-sum split: [r*(m,3) ≤ φ·m + O(1)]

    [quadratic_no_three_disjoint_bound] splits the family three ways
    against a matching [{A, B}] and bounds each piece separately. That
    split throws away the one quantity Rao's condition makes cheap: the
    [m] point degrees *inside a single member* have never been summed.
    Doing so gives a **two-way** split that is both simpler and sharper.

    Against a single member [A] the family divides into

    - [{C : C ∩ A ≠ ∅}] — covered by the [m] points of [A], so at most
      [m·r^(m-1)] by [cover_by_points] and [rao_point];
    - [{C : C ∩ A = ∅}] — which must meet [B] (else [A], [B], [C] are
      three pairwise disjoint) and is intersecting by
      [miss_member_intersecting], so [intersecting_piece_bound] applies
      with [B] as its anchor.

    No third piece, and the cross piece — the one the quadratic bound
    charges [m²·r^(m-2)] for — is absorbed into the cover count at no
    cost. The result is

<<
      |F| ≤ m·r^(m-1) + (r^(m-1) + (m-1)²·r^(m-2))
          = (m+1)·r^(m-1) + (m-1)²·r^(m-2),
>>

    so [r^m] dominates as soon as [(m+1)·r + (m-1)² ≤ r²], i.e.

<<
      r ≥ ((m+1) + √((m+1)² + 4(m-1)²)) / 2  →  m·(1+√5)/2 = φ·m,
>>

    against the [√3·m = 1.732 m] of [quadratic_spread_disjoint]. The new
    condition is implied by the old one at every [(m, r)]
    (`rust/tests/spread_threshold.rs` pins that over a grid), so this is
    a strict improvement, and it moves four rows of the table:
    [r*(3,3) ≤ 5], [r*(5,3) ≤ 8], [r*(6,3) ≤ 10], [r*(10,3) ≤ 17].

    **Where this sits relative to the literature.** Through
    [spread_reduction] the bound gives [f(m,3) ≤ (φm)^m + 1], which is
    *worse* than the [m!·2^m + 1 ≈ (0.74m)^m] of Erdős–Rado 1960 and far
    worse than the [(O(log m))^m] of ALWZ / Rao /
    Bell–Chueluecha–Warnke. It is not a competitive bound on [f] and must
    not be quoted as one. Its content is about the sequence [r*(m,3)]
    itself, whose boundedness in [m] is the conjecture at [k = 3]: the
    first *open* term of that sequence is [m = 3], and this narrows it
    from [[3,6]] to [[3,5]]. *)

Theorem split_no_three_disjoint_bound :
  forall m r (F : Family),
    2 <= m -> m - 1 <= r ->
    Uniform m F -> RaoSpread m F r ->
    NoKDisjoint 3 F ->
    length F <= m * r ^ (m - 1)
                + (r ^ (m - 1) + (m - 1) * (m - 1) * r ^ (m - 2)).
Proof.
  intros m r F Hm Hr HU HR Hno.
  assert (Hne : forall A, In A F -> A <> []).
  { intros A HA; destruct (@uniform_mem m F A HU HA) as [Hlen _].
    destruct A as [|a A']; [simpl in Hlen; lia | discriminate]. }
  destruct (existsb (fun A => existsb (fun B => disjointb A B) F) F) eqn:Hex.
  - (* the family has a matching of size two *)
    apply existsb_exists in Hex as [A [HA HB']].
    apply existsb_exists in HB' as [B [HB HABb]].
    apply disjointb_correct in HABb.
    destruct (@uniform_mem m F A HU HA) as [HAlen HAnd].
    destruct (@uniform_mem m F B HU HB) as [HBlen HBnd].
    set (f := fun C : list nat => disjointb C A).
    assert (Hsplit : length F = length (filter f F)
                                + length (filter (fun C => negb (f C)) F))
      by apply length_filter_partition.
    (* the piece meeting A is covered by the m points of A *)
    assert (HM : length (filter (fun C => negb (f C)) F) <= m * r ^ (m - 1)).
    { assert (HMA : length (filter (fun C => negb (f C)) F)
                    <= length A * r ^ (m - 1)).
      { apply cover_by_points.
        - intros C HC; apply filter_In in HC as [_ HCf].
          apply Bool.negb_true_iff in HCf; unfold f in HCf.
          apply meets_of_not_disjointb; exact HCf.
        - intros x _.
          eapply Nat.le_trans; [apply deg_filter_le | eapply rao_point; exact HR]. }
      rewrite HAlen in HMA; exact HMA. }
    (* the piece missing A meets B, and is intersecting *)
    assert (HP : length (filter f F)
                 <= r ^ (m - 1) + (m - 1) * (m - 1) * r ^ (m - 2)).
    { apply (@intersecting_piece_bound m r (filter f F) B); try assumption.
      - apply uniform_filter; exact HU.
      - intros T HT HTn.
        eapply Nat.le_trans; [apply deg_filter_le | apply HR; assumption].
      - intros C HC; apply filter_In in HC as [HCF HCf].
        unfold f in HCf; apply disjointb_correct in HCf.
        destruct (disjointb C B) eqn:ECB.
        + exfalso; apply disjointb_correct in ECB.
          apply Hno; exact (@three_disjoint_witness F C A B HCF HA HB
                              (Hne C HCF) (Hne A HA) (Hne B HB) HCf ECB HABb).
        + apply meets_of_not_disjointb; exact ECB.
      - intros C D HC HD.
        apply filter_In in HC as [HCF HCf]; apply filter_In in HD as [HDF HDf].
        unfold f in HCf, HDf.
        apply disjointb_correct in HCf; apply disjointb_correct in HDf.
        destruct (disjointb C D) eqn:ECD.
        + exfalso; apply disjointb_correct in ECD.
          exact (@miss_member_intersecting m F A C D ltac:(lia) HU Hno
                   HA HCF HDF HCf HDf ECD).
        + apply disjointb_false_iff in ECD as [x [HxC HxD]].
          exists x; split; assumption. }
    lia.
  - (* the family is intersecting: the second piece is the whole family *)
    destruct F as [|A0 F0]; [simpl length; apply Nat.le_0_l|].
    assert (HA0 : In A0 (A0 :: F0)) by (left; reflexivity).
    destruct (@uniform_mem m (A0 :: F0) A0 HU HA0) as [HA0len HA0nd].
    assert (Hint : forall C D, In C (A0 :: F0) -> In D (A0 :: F0) ->
                     exists x, In x C /\ In x D).
    { intros C D HC HD.
      destruct (disjointb C D) eqn:ECD.
      - exfalso.
        assert (Hcontra : existsb
                  (fun A => existsb (fun B => disjointb A B) (A0 :: F0)) (A0 :: F0)
                = true).
        { apply existsb_exists; exists C; split; [exact HC|].
          apply existsb_exists; exists D; split; [exact HD | exact ECD]. }
        congruence.
      - apply disjointb_false_iff in ECD as [x [HxC HxD]].
        exists x; split; assumption. }
    assert (HB : length (A0 :: F0)
                 <= r ^ (m - 1) + (m - 1) * (m - 1) * r ^ (m - 2)).
    { apply (@intersecting_piece_bound m r (A0 :: F0) A0); try assumption.
      intros C HC; destruct (Hint C A0 HC HA0) as [x [HxC HxA0]].
      exists x; split; assumption. }
    lia.
Qed.

(** ** The threshold

    [(m+1)·r + (m-1)² ≤ r²] is monotone in [m], so asking it at [n]
    covers every [m ≤ n]. *)

Theorem split_spread_disjoint :
  forall n r,
    1 <= n -> 1 <= r ->
    (n + 1) * r + (n - 1) * (n - 1) <= r * r ->
    SpreadYieldsDisjoint n 3 r.
Proof.
  intros n r Hn Hr1 Hcond m F Hm Hmn HU HD Hsize HR.
  destruct (@decide_three_disjoint m F ltac:(lia) HU) as [Hyes|Hno];
    [exact Hyes | exfalso].
  (* the condition at n implies the condition at every m <= n *)
  assert (Hsub : m - 1 <= n - 1) by lia.
  assert (Hcm : (m + 1) * r + (m - 1) * (m - 1) <= r * r) by nia.
  destruct (Nat.eq_dec m 1) as [Hm1|Hm2].
  - subst m.
    assert (Hb : length F <= 2 * 1 * r ^ (1 - 1))
      by (eapply no_three_disjoint_cover_bound; eauto).
    simpl in Hb, Hsize.
    (* at m = 1 the condition reads 2r <= r², so r >= 2, but |F| <= 2 *)
    assert (2 <= r) by nia.
    lia.
  - assert (Hm2' : 2 <= m) by lia.
    assert (Hr1' : m - 1 <= r).
    { destruct (le_lt_dec (m - 1) r) as [H|H]; [exact H | exfalso; nia]. }
    pose proof (@split_no_three_disjoint_bound m r F Hm2' Hr1' HU HR Hno) as Hb.
    assert (E1 : r ^ (m - 1) = r * r ^ (m - 2))
      by (replace (m - 1) with (S (m - 2)) by lia; reflexivity).
    assert (E2 : r ^ m = r * (r * r ^ (m - 2))).
    { replace m with (S (S (m - 2))) at 1 by lia; reflexivity. }
    rewrite E1 in Hb.
    set (p := r ^ (m - 2)) in *.
    (* |F| <= ((m+1)r + (m-1)²)·p <= r²·p = r^m *)
    assert (Hle : m * (r * p) + (r * p + (m - 1) * (m - 1) * p)
                  <= r * (r * p)) by nia.
    lia.
Qed.

(** The four rows that move. Each is strictly below what
    [quadratic_spread_disjoint] gives at the same [n]: 6, 9, 11, 18. *)

Corollary r_star_three_at_most_five : SpreadYieldsDisjoint 3 3 5.
Proof. apply split_spread_disjoint; lia. Qed.

Corollary r_star_five_at_most_eight : SpreadYieldsDisjoint 5 3 8.
Proof. apply split_spread_disjoint; lia. Qed.

Corollary r_star_six_at_most_ten : SpreadYieldsDisjoint 6 3 10.
Proof. apply split_spread_disjoint; lia. Qed.

Corollary r_star_ten_at_most_seventeen : SpreadYieldsDisjoint 10 3 17.
Proof. apply split_spread_disjoint; lia. Qed.

(** [r*(4,3) ≤ 7] again, by the new route: [5·7 + 9 = 44 ≤ 49]. The
    quadratic bound also gives 7 here, so [m = 4] is the one small row
    where the two agree. *)

Corollary r_star_four_at_most_seven' : SpreadYieldsDisjoint 4 3 7.
Proof. apply split_spread_disjoint; lia. Qed.

(** The sunflower number the sharpened threshold yields at [m = 3].
    [spread_reduction] turns [r*(3,3) ≤ 5] into [f(3,3) ≤ 5^3 + 1 = 126].
    That is far behind [Sharp]'s exact small-case work — the point is the
    threshold, not the number. *)

Corollary f_three_three_from_split_threshold : UpperBound 3 3 126.
Proof.
  replace 126 with (S (5 ^ 3)) by reflexivity.
  apply (@spread_reduction 3 3 5); [lia | lia | apply r_star_three_at_most_five | lia].
Qed.
