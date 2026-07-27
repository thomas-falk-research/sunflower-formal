(** * SpreadReduction.v -- From spread families to sunflowers.

    This file contains the *deterministic half* of the modern
    (Alweiss–Lovett–Wu–Zhang / Rao) approach to the sunflower problem,
    fully machine-checked and axiom-free.

    The modern proof separates into two statements:

    - the **spread lemma** — an [r]-spread family of sets of size at
      most [n] contains [k] pairwise disjoint members, provided
      [r ≳ k log n]. This is the hard, analytic half.
    - the **reduction** — that statement, for *any* value of [r],
      already implies the sunflower bound [f(n,k) ≤ r^n + 1].

    [spread_reduction] below is the reduction, proved once and for all
    by strong induction on the uniformity. Its hypothesis is packaged
    as [SpreadYieldsDisjoint n k r].

    The induction is the ALWZ §4 / Rao "from spread to sunflowers"
    argument: given an [m]-uniform family with more than [r^m] members,
    either it is [r]-spread — and then the hypothesis hands us [k]
    pairwise disjoint members, which are a [k]-sunflower with empty
    core — or some nonempty [T] is contained in more than an
    [r^{-|T|}] fraction of the members, and the link
    [{A \ T : T ⊆ A ∈ F}] is a smaller-uniformity family that is still
    large enough for the induction hypothesis. A sunflower in the link
    lifts back to one in [F] by merging [T] into the core
    ([Spread.link_sunflower_lift]).

    Two things make this worth isolating:

    - It shrinks the trusted core. Instead of assuming the *conclusion*
      of the 2020 papers, [ALWZ.v] now assumes only their *spread
      lemma*, a self-contained combinatorial statement, and derives the
      bound from it here.
    - It is not vacuous. [elementary_spread_disjoint] proves the spread
      lemma outright for the (much larger) parameter [r = n(k-1)+1],
      by a maximal-disjoint-cover and pigeonhole argument. Feeding that
      into the reduction yields [spread_erdos_rado], an unconditional
      Erdős–Rado-quality bound [f(n,k) ≤ (n(k-1)+1)^n + 1] obtained
      entirely through the spread framework rather than by the 1960
      argument. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat Wf_nat.
From Sunflower Require Import Sets Sunflower Pigeonhole ErdosRado Spread.
Import ListNotations.

Set Implicit Arguments.

(** ** Small arithmetic and list helpers *)

Lemma pow_pos : forall r m, 1 <= r -> 1 <= r ^ m.
Proof.
  intros r m Hr; induction m as [|m IH]; simpl; [lia | nia].
Qed.

Lemma incl_firstn : forall {A : Type} (k : nat) (l : list A), incl (firstn k l) l.
Proof.
  intros A k l x Hx.
  rewrite <- (firstn_skipn k l); apply in_or_app; left; exact Hx.
Qed.

Lemma NoDup_firstn :
  forall {A : Type} (k : nat) (l : list A), NoDup l -> NoDup (firstn k l).
Proof.
  intros A k l; revert k.
  induction l as [|a l IH]; intros k Hnd; simpl.
  - destruct k; constructor.
  - destruct k as [|k']; [constructor|].
    simpl. inversion Hnd as [|? ? Hni Hnd']; subst.
    constructor.
    + intro Hin; apply Hni. apply (incl_firstn k' l); exact Hin.
    + apply IH; exact Hnd'.
Qed.

(** ** The hypothesis supplied by a spread lemma

    "Every [r]-spread distinct family of [m]-sets, [1 ≤ m ≤ n],
    contains [k] pairwise disjoint members." *)

Definition SpreadYieldsDisjoint (n k r : nat) : Prop :=
  forall (m : nat) (F : Family),
    1 <= m -> m <= n ->
    Uniform m F -> Distinct F -> 1 <= length F ->
    Spread F r ->
    exists S : list (list nat),
      incl S F /\ NoDup S /\ length S = k /\ PairwiseDisjoint S.

(** ** The reduction

    [SpreadYieldsDisjoint n k r] implies [f(m,k) ≤ r^m + 1] for every
    [m ≤ n]. *)

Theorem spread_reduction :
  forall n k r,
    2 <= k -> 1 <= r ->
    SpreadYieldsDisjoint n k r ->
    forall m, m <= n -> UpperBound m k (S (r ^ m)).
Proof.
  intros n k r Hk Hr Hsyd m.
  induction m as [m IH] using lt_wf_ind.
  intros Hmn F HU HD Hsize.
  destruct m as [|m'].
  - (* 0-uniform: every member is empty, so a distinct family has at
       most one member, but we are given at least two. *)
    exfalso.
    assert (H2 : 2 <= length F) by (simpl in Hsize; lia).
    destruct F as [|A [|B F'']]; simpl in H2; try lia.
    unfold Uniform in HU.
    inversion HU as [|? ? HUA HU']; subst.
    inversion HU' as [|? ? HUB HU'']; subst.
    destruct HUA as [HAlen _]; destruct HUB as [HBlen _].
    destruct A as [|a A0]; [|simpl in HAlen; lia].
    destruct B as [|b B0]; [|simpl in HBlen; lia].
    inversion HD as [|? ? Hni _]; subst.
    apply (Hni [] (or_introl eq_refl)); apply SetEq_refl.
  - (* uniformity S m' *)
    destruct (spread_witness F r) as [T|] eqn:Ewit.
    + (* Some member-subset T is over-represented: recurse into the link. *)
      apply spread_witness_some in Ewit as [Hcand Hviol].
      destruct (@in_cands_inv F T Hcand) as [A [HAF HTsub]].
      assert (HAnd : NoDup A).
      { unfold Uniform in HU; rewrite Forall_forall in HU.
        destruct (HU A HAF) as [_ Hnd]; exact Hnd. }
      assert (HAlen : length A = S m').
      { unfold Uniform in HU; rewrite Forall_forall in HU.
        destruct (HU A HAF) as [Hl _]; exact Hl. }
      assert (HTnd : NoDup T) by (apply (@subsets_NoDup A T HAnd HTsub)).
      assert (HTA : Subset T A) by (apply (@subsets_incl A T HTsub)).
      assert (HTlen : length T <= S m').
      { rewrite <- HAlen. apply NoDup_incl_length; assumption. }
      assert (HTpos : 1 <= length T).
      { destruct T as [|t T0]; [|simpl; lia].
        exfalso; simpl in Hviol; rewrite deg_nil in Hviol; lia. }
      (* The link is still large enough for the induction hypothesis. *)
      assert (Hdeg : r ^ (S m' - length T) < deg T F).
      { destruct (le_lt_dec (deg T F) (r ^ (S m' - length T))) as [Hle | Hlt];
          [|exact Hlt].
        exfalso.
        assert (Hmul : r ^ (length T) * deg T F
                       <= r ^ (length T) * r ^ (S m' - length T))
          by (apply Nat.mul_le_mono_l; exact Hle).
        rewrite <- Nat.pow_add_r in Hmul.
        replace (length T + (S m' - length T)) with (S m') in Hmul by lia.
        lia. }
      apply (@link_sunflower_lift T F k).
      assert (Hlt : S m' - length T < S m') by lia.
      assert (Hle : S m' - length T <= n) by lia.
      apply (IH (S m' - length T) Hlt Hle).
      * apply link_uniform; assumption.
      * apply link_distinct; exact HD.
      * rewrite length_link; lia.
    + (* No violation: F is r-spread, so the spread lemma applies. *)
      assert (HFnd : Forall (fun A : list nat => NoDup A) F).
      { unfold Uniform in HU. apply Forall_forall; intros A HA.
        rewrite Forall_forall in HU; destruct (HU A HA) as [_ Hnd]; exact Hnd. }
      assert (Hsp : Spread F r) by (apply (@spread_witness_none F r HFnd Ewit)).
      assert (HFpos : 1 <= length F).
      { pose proof (pow_pos (S m') Hr) as Hp; lia. }
      destruct (Hsyd (S m') F (le_n_S _ _ (Nat.le_0_l _)) Hmn HU HD HFpos Hsp)
        as [S0 [Hincl [Hnd0 [Hlen0 Hpd0]]]].
      assert (Hne : Forall (fun A : list nat => A <> []) S0).
      { apply Forall_forall; intros A HA.
        assert (HAF : In A F) by (apply Hincl; exact HA).
        unfold Uniform in HU; rewrite Forall_forall in HU.
        destruct (HU A HAF) as [HAlen _].
        destruct A; [simpl in HAlen; lia | discriminate]. }
      exists S0; split.
      * apply SubFamilySetEq_incl; exact Hincl.
      * apply k_pairwise_disjoint_sunflower; assumption.
Qed.

Corollary spread_reduction_top :
  forall n k r,
    2 <= k -> 1 <= r ->
    SpreadYieldsDisjoint n k r ->
    UpperBound n k (S (r ^ n)).
Proof.
  intros n k r Hk Hr Hsyd.
  apply (spread_reduction Hk Hr Hsyd); lia.
Qed.

(** ** An elementary spread lemma

    The 2020 papers prove [SpreadYieldsDisjoint] for [r = Θ(k log n)].
    A far weaker statement is elementary and is proved here in full:
    [r = n(k-1)+1] suffices.

    Proof. Take a maximal pairwise-disjoint subfamily [Scov]. If
    [|Scov| ≥ k] we are done. Otherwise [X = ⋃ Scov] has at most
    [(k-1)·m ≤ (k-1)·n < r] elements and every member of [F] meets [X],
    so by pigeonhole some [x ∈ X] satisfies [|X|·deg{x} ≥ |F|]; since
    [r > |X|] this gives [r·deg{x} > |F|], contradicting spreadness. *)

Theorem elementary_spread_disjoint :
  forall n k, 2 <= k -> SpreadYieldsDisjoint n k (n * (k - 1) + 1).
Proof.
  intros n k Hk m F Hm Hmn HU HD HFpos Hsp.
  set (r := n * (k - 1) + 1).
  assert (HFne : Forall (fun A : list nat => A <> []) F).
  { apply Forall_forall; intros A HA.
    unfold Uniform in HU; rewrite Forall_forall in HU.
    destruct (HU A HA) as [HAlen _].
    destruct A; [simpl in HAlen; lia | discriminate]. }
  destruct (max_disjoint_cover HFne) as [Scov [Hincl [Hnd [Hpd Hcov]]]].
  destruct (le_lt_dec k (length Scov)) as [Hkge | Hklt].
  - (* Enough pairwise disjoint sets already: take the first k. *)
    exists (firstn k Scov); repeat split.
    + intros B HB; apply Hincl, (incl_firstn k Scov); exact HB.
    + apply NoDup_firstn; exact Hnd.
    + apply firstn_length_le; lia.
    + intros B C HB HC HBC.
      apply Hpd; try (apply (incl_firstn k Scov); assumption); exact HBC.
  - (* Fewer than k: the union of the cover is too small for a spread
       family, a contradiction. *)
    exfalso.
    set (X := concat Scov).
    assert (HXcov : forall A, In A F -> exists x, In x A /\ In x X).
    { intros A HA. apply (cover_provides_element F Scov A); auto. }
    assert (HXlen : length X <= length Scov * m).
    { unfold X. apply concat_uniform_length.
      apply Forall_forall; intros B HB.
      apply Hincl in HB. unfold Uniform in HU.
      rewrite Forall_forall in HU; apply HU; exact HB. }
    assert (HXlt : length X < r).
    { unfold r. assert (Hs : length Scov <= k - 1) by lia. nia. }
    assert (HXpos : 1 <= length X).
    { destruct (Nat.eq_dec (length X) 0) as [E0 | Hne0]; [|lia].
      exfalso. apply length_zero_iff_nil in E0.
      destruct F as [|A F']; [simpl in HFpos; lia|].
      destruct (HXcov A (or_introl eq_refl)) as [x [_ Hx]].
      rewrite E0 in Hx; inversion Hx. }
    assert (Hb : length X <> 0) by lia.
    set (K := (length F - 1) / length X).
    assert (HpigSize : length F > length X * K).
    { pose proof (Nat.mul_div_le (length F - 1) (length X) Hb) as Hd.
      unfold K; lia. }
    destruct (pigeonhole_family F X K HXcov HpigSize) as [x [HxX Hcount]].
    assert (Hdegx : deg [x] F > K) by (rewrite deg_single; exact Hcount).
    assert (Hmod : length X * (K + 1) > length F - 1).
    { pose proof (Nat.div_mod_eq (length F - 1) (length X)) as Hdm.
      pose proof (Nat.mod_upper_bound (length F - 1) (length X) Hb) as Hub.
      unfold K; lia. }
    assert (Hge : length X * deg [x] F >= length F).
    { assert (Hd1 : deg [x] F >= K + 1) by lia. nia. }
    assert (Hnd1 : NoDup [x]) by (constructor; [simpl; tauto | constructor]).
    specialize (Hsp [x] Hnd1).
    simpl in Hsp.
    assert (Hd1 : 1 <= deg [x] F) by lia.
    nia.
Qed.

(** ** An unconditional bound, proved through the spread framework

    [f(n,k) ≤ (n(k-1)+1)^n + 1], with no axioms.

    This is comparable to — and slightly weaker than — the 1960
    Erdős–Rado bound [(k-1)^n·n! + 1 ≈ (nk/e)^n], but it is obtained by
    a completely different route: the spread dichotomy of the 2020
    proof, with its hard analytic input replaced by the trivial
    estimate. It also certifies that [spread_reduction] is not
    vacuous. *)

Theorem spread_erdos_rado :
  forall n k, 2 <= k -> UpperBound n k (S ((n * (k - 1) + 1) ^ n)).
Proof.
  intros n k Hk.
  apply (@spread_reduction_top n k (n * (k - 1) + 1)); [exact Hk | nia |].
  apply elementary_spread_disjoint; exact Hk.
Qed.
