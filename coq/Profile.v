(** * Profile.v -- the reduction does not care that the profile is a power,
      and the greedy cover step cannot beat Erdős–Rado.

    [SpreadReduction.spread_reduction] takes a family that is Rao-spread
    with parameter [r] — [deg T F ≤ r^(m-|T|)] — and returns
    [f(m,k) ≤ r^m + 1]. Its induction never uses that [r^·] is a power.
    Replace [r^j] by an arbitrary [B : nat -> nat] and every step goes
    through verbatim: when [T] violates the condition the link has
    uniformity [j = m - |T|] and more than [B j] members, and its own
    degrees are [deg S (link T F) = deg (S ++ T) F ≤ B (m - |S| - |T|)
    = B (j - |S|)]. The recursion is *profile-preserving*, and what the
    reduction actually proves is

    >  ProfileYieldsDisjoint n k B  ->  f(m,k) ≤ B m + 1   for every m ≤ n.

    This file states that, and then uses it for one thing.

    ** Why this is worth a module

    Two of this development's bounds are the same theorem at two
    profiles.

    - [B j = r^j] is Rao's condition, and the reduction gives [r^m].
    - [B j = (k-1)^j · j!] is *Erdős–Rado 1960*, and the reduction gives
      [(k-1)^m · m! + 1] — the 1960 bound, re-derived here through the
      spread reduction rather than through [ErdosRado.v]'s own induction
      ([erdos_rado_via_profile] below).

    That is not a coincidence, and the reason is the point of the file.
    The *greedy cover step* — no [k] pairwise disjoint members, so a
    maximal matching has at most [k-1] of them, so the family is covered
    by [(k-1)m] points, so [|F| ≤ (k-1)·m·B(m-1)] — closes the reduction
    at a profile [B] exactly when

    >  (k-1) · m · B(m-1)  ≤  B m        for every m ≤ n.

    Unrolling that recurrence from [B 0 = 1] gives [B m ≥ (k-1)^m · m!].
    So:

    > **[greedy_forces_erdos_rado]: every profile that the greedy cover
    > step closes is at least Erdős–Rado's. The greedy step cannot beat
    > 1960, at any [k], by any amount.**

    This is exact, not asymptotic: no Stirling, no [e], no range check.
    It is the formal content of the sentence that the [m!] in Erdős–Rado
    *is* the factor [m] paid once per level by covering with one member's
    points.

    ** What it says about this development's routes

    [SpreadThreshold.cover_spread_disjoint] ([r*(n,3) ≤ 2n]) is exactly
    the greedy step at the profile [r^j]: [(k-1)·m·r^(m-1) ≤ r^m] iff
    [r ≥ (k-1)m]. It generalises to every [k] for free
    ([cover_spread_disjoint_general]) — and by the theorem above it can
    never do better than 1960.

    [SpreadThreshold.quadratic_spread_disjoint] ([r*(n,3) ≤ 1.74n]) beats
    [2n] precisely because it is *not* greedy-only: it pays [r^(m-2)] for
    a pair where the greedy step pays [r^(m-1)] for a point.

    That leaves the question of what a *linear* profile costs at all, and
    [erdos_rado_below_the_n_to_the_n_ceiling] answers it exactly:
    [2^n·n! ≤ (n+1)^n] at every [n]. So the ceiling
    [(n+1)^n] that [HiltonMilner.star_extremal_route_needs_r_above_n]
    pins the star-extremality route to is worse than Erdős–Rado at every
    [n] — which `docs/roadmap.md` §28.4 established by checking [n ≤ 200]
    in exact arithmetic, and which is now a theorem with no range on it.
*)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat Wf_nat.
From Sunflower Require Import Sets Sunflower Spread SpreadReduction
     ErdosRado ErdosRado_Greedy SpreadThreshold.
Import ListNotations.

Set Implicit Arguments.

(** ** The profile condition

    [ProfileSpread B m F] is [Spread.RaoSpread] with [r^(m-|T|)] replaced
    by [B (m-|T|)]. Nothing is assumed about [B]. *)

Definition ProfileSpread (B : nat -> nat) (m : nat) (F : Family) : Prop :=
  forall T : list nat,
    NoDup T -> T <> [] -> deg T F <= B (m - length T).

(** Rao's condition is the power profile, definitionally. *)

Lemma RaoSpread_ProfileSpread : forall m F r,
    RaoSpread m F r <-> ProfileSpread (fun j => r ^ j) m F.
Proof. intros m F r; split; intros H T H1 H2; exact (H T H1 H2). Qed.

(** A profile that dominates another inherits its condition. *)

Lemma ProfileSpread_mono : forall (B B' : nat -> nat) m F,
    ProfileSpread B m F -> (forall j, B j <= B' j) -> ProfileSpread B' m F.
Proof.
  intros B B' m F HP Hle T HT Hne.
  eapply Nat.le_trans; [apply HP; assumption | apply Hle].
Qed.

(** ** The decision procedure, at an arbitrary profile

    Verbatim [Spread.rao_witness] with the profile abstracted. As there,
    the search is over [Spread.cands F] — the sublists of members — which
    is a finite list, so no excluded middle is imported. *)

Definition profile_violatesb (B : nat -> nat) (m : nat) (F : Family)
                             (T : list nat) : bool :=
  match T with
  | [] => false
  | _ :: _ => Nat.ltb (B (m - length T)) (deg T F)
  end.

Definition profile_witness (B : nat -> nat) (m : nat) (F : Family)
  : option (list nat) :=
  find (profile_violatesb B m F) (cands F).

Lemma profile_violatesb_false_inv : forall B m F T,
    T <> [] -> profile_violatesb B m F T = false -> deg T F <= B (m - length T).
Proof.
  intros B m F T Hne H; destruct T as [|t T0]; [contradiction|].
  unfold profile_violatesb in H; apply Nat.ltb_ge in H; exact H.
Qed.

Lemma profile_witness_some :
  forall B m F T, profile_witness B m F = Some T ->
    In T (cands F) /\ T <> [] /\ B (m - length T) < deg T F.
Proof.
  intros B m F T H; unfold profile_witness in H.
  apply find_some in H as [Hin Hv].
  destruct T as [|t T0]; [discriminate|].
  unfold profile_violatesb in Hv; apply Nat.ltb_lt in Hv.
  repeat split; [exact Hin | discriminate | exact Hv].
Qed.

Lemma profile_witness_none :
  forall B m F,
    Forall (fun A : list nat => NoDup A) F ->
    profile_witness B m F = None ->
    ProfileSpread B m F.
Proof.
  intros B m F Hnd Hnone T HT Hne.
  unfold profile_witness in Hnone.
  destruct (deg T F) as [|d] eqn:Hdeg; [lia|].
  destruct (@deg_pos_inv T F ltac:(lia)) as [A [HAF HTA]].
  assert (HAnd : NoDup A) by (rewrite Forall_forall in Hnd; apply Hnd, HAF).
  set (T' := filter (fun x => memb x T) A).
  assert (HTT' : Subset T T').
  { intros x Hx; unfold T'; apply filter_In; split;
      [apply HTA, Hx | apply memb_true_iff; exact Hx]. }
  assert (HT'T : Subset T' T).
  { intros x Hx; unfold T' in Hx; apply filter_In in Hx as [_ Hm].
    apply memb_true_iff; exact Hm. }
  assert (HT'nd : NoDup T') by (unfold T'; apply NoDup_filter; exact HAnd).
  assert (Hlen : length T' = length T).
  { assert (H1 : length T <= length T') by (apply NoDup_incl_length; assumption).
    assert (H2 : length T' <= length T) by (apply NoDup_incl_length; assumption).
    lia. }
  assert (Hdegeq : deg T' F = deg T F) by (apply deg_setEq; assumption).
  assert (HT'ne : T' <> []).
  { destruct T as [|t T0]; [contradiction|].
    intro E. assert (Hin : In t T') by (apply HTT'; left; reflexivity).
    rewrite E in Hin; inversion Hin. }
  assert (HT'cand : In T' (cands F))
    by (unfold T'; apply in_cands_filter; exact HAF).
  pose proof (find_none _ _ Hnone T' HT'cand) as Hv.
  pose proof (@profile_violatesb_false_inv B m F T' HT'ne Hv) as Hle.
  rewrite Hlen, Hdegeq, Hdeg in Hle.
  exact Hle.
Qed.

(** ** The reduction at an arbitrary profile

    [SpreadReduction.SpreadYieldsDisjoint] with [r^m] replaced by [B m].
    Note the induction below never needs to *propagate* the profile
    condition into the link: as in [spread_reduction], spreadness is
    re-decided at every level by [profile_witness]. That is what makes
    the generalisation free. *)

Definition ProfileYieldsDisjoint (n k : nat) (B : nat -> nat) : Prop :=
  forall (m : nat) (F : Family),
    1 <= m -> m <= n ->
    Uniform m F -> Distinct F ->
    B m < length F ->
    ProfileSpread B m F ->
    exists S : list (list nat),
      incl S F /\ NoDup S /\ length S = k /\ PairwiseDisjoint S.

Lemma ProfileYieldsDisjoint_pow : forall n k r,
    ProfileYieldsDisjoint n k (fun j => r ^ j) <-> SpreadYieldsDisjoint n k r.
Proof.
  intros n k r; split.
  - intros H m F H1 H2 H3 H4 H5 H6.
    apply (H m F H1 H2 H3 H4 H5).
    apply RaoSpread_ProfileSpread; exact H6.
  - intros H m F H1 H2 H3 H4 H5 H6.
    apply (H m F H1 H2 H3 H4 H5).
    apply RaoSpread_ProfileSpread; exact H6.
Qed.

Theorem profile_reduction :
  forall n k (B : nat -> nat),
    2 <= k -> 1 <= B 0 ->
    ProfileYieldsDisjoint n k B ->
    forall m, m <= n -> UpperBound m k (S (B m)).
Proof.
  intros n k B Hk HB0 Hpyd m.
  induction m as [m IH] using lt_wf_ind.
  intros Hmn F HU HD Hsize.
  destruct m as [|m'].
  - (* 0-uniform: [B 0 ≥ 1] forces two members, but a distinct 0-uniform
       family has at most one. *)
    exfalso.
    assert (H2 : 2 <= length F) by lia.
    destruct F as [|A [|C F'']]; simpl in H2; try lia.
    unfold Uniform in HU.
    inversion HU as [|? ? HUA HU']; subst.
    inversion HU' as [|? ? HUC HU'']; subst.
    destruct HUA as [HAlen _]; destruct HUC as [HClen _].
    destruct A as [|a A0]; [|simpl in HAlen; lia].
    destruct C as [|c C0]; [|simpl in HClen; lia].
    inversion HD as [|? ? Hni _]; subst.
    apply (Hni [] (or_introl eq_refl)); apply SetEq_refl.
  - destruct (profile_witness B (S m') F) as [T|] eqn:Ewit.
    + (* Some sublist of a member is over-represented: recurse into the
         link, whose uniformity is [S m' - |T|] and whose size exceeds
         [B (S m' - |T|)] by the violation. *)
      apply profile_witness_some in Ewit as [Hcand [Hne Hviol]].
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
      { destruct T as [|t T0]; [contradiction | simpl; lia]. }
      apply (@link_sunflower_lift T F k).
      assert (Hlt : S m' - length T < S m') by lia.
      assert (Hle : S m' - length T <= n) by lia.
      apply (IH (S m' - length T) Hlt Hle).
      * apply link_uniform; assumption.
      * apply link_distinct; exact HD.
      * rewrite length_link; lia.
    + (* No violation: the profile condition holds, so the oracle fires. *)
      assert (HFnd : Forall (fun A : list nat => NoDup A) F).
      { unfold Uniform in HU. apply Forall_forall; intros A HA.
        rewrite Forall_forall in HU; destruct (HU A HA) as [_ Hnd]; exact Hnd. }
      assert (Hsp : ProfileSpread B (S m') F)
        by (apply (@profile_witness_none B (S m') F HFnd Ewit)).
      assert (Hbig : B (S m') < length F) by lia.
      destruct (Hpyd (S m') F (le_n_S _ _ (Nat.le_0_l _)) Hmn HU HD Hbig Hsp)
        as [S0 [Hincl [Hnd0 [Hlen0 Hpd0]]]].
      exists S0; split.
      * apply SubFamilySetEq_incl; exact Hincl.
      * apply k_pairwise_disjoint_sunflower; assumption.
Qed.

(** [spread_reduction] is the instance at [B j = r^j]. *)

Corollary spread_reduction_is_a_profile_instance :
  forall n k r,
    2 <= k -> 1 <= r ->
    SpreadYieldsDisjoint n k r ->
    forall m, m <= n -> UpperBound m k (S (r ^ m)).
Proof.
  intros n k r Hk Hr Hsyd.
  apply (@profile_reduction n k (fun j => r ^ j) Hk).
  - simpl; lia.
  - apply ProfileYieldsDisjoint_pow; exact Hsyd.
Qed.

(** ** The greedy cover step, at an arbitrary profile

    "No [k] pairwise disjoint members" bounds a maximal matching by
    [k-1]; its union is at most [(k-1)m] points; every member meets it;
    each point has degree at most [B (m-1)]. *)

Lemma matching_at_most_k_minus_one :
  forall (k : nat) (F : Family) (S : list (list nat)),
    NoKDisjoint k F -> incl S F -> NoDup S -> PairwiseDisjoint S ->
    length S <= k - 1.
Proof.
  intros k F S Hno Hincl Hnd Hpd.
  destruct (le_lt_dec (length S) (k - 1)) as [Hle|Hgt]; [exact Hle|exfalso].
  apply Hno.
  exists (firstn k S); repeat split.
  - intros X HX; apply Hincl; eapply incl_firstn; exact HX.
  - apply NoDup_firstn; exact Hnd.
  - rewrite firstn_length; lia.
  - intros X Y HX HY HXY; apply Hpd;
      [eapply incl_firstn; exact HX | eapply incl_firstn; exact HY | exact HXY].
Qed.

Theorem greedy_profile_bound :
  forall k m (B : nat -> nat) (F : Family),
    1 <= m ->
    Uniform m F -> ProfileSpread B m F -> NoKDisjoint k F ->
    length F <= (k - 1) * m * B (m - 1).
Proof.
  intros k m B F Hm HU HP Hno.
  destruct (max_disjoint_cover (uniform_nonempty Hm HU))
    as [S [Hincl [Hnd [Hpd Hcov]]]].
  assert (Hlek : length S <= k - 1)
    by (eapply matching_at_most_k_minus_one; eassumption).
  assert (HSu : Forall (UniformSet m) S).
  { apply Forall_forall; intros A HA.
    unfold Uniform in HU; rewrite Forall_forall in HU; apply HU, Hincl, HA. }
  assert (Hpts : length (concat S) <= (k - 1) * m).
  { eapply Nat.le_trans; [apply (ErdosRado.concat_uniform_length HSu)|].
    apply Nat.mul_le_mono_r; exact Hlek. }
  assert (Hdegpt : forall x, deg [x] F <= B (m - 1)).
  { intros x; apply (HP [x]); [constructor; [intros []|constructor] | discriminate]. }
  assert (Hbound : length F <= length (concat S) * B (m - 1)).
  { apply cover_by_points.
    - intros A HA.
      destruct (@cover_provides_element F S A Hcov HA) as [x [HxA Hxc]].
      exists x; split; assumption.
    - intros x _; apply Hdegpt. }
  assert (Hmul : length (concat S) * B (m - 1) <= (k - 1) * m * B (m - 1))
    by (apply Nat.mul_le_mono_r; exact Hpts).
  lia.
Qed.

(** A profile is *greedy-closed* up to [n] when the greedy bound above
    already lands inside it. This is the exact hypothesis under which the
    cover step alone discharges [ProfileYieldsDisjoint]. *)

Definition GreedyClosed (n k : nat) (B : nat -> nat) : Prop :=
  forall m, 1 <= m -> m <= n -> (k - 1) * m * B (m - 1) <= B m.

(** The same argument run forwards rather than by contradiction, so that
    no decidability of [NoKDisjoint] is needed: [max_disjoint_cover]
    either already hands back [k] pairwise disjoint members, or a cover
    small enough to contradict the size hypothesis. *)

Theorem greedy_closes_profile :
  forall n k (B : nat -> nat),
    2 <= k -> GreedyClosed n k B -> ProfileYieldsDisjoint n k B.
Proof.
  intros n k B Hk Hgc m F Hm Hmn HU HD Hsize HP.
  destruct (max_disjoint_cover (uniform_nonempty Hm HU))
    as [S [Hincl [Hnd [Hpd Hcov]]]].
  destruct (le_lt_dec k (length S)) as [Hge | Hlt].
  - exists (firstn k S); repeat split.
    + intros X HX; apply Hincl; eapply incl_firstn; exact HX.
    + apply NoDup_firstn; exact Hnd.
    + rewrite firstn_length; lia.
    + intros X Y HX HY HXY; apply Hpd;
        [eapply incl_firstn; exact HX | eapply incl_firstn; exact HY | exact HXY].
  - exfalso.
    assert (HSu : Forall (UniformSet m) S).
    { apply Forall_forall; intros A HA.
      unfold Uniform in HU; rewrite Forall_forall in HU; apply HU, Hincl, HA. }
    assert (Hpts : length (concat S) <= (k - 1) * m).
    { eapply Nat.le_trans; [apply (ErdosRado.concat_uniform_length HSu)|].
      apply Nat.mul_le_mono_r; lia. }
    assert (Hbound : length F <= length (concat S) * B (m - 1)).
    { apply cover_by_points.
      - intros A HA.
        destruct (@cover_provides_element F S A Hcov HA) as [x [HxA Hxc]].
        exists x; split; assumption.
      - intros x _; apply (HP [x]);
          [constructor; [intros []|constructor] | discriminate]. }
    assert (Hmul : length (concat S) * B (m - 1) <= (k - 1) * m * B (m - 1))
      by (apply Nat.mul_le_mono_r; exact Hpts).
    pose proof (Hgc m Hm Hmn) as Hgm.
    lia.
Qed.

(** ** The barrier: greedy-closed means at least Erdős–Rado

    Unrolling [GreedyClosed] from [B 0 = 1]. No asymptotics appear: the
    conclusion is the 1960 constant itself. *)

Theorem greedy_forces_erdos_rado :
  forall n k (B : nat -> nat),
    1 <= B 0 -> GreedyClosed n k B ->
    forall m, m <= n -> (k - 1) ^ m * fact m <= B m.
Proof.
  intros n k B HB0 Hgc m.
  induction m as [|m IH]; intros Hmn.
  - simpl; lia.
  - assert (Hm : m <= n) by lia.
    specialize (IH Hm).
    pose proof (Hgc (S m) ltac:(lia) Hmn) as Hstep.
    replace (S m - 1) with m in Hstep by lia.
    assert (Hexp : (k - 1) ^ S m * fact (S m)
                   = (k - 1) * S m * ((k - 1) ^ m * fact m)).
    { simpl fact; simpl Nat.pow; ring. }
    rewrite Hexp.
    eapply Nat.le_trans; [| exact Hstep].
    apply Nat.mul_le_mono_l; exact IH.
Qed.

(** The headline, in the shape a later session will want to quote: the
    bound that the greedy step yields through [profile_reduction] is
    never smaller than [ErdosRado_Greedy.er_upper_bound]. *)

Corollary greedy_cannot_beat_erdos_rado :
  forall n k (B : nat -> nat),
    1 <= B 0 -> GreedyClosed n k B ->
    forall m, m <= n -> er_upper_bound m k <= S (B m).
Proof.
  intros n k B HB0 Hgc m Hmn.
  unfold er_upper_bound.
  apply le_n_S.
  apply (@greedy_forces_erdos_rado n k B HB0 Hgc m Hmn).
Qed.

(** ** Instance 1: Erdős–Rado's own profile, and the 1960 bound re-derived

    [(k-1)^j · j!] is greedy-closed with equality at every level — that
    is what makes it the least greedy-closed profile — so
    [profile_reduction] returns the 1960 bound. This is a second,
    independent derivation of [ErdosRado.erdos_rado_upper_bound] inside
    this development: that file inducts on the uniformity directly, this
    one goes through the spread reduction. *)

Definition er_profile (k : nat) (j : nat) : nat := (k - 1) ^ j * fact j.

Lemma er_profile_greedy_closed : forall n k, GreedyClosed n k (er_profile k).
Proof.
  intros n k m Hm _; unfold er_profile.
  destruct m as [|m']; [lia|].
  replace (S m' - 1) with m' by lia.
  assert (Hexp : (k - 1) ^ S m' * fact (S m')
                 = (k - 1) * S m' * ((k - 1) ^ m' * fact m')).
  { simpl fact; simpl Nat.pow; ring. }
  lia.
Qed.

Theorem erdos_rado_via_profile :
  forall n k, 2 <= k -> UpperBound n k (S ((k - 1) ^ n * fact n)).
Proof.
  intros n k Hk.
  apply (@profile_reduction n k (er_profile k) Hk).
  - unfold er_profile; simpl; lia.
  - apply greedy_closes_profile; [exact Hk | apply er_profile_greedy_closed].
  - reflexivity.
Qed.

(** ** Instance 2: the power profile, i.e. the cover bound at every [k]

    [SpreadThreshold.cover_spread_disjoint] is [k = 3] of this. The
    greedy step closes [r^j] exactly when [r ≥ (k-1)m], so [r = (k-1)n]
    works throughout. *)

Lemma pow_profile_greedy_closed :
  forall n k, GreedyClosed n k (fun j => ((k - 1) * n) ^ j).
Proof.
  intros n k m Hm Hmn.
  destruct m as [|m']; [lia|].
  replace (S m' - 1) with m' by lia.
  assert (Hexp : ((k - 1) * n) ^ S m' = (k - 1) * n * ((k - 1) * n) ^ m')
    by reflexivity.
  rewrite Hexp.
  apply Nat.mul_le_mono_r.
  apply Nat.mul_le_mono_l; lia.
Qed.

Theorem cover_spread_disjoint_general :
  forall n k, 2 <= k -> SpreadYieldsDisjoint n k ((k - 1) * n).
Proof.
  intros n k Hk.
  apply ProfileYieldsDisjoint_pow.
  apply greedy_closes_profile; [exact Hk | apply pow_profile_greedy_closed].
Qed.

(** And the barrier applied to it: the cover bound's output
    [((k-1)n)^n] is never better than 1960's. *)

Corollary cover_bound_cannot_beat_erdos_rado :
  forall n k, (k - 1) ^ n * fact n <= ((k - 1) * n) ^ n.
Proof.
  intros n k.
  apply (@greedy_forces_erdos_rado n k (fun j => ((k - 1) * n) ^ j));
    [simpl; lia | apply pow_profile_greedy_closed | lia].
Qed.

(** ** The linear ceiling, exactly

    The greedy barrier above is exact and needs no arithmetic. The other
    two routes this development has costed —
    [HiltonMilner.star_extremal_route_needs_r_above_n]'s [(n+1)^n] and
    `docs/roadmap.md` §21.5's [b^b] — are *not* greedy-only, so they need
    the comparison done directly. §28.4 did it by evaluating both sides
    for [n ≤ 200]. It is a theorem, and the whole proof is one Bernoulli
    inequality in [nat]. *)

(** Bernoulli, in the multiplicative form [nat] wants:
    [n^k·(n+k) ≤ n·(n+1)^k]. Induction on [k]; the step needs only
    [0 ≤ k]. Taking [k = n] gives [2·n^n ≤ (n+1)^n]. *)

Lemma pow_bernoulli : forall k n, n ^ k * (n + k) <= n * (n + 1) ^ k.
Proof.
  induction k as [|k IH]; intros n.
  - simpl; lia.
  - assert (Hstep : n ^ S k * (n + S k) <= n ^ k * (n + k) * (n + 1)).
    { simpl Nat.pow.
      assert (E : n * n ^ k * (n + S k) = n ^ k * (n * (n + k + 1))) by ring.
      rewrite E.
      assert (E2 : n ^ k * (n + k) * (n + 1) = n ^ k * ((n + k) * (n + 1)))
        by ring.
      rewrite E2.
      apply Nat.mul_le_mono_l; nia. }
    eapply Nat.le_trans; [exact Hstep|].
    assert (E3 : n * (n + 1) ^ S k = n * (n + 1) ^ k * (n + 1))
      by (simpl Nat.pow; ring).
    rewrite E3.
    apply Nat.mul_le_mono_r; apply IH.
Qed.

Lemma two_pow_le_succ_pow : forall n, 1 <= n -> 2 * n ^ n <= (n + 1) ^ n.
Proof.
  intros n Hn.
  pose proof (pow_bernoulli n n) as H.
  assert (E : n ^ n * (n + n) = n * (2 * n ^ n)) by ring.
  rewrite E in H.
  apply (proj2 (Nat.mul_le_mono_pos_l (2 * n ^ n) ((n + 1) ^ n) n ltac:(lia))).
  exact H.
Qed.

(** **[2^n·n! ≤ (n+1)^n] at every [n]**: Erdős–Rado's bound at [k = 3]
    never exceeds the [(n+1)^n] ceiling that the star-extremality route
    is pinned to. So that route cannot produce a record, at any [n], and
    §28.4's check to [n = 200] is subsumed. *)

Theorem erdos_rado_below_the_n_to_the_n_ceiling :
  forall n, 2 ^ n * fact n <= (n + 1) ^ n.
Proof.
  induction n as [|n IH].
  - simpl; lia.
  - assert (Ef : fact (S n) = S n * fact n) by reflexivity.
    assert (Ep : 2 ^ S n = 2 * 2 ^ n) by reflexivity.
    assert (E1 : 2 ^ S n * fact (S n) = 2 * S n * (2 ^ n * fact n))
      by (rewrite Ef, Ep; ring).
    rewrite E1.
    assert (H1 : 2 * S n * (2 ^ n * fact n) <= 2 * S n * (n + 1) ^ n)
      by (apply Nat.mul_le_mono_l; exact IH).
    eapply Nat.le_trans; [exact H1|].
    (* [2·(n+1)^(n+1) ≤ (n+2)^(n+1)] is [two_pow_le_succ_pow] at [S n] *)
    assert (HSn : 1 <= S n) by lia.
    pose proof (@two_pow_le_succ_pow (S n) HSn) as Hb.
    assert (E2 : S n ^ S n = S n * (n + 1) ^ n).
    { assert (Eu : S n ^ S n = S n * S n ^ n) by reflexivity.
      rewrite Eu; f_equal; f_equal; lia. }
    rewrite E2 in Hb.
    lia.
Qed.

(** The same comparison in the form §28.4 states it: the star-extremality
    route's ceiling [(n+1)^n + 1] is at least the Erdős–Rado bound
    [2^n·n! + 1], at every [n], with no range check. *)

Corollary star_extremal_ceiling_is_worse_than_erdos_rado :
  forall n, er_upper_bound n 3 <= S ((n + 1) ^ n).
Proof.
  intros n; unfold er_upper_bound.
  apply le_n_S.
  replace (3 - 1) with 2 by reflexivity.
  apply erdos_rado_below_the_n_to_the_n_ceiling.
Qed.
