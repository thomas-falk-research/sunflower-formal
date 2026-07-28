(** * Audit.v -- Coherence and non-vacuity checks on the definitions.

    Nothing here is needed to prove any bound. Everything here exists
    to catch the failure mode this development has actually suffered
    from twice: a *statement* error rather than a proof error.

    The kernel cannot help with those. A degenerate definition — the
    old [Spread.w_spread_legacy], which forced every member of a
    "spread" family to be empty — typechecks perfectly, and so does a
    hypothesis that quietly says something stronger or weaker than the
    paper it cites. What catches them is asking the definitions
    questions whose answers are known in advance, and checking that
    the machine agrees.

    The questions asked here:

    - Are [UpperBound] and [LowerBound] really complementary? If they
      could both hold at the same [m], one of them means something
      other than what its name says. ([lower_bound_excludes_upper],
      [lower_lt_upper].)
    - Is [ContainsKSunflower] a property of the *family of sets*, or of
      the list-of-lists encoding? ([ContainsKSunflower_equiv],
      [ContainsKSunflower_perm].)
    - Is the [core] of a sunflower determined by its petals, or could a
      family be a sunflower with two genuinely different cores?
      ([sunflower_core_unique].)
    - Is [Distinct] doing any work beyond [NoDup]?
      ([distinct_strictly_stronger].)
    - Is [SpreadYieldsDisjoint] — the shape of the one axiom — ever
      *false*? An axiom whose conclusion held for every parameter would
      be assuming nothing, and its threshold hypothesis would be
      decoration. ([spread_yields_disjoint_sandwich],
      [no_spread_yields_disjoint_2_3_2].)
    - Do the development's own bounds fit in one consistent order?
      Each inequality in the last section is *derived* from the two
      formal statements it names; a contradictory pair would make the
      corresponding line a proof of [False].
      ([bounds_coherent_er], [bounds_coherent_spread],
      [bounds_coherent_f_2_3].) *)

From Coq Require Import List Arith Lia Bool Permutation.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower Pigeonhole ErdosRado LowerBound
     ProductLowerBound Spread Reflect SpreadReduction TwoUniform F23.
Import ListNotations.

Set Implicit Arguments.

(** ** The two bound predicates are complementary

    [UpperBound n k m] says every uniform distinct family of size at
    least [m] contains a [k]-sunflower; [LowerBound n k m] exhibits one
    of size exactly [m] that does not. They must not both hold. The
    development previously proved this only for one concrete pair
    ([LowerBound.f_n_k_ge_k]); here it is a property of the
    definitions. *)

Theorem lower_bound_excludes_upper :
  forall n k m, LowerBound n k m -> ~ UpperBound n k m.
Proof.
  intros n k m [F [HU [HD [Hlen Hns]]]] Hub.
  apply Hns, Hub; [exact HU | exact HD | lia].
Qed.

Corollary upper_bound_excludes_lower :
  forall n k m, UpperBound n k m -> ~ LowerBound n k m.
Proof. intros n k m Hub Hlb; exact (lower_bound_excludes_upper Hlb Hub). Qed.

(** The sharper form: every lower bound lies strictly below every upper
    bound, so the two really do sandwich a well-defined [f(n,k)]. *)

Theorem lower_lt_upper :
  forall n k a b, LowerBound n k a -> UpperBound n k b -> a < b.
Proof.
  intros n k a b [F [HU [HD [Hlen Hns]]]] Hub.
  destruct (le_lt_dec b a) as [Hle | Hlt]; [exfalso | exact Hlt].
  apply Hns, Hub; [exact HU | exact HD | lia].
Qed.

(** ** [ContainsKSunflower] is a property of the underlying sets

    Families are encoded as lists of lists, so the same mathematical
    family has many encodings: the members can be permuted, and the
    elements inside each member can be permuted. A sunflower predicate
    that could tell those apart would be the wrong predicate. *)

Lemma SubFamilySetEq_trans :
  forall S F G,
    SubFamilySetEq S F -> SubFamilySetEq F G -> SubFamilySetEq S G.
Proof.
  intros S F G HSF HFG A HA.
  destruct (HSF A HA) as [B [HB Hab]].
  destruct (HFG B HB) as [C [HC Hbc]].
  exists C; split; [exact HC | apply (@SetEq_trans A B C Hab Hbc)].
Qed.

Theorem ContainsKSunflower_mono :
  forall k F G,
    SubFamilySetEq F G -> ContainsKSunflower k F -> ContainsKSunflower k G.
Proof.
  intros k F G Hfg [S [Hsub Hks]].
  exists S; split; [apply (SubFamilySetEq_trans Hsub Hfg) | exact Hks].
Qed.

Corollary ContainsKSunflower_incl :
  forall k F G, incl F G -> ContainsKSunflower k F -> ContainsKSunflower k G.
Proof.
  intros k F G Hincl; apply ContainsKSunflower_mono.
  apply SubFamilySetEq_incl; exact Hincl.
Qed.

(** Two families are equivalent when each member of one is set-equal to
    a member of the other. This is exactly "the same family of sets". *)

Definition FamilyEquiv (F G : Family) : Prop :=
  SubFamilySetEq F G /\ SubFamilySetEq G F.

Theorem ContainsKSunflower_equiv :
  forall k F G,
    FamilyEquiv F G -> (ContainsKSunflower k F <-> ContainsKSunflower k G).
Proof.
  intros k F G [Hfg Hgf]; split;
    [apply ContainsKSunflower_mono; exact Hfg
    | apply ContainsKSunflower_mono; exact Hgf].
Qed.

Lemma Permutation_FamilyEquiv :
  forall F G : Family, Permutation F G -> FamilyEquiv F G.
Proof.
  intros F G Hp; split; intros A HA; exists A; split;
    [ apply (Permutation_in _ Hp); exact HA | apply SetEq_refl
    | apply (Permutation_in _ (Permutation_sym Hp)); exact HA
    | apply SetEq_refl ].
Qed.

Corollary ContainsKSunflower_perm :
  forall k (F G : Family),
    Permutation F G -> (ContainsKSunflower k F <-> ContainsKSunflower k G).
Proof.
  intros k F G Hp; apply ContainsKSunflower_equiv, Permutation_FamilyEquiv, Hp.
Qed.

(** Permuting the elements *inside* the members changes nothing either:
    each member is set-equal to its permutation. *)

Corollary ContainsKSunflower_member_perm :
  forall k (F G : Family),
    length F = length G ->
    (forall A, In A F -> exists B, In B G /\ SetEq A B) ->
    (forall B, In B G -> exists A, In A F /\ SetEq B A) ->
    (ContainsKSunflower k F <-> ContainsKSunflower k G).
Proof.
  intros k F G _ H1 H2; apply ContainsKSunflower_equiv; split; assumption.
Qed.

(** ** Monotonicity of the two bound predicates

    [UpperBound] rises ([Sunflower.UpperBound_mono]); [LowerBound]
    falls. The latter needs that a subfamily of a sunflower-free family
    is sunflower-free, which is [ContainsKSunflower_incl]
    contraposed. *)

Theorem LowerBound_antitone :
  forall n k m m', LowerBound n k m -> m' <= m -> LowerBound n k m'.
Proof.
  intros n k m m' [F [HU [HD [Hlen Hns]]]] Hle.
  exists (firstn m' F); repeat split.
  - apply (@Uniform_sublist n F (firstn m' F) HU (incl_firstn m' F)).
  - apply (@SetNoDup_incl (firstn m' F) F HD (NoDup_firstn m' (SetNoDup_NoDup HD))
             (incl_firstn m' F)).
  - apply firstn_length_le; lia.
  - intro Hc; apply Hns.
    apply (@ContainsKSunflower_incl k (firstn m' F) F (incl_firstn m' F) Hc).
Qed.

(** [LowerBound] pins the family size with an equality. The variant
    that only asks for *at least* [m] members defines the same
    predicate — antitonicity is exactly what makes the two agree. The
    mutation [lowerbound-at-least] in [tools/mutations.toml] weakens
    the definition this way and the build breaks; this theorem is why
    that break is a property of four tactic scripts and not of the
    mathematics. *)

Definition LowerBoundGE (n k m : nat) : Prop :=
  exists F : Family,
    Uniform n F /\ Distinct F /\ length F >= m /\ ~ ContainsKSunflower k F.

Theorem LowerBound_ge_equiv :
  forall n k m, LowerBoundGE n k m <-> LowerBound n k m.
Proof.
  intros n k m; split.
  - intros [F [HU [HD [Hlen Hns]]]].
    apply (@LowerBound_antitone n k (length F) m); [| exact Hlen].
    exists F; split; [exact HU | split; [exact HD | split; [lia | exact Hns]]].
  - intros [F [HU [HD [Hlen Hns]]]].
    exists F; split; [exact HU | split; [exact HD | split; [lia | exact Hns]]].
Qed.

(** Consequently [UpperBound] is *false* everywhere below the
    exponential lower bound — for every [n] and [k] at once. Before
    this, the only [~ UpperBound] facts in the development were the two
    concrete ones in [LowerBound.v] and [F23.v]. *)

Theorem no_upper_bound_below_exponential :
  forall n k m, 1 <= n -> 2 <= k -> m <= (k - 1) ^ n -> ~ UpperBound n k m.
Proof.
  intros n k m Hn Hk Hm.
  apply lower_bound_excludes_upper.
  apply (@LowerBound_antitone n k ((k - 1) ^ n) m); [| exact Hm].
  apply lower_bound_exponential; assumption.
Qed.

(** ** The core of a sunflower is determined by its petals *)

Theorem sunflower_core_unique :
  forall S c1 c2,
    2 <= length S -> Sunflower S c1 -> Sunflower S c2 -> SetEq c1 c2.
Proof.
  intros S c1 c2 Hlen [Hsnd Hc1] [_ Hc2].
  destruct S as [|A [|B S']]; simpl in Hlen; try lia.
  assert (HAB : A <> B).
  { pose proof (SetNoDup_NoDup Hsnd) as Hnd.
    inversion Hnd as [|? ? Hni _]; subst.
    intro E; subst B; apply Hni; left; reflexivity. }
  assert (HA : In A (A :: B :: S')) by (left; reflexivity).
  assert (HB : In B (A :: B :: S')) by (right; left; reflexivity).
  apply (@SetEq_trans c1 (inter A B) c2).
  - apply SetEq_sym, (Hc1 A B HA HB HAB).
  - apply (Hc2 A B HA HB HAB).
Qed.

(** ** [Distinct] is strictly stronger than [NoDup]

    [Sunflower.v] deliberately defines [Distinct] as [SetNoDup] rather
    than [NoDup], because [[0;1]] and [[1;0]] are the same set. This
    certifies that the choice is not cosmetic: there is a family that
    is [NoDup] and not [Distinct]. Written with the *completeness*
    half of [Reflect.distinctb_correct] — soundness alone could not
    refute anything. *)

Example distinct_strictly_stronger :
  NoDup [[0; 1]; [1; 0]] /\ ~ Distinct [[0; 1]; [1; 0]].
Proof.
  split.
  - constructor.
    + simpl; intros [E | []]; discriminate.
    + constructor; [simpl; tauto | constructor].
  - intro H; apply distinctb_correct in H; vm_compute in H; discriminate.
Qed.

(** ** How many pairwise disjoint [m]-sets fit in a ground set

    [k] pairwise disjoint sets of size [m] use [km] distinct elements.
    This is the only tool needed to refute the spread hypothesis at
    parameters where the published threshold has not yet been
    reached. *)

Lemma length_le_1_of_all_eq :
  forall (X : Type) (L : list X),
    NoDup L -> (forall a b, In a L -> In b L -> a = b) -> length L <= 1.
Proof.
  intros X L Hnd Heq.
  destruct L as [|a [|b L']]; simpl; [lia | lia | exfalso].
  inversion Hnd as [|? ? Hni _]; subst.
  apply Hni.
  rewrite (Heq a b (or_introl eq_refl) (or_intror (or_introl eq_refl))).
  left; reflexivity.
Qed.

Lemma NoDup_concat_pairwise_disjoint :
  forall S : list (list nat),
    NoDup S ->
    Forall (fun A : list nat => NoDup A) S ->
    PairwiseDisjoint S ->
    NoDup (concat S).
Proof.
  intros S; induction S as [|A S' IH]; simpl; intros Hnd Hall Hpd; [constructor|].
  inversion Hnd as [|? ? HniA Hnd']; subst.
  inversion Hall as [|? ? HndA Hall']; subst.
  apply NoDup_app_intro.
  - exact HndA.
  - apply IH; [exact Hnd' | exact Hall' |].
    intros C D HC HD HCD; apply Hpd; [right; exact HC | right; exact HD | exact HCD].
  - intros x HxA Hxc.
    apply in_concat in Hxc as [B [HB HxB]].
    assert (HAB : A <> B) by (intro E; subst B; contradiction).
    apply (Hpd A B (or_introl eq_refl) (or_intror HB) HAB x HxA HxB).
Qed.

Lemma length_concat_uniform :
  forall m S, Uniform m S -> length (concat S) = length S * m.
Proof.
  intros m S; unfold Uniform; induction S as [|A S' IH]; simpl; intros H;
    [reflexivity|].
  inversion H as [|? ? HUA H']; subst.
  destruct HUA as [HAlen _].
  rewrite app_length, HAlen, (IH H'); reflexivity.
Qed.

Theorem pairwise_disjoint_ground_bound :
  forall (S : list (list nat)) (U : list nat) (m : nat),
    NoDup S -> NoDup U ->
    Uniform m S ->
    (forall A, In A S -> Subset A U) ->
    PairwiseDisjoint S ->
    length S * m <= length U.
Proof.
  intros S U m HndS HndU HU Hsub Hpd.
  assert (Hnc : NoDup (concat S)).
  { apply NoDup_concat_pairwise_disjoint;
      [exact HndS | apply (@Uniform_NoDup m S HU) | exact Hpd]. }
  assert (Hincl : incl (concat S) U).
  { intros x Hx; apply in_concat in Hx as [A [HA HxA]].
    apply (Hsub A HA); exact HxA. }
  pose proof (NoDup_incl_length Hnc Hincl) as Hle.
  rewrite (@length_concat_uniform m S HU) in Hle; exact Hle.
Qed.

(** ** Is the axiom's shape ever false?

    [SpreadYieldsDisjoint n k r] is the shape of [ALWZ.Rao20_lemma2]:
    "every [r]-spread [m]-uniform family with more than [r^m] members
    has [k] pairwise disjoint members". If it held for all [r] the
    axiom's threshold hypothesis would be assuming nothing.

    It does not. Below, a family of [k-1] pairwise disjoint blocks
    satisfies every hypothesis whenever [r^m < k-1] — a pairwise
    disjoint family is as spread as a family can be — and obviously
    fails the conclusion, having only [k-1] members. *)

Lemma deg_le_1_of_pairwise_disjoint :
  forall F T, NoDup F -> PairwiseDisjoint F -> T <> [] -> deg T F <= 1.
Proof.
  intros F T HndF Hpd Hne; unfold deg.
  apply (@length_le_1_of_all_eq (list nat)).
  - apply NoDup_filter; exact HndF.
  - intros A B HA HB.
    apply filter_In in HA as [HAF HcA]; apply filter_In in HB as [HBF HcB].
    apply containsb_true_iff in HcA; apply containsb_true_iff in HcB.
    destruct (list_eq_dec Nat.eq_dec A B) as [E | NE]; [exact E | exfalso].
    destruct T as [|t T0]; [contradiction|].
    apply (Hpd A B HAF HBF NE t); [apply HcA | apply HcB]; left; reflexivity.
Qed.

Lemma disjoint_blocks_PairwiseDisjoint :
  forall count n, n >= 1 -> PairwiseDisjoint (disjoint_blocks count n).
Proof.
  intros count n Hn A B HA HB HAB.
  apply in_disjoint_blocks_iff in HA as [i [Hi EA]].
  apply in_disjoint_blocks_iff in HB as [j [Hj EB]].
  subst A B.
  assert (Hij : i <> j) by (intro E; subst j; apply HAB; reflexivity).
  apply (@disjoint_blocks_pairwise_disjoint count n Hn i j Hi Hj Hij).
Qed.

Theorem spread_yields_disjoint_below_threshold :
  forall n k r m,
    1 <= m -> m <= n -> 2 <= k -> 1 <= r ->
    r ^ m < k - 1 ->
    ~ SpreadYieldsDisjoint n k r.
Proof.
  intros n k r m Hm Hmn Hk Hr Hlt Hsyd.
  assert (HU : Uniform m (disjoint_blocks (k - 1) m))
    by (apply disjoint_blocks_Uniform; lia).
  assert (HD : Distinct (disjoint_blocks (k - 1) m))
    by (apply disjoint_blocks_SetNoDup; lia).
  assert (Hlen : length (disjoint_blocks (k - 1) m) = k - 1)
    by apply disjoint_blocks_length.
  assert (HndF : NoDup (disjoint_blocks (k - 1) m))
    by (apply SetNoDup_NoDup; exact HD).
  assert (Hpd : PairwiseDisjoint (disjoint_blocks (k - 1) m))
    by (apply disjoint_blocks_PairwiseDisjoint; lia).
  assert (Hsp : RaoSpread m (disjoint_blocks (k - 1) m) r).
  { intros T HT Hne.
    pose proof (deg_le_1_of_pairwise_disjoint HndF Hpd Hne) as H1.
    pose proof (pow_pos (m - length T) Hr) as H2.
    lia. }
  destruct (Hsyd m (disjoint_blocks (k - 1) m) Hm Hmn HU HD ltac:(lia) Hsp)
    as [S [Hincl [Hnd [HlenS _]]]].
  pose proof (NoDup_incl_length Hnd Hincl) as Hle.
  lia.
Qed.

(** At [m = 1] this is sharpest: no [r] below [k-1] can work, for any
    uniformity. *)

Corollary spread_yields_disjoint_needs_r :
  forall n k r,
    1 <= n -> 2 <= k -> 1 <= r -> r < k - 1 -> ~ SpreadYieldsDisjoint n k r.
Proof.
  intros n k r Hn Hk Hr Hlt.
  apply (@spread_yields_disjoint_below_threshold n k r 1); try lia.
  rewrite Nat.pow_1_r; exact Hlt.
Qed.

(** Paired with [SpreadReduction.spread_disjoint_above_elementary],
    which proves the same statement true for every [r > n(k-1)], this
    sandwiches the truth region: false below [k-1], true above
    [n(k-1)]. The axiom asserts something about the gap in between, and
    is therefore neither vacuous nor already proved. *)

Theorem spread_yields_disjoint_sandwich :
  forall n k r,
    1 <= n -> 2 <= k -> 1 <= r ->
    (r < k - 1 -> ~ SpreadYieldsDisjoint n k r) /\
    (n * (k - 1) < r -> SpreadYieldsDisjoint n k r).
Proof.
  intros n k r Hn Hk Hr; split.
  - apply spread_yields_disjoint_needs_r; assumption.
  - intro Hbig; apply spread_disjoint_above_elementary; assumption.
Qed.

(** ** A witness inside the gap

    The disjoint-blocks family above is blind at [k = 3]: it needs
    [r^m < k-1 = 2], so it only rules out [r = 1]. The five-cycle
    rules out [r = 2] at uniformity [m = 2] — and no family of
    singletons can, since at [m = 1] the requirement is only
    [r >= k-1 = 2]. So the threshold genuinely grows with the
    uniformity, which is the qualitative content of the [log] factor
    in the published bound.

    Every hypothesis below is discharged by [vm_compute] through the
    certificates of [Reflect.v]; the conclusion is refuted by the
    ground-set bound, since three pairwise disjoint 2-sets need six
    elements and the cycle has five. This family was found by the
    exhaustive search in [rust/src/testbed.rs]: over a five-element
    ground set it reports exactly twelve counterexamples at these
    parameters, all of them relabellings of this one
    ([every_counterexample_on_five_points_is_a_five_cycle]). *)

Definition c5 : Family := [[0; 1]; [1; 2]; [2; 3]; [3; 4]; [0; 4]].

Definition c5_ground : list nat := [0; 1; 2; 3; 4].

Lemma c5_uniform : Uniform 2 c5.
Proof. apply uniformb_correct; reflexivity. Qed.

Lemma c5_distinct : Distinct c5.
Proof. apply distinctb_correct; reflexivity. Qed.

Lemma c5_grounded : forall A, In A c5 -> Subset A c5_ground.
Proof. apply groundedb_correct; reflexivity. Qed.

Lemma c5_rao_spread : RaoSpread 2 c5 2.
Proof.
  apply (@rao_witness_none 2 c5 2).
  - apply (@Uniform_NoDup 2 c5 c5_uniform).
  - vm_compute; reflexivity.
Qed.

(** The same verdict from the independent ground-set procedure. *)

Lemma c5_rao_spread_second_opinion : rao_spreadb 2 c5 2 c5_ground = true.
Proof. vm_compute; reflexivity. Qed.

Theorem no_spread_yields_disjoint_2_3_2 : ~ SpreadYieldsDisjoint 2 3 2.
Proof.
  intro H.
  destruct (H 2 c5 ltac:(lia) ltac:(lia) c5_uniform c5_distinct
              ltac:(vm_compute; lia) c5_rao_spread)
    as [S [Hincl [Hnd [Hlen Hpd]]]].
  assert (HU : Uniform 2 S) by (apply (@Uniform_sublist 2 c5 S c5_uniform Hincl)).
  assert (Hsub : forall A, In A S -> Subset A c5_ground)
    by (intros A HA; apply c5_grounded, Hincl, HA).
  assert (HndU : NoDup c5_ground) by (apply nodupb_correct; reflexivity).
  pose proof (@pairwise_disjoint_ground_bound S c5_ground 2 Hnd HndU HU Hsub Hpd)
    as Hb.
  rewrite Hlen in Hb; vm_compute in Hb; lia.
Qed.

(** ** A second witness, by a completely different argument

    A family already known to contain no [k]-sunflower cannot contain
    [k] pairwise disjoint members either: pairwise disjoint nonempty
    sets *are* a sunflower, with empty core. Every sunflower-free
    family in the repository is therefore a ready-made candidate
    counterexample to the spread hypothesis, needing only a spread
    check.

    Applied to [F23.two_triangles] — the six-edge family that witnesses
    [f(2,3) >= 7] — this refutes [SpreadYieldsDisjoint 2 3 2] a second
    time, sharing no step with the [c5] proof above: that one counts
    ground-set elements, this one goes through the reflective
    3-sunflower detector of [F23.v]. Two independent routes to the same
    refutation is the point; if they disagreed, one of the two notions
    would not mean what its name says. *)

Lemma no_k_disjoint_of_no_sunflower :
  forall k m F S,
    1 <= m -> Uniform m F -> ~ ContainsKSunflower k F ->
    incl S F -> NoDup S -> length S = k -> PairwiseDisjoint S -> False.
Proof.
  intros k m F S Hm HU Hns Hincl Hnd Hlen Hpd.
  apply Hns.
  apply (@ContainsKSunflower_of_incl k S F []); [exact Hincl | exact Hlen |].
  apply pairwise_disjoint_sunflower; [exact Hnd | | exact Hpd].
  apply Forall_forall; intros A HA.
  assert (HAF : In A F) by (apply Hincl, HA).
  pose proof (@Uniform_length m F A HU HAF) as Hl.
  destruct A; [simpl in Hl; lia | discriminate].
Qed.

Lemma two_triangles_rao_spread : RaoSpread 2 two_triangles 2.
Proof.
  apply (@rao_witness_none 2 two_triangles 2).
  - apply (@Uniform_NoDup 2 two_triangles two_triangles_uniform).
  - vm_compute; reflexivity.
Qed.

Theorem no_spread_yields_disjoint_2_3_2_alt : ~ SpreadYieldsDisjoint 2 3 2.
Proof.
  intro H.
  destruct (H 2 two_triangles ltac:(lia) ltac:(lia)
              two_triangles_uniform two_triangles_distinct
              ltac:(vm_compute; lia) two_triangles_rao_spread)
    as [S [Hincl [Hnd [Hlen Hpd]]]].
  apply (@no_k_disjoint_of_no_sunflower 3 2 two_triangles S);
    [lia | exact two_triangles_uniform | exact two_triangles_no_sunflower
     | exact Hincl | exact Hnd | exact Hlen | exact Hpd].
Qed.

(** ** The development's own bounds fit in one order

    Each inequality is obtained by feeding two of the development's
    theorems to [lower_lt_upper]. None of them is restated arithmetic:
    if the lower bound and the upper bound it is paired with were
    mutually contradictory, the line would instead be a derivation of
    [False] from theorems that are all machine-checked — which is to
    say, one of them would be misstated. *)

Corollary bounds_coherent_er :
  forall n k, 1 <= n -> 2 <= k -> (k - 1) ^ n < S ((k - 1) ^ n * fact n).
Proof.
  intros n k Hn Hk.
  apply (@lower_lt_upper n k).
  - apply lower_bound_exponential; assumption.
  - apply erdos_rado_upper_bound; assumption.
Qed.

Corollary bounds_coherent_spread :
  forall n k, 1 <= n -> 2 <= k -> (k - 1) ^ n < S ((n * (k - 1) + 1) ^ n).
Proof.
  intros n k Hn Hk.
  apply (@lower_lt_upper n k).
  - apply lower_bound_exponential; assumption.
  - apply spread_erdos_rado; assumption.
Qed.

(** The exact value [f(2,3) = 7] against both upper bounds and against
    the exponential lower bound. *)

Corollary bounds_coherent_f_2_3 : 6 < 7 /\ 4 < 7 /\ 6 < 26.
Proof.
  repeat split.
  - apply (@lower_lt_upper 2 3); [exact f_2_3_lower | exact f_2_3_upper].
  - apply (@lower_lt_upper 2 3);
      [apply (@lower_bound_exponential 2 3); lia | exact f_2_3_upper].
  - apply (@lower_lt_upper 2 3);
      [exact f_2_3_lower | apply (@spread_erdos_rado 2 3); lia].
Qed.

(** ** The uniformity-2 characterisation

    [TwoUniform.two_uniform_sunflower_free_iff] says a distinct
    2-uniform family avoids [k]-sunflowers exactly when its matching
    number and its maximum degree are both below [k]. Two questions
    that answer themselves if the statement is right and do not if it
    is not. *)

(** *** Is uniformity 2 doing any work in [star_sunflower]?

    [star_sunflower] says distinct 2-sets through a common point are a
    sunflower. The [Forall (UniformSet 2)] hypothesis is the only thing
    stopping it from being a statement about arbitrary families, and if
    it could be dropped the whole sunflower problem would be a
    statement about degrees at every uniformity.

    It cannot. Three 3-sets through the point 1 whose pairwise
    intersections are [{1,2}] and [{1,3}] — different sets, so no
    common core exists at all. *)

Definition three_uniform_star : Family := [[1; 2; 3]; [1; 2; 4]; [1; 3; 5]].

Example star_needs_uniformity_two :
  Uniform 3 three_uniform_star
  /\ Distinct three_uniform_star
  /\ Forall (fun A => In 1 A) three_uniform_star
  /\ ~ (exists core, Sunflower three_uniform_star core).
Proof.
  repeat split.
  - apply uniformb_correct; reflexivity.
  - apply distinctb_correct; reflexivity.
  - repeat (constructor; [simpl; auto|]); constructor.
  - intros [core [_ Hcore]].
    assert (H12 : SetEq (inter [1; 2; 3] [1; 2; 4]) core).
    { apply Hcore; [simpl; auto | simpl; auto | discriminate]. }
    assert (H13 : SetEq (inter [1; 2; 3] [1; 3; 5]) core).
    { apply Hcore; [simpl; auto | simpl; auto | discriminate]. }
    vm_compute in H12, H13.
    assert (H2core : In 2 core) by (apply (proj1 H12); simpl; auto).
    pose proof (proj2 H13 2 H2core) as Hbad.
    simpl in Hbad; lia.
Qed.

(** *** Is [two_triangles] extremal for both parameters at once?

    [F23.two_triangles] witnesses [f(2,3) >= 7], and separately refutes
    [SpreadYieldsDisjoint 2 3 2]. Under the characterisation those are
    not two facts: a 3-sunflower-free graph is exactly one with maximum
    degree at most 2 and matching number at most 2, and [two_triangles]
    is the largest such graph — six edges, which is [CH(2,2)] for the
    Chvátal–Hanson function.

    So both constraints must be *tight* on it. The bounds below are
    derived from [two_triangles_no_sunflower] through the
    characterisation; the matching witness and the degree value are
    computed directly. If the characterisation were off by one in
    either parameter, the derived bound and the computed value would
    contradict each other here. *)

Corollary two_triangles_saturates_both_parameters :
  (forall v, deg [v] two_triangles < 3)
  /\ ~ HasKDisjoint 3 two_triangles
  /\ deg [0] two_triangles = 2
  /\ HasKDisjoint 2 two_triangles.
Proof.
  destruct (proj1 (two_uniform_sunflower_free_iff 3 two_triangles
                     ltac:(lia) two_triangles_uniform two_triangles_distinct)
              two_triangles_no_sunflower) as [Hnd Hdeg].
  split; [exact Hdeg|].
  split; [exact Hnd|].
  split; [vm_compute; reflexivity|].
  exists [[0; 1]; [3; 4]].
  split; [| split; [| split]].
  - intros A [E | [E | []]]; subst A; simpl; auto.
  - apply SetNoDup_NoDup, distinctb_correct; reflexivity.
  - reflexivity.
  - apply pairwise_disjointb_correct; reflexivity.
Qed.

(** *** The two shapes are both realised

    [sunflower_shape] splits every sunflower into a matching or a star.
    Neither branch is decoration: [Reflect.three_pairs] is a
    3-sunflower of the first kind and [Reflect.star3] one of the
    second, and the characterisation sees both. *)

Example both_sunflower_shapes_occur :
  ContainsKSunflower 3 three_pairs /\ ContainsKSunflower 3 star3.
Proof.
  split; apply (two_uniform_sunflower_iff 3 _ ltac:(lia));
    try (apply uniformb_correct; reflexivity);
    try (apply distinctb_correct; reflexivity).
  - left. exists three_pairs.
    split; [| split; [| split]].
    + apply incl_refl.
    + apply SetNoDup_NoDup, distinctb_correct; reflexivity.
    + reflexivity.
    + apply pairwise_disjointb_correct; reflexivity.
  - right. exists 0. vm_compute; lia.
Qed.
