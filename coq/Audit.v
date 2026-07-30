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
     ProductLowerBound Spread Reflect SpreadReduction TwoUniform
     CliqueLowerBound F23 LinkCharacterisation DirectSum Intersecting
     Conjecture IotaRate SpreadRestrictions SliceRank IotaGround Compression
     ErdosRado_Greedy Product Sharp.
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
  - rewrite firstn_length_le; lia.
  - intro Hc; apply Hns.
    apply (@ContainsKSunflower_incl k (firstn m' F) F (incl_firstn m' F) Hc).
Qed.

(** [LowerBound] pins the family size with an equality. The variant
    that only asks for *at least* [m] members defines the same
    predicate — antitonicity is exactly what makes the two agree.

    The mutation [lowerbound-at-least] in [tools/mutations.toml]
    weakens the definition this way, and is the development's one
    genuine survivor: this theorem is why nothing can notice. It used
    to be recorded as a script-level kill, because four proofs proved
    the size hypothesis with tactics that only worked against [=]; they
    now use [rewrite ...; lia], which works against either, so what the
    mutation reports is a property of the definition. *)

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

(** [length_le_1_of_all_eq] stays here; the counting bound it sits next
    to moved to [LowerBound.v], where the pairwise-disjoint
    constructions it bounds are built. *)

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
    [k] pairwise disjoint members either: pairwise disjoint sets *are*
    a sunflower, with empty core. Every sunflower-free family in the
    repository is therefore a ready-made candidate counterexample to
    the spread hypothesis, needing only a spread check.

    No uniformity is needed — the empty set is disjoint from everything
    and is a legitimate petal of the empty core, so the statement holds
    of families containing it too. It used to carry [1 <= m] and
    [Uniform m F] to rule that case out; see
    [Sunflower.SetNoDup_of_pairwise_disjoint] for why they were
    decoration, and [LinkCharacterisation.v] for where the case is
    load-bearing rather than merely admissible.

    Applied to [F23.two_triangles] — the six-edge family that witnesses
    [f(2,3) >= 7] — this refutes [SpreadYieldsDisjoint 2 3 2] a second
    time, sharing no step with the [c5] proof above: that one counts
    ground-set elements, this one goes through the reflective
    3-sunflower detector of [F23.v]. Two independent routes to the same
    refutation is the point; if they disagreed, one of the two notions
    would not mean what its name says. *)

Lemma no_k_disjoint_of_no_sunflower :
  forall k F S,
    ~ ContainsKSunflower k F ->
    incl S F -> NoDup S -> length S = k -> PairwiseDisjoint S -> False.
Proof.
  intros k F S Hns Hincl Hnd Hlen Hpd.
  apply Hns.
  apply (@ContainsKSunflower_of_incl k S F []); [exact Hincl | exact Hlen |].
  apply pairwise_disjoint_sunflower; [exact Hnd | exact Hpd].
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
  apply (@no_k_disjoint_of_no_sunflower 3 two_triangles S);
    [exact two_triangles_no_sunflower
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

(** *** Is [Distinct] doing any work in the degree identification?

    [rao_spread_two_iff_degree] says [RaoSpread 2 F r] is exactly the
    maximum-degree bound. That rests entirely on [Distinct]: the
    [|T| = 2] clause of the spread condition asks [deg T F <= r ^ 0 =
    1], and it is distinctness, not uniformity, that supplies it.

    Drop it and the identification is false in the interesting
    direction. [[0;1]] and [[1;0]] are the same set written twice —
    [NoDup] as a list of lists, not [Distinct] — every vertex has
    degree 2, and yet the family is not 2-spread, because the 2-set
    [{0,1}] lies in two members. So the degree bound holds and
    [RaoSpread] fails.

    Same family as [distinct_strictly_stronger], which is the point:
    the design choice recorded there is what makes the identification
    true here. *)

Definition repeated_edge : Family := [[0; 1]; [1; 0]].

Example distinct_is_load_bearing_in_the_degree_identification :
  Uniform 2 repeated_edge
  /\ NoDup repeated_edge
  /\ ~ Distinct repeated_edge
  /\ (forall v, deg [v] repeated_edge <= 2)
  /\ ~ RaoSpread 2 repeated_edge 2.
Proof.
  split; [apply uniformb_correct; reflexivity|].
  split.
  { constructor; [intros [E | []]; discriminate |].
    constructor; [intros [] | constructor]. }
  split.
  { intro H; apply distinctb_correct in H; vm_compute in H; discriminate. }
  split.
  { intros v; destruct v as [|[|v]]; vm_compute; lia. }
  intro Hspread.
  assert (HndT : NoDup [0; 1])
    by (constructor; [intros [E | []]; discriminate |];
        constructor; [intros [] | constructor]).
  pose proof (Hspread [0; 1] HndT ltac:(discriminate)) as Hb.
  vm_compute in Hb; lia.
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

(** ** The clique lower bound

    [CliqueLowerBound.two_cliques_lower_bound] gives [f(2,k) >= k(k-1)+1]
    for every odd [k], from two disjoint copies of [K_k]. Three
    questions. *)

(** *** Does it contradict any upper bound the development proves?

    Derived, not restated: if [k(k-1)] members could be forced to
    contain a [k]-sunflower, the line below would be a proof of [False]
    from two machine-checked theorems. *)

Corollary bounds_coherent_clique :
  forall k, 3 <= k -> Nat.Odd k -> k * (k - 1) < S ((k - 1) ^ 2 * fact 2).
Proof.
  intros k Hk Hodd.
  apply (@lower_lt_upper 2 k).
  - apply two_cliques_lower_bound; assumption.
  - apply erdos_rado_upper_bound; lia.
Qed.

(** *** Is it the same construction as the one already formalised?

    At [k = 3] it must be, or one of the two witnesses is wrong. The
    clique construction emits the six edges in a different order, so
    the families are not equal as lists — they are equal as families,
    which is what [FamilyEquiv] says and what
    [ContainsKSunflower_equiv] then makes interchangeable. *)

Example clique_construction_is_two_triangles_reordered :
  FamilyEquiv (two_cliques [0; 1; 2] [3; 4; 5]) two_triangles.
Proof.
  split; apply SubFamilySetEq_incl; intros A HA;
    vm_compute in HA |- *; tauto.
Qed.

(** *** Is oddness of [k] doing work, or is it an artefact of the proof?

    It is doing work. Two copies of [K_k] have [2k] vertices, and [k]
    disjoint edges would have to match all of them; each component
    blocks that only because it has an odd number of vertices. At
    [k = 4] the same construction has four disjoint edges and therefore
    *does* contain a 4-sunflower, so the hypothesis cannot simply be
    dropped — the even case needs the other Chvátal–Hanson extremal
    graph, which is not two cliques. *)

Example oddness_is_needed :
  ContainsKSunflower 4 (two_cliques [0; 1; 2; 3] [4; 5; 6; 7]).
Proof.
  apply (two_uniform_sunflower_iff 4 _ ltac:(lia)).
  - apply two_cliques_uniform; apply nodupb_correct; reflexivity.
  - apply two_cliques_distinct;
      [apply nodupb_correct; reflexivity
      | apply nodupb_correct; reflexivity
      | apply disjointb_correct; reflexivity].
  - left. exists [[0; 1]; [2; 3]; [4; 5]; [6; 7]].
    split; [| split; [| split]].
    + intros A HA; vm_compute in HA |- *; tauto.
    + apply SetNoDup_NoDup, distinctb_correct; reflexivity.
    + reflexivity.
    + apply pairwise_disjointb_correct; reflexivity.
Qed.

(** ** The link characterisation

    [LinkCharacterisation.sunflower_iff_link_matching] says a family
    has a [k]-sunflower exactly when some link of it has [k] pairwise
    disjoint members. Three questions, each of which the exhaustive
    enumeration in `rust/tests/link_characterisation.rs` also asks
    computationally.

    The first two pin down the cases where a *weaker* reading of the
    statement — one that a uniform family cannot distinguish, or one
    restricted to the cores the uniformity-2 theorem uses — would still
    have compiled. *)

(** *** May a member of a sunflower equal its core?

    It may, and the characterisation needs it to. [{1}, {1,2}, {1,3}]
    is a 3-sunflower with core [{1}] — every pairwise intersection is
    [{1}], including [{1} ∩ {1,2}] — and the member equal to the core
    contributes the *empty* petal to the link, which is disjoint from
    everything.

    So [Sunflower.pairwise_disjoint_sunflower] must not require its
    members to be nonempty. It used to. No uniform family exhibits the
    case, because at uniformity [m] at most one member can equal a
    given [Y], so the empty petal never has a second petal to be
    disjoint from; the non-uniform enumeration is what found it. *)

Definition core_is_a_member : Family := [[1]; [1; 2]; [1; 3]].

Example a_member_may_equal_the_core :
  link [1] core_is_a_member = [[]; [2]; [3]]
  /\ HasKDisjoint 3 (link [1] core_is_a_member)
  /\ ContainsKSunflower 3 core_is_a_member.
Proof.
  assert (Hm : HasKDisjoint 3 (link [1] core_is_a_member)).
  { exists [[]; [2]; [3]].
    split; [| split; [| split]].
    - intros A HA; vm_compute in HA |- *; tauto.
    - apply SetNoDup_NoDup, distinctb_correct; reflexivity.
    - reflexivity.
    - apply pairwise_disjointb_correct; reflexivity. }
  split; [vm_compute; reflexivity|].
  split; [exact Hm|].
  exact (link_matching_gives_sunflower 3 core_is_a_member [1] Hm).
Qed.

(** *** Are cores of size two or more ever needed?

    At uniformity 2 they never are
    ([LinkCharacterisation.two_uniform_only_small_cores]), which is
    what makes [TwoUniform.v] a statement about graphs. Above it they
    are, and the smallest witness is three 3-sets through a common
    pair.

    [{0,1,2}, {0,1,3}, {0,1,4}] is a 3-sunflower with core [{0,1}].
    Every member contains both 0 and 1, so
    [two_common_points_force_a_big_core] rules out every core with
    fewer than two points at once — the empty core (the family is not a
    matching), and every singleton (a link over one of the two shared
    points still passes through the other).

    This is what the [exists Y] in the characterisation is quantifying
    over, and it is why the statement is not a restatement of
    [sunflower_shape]. *)

Definition common_pair : Family := [[0; 1; 2]; [0; 1; 3]; [0; 1; 4]].

Example core_of_size_two_is_needed :
  Uniform 3 common_pair /\ Distinct common_pair
  /\ HasKDisjoint 3 (link [0; 1] common_pair)
  /\ ContainsKSunflower 3 common_pair
  /\ (forall Y, HasKDisjoint 3 (link Y common_pair) ->
                exists a b, In a Y /\ In b Y /\ a <> b).
Proof.
  assert (Hm : HasKDisjoint 3 (link [0; 1] common_pair)).
  { exists [[2]; [3]; [4]].
    split; [| split; [| split]].
    - intros A HA; vm_compute in HA |- *; tauto.
    - apply SetNoDup_NoDup, distinctb_correct; reflexivity.
    - reflexivity.
    - apply pairwise_disjointb_correct; reflexivity. }
  split; [apply uniformb_correct; reflexivity|].
  split; [apply distinctb_correct; reflexivity|].
  split; [exact Hm|].
  split; [exact (link_matching_gives_sunflower 3 common_pair [0; 1] Hm)|].
  intros Y HY.
  apply (two_common_points_force_a_big_core 3 common_pair 0 1 Y);
    [lia | lia | | | exact HY];
    apply Forall_forall; intros A HA;
    destruct HA as [E | [E | [E | []]]]; subst A; simpl; auto.
Qed.

(** *** Do the two routes to the uniformity-2 characterisation agree?

    [TwoUniform.two_uniform_sunflower_iff] is proved through
    [sunflower_shape] and [star_sunflower].
    [LinkCharacterisation.two_uniform_sunflower_iff_via_link] proves
    the same statement from the general characterisation and two
    counting facts about links, mentioning neither. Two independent
    routes to one statement: if they disagreed, one of the two notions
    would not mean what its name says.

    The specification is named once and both routes are checked
    against it by [exact]. That is the whole content: if either
    theorem's statement drifts, the corresponding line stops
    typechecking. Writing it as an implication between the two would
    have been vacuous — [P <-> P] is provable by [reflexivity], so it
    would check nothing about either proof. *)

Definition TwoUniformCharacterisation : Prop :=
  forall (k : nat) (F : Family),
    2 <= k -> Uniform 2 F -> Distinct F ->
    (ContainsKSunflower k F
     <-> HasKDisjoint k F \/ (exists v, k <= deg [v] F)).

Example the_shape_route_proves_it : TwoUniformCharacterisation.
Proof. exact two_uniform_sunflower_iff. Qed.

Example the_link_route_proves_it : TwoUniformCharacterisation.
Proof. exact two_uniform_sunflower_iff_via_link. Qed.

(** ** The direct sum

    [DirectSum.lower_bound_sum] is the first bound here that is not a
    construction but an *operation* on constructions, so the questions
    it raises are different from the ones a construction raises. Four
    are pinned below: does it contradict any upper bound proved here;
    is it genuinely stronger than the construction it supersedes, as a
    statement about [UpperBound] rather than as arithmetic; does it
    reproduce that construction; and does it say anything at a concrete
    parameter. *)

(** *** Does it contradict any upper bound the development proves?

    Same idiom as [bounds_coherent_er]: the inequality is *derived*
    from the two theorems by [lower_lt_upper], so a contradictory pair
    would make this a machine-checked proof of [False]. *)

Corollary bounds_coherent_direct_sum :
  forall t, 1 <= t -> 6 ^ t < S ((3 - 1) ^ (t * 2) * fact (t * 2)).
Proof.
  intros t Ht.
  apply (@lower_lt_upper (t * 2) 3).
  - exact (lower_bound_f_n_3 t).
  - apply erdos_rado_upper_bound; lia.
Qed.

Corollary bounds_coherent_direct_sum_spread :
  forall t, 1 <= t -> 6 ^ t < S ((t * 2 * (3 - 1) + 1) ^ (t * 2)).
Proof.
  intros t Ht.
  apply (@lower_lt_upper (t * 2) 3).
  - exact (lower_bound_f_n_3 t).
  - apply spread_erdos_rado; lia.
Qed.

(** *** Is it strictly stronger than the product construction?

    [no_upper_bound_below_exponential] refutes [UpperBound n k m] for
    every [m <= (k-1)^n], and nothing before this file refuted it any
    higher. At uniformity [2t] that ceiling is [2^(2t)]. The direct sum
    refutes [UpperBound] at [6^t], and [six_beats_four] places that
    strictly above the ceiling — for every [t >= 1], with the gap
    growing geometrically. So the second conjunct is a statement the
    rest of the development cannot prove. *)

Corollary direct_sum_strictly_beyond_the_product :
  forall t, 1 <= t ->
    2 ^ (t * 2) < 6 ^ t /\ ~ UpperBound (t * 2) 3 (6 ^ t).
Proof.
  intros t Ht.
  split; [exact (six_beats_four t Ht)|].
  apply lower_bound_excludes_upper, lower_bound_f_n_3.
Qed.

(** [1 <= t] is not decoration: at [t = 0] both sides are the empty
    product, so the inequality is [1 < 1]. The improvement starts at
    uniformity 2 and compounds from there. *)

Corollary no_upper_bound_at_clique_power :
  forall k t, 3 <= k -> Nat.Odd k -> 1 <= t ->
    (k - 1) ^ (t * 2) < (k * (k - 1)) ^ t /\
    ~ UpperBound (t * 2) k ((k * (k - 1)) ^ t).
Proof.
  intros k t Hk Hodd Ht.
  split; [apply cliques_beat_product; lia|].
  apply lower_bound_excludes_upper, lower_bound_cliques_power; assumption.
Qed.

(** *** Does it reproduce the construction it supersedes?

    The [t]-fold direct sum of the trivial [(k-1)]-point family is the
    product family of [ProductLowerBound.v], so the exponential lower
    bound should fall out of the general theorem as well as out of its
    own dedicated induction. Both routes are checked against one named
    specification by [exact], the same way the two routes to the
    uniformity-2 characterisation are: if either statement drifts, the
    corresponding line stops typechecking. The routes share exactly one
    step, the canonicalisation lemma [contains_sunflower_literal], which
    both use to turn an abstract sunflower into a literal subfamily.
    Past that they diverge completely: [ProductLowerBound] reasons about
    [prod_family] by an induction on blocks, and [DirectSum] never
    mentions it. *)

Definition ExponentialLowerBound : Prop :=
  forall n k, 1 <= n -> 2 <= k -> LowerBound n k ((k - 1) ^ n).

Example the_product_route_proves_it : ExponentialLowerBound.
Proof. exact lower_bound_exponential. Qed.

Example the_direct_sum_route_proves_it : ExponentialLowerBound.
Proof. exact lower_bound_exponential_via_direct_sum. Qed.

(** *** What does it say at a concrete parameter?

    At uniformity 4 and [k = 3]: the product family has 16 members and
    the direct sum of two copies of [two_triangles] has 36, so
    [f(4,3) >= 37] where the development previously reached only
    [f(4,3) >= 17]. Both numbers are the general theorems evaluated,
    not separate constructions. *)

Example f_4_3_at_least_37 :
  LowerBound 4 3 36 /\ ~ UpperBound 4 3 36 /\ LowerBound 4 3 16.
Proof.
  split; [exact (lower_bound_f_n_3 2)|].
  split; [apply lower_bound_excludes_upper; exact (lower_bound_f_n_3 2)|].
  exact (@lower_bound_exponential 4 3 ltac:(lia) ltac:(lia)).
Qed.

(** *** Is the relabelling doing anything?

    [rmapF] is what lets two families from [LowerBound]'s existential be
    placed on disjoint ground sets. Evaluating it says both that it
    moves the points and that the two images are disjoint — the
    property [sum_family_no_sunflower] needs and cannot check for
    itself. *)

Example relabelling_separates_the_ground_sets :
  rmapF ev [[0; 1]; [1; 2]] = [[0; 2]; [2; 4]]
  /\ rmapF od [[0; 1]; [1; 2]] = [[1; 3]; [3; 5]]
  /\ length (sum_family (rmapF ev two_triangles) (rmapF od two_triangles)) = 36.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** *** Is the asymmetry real?

    [DirectSum.sum_family_no_sunflower] asks only the *first* family to
    be uniform, because the proof splits each member of the sum at the
    front. That is a fact about the proof, not about the construction:
    the two sums are the same family of sets with the halves swapped,
    and [ContainsKSunflower_equiv] says the predicate cannot tell them
    apart. So either side's uniformity is enough, and this is where it
    can be said, since the invariance lemma lives here.

    What fails is dropping it from both, which is the next entry. *)

Lemma sum_family_comm_equiv :
  forall F1 F2, FamilyEquiv (sum_family F1 F2) (sum_family F2 F1).
Proof.
  assert (H : forall F1 F2, SubFamilySetEq (sum_family F1 F2) (sum_family F2 F1)).
  { intros F1 F2 C HC.
    apply in_sum_family_iff in HC as [A [B [HA [HB E]]]]; subst C.
    exists (B ++ A); split.
    - apply in_sum_family_iff; exists B, A.
      split; [exact HB | split; [exact HA | reflexivity]].
    - split; intros x Hx; apply in_app_or in Hx; apply in_or_app; tauto. }
  intros F1 F2; split; apply H.
Qed.

Corollary sum_family_no_sunflower_right :
  forall b k (F1 F2 : Family),
    2 <= k ->
    Uniform b F2 ->
    ~ ContainsKSunflower k F1 -> ~ ContainsKSunflower k F2 ->
    CrossDisjoint F1 F2 ->
    ~ ContainsKSunflower k (sum_family F1 F2).
Proof.
  intros b k F1 F2 Hk HU2 Hno1 Hno2 Hcross Hc.
  assert (Hcross' : CrossDisjoint F2 F1).
  { intros A B HA HB; apply Disjoint_sym; exact (Hcross B A HB HA). }
  apply (sum_family_no_sunflower b k F2 F1 Hk HU2 Hno2 Hno1 Hcross').
  apply (@ContainsKSunflower_equiv k (sum_family F1 F2) (sum_family F2 F1)
           (sum_family_comm_equiv F1 F2)).
  exact Hc.
Qed.

(** *** Is uniformity doing any work in the direct sum?

    It is, and the counterexample is as small as it can be. Drop
    uniformity from [DirectSum.sum_family_no_sunflower] and the theorem
    is false: [{0}, {0,1}] and [{2}, {2,3}] have two members each, so
    neither contains a 3-sunflower for the trivial reason, their ground
    sets are disjoint, and their direct sum contains one.

    The mechanism is exactly the second bullet of the file's case
    analysis. There the argument runs "two first halves coincide, so
    their common value is the constant intersection, so it sits inside
    every first half — and since all of them have size [a], all of them
    coincide". Without uniformity the last step fails: [{0}] sits inside
    [{0,1}] without equalling it, and the sunflower below is built out
    of precisely that containment, with the same containment happening
    on the other side ([{2}] inside [{2,3}]).

    So this is not a gap in the proof that a cleverer argument would
    close. The hypothesis is the theorem. *)

Example uniformity_is_needed_in_the_direct_sum :
  ~ ContainsKSunflower 3 [[0]; [0; 1]]
  /\ ~ ContainsKSunflower 3 [[2]; [2; 3]]
  /\ CrossDisjoint [[0]; [0; 1]] [[2]; [2; 3]]
  /\ Distinct (sum_family [[0]; [0; 1]] [[2]; [2; 3]])
  /\ ContainsKSunflower 3 (sum_family [[0]; [0; 1]] [[2]; [2; 3]]).
Proof.
  split; [apply no_k_sunflower_short_family; simpl; lia|].
  split; [apply no_k_sunflower_short_family; simpl; lia|].
  split.
  { intros A B HA HB x HxA HxB.
    simpl in HA, HB.
    destruct HA as [E | [E | []]]; destruct HB as [E' | [E' | []]];
      subst A B; simpl in HxA, HxB; lia. }
  split; [apply distinctb_correct; reflexivity|].
  apply (@ContainsKSunflower_of_incl 3 [[0; 2]; [0; 2; 3]; [0; 1; 2]] _ [0; 2]).
  - intros A HA; simpl in HA |- *; tauto.
  - reflexivity.
  - split; [apply set_nodupb_correct; reflexivity|].
    intros A B HA HB Hne.
    simpl in HA, HB.
    destruct HA as [E | [E | [E | []]]]; destruct HB as [E' | [E' | [E' | []]]];
      subst A B; try (exfalso; apply Hne; reflexivity);
      split; intros x Hx; simpl in Hx |- *; lia.
Qed.

(** The other hypothesis, cross-disjointness, is load-bearing one step
    earlier: overlapping ground sets make the concatenation repeat a
    point, so the sum is not even a family of sets. [sum_family_Uniform]
    is where that is used, and the mutation [directsum-drop-cross] in
    [tools/mutations.toml] is what checks that no later proof quietly
    survives without it. *)

(** ** The two restrictions of the spread lemma

    [SpreadRestrictions] settles two readings of "the recursion's
    families are special" in opposite directions. Both deserve a
    non-vacuity check, because a restriction that turns out to be
    vacuous and one that turns out to have content look identical until
    someone checks. *)

(** *** Is the link restriction really vacuous, or only unprovable?

    Vacuous: [two_triangles] — a family with no obvious "I am a link"
    about it — is exhibited as the link of an explicit 3-uniform family,
    by computation rather than by the general theorem. If the
    construction were wrong, this would not evaluate. *)

Example two_triangles_is_a_link :
  link (fresh_block two_triangles 1) (lift_to_link two_triangles 1)
  = two_triangles
  /\ length (lift_to_link two_triangles 1) = 6
  /\ Uniform 3 (lift_to_link two_triangles 1).
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  apply uniformb_correct; vm_compute; reflexivity.
Qed.

(** *** Does the sunflower-free restriction have content?

    It does, in the only sense available without proving the two
    hypotheses inequivalent: it is *implied* by the unrestricted one
    ([SpreadRestrictions.syd_implies_sunflower_free_bound]) and it is
    enough to run the reduction, so the development asks for strictly
    less than it did. What is checked here is that the weaker hypothesis
    is not vacuous — it fails at parameters where the stronger one
    fails, so it is not accidentally trivial.

    At [(m,k,r) = (2,3,2)] the five-cycle is 2-spread with 5 > 4
    members and sunflower-free, so it refutes the restricted form too. *)

Lemma c5_no_sunflower : ~ ContainsKSunflower 3 c5.
Proof.
  intro Hc.
  pose proof (sunflower3b_sound c5 Hc) as E; vm_compute in E; discriminate.
Qed.

Theorem no_spread_bounds_sunflower_free_2_3_2 :
  ~ SpreadBoundsSunflowerFree 2 3 2.
Proof.
  intro H.
  assert (Hb : length c5 <= 2 ^ 2).
  { apply (H 2 c5); try lia.
    - exact c5_uniform.
    - exact c5_distinct.
    - exact c5_no_sunflower.
    - exact c5_rao_spread. }
  vm_compute in Hb; lia.
Qed.

(** ** The polynomial method

    [SliceRank] names the one fact that stands between Naslund–Sawin and
    the conjecture at [k = 3]. Two things are worth pinning: that the
    axiom's exponential is load-bearing rather than decoration, and that
    the missing hypothesis is realised at the one exact value known
    here. *)

(** *** Is the exponential in [NaslundSawin] doing work?

    Replace [C ^ n] by a linear function of the ground set and the
    statement is false, witnessed by the product family: [prod_family 2 6]
    is 64 sunflower-free 6-sets on 12 points, against [3 * (12 + 1) = 39].

    So the axiom is not a weak statement dressed up — anything that
    proves it has to see the exponential. *)

Theorem ns_exponential_is_load_bearing :
  ~ (forall (U : list nat) (F : Family),
        NoDup U -> Distinct F -> Grounded F U ->
        ~ ContainsKSunflower 3 F ->
        length F <= 3 * (length U + 1)).
Proof.
  intro H.
  assert (Hno : ~ ContainsKSunflower 3 (prod_family 2 6)).
  { intro Hc.
    destruct (contains_sunflower_literal 3 (prod_family 2 6) Hc)
      as [S [core [Hincl [Hnd [Hlen Hsun]]]]].
    exact (prod_family_no_literal_sunflower 2 3 ltac:(lia) ltac:(lia) 6 S core
             Hincl Hnd Hlen Hsun). }
  assert (Hb : length (prod_family 2 6) <= 3 * (length (seq 0 12) + 1)).
  { apply H.
    - apply seq_NoDup.
    - apply prod_family_SetNoDup.
    - intros A HA y Hy.
      apply in_seq; split; [lia|].
      pose proof (prod_family_bounded 2 6 A y HA Hy); lia.
    - exact Hno. }
  rewrite prod_family_length, seq_length in Hb.
  vm_compute in Hb; lia.
Qed.

(** *** Is [GroundBounded] realised anywhere?

    At the one exact value this development knows. [f(2,3) = 7], so the
    extremal 2-uniform sunflower-free family has six members, and
    [two_triangles] realises it on six points — [3 * m] with [m = 2].
    That is the [m = 2] row of the table in [SliceRank]'s header,
    machine-checked rather than measured. *)

Example ground_bounded_at_m_2 :
  Uniform 2 two_triangles /\ Distinct two_triangles
  /\ length two_triangles = 6
  /\ ~ ContainsKSunflower 3 two_triangles
  /\ Grounded two_triangles (seq 0 6)
  /\ length (seq 0 6) <= 3 * 2.
Proof.
  split; [apply uniformb_correct; vm_compute; reflexivity|].
  split; [apply distinctb_correct; vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [exact two_triangles_no_sunflower|].
  split.
  { unfold Grounded.
    apply (proj1 (groundedb_correct two_triangles (seq 0 6))).
    vm_compute; reflexivity. }
  vm_compute; lia.
Qed.

(** *** Does the searched family beat the constructed one?

    [SliceRank.lower_bound_3_3_14] comes from an exhaustive search;
    [DirectSum.lower_bound_f_n_3_odd] at [t = 1] comes from a
    construction. They are bounds on the same quantity, so they must be
    comparable and the search must not be *below* the construction —
    the search is exhaustive over nine points, and the direct-sum family
    at uniformity 3 lives on eight, so it was inside the search space.

    Derived from the two formal statements rather than restated: if the
    search had returned something smaller than the construction, this
    would be a proof that the construction is not what it says. *)

Corollary searched_beats_constructed_at_3_3 :
  LowerBound 3 3 12 /\ LowerBound 3 3 14 /\ 12 < 14.
Proof.
  split; [exact (lower_bound_f_n_3_odd 1)|].
  split; [exact lower_bound_3_3_14 | lia].
Qed.

(** And it does not contradict either upper bound. *)

Corollary bounds_coherent_3_3 : 14 < S (2 ^ 3 * fact 3) /\ 14 < S (7 ^ 3).
Proof.
  split.
  - apply (@lower_lt_upper 3 3);
      [exact lower_bound_3_3_14 | apply erdos_rado_upper_bound; lia].
  - apply (@lower_lt_upper 3 3);
      [exact lower_bound_3_3_14 | apply (@spread_erdos_rado 3 3); lia].
Qed.

(** ** Doubling an intersecting family

    [Intersecting.doubling_lower_bound] generalises [two_triangles]:
    two disjoint copies of an *intersecting* sunflower-free family are
    sunflower-free. The hypothesis that is easy to overlook is
    "intersecting", so that is what gets pinned. *)

(** *** Is the intersecting hypothesis load-bearing?

    It is, and the counterexample is as small as a counterexample can
    be. [{0}, {1}] is 1-uniform, distinct and 3-sunflower-free for the
    trivial reason that it has two members — but it is not intersecting,
    and its doubling is four singletons, any three of which are pairwise
    disjoint and so a 3-sunflower with empty core.

    Without the hypothesis the theorem is false at [b = 1], and the
    whole [iota] programme rests on it. *)

Example intersecting_is_needed_in_the_doubling :
  Uniform 1 [[0]; [1]] /\ Distinct [[0]; [1]]
  /\ ~ ContainsKSunflower 3 [[0]; [1]]
  /\ ~ Intersecting [[0]; [1]]
  /\ ContainsKSunflower 3 (double [[0]; [1]]).
Proof.
  split; [apply uniformb_correct; vm_compute; reflexivity|].
  split; [apply distinctb_correct; vm_compute; reflexivity|].
  split; [apply no_k_sunflower_short_family; simpl; lia|].
  split.
  { intro H.
    apply (H [0] [1] (or_introl eq_refl) (or_intror (or_introl eq_refl))).
    intros x [E | []] [E' | []]; subst x; discriminate. }
  apply (@ContainsKSunflower_of_incl 3 [[0]; [2]; [1]] _ []).
  - intros A HA; vm_compute in HA |- *; tauto.
  - reflexivity.
  - split; [apply set_nodupb_correct; reflexivity|].
    intros A B HA HB Hne.
    simpl in HA, HB.
    destruct HA as [E | [E | [E | []]]]; destruct HB as [E' | [E' | [E' | []]]];
      subst A B; try (exfalso; apply Hne; reflexivity);
      split; intros x Hx; vm_compute in Hx |- *; tauto.
Qed.

(** *** Does the sharper seed contradict anything?

    [f(3,3) >= 21] against both upper bounds, derived rather than
    restated. And against the two weaker lower bounds it replaces: the
    ground-set search's 15 and the direct sum's 13. *)

Corollary bounds_coherent_3_3_sharp :
  20 < S ((3 - 1) ^ 3 * fact 3) /\ 20 < S (7 ^ 3)
  /\ 12 < 14 /\ 14 < 20.
Proof.
  split.
  { apply (@lower_lt_upper 3 3);
      [exact lower_bound_3_3_20 | apply erdos_rado_upper_bound; lia]. }
  split.
  { apply (@lower_lt_upper 3 3);
      [exact lower_bound_3_3_20 | apply (@spread_erdos_rado 3 3); lia]. }
  split; lia.
Qed.

(** *** Is the doubling the construction we already had?

    At [b = 2] the largest intersecting sunflower-free graph is the
    triangle, and doubling it is [two_triangles] up to relabelling —
    the same family that gives [f(2,3) = 7]. So the general theorem
    subsumes the specific construction rather than sitting beside it. *)

Example doubling_at_b_2_is_two_triangles :
  double [[0; 1]; [0; 2]; [1; 2]]
  = [[0; 2]; [0; 4]; [2; 4]; [1; 3]; [1; 5]; [3; 5]]
  /\ LowerBound 2 3 6.
Proof.
  split; [vm_compute; reflexivity|].
  apply (doubling_lower_bound 2 [[0; 1]; [0; 2]; [1; 2]]);
    [ lia
    | apply uniformb_correct; vm_compute; reflexivity
    | apply distinctb_correct; vm_compute; reflexivity
    | apply intersectingb_correct; vm_compute; reflexivity
    | intro Hc;
      pose proof (sunflower3b_sound [[0; 1]; [0; 2]; [1; 2]] Hc) as E;
      vm_compute in E; discriminate ].
Qed.

(** *** Is the upper bound on [iota] doing anything?

    [Intersecting.intersecting_link_bound] is the only thing proved
    about [iota] in the upward direction — every other value in the
    programme is a measurement. Two questions it should answer.

    First, is it *satisfied* by what the search returns, or does the
    search contradict it? [iota3] has ten members and the bound at
    [b = 3] is eighteen, so the two are consistent — and the check is
    the bound applied to the witness, not the numbers restated.

    Second, is it *loose*? Yes, by eight at the one place both are
    known, which is worth recording so nobody mistakes it for sharp. *)

Example iota_bound_holds_at_the_witness :
  length iota3 = 10 /\ length iota3 <= 18 /\ 10 < 18.
Proof.
  split; [vm_compute; reflexivity|].
  split; [| lia].
  apply iota_three_at_most_eighteen;
    [ apply iota3_uniform | apply iota3_distinct
    | apply iota3_intersecting | apply iota3_no_sunflower ].
Qed.

(** The bound is not vacuous either: it is *below* the trivial ceiling.
    Without it, an intersecting 3-uniform sunflower-free family on a
    ground set of [n] points has no bound better than [C(n,3)], which
    grows without limit; the link bound caps it at 18 whatever the
    ground set. Checked against the largest ground set the search
    reaches. *)

Example iota_bound_beats_the_ground_set :
  forall F : Family,
    Uniform 3 F -> Distinct F -> Intersecting F ->
    ~ ContainsKSunflower 3 F ->
    length F <= 18.
Proof. exact iota_three_at_most_eighteen. Qed.

(** *** Does [star] mean "the members through this point"?

    [Intersecting.star] is [filter (memb x)], which is what the
    pigeonhole counts, so the risk is not that it is wrong but that the
    theorem is stated against the wrong counter. Two checks: the
    membership characterisation, and that the star and the *link* at a
    point have the same size.

    The second is the one worth having. The two bounds on [iota] in this
    development go opposite ways and use opposite devices — the upper
    bound [iota(b) <= b*g(b-1)] counts the link at a popular point, the
    lower bound [g(b) <= 2b*iota(b)] counts the star at one — and if
    those two counts disagreed, one of the theorems would be about a
    quantity nobody named. *)

Theorem star_correct :
  forall x F A, In A (star x F) <-> In A F /\ In x A.
Proof.
  intros x F A; unfold star; rewrite filter_In; split; intros [Ha Hb].
  - split; [exact Ha | apply memb_true_iff; exact Hb].
  - split; [exact Ha | apply memb_true_iff; exact Hb].
Qed.

Theorem star_and_link_agree :
  forall x F, length (star x F) = length (link [x] F).
Proof.
  intros x F; rewrite length_link; unfold deg, star.
  f_equal; apply filter_ext_eq; intros B; symmetry; apply containsb_singleton.
Qed.

(** *** Is the factor [2b] in the star bound decoration?

    No: it is *attained* at [b = 1]. Two disjoint singletons are
    sunflower-free (a family of two members contains no 3-sunflower for
    the silliest reason), so [g(1) = 2]; and an intersecting 1-uniform
    distinct family has one member, so [iota(1) = 1]. Hence
    [g(1) = 2 = 2*1*iota(1)] with equality, and no constant below 2
    works at [b = 1].

    That does not say [2b] is sharp for every [b] — the exhaustive
    sample in [rust/tests/iota_sandwich.rs] reaches only 3 of the 4
    available at [b = 2] and 2.75 of the 6 at [b = 3]. It says the
    factor is not an artefact of a lazy estimate at the one place both
    ends are known exactly. *)

Lemma zero_uniform_at_most_one :
  forall G : Family, Uniform 0 G -> Distinct G -> length G <= 1.
Proof.
  intros G HU HD.
  destruct G as [|A [|B G'']]; simpl; [lia | lia |].
  exfalso.
  unfold Uniform in HU.
  inversion HU as [|? ? HUA HU']; subst.
  inversion HU' as [|? ? HUB HU'']; subst.
  destruct HUA as [HAlen _]; destruct HUB as [HBlen _].
  destruct A as [|a A0]; [|simpl in HAlen; lia].
  destruct B as [|b B0]; [|simpl in HBlen; lia].
  inversion HD as [|? ? Hni _]; subst.
  apply (Hni [] (or_introl eq_refl)); apply SetEq_refl.
Qed.

Theorem iota_one_is_one : IotaAtMost 1 1.
Proof.
  intros H HU HD HI Hno.
  apply (intersecting_link_bound 1 1 H); try assumption; [lia|].
  intros G HUG HDG _; simpl in HUG.
  exact (@zero_uniform_at_most_one G HUG HDG).
Qed.

Theorem the_factor_two_b_is_attained :
  LowerBound 1 3 2 /\ IotaAtMost 1 1 /\ ~ GAtMost 1 1.
Proof.
  assert (HL : LowerBound 1 3 2).
  { exists [[0]; [1]].
    split; [apply uniformb_correct; vm_compute; reflexivity|].
    split; [apply distinctb_correct; vm_compute; reflexivity|].
    (* [simpl; lia] rather than [reflexivity]: the mutation
       [lowerbound-at-least] turns this equation into [>=], and a proof
       sensitive to which one it is would kill the development's one
       genuine mutation survivor without saying anything. *)
    split; [simpl; lia|].
    apply (@no_k_sunflower_short_family [[0]; [1]] 3); simpl; lia. }
  split; [exact HL|]; split; [exact iota_one_is_one|].
  intros Hg; destruct HL as [F [HU [HD [Hlen Hno]]]].
  pose proof (Hg F HU HD Hno); lia.
Qed.

(** *** Is [1 <= b] in the star bound load-bearing?

    Yes, and the counterexample is the smallest one there is. At [b = 0]
    the family [{∅}] is 0-uniform, distinct and sunflower-free with one
    member, while *no* 0-uniform family is intersecting at all — [∅] is
    disjoint from itself — so [iota(0) = 0] and the bound [2*0*0] would
    read [0 >= 1].

    The mechanism is exactly the step the hypothesis licenses: the proof
    needs every member nonempty before it can take a maximal disjoint
    subfamily, and at [b = 0] the empty set is disjoint from everything
    including itself, so the greedy cover never starts. *)

Theorem iota_zero_is_zero : IotaAtMost 0 0.
Proof.
  intros H HU HD HI Hno.
  destruct H as [|A H']; simpl; [lia|].
  exfalso.
  unfold Uniform in HU; inversion HU as [|? ? HUA _]; subst.
  destruct HUA as [HAlen _].
  destruct A as [|a A0]; [|simpl in HAlen; lia].
  apply (HI [] [] (or_introl eq_refl) (or_introl eq_refl)).
  intros y Hy; inversion Hy.
Qed.

Theorem positive_uniformity_is_needed_in_the_star_bound :
  Uniform 0 [[]] /\ Distinct [[]] /\ ~ ContainsKSunflower 3 [[]]
  /\ IotaAtMost 0 0 /\ 2 * 0 * 0 < length ([[]] : Family).
Proof.
  repeat split.
  - apply uniformb_correct; vm_compute; reflexivity.
  - apply distinctb_correct; vm_compute; reflexivity.
  - apply (@no_k_sunflower_short_family [[]] 3); simpl; lia.
  - exact iota_zero_is_zero.
  - simpl; lia.
Qed.

(** *** Does [IotaAtMost] pin anything, or is it satisfiable at every [N]?

    Both ends are proved, so the truth boundary of [IotaAtMost 3 N] is
    trapped: false at 9, true at 18. The measured value is 10, which is
    inside that window and is the only thing the search is being trusted
    for. A definition that was accidentally vacuous — satisfied at every
    [N] — would fail the first half. *)

Theorem iota_three_between_ten_and_eighteen :
  ~ IotaAtMost 3 9 /\ IotaAtMost 3 18.
Proof.
  split.
  - intros Hi.
    pose proof (Hi iota3 iota3_uniform iota3_distinct iota3_intersecting
                  iota3_no_sunflower) as Hle.
    vm_compute in Hle; lia.
  - intros H HU HD HI Hno; exact (iota_three_at_most_eighteen H HU HD HI Hno).
Qed.

(** *** Does the star bound contradict anything already proved?

    [IotaRate.g_three_at_most_108] caps every sunflower-free 3-uniform
    family at 108 members. Every lower bound the development proves at
    uniformity 3 must sit below it, and the check is the bound *applied*
    to the lower bound's own witness — so a contradictory pair would
    make this line a derivation of [False] rather than a restatement of
    two numbers. *)

Corollary bounds_coherent_star_bound :
  forall m, LowerBound 3 3 m -> m <= 108.
Proof.
  intros m [F [HU [HD [Hlen Hno]]]].
  (* [pose ...; lia], not [rewrite <- Hlen]: see
     [IotaRate.every_construction_is_within_2b_of_iota]. *)
  pose proof (g_three_at_most_108 F HU HD Hno) as Hle; lia.
Qed.

Corollary bounds_coherent_iota_sandwich : 20 <= 108 /\ 15 <= 108.
Proof.
  split; apply bounds_coherent_star_bound;
    [ exact lower_bound_3_3_20
    | exact (@LowerBound_antitone 3 3 20 15 lower_bound_3_3_20 ltac:(lia)) ].
Qed.

(** *** Is the equivalence with the conjecture really an equivalence?

    Both sides are open, so neither can be witnessed. What *can* be
    checked is that the two directions are not the same statement read
    twice: the forward one is a bound on intersecting families producing
    an [UpperBound], the backward one is an [UpperBound] producing a
    bound on intersecting families. Composing them in either order is
    the identity on the proposition, which is what
    [conjecture_k_3_iff_iota_exponential] asserts — recorded here
    against a named specification so a later weakening of either
    direction shows up as a moved statement. *)

Definition IotaEquivalence : Prop :=
  sunflower_conjecture_k_3 <-> IotaExponential.

Theorem the_iota_route_proves_the_equivalence : IotaEquivalence.
Proof. exact conjecture_k_3_iff_iota_exponential. Qed.

(** *** Is the detector's converse the converse?

    [F23.sunflower3b] is now proved sound *and* complete, so it decides
    [ContainsKSunflower 3]. Two checks that the pair says what it should:
    the decision agrees with the boolean on a family that has a sunflower
    and on one that does not. [two_triangles] is the interesting side —
    it is the six-member family behind [f(2,3) = 7], and if the detector
    accepted it the value would be wrong. *)

Theorem the_detector_decides :
  sunflower3b two_triangles = false
  /\ ~ ContainsKSunflower 3 two_triangles
  /\ sunflower3b [[0]; [1]; [2]] = true
  /\ ContainsKSunflower 3 [[0]; [1]; [2]].
Proof.
  split; [vm_compute; reflexivity|].
  split; [exact two_triangles_no_sunflower|].
  split; [vm_compute; reflexivity|].
  apply sunflower3b_complete; vm_compute; reflexivity.
Qed.

(** *** Does the double count count the right thing?

    [IotaGround.degsum] and [IotaGround.sizesum] are two sums over the
    same incidence table, and the theorem that they agree is what turns
    the link bound into a ground-set bound. The risk is not that the
    identity is false — it is proved — but that either side is summing
    something other than what its name says. So: evaluate both on a
    family whose incidences can be counted by hand.

    [two_triangles] has six 2-sets on six points, every point in exactly
    two of them. Degrees sum to 12; sizes sum to 12; and both equal
    [2 * 6]. A [degsum] that had transposed its filters, or a [sizesum]
    that counted members rather than points, would miss. *)

Example the_double_count_is_the_incidence_count :
  degsum [0;1;2;3;4;5] two_triangles = 12
  /\ sizesum [0;1;2;3;4;5] two_triangles = 12
  /\ degsum [0;1;2;3;4;5] two_triangles = 2 * length two_triangles.
Proof.
  split; [vm_compute; reflexivity|].
  split; vm_compute; reflexivity.
Qed.

(** *** Is the ground-set link bound tight, or is it an estimate?

    Tight, at the one place the development can check it in the kernel:
    [two_triangles] is 2-uniform on six points with [N(1,5) = 2], and
    [2 * 6 = 6 * 2] exactly. Equality forces the family to be regular and
    every link to be extremal, which is what the measured rows show at
    [(2,3)], [(3,6)], [(4,8)] and [(4,9)] as well
    ([rust/examples/iota_ground.rs]).

    So the bound is not a lazy estimate that happens to be provable — at
    uniformity 2 it is an identity, and the slack at larger ground sets
    is the honest content of the inequality. *)

Example the_ground_bound_is_attained :
  2 * length two_triangles <= length [0;1;2;3;4;5] * 2
  /\ 2 * length two_triangles = length [0;1;2;3;4;5] * 2.
Proof.
  split; vm_compute; (reflexivity || lia).
Qed.

(** *** Does the intersecting ground hypothesis differ from the general one?

    Both settle [k = 3], and [IotaGround.both_ground_hypotheses_settle_k3]
    puts them side by side so the difference is visible as a statement
    rather than as prose. Neither implies the other — [GroundBounded]
    demands the small ground set of *every* sunflower-free family and
    [IotaGroundBounded] only of intersecting ones, so the first is
    stronger there; but the first also produces a family of the same size
    and the second is free to produce any equally large sunflower-free
    one, so it is weaker there. What separates them is not logic, it is
    that the measurements support one and not the other.

    Recorded against a named specification, so a later weakening of
    either shows up as a moved statement. *)

Definition GroundHypotheses : Prop :=
  NaslundSawinBound ->
  forall c, 1 <= c ->
    (GroundBounded c -> forall m j, 1 <= m -> LowerBound m 3 j
                                    -> j <= (27 ^ (c + 1)) ^ m)
    /\ (IotaGroundBounded c -> sunflower_conjecture_k_3).

Theorem the_two_ground_hypotheses_are_both_sufficient : GroundHypotheses.
Proof. exact both_ground_hypotheses_settle_k3. Qed.

(** *** Is [N(3,g) <= 2g] any use, or is it above the trivial ceiling?

    Below it, and by a lot. On ten points the trivial bound is
    [C(10,3) = 120] and Erdős–Rado gives 48 at uniformity 3; the link
    count gives 20. It is still above the measured 14, and it does not
    decide whether the row plateaus — which is the question
    [SliceRank.v] actually needs — but it is the first proved cap on
    that row. *)

Example the_ground_cap_beats_erdos_rado_at_ten :
  forall (U : list nat) (F : Family),
    NoDup U -> length U <= 10 ->
    Uniform 3 F -> Distinct F -> Grounded F U ->
    ~ ContainsKSunflower 3 F ->
    length F <= 20 /\ 20 < 48.
Proof.
  intros U F HndU Hu HU HD HG Hno.
  split; [exact (n_three_ten_at_most_twenty U F HndU Hu HU HD HG Hno) | lia].
Qed.

(** ** Compression: does [LeftCompressed] mean "the shift does not move
       it"?

    [Compression.LeftCompressed] is stated as a closure property of the
    family; [Compression.shift_family] is the operation itself. Nothing
    in the kernel forces the two to be about the same thing, and the
    whole file turns on their agreeing. They do, in both directions.

    The [i < j] is not decoration: an upward shift is not constrained by
    [LeftCompressed] and really can move a compressed family, which is
    why the equivalence is stated for [i < j] and no wider. *)

Lemma map_id_of_pointwise :
  forall (f : list nat -> list nat) (F : Family),
    (forall A, In A F -> f A = A) -> map f F = F.
Proof.
  intros f F; induction F as [|A F IH]; simpl; intro H; [reflexivity|].
  rewrite (H A (or_introl eq_refl)); f_equal.
  apply IH; intros B HB; apply H; right; exact HB.
Qed.

Lemma map_id_on_members :
  forall (f : list nat -> list nat) (F : Family),
    map f F = F -> forall A, In A F -> f A = A.
Proof.
  intros f F; induction F as [|A F IH]; simpl; intros Hmap B HB; [contradiction|].
  injection Hmap as Hhead Htail.
  destruct HB as [E | HB]; [subst B; exact Hhead | apply IH; assumption].
Qed.

Theorem compressed_iff_the_shift_does_not_move_it :
  forall F,
    LeftCompressed F <-> (forall i j, i < j -> shift_family i j F = F).
Proof.
  intro F; split.
  - intros Hlc i j Hij; unfold shift_family.
    assert (Hid : forall A, In A F -> shift_one i j F A = A).
    { intros A HA; unfold shift_one.
      destruct (memb j A && negb (memb i A)
                && negb (setmemb (shift_member i j A) F)) eqn:Eg;
        [| reflexivity].
      exfalso.
      apply Bool.andb_true_iff in Eg as [Eg Eimg].
      apply Bool.andb_true_iff in Eg as [Ej Ei].
      apply Bool.negb_true_iff in Eimg.
      assert (HjA : In j A) by (apply memb_true_iff; exact Ej).
      assert (HiA : ~ In i A)
        by (apply memb_false_iff, Bool.negb_true_iff; exact Ei).
      destruct (Hlc A i j HA Hij HjA HiA) as [B [HB Hseq]].
      unfold setmemb in Eimg.
      assert (Hex : existsb (fun C => seteqb (shift_member i j A) C) F = true).
      { apply existsb_exists; exists B; split;
          [exact HB | apply seteqb_correct, SetEq_sym; exact Hseq]. }
      congruence. }
    apply map_id_of_pointwise; exact Hid.
  - intros Hfix A i j HA Hij HjA HiA.
    specialize (Hfix i j Hij); unfold shift_family in Hfix.
    assert (Hone : shift_one i j F A = A)
      by (eapply map_id_on_members; [exact Hfix | exact HA]).
    unfold shift_one in Hone.
    destruct (memb j A && negb (memb i A)
              && negb (setmemb (shift_member i j A) F)) eqn:Eg.
    + (* The guard fired, so A moved to a set containing i — but it did
         not move, and i is not in A. *)
      exfalso; apply HiA; rewrite <- Hone; unfold shift_member; left; reflexivity.
    + apply Bool.andb_false_iff in Eg as [Eg | Eimg].
      * apply Bool.andb_false_iff in Eg as [Ej | Ei].
        -- rewrite (proj2 (memb_true_iff j A) HjA) in Ej; discriminate.
        -- apply Bool.negb_false_iff, memb_true_iff in Ei; contradiction.
      * apply Bool.negb_false_iff in Eimg; unfold setmemb in Eimg.
        apply existsb_exists in Eimg as [B [HB Hb]].
        exists B; split; [exact HB | apply SetEq_sym, seteqb_correct; exact Hb].
Qed.

(** *** And it is not vacuous in either direction

    [two_triangles] attains [f(2,3) - 1 = 6] and a compressed family at
    uniformity 2 has at most three members, so it cannot be compressed —
    derived from [compressed_bound] rather than checked. The shift that
    moves it is then exhibited outright, so the negative statement has a
    positive witness behind it. *)

Theorem two_triangles_is_not_compressed : ~ LeftCompressed two_triangles.
Proof.
  intro Hlc.
  assert (Hb : length two_triangles <= 2 + 1).
  { apply compressed_bound with (m := 2);
      [lia | exact Hlc | exact two_triangles_uniform
       | exact two_triangles_distinct | exact two_triangles_no_sunflower]. }
  simpl in Hb; lia.
Qed.

Theorem the_shift_really_moves_two_triangles :
  shift_family 0 3 two_triangles <> two_triangles.
Proof. vm_compute; intro H; discriminate. Qed.

(** *** The obstruction, evaluated

    The abstract argument produces three sets of the form
    [{0,...,m-2} ∪ {t}] and calls them a sunflower. At [m = 3] those are
    [{0,1,2}], [{0,1,3}] and [{0,1,4}], and the reflective detector
    agrees — so [three_chains_are_a_sunflower] is about the same objects
    the search would have found. *)

Theorem the_chain_obstruction_is_real :
  ContainsKSunflower 3 [chain 3 2; chain 3 3; chain 3 4]
  /\ [chain 3 2; chain 3 3; chain 3 4] = [[2;0;1]; [3;0;1]; [4;0;1]].
Proof.
  split; [apply sunflower3b_complete | ]; vm_compute; reflexivity.
Qed.

(** *** The collapse, in numbers

    What compression permits against what the development proves exists,
    at the two uniformities where both are known. Not a constant factor:
    3 against 6 at uniformity 2, and 4 against 20 at uniformity 3, where
    the compressed bound stays linear and the truth is exponential. *)

Theorem compression_collapses_the_problem :
  (forall F, LeftCompressed F -> Uniform 2 F -> Distinct F ->
             ~ ContainsKSunflower 3 F -> length F <= 3)
  /\ LowerBound 2 3 6
  /\ (forall F, LeftCompressed F -> Uniform 3 F -> Distinct F ->
                ~ ContainsKSunflower 3 F -> length F <= 4)
  /\ LowerBound 3 3 20.
Proof.
  split; [| split; [exact f_2_3_lower | split; [| exact lower_bound_3_3_20]]].
  - intros F Hlc Hun Hd Hno.
    assert (H : length F <= 2 + 1)
      by (apply compressed_bound with (m := 2); assumption || lia).
    lia.
  - intros F Hlc Hun Hd Hno.
    assert (H : length F <= 3 + 1)
      by (apply compressed_bound with (m := 3); assumption || lia).
    lia.
Qed.

(** ** The cone, and the definitions [coq/Product.v] adds

    Four questions, in the shape the rest of this file uses.

    - Is the freshness hypothesis in [Product.cone] load-bearing, or
      would any point do? ([cone_needs_freshness].)
    - Is [Product.IotaAtLeast] the complement of [IotaRate.IotaAtMost],
      or are the two about different quantities?
      ([iota_four_between_27_and_192].)
    - Does the new lower bound at uniformity 4 contradict any upper bound
      the development proves? ([bounds_coherent_cone].)
    - And the correction: [IotaGround.both_ground_hypotheses_settle_k3]
      says "neither implies the other".
      ([the_ground_hypotheses_are_not_independent_after_all].) *)

(** *** The freshness hypothesis is the theorem

    [Product.cone p F] prepends [p] to every member. If [p] is already in
    a member, the image repeats a point, so it is not a set of the right
    size at all — and the mechanism is exactly the step [Fresh] licenses.
    The triangle coned at one of its own points is the minimal witness:
    three 2-sets, and two of the three images fail [UniformSet 3]. *)

Example cone_needs_freshness :
  ~ Uniform 3 (Product.cone 0 triangle)
  /\ Uniform 3 (Product.cone 3 triangle)
  /\ Product.Fresh 3 triangle
  /\ ~ Product.Fresh 0 triangle.
Proof.
  split.
  { intro HU.
    unfold Uniform in HU; rewrite Forall_forall in HU.
    assert (Hin : In [0; 0; 1] (Product.cone 0 triangle))
      by (vm_compute; tauto).
    destruct (HU _ Hin) as [_ Hnd].
    inversion Hnd as [|? ? Hni _]; subst; apply Hni; left; reflexivity. }
  assert (Hfr : Product.Fresh 3 triangle).
  { apply (Product.Fresh_of_Grounded 3 triangle (seq 0 3)).
    - unfold Grounded.
      apply (proj1 (groundedb_correct triangle (seq 0 3))).
      vm_compute; reflexivity.
    - rewrite in_seq; lia. }
  split; [exact (Product.cone_Uniform 2 3 triangle Hfr triangle_uniform)|].
  split; [exact Hfr|].
  intro H.
  apply (H [0; 1] ltac:(vm_compute; tauto)); left; reflexivity.
Qed.

(** *** The truth boundary for [iota(4)], in the kernel

    The analogue of [iota_three_between_ten_and_eighteen] one uniformity
    up. The lower end is [Product.iota_four_at_least_27], the exhaustive
    maximum at nine points; the upper end is
    [Intersecting.intersecting_link_bound] fed the Erdős–Rado value
    [g(3) <= 48], which is what the development proves without any search.

    The gap is enormous — 27 against 192 — and that is the honest state of
    knowledge. What the pair rules out is a definition that had become
    accidentally vacuous: the first half would fail. *)

Theorem iota_four_between_27_and_192 :
  ~ IotaAtMost 4 26 /\ IotaAtMost 4 192.
Proof.
  split; [exact Product.not_iota_four_at_most_26|].
  intros H HU HD HI Hno.
  replace 192 with (4 * 48) by reflexivity.
  apply (intersecting_link_bound 4 48 H ltac:(lia) HU HD HI Hno).
  intros G HUG HDG HnoG; simpl in HUG.
  destruct (le_lt_dec (length G) 48) as [Hle | Hlt]; [exact Hle | exfalso].
  assert (Her : er_upper_bound 3 3 = 49)
    by (unfold er_upper_bound; vm_compute; reflexivity).
  apply HnoG.
  apply (@erdos_rado_counted 3 3 ltac:(lia) ltac:(lia));
    [exact HUG | exact HDG | rewrite Her; lia].
Qed.

(** *** The new value at uniformity 4 fits under every proved upper bound

    Derived from the two formal statements, so a contradictory pair would
    make this a proof of [False]. [Product.lower_bound_4_3_54] against
    Erdős–Rado's [er_upper_bound 4 3 = 385]. *)

Corollary bounds_coherent_cone : 54 < er_upper_bound 4 3.
Proof.
  apply (lower_lt_upper (n := 4) (k := 3));
    [exact Product.lower_bound_4_3_54
    | apply erdos_rado_counted; lia].
Qed.

(** And it strictly improves what the development had: 54 against the
    direct sum's 36, so it refutes an [UpperBound] the previous best did
    not. *)

Corollary the_cone_route_beats_the_direct_sum_at_four :
  LowerBound 4 3 36 /\ LowerBound 4 3 54 /\ ~ UpperBound 4 3 54 /\ 36 < 54.
Proof.
  split; [exact (lower_bound_f_n_3 2)|].
  split; [exact Product.lower_bound_4_3_54|].
  split; [exact Product.no_upper_bound_4_3_54 | lia].
Qed.

(** *** The correction, against a named specification

    [IotaGround.both_ground_hypotheses_settle_k3] puts the two
    ground-set hypotheses side by side with the remark that "neither
    implies the other". One direction is immediate and the cone gives the
    other up to the constant, so the remark is withdrawn. Both halves are
    recorded here so the retraction is a theorem rather than an edited
    comment. *)

Theorem the_ground_hypotheses_are_not_independent_after_all :
  forall c,
    (GroundBounded c -> IotaGroundBounded c)
    /\ (IotaGroundBounded c ->
        forall m j, 1 <= m -> LowerBound m 3 j -> j <= (2 ^ c) ^ (m + 1)).
Proof. exact Product.the_two_ground_hypotheses_are_not_independent. Qed.

(** *** The sharp reformulation: is the shift a reindexing, and is the
    sharp constant forced?

    [Sharp.conjecture_k_3_iff_iota_shifted] restates the conjecture at
    [k = 3] as [iota(b) <= C^(b-1)] rather than [iota(b) <= C^b]. Two
    questions that has to answer.

    First, does the shift *change* anything, or is [C^(b-1)] just [C^b]
    with the constant renamed? It changes it: at [C = 3] the shifted
    statement is **false**, refuted by the witnessed [iota(3) >= 10]
    against [3^2 = 9], while the unshifted one at [C = 3] is not refuted
    by that family at all ([10 <= 27]). So the base in the shifted form is
    at least 4 — which is exactly the base
    [Sharp.sharp_gives_base_four] produces from the sharp bound, and it
    is the finitistic content of "[L] is above 3, and [sqrt(10) = 3.162]
    is the value conjectured".

    Second, would a definition that had become accidentally vacuous be
    caught? It would: a vacuously true [IotaAtMost] would make this
    theorem unprovable. *)

Theorem the_shifted_bound_at_three_is_false : ~ Sharp.IotaShiftedAt 3.
Proof.
  intros H.
  pose proof (Product.iota_at_least_le_at_most 3 10 (3 ^ (3 - 1))
                Product.iota_three_at_least_ten (H 3 ltac:(lia))) as Hle.
  vm_compute in Hle; lia.
Qed.

(** *** The sharp conjecture fits under the development's own bounds

    [Sharp.AHSOptimal] implies [f(3,3) <= 32]
    ([Sharp.sharp_beats_erdos_rado_at_three]), and the development proves
    [f(3,3) >= 21] ([Intersecting.lower_bound_3_3_20]). This is that pair
    fed to [lower_lt_upper], so if the sharp bound contradicted a lower
    bound already proved here, this line would be a proof of [False] and
    would fail to be provable in the form written. It is the
    [bounds_coherent_*] pattern applied to a hypothesis rather than to a
    theorem. *)

Corollary bounds_coherent_sharp : Sharp.AHSOptimal -> 20 < 32.
Proof.
  intros Hs.
  apply (lower_lt_upper (n := 3) (k := 3));
    [exact lower_bound_3_3_20
    | exact (proj1 (Sharp.sharp_beats_erdos_rado_at_three Hs))].
Qed.

(** *** And it says strictly more than the development knows

    A hypothesis that only re-derived what is already proved would be
    worth nothing. [Audit.iota_four_between_27_and_192] traps [iota(4)]
    in [[27, 192]] with what is proved; the sharp bound closes that to
    [[27, 31]]. Both ends are kept in the statement so the narrowing is
    visible rather than asserted. *)

Theorem the_sharp_bound_narrows_iota_four :
  Sharp.AHSOptimal ->
  ~ IotaAtMost 4 26 /\ IotaAtMost 4 192 /\ IotaAtMost 4 31 /\ 26 < 31 < 192.
Proof.
  intros Hs.
  split; [exact Product.not_iota_four_at_most_26|].
  split; [exact (proj2 iota_four_between_27_and_192)|].
  split; [exact (Sharp.sharp_forces_iota_four_at_most_31 Hs) | lia].
Qed.
