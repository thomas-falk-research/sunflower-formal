(** * IotaRate.v -- iota and g have the same exponential rate.

    Write [g(b) = f(b,3) - 1] for the largest 3-sunflower-free
    [b]-uniform family and

    >  iota(b)  =  the largest *intersecting* 3-sunflower-free
    >              b-uniform family.

    Two theorems bracket one by the other:

    >  2 * iota(b)  <=  g(b)  <=  2b * iota(b).

    The left half is [Intersecting.doubling_lower_bound] — two disjoint
    copies of an intersecting sunflower-free family are sunflower-free.
    The right half is [Intersecting.sunflower_free_star_bound] — a
    sunflower-free family has no three pairwise disjoint members, so a
    maximal disjoint subfamily spans at most [2b] points and meets
    everything, and the star at the most popular of them is an
    intersecting sunflower-free family of at least [|F|/(2b)] members.

    ** What the sandwich buys

    The factor between the two ends is [b], which is subexponential. So
    a bound [iota(b) <= C^b] gives [g(b) <= 2b*C^b <= (2C)^b], and a
    bound [g(b) <= c^b] gives [iota(b) <= c^b] for nothing. That is
    [iota_exponential_iff], and its consequence is the point of this
    file:

    >  the sunflower conjecture at k = 3 is *equivalent* to
    >  "iota(b) <= C^b for some constant C"
    >  ([conjecture_k_3_iff_iota_exponential]).

    An equivalence, not an implication: a bound on intersecting families
    is not merely sufficient, it is necessary. So the whole problem at
    [k = 3] is a question about *intersecting* families — where the
    extremal set theory toolbox (Erdős–Ko–Rado, Hilton–Milner, Frankl)
    is at its strongest.

    ** Correction: the intersecting side of the spread framework is not
       untouched

    A previous revision of this header added "and where, as far as we
    have found, it has never been pointed". **Withdrawn.** [ALWZ20] §4.2
    is titled *Intersecting set systems* and its Theorem 4.2 reads, on
    the rendered page 13: *"If `F` is an intersecting `w`-uniform set
    system, and for all `T`, `|F_T| <= κ^{-|T|}|F|`, then
    `κ = O(log w)`."* — with, on the same page, *"An example from [16]
    shows that for `κ = Ω(log w/ log log w)`, there are intersecting
    `κ`-spread `w`-uniform set systems, so the bound in Theorem 4.2 is
    close to tight."* So intersecting families inside the spread
    framework are a studied object with a near-sharp answer.

    What this does *not* do is displace anything below. ALWZ's Theorem
    4.2 is about intersecting **spread** families; [IotaAtMost] is about
    intersecting **sunflower-free** families, and neither hypothesis
    implies the other. The sandwich and the equivalence stand. What
    changes is the claim that nobody had looked, which was false, and
    the elementary version of ALWZ's theorem is recorded below as a
    theorem rather than left as a citation — see
    [intersecting_not_spread_above_uniformity].

    The equivalence is unconditional. Getting from a bound on
    sunflower-free families back to [UpperBound] needs
    [ContainsKSunflower 3] to be decidable, which
    [F23.contains_3_sunflower_dec] now proves — the detector
    [F23.sunflower3b] was already known to accept every sunflower, and
    the converse is [F23.sunflower3b_complete].

    ** What it does not buy

    Nothing numerical. The proved bound on [iota(3)] is 18
    ([Intersecting.iota_three_at_most_eighteen]), so the sandwich gives
    [g(3) <= 108] against Erdős–Rado's 48. Even at the *measured*
    [iota(3) = 10] it gives 60, still above 48. The content here is
    structural: it says which quantity to compute, not a better value
    for any particular one.

    ** The measured rates

    The rate the Abbott–Hanson–Sauer substitution extracts from [iota]
    is [iota(b)^(1/(b-1))] per point. Exhaustively
    ([rust/examples/iota_scan.rs], [rust/examples/g10.rs]):

    >  b = 2   iota = 3            rate 3.0000
    >  b = 3   iota = 10           rate 3.1623   <- the 1972 constant
    >  b = 4   iota = 27 (g <= 9)  rate 3.0000
    >  b = 4   iota < 32 (g = 10)  rate < 3.1414

    Flat, not growing, over every value that has been decided. Read
    through this file that is mild evidence *for* the conjecture at
    [k = 3], with [c(3)] somewhere near 3.2 — and evidence that the 1972
    construction is close to optimal, since by the sandwich no
    construction at uniformity [b] can exceed [2b * iota(b)].

    Zero axioms, zero admits. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower LowerBound Conjecture F23
     Intersecting Pigeonhole Spread.
Import ListNotations.

(** ** The elementary form of ALWZ's Theorem 4.2

    An intersecting family cannot be spread beyond its own uniformity.
    Every member meets a fixed member [A], so pigeonhole on [A]'s [m]
    points gives a point of degree at least [|F|/m], while
    [Spread F r] caps every degree at [|F|/r]. Hence [r ≤ m].

    That is the trivial bound; ALWZ's Theorem 4.2 sharpens [m] to
    [O(log m)] and their §4.2 shows that is close to best possible. The
    point of proving the trivial version here is that it is the shape of
    the published statement, checked by the kernel, and it makes precise
    what the header above withdraws: this is a studied question, and the
    elementary answer costs fifteen lines. *)

Theorem intersecting_not_spread_above_uniformity :
  forall m (F : Family) r,
    Uniform m F -> Intersecting F -> F <> [] -> m < r -> ~ Spread F r.
Proof.
  intros m F r HU HI Hne Hmr Hspread.
  destruct F as [|A0 F']; [contradiction|].
  set (FF := A0 :: F').
  assert (HA0 : In A0 FF) by (left; reflexivity).
  unfold Uniform in HU; rewrite Forall_forall in HU.
  destruct (HU A0 HA0) as [HA0len _].
  (* every member meets [A0] *)
  assert (Hcov : forall B, In B FF -> exists x, In x B /\ In x A0).
  { intros B HB.
    destruct (disjointb B A0) eqn:E.
    - exfalso. apply (HI B A0 HB HA0). apply disjointb_correct; exact E.
    - apply disjointb_false_iff; exact E. }
  assert (Hm1 : 1 <= m).
  { destruct m as [|m']; [| lia]. exfalso.
    destruct (Hcov A0 HA0) as [x [Hx _]].
    destruct A0 as [|a A1]; [inversion Hx | simpl in HA0len; lia]. }
  assert (HFpos : 1 <= length FF) by (simpl; lia).
  set (K := (length FF - 1) / m).
  assert (Hmne : m <> 0) by lia.
  assert (Hpig : length FF > length A0 * K).
  { pose proof (Nat.mul_div_le (length FF - 1) m Hmne) as Hd.
    unfold K; rewrite HA0len; lia. }
  destruct (pigeonhole_family FF A0 K Hcov Hpig) as [x [_ Hcount]].
  assert (Hdeg : K + 1 <= deg [x] FF).
  { rewrite deg_single; lia. }
  assert (Hup : r * deg [x] FF <= length FF).
  { pose proof (Hspread [x] (NoDup_cons x (in_nil (a := x)) (NoDup_nil nat))) as H.
    simpl in H; rewrite Nat.mul_1_r in H; exact H. }
  assert (Hlow : length FF <= m * (K + 1)).
  { pose proof (Nat.div_mod_eq (length FF - 1) m) as Hdm.
    pose proof (Nat.mod_upper_bound (length FF - 1) m Hmne) as Hub.
    unfold K; lia. }
  nia.
Qed.

(** ** The two extremal quantities, as bounds

    Neither [g] nor [iota] is a function in this development — the
    extremal values are not known — so both appear the way
    [Intersecting.intersecting_link_bound] already uses them: as a
    number carried with the statement that it bounds every family of the
    relevant kind. [IotaAtMost b N] reads "iota(b) <= N" and
    [GAtMost b M] reads "g(b) <= M". *)

Definition IotaAtMost (b N : nat) : Prop :=
  forall H : Family,
    Uniform b H -> Distinct H -> Intersecting H ->
    ~ ContainsKSunflower 3 H -> length H <= N.

Definition GAtMost (b M : nat) : Prop :=
  forall F : Family,
    Uniform b F -> Distinct F -> ~ ContainsKSunflower 3 F -> length F <= M.

(** ** The two halves

    [iota_le_g] is the trivial one and is stated for symmetry: an
    intersecting sunflower-free family *is* a sunflower-free family, so
    any bound on the second bounds the first. All the content is in the
    other direction. *)

Theorem iota_le_g : forall b M, GAtMost b M -> IotaAtMost b M.
Proof. intros b M Hg H HU HD _ Hno; exact (Hg H HU HD Hno). Qed.

Theorem g_le_iota_scaled :
  forall b N, 1 <= b -> IotaAtMost b N -> GAtMost b (2 * b * N).
Proof.
  intros b N Hb Hiota F HU HD Hno.
  exact (sunflower_free_star_bound b N F Hb HU HD Hno Hiota).
Qed.

(** ** The sandwich

    Both halves at once. The left needs a witness — a bound on [iota]
    says nothing about whether any family attains it — so the
    intersecting family is a hypothesis, and when it attains [N] the
    conclusion reads [2N <= g(b) <= 2bN]. *)

Theorem iota_g_sandwich :
  forall b N (H : Family),
    1 <= b ->
    Uniform b H -> Distinct H -> Intersecting H ->
    ~ ContainsKSunflower 3 H ->
    IotaAtMost b N ->
    LowerBound b 3 (2 * length H) /\ GAtMost b (2 * b * N).
Proof.
  intros b N H Hb HU HD HI Hno Hiota; split.
  - exact (doubling_lower_bound b H Hb HU HD HI Hno).
  - exact (g_le_iota_scaled b N Hb Hiota).
Qed.

(** Every lower-bound construction at uniformity [b], whatever it is, is
    within a factor [2b] of the doubling of the best intersecting
    family. This is the precise finitistic form of "no cleverer version
    of the 1972 substitution beats computing [iota] for larger [b]": the
    substitution is not being compared against other constructions here,
    it is being compared against the extremal function, and the gap is
    subexponential. *)

Theorem every_construction_is_within_2b_of_iota :
  forall b N m,
    1 <= b -> IotaAtMost b N -> LowerBound b 3 m -> m <= 2 * b * N.
Proof.
  intros b N m Hb Hiota [F [HU [HD [Hlen Hno]]]].
  (* [pose ...; lia] rather than [rewrite <- Hlen]: the mutation
     [lowerbound-at-least] turns [LowerBound]'s size equation into [>=],
     and a rewrite is sensitive to which one it is. That mutation is the
     development's one genuine survivor and killing it by accident says
     nothing about anything. *)
  pose proof (g_le_iota_scaled b N Hb Hiota F HU HD Hno) as Hle.
  lia.
Qed.

(** ** The arithmetic that makes the factor disappear

    [2b] is subexponential, and that is the whole reason the sandwich
    says anything about rates. Stated separately because it is exactly
    what a reader should check: [2b * C^b <= (2C)^b] is the step where
    the factor is absorbed into the base. *)

Lemma pow_two_pos : forall b, 1 <= 2 ^ b.
Proof. induction b as [|b IH]; simpl; lia. Qed.

Lemma two_b_le_pow_two : forall b, 1 <= b -> 2 * b <= 2 ^ b.
Proof.
  induction b as [|b IH]; intros Hb; [lia|].
  simpl (2 ^ S b).
  destruct (Nat.eq_dec b 0) as [E | Hne]; [subst b; simpl; lia|].
  assert (Hprev : 2 * b <= 2 ^ b) by (apply IH; lia).
  assert (H2 : 2 <= 2 ^ b).
  { destruct b as [|b']; [lia|].
    simpl; pose proof (pow_two_pos b'); lia. }
  lia.
Qed.

Lemma scaled_power_absorbs :
  forall b C, 1 <= b -> 2 * b * C ^ b <= (2 * C) ^ b.
Proof.
  intros b C Hb.
  rewrite Nat.pow_mul_l.
  apply Nat.mul_le_mono_r, two_b_le_pow_two, Hb.
Qed.

(** ** Same exponential rate

    The two quantities admit exponential bounds at the same time, and
    the constant moves by a factor 2. That is what "[iota] and [g] have
    the same exponential rate" means finitistically: no statement about
    limits is needed, and none is made. *)

Definition IotaExponential : Prop :=
  exists C : nat, forall b, 1 <= b -> IotaAtMost b (C ^ b).

Definition GExponential : Prop :=
  exists c : nat, forall b, 1 <= b -> GAtMost b (c ^ b).

Theorem iota_exponential_iff : IotaExponential <-> GExponential.
Proof.
  split.
  - intros [C HC]; exists (2 * C); intros b Hb F HU HD Hno.
    pose proof (g_le_iota_scaled b (C ^ b) Hb (HC b Hb) F HU HD Hno) as Hle.
    pose proof (scaled_power_absorbs b C Hb) as Habs.
    lia.
  - intros [c Hc]; exists c; intros b Hb.
    exact (iota_le_g b (c ^ b) (Hc b Hb)).
Qed.

(** ** The equivalence with the conjecture

    [Conjecture.sunflower_conjecture_k_3] is stated with [UpperBound]:
    every family above the threshold *contains* a sunflower. [GAtMost]
    is its contrapositive shape: every sunflower-free family is below
    the threshold. Passing from the second to the first is the step that
    needs decidability, and [F23.upper_bound_of_sunflower_free_bound]
    supplies it. *)

Theorem conjecture_k_3_iff_g_exponential :
  sunflower_conjecture_k_3 <-> GExponential.
Proof.
  split.
  - intros [c Hc]; exists c; intros b Hb F HU HD Hno.
    destruct (le_lt_dec (length F) (c ^ b)) as [Hle | Hlt]; [exact Hle | exfalso].
    exact (Hno (Hc b Hb F HU HD ltac:(lia))).
  - intros [c Hc]; exists c; intros n Hn.
    apply upper_bound_of_sunflower_free_bound.
    exact (Hc n Hn).
Qed.

(** **The statement this file exists for.**

    The sunflower conjecture at [k = 3] — Erdős's $1000 case — is
    equivalent to an exponential bound on *intersecting* sunflower-free
    families. Not a sufficient condition: an equivalence. *)

Theorem conjecture_k_3_iff_iota_exponential :
  sunflower_conjecture_k_3 <-> IotaExponential.
Proof.
  rewrite conjecture_k_3_iff_g_exponential; symmetry; exact iota_exponential_iff.
Qed.

(** And spelled out in one direction, with the constant visible: a bound
    [iota(b) <= C^b] settles [k = 3] with [c(3) = 2C]. At the measured
    rates — [iota(b)^(1/(b-1))] flat around 3.0 to 3.16 — the value of
    [C] this predicts is a little above 3, so [c(3)] a little above 6.
    That is not sharp and is not meant to be; [DirectSum]'s lower bounds
    force [c(3) >= 3.162...] and nothing here closes that gap. *)

Corollary iota_bound_settles_k_3 :
  forall C,
    (forall b, 1 <= b -> IotaAtMost b (C ^ b)) ->
    forall n, 1 <= n -> UpperBound n 3 (S ((2 * C) ^ n)).
Proof.
  intros C HC.
  destruct (proj2 conjecture_k_3_iff_iota_exponential (ex_intro _ C HC)) as [c Hc].
  (* [c] is whatever the equivalence produced; re-derive at [2 * C]
     directly rather than relying on which constant that was. *)
  clear c Hc; intros n Hn.
  apply upper_bound_of_sunflower_free_bound; intros F HU HD Hno.
  pose proof (g_le_iota_scaled n (C ^ n) Hn (HC n Hn) F HU HD Hno) as Hle.
  pose proof (scaled_power_absorbs n C Hn) as Habs.
  lia.
Qed.

(** ** The sandwich at the values the development knows

    [Intersecting.iota_three_at_most_eighteen] is the only bound on
    [iota] proved here, and it is loose (18 against the measured 10).
    Both instantiations are recorded, the proved one and the measured
    one, so the distance between what is known and what is true stays
    visible.

    Neither improves on Erdős–Rado's [f(3,3) <= 49]. That is not a
    defect of the sandwich — it is the factor [2b] being paid at a
    uniformity where [b] is not yet small compared to anything. *)

Corollary g_three_at_most_108 : GAtMost 3 108.
Proof.
  replace 108 with (2 * 3 * 18) by reflexivity.
  apply g_le_iota_scaled; [lia|].
  intros H HU HD HI Hno; exact (iota_three_at_most_eighteen H HU HD HI Hno).
Qed.

Corollary g_three_at_most_60_if_iota_three_is_ten :
  IotaAtMost 3 10 -> GAtMost 3 60.
Proof.
  intros Hiota; replace 60 with (2 * 3 * 10) by reflexivity.
  apply g_le_iota_scaled; [lia | exact Hiota].
Qed.

(** The other end, unconditionally: [iota(3) >= 10] is witnessed by
    [Intersecting.iota3], so the sandwich at [b = 3] is
    [20 <= g(3) <= 108] with what is proved, and [20 <= g(3) <= 60] with
    what is measured. *)

Corollary iota_three_sandwich :
  LowerBound 3 3 20 /\ GAtMost 3 108.
Proof. split; [exact lower_bound_3_3_20 | exact g_three_at_most_108]. Qed.
