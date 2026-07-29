(** * SliceRank.v -- The polynomial method, and exactly what it is missing.

    Naslund and Sawin, in *Upper bounds for sunflower-free sets*, Forum
    of Mathematics Sigma 5 (2017), applied the slice-rank method — the
    machinery that settled cap set — to the sunflower problem and got a
    bound of the form [constant ^ n]:

    >  a 3-sunflower-free family of subsets of [[n]] has at most
    >  [3 (n+1) * C ^ n] members, with [C = 3 / 2^(2/3) < 1.89].

    That is a [constant ^ n] bound of exactly the shape the sunflower
    conjecture asks for, obtained by the only technique in the
    neighbourhood that has ever produced one. It does not settle the
    conjecture, and this file says precisely why.

    ** The mismatch, stated exactly

    Naslund–Sawin bounds a family by its **ground set**. The conjecture
    bounds a family by its **uniformity**. For families of [m]-sets the
    two coincide only if the ground set can be taken to be [O(m)], and
    nothing says it can.

    [ns_bounds_by_ground_set] is the bound specialised to uniform
    families — immediate, since a uniform family is in particular a
    family. [bounded_ground_set_settles_k3] is the conditional: *if*
    extremal sunflower-free [m]-uniform families live on [c * m] points
    for some absolute [c], then [f(m,3) <= B ^ m + 1] with
    [B = 27 ^ (c+1)], which is the sunflower conjecture at [k = 3].

    So the polynomial method is not blocked by a barrier internal to
    itself, and it is not blocked by "the ground set is not a product" —
    the slice rank already handles [{0,1}^n]. It is blocked by one
    missing combinatorial fact, and this file names it: [GroundBounded].

    ** Is [GroundBounded] plausible?

    [rust/examples/ground_scan.rs] measures [N(m, g)], the largest
    [m]-uniform 3-sunflower-free family on [g] points. It is
    non-decreasing in [g] and bounded by [f(m,3) - 1], so it plateaus;
    [GroundBounded c] says it plateaus by [g = c * m]. Measured:

    >    m = 1:  1 2 2 2 2 2 2 ...        plateau at g = 2 = 2m,  value 2
    >    m = 2:  1 3 4 5 6 6 6 6 ...      plateau at g = 6 = 3m,  value 6
    >    m = 3:  1 4 6 10 12 12 14 ...    still rising at g = 9 = 3m

    All three rows are exhaustive as far as they go; [g = 10] at [m = 3]
    is where the search stops finishing. Two plateaus, at ratios 2 and
    3, and a third row that is *still climbing at [3m]* — so [c = 3]
    survives only if [N(3,10) = 14], which is exactly the value not yet
    decided. Read the table as a measurement of where the question
    starts, not as evidence either way.

    One thing it does settle: [N(3,6) = 10] exactly. The
    Abbott–Hanson–Sauer construction is reported to be seeded by a
    3-uniform family of size 10, and that is this family — a maximum on
    *six* points, not a maximum over all ground sets. An earlier note in
    this repository read the two as contradictory. They are not.

    ** What is assumed here

    [NaslundSawinBound] is a [Prop], **not** an axiom, and is carried as
    an explicit hypothesis by the theorems that use it — the same shape
    [SpreadReduction.spread_reduction] uses for
    [SpreadYieldsDisjoint]. So the development's trusted core is
    unchanged: [ALWZ.Rao20_lemma2] remains the only [Axiom] in it, and
    every theorem here is closed under the global context.

    It is stated over [nat] by cubing, since [C ^ n] is irrational
    while [C ^ 3 = 27 / 4] is not:

    >  |F| ^ 3 * 4 ^ n  <=  27 * (n+1) ^ 3 * 27 ^ n.

    Cubing [3 (n+1) * C ^ n] gives [27 (n+1)^3 (27/4)^n]; clearing the
    denominator gives the line above. Nothing is rounded away, and the
    weakening is in the safe direction only in that [<=] is used where
    the source has [<=].

    [GroundBounded] is likewise a hypothesis, not an assumption, because
    it is the open question this file exists to name.

    Zero axioms, zero admits: every theorem here reports
    [Closed under the global context], because what would have been
    assumed is carried in the statements instead. In particular
    [sunflower_iff_no_point_in_exactly_two], the bridge to the
    polynomial-method literature, is unconditional. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower LowerBound ProductLowerBound
     Reflect F23.
Import ListNotations.

(** ** Sunflower-freeness in the form the slice rank consumes

    Naslund and Sawin bound the slice rank of a tensor that is nonzero
    exactly when [x = y = z] or [x, y, z] form a sunflower. The
    combinatorial input is this reformulation, which mentions no
    intersections at all: three sets are a sunflower exactly when no
    point lies in *exactly two* of them.

    This is the bridge between the two literatures, and it is why the
    method reaches [{0,1}^n] at all — "lies in exactly two" is a
    condition on one coordinate at a time, which is what lets the
    tensor factor. Proved here unconditionally, in both directions, with
    no hypothesis on the three sets. *)

Definition InExactlyTwo (x : nat) (A B C : list nat) : Prop :=
  (In x A /\ In x B /\ ~ In x C)
  \/ (In x A /\ ~ In x B /\ In x C)
  \/ (~ In x A /\ In x B /\ In x C).

Theorem sunflower_iff_no_point_in_exactly_two :
  forall A B C,
    (SetEq (inter A B) (inter A C) /\ SetEq (inter A B) (inter B C))
    <-> (forall x, ~ InExactlyTwo x A B C).
Proof.
  intros A B C; split.
  - intros [H1 H2] x Hx.
    destruct Hx as [[HA [HB HC]] | [[HA [HB HC]] | [HA [HB HC]]]].
    + apply HC. destruct H1 as [Hs _].
      assert (Hin : In x (inter A B)) by (apply in_inter_iff; auto).
      apply Hs, in_inter_iff in Hin; tauto.
    + apply HB. destruct H1 as [_ Hs].
      assert (Hin : In x (inter A C)) by (apply in_inter_iff; auto).
      apply Hs, in_inter_iff in Hin; tauto.
    + apply HA. destruct H2 as [_ Hs].
      assert (Hin : In x (inter B C)) by (apply in_inter_iff; auto).
      apply Hs, in_inter_iff in Hin; tauto.
  - intros H; split; split; intros x Hx; apply in_inter_iff in Hx as [H1 H2];
      apply in_inter_iff.
    + split; [exact H1|].
      destruct (in_dec Nat.eq_dec x C) as [HC | HC]; [exact HC|].
      exfalso; apply (H x); left; auto.
    + split; [exact H1|].
      destruct (in_dec Nat.eq_dec x B) as [HB | HB]; [exact HB|].
      exfalso; apply (H x); right; left; auto.
    + split; [exact H2|].
      destruct (in_dec Nat.eq_dec x C) as [HC | HC]; [exact HC|].
      exfalso; apply (H x); left; auto.
    + split; [| exact H1].
      destruct (in_dec Nat.eq_dec x A) as [HA | HA]; [exact HA|].
      exfalso; apply (H x); right; right; auto.
Qed.

(** The direction that needs no case analysis on membership: if every
    distinct triple has a point in exactly two of its members, the
    family has no 3-sunflower. Stated to check that the reformulation
    is the *same* notion this development calls sunflower-freeness, in
    the one direction that is constructive. *)

Definition NSSunflowerFree (F : Family) : Prop :=
  forall A B C,
    In A F -> In B F -> In C F ->
    A <> B -> A <> C -> B <> C ->
    exists x, InExactlyTwo x A B C.

Theorem ns_free_has_no_sunflower :
  forall F, NSSunflowerFree F -> ~ ContainsKSunflower 3 F.
Proof.
  intros F Hns Hc.
  destruct (contains_sunflower_literal 3 F Hc)
    as [S [core [Hincl [Hnd [Hlen [Hsnd Hcore]]]]]].
  destruct S as [|A [|B [|C [|D S']]]]; simpl in Hlen; try discriminate.
  assert (HA : In A F) by (apply Hincl; left; reflexivity).
  assert (HB : In B F) by (apply Hincl; right; left; reflexivity).
  assert (HC : In C F) by (apply Hincl; right; right; left; reflexivity).
  inversion Hnd as [|? ? HniA HndBC]; subst.
  inversion HndBC as [|? ? HniB HndC]; subst.
  assert (HAB : A <> B) by (intro E; subst; apply HniA; left; reflexivity).
  assert (HAC : A <> C)
    by (intro E; subst; apply HniA; right; left; reflexivity).
  assert (HBC : B <> C) by (intro E; subst; apply HniB; left; reflexivity).
  assert (inA : In A [A; B; C]) by (left; reflexivity).
  assert (inB : In B [A; B; C]) by (right; left; reflexivity).
  assert (inC : In C [A; B; C]) by (right; right; left; reflexivity).
  destruct (Hns A B C HA HB HC HAB HAC HBC) as [x Hx].
  apply (proj1 (sunflower_iff_no_point_in_exactly_two A B C)) with (x := x);
    [| exact Hx].
  split.
  - eapply SetEq_trans;
      [exact (Hcore A B inA inB HAB) | apply SetEq_sym; exact (Hcore A C inA inC HAC)].
  - eapply SetEq_trans;
      [exact (Hcore A B inA inB HAB) | apply SetEq_sym; exact (Hcore B C inB inC HBC)].
Qed.

(** ** The Naslund–Sawin bound, as a named axiom *)

Definition Grounded (F : Family) (U : list nat) : Prop :=
  forall A, In A F -> Subset A U.

(** **Naslund–Sawin 2017, Theorem 1**, verbatim up to cubing, as a
    [Prop] to be discharged or assumed at the point of use:
    a 3-sunflower-free family of subsets of an [n]-point ground set has
    at most [3 (n+1) C^n] members, [C = 3 / 2^(2/3)].

    Stated over [nat] by cubing both sides, because [C] is irrational
    and [C^3 = 27/4] is not. No uniformity hypothesis: the source has
    none, and that absence is exactly the point of this file. *)

Definition NaslundSawinBound : Prop :=
  forall (U : list nat) (F : Family),
    NoDup U -> Distinct F -> Grounded F U ->
    ~ ContainsKSunflower 3 F ->
    (length F) ^ 3 * 4 ^ (length U)
    <= 27 * (length U + 1) ^ 3 * 27 ^ (length U).

(** Specialised to uniform families. Nothing happens: a uniform family
    is a family, and the bound never mentions the uniformity. That is
    the mismatch, in one theorem. *)

Theorem ns_bounds_by_ground_set :
  NaslundSawinBound ->
  forall m U F,
    NoDup U -> Uniform m F -> Distinct F -> Grounded F U ->
    ~ ContainsKSunflower 3 F ->
    (length F) ^ 3 * 4 ^ (length U)
    <= 27 * (length U + 1) ^ 3 * 27 ^ (length U).
Proof.
  intros NS m U F HU _ HD HG Hno; exact (NS U F HU HD HG Hno).
Qed.

(** ** The missing fact

    That an extremal sunflower-free [m]-uniform family can be realised
    on [c * m] points. Every theorem below carries it as a hypothesis;
    it is not assumed anywhere. *)

Definition GroundBounded (c : nat) : Prop :=
  forall m j,
    1 <= m -> LowerBound m 3 j ->
    exists F U,
      Uniform m F /\ Distinct F /\ length F = j
      /\ ~ ContainsKSunflower 3 F
      /\ NoDup U /\ Grounded F U /\ length U <= c * m.

(** ** Arithmetic *)

Lemma cube_bounded : forall n, 1 <= n -> n ^ 3 <= 8 ^ n.
Proof.
  intros n Hn; induction n as [|n IH]; [lia|].
  destruct (Nat.eq_dec n 0) as [E | NE]; [subst n; simpl; lia|].
  assert (IHn : n ^ 3 <= 8 ^ n) by (apply IH; lia).
  assert (Hstep : (S n) ^ 3 <= 8 * n ^ 3).
  { simpl; nia. }
  assert (H8 : 8 * n ^ 3 <= 8 * 8 ^ n) by lia.
  simpl (8 ^ S n); lia.
Qed.

Lemma cube_le_inv : forall a b, a ^ 3 <= b ^ 3 -> a <= b.
Proof.
  intros a b H.
  destruct (le_lt_dec a b) as [Hle | Hlt]; [exact Hle | exfalso].
  assert (Hb : b ^ 3 < a ^ 3) by (apply Nat.pow_lt_mono_l; [lia | exact Hlt]).
  lia.
Qed.

(** ** The conditional

    A bound on the ground set turns the polynomial method into the
    sunflower conjecture at [k = 3], with the explicit constant
    [B = 27 ^ (c+1)]. The constant is not chased — see the scoping note
    in [docs/roadmap.md]; any explicit [B] makes the point. *)

(** The arithmetic on its own, with no mention of where the small ground
    set came from: a sunflower-free family living on at most [c * m]
    points has at most [(27^(c+1))^m] members.

    Extracted because a second hypothesis feeds the same computation.
    [coq/IotaGround.v] bounds the ground set of *intersecting*
    sunflower-free families instead — a hypothesis the measurements
    support, where this one's general form is still climbing — and
    reaches the conjecture through the same forty lines. Neither theorem
    should own them. *)

Lemma ns_bound_to_exponential :
  NaslundSawinBound ->
  forall c m (F : Family) (U : list nat),
    1 <= c -> 1 <= m ->
    Distinct F -> ~ ContainsKSunflower 3 F ->
    NoDup U -> Grounded F U -> length U <= c * m ->
    length F <= (27 ^ (c + 1)) ^ m.
Proof.
  intros NS c m F U Hc Hm HDF Hno HndU HG Hu.
  pose proof (NS U F HndU HDF HG Hno) as Hns.
  set (j := length F) in *.
  set (u := length U) in *.
  set (x := c * m).
  assert (Hx : 1 <= x) by (unfold x; nia).
  (* Drop the [4 ^ u] on the left and push [u] up to [x] on the right. *)
  assert (H1 : j ^ 3 <= 27 * (u + 1) ^ 3 * 27 ^ u).
  { assert (H4 : 1 <= 4 ^ u).
    { replace 1 with (4 ^ 0) by reflexivity.
      apply Nat.pow_le_mono_r; lia. }
    nia. }
  assert (H2 : 27 * (u + 1) ^ 3 * 27 ^ u <= 27 * (x + 1) ^ 3 * 27 ^ x).
  { assert (Ha : (u + 1) ^ 3 <= (x + 1) ^ 3)
      by (apply Nat.pow_le_mono_l; lia).
    assert (Hb : 27 ^ u <= 27 ^ x) by (apply Nat.pow_le_mono_r; lia).
    nia. }
  (* [27 (x+1)^3 <= 216 * 8^x <= 216 * 27^x], and [216 <= 27^x * 27^(3m)]. *)
  assert (H3 : 27 * (x + 1) ^ 3 <= 216 * 8 ^ x).
  { assert (Hcb : (x + 1) ^ 3 <= 8 ^ (x + 1)) by (apply cube_bounded; lia).
    replace (8 ^ (x + 1)) with (8 ^ x * 8) in Hcb
      by (rewrite Nat.pow_add_r; simpl; lia).
    lia. }
  assert (H4 : 8 ^ x <= 27 ^ x) by (apply Nat.pow_le_mono_l; lia).
  (* [216 <= 27^2], and the exponent is at least 2. Going through
     [27^2] rather than [27^4] keeps [simpl] off a six-digit numeral. *)
  assert (H5 : (216 : nat) <= 27 ^ (x + 3 * m)).
  { transitivity (27 ^ 2); [simpl; lia|].
    apply Nat.pow_le_mono_r; lia. }
  (* Assemble: [j^3 <= 27^((c+1)*m*3)], then take cube roots. *)
  apply cube_le_inv.
  rewrite <- !Nat.pow_mul_r.
  assert (Hgoal : 27 * (x + 1) ^ 3 * 27 ^ x <= 27 ^ ((c + 1) * (m * 3))).
  { assert (Ha : 27 * (x + 1) ^ 3 <= 216 * 27 ^ x) by lia.
    assert (Hb : 216 * 27 ^ x <= 27 ^ (x + 3 * m) * 27 ^ x)
      by (apply Nat.mul_le_mono_r; exact H5).
    assert (Hc2 : 27 * (x + 1) ^ 3 <= 27 ^ (x + 3 * m) * 27 ^ x) by lia.
    assert (Hd : 27 * (x + 1) ^ 3 * 27 ^ x
                 <= 27 ^ (x + 3 * m) * 27 ^ x * 27 ^ x)
      by (apply Nat.mul_le_mono_r; exact Hc2).
    assert (Hsum : 27 ^ (x + 3 * m) * 27 ^ x * 27 ^ x
                   = 27 ^ (x + 3 * m + x + x))
      by (rewrite <- !Nat.pow_add_r; reflexivity).
    assert (Hfin : 27 ^ (x + 3 * m + x + x) <= 27 ^ ((c + 1) * (m * 3))).
    { apply Nat.pow_le_mono_r; [lia | unfold x; nia]. }
    lia. }
  lia.
Qed.

Theorem bounded_ground_set_settles_k3 :
  NaslundSawinBound ->
  forall c, 1 <= c -> GroundBounded c ->
    forall m j, 1 <= m -> LowerBound m 3 j -> j <= (27 ^ (c + 1)) ^ m.
Proof.
  intros NS c Hc HGB m j Hm HL.
  destruct (HGB m j Hm HL) as [F [U [HUF [HDF [Hlen [Hno [HndU [HG Hu]]]]]]]].
  pose proof (ns_bound_to_exponential NS c m F U Hc Hm HDF Hno HndU HG Hu) as Hb.
  lia.
Qed.

(** The same statement in the repository's bound vocabulary. *)

Corollary bounded_ground_set_excludes_lower_bounds :
  NaslundSawinBound ->
  forall c, 1 <= c -> GroundBounded c ->
    forall m j, 1 <= m -> (27 ^ (c + 1)) ^ m < j -> ~ LowerBound m 3 j.
Proof.
  intros NS c Hc HGB m j Hm Hj HL.
  pose proof (bounded_ground_set_settles_k3 NS c Hc HGB m j Hm HL); lia.
Qed.

(** ** What the ground-set search found

    The measurement is not only a diagnostic. Its [m = 3] row tops out
    (so far) at [N(3,9) = 14], and the witness is something this
    development can check outright: [f(3,3) >= 15], against the 13 that
    [DirectSum.lower_bound_f_n_3_odd] gives at [t = 1].

    The family is not designed. It is the maximum returned by the
    exhaustive branch-and-bound search in
    [rust/examples/ground_scan.rs] at [g = 9], transcribed. Fifteen
    minutes of search there; what makes it a theorem here is
    [F23.sunflower3b], the reflective 3-sunflower detector, whose
    soundness is proved — so the Coq side re-derives the property from
    the family alone and takes nothing from the search.

    It does not improve the *rate*: [14^(1/3) = 2.41] is below the
    [6^(1/2) = 2.449] that [DirectSum] reaches by pairing up. What it
    improves is the value at one uniformity, and it is the input any
    substitution-style construction would want — see
    [docs/roadmap.md] section 5. *)

Definition ground9_max : Family :=
  [[0; 1; 2]; [0; 1; 3]; [0; 2; 3]; [1; 2; 3];
   [0; 4; 5]; [1; 4; 5]; [0; 4; 6]; [1; 4; 6];
   [2; 5; 7]; [3; 6; 7]; [2; 5; 8]; [3; 6; 8];
   [2; 7; 8]; [3; 7; 8]].

Lemma ground9_max_no_sunflower : ~ ContainsKSunflower 3 ground9_max.
Proof.
  intro Hc.
  pose proof (sunflower3b_sound ground9_max Hc) as E.
  vm_compute in E; discriminate.
Qed.

Theorem lower_bound_3_3_14 : LowerBound 3 3 14.
Proof.
  exists ground9_max.
  split; [apply uniformb_correct; vm_compute; reflexivity|].
  split; [apply distinctb_correct; vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  exact ground9_max_no_sunflower.
Qed.

Corollary no_upper_bound_3_3_14 : ~ UpperBound 3 3 14.
Proof.
  intro Hub.
  destruct lower_bound_3_3_14 as [F [HU [HD [Hlen Hno]]]].
  apply Hno, Hub; [exact HU | exact HD | lia].
Qed.

(** It lives on nine points, which is the [m = 3] entry of the
    [GroundBounded] table and the reason the row has not plateaued at
    [3m]. Checked, rather than asserted. *)

Lemma ground9_max_is_grounded : Grounded ground9_max (seq 0 9).
Proof.
  unfold Grounded.
  apply (proj1 (groundedb_correct ground9_max (seq 0 9))).
  vm_compute; reflexivity.
Qed.
