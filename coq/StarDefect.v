(** * StarDefect.v — the Erdős–Rado ratio, and why it cannot be a constant

    Erdős–Rado's proof is one step iterated: find a heavy point, recurse
    into its link. [Intersecting.sunflower_free_star_bound] proves the
    step, and this file names the quantity it bounds. Write

    >  rho(F)  =  |F| / maxdeg(F)

    for the ratio between a family's size and its largest point degree.

    ** Why it is the quantity to watch

    The link at a maximum-degree point has [maxdeg(F)] members and
    uniformity [b - 1], so [|F| = rho(F) * |link|] and, descending to the
    bottom,

    >  |F|  =  rho_0 * rho_1 * ... * rho_{b-1}

    **exactly**, not as an estimate — the chain telescopes, and
    [rust/tests/star_defect.rs] checks that it does. Erdős–Rado bounds
    each factor by [2(b-j)] and gets [2^b b!]. The sunflower conjecture
    at [k = 3] is precisely that the product is [C^b], i.e. that the
    ratios are [O(1)] *on average along the chain*.

    And a constant bound on a *single* factor would settle it outright:

    >  StarBounded c  :=  every sunflower-free b-uniform family has a
    >                     point x with |F| <= c * deg(x)

    gives [g(b) <= c g(b-1)] hence [g(b) <= 2 c^(b-1)] — the whole
    conjecture, from one inequality with one number in it
    ([star_bounded_settles_k3], with [c(3) = 2c]).

    ** So is it bounded? No, and the witness is the 1972 construction

    [rust/tests/iota_sandwich.rs] has measured the worst ratio for a
    while — 2, 3, 2.75 at uniformities 1, 2, 3 against the proved [2b] —
    and the row looks flat. **It is not flat.** Measured in
    [rust/examples/star_defect.rs], with exact rational arithmetic and
    every family re-verified: [rho] is *multiplicative* under the
    Abbott–Hanson–Sauer substitution,

    >  |substitute(G,H)|       = |G| |H|^a
    >  maxdeg(substitute(G,H)) = maxdeg(G) maxdeg(H) |H|^(a-1)
    >  ==>  rho(substitute(G,H)) = rho(G) rho(H)

    — the [|H|^(a-1)] cancels. With [rho(iota(2)) = 3/2] and
    [rho(iota(3)) = 2], iterating on [iota(3)] gives [rho = 2^k] at
    [b = 3^k], i.e. [rho = b^(log_3 2) = b^0.6309...]. **Unbounded.**
    Confirmed directly at [b = 9], where the substitution's 10000 members
    have maximum degree 2500 and [rho = 4] exactly.

    Formalising that refutation needs [substitute] in Coq, which
    [docs/roadmap.md] §5 item 2 costs a session on its own. What is
    proved here instead is the finitistic half:
    [star_bounded_needs_c_at_least_five] — the doubling of the
    exhaustively extremal [iota(4,9) = 27] has 54 members with maximum
    degree 12, so any admissible [c] is at least 5, where the proved
    ceiling at that uniformity is [2b = 8]. The same shape as
    [Product.step_bounded_needs_D_at_least_three] and
    [IotaGround.ground_bounded_needs_c_at_least_four]: the data forces
    the constant up, and here the constructions force it up without
    limit.

    ** What survives

    The average. On the same tower the product of the [b] chain ratios is
    [10^((b-1)/2)], so their geometric mean tends to [sqrt(10) = 3.162]
    while the largest single factor grows like [b^0.63]. That gap is
    exactly [docs/roadmap.md] §4's still-unclaimed "are the covers
    correlated across levels?", and it is the shape "pay the log once"
    has to take: **the conjecture is a statement about the geometric mean
    of the chain, and a per-level constant is provably unavailable.**

    Zero axioms, zero admits. *)

From Coq Require Import List Arith Lia Bool.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower LowerBound Reflect Pigeonhole
     ErdosRado Spread SpreadReduction Conjecture F23 Intersecting IotaRate
     SliceRank Product.
Import ListNotations.

(** ** Naming the heaviest point

    [pigeonhole_family] produces a point of *more* than a given degree;
    to name the maximiser the degrees over a finite point list have to be
    compared, which is what this fold does. *)

Definition maxdeg_over (X : list nat) (F : Family) : nat :=
  fold_right (fun x acc => Nat.max (length (star x F)) acc) 0 X.

Lemma maxdeg_over_cons :
  forall y X F,
    maxdeg_over (y :: X) F = Nat.max (length (star y F)) (maxdeg_over X F).
Proof. reflexivity. Qed.

Lemma maxdeg_over_ge :
  forall X F x, In x X -> length (star x F) <= maxdeg_over X F.
Proof.
  induction X as [|y X' IH]; intros F x Hx; [inversion Hx|].
  rewrite maxdeg_over_cons.
  destruct Hx as [E | Hx]; [subst y; lia|].
  pose proof (IH F x Hx); lia.
Qed.

Lemma maxdeg_over_attained :
  forall X F, X <> [] -> exists x, In x X /\ length (star x F) = maxdeg_over X F.
Proof.
  induction X as [|y X' IH]; intros F Hne; [contradiction|].
  destruct X' as [|z X''].
  - exists y; split; [left; reflexivity|].
    rewrite maxdeg_over_cons; simpl (maxdeg_over [] F); lia.
  - destruct (IH F ltac:(discriminate)) as [x [Hx Hval]].
    rewrite maxdeg_over_cons.
    destruct (le_lt_dec (length (star y F)) (maxdeg_over (z :: X'') F))
      as [Hle | Hlt].
    + exists x; split; [right; exact Hx | lia].
    + exists y; split; [left; reflexivity | lia].
Qed.

(** ** The first step of Erdős–Rado, with the point named

    [Intersecting.sunflower_free_star_bound] proves this and immediately
    consumes it; the same argument, stopped one line earlier, says that
    every sunflower-free family has a point of degree at least
    [|F|/(2b)]. That is the per-family form, and it is what the recursion
    below iterates.

    The proof is the source's, verbatim as far as the pigeonhole: a
    maximal pairwise-disjoint subfamily has at most two members (three
    would be a sunflower with empty core), so its union [X] has at most
    [2b] points and meets everything. What differs is the last step —
    instead of bounding the star by a hypothesis, the maximiser over [X]
    is named. *)

Theorem star_defect_bound :
  forall b (F : Family),
    1 <= b -> Uniform b F -> Distinct F -> ~ ContainsKSunflower 3 F ->
    exists x, length F <= 2 * b * length (star x F).
Proof.
  intros b F Hb HU HD Hno.
  destruct F as [|A0 F']; [exists 0; simpl; lia|].
  set (FF := A0 :: F').
  assert (HFne : Forall (fun A : list nat => A <> []) FF).
  { apply Forall_forall; intros A HA.
    unfold Uniform in HU; rewrite Forall_forall in HU.
    destruct (HU A HA) as [HAlen _].
    destruct A; [simpl in HAlen; lia | discriminate]. }
  destruct (max_disjoint_cover HFne) as [Scov [Hincl [Hnd [Hpd Hcov]]]].
  assert (Hcov2 : length Scov <= 2).
  { destruct (le_lt_dec (length Scov) 2) as [H2 | H3]; [exact H2 | exfalso].
    apply Hno.
    apply (@ContainsKSunflower_of_incl 3 (firstn 3 Scov) FF []).
    - intros B HB; apply Hincl, (incl_firstn 3 Scov); exact HB.
    - apply firstn_length_le; lia.
    - apply pairwise_disjoint_sunflower;
        [ apply NoDup_firstn; exact Hnd
        | intros B C HB HC HBC; apply Hpd;
          try (apply (incl_firstn 3 Scov); assumption); exact HBC ]. }
  set (X := concat Scov).
  assert (HXcov : forall A, In A FF -> exists x, In x A /\ In x X)
    by (intros A HA; apply (cover_provides_element FF Scov A); auto).
  assert (HXlen : length X <= 2 * b).
  { assert (H1 : length X <= length Scov * b).
    { unfold X; apply concat_uniform_length.
      apply Forall_forall; intros B HB; apply Hincl in HB.
      unfold Uniform in HU; rewrite Forall_forall in HU; apply HU; exact HB. }
    nia. }
  (* [X] is nonempty: the first member meets it. *)
  assert (HXne : X <> []).
  { destruct (HXcov A0 (or_introl eq_refl)) as [x [_ HxX]].
    intro E; rewrite E in HxX; inversion HxX. }
  destruct (maxdeg_over_attained X FF HXne) as [x [HxX Hval]].
  exists x.
  (* If the maximum degree were too small, the pigeonhole would produce a
     point above it. *)
  destruct (le_lt_dec (length FF) (2 * b * length (star x FF))) as [Hle | Hlt];
    [exact Hle | exfalso].
  assert (Hsize : length FF > length X * maxdeg_over X FF) by nia.
  destruct (pigeonhole_family FF X (maxdeg_over X FF) HXcov Hsize)
    as [y [HyX Hdeg]].
  pose proof (maxdeg_over_ge X FF y HyX) as Hmax.
  rewrite star_length in Hmax; lia.
Qed.

(** ** The hypothesis: can the factor be a constant?

    [star_defect_bound] gives the factor [2b]. A *uniform* factor is a
    different statement, and it is the one that would settle the
    conjecture. *)

Definition StarBounded (c : nat) : Prop :=
  forall b (F : Family),
    1 <= b -> Uniform b F -> Distinct F -> ~ ContainsKSunflower 3 F ->
    exists x, length F <= c * length (star x F).

(** The recursion, parametric in the constant: one level of
    [StarBounded] turns a bound at uniformity [b] into one at [b + 1].
    The link at the heavy point is where the uniformity drops, and it is
    sunflower-free because links of sunflower-free families are. *)

Lemma link_singleton_length :
  forall x F, length (link [x] F) = length (star x F).
Proof.
  intros x F.
  rewrite length_link; unfold deg, star.
  f_equal; apply filter_ext_eq; intros B; apply containsb_singleton.
Qed.

Theorem star_step :
  forall c b M,
    StarBounded c -> GAtMost b M -> GAtMost (S b) (c * M).
Proof.
  intros c b M Hsb Hg F HU HD Hno.
  destruct (Hsb (S b) F ltac:(lia) HU HD Hno) as [x Hx].
  assert (Hlink : length (link [x] F) <= M).
  { apply Hg.
    - replace b with (S b - length [x]) by (simpl; lia).
      apply (@link_uniform (S b) [x] F HU).
      constructor; [intros [] | constructor].
    - exact (@link_distinct [x] F HD).
    - intro Hc; exact (Hno (@link_sunflower_lift [x] F 3 Hc)). }
  rewrite link_singleton_length in Hlink; nia.
Qed.

(** Iterated from [g(1) = 2]. *)

Theorem star_bounded_gives_explicit_bound :
  forall c b, StarBounded c -> 1 <= b -> GAtMost b (2 * c ^ (b - 1)).
Proof.
  intros c b Hsb.
  induction b as [|b IH]; intros Hb; [lia|].
  destruct (Nat.eq_dec b 0) as [E | Hne].
  - subst b; simpl; replace (2 * 1) with 2 by lia; exact g_one_at_most_two.
  - pose proof (IH ltac:(lia)) as Hprev.
    pose proof (star_step c b (2 * c ^ (b - 1)) Hsb Hprev) as Hstep.
    replace (S b - 1) with b by lia.
    assert (E : c * (2 * c ^ (b - 1)) = 2 * c ^ b).
    { replace b with (S (b - 1)) at 2 by lia.
      replace (c ^ S (b - 1)) with (c * c ^ (b - 1)) by reflexivity.
      ring. }
    rewrite E in Hstep; exact Hstep.
Qed.

(** A [StarBounded] constant is at least 1, because a one-member family
    at uniformity 1 exists. Needed to absorb the [2] into the base. *)

Lemma star_bounded_pos : forall c, StarBounded c -> 1 <= c.
Proof.
  intros c Hsb.
  assert (HU : Uniform 1 [[0]]) by (apply uniformb_correct; vm_compute; reflexivity).
  assert (HD : Distinct [[0]]) by (apply distinctb_correct; vm_compute; reflexivity).
  assert (Hno : ~ ContainsKSunflower 3 [[0]]).
  { intro Hc; pose proof (sunflower3b_sound [[0]] Hc) as E;
      vm_compute in E; discriminate. }
  destruct (Hsb 1 [[0]] ltac:(lia) HU HD Hno) as [x Hx].
  assert (Hle : length (star x [[0]]) <= 1).
  { unfold star; simpl; destruct (memb x [0]); simpl; lia. }
  simpl in Hx; nia.
Qed.

Theorem star_bounded_settles_k3 :
  forall c, StarBounded c -> sunflower_conjecture_k_3.
Proof.
  intros c Hsb.
  apply conjecture_k_3_iff_g_exponential.
  exists (2 * c); intros b Hb.
  pose proof (star_bounded_gives_explicit_bound c b Hsb Hb) as Hg.
  pose proof (star_bounded_pos c Hsb) as Hc1.
  intros F HU HD Hno.
  pose proof (Hg F HU HD Hno) as Hle.
  assert (Hpow : 2 * c ^ (b - 1) <= (2 * c) ^ b).
  { rewrite Nat.pow_mul_l.
    assert (H2 : 2 <= 2 ^ b).
    { destruct b as [|b']; [lia|].
      simpl; pose proof (pow_two_pos b'); lia. }
    assert (Hc : c ^ (b - 1) <= c ^ b) by (apply Nat.pow_le_mono_r; lia).
    nia. }
  lia.
Qed.

Corollary star_bounded_gives_the_constant :
  forall c, StarBounded c -> forall n, 1 <= n -> UpperBound n 3 (S ((2 * c) ^ n)).
Proof.
  intros c Hsb n Hn.
  apply upper_bound_of_sunflower_free_bound.
  pose proof (star_bounded_gives_explicit_bound c n Hsb Hn) as Hg.
  pose proof (star_bounded_pos c Hsb) as Hc1.
  intros F HU HD Hno.
  pose proof (Hg F HU HD Hno) as Hle.
  assert (Hpow : 2 * c ^ (n - 1) <= (2 * c) ^ n).
  { rewrite Nat.pow_mul_l.
    assert (H2 : 2 <= 2 ^ n).
    { destruct n as [|n']; [lia|].
      simpl; pose proof (pow_two_pos n'); lia. }
    assert (Hc : c ^ (n - 1) <= c ^ n) by (apply Nat.pow_le_mono_r; lia).
    nia. }
  lia.
Qed.

(** ** The constant the data already forces

    The doubling of the exhaustively extremal [iota(4,9) = 27] is 54
    members at uniformity 4, and every point of it lies in at most 12 of
    them — so any admissible [c] satisfies [54 <= 12c], hence [c >= 5].

    Quantifying over *all* [x], not only the eighteen points the family
    uses, is what makes this a bound on [StarBounded] rather than on a
    ground-set-restricted variant: a point outside the ground set has
    degree zero, and [star_outside_ground] is that. *)

Definition doubled_iota4 : Family := double iota4.

Lemma star_outside_ground :
  forall F U x, Grounded F U -> ~ In x U -> star x F = [].
Proof.
  intros F U x Hgr Hnin.
  destruct (star x F) as [|A S] eqn:E; [reflexivity | exfalso].
  assert (HA : In A (star x F)) by (rewrite E; left; reflexivity).
  unfold star in HA; apply filter_In in HA as [HAF Hmemb].
  apply memb_true_iff in Hmemb.
  exact (Hnin (Hgr A HAF x Hmemb)).
Qed.

Lemma doubled_iota4_length : length doubled_iota4 = 54.
Proof. vm_compute; reflexivity. Qed.

Lemma doubled_iota4_grounded : Grounded doubled_iota4 (seq 0 18).
Proof.
  unfold Grounded.
  apply (proj1 (groundedb_correct doubled_iota4 (seq 0 18))).
  vm_compute; reflexivity.
Qed.

Lemma doubled_iota4_maxdeg :
  forall x, length (star x doubled_iota4) <= 12.
Proof.
  intros x.
  destruct (in_dec Nat.eq_dec x (seq 0 18)) as [Hin | Hnin].
  - assert (Hall : forallb (fun y => Nat.leb (length (star y doubled_iota4)) 12)
                     (seq 0 18) = true) by (vm_compute; reflexivity).
    pose proof (proj1 (forallb_forall _ _) Hall x Hin) as Hb.
    apply Nat.leb_le; exact Hb.
  - rewrite (star_outside_ground doubled_iota4 (seq 0 18) x
               doubled_iota4_grounded Hnin); simpl; lia.
Qed.

Lemma doubled_iota4_uniform : Uniform 4 doubled_iota4.
Proof. apply uniformb_correct; vm_compute; reflexivity. Qed.

Lemma doubled_iota4_distinct : Distinct doubled_iota4.
Proof. apply distinctb_correct; vm_compute; reflexivity. Qed.

Lemma doubled_iota4_no_sunflower : ~ ContainsKSunflower 3 doubled_iota4.
Proof.
  intro Hc.
  pose proof (sunflower3b_sound doubled_iota4 Hc) as E;
    vm_compute in E; discriminate.
Qed.

Theorem star_bounded_needs_c_at_least_five :
  forall c, StarBounded c -> 5 <= c.
Proof.
  intros c Hsb.
  destruct (Hsb 4 doubled_iota4 ltac:(lia)
              doubled_iota4_uniform doubled_iota4_distinct
              doubled_iota4_no_sunflower) as [x Hx].
  rewrite doubled_iota4_length in Hx.
  pose proof (doubled_iota4_maxdeg x) as Hd.
  nia.
Qed.

(** And the proved ceiling at that uniformity, for contrast: [2b = 8].
    So at [b = 4] the truth for the ratio is somewhere in [[4.5, 8]], and
    the constructions push the lower end up without limit — see the
    header, and [rust/examples/star_defect.rs] for the measurement. *)

Corollary the_ratio_at_four_is_between_the_witness_and_the_ceiling :
  (forall F : Family,
      Uniform 4 F -> Distinct F -> ~ ContainsKSunflower 3 F ->
      exists x, length F <= 8 * length (star x F))
  /\ length doubled_iota4 = 54
  /\ (forall x, length (star x doubled_iota4) <= 12).
Proof.
  split; [| split; [exact doubled_iota4_length | exact doubled_iota4_maxdeg]].
  intros F HU HD Hno.
  destruct (star_defect_bound 4 F ltac:(lia) HU HD Hno) as [x Hx].
  exists x; lia.
Qed.
