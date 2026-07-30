(** * IotaGround.v -- Point the ground-set hypothesis at iota, not at g.

    [SliceRank.v] names the one fact that would turn the polynomial
    method into the sunflower conjecture at [k = 3]:

    >  GroundBounded c  :=  an extremal sunflower-free m-uniform family
    >                       can be realised on at most c*m points

    and records, correctly, that the measurements do not support it. The
    general ground-set row is *still climbing* where it would have to
    plateau:

    >    N(m,g)   g =  3  4  5  6   7   8   9
    >    m = 3:        1  4  6  10  12  12  14      still rising at 3m

    This file asks the same question about *intersecting* sunflower-free
    families, which [IotaRate.conjecture_k_3_iff_iota_exponential] says
    is an equivalent problem. The row could not look more different:

    >    iota(3,g) g =  3  4  5  6   7   8   9  10  11  12  13  14
    >                   1  4  6  10  10  10  10  10  10  10  10  10

    They agree at six points — where both are 10 — and then diverge. The
    general maximum climbs to 14 by nine points; the intersecting one has
    not moved by fourteen, which is where the search was stopped rather
    than where it slowed down ([rust/examples/iota_ground.rs], every entry
    exhaustive and each one instant).

    That is not an accident of small numbers. Intersecting-ness is a
    *locality* constraint: every member meets every other, so the family
    cannot spread out over a large ground set the way an arbitrary
    sunflower-free family can. It is exactly the property a ground-set
    bound needs, and exactly the property the general problem lacks.

    So [IotaGroundBounded c] plus Naslund–Sawin settles [k = 3]
    ([iota_ground_bounded_settles_k3]), by the same forty lines of
    arithmetic [SliceRank.bounded_ground_set_settles_k3] uses — now
    factored out as [SliceRank.ns_bound_to_exponential] so neither owns
    them.

    ** The second thing here: a ground-set-aware link bound

    [Intersecting.intersecting_link_bound] is [iota(b) <= b * g(b-1)]:
    every member meets one fixed member, which has [b] points. Counting
    over the *whole* ground set instead of over one member gives

    >  b * |F|  <=  |U| * N(b-1, |U|-1)

    for any sunflower-free [b]-uniform family on [U] — no intersecting
    hypothesis, and no hypothesis at all beyond the ones that make the
    statement well-formed. It is double counting: the incidences between
    [U] and [F] number [b|F|] from one side, and from the other side each
    point contributes its degree, which is the size of a link.

    Measured, it is met with **equality** at three of the four places
    where both sides are known:

    >    b  g   iota   b*|F|   g*N(b-1,g-1)
    >    2  3      3       6              6   TIGHT
    >    3  6     10      30             30   TIGHT
    >    4  8     24      96             96   TIGHT
    >    4  9     27     108            108   TIGHT

    Equality forces the extremal family to be regular *and* every one of
    its links to be an extremal [N(b-1,g-1)] family. The witnesses are
    regular ([rust/examples/iota_ground.rs] checks the degree sequence),
    so the rigidity is real, and it says the extremal intersecting
    families are as far from a star as a family can be — [iota3] is
    5-regular on six points, diversity 5 out of 10. That is the regime
    where Hilton–Milner and Frankl's diversity theorems are strongest,
    which is where [docs/roadmap.md] §5 item 0 points next.

    Unconditionally, at [b = 3] with the proved [g(2) = 6], it gives
    [N(3,g) <= 2g] — a proved cap on the row [SliceRank.v] can only
    measure, and in particular [N(3,10) <= 20] where the search does not
    finish.

    Zero axioms, zero admits. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower HallCore LowerBound Conjecture
     Spread Reflect F23 Intersecting IotaRate SliceRank.
Import ListNotations.

(** ** Double counting the incidences between a ground set and a family

    Two ways of summing the same table: down the columns (one per ground
    point, contributing its degree) and along the rows (one per member,
    contributing its size). No hypotheses — the identity is about the
    lists, and the hypotheses come in only when the two sides are
    evaluated. *)

Fixpoint degsum (U : list nat) (F : Family) : nat :=
  match U with
  | [] => 0
  | x :: U' => length (filter (fun A => memb x A) F) + degsum U' F
  end.

Fixpoint sizesum (U : list nat) (F : Family) : nat :=
  match F with
  | [] => 0
  | A :: F' => length (filter (fun x => memb x A) U) + sizesum U F'
  end.

(** Recursion on the *other* argument is the whole content: [degsum]
    recurses on the ground set, [sizesum] on the family, and the
    identity between them is where the two directions of the count meet. *)

Lemma degsum_cons_point :
  forall x U F,
    degsum (x :: U) F = length (filter (fun A => memb x A) F) + degsum U F.
Proof. reflexivity. Qed.

Lemma sizesum_cons_member :
  forall U A F,
    sizesum U (A :: F) = length (filter (fun x => memb x A) U) + sizesum U F.
Proof. reflexivity. Qed.

Lemma length_filter_cons :
  forall {T : Type} (f : T -> bool) (a : T) (l : list T),
    length (filter f (a :: l)) = (if f a then 1 else 0) + length (filter f l).
Proof. intros T f a l; simpl; destruct (f a); simpl; lia. Qed.

Lemma degsum_nil_family : forall U, degsum U [] = 0.
Proof.
  intros U; induction U as [|x U IH]; [reflexivity|].
  rewrite degsum_cons_point, IH; reflexivity.
Qed.

Lemma degsum_cons_family :
  forall U A F,
    degsum U (A :: F) = length (filter (fun x => memb x A) U) + degsum U F.
Proof.
  intros U A F; induction U as [|x U IH]; [reflexivity|].
  rewrite !degsum_cons_point.
  rewrite (length_filter_cons (fun B : list nat => memb x B) A F).
  rewrite (length_filter_cons (fun y : nat => memb y A) x U).
  rewrite IH.
  destruct (memb x A); lia.
Qed.

Theorem degsum_eq_sizesum : forall U F, degsum U F = sizesum U F.
Proof.
  intros U F; induction F as [|A F IH]; [apply degsum_nil_family|].
  rewrite degsum_cons_family, sizesum_cons_member, IH; reflexivity.
Qed.

(** The row side: every member has [b] points and all of them lie in
    [U], so its row contributes exactly [b]. *)

Lemma sizesum_uniform :
  forall b U F,
    NoDup U -> Uniform b F -> Grounded F U -> sizesum U F = b * length F.
Proof.
  intros b U F HndU HU HG; induction F as [|A F IH]; [simpl; lia|].
  assert (HAin : In A (A :: F)) by (left; reflexivity).
  unfold Uniform in HU; inversion HU as [|? ? HUA HU']; subst.
  destruct HUA as [HAlen HAnd].
  rewrite sizesum_cons_member.
  rewrite (length_filter_memb HndU HAnd (HG A HAin)), HAlen.
  rewrite IH; [simpl; lia | exact HU' |].
  intros B HB; apply HG; right; exact HB.
Qed.

(** The column side: each point's column is the star there, which is a
    link, hence a smaller sunflower-free family. *)

Lemma degsum_le :
  forall (U : list nat) (F : Family) (N : nat),
    (forall x, In x U -> length (filter (fun A => memb x A) F) <= N) ->
    degsum U F <= length U * N.
Proof.
  intros U F N; induction U as [|x U IH]; intros Hpt; [simpl; lia|].
  rewrite degsum_cons_point.
  assert (Hx : length (filter (fun A => memb x A) F) <= N)
    by (apply Hpt; left; reflexivity).
  assert (Hrest : degsum U F <= length U * N)
    by (apply IH; intros y Hy; apply Hpt; right; exact Hy).
  simpl (length (x :: U)); lia.
Qed.

(** ** The star at a point is a link, and links are smaller

    The same three facts [Intersecting.intersecting_link_bound] uses,
    isolated so the ground-set version can reuse them — and sharpened
    with the ground set of the link, which is [U] minus the point. That
    sharpening is what makes the bound tight at the measured rows. *)

Lemma link_grounded :
  forall x (U : list nat) (F : Family),
    Grounded F U -> Grounded (link [x] F) (rem_elt x U).
Proof.
  intros x U F HG B HB.
  apply in_link_inv in HB as [A [HAF [HTA E]]]; subst B.
  intros y Hy; apply in_setminus_iff in Hy as [HyA HyT].
  apply in_rem_iff; split; [exact (HG A HAF y HyA)|].
  intro E; subst y; apply HyT; left; reflexivity.
Qed.

Lemma star_at_point_bounded :
  forall b N x (U : list nat) (F : Family),
    NoDup U -> In x U ->
    Uniform b F -> Distinct F -> Grounded F U ->
    ~ ContainsKSunflower 3 F ->
    (forall (V : list nat) (G : Family),
        NoDup V -> S (length V) <= length U ->
        Uniform (b - 1) G -> Distinct G -> Grounded G V ->
        ~ ContainsKSunflower 3 G -> length G <= N) ->
    length (filter (fun A => memb x A) F) <= N.
Proof.
  intros b N x U F HndU HxU HU HD HG Hno Hlink.
  assert (Heq : length (link [x] F) = length (filter (fun A => memb x A) F)).
  { rewrite length_link; unfold deg.
    f_equal; apply filter_ext_eq; intros B; apply containsb_singleton. }
  rewrite <- Heq.
  apply (Hlink (rem_elt x U)).
  - apply rem_NoDup; exact HndU.
  - rewrite (@length_rem_elt_in x U HndU HxU).
    destruct U as [|u U']; [inversion HxU | simpl; lia].
  - replace (b - 1) with (b - length [x]) by (simpl; lia).
    apply (@link_uniform b [x] F HU).
    constructor; [intros [] | constructor].
  - exact (@link_distinct [x] F HD).
  - exact (link_grounded x U F HG).
  - intro Hc; exact (Hno (@link_sunflower_lift [x] F 3 Hc)).
Qed.

(** ** The ground-set link bound

    >  b * |F|  <=  |U| * N(b-1, |U|-1)

    Double counting, with the two sides evaluated by the two lemmas
    above. No uniformity-positivity hypothesis and no intersecting one:
    it holds of every sunflower-free uniform family on every ground set.

    Compare [Intersecting.intersecting_link_bound], which counts over one
    member's [b] points and needs the family to be intersecting to know
    every member is there. This counts over all [|U|] points and needs
    nothing, at the cost of a bound that grows with the ground set — so
    the two are useful in opposite regimes, and this one is the one that
    says something when the ground set is *small*. *)

Theorem link_degree_ground_bound :
  forall b N (U : list nat) (F : Family),
    NoDup U -> Uniform b F -> Distinct F -> Grounded F U ->
    ~ ContainsKSunflower 3 F ->
    (forall (V : list nat) (G : Family),
        NoDup V -> S (length V) <= length U ->
        Uniform (b - 1) G -> Distinct G -> Grounded G V ->
        ~ ContainsKSunflower 3 G -> length G <= N) ->
    b * length F <= length U * N.
Proof.
  intros b N U F HndU HU HD HG Hno Hlink.
  rewrite <- (sizesum_uniform b U F HndU HU HG), <- degsum_eq_sizesum.
  apply degsum_le; intros x HxU.
  exact (star_at_point_bounded b N x U F HndU HxU HU HD HG Hno Hlink).
Qed.

(** At [b = 3] the link bound is [g(2) = 6], which this development
    proves, so the whole thing becomes unconditional: a 3-uniform
    sunflower-free family on [U] has at most [2|U|] members. *)

Corollary three_uniform_ground_bound :
  forall (U : list nat) (F : Family),
    NoDup U -> Uniform 3 F -> Distinct F -> Grounded F U ->
    ~ ContainsKSunflower 3 F ->
    length F <= 2 * length U.
Proof.
  intros U F HndU HU HD HG Hno.
  assert (Hb : 3 * length F <= length U * 6).
  { apply (link_degree_ground_bound 3 6 U F HndU HU HD HG Hno).
    intros V G HndV _ HUG HDG _ HnoG.
    destruct (le_lt_dec (length G) 6) as [Hle | Hlt]; [exact Hle | exfalso].
    apply HnoG, f_2_3_upper; [exact HUG | exact HDG | lia]. }
  lia.
Qed.

(** The value [SliceRank.v] records as the one the search does not
    decide. It is now capped by a theorem: [N(3,10) <= 20], against the
    [C(10,3) = 120] that counting alone gives and the 48 that
    Erdős–Rado gives at uniformity 3. Still far from the measured 14,
    and it does *not* decide whether the row plateaus. *)

Corollary n_three_ten_at_most_twenty :
  forall (U : list nat) (F : Family),
    NoDup U -> length U <= 10 ->
    Uniform 3 F -> Distinct F -> Grounded F U ->
    ~ ContainsKSunflower 3 F ->
    length F <= 20.
Proof.
  intros U F HndU Hu HU HD HG Hno.
  pose proof (three_uniform_ground_bound U F HndU HU HD HG Hno); lia.
Qed.

(** ** How [GroundBounded] must be read, and why that is not pedantry

    [FPPTZ24] (the "Odd-sunflowers" paper, JCTA 2024) records that the
    ground set of a sunflower-free [k]-uniform family can be
    **exponentially** large: [g_v(k) >= 2^k - 1], witnessed by the
    root-to-leaf paths of a rooted binary tree of depth [k], taken as sets
    of edges. Two such paths meet in the path to their leaves' least
    common ancestor, and among any three leaves two are strictly closer
    than the other pairs, so of the three pairwise intersections two
    coincide and one is strictly longer — never all three equal.

    So the *universal* reading of [SliceRank.GroundBounded] — "every
    sunflower-free [m]-uniform family lives on [c*m] points" — is **false
    for every [c]**. What survives is the existence reading the definition
    actually has: some family of each achievable size can be *realised* on
    [c*m] points. That distinction is load-bearing.

    The instance at [k = 3] is small enough to check outright: eight
    triples that genuinely use fourteen points, against
    [ground_bounded_needs_c_at_least_four]'s [4*3 = 12]. The construction
    at every [k <= 6] is verified in `rust/tests/ground_set.rs`.

    Note also which way this cuts for the measurements. The [N(m,g)] table
    is the *largest family on [g] points*, which is exactly the quantity
    the existence reading needs; it is not the quantity [FPPTZ24] bounds
    below. The two do not conflict. *)

Definition tree_paths_three : Family :=
  [[0; 2; 6]; [0; 2; 7]; [0; 3; 8]; [0; 3; 9];
   [1; 4; 10]; [1; 4; 11]; [1; 5; 12]; [1; 5; 13]].

Lemma tree_paths_three_no_sunflower : ~ ContainsKSunflower 3 tree_paths_three.
Proof.
  intro Hc.
  pose proof (sunflower3b_sound tree_paths_three Hc) as E.
  vm_compute in E; discriminate.
Qed.

Lemma tree_paths_three_grounded : Grounded tree_paths_three (seq 0 14).
Proof.
  unfold Grounded.
  apply (proj1 (groundedb_correct tree_paths_three (seq 0 14))).
  vm_compute; reflexivity.
Qed.

(** And it does not fit on thirteen: the last member uses point 13. *)

Lemma tree_paths_three_needs_fourteen : ~ Grounded tree_paths_three (seq 0 13).
Proof.
  intro HG.
  assert (Hin : In [1; 5; 13] tree_paths_three) by (vm_compute; tauto).
  specialize (HG _ Hin 13 ltac:(vm_compute; tauto)).
  rewrite in_seq in HG; lia.
Qed.

Theorem the_universal_ground_reading_is_false :
  Uniform 3 tree_paths_three
  /\ Distinct tree_paths_three
  /\ ~ ContainsKSunflower 3 tree_paths_three
  /\ Grounded tree_paths_three (seq 0 14)
  /\ ~ Grounded tree_paths_three (seq 0 13)
  /\ 4 * 3 < 14.
Proof.
  split; [apply uniformb_correct; vm_compute; reflexivity|].
  split; [apply distinctb_correct; vm_compute; reflexivity|].
  split; [exact tree_paths_three_no_sunflower|].
  split; [exact tree_paths_three_grounded|].
  split; [exact tree_paths_three_needs_fourteen | lia].
Qed.

(** ** The row at ten points, both ends

    [SliceRank.v] names [N(3,10)] as the value the general row turns on,
    and records that the search does not decide it. The upper end is
    [n_three_ten_at_most_twenty] above. The lower end is this family,
    found by the SAT encoding in [rust/src/sat.rs] and re-verified by an
    independent checker before it was written down: sixteen 3-sets on ten
    points, sunflower-free, degrees [(6,6,6,6,4,4,4,4,4,4)].

    Its shape is worth reading. The first four members are *all* the
    triples of [{0,1,2,3}] — which is exactly
    [Compression.compressed_bound]'s extremal family at [m = 3], the
    largest a compressed family may be. The other twelve are the pairs
    from [{0,1}] joined to a triangle on [{4,5,6}] and the pairs from
    [{2,3}] joined to a triangle on [{7,8,9}]. Four plus six plus six.

    So the general row is **still climbing at ten points**: 14 at nine,
    at least 16 at ten. That is the measurement §7 of the roadmap asks
    for, and it goes the way that hurts [GroundBounded]. *)

Definition ground10_max : Family :=
  [[0; 1; 2]; [0; 1; 3]; [0; 2; 3]; [1; 2; 3];
   [0; 4; 5]; [1; 4; 5]; [0; 4; 6]; [1; 4; 6]; [0; 5; 6]; [1; 5; 6];
   [2; 7; 8]; [3; 7; 8]; [2; 7; 9]; [3; 7; 9]; [2; 8; 9]; [3; 8; 9]].

Lemma ground10_max_no_sunflower : ~ ContainsKSunflower 3 ground10_max.
Proof.
  intro Hc.
  pose proof (sunflower3b_sound ground10_max Hc) as E.
  vm_compute in E; discriminate.
Qed.

Lemma ground10_max_is_grounded : Grounded ground10_max (seq 0 10).
Proof.
  unfold Grounded.
  apply (proj1 (groundedb_correct ground10_max (seq 0 10))).
  vm_compute; reflexivity.
Qed.

(** [N(3,10)] is between sixteen and twenty, and both ends are theorems.
    The gap is four; the search closed neither end. *)

Theorem n_three_ten_between_sixteen_and_twenty :
  (Uniform 3 ground10_max /\ Distinct ground10_max
   /\ Grounded ground10_max (seq 0 10) /\ length (seq 0 10) = 10
   /\ ~ ContainsKSunflower 3 ground10_max /\ length ground10_max = 16)
  /\ (forall (U : list nat) (F : Family),
        NoDup U -> length U <= 10 ->
        Uniform 3 F -> Distinct F -> Grounded F U ->
        ~ ContainsKSunflower 3 F -> length F <= 20).
Proof.
  split; [| exact n_three_ten_at_most_twenty].
  split; [apply uniformb_correct; vm_compute; reflexivity|].
  split; [apply distinctb_correct; vm_compute; reflexivity|].
  split; [exact ground10_max_is_grounded|].
  split; [vm_compute; reflexivity|].
  split; [exact ground10_max_no_sunflower | vm_compute; reflexivity].
Qed.

(** It beats the nine-point family, so the row really did move. *)

Corollary the_general_row_climbs_from_nine_to_ten :
  length SliceRank.ground9_max = 14 /\ length ground10_max = 16.
Proof. split; vm_compute; reflexivity. Qed.

(** ** The polynomial method is not what makes the ground bound work

    [SliceRank.v] presents [GroundBounded] as the one hypothesis standing
    between Naslund–Sawin and the conjecture at [k = 3]. Reading the
    literature turned that framing around. [FPPTZ24] (the "Odd-sunflowers"
    paper, JCTA 2024) records a conjecture of exactly this shape — the
    number of *base elements* of a sunflower-free [k]-uniform family is at
    most [c^k] — and reports, crediting Zach Hunter, that it is
    **equivalent** to the Erdős–Rado conjecture. A ground-set framing of
    the problem is therefore known.

    Chasing that down exposes something the development had missed. The
    implication [GroundBounded c ==> conjecture] does not need the
    polynomial method **at all**. A family of distinct subsets of a
    [g]-point set has at most [2^g] members — pure counting — so a ground
    set of size [c*m] gives [2^(c*m) = (2^c)^m] directly.

    What Naslund–Sawin contributes is the constant: [1.89^g] against
    [2^g]. That is a real theorem and a better constant, and it is *not*
    what makes the implication work. Compare:

    - [SliceRank.bounded_ground_set_settles_k3]: needs
      [NaslundSawinBound], gives [(27^(c+1))^m];
    - [ground_bounded_settles_k3_by_counting] below: needs nothing,
      gives [(2^c)^m], which is smaller for every [c].

    So the honest reading of §7 is that the ground-set hypothesis is the
    whole content and the polynomial method is decoration on the
    constant. The axiom-free version is the one to quote. *)

Lemma sublists_length : forall l, length (sublists l) = 2 ^ length l.
Proof.
  induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite app_length, map_length, IH; lia.
Qed.

Lemma NoDup_map_inj_lists :
  forall (f : list nat -> list nat) (F : Family),
    NoDup F ->
    (forall A B, In A F -> In B F -> f A = f B -> A = B) ->
    NoDup (map f F).
Proof.
  intros f F; induction F as [|A F IH]; simpl; intros Hnd Hinj; [constructor|].
  inversion Hnd as [| ? ? Hni Hnd']; subst.
  constructor.
  - intro Hin; apply in_map_iff in Hin as [B [Hfb HB]].
    assert (E : A = B)
      by (apply Hinj; [left; reflexivity | right; exact HB | symmetry; exact Hfb]).
    subst B; contradiction.
  - apply IH; [exact Hnd'|].
    intros X Y HX HY; apply Hinj; right; assumption.
Qed.

(** Counting, and nothing more: a [Distinct] family of subsets of [U] has
    at most [2 ^ |U|] members. Each member is pinned by which points of
    [U] it contains, and [HallCore.sublists] enumerates the
    possibilities. *)

Theorem grounded_family_at_most_two_to_the_ground :
  forall (U : list nat) (F : Family),
    Distinct F -> Grounded F U -> length F <= 2 ^ length U.
Proof.
  intros U F Hd HG.
  assert (Hmem : forall A x, In A F -> (In x (filter (fun y => memb y A) U) <-> In x A)).
  { intros A x HA; split.
    - intro Hx; apply filter_In in Hx as [_ Hb]; apply memb_true_iff; exact Hb.
    - intro Hx; apply filter_In; split;
        [apply (HG A HA); exact Hx | apply memb_true_iff; exact Hx]. }
  assert (Hinj : forall A B, In A F -> In B F ->
             filter (fun y => memb y A) U = filter (fun y => memb y B) U -> A = B).
  { intros A B HA HB Heq.
    apply (SetNoDup_setEq_eq Hd HA HB); split; intros x Hx.
    - apply (Hmem B x HB); rewrite <- Heq; apply (Hmem A x HA); exact Hx.
    - apply (Hmem A x HA); rewrite Heq; apply (Hmem B x HB); exact Hx. }
  assert (Hnd : NoDup (map (fun A => filter (fun y => memb y A) U) F))
    by (apply NoDup_map_inj_lists;
        [apply SetNoDup_NoDup; exact Hd | exact Hinj]).
  assert (Hincl : incl (map (fun A => filter (fun y => memb y A) U) F) (sublists U)).
  { intros z Hz; apply in_map_iff in Hz as [A [E _]]; subst z;
      apply filter_in_sublists. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hle.
  rewrite map_length, sublists_length in Hle; exact Hle.
Qed.

(** And therefore, with no axiom and no polynomial method: *)

Theorem ground_bounded_settles_k3_by_counting :
  forall c, GroundBounded c ->
    forall m j, 1 <= m -> LowerBound m 3 j -> j <= (2 ^ c) ^ m.
Proof.
  intros c HGB m j Hm HL.
  destruct (HGB m j Hm HL) as [F [U [HunF [HdF [HlenF [HnoF [HndU [HG Hu]]]]]]]].
  assert (Hb : length F <= 2 ^ length U)
    by (apply grounded_family_at_most_two_to_the_ground with (U := U); assumption).
  assert (Hmono : 2 ^ length U <= 2 ^ (c * m))
    by (apply Nat.pow_le_mono_r; lia).
  rewrite <- Nat.pow_mul_r; lia.
Qed.

(** ** A lower bound on the constant [GroundBounded] could have

    The two halves of this file meet here, and they refute something.
    [SliceRank.GroundBounded c] asserts that an extremal sunflower-free
    [m]-uniform family can be realised on [c*m] points. At [m = 3] the
    development knows a family of twenty members
    ([Intersecting.lower_bound_3_3_20], the doubled [iota(3)]), and it
    knows [N(3,g) <= 2g] outright. Twenty members on [3c] points needs
    [20 <= 6c].

    So **[GroundBounded c] is false for every [c <= 3]** — proved, not
    measured. §7 of the roadmap records the measurement that the
    [m = 3] row is "still climbing at [g = 3m]"; this is the same fact
    with the search taken out of it, and it is stronger, because the
    search never decided [N(3,10)] at all.

    What it does not do is refute the hypothesis. [c = 4] is untouched,
    and [bounded_ground_set_settles_k3] at [c = 4] still gives the
    conjecture at [k = 3], with a worse constant. What it removes is the
    reading of the two plateaus at [2m] and [3m] as evidence for a small
    [c]: at uniformity 3 the constant is at least 4. *)

Theorem ground_bounded_needs_c_at_least_four :
  forall c, GroundBounded c -> 4 <= c.
Proof.
  intros c HGB.
  destruct (HGB 3 20 ltac:(lia) lower_bound_3_3_20)
    as [F [U [HunF [HdF [HlenF [HnoF [HndU [HG Hu]]]]]]]].
  pose proof (three_uniform_ground_bound U F HndU HunF HdF HG HnoF) as Hb.
  lia.
Qed.

Corollary ground_bounded_three_is_false : ~ GroundBounded 3.
Proof. intro H; pose proof (ground_bounded_needs_c_at_least_four _ H); lia. Qed.

(** The same for [c = 1] and [c = 2], which is where the two measured
    plateaus sit — so neither of them is the constant. *)

Corollary ground_bounded_two_is_false : ~ GroundBounded 2.
Proof. intro H; pose proof (ground_bounded_needs_c_at_least_four _ H); lia. Qed.

(** ** The hypothesis, pointed at intersecting families

    Deliberately *weaker* than what the measurement supports at [b = 3].
    All that is asked here is that *some* equally large
    sunflower-free family fits on [c * b] points — which is all the
    polynomial method consumes, and assuming less makes the theorem
    below say more.

    Compare [SliceRank.GroundBounded], which is the same demand made of
    every sunflower-free family. The two differ by the word
    "intersecting", and [IotaRate.conjecture_k_3_iff_iota_exponential] is
    why that word costs nothing.

    **Two corrections from [coq/Product.v], both by the cone.** First, the
    *universal* reading — "the extremal intersecting sunflower-free family
    literally lives on [O(b)] points" — is **false**, exactly as it is for
    [GroundBounded]: coning the tree-path family gives an intersecting
    3-sunflower-free [b]-uniform family with [2^(b-1)] members on
    [2^b - 1] points, every one used
    ([Product.the_universal_iota_ground_reading_is_false]). This paragraph
    said otherwise and was wrong. Second, the two hypotheses are **not**
    independent: [Product.ground_bounded_implies_iota_ground_bounded] is
    immediate and [Product.iota_ground_bounded_bounds_the_general_row] is
    the converse with the uniformity shifted by one. See
    [both_ground_hypotheses_settle_k3] below and [docs/roadmap.md] §11.2. *)

Definition IotaGroundBounded (c : nat) : Prop :=
  forall b (H : Family),
    1 <= b -> Uniform b H -> Distinct H -> Intersecting H ->
    ~ ContainsKSunflower 3 H ->
    exists (H' : Family) (U : list nat),
      Distinct H'
      /\ length H' = length H
      /\ ~ ContainsKSunflower 3 H'
      /\ NoDup U /\ Grounded H' U /\ length U <= c * b.

(** ** The composition

    A ground-set bound on intersecting families, plus Naslund–Sawin,
    bounds [iota] exponentially — and by the equivalence that *is* the
    conjecture at [k = 3]. *)

Theorem iota_ground_bounded_gives_exponential :
  NaslundSawinBound ->
  forall c, 1 <= c -> IotaGroundBounded c ->
    forall b, 1 <= b -> IotaAtMost b ((27 ^ (c + 1)) ^ b).
Proof.
  intros NS c Hc HIGB b Hb H HU HD HI Hno.
  destruct (HIGB b H Hb HU HD HI Hno)
    as [H' [U [HD' [Hlen [Hno' [HndU [HG Hu]]]]]]].
  pose proof (ns_bound_to_exponential NS c b H' U Hc Hb HD' Hno' HndU HG Hu) as Hb2.
  lia.
Qed.

Theorem iota_ground_bounded_is_exponential :
  NaslundSawinBound ->
  forall c, 1 <= c -> IotaGroundBounded c -> IotaExponential.
Proof.
  intros NS c Hc HIGB.
  exists (27 ^ (c + 1)).
  exact (iota_ground_bounded_gives_exponential NS c Hc HIGB).
Qed.

(** **The statement this file exists for.** *)

Theorem iota_ground_bounded_settles_k3 :
  NaslundSawinBound ->
  forall c, 1 <= c -> IotaGroundBounded c -> sunflower_conjecture_k_3.
Proof.
  intros NS c Hc HIGB.
  apply (proj2 conjecture_k_3_iff_iota_exponential).
  exact (iota_ground_bounded_is_exponential NS c Hc HIGB).
Qed.

(** And the same conclusion in the [LowerBound]-complement form, which is
    what a search would actually contradict. *)

Corollary iota_ground_bounded_excludes_lower_bounds :
  NaslundSawinBound ->
  forall c, 1 <= c -> IotaGroundBounded c ->
    forall m j, 1 <= m -> (2 * 27 ^ (c + 1)) ^ m < j -> ~ LowerBound m 3 j.
Proof.
  intros NS c Hc HIGB m j Hm Hj [F [HU [HD [Hlen Hno]]]].
  (* [g <= 2b*iota] at the bound just proved, then the factor absorbed
     into the base. The constant doubles; see the scoping note in
     [docs/roadmap.md] on not chasing it. *)
  pose proof (g_le_iota_scaled m ((27 ^ (c + 1)) ^ m) Hm
                (iota_ground_bounded_gives_exponential NS c Hc HIGB m Hm)
                F HU HD Hno) as Hb.
  pose proof (scaled_power_absorbs m (27 ^ (c + 1)) Hm) as Habs.
  lia.
Qed.

(** ** The two hypotheses side by side

    Both are one sentence, both would settle [k = 3], and the difference
    between them is a single word.

    **The remark that used to be here is withdrawn.** It said "what
    separates them is not their logical strength — neither implies the
    other — but that one of them has a measurement behind it". The first
    half is false: [Product.ground_bounded_implies_iota_ground_bounded]
    proves one direction outright, and the cone gives the other up to a
    shift in the uniformity
    ([Product.the_two_ground_hypotheses_are_not_independent],
    [Audit.the_ground_hypotheses_are_not_independent_after_all]). So the
    two measurements — the flat [iota(3,g)] row and the still-climbing
    [N(3,g)] row — are measurements of the same question at two
    uniformities, and they pull in opposite directions. *)

Theorem iota_ground_bounded_gives_exponential_by_counting :
  forall c, IotaGroundBounded c ->
    forall b, 1 <= b -> IotaAtMost b ((2 ^ c) ^ b).
Proof.
  intros c HIGB b Hb H HU HD HI Hno.
  destruct (HIGB b H Hb HU HD HI Hno)
    as [H' [U [HD' [Hlen [Hno' [HndU [HG Hu]]]]]]].
  assert (Hb2 : length H' <= 2 ^ length U)
    by (apply grounded_family_at_most_two_to_the_ground with (U := U); assumption).
  assert (Hmono : 2 ^ length U <= 2 ^ (c * b))
    by (apply Nat.pow_le_mono_r; lia).
  rewrite <- Nat.pow_mul_r; lia.
Qed.

Theorem iota_ground_bounded_settles_k3_without_the_axiom :
  forall c, 1 <= c -> IotaGroundBounded c -> sunflower_conjecture_k_3.
Proof.
  intros c Hc HIGB.
  apply (proj2 conjecture_k_3_iff_iota_exponential).
  exists (2 ^ c); intros b Hb.
  apply (iota_ground_bounded_gives_exponential_by_counting c HIGB b Hb).
Qed.

Theorem both_ground_hypotheses_settle_k3 :
  NaslundSawinBound ->
  forall c, 1 <= c ->
    (GroundBounded c -> forall m j, 1 <= m -> LowerBound m 3 j
                                    -> j <= (27 ^ (c + 1)) ^ m)
    /\ (IotaGroundBounded c -> sunflower_conjecture_k_3).
Proof.
  intros NS c Hc; split.
  - intros HGB; exact (bounded_ground_set_settles_k3 NS c Hc HGB).
  - intros HIGB; exact (iota_ground_bounded_settles_k3 NS c Hc HIGB).
Qed.
