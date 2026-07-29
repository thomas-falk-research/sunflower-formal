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
From Sunflower Require Import Sets Sunflower LowerBound Conjecture Spread
     Reflect F23 Intersecting IotaRate SliceRank.
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

(** ** The hypothesis, pointed at intersecting families

    Deliberately *weaker* than what the measurement supports. The data
    says the extremal intersecting sunflower-free family literally lives
    on [O(b)] points, which would give a witness that is itself uniform
    and intersecting. All that is asked here is that *some* equally large
    sunflower-free family fits on [c * b] points — which is all the
    polynomial method consumes, and assuming less makes the theorem
    below say more.

    Compare [SliceRank.GroundBounded], which is the same demand made of
    every sunflower-free family. That one is not supported by the
    measurements and this one is; the two differ by the word
    "intersecting", and [IotaRate.conjecture_k_3_iff_iota_exponential] is
    why that word costs nothing. *)

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
    between them is a single word. What separates them is not their
    logical strength — neither implies the other — but that one of them
    has a measurement behind it. *)

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
