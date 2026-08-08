(** * HiltonMilner.v -- the spread Hilton–Milner family, and the exact
    boundary of star extremality.

    Every Rao-spread family in this development before this file is a
    *finite witness*, written out by hand and checked by reflection.
    This file builds the first **parametric** one: a family
    [HM m r] defined for all [m] and [r], whose spreadness is a theorem
    with an induction in it rather than a [vm_compute].

    ** The object

    Partition an initial segment of the naturals into consecutive blocks

    <<
      E   = seq 0 m          the special set, m points
      W   = {m}              the apex, w := m
      Y_j = r points each    j = 0 .. m-3
    >>

    and let [HM m r] be [E] together with every transversal
    [{i, w} ∪ {y_0, ..., y_{m-3}}], [i ∈ E], [y_j ∈ Y_j]. This is the
    Hilton–Milner shape — one set off to the side, and the star at an
    apex outside it, thinned to a grid so that it is spread — and it has

    >  |HM m r| = m·r^(m-2) + 1

    members. [CrossRefined.hm16] is [HM 3 5] up to relabelling,
    written out by hand before the family it belongs to had a name.

    ** The two inequalities, and why they meet at one point

    The apex degree is [deg {w} = m·r^(m-2)], which the spread condition
    caps at [r^(m-1)]. So

    >  HM m r is Rao(r)-spread   iff   r >= m,

    and this is the *only* obstruction. Many other sets are tight —
    [{i,w}] has degree [r^(m-2)] against a ceiling of [r^(m-2)] — but
    they are tight at *every* [r], so they impose no condition; the only
    other place [m] is weighed against a power of [r] is the sets that
    avoid both the apex and the special set, and they ask only for
    [m <= r^2]. On the other side,

    >  |HM m r| > r^(m-1)   iff   m >= r.

    Both hold at exactly one value of [r], namely [r = m], where the apex
    degree is [m^(m-1) = r^(m-1)] — sitting precisely on the ceiling — and
    the family has [m^(m-1) + 1] members, precisely one more than the star.
    Hence

    >  **[~ StarExtremalAt m m] for every [m >= 2]**,

    which is [not_star_extremal_at_m_m] below. Two consequences:

    - the threshold [r >= m+1] in
      [CrossIntersecting.two_cover_star_extremal] is **sharp** — [HM m m]
      has a two-point cover, so the hypothesis cannot be weakened to
      [r >= m] ([two_cover_threshold_is_sharp]);
    - no [r <= m] can be a star-extremality threshold at uniformity [m]
      ([star_extremal_needs_r_above_m]).

    ** What is *not* proved here

    That [StarExtremalAt m r] holds for some [r], and in particular at
    [r = m+1]; the [tau >= 3] half of that is open at every [m >= 4].
    Nor is [StarExtremalAt m ·] known to be monotone in [r] — [RaoSpread]
    weakens as [r] grows while the bound [r^(m-1)] grows too, and neither
    dominates. Every statement below is therefore at one specific [r].
    See [docs/roadmap.md] §28. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower Spread Reflect
     CliqueLowerBound SpreadThreshold TwoCover TauThree CrossIntersecting
     CrossRefined.
Import ListNotations.

(** ** Transversal families

    [tstep B F] prefixes each point of [B] to each member of [F];
    [blocks bs] iterates it, so that [blocks [B_0; ...; B_{k-1}]] is the
    list of all transversals [[x_0; ...; x_{k-1}]], [x_i ∈ B_i]. *)

Definition tstep (B : list nat) (F : Family) : Family :=
  flat_map (fun x => map (cons x) F) B.

Fixpoint blocks (bs : list (list nat)) : Family :=
  match bs with
  | [] => [[]]
  | B :: bs' => tstep B (blocks bs')
  end.

Lemma tstep_cons :
  forall x B F, tstep (x :: B) F = map (cons x) F ++ tstep B F.
Proof. reflexivity. Qed.

Lemma tstep_length :
  forall B F, length (tstep B F) = length B * length F.
Proof.
  intros B F; induction B as [|x B IH]; simpl; [reflexivity|].
  rewrite app_length, map_length, IH; reflexivity.
Qed.

Lemma in_tstep_inv :
  forall A B F, In A (tstep B F) ->
    exists x A', In x B /\ In A' F /\ A = x :: A'.
Proof.
  intros A B F H; induction B as [|x B IH]; simpl in H; [contradiction|].
  apply in_app_or in H as [H|H].
  - apply in_map_iff in H as [A' [E HA']].
    exists x, A'; repeat split; [left; reflexivity | exact HA' | symmetry; exact E].
  - destruct (IH H) as [y [A' [Hy [HA' E]]]].
    exists y, A'; repeat split; [right; exact Hy | exact HA' | exact E].
Qed.

(** *** Degree of a transversal step

    The one identity everything rests on: prefixing [x] to every member
    turns "[T] is contained in it" into "[T] minus [x] is contained in
    the tail". *)

Lemma containsb_cons_rem :
  forall T x A, containsb T (x :: A) = containsb (rem_elt x T) A.
Proof.
  intros T x A.
  destruct (containsb T (x :: A)) eqn:E1; destruct (containsb (rem_elt x T) A) eqn:E2;
    try reflexivity.
  - exfalso; rewrite containsb_true_iff in E1.
    assert (E3 : containsb (rem_elt x T) A = true).
    { apply containsb_true_iff; intros y Hy.
      rewrite in_rem_iff in Hy; destruct Hy as [HyT Hyx].
      destruct (E1 y HyT) as [E|E]; [congruence | exact E]. }
    congruence.
  - exfalso; rewrite containsb_true_iff in E2.
    assert (E3 : containsb T (x :: A) = true).
    { apply containsb_true_iff; intros y Hy.
      destruct (Nat.eq_dec y x) as [Ey|Ny]; [left; symmetry; exact Ey|].
      right; apply E2, in_rem_iff; split; [exact Hy | exact Ny]. }
    congruence.
Qed.

Lemma deg_cone :
  forall T x F, deg T (map (cons x) F) = deg (rem_elt x T) F.
Proof.
  intros T x F; unfold deg.
  induction F as [|A F IH]; simpl; [reflexivity|].
  rewrite containsb_cons_rem.
  destruct (containsb (rem_elt x T) A); simpl; rewrite IH; reflexivity.
Qed.

(** A point that no member carries kills the degree of any [T] through
    it. This is what makes a block "fresh" for the families below it. *)

Lemma deg_zero_of_fresh :
  forall y T F, In y T -> (forall A, In A F -> ~ In y A) -> deg T F = 0.
Proof.
  intros y T F HyT Hfresh; unfold deg.
  destruct (filter (containsb T) F) as [|A L] eqn:Ef; [reflexivity | exfalso].
  assert (HA : In A (filter (containsb T) F)) by (rewrite Ef; left; reflexivity).
  apply filter_In in HA as [HAF Hc].
  apply containsb_true_iff in Hc.
  exact (Hfresh A HAF (Hc y HyT)).
Qed.

Definition BlockFresh (B : list nat) (F : Family) : Prop :=
  forall A, In A F -> forall y, In y B -> ~ In y A.

(** *** The two cases of a transversal step

    A block the test set misses multiplies the degree by the block size;
    a block it meets once selects a single term and deletes that point. *)

Lemma tstep_deg_miss :
  forall T B F,
    (forall x, In x B -> ~ In x T) ->
    deg T (tstep B F) = length B * deg T F.
Proof.
  intros T B F Hmiss; induction B as [|x B IH]; simpl; [reflexivity|].
  rewrite deg_app, deg_cone.
  assert (Ex : deg (rem_elt x T) F = deg T F).
  { apply deg_setEq; [apply rem_Subset|].
    intros y Hy; apply in_rem_iff; split; [exact Hy|].
    intro E; subst y; exact (Hmiss x (or_introl eq_refl) Hy). }
  rewrite Ex, IH by (intros y Hy; apply Hmiss; right; exact Hy).
  lia.
Qed.

Lemma tstep_deg_hit :
  forall T B F x0,
    NoDup B -> In x0 B -> In x0 T -> BlockFresh B F ->
    deg T (tstep B F) = deg (rem_elt x0 T) F.
Proof.
  intros T B F x0 HB; revert T; induction HB as [|x B Hx HB IH]; intros T Hin HxT Hfresh;
    [contradiction|].
  rewrite tstep_cons, deg_app, deg_cone.
  destruct (Nat.eq_dec x x0) as [E|N].
  - subst x.
    assert (Hz : deg T (tstep B F) = 0).
    { apply (@deg_zero_of_fresh x0 T _ HxT).
      intros A HA; destruct (in_tstep_inv _ _ _ HA) as [y [A' [HyB [HA' EA]]]].
      subst A; simpl; intros [Ey|HyA'].
      - subst y; contradiction.
      - exact (Hfresh A' HA' x0 (or_introl eq_refl) HyA'). }
    lia.
  - assert (Hx0B : In x0 B) by (destruct Hin as [E|H]; [congruence | exact H]).
    assert (Hz : deg (rem_elt x T) F = 0).
    { apply (@deg_zero_of_fresh x0 _ F).
      - apply in_rem_iff; split; [exact HxT | congruence].
      - intros A HA; exact (Hfresh A HA x0 (or_intror Hx0B)). }
    rewrite Hz, (IH T Hx0B HxT); [lia|].
    intros A HA y HyB; exact (Hfresh A HA y (or_intror HyB)).
Qed.

(** ** The grid: [k] consecutive blocks of [r] points each *)

Fixpoint gridblocks (base k r : nat) : list (list nat) :=
  match k with
  | 0 => []
  | S k' => seq base r :: gridblocks (base + r) k' r
  end.

Definition grid (base k r : nat) : Family := blocks (gridblocks base k r).

Lemma grid_zero : forall base r, grid base 0 r = [[]].
Proof. reflexivity. Qed.

Lemma grid_succ :
  forall base k r,
    grid base (S k) r = tstep (seq base r) (grid (base + r) k r).
Proof. reflexivity. Qed.

Lemma grid_length : forall base k r, length (grid base k r) = r ^ k.
Proof.
  intros base k; revert base; induction k as [|k IH]; intros base r; [reflexivity|].
  rewrite grid_succ, tstep_length, seq_length, IH; reflexivity.
Qed.

(** Every member is a [k]-point set living strictly inside
    [[base, base + k·r)], one point per block. *)

Lemma grid_bounds :
  forall base k r A, In A (grid base k r) ->
    forall y, In y A -> base <= y /\ y < base + k * r.
Proof.
  intros base k; revert base; induction k as [|k IH]; intros base r A HA y Hy.
  - destruct HA as [E|[]]; subst A; contradiction.
  - rewrite grid_succ in HA.
    destruct (in_tstep_inv _ _ _ HA) as [x [A' [HxB [HA' EA]]]].
    subst A; destruct Hy as [Ey|HyA'].
    + subst y; apply in_seq in HxB; lia.
    + destruct (IH (base + r) r A' HA' y HyA'); lia.
Qed.

Lemma grid_fresh_below :
  forall base k r y, y < base -> forall A, In A (grid base k r) -> ~ In y A.
Proof.
  intros base k r y Hy A HA HyA.
  destruct (grid_bounds base k r A HA y HyA); lia.
Qed.

Lemma grid_member_length :
  forall base k r A, In A (grid base k r) -> length A = k.
Proof.
  intros base k; revert base; induction k as [|k IH]; intros base r A HA.
  - destruct HA as [E|[]]; subst A; reflexivity.
  - rewrite grid_succ in HA.
    destruct (in_tstep_inv _ _ _ HA) as [x [A' [_ [HA' EA]]]].
    subst A; simpl; f_equal; exact (IH (base + r) r A' HA').
Qed.

Lemma grid_member_nodup :
  forall base k r A, In A (grid base k r) -> NoDup A.
Proof.
  intros base k; revert base; induction k as [|k IH]; intros base r A HA.
  - destruct HA as [E|[]]; subst A; constructor.
  - rewrite grid_succ in HA.
    destruct (in_tstep_inv _ _ _ HA) as [x [A' [HxB [HA' EA]]]].
    subst A; apply in_seq in HxB; constructor.
    + intro HxA'; destruct (grid_bounds (base + r) k r A' HA' x HxA'); lia.
    + exact (IH (base + r) r A' HA').
Qed.

Lemma grid_nonempty :
  forall base k r, 1 <= r -> exists g, In g (grid base k r).
Proof.
  intros base k r Hr.
  remember (grid base k r) as G eqn:EG.
  destruct G as [|g G0]; [exfalso | exists g; left; reflexivity].
  assert (Hl : length (grid base k r) = r ^ k) by apply grid_length.
  rewrite <- EG in Hl; simpl in Hl.
  assert (1 <= r ^ k) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  lia.
Qed.

Lemma grid_uniform : forall base k r, Uniform k (grid base k r).
Proof.
  intros base k r; apply Forall_forall; intros A HA; split;
    [exact (grid_member_length base k r A HA)
    | exact (grid_member_nodup base k r A HA)].
Qed.

(** *** The degree bound, in multiplicative form

    Stated as [deg T · r^|T| <= r^k] rather than
    [deg T <= r^(k-|T|)] so that truncated subtraction never appears:
    the [|T| > k] case is then automatic rather than a separate argument.
    Both readings are the same statement whenever [|T| <= k]. *)

Theorem grid_deg_mul :
  forall base k r T,
    NoDup T -> deg T (grid base k r) * r ^ (length T) <= r ^ k.
Proof.
  intros base k; revert base; induction k as [|k IH]; intros base r T HT.
  - rewrite grid_zero; simpl.
    destruct T as [|t T0]; simpl; [lia|].
    unfold deg; simpl; unfold containsb; simpl; unfold memb; simpl.
    destruct (in_dec_nat t []) as [[]|_]; simpl; lia.
  - rewrite grid_succ.
    assert (Hfresh : BlockFresh (seq base r) (grid (base + r) k r)).
    { intros A HA y HyB; apply in_seq in HyB.
      intro HyA; destruct (grid_bounds (base + r) k r A HA y HyA); lia. }
    destruct (disjointb T (seq base r)) eqn:ED.
    + (* the block is missed: the degree picks up a factor [r] *)
      apply disjointb_correct in ED.
      rewrite (@tstep_deg_miss T (seq base r) (grid (base + r) k r)
                 (fun x Hx HxT => ED x HxT Hx)), seq_length.
      pose proof (IH (base + r) r T HT) as Hrec.
      simpl; nia.
    + (* the block is hit: one term survives and one point is deleted *)
      apply disjointb_false_iff in ED as [x0 [Hx0T Hx0B]].
      rewrite (@tstep_deg_hit T (seq base r) (grid (base + r) k r) x0
                 (seq_NoDup r base) Hx0B Hx0T Hfresh).
      assert (Hlen : length T = S (length (rem_elt x0 T))).
      { rewrite (@length_rem_elt_in x0 T HT Hx0T).
        destruct T as [|t T0]; simpl in *; [contradiction | lia]. }
      pose proof (IH (base + r) r (rem_elt x0 T) (@rem_NoDup x0 T HT)) as Hrec.
      rewrite Hlen, !Nat.pow_succ_r'; nia.
Qed.

(** ** The family

    [hme m] is the special set, [hmw m] the apex, [hmstar m r] the
    thinned star through the apex, and [HM m r] the two together. *)

Definition hmw (m : nat) : nat := m.
Definition hme (m : nat) : list nat := seq 0 m.

Definition hmstar (m r : nat) : Family :=
  tstep (hme m) (tstep [hmw m] (grid (S m) (m - 2) r)).

Definition HM (m r : nat) : Family := hme m :: hmstar m r.

Lemma hmstar_length :
  forall m r, length (hmstar m r) = m * r ^ (m - 2).
Proof.
  intros m r; unfold hmstar, hme.
  rewrite !tstep_length, seq_length, grid_length; simpl; lia.
Qed.

Theorem HM_length : forall m r, length (HM m r) = m * r ^ (m - 2) + 1.
Proof. intros m r; simpl; rewrite hmstar_length; lia. Qed.

(** Every member of the star is [i :: w :: g] with [i] in the special
    set and [g] in the grid — the shape every argument below uses. *)

Lemma hmstar_shape :
  forall m r A, In A (hmstar m r) ->
    exists i g, In i (hme m) /\ In g (grid (S m) (m - 2) r)
                /\ A = i :: hmw m :: g.
Proof.
  intros m r A HA; unfold hmstar in HA.
  destruct (in_tstep_inv _ _ _ HA) as [i [A1 [Hi [HA1 EA]]]].
  destruct (in_tstep_inv _ _ _ HA1) as [w [g [Hw [Hg EA1]]]].
  destruct Hw as [Ew|[]]; subst w.
  exists i, g; repeat split; [exact Hi | exact Hg | subst; reflexivity].
Qed.

Lemma hme_lt : forall m y, In y (hme m) -> y < m.
Proof. intros m y H; unfold hme in H; apply in_seq in H; lia. Qed.

Lemma hme_length : forall m, length (hme m) = m.
Proof. intro m; unfold hme; apply seq_length. Qed.

Lemma hme_nodup : forall m, NoDup (hme m).
Proof. intro m; unfold hme; apply seq_NoDup. Qed.

Theorem HM_uniform : forall m r, 2 <= m -> Uniform m (HM m r).
Proof.
  intros m r Hm; apply Forall_forall; intros A HA.
  destruct HA as [EA|HA].
  - subst A; split; [apply seq_length | apply seq_NoDup].
  - destruct (hmstar_shape m r A HA) as [i [g [Hi [Hg EA]]]]; subst A.
    assert (Hi' : i < m) by (apply hme_lt; exact Hi).
    assert (Hglen : length g = m - 2) by (apply (grid_member_length (S m) (m-2) r); exact Hg).
    assert (Hgb : forall y, In y g -> S m <= y)
      by (intros y Hy; destruct (grid_bounds (S m) (m-2) r g Hg y Hy); lia).
    split.
    + simpl; rewrite Hglen; lia.
    + constructor.
      * simpl; intros [E|Hin]; unfold hmw in *; [lia|]. specialize (Hgb i Hin); lia.
      * constructor.
        -- intro Hin; specialize (Hgb (hmw m) Hin); unfold hmw in *; lia.
        -- exact (grid_member_nodup (S m) (m-2) r g Hg).
Qed.

(** Two members of the star share the apex; the special set meets each
    star member in its first point. No hypothesis on [r]. *)

Theorem HM_intersecting :
  forall m r, 1 <= m ->
    forall C D, In C (HM m r) -> In D (HM m r) -> exists x, In x C /\ In x D.
Proof.
  intros m r Hm C D HC HD.
  assert (Hstar : forall A, In A (hmstar m r) ->
                   In (hmw m) A /\ exists i, In i (hme m) /\ In i A).
  { intros A HA; destruct (hmstar_shape m r A HA) as [i [g [Hi [_ EA]]]]; subst A.
    split; [right; left; reflexivity|].
    exists i; split; [exact Hi | left; reflexivity]. }
  destruct HC as [EC|HC]; destruct HD as [ED|HD].
  - subst C D; exists 0; unfold hme; split; apply in_seq; lia.
  - subst C; destruct (Hstar D HD) as [_ [i [Hi HiD]]]; exists i; split; assumption.
  - subst D; destruct (Hstar C HC) as [_ [i [Hi HiC]]]; exists i; split; assumption.
  - destruct (Hstar C HC) as [HwC _]; destruct (Hstar D HD) as [HwD _].
    exists (hmw m); split; assumption.
Qed.

(** ** Spreadness, and the single inequality it needs

    The apex block contributes the factor [m] to [deg {w}] and the
    spread ceiling allows a factor [r]: [m <= r] is the whole content. *)
Lemma nodup_singleton : forall x : nat, NoDup [x].
Proof. intro x; constructor; [simpl; tauto | constructor]. Qed.

Lemma apex_fresh_grid :
  forall m r, BlockFresh [hmw m] (grid (S m) (m - 2) r).
Proof.
  intros m r A HA y Hy; destruct Hy as [Ey|[]]; subst y; unfold hmw.
  apply (grid_fresh_below (S m) (m - 2) r m); [lia | exact HA].
Qed.

Lemma hme_fresh_star :
  forall m r, BlockFresh (hme m) (tstep [hmw m] (grid (S m) (m - 2) r)).
Proof.
  intros m r A HA y Hy.
  destruct (in_tstep_inv _ _ _ HA) as [w [g [Hw [Hg EA]]]].
  destruct Hw as [Ew|[]]; subst w A.
  apply hme_lt in Hy.
  simpl; intros [E|Hin]; unfold hmw in *; [lia|].
  destruct (grid_bounds (S m) (m - 2) r g Hg y Hin); lia.
Qed.

(** The apex is never inside the special set, so a test set contained in
    the special set never selects the apex block. *)

Lemma apex_not_in_hme : forall m T, Subset T (hme m) -> ~ In (hmw m) T.
Proof.
  intros m T Hsub Hin.
  pose proof (hme_lt m (hmw m) (Hsub _ Hin)) as H; unfold hmw in *; lia.
Qed.

(** *** The star, bounded

    Multiplicative form throughout: [deg T · r^|T| <= r^m] is
    [deg T <= r^(m-|T|)] with no truncated subtraction anywhere, and it
    is what the grid induction already delivers. *)

Lemma miss_singleton :
  forall (w : nat) (T : list nat), ~ In w T -> forall x, In x [w] -> ~ In x T.
Proof. intros w T H x Hx; destruct Hx as [E|[]]; subst x; exact H. Qed.

Lemma mul_le_pair : forall a b c d : nat, a <= b -> c <= d -> a * c <= b * d.
Proof. intros a b c d H1 H2; apply Nat.mul_le_mono; assumption. Qed.

Lemma hmstar_deg_mul :
  forall m r T,
    2 <= m -> m <= r -> NoDup T ->
    deg T (hmstar m r) * r ^ (length T) <= r ^ m.
Proof.
  intros m r T Hm Hr HT.
  assert (Hr1 : 1 <= r) by lia.
  assert (Epow2 : r ^ m = r * r * r ^ (m - 2))
    by (rewrite <- Nat.mul_assoc, <- !Nat.pow_succ_r'; f_equal; lia).
  unfold hmstar.
  destruct (disjointb T (hme m)) eqn:ED.
  - (* the special block is missed: the factor [m] appears *)
    apply disjointb_correct in ED.
    rewrite (@tstep_deg_miss T (hme m) _ (fun x Hx HxT => ED x HxT Hx)), hme_length.
    destruct (in_dec_nat (hmw m) T) as [HwT|HwT].
    + (* apex present: [m <= r] is exactly what pays for it *)
      rewrite (@tstep_deg_hit T [hmw m] _ (hmw m) (nodup_singleton _)
                 (or_introl eq_refl) HwT (apex_fresh_grid m r)).
      set (T2 := rem_elt (hmw m) T).
      set (D := deg T2 (grid (S m) (m - 2) r)).
      assert (Hlen : length T = S (length T2))
        by (unfold T2; rewrite (@length_rem_elt_in (hmw m) T HT HwT);
            destruct T as [|t T0]; simpl in *; [contradiction | lia]).
      assert (Hg : D * r ^ (length T2) <= r ^ (m - 2))
        by (apply (grid_deg_mul (S m) (m - 2) r T2 (@rem_NoDup (hmw m) T HT))).
      assert (EP : r ^ (length T) = r * r ^ (length T2))
        by (rewrite Hlen, Nat.pow_succ_r'; reflexivity).
      rewrite EP, Epow2.
      replace (m * D * (r * r ^ length T2))
        with ((m * r) * (D * r ^ length T2)) by ring.
      apply mul_le_pair; [nia | exact Hg].
    + (* apex absent: [m <= r^2] is more than enough *)
      rewrite (@tstep_deg_miss T [hmw m] _
                 (miss_singleton (hmw m) T HwT)).
      set (D := deg T (grid (S m) (m - 2) r)).
      assert (Hg : D * r ^ (length T) <= r ^ (m - 2))
        by (apply (grid_deg_mul (S m) (m - 2) r T HT)).
      rewrite Epow2.
      replace (m * (length [hmw m] * D) * r ^ length T)
        with (m * (D * r ^ length T)) by (simpl; ring).
      apply mul_le_pair; [nia | exact Hg].
  - (* the special block is hit: no factor [m], and a point is deleted *)
    apply disjointb_false_iff in ED as [i0 [Hi0T Hi0E]].
    rewrite (@tstep_deg_hit T (hme m) _ i0 (hme_nodup m) Hi0E Hi0T
               (hme_fresh_star m r)).
    set (T1 := rem_elt i0 T).
    assert (HT1 : NoDup T1) by (apply (@rem_NoDup _ _ HT)).
    assert (Hlen1 : length T = S (length T1))
      by (unfold T1; rewrite (@length_rem_elt_in i0 T HT Hi0T);
          destruct T as [|t T0]; simpl in *; [contradiction | lia]).
    destruct (in_dec_nat (hmw m) T1) as [HwT1|HwT1].
    + rewrite (@tstep_deg_hit T1 [hmw m] _ (hmw m) (nodup_singleton _)
                 (or_introl eq_refl) HwT1 (apex_fresh_grid m r)).
      set (T2 := rem_elt (hmw m) T1).
      set (D := deg T2 (grid (S m) (m - 2) r)).
      assert (Hlen2 : length T1 = S (length T2))
        by (unfold T2; rewrite (@length_rem_elt_in (hmw m) T1 HT1 HwT1);
            destruct T1 as [|t T0]; simpl in *; [contradiction | lia]).
      assert (Hg : D * r ^ (length T2) <= r ^ (m - 2))
        by (apply (grid_deg_mul (S m) (m - 2) r T2 (@rem_NoDup (hmw m) T1 HT1))).
      assert (EP : r ^ (length T) = r * r * r ^ (length T2))
        by (rewrite Hlen1, Hlen2, <- Nat.mul_assoc, <- !Nat.pow_succ_r'; reflexivity).
      rewrite EP, Epow2.
      replace (D * (r * r * r ^ length T2))
        with ((r * r) * (D * r ^ length T2)) by ring.
      apply mul_le_pair; [lia | exact Hg].
    + rewrite (@tstep_deg_miss T1 [hmw m] _
                 (miss_singleton (hmw m) T1 HwT1)).
      set (D := deg T1 (grid (S m) (m - 2) r)).
      assert (Hg : D * r ^ (length T1) <= r ^ (m - 2))
        by (apply (grid_deg_mul (S m) (m - 2) r T1 HT1)).
      assert (EP : r ^ (length T) = r * r ^ (length T1))
        by (rewrite Hlen1, Nat.pow_succ_r'; reflexivity).
      rewrite EP, Epow2.
      replace (length [hmw m] * D * (r * r ^ length T1))
        with (r * (D * r ^ length T1)) by (simpl; ring).
      apply mul_le_pair; [nia | exact Hg].
Qed.

(** *** Inside the special set, where the extra member is felt

    [hme m] itself is the only member of [HM] outside the star, so it
    adds 1 to the degree of exactly those [T] it contains. Those [T] are
    also the ones where the star bound has a spare factor of [r], and the
    two facts are proved together because that is the only place they
    have to be reconciled. *)

Lemma hmstar_deg_inside :
  forall m r T,
    2 <= m -> m <= r -> NoDup T -> T <> [] -> Subset T (hme m) ->
    (deg T (hmstar m r) + 1) * r ^ (length T) <= r ^ m.
Proof.
  intros m r T Hm Hr HT Hne Hsub.
  assert (Hr2 : 2 <= r) by lia.
  assert (Hp2 : 1 <= r ^ (m - 2)) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  assert (Epow2 : r ^ m = r * r * r ^ (m - 2))
    by (rewrite <- Nat.mul_assoc, <- !Nat.pow_succ_r'; f_equal; lia).
  assert (Hlen_le : length T <= m)
    by (rewrite <- (seq_length m 0); apply NoDup_incl_length; [exact HT | exact Hsub]).
  destruct T as [|i0 T0]; [contradiction|].
  assert (Hi0E : In i0 (hme m)) by (apply Hsub; left; reflexivity).
  assert (HT1 : NoDup (rem_elt i0 (i0 :: T0))) by (apply (@rem_NoDup _ _ HT)).
  assert (Hsub1 : Subset (rem_elt i0 (i0 :: T0)) (hme m))
    by (intros y Hy; apply Hsub, (rem_Subset i0 (i0 :: T0)); exact Hy).
  assert (Hlen1 : length (i0 :: T0) = S (length (rem_elt i0 (i0 :: T0))))
    by (rewrite (@length_rem_elt_in i0 (i0 :: T0) HT (or_introl eq_refl)); simpl; lia).
  unfold hmstar.
  rewrite (@tstep_deg_hit (i0 :: T0) (hme m) _ i0 (hme_nodup m) Hi0E
             (or_introl eq_refl) (hme_fresh_star m r)).
  rewrite (@tstep_deg_miss (rem_elt i0 (i0 :: T0)) [hmw m] _
             (miss_singleton (hmw m) _ (apex_not_in_hme m _ Hsub1))).
  destruct (rem_elt i0 (i0 :: T0)) as [|y T1'] eqn:ET1.
  - (* one point of the special set: the whole grid is in its degree, and
       [r^(m-2) + 1 <= r^(m-1)] is what absorbs the extra member *)
    assert (Elen : length (i0 :: T0) = 1) by (rewrite Hlen1; reflexivity).
    rewrite deg_nil, grid_length, Elen, Epow2; simpl; nia.
  - (* two or more: the grid never meets the special set, so degree 0 *)
    assert (Hz : deg (y :: T1') (grid (S m) (m - 2) r) = 0).
    { apply (@deg_zero_of_fresh y (y :: T1') (grid (S m) (m - 2) r)
               (or_introl eq_refl)).
      intros A HA; apply (grid_fresh_below (S m) (m - 2) r y); [|exact HA].
      pose proof (hme_lt m y (Hsub1 y (or_introl eq_refl))); lia. }
    rewrite Hz, Nat.mul_0_r, Nat.add_0_l, Nat.mul_1_l.
    apply Nat.pow_le_mono_r; lia.
Qed.

Theorem HM_rao :
  forall m r, 2 <= m -> m <= r -> RaoSpread m (HM m r) r.
Proof.
  intros m r Hm Hr T HT Hne.
  assert (Hr1 : 1 <= r) by lia.
  destruct (le_lt_dec (length T) m) as [Hlen|Hlen];
    [| rewrite (@deg_zero_of_long m (HM m r) T (HM_uniform m r Hm) HT Hlen); lia].
  assert (Hpt : 1 <= r ^ (length T)) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  assert (Hsplit : deg T (HM m r) = deg T [hme m] + deg T (hmstar m r))
    by (unfold HM; rewrite <- deg_app; reflexivity).
  assert (Hmul : r ^ (m - length T) * r ^ (length T) = r ^ m)
    by (rewrite <- Nat.pow_add_r; f_equal; lia).
  assert (Hgoal : deg T (HM m r) * r ^ (length T) <= r ^ m).
  { destruct (containsb T (hme m)) eqn:EC.
    - assert (Hin : deg T [hme m] = 1) by (unfold deg; simpl; rewrite EC; reflexivity).
      rewrite Hsplit, Hin, Nat.add_comm.
      apply hmstar_deg_inside; try assumption.
      apply containsb_true_iff; exact EC.
    - assert (Hin : deg T [hme m] = 0) by (unfold deg; simpl; rewrite EC; reflexivity).
      rewrite Hsplit, Hin; simpl.
      apply hmstar_deg_mul; assumption. }
  nia.
Qed.

(** ** The theorem

    At [r = m] the family is spread and has one member more than the
    star, so no star bound can hold. *)

Theorem HM_beats_star :
  forall m, 2 <= m -> m ^ (m - 1) < length (HM m m).
Proof.
  intros m Hm; rewrite HM_length.
  assert (E : m * m ^ (m - 2) = m ^ (m - 1))
    by (rewrite <- Nat.pow_succ_r'; f_equal; lia).
  lia.
Qed.

Theorem not_star_extremal_at_m_m :
  forall m, 2 <= m -> ~ StarExtremalAt m m.
Proof.
  intros m Hm Hstar.
  pose proof (Hstar (HM m m) (HM_uniform m m Hm) (HM_rao m m Hm (Nat.le_refl m))
                (HM_intersecting m m ltac:(lia))) as Hle.
  pose proof (HM_beats_star m Hm) as Hgt.
  lia.
Qed.

(** *** The family is not a star, so it is a lower bound for [I2]

    [I2(m,r)] (see [CrossRefined]) is the largest [m]-uniform intersecting
    Rao(r)-spread family that is not a star. [HM m r] is one, for every
    [r >= m], so

    >  I2(m,r) >= m·r^(m-2) + 1   whenever   r >= m,

    which is the lower half of Conjecture HM (roadmap §28) at every
    uniformity. *)

Theorem HM_nonstar :
  forall m r, 2 <= m -> 1 <= r -> NonStar (HM m r).
Proof.
  intros m r Hm Hr w.
  destruct (in_dec_nat w (hme m)) as [HwE|HwE].
  - (* [w] is in the special set: a star member on a different point of it *)
    assert (Hw : w < m) by (apply hme_lt; exact HwE).
    assert (Hne : exists i, In i (hme m) /\ i <> w).
    { destruct (Nat.eq_dec w 0) as [E0|N0].
      - exists 1; split; [unfold hme; apply in_seq; lia | lia].
      - exists 0; split; [unfold hme; apply in_seq; lia | lia]. }
    destruct Hne as [i [HiE Hiw]].
    destruct (grid_nonempty (S m) (m - 2) r Hr) as [g Hgm].
    exists (i :: hmw m :: g); split.
    + right; unfold hmstar.
      apply in_flat_map; exists i; split; [exact HiE|].
      apply in_map_iff; exists (hmw m :: g); split; [reflexivity|].
      apply in_flat_map; exists (hmw m); split; [left; reflexivity|].
      apply in_map_iff; exists g; split; [reflexivity | exact Hgm].
    + simpl; intros [Ei|[Ew|Hgw]].
      * congruence.
      * unfold hmw in Ew; lia.
      * destruct (grid_bounds (S m) (m - 2) r g Hgm w Hgw); lia.
  - (* [w] is anywhere else: the special set itself misses it *)
    exists (hme m); split; [left; reflexivity | exact HwE].
Qed.

Theorem HM_distinct : forall m r, 2 <= m -> m <= r -> Distinct (HM m r).
Proof.
  intros m r Hm Hr.
  exact (@rao_uniform_distinct m r (HM m r) ltac:(lia)
           (HM_uniform m r Hm) (HM_rao m r Hm Hr)).
Qed.

(** *** [I2(3,r) = 3r+1] for every [r >= 5]

    [CrossRefined.nonstar_three_bound] gives [I2(3,r) <= max(3r+1, 16)],
    and [3r+1 >= 16] exactly when [r >= 5]. [HM 3 r] attains [3r+1]. So
    the row §27.6 closed at [r = 5] closes at every [r >= 5], and
    [CrossRefined.i2_three_five_is_sixteen] is its first instance. *)

Theorem i2_three_exact :
  forall r, 5 <= r ->
    (Uniform 3 (HM 3 r) /\ Distinct (HM 3 r) /\ RaoSpread 3 (HM 3 r) r /\
     (forall C D, In C (HM 3 r) -> In D (HM 3 r) -> exists x, In x C /\ In x D) /\
     NonStar (HM 3 r) /\ length (HM 3 r) = 3 * r + 1)
    /\ (forall A : Family,
           Uniform 3 A -> Distinct A -> RaoSpread 3 A r ->
           (forall C D, In C A -> In D A -> exists x, In x C /\ In x D) ->
           NonStar A -> length A <= 3 * r + 1).
Proof.
  intros r Hr; split.
  - refine (conj (HM_uniform 3 r ltac:(lia))
             (conj (HM_distinct 3 r ltac:(lia) ltac:(lia))
                (conj (HM_rao 3 r ltac:(lia) ltac:(lia))
                   (conj (HM_intersecting 3 r ltac:(lia))
                      (conj (HM_nonstar 3 r ltac:(lia) ltac:(lia)) _))))).
    rewrite HM_length; simpl; lia.
  - intros A HU HD HR Hint Hns.
    pose proof (@nonstar_three_bound r A ltac:(lia) HU HD HR Hint Hns) as H.
    assert (E : Nat.max (3 * r + 1) 16 = 3 * r + 1) by lia.
    rewrite E in H; exact H.
Qed.

(** *** Consequence 1: [r >= m+1] in the two-cover theorem is sharp

    [HM m m] is covered by the two points [{0, m}] — every star member
    carries the apex [m], and the special set carries 0. So
    [CrossIntersecting.two_cover_star_extremal] would be false with its
    hypothesis [m+1 <= r] weakened to [m <= r], and the threshold it
    carries is exactly right rather than an artefact of its proof. *)

Lemma HM_two_cover :
  forall m r, 1 <= m -> forall C, In C (HM m r) -> In 0 C \/ In (hmw m) C.
Proof.
  intros m r Hm C HC; destruct HC as [EC|HC].
  - subst C; left; unfold hme; apply in_seq; lia.
  - right; destruct (hmstar_shape m r C HC) as [i [g [_ [_ EC]]]]; subst C.
    right; left; reflexivity.
Qed.

Theorem two_cover_threshold_is_sharp :
  forall m, 2 <= m ->
    ~ (forall (G : Family) p q,
          Uniform m G -> RaoSpread m G m ->
          (forall C D, In C G -> In D G -> exists x, In x C /\ In x D) ->
          (forall C, In C G -> In p C \/ In q C) ->
          length G <= m ^ (m - 1)).
Proof.
  intros m Hm Hbad.
  pose proof (Hbad (HM m m) 0 (hmw m) (HM_uniform m m Hm)
                (HM_rao m m Hm (Nat.le_refl m))
                (HM_intersecting m m ltac:(lia))
                (HM_two_cover m m ltac:(lia))) as Hle.
  pose proof (HM_beats_star m Hm) as Hgt; lia.
Qed.

(** *** Consequence 2: no threshold at or below [m] can work

    [StarExtremalAt m ·] is not known to be monotone in [r], so this is
    stated as what it is: the *specific* value [r = m] fails, hence any
    claim of the form "[StarExtremalAt m r] for all [r >= s]" needs
    [s >= m+1]. *)

Theorem star_extremal_needs_r_above_m :
  forall m s, 2 <= m -> s <= m ->
    ~ (forall r, s <= r -> StarExtremalAt m r).
Proof.
  intros m s Hm Hs Hall.
  exact (not_star_extremal_at_m_m m Hm (Hall m Hs)).
Qed.

(** *** Consequence 3: the barrier

    [TwoCover.star_extremal_gives_m_plus_one] is the route this
    development built from star extremality to a sunflower bound:

    <<
      (forall m <= n, StarExtremalAt m r)
        -> SpreadYieldsDisjoint n 3 r
        -> f(n,3) <= r^n + 1                (SpreadReduction.spread_reduction)
    >>

    and it is instantiated there at [r = n+1]. The natural hope is that
    a smaller [r] would do — a *constant* [r] would give [f(n,3) <= C^n]
    and settle the conjecture at [k = 3]. It would not, and the reason is
    one line: the hypothesis quantifies over every [m <= n], so it
    includes [StarExtremalAt r r], which [HM r r] refutes.

    > **No [r <= n] can satisfy the hypothesis of
    > [star_extremal_gives_m_plus_one].**

    So the route's parameter is pinned at [r >= n+1] and its best
    possible output is [f(n,3) <= (n+1)^n + 1]. That is *worse* than
    Erdős–Rado's [2^n·n! + 1] — by a factor growing like [(e/2)^n] up
    to polynomial corrections, since [2^n·n! ≈ sqrt(2πn)·(2n/e)^n] and
    [(n+1)^n ≈ e·n^n], so the ratio is [(e/sqrt(2πn))·(e/2)^n]. The
    arithmetic is exposed in [docs/roadmap.md] §28.4 and checked in exact
    big integers in [rust/tests/hilton_milner.rs].

    This does not say the *destination* is out of reach: [SpreadYieldsDisjoint
    n 3 r] holds for [r = Θ(log n)] by the modern spread lemma, which is
    what [ALWZ.sunflower_bound_from_spread_lemma] uses. It says the
    star-extremality *hypothesis*, under Rao's absolute spread condition,
    cannot be the thing that supplies it. *)

Theorem star_extremal_route_needs_r_above_n :
  forall n r, 2 <= r -> r <= n ->
    ~ (forall m, 1 <= m -> m <= n -> StarExtremalAt m r).
Proof.
  intros n r Hr Hrn Hall.
  exact (not_star_extremal_at_m_m r Hr (Hall r ltac:(lia) Hrn)).
Qed.

(** *** The two small instances, written out

    [HM 3 3] has 10 members against [3^2 = 9], and [HM 4 4] has 65
    against [4^3 = 64]. The second is the one §26.4 and §27 were circling:
    it says that the open constant at [(m,r) = (4,5)] cannot be pushed
    down to a statement about [r = 4]. *)

Corollary not_star_extremal_three_three : ~ StarExtremalAt 3 3.
Proof. apply not_star_extremal_at_m_m; lia. Qed.

Corollary not_star_extremal_four_four : ~ StarExtremalAt 4 4.
Proof. apply not_star_extremal_at_m_m; lia. Qed.

Corollary HM_four_four_length : length (HM 4 4) = 65.
Proof. rewrite HM_length; reflexivity. Qed.

Corollary HM_three_three_length : length (HM 3 3) = 10.
Proof. rewrite HM_length; reflexivity. Qed.

(** ** Below the boundary: projective planes, and the [m = 3] row closed

    [HM m m] refutes star extremality at [r = m]. It says nothing about
    [r < m], where it is not spread — and there the obstruction is a
    different object. A projective plane of order [q] is
    [(q+1)]-uniform, has [q^2+q+1] lines, any two of which meet, and its
    degrees are [q+1] at a point and [1] at a pair. So it is
    Rao(2)-spread as soon as [q+1 <= 2^q], which is every [q >= 1], and
    it beats the star bound [2^q] exactly when [q^2+q+1 > 2^q] — at
    [q = 2, 3, 4] and no further.

    Two instances are written out below. [fano] is [PG(2,2)]: 7 lines on
    7 points, against a star bound of [4]. [pg23] is [PG(2,3)]: 13 lines
    of 4 points on 13 points, against a star bound of [8].

    At [m = 3] this closes the row completely. Star extremality fails at
    [r = 2] ([fano]) and at [r = 3] ([HM 3 3]), and holds at every
    [r >= 4] by [TauThree.three_uniform_star_extremal]. So the threshold
    is exactly [4 = m+1], which is Conjecture T (roadmap §28.5) settled
    at its first nontrivial uniformity.

    One wrinkle the row exposes, and it is a correction to how the
    conjecture should be stated. [StarExtremalAt 3 0] and
    [StarExtremalAt 3 1] are *true*, vacuously: Rao(0) forces every point
    to have degree 0 and Rao(1) forces the members to be pairwise
    disjoint, so in both cases an intersecting family has at most one
    member. "Least [r] such that [StarExtremalAt m r]" is therefore 0,
    not [m+1], and the quantity Conjecture T is about is the least [s]
    such that it holds for *every* [r >= s]. *)

Definition fano : Family :=
  [[0;1;6]; [0;2;4]; [0;3;5]; [1;2;5]; [1;3;4]; [2;3;6]; [4;5;6]].

Definition pg23 : Family :=
  [[0;1;2;12]; [0;3;6;9];  [0;4;8;10]; [0;5;7;11]; [1;3;8;11];
   [1;4;7;9];  [1;5;6;10]; [2;3;7;10]; [2;4;6;11]; [2;5;8;9];
   [3;4;5;12]; [6;7;8;12]; [9;10;11;12]].

Lemma fano_uniform : Uniform 3 fano.
Proof. apply uniformb_correct; vm_compute; reflexivity. Qed.

Lemma fano_rao : RaoSpread 3 fano 2.
Proof.
  apply (@rao_spreadb_correct 3 fano 2 (seq 0 7)).
  - apply nodupb_correct; vm_compute; reflexivity.
  - apply Forall_forall; intros A HA.
    destruct (@uniform_mem 3 fano A fano_uniform HA) as [_ Hnd]; exact Hnd.
  - apply groundedb_correct; vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

Lemma fano_int :
  forall C D, In C fano -> In D fano -> exists x, In x C /\ In x D.
Proof. apply int_b_correct; vm_compute; reflexivity. Qed.

Theorem not_star_extremal_three_two : ~ StarExtremalAt 3 2.
Proof.
  intro H.
  pose proof (H fano fano_uniform fano_rao (@fano_int)) as Hle.
  vm_compute in Hle; lia.
Qed.

Lemma pg23_uniform : Uniform 4 pg23.
Proof. apply uniformb_correct; vm_compute; reflexivity. Qed.

Lemma pg23_rao : RaoSpread 4 pg23 2.
Proof.
  apply (@rao_spreadb_correct 4 pg23 2 (seq 0 13)).
  - apply nodupb_correct; vm_compute; reflexivity.
  - apply Forall_forall; intros A HA.
    destruct (@uniform_mem 4 pg23 A pg23_uniform HA) as [_ Hnd]; exact Hnd.
  - apply groundedb_correct; vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

Lemma pg23_int :
  forall C D, In C pg23 -> In D pg23 -> exists x, In x C /\ In x D.
Proof. apply int_b_correct; vm_compute; reflexivity. Qed.

Theorem not_star_extremal_four_two : ~ StarExtremalAt 4 2.
Proof.
  intro H.
  pose proof (H pg23 pg23_uniform pg23_rao (@pg23_int)) as Hle.
  vm_compute in Hle; lia.
Qed.

(** > **The [m = 3] row of Conjecture T, complete.** Star extremality at
    > uniformity three fails at [r = 2] and [r = 3] and holds at every
    > [r >= 4]; the threshold is exactly [m+1]. *)

Theorem star_extremal_three_row :
  ~ StarExtremalAt 3 2 /\ ~ StarExtremalAt 3 3
  /\ (forall r, 4 <= r -> StarExtremalAt 3 r).
Proof.
  refine (conj not_star_extremal_three_two
            (conj not_star_extremal_three_three _)).
  exact three_uniform_star_extremal.
Qed.

Theorem star_threshold_three_is_four :
  (forall r, 4 <= r -> StarExtremalAt 3 r)
  /\ (forall s, (forall r, s <= r -> StarExtremalAt 3 r) -> 4 <= s).
Proof.
  split; [exact three_uniform_star_extremal|].
  intros s Hs.
  destruct (le_lt_dec 4 s) as [H4|H4]; [exact H4 | exfalso].
  exact (not_star_extremal_three_three (Hs 3 ltac:(lia))).
Qed.

(** ** A second opinion on the two small instances

    Everything above is proved by induction. [Reflect.rao_spreadb] decides
    the same condition a completely different way — it enumerates every
    subset of every member and counts degrees by filtering — so running it
    on [HM 3 3] and [HM 4 4] checks the induction against a computation
    that shares no code with it. If [grid_deg_mul] were wrong, these would
    disagree. The ground sets are [seq 0 7] and [seq 0 13]. *)

Lemma HM_three_three_grounded : groundedb (HM 3 3) (seq 0 7) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma HM_four_four_grounded : groundedb (HM 4 4) (seq 0 13) = true.
Proof. vm_compute; reflexivity. Qed.

Theorem HM_three_three_second_opinion :
  uniformb 3 (HM 3 3) = true
  /\ rao_spreadb 3 (HM 3 3) 3 (seq 0 7) = true
  /\ int_b (HM 3 3) = true
  /\ length (HM 3 3) = 10.
Proof. vm_compute; repeat apply conj; reflexivity. Qed.

Theorem HM_four_four_second_opinion :
  uniformb 4 (HM 4 4) = true
  /\ rao_spreadb 4 (HM 4 4) 4 (seq 0 13) = true
  /\ int_b (HM 4 4) = true
  /\ length (HM 4 4) = 65.
Proof. vm_compute; repeat apply conj; reflexivity. Qed.

(** ** Print Assumptions

    Everything above is closed under the global context; the file adds no
    axiom and no admitted statement. *)
