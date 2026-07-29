(** * Intersecting.v -- Doubling an intersecting family, and the rate it buys.

    Write [g(m) = f(m,3) - 1] for the largest 3-sunflower-free
    [m]-uniform family, and

    >  iota(b)  =  the largest *intersecting* 3-sunflower-free
    >              b-uniform family.

    The theorem here is that the second bounds the first:

    >  g(b)  >=  2 * iota(b).

    Two disjoint copies of an intersecting sunflower-free family are
    sunflower-free. Any three members put two in the same copy, and
    those two *meet*; a member of the other copy is disjoint from both.
    A sunflower needs all three pairwise intersections equal, so it
    cannot have one empty and one not. That is the whole argument, and
    the intersecting hypothesis is the only thing making it work
    ([Audit.intersecting_is_needed_in_the_doubling] is the
    counterexample without it).

    ** Why this is worth having

    At [b = 2] the largest intersecting sunflower-free graph is the
    triangle, [iota(2) = 3], and the doubling *is* [F23.two_triangles].
    So this generalises the construction that gives [f(2,3) = 7].

    At [b = 3] an exhaustive search says [iota(3) = 10], attained on six
    points, and stable from there to twelve
    ([rust/examples/iota_scan.rs]). Doubling gives a 20-member
    3-uniform sunflower-free family on twelve points, so
    [f(3,3) >= 21] — against the 15 that the raw ground-set search
    reached at nine points, and the 13 the direct sum gives.

    Feeding *that* to [DirectSum.lower_bound_power]:

    >  f(n,3)  >=  20^(n/3) + 1  =  2.714...^n

    against the previous best here of [6^(n/2) = 2.449...^n]. The
    improvement is the whole point of measuring [iota] rather than [g].

    ** Where this is going

    [iota] is the right quantity for a second reason, which is not
    formalised here. The Abbott–Hanson–Sauer *substitution* construction
    — blow up each point of a member of an [a]-uniform family into a
    member of a [b]-uniform one — is sunflower-free exactly when the
    inner family is intersecting, and iterating it has fixed point
    [c^b = c * iota(b)], i.e. a rate of [iota(b)^(1/(b-1))]. At
    [iota(3) = 10] that is [10^(1/2) = 3.162...], which is the published
    1972 bound on the nose. So on this reading [iota(3) = 10] is the
    content of that paper, and the record moves as soon as some [b] has
    [iota(b) > 10^((b-1)/2)] — [iota(4) >= 32] would do it.

    It does not, through ten points. Exhaustive search gives
    [iota(4,9) = 27] (a rate of exactly 3.0000) and no family of 32 or
    more on ten points, so [b = 4] does not beat the 1972 rate there.
    Grounds eleven and up are open and, at the measured 89x cost per
    extra point, out of reach of the present search.

    The reconstruction is ours and the paper was not read; that it
    reproduces both [iota(2) = 3] with [g(2) = 6] and the published
    constant exactly is the evidence for it. See [docs/roadmap.md] §5.

    Zero axioms, zero admits. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower LowerBound ProductLowerBound
     Spread Reflect F23 DirectSum.
Import ListNotations.

(** ** Intersecting families *)

Definition Intersecting (F : Family) : Prop :=
  forall A B, In A F -> In B F -> ~ Disjoint A B.

Definition intersectingb (F : Family) : bool :=
  forallb (fun A => forallb (fun B => negb (disjointb A B)) F) F.

Lemma intersectingb_correct :
  forall F, intersectingb F = true <-> Intersecting F.
Proof.
  intros F; unfold intersectingb, Intersecting; split.
  - intros H A B HA HB Hdis.
    rewrite forallb_forall in H; specialize (H A HA).
    rewrite forallb_forall in H; specialize (H B HB).
    apply Bool.negb_true_iff in H.
    rewrite <- disjointb_correct in Hdis; congruence.
  - intros H; apply forallb_forall; intros A HA.
    apply forallb_forall; intros B HB.
    apply Bool.negb_true_iff.
    destruct (disjointb A B) eqn:E; [|reflexivity].
    exfalso; apply (H A B HA HB), disjointb_correct; exact E.
Qed.

Lemma Intersecting_rmapF :
  forall g h, (forall x, h (g x) = x) ->
  forall F, Intersecting F -> Intersecting (rmapF g F).
Proof.
  intros g h Hgh F HI A B HA HB Hdis.
  unfold rmapF in HA, HB.
  apply in_map_iff in HA as [A0 [EA HA0]].
  apply in_map_iff in HB as [B0 [EB HB0]].
  subst A B.
  apply (HI A0 B0 HA0 HB0).
  intros x HxA HxB.
  apply (Hdis (g x)); apply in_map_iff; exists x; split; auto.
Qed.

(** ** The obstruction, isolated

    A sunflower cannot have one pairwise intersection empty and another
    not. Everything about the doubling is this lemma plus bookkeeping. *)

Lemma no_sunflower_across :
  forall A B C core,
    ~ Disjoint A B -> Disjoint A C ->
    SetEq (inter A B) core -> SetEq (inter A C) core -> False.
Proof.
  intros A B C core Hmeet Hdis Hab Hac.
  apply Hmeet; intros x HxA HxB.
  assert (Hin : In x (inter A B)) by (apply in_inter_iff; auto).
  apply (proj1 Hab) in Hin.
  apply (proj2 Hac) in Hin.
  apply in_inter_iff in Hin as [_ HxC].
  exact (Hdis x HxA HxC).
Qed.

Lemma split_kills_sunflower :
  forall (P Q : Family) A B C core,
    In A P -> In B P -> In C Q ->
    Intersecting P ->
    (forall X Y, In X P -> In Y Q -> Disjoint X Y) ->
    SetEq (inter A B) core -> SetEq (inter A C) core ->
    False.
Proof.
  intros P Q A B C core HA HB HC HI Hcross Hab Hac.
  exact (no_sunflower_across A B C core (HI A B HA HB) (Hcross A C HA HC) Hab Hac).
Qed.

(** ** [SetNoDup] of an append *)

Lemma inter_comm_SetEq : forall A B, SetEq (inter A B) (inter B A).
Proof.
  intros A B; split; intros x Hx; apply in_inter_iff in Hx as [H1 H2];
    apply in_inter_iff; split; assumption.
Qed.

Lemma SetNoDup_app :
  forall P Q : Family,
    SetNoDup P -> SetNoDup Q ->
    (forall A B, In A P -> In B Q -> ~ SetEq A B) ->
    SetNoDup (P ++ Q).
Proof.
  induction P as [|A P IH]; intros Q HP HQ Hcross; simpl; [exact HQ|].
  inversion HP as [|A' P' Hni HP']; subst.
  constructor.
  - intros B HB Hseq.
    apply in_app_or in HB as [HB | HB].
    + exact (Hni B HB Hseq).
    + exact (Hcross A B (or_introl eq_refl) HB Hseq).
  - apply IH; [exact HP' | exact HQ |].
    intros A0 B0 H1 H2; apply Hcross; [right; exact H1 | exact H2].
Qed.

(** ** The doubling

    The two copies are the even and odd relabellings from [DirectSum],
    so they are disjoint by parity and no maximum has to be computed. *)

Definition double (H : Family) : Family := rmapF ev H ++ rmapF od H.

Lemma double_length : forall H, length (double H) = 2 * length H.
Proof.
  intros H; unfold double; rewrite app_length, !rmapF_length; lia.
Qed.

Lemma double_cross_disjoint :
  forall H A B, In A (rmapF ev H) -> In B (rmapF od H) -> Disjoint A B.
Proof.
  intros H A B HA HB.
  unfold rmapF in HA, HB.
  apply in_map_iff in HA as [A0 [EA _]].
  apply in_map_iff in HB as [B0 [EB _]].
  subst A B; apply ev_od_disjoint.
Qed.

Lemma double_Uniform :
  forall b H, Uniform b H -> Uniform b (double H).
Proof.
  intros b H HU; unfold double, Uniform.
  apply Forall_forall; intros A HA.
  apply in_app_or in HA as [HA | HA];
    [ pose proof (rmapF_Uniform ev Nat.div2 div2_ev b H HU) as HE
    | pose proof (rmapF_Uniform od Nat.div2 div2_od b H HU) as HE ];
    unfold Uniform in HE; rewrite Forall_forall in HE; exact (HE A HA).
Qed.

Lemma double_Distinct :
  forall b H, 1 <= b -> Uniform b H -> Distinct H -> Distinct (double H).
Proof.
  intros b H Hb HU HD; unfold double, Distinct.
  apply SetNoDup_app.
  - exact (rmapF_Distinct ev Nat.div2 div2_ev H HD).
  - exact (rmapF_Distinct od Nat.div2 div2_od H HD).
  - intros A B HA HB Hseq.
    (* [A] is nonempty because it has [b >= 1] elements, and its points
       are even while [B]'s are odd. *)
    assert (HUA : Uniform b (rmapF ev H))
      by exact (rmapF_Uniform ev Nat.div2 div2_ev b H HU).
    unfold Uniform in HUA; rewrite Forall_forall in HUA.
    destruct (HUA A HA) as [Hlen _].
    destruct A as [|x A0]; [simpl in Hlen; lia|].
    assert (HxB : In x B) by (apply (proj1 Hseq); left; reflexivity).
    exact (double_cross_disjoint H (x :: A0) B HA HB x (or_introl eq_refl) HxB).
Qed.

Theorem double_no_sunflower :
  forall b (H : Family),
    1 <= b -> Uniform b H -> Distinct H ->
    Intersecting H -> ~ ContainsKSunflower 3 H ->
    ~ ContainsKSunflower 3 (double H).
Proof.
  intros b H Hb HU HD HI Hno Hc.
  assert (HnoE : ~ ContainsKSunflower 3 (rmapF ev H))
    by exact (rmapF_no_sunflower ev Nat.div2 div2_ev 3 H Hno).
  assert (HnoO : ~ ContainsKSunflower 3 (rmapF od H))
    by exact (rmapF_no_sunflower od Nat.div2 div2_od 3 H Hno).
  assert (HIE : Intersecting (rmapF ev H))
    by exact (Intersecting_rmapF ev Nat.div2 div2_ev H HI).
  assert (HIO : Intersecting (rmapF od H))
    by exact (Intersecting_rmapF od Nat.div2 div2_od H HI).
  assert (Hcross : forall X Y, In X (rmapF ev H) -> In Y (rmapF od H) ->
                     Disjoint X Y)
    by (intros X Y; apply double_cross_disjoint).
  assert (Hcross' : forall X Y, In X (rmapF od H) -> In Y (rmapF ev H) ->
                      Disjoint X Y)
    by (intros X Y HX HY; apply Disjoint_sym; apply (double_cross_disjoint H); auto).
  destruct (contains_sunflower_literal 3 (double H) Hc)
    as [S [core [Hincl [Hnd [Hlen Hsun]]]]].
  destruct S as [|A [|B [|C [|D S']]]]; simpl in Hlen; try discriminate.
  destruct Hsun as [Hsnd Hcore].
  assert (inA : In A [A; B; C]) by (left; reflexivity).
  assert (inB : In B [A; B; C]) by (right; left; reflexivity).
  assert (inC : In C [A; B; C]) by (right; right; left; reflexivity).
  inversion Hnd as [|? ? HniA HndBC]; subst.
  inversion HndBC as [|? ? HniB HndC]; subst.
  assert (HAB : A <> B) by (intro E; subst; apply HniA; left; reflexivity).
  assert (HAC : A <> C)
    by (intro E; subst; apply HniA; right; left; reflexivity).
  assert (HBC : B <> C) by (intro E; subst; apply HniB; left; reflexivity).
  pose proof (Hcore A B inA inB HAB) as Hab.
  pose proof (Hcore A C inA inC HAC) as Hac.
  pose proof (Hcore B C inB inC HBC) as Hbc.
  assert (HA : In A (double H)) by (apply Hincl; exact inA).
  assert (HB : In B (double H)) by (apply Hincl; exact inB).
  assert (HC : In C (double H)) by (apply Hincl; exact inC).
  unfold double in HA, HB, HC.
  apply in_app_or in HA as [HA | HA];
    apply in_app_or in HB as [HB | HB];
    apply in_app_or in HC as [HC | HC].
  - (* all even *)
    apply HnoE.
    apply (@ContainsKSunflower_of_incl 3 [A; B; C] (rmapF ev H) core);
      [ intros U [E|[E|[E|[]]]]; subst U; assumption
      | reflexivity
      | split; assumption ].
  - exact (split_kills_sunflower _ _ A B C core HA HB HC HIE Hcross Hab Hac).
  - exact (split_kills_sunflower _ _ A C B core HA HC HB HIE Hcross Hac Hab).
  - exact (split_kills_sunflower _ _ B C A core HB HC HA HIO Hcross' Hbc
             (SetEq_trans (inter_comm_SetEq B A) Hab)).
  - exact (split_kills_sunflower _ _ B C A core HB HC HA HIE Hcross Hbc
             (SetEq_trans (inter_comm_SetEq B A) Hab)).
  - exact (split_kills_sunflower _ _ A C B core HA HC HB HIO Hcross' Hac Hab).
  - exact (split_kills_sunflower _ _ A B C core HA HB HC HIO Hcross' Hab Hac).
  - (* all odd *)
    apply HnoO.
    apply (@ContainsKSunflower_of_incl 3 [A; B; C] (rmapF od H) core);
      [ intros U [E|[E|[E|[]]]]; subst U; assumption
      | reflexivity
      | split; assumption ].
Qed.

(** ** [g(b) >= 2 * iota(b)] *)

Theorem doubling_lower_bound :
  forall b (H : Family),
    1 <= b -> Uniform b H -> Distinct H ->
    Intersecting H -> ~ ContainsKSunflower 3 H ->
    LowerBound b 3 (2 * length H).
Proof.
  intros b H Hb HU HD HI Hno.
  exists (double H).
  split; [apply double_Uniform; exact HU|].
  split; [exact (double_Distinct b H Hb HU HD)|].
  (* [rewrite; lia] rather than [apply]: the mutation
     [lowerbound-at-least] turns this equation into [>=], and a proof
     that discharges it by [apply] is sensitive to [LowerBound]'s shape
     rather than to its content. *)
  split; [rewrite double_length; lia|].
  exact (double_no_sunflower b H Hb HU HD HI Hno).
Qed.

(** ** [iota(3) = 10], and what it gives

    The witness is the maximum returned by the exhaustive search in
    [rust/examples/iota_scan.rs] at [b = 3] on six points, transcribed.
    Every property is re-derived here by a reflective check, so nothing
    is taken on the search's word. *)

Definition iota3 : Family :=
  [[0; 1; 2]; [0; 1; 3]; [0; 2; 4]; [1; 3; 4]; [2; 3; 4];
   [1; 2; 5]; [0; 3; 5]; [2; 3; 5]; [0; 4; 5]; [1; 4; 5]].

Lemma iota3_uniform : Uniform 3 iota3.
Proof. apply uniformb_correct; vm_compute; reflexivity. Qed.

Lemma iota3_distinct : Distinct iota3.
Proof. apply distinctb_correct; vm_compute; reflexivity. Qed.

Lemma iota3_intersecting : Intersecting iota3.
Proof. apply intersectingb_correct; vm_compute; reflexivity. Qed.

Lemma iota3_no_sunflower : ~ ContainsKSunflower 3 iota3.
Proof.
  intro Hc.
  pose proof (sunflower3b_sound iota3 Hc) as E; vm_compute in E; discriminate.
Qed.

(** [f(3,3) >= 21]. The previous best here was 15 (the raw ground-set
    maximum on nine points) and before that 13 (the direct sum). *)

Theorem lower_bound_3_3_20 : LowerBound 3 3 20.
Proof.
  apply (doubling_lower_bound 3 iota3);
    [ lia | apply iota3_uniform | apply iota3_distinct
    | apply iota3_intersecting | apply iota3_no_sunflower ].
Qed.

Corollary no_upper_bound_3_3_20 : ~ UpperBound 3 3 20.
Proof.
  intro Hub.
  destruct lower_bound_3_3_20 as [F [HU [HD [Hlen Hno]]]].
  apply Hno, Hub; [exact HU | exact HD | lia].
Qed.

(** ** The rate

    [DirectSum.lower_bound_power] raises any single value to the
    [t]-th power. Seeded at uniformity 3 with 20 rather than at
    uniformity 2 with 6, the rate goes from [6^(1/2) = 2.449] to
    [20^(1/3) = 2.714]. *)

Theorem lower_bound_f_n_3_sharp :
  forall t, LowerBound (t * 3) 3 (20 ^ t).
Proof. intros t; apply lower_bound_power; [lia | exact lower_bound_3_3_20]. Qed.

(** Strictly better than pairing up, and the gap compounds: at
    uniformity [6t] the two constructions give [20^(2t)] and [6^(3t)],
    i.e. [400^t] against [216^t]. *)

Theorem twenty_beats_six :
  forall t, 1 <= t -> 6 ^ (3 * t) < 20 ^ (2 * t).
Proof.
  intros t Ht.
  (* [6^(3t) = 216^t] and [20^(2t) = 400^t]: same exponent, so the
     comparison is between the bases. *)
  rewrite !Nat.pow_mul_r.
  apply Nat.pow_lt_mono_l; [lia|].
  simpl; lia.
Qed.

(** And better than the previous headline at every uniformity divisible
    by 6, which is where the two are directly comparable. *)

Corollary sharp_beats_previous :
  forall t, 1 <= t ->
    LowerBound (t * 6) 3 (6 ^ (3 * t))
    /\ LowerBound (t * 6) 3 (20 ^ (2 * t))
    /\ 6 ^ (3 * t) < 20 ^ (2 * t).
Proof.
  intros t Ht.
  split.
  { replace (t * 6) with (3 * t * 2) by lia.
    apply lower_bound_f_n_3. }
  split.
  { replace (t * 6) with (2 * t * 3) by lia.
    apply lower_bound_f_n_3_sharp. }
  apply twenty_beats_six; exact Ht.
Qed.
