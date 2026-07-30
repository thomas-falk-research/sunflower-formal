(** * Product.v -- the multiplicative structure of iota, the cone, and
      what a splitting argument cannot buy.

    [IotaRate.conjecture_k_3_iff_iota_exponential] says the sunflower
    conjecture at [k = 3] is *equivalent* to [iota(b) <= C^b], where

    >  iota(b)  =  the largest intersecting 3-sunflower-free b-uniform
    >              family.

    That is a statement about a single sequence, and sequences bounded by
    [C^b] are exactly the ones whose growth is controlled
    multiplicatively. This file works out what multiplicative structure
    [iota] actually has.

    ** Supermultiplicativity, and the limit it creates

    [iota_supermultiplicative]: [iota(a+b) >= iota(a) * iota(b)]. The
    direct sum of two intersecting families on disjoint ground sets is
    intersecting — two members meet in their first halves — and
    [DirectSum.sum_family_no_sunflower] already says it is
    sunflower-free. So [log iota] is superadditive and, by Fekete's
    lemma, [iota(b)^(1/b)] converges to

    >  L  =  sup_b iota(b)^(1/b)  in  (0, infinity],

    and **the conjecture at [k = 3] is exactly [L < infinity]**. No limit
    is taken in this file; what is proved is the finitistic content of
    that sentence, which is that the two *sufficient* conditions

    >  IotaSubMultiplicative D  :  iota(a+b) <= D * iota(a) * iota(b)
    >  IotaStepBounded D        :  iota(b+1) <= D * iota(b)

    each settle [k = 3], with an explicit constant
    ([submultiplicative_settles_k3], [step_bounded_settles_k3]). The
    second is *one bounded ratio*: the whole conjecture at [k = 3] is
    implied by the boundedness of [iota(b+1)/iota(b)].

    ** The cone, and why it changes the reading of the problem

    The other half of the file is a construction the development did not
    have. Add one fresh point to every member of a sunflower-free
    [m]-uniform family. The result is [(m+1)]-uniform, **intersecting**,
    and still sunflower-free — three members [A_i ∪ {p}] have pairwise
    intersections [(A_i ∩ A_j) ∪ {p}], which are all equal exactly when
    the [A_i ∩ A_j] are. So

    >  g(m)  <=  iota(m+1)                     [iota_at_least_g_pred]

    against [Intersecting.intersecting_link_bound]'s
    [iota(b) <= b * g(b-1)]. A second sandwich, in the other variable:

    >  g(b-1)  <=  iota(b)  <=  b * g(b-1).

    Four consequences, and they are the point of the file.

    - **The intersecting hypothesis is worth exactly one point of
      uniformity.** Anything true of every sunflower-free family at
      uniformity [m] is true of an intersecting one at [m+1], and
      conversely up to the factor [b]. So no argument whose only use of
      intersecting-ness is "the pieces are intersecting" can beat the
      general argument.

    - **An upper bound on [iota] is an upper bound on [g] one uniformity
      down** ([iota_bound_bounds_g]). In particular a proof of
      [iota(4) <= 27] — which is what the "decisive experiment" of
      [docs/roadmap.md] §7 would establish — gives [f(3,3) <= 28], where
      Erdős–Rado gives 49 and this development's best is
      [f(3,3) >= 21]. That is a *hardness* statement: the ladder is not
      a bookkeeping computation
      ([iota_four_at_most_27_would_beat_erdos_rado]).

    - **The two ground-set hypotheses are not independent.**
      [IotaGround.both_ground_hypotheses_settle_k3] records that
      "neither implies the other". One direction is immediate
      ([ground_bounded_implies_iota_ground_bounded]) and the cone gives
      the other up to the constant
      ([iota_ground_bounded_bounds_the_general_row]). The claim is
      withdrawn here.

    - **The universal reading of [IotaGroundBounded] is false.**
      [IotaGround.v] notes that "the data says the extremal intersecting
      sunflower-free family literally lives on [O(b)] points". The cone
      of the [FPPTZ24] tree-path family is an intersecting
      sunflower-free [b]-uniform family on [2^b - 1] points, every one of
      them used ([the_universal_iota_ground_reading_is_false]).

    ** And the diagnosis, in the same shape as [Compression.v]

    [LinkCharacterisation.sunflower_iff_link_matching] makes
    sunflower-freeness a conjunction with one clause per core [Y]:
    [nu(F_Y) <= 2]. [Compression.only_the_empty_core_survives_compression]
    says shifting commutes with the clause at [Y = ∅] and with no other.
    The cone is the mirror image: it **imposes** the empty-core clause
    for free — [cone_Intersecting] needs no hypothesis at all — and
    transports every other clause unchanged, because
    [link [p] (cone p F) = F] *literally* ([link_of_cone]).

    So both operations touch exactly one clause of the conjunction, and
    it is the same clause. That is [only_the_empty_core_is_cheap], and it
    is why a splitting argument cannot use the intersecting hypothesis:
    the fibre of a cone over its own trace is a general sunflower-free
    family, so the fibres of a split are bounded by [g] and not by
    [iota] ([the_split_fibres_are_not_intersecting]).

    Zero axioms, zero admits. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower LowerBound ProductLowerBound
     Conjecture Pigeonhole Spread SpreadReduction Reflect SmallCases TwoUniform
     F23 LinkCharacterisation DirectSum Intersecting IotaRate SliceRank
     IotaGround Compression.
Import ListNotations.

(** ** A witnessed lower bound on [iota]

    [IotaRate.IotaAtMost b N] reads "iota(b) <= N". This is the other
    side: a family attaining [N]. It is [LowerBound] with the
    intersecting clause added, and the same warning applies — the size is
    stated as an equation, so a proof needing a family of an exact size
    must *trim* one rather than assume one (see [docs/testing.md] §4). *)

Definition IotaAtLeast (b N : nat) : Prop :=
  exists H : Family,
    Uniform b H /\ Distinct H /\ Intersecting H
    /\ length H = N /\ ~ ContainsKSunflower 3 H.

(** The two sides fit together: a lower bound never exceeds an upper
    bound. Nothing forces this, and if the two predicates were about
    different quantities it would fail. *)

Theorem iota_at_least_le_at_most :
  forall b N M, IotaAtLeast b N -> IotaAtMost b M -> N <= M.
Proof.
  intros b N M [H [HU [HD [HI [Hlen Hno]]]]] Hub.
  pose proof (Hub H HU HD HI Hno) as Hle; lia.
Qed.

(** Intersecting-ness, uniformity, distinctness and sunflower-freeness all
    pass to subfamilies, so [IotaAtLeast] is downward closed: a family of
    exactly [N] members has an initial segment of exactly [N'] for every
    [N' <= N]. This is [Audit.LowerBound_ge_equiv]'s content for the new
    predicate, and it is what lets a proof *trim* rather than assume. *)

Lemma Intersecting_incl :
  forall F G, incl G F -> Intersecting F -> Intersecting G.
Proof. intros F G Hincl HI A B HA HB; exact (HI A B (Hincl A HA) (Hincl B HB)). Qed.

Theorem IotaAtLeast_antitone :
  forall b N N', N' <= N -> IotaAtLeast b N -> IotaAtLeast b N'.
Proof.
  intros b N N' Hle [H [HU [HD [HI [Hlen Hno]]]]].
  set (G := firstn N' H).
  assert (Hincl : incl G H) by (unfold G; apply incl_firstn).
  exists G.
  split; [exact (Uniform_sublist HU Hincl)|].
  split; [exact (SetNoDup_incl HD (NoDup_firstn N' (SetNoDup_NoDup HD)) Hincl)|].
  split; [exact (Intersecting_incl H G Hincl HI)|].
  split; [unfold G; rewrite firstn_length_le; lia|].
  intro Hc; exact (Hno (contains_sunflower_incl Hincl Hc)).
Qed.

(** ** Supermultiplicativity

    The one thing the direct sum needs that [DirectSum.v] does not
    supply: the sum of two intersecting families is intersecting. Only
    the *first* family has to be intersecting, for the same reason only
    the first has to be uniform there — the proof looks at the front
    halves. *)

Lemma sum_family_Intersecting :
  forall F1 F2, Intersecting F1 -> Intersecting (sum_family F1 F2).
Proof.
  intros F1 F2 HI C D HC HD Hdis.
  apply in_sum_family_iff in HC as [A1 [B1 [HA1 [_ EC]]]].
  apply in_sum_family_iff in HD as [A2 [B2 [HA2 [_ ED]]]].
  subst C D.
  (* [A1] and [A2] meet; the witness has to be extracted, so it comes
     through the boolean test rather than out of the negation. *)
  destruct (disjointb A1 A2) eqn:E.
  - exact (HI A1 A2 HA1 HA2 (proj1 (disjointb_correct A1 A2) E)).
  - destruct (proj1 (disjointb_false_iff A1 A2) E) as [x [Hx1 Hx2]].
    apply (Hdis x); apply in_or_app; left; assumption.
Qed.

Theorem iota_supermultiplicative :
  forall a b p q,
    IotaAtLeast a p -> IotaAtLeast b q -> IotaAtLeast (a + b) (p * q).
Proof.
  intros a b p q [H1 [HU1 [HD1 [HI1 [Hl1 Hn1]]]]] [H2 [HU2 [HD2 [_ [Hl2 Hn2]]]]].
  (* Relabel onto the even and odd points, exactly as
     [DirectSum.lower_bound_sum] does, so no ground set has to be named. *)
  destruct (relabel_preserves ev Nat.div2 div2_ev a 3 H1 HU1 HD1 Hn1)
    as [GU1 [GD1 [GL1 GN1]]].
  destruct (relabel_preserves od Nat.div2 div2_od b 3 H2 HU2 HD2 Hn2)
    as [GU2 [GD2 [GL2 GN2]]].
  assert (GI1 : Intersecting (rmapF ev H1))
    by exact (Intersecting_rmapF ev Nat.div2 div2_ev H1 HI1).
  assert (Hcross : CrossDisjoint (rmapF ev H1) (rmapF od H2)).
  { intros A B HA HB.
    unfold rmapF in HA, HB.
    apply in_map_iff in HA as [A0 [EA _]].
    apply in_map_iff in HB as [B0 [EB _]].
    subst A B; apply ev_od_disjoint. }
  exists (sum_family (rmapF ev H1) (rmapF od H2)).
  split; [exact (sum_family_Uniform a b _ _ GU1 GU2 Hcross)|].
  split; [exact (sum_family_Distinct a b _ _ GU1 GU2 GD1 GD2 Hcross)|].
  split; [exact (sum_family_Intersecting _ _ GI1)|].
  split.
  (* [nia], not [rewrite ...; reflexivity]: the mutation
     [iotaatleast-at-least] turns these length equations into [>=], and a
     proof that rewrites with them is sensitive to the *shape* of
     [IotaAtLeast] rather than to its content. This is the rule
     [docs/testing.md] §4 states, applied to the new predicate. *)
  - rewrite sum_family_length, GL1, GL2; nia.
  - exact (sum_family_no_sunflower a 3 _ _ ltac:(lia) GU1 GN1 GN2 Hcross).
Qed.

(** The trivial base, and the iterate. [iota(1) = 1]: two distinct
    singletons are disjoint. *)

Lemma iota_one_at_least_one : IotaAtLeast 1 1.
Proof.
  exists [[0]].
  split; [apply uniformb_correct; vm_compute; reflexivity|].
  split; [apply distinctb_correct; vm_compute; reflexivity|].
  split; [apply intersectingb_correct; vm_compute; reflexivity|].
  (* [simpl; lia], not [reflexivity]: the mutation [iotaatleast-at-least]
     turns this equation into [>=], and [reflexivity] is sensitive to the
     *shape* of [IotaAtLeast] rather than to its content. *)
  split; [simpl; lia|].
  apply no_k_sunflower_short_family; simpl; lia.
Qed.

Theorem iota_at_least_power :
  forall a p t, IotaAtLeast a p -> 1 <= t -> IotaAtLeast (t * a) (p ^ t).
Proof.
  intros a p t HL Ht.
  induction t as [|t IH]; [lia|].
  destruct (Nat.eq_dec t 0) as [E | Hne].
  - subst t; simpl; rewrite Nat.mul_1_r, Nat.add_0_r.
    replace (a + 0) with a by lia; exact HL.
  - replace (S t * a) with (a + t * a) by lia.
    replace (p ^ S t) with (p * p ^ t) by reflexivity.
    exact (iota_supermultiplicative a (t * a) p (p ^ t) HL (IH ltac:(lia))).
Qed.

(** ** [iota(1) = 1] from above, which the induction below needs *)

Theorem iota_one_at_most_one : IotaAtMost 1 1.
Proof.
  intros H HU HD HI Hno.
  destruct H as [|A [|B H']]; simpl; [lia | lia |].
  exfalso.
  unfold Uniform in HU; rewrite Forall_forall in HU.
  destruct (HU A (or_introl eq_refl)) as [HlA _].
  destruct (HU B (or_intror (or_introl eq_refl))) as [HlB _].
  destruct A as [|a [|? ?]]; simpl in HlA; try discriminate.
  destruct B as [|b [|? ?]]; simpl in HlB; try discriminate.
  (* Two distinct singletons: intersecting forces [a = b], distinctness
     forbids it. *)
  assert (Hab : a = b).
  { destruct (Nat.eq_dec a b) as [E | Hne]; [exact E | exfalso].
    apply (HI [a] [b] (or_introl eq_refl) (or_intror (or_introl eq_refl))).
    intros x [E | []] [E' | []]; subst; contradiction. }
  subst b.
  inversion HD as [|? ? Hni _]; subst.
  exact (Hni [a] (or_introl eq_refl) (SetEq_refl [a])).
Qed.

(** ** [g(1) = 2] and [iota(2) <= 4], which the constant below needs

    [SmallCases.f_1_k_eq_k] gives [f(1,3) = 3], hence [g(1) = 2]. Feeding
    that to [Intersecting.intersecting_link_bound] at [b = 2] gives
    [iota(2) <= 2 * 2 = 4]; the measured value is 3, and 4 is enough. *)

Lemma g_one_at_most_two : GAtMost 1 2.
Proof.
  intros F HU HD Hno.
  destruct (le_lt_dec (length F) 2) as [Hle | Hlt]; [exact Hle | exfalso].
  assert (Hk : 2 <= 3) by lia.
  apply Hno.
  apply (@upper_bound_1_k 3 Hk); [exact HU | exact HD | lia].
Qed.

Lemma iota_two_at_most_four : IotaAtMost 2 4.
Proof.
  intros H HU HD HI Hno.
  replace 4 with (2 * 2) by reflexivity.
  apply (intersecting_link_bound 2 2 H ltac:(lia) HU HD HI Hno).
  intros G HUG HDG HnoG; simpl in HUG.
  exact (g_one_at_most_two G HUG HDG HnoG).
Qed.

(** ** Two sufficient conditions, and the constant each gives

    [IotaSubMultiplicative D] is the tensor-power hypothesis: the defect
    in [iota(a+b) >= iota(a) iota(b)] is bounded. [IotaStepBounded D] is
    the weaker, local one: the ratio [iota(b+1)/iota(b)] is bounded.
    Both are stated relationally, because neither [iota] nor [g] is a
    function in this development. *)

Definition IotaSubMultiplicative (D : nat) : Prop :=
  forall a b p q,
    1 <= a -> 1 <= b ->
    IotaAtMost a p -> IotaAtMost b q -> IotaAtMost (a + b) (D * p * q).

Definition IotaStepBounded (D : nat) : Prop :=
  forall b p, 1 <= b -> IotaAtMost b p -> IotaAtMost (S b) (D * p).

(** The tensor-power hypothesis is the stronger of the two: take
    [a = 1], where [iota(1) = 1]. *)

Theorem submultiplicative_gives_step_bounded :
  forall D, IotaSubMultiplicative D -> IotaStepBounded D.
Proof.
  intros D HS b p Hb Hp.
  replace (S b) with (1 + b) by lia.
  replace (D * p) with (D * 1 * p) by lia.
  exact (HS 1 b 1 p ltac:(lia) Hb iota_one_at_most_one Hp).
Qed.

(** And the local hypothesis already gives the exponential bound, with
    base [D]: iterating [iota(b+1) <= D iota(b)] from [iota(1) = 1]. *)

Theorem step_bounded_gives_explicit_bound :
  forall D, IotaStepBounded D -> forall b, 1 <= b -> IotaAtMost b (D ^ (b - 1)).
Proof.
  intros D HS b; induction b as [|b IH]; intros Hb; [lia|].
  destruct (Nat.eq_dec b 0) as [E | Hne].
  - subst b; simpl; exact iota_one_at_most_one.
  - assert (Hprev : IotaAtMost b (D ^ (b - 1))) by (apply IH; lia).
    pose proof (HS b (D ^ (b - 1)) ltac:(lia) Hprev) as Hstep.
    (* [D * D^(b-1) = D^b = D^(S b - 1)] *)
    replace (S b - 1) with b by lia.
    replace (D ^ b) with (D * D ^ (b - 1)); [exact Hstep|].
    replace b with (S (b - 1)) at 2 by lia.
    reflexivity.
Qed.

Theorem step_bounded_gives_iota_exponential :
  forall D, IotaStepBounded D -> IotaExponential.
Proof.
  intros D HS; exists (S D); intros b Hb H HU HD HI Hno.
  pose proof (step_bounded_gives_explicit_bound D HS b Hb H HU HD HI Hno) as Hle.
  (* [S D] rather than [D] so the statement holds at [D = 0] too, where
     [D ^ 0 = 1] exceeds [D ^ 1 = 0]. The hypothesis is false at [D = 0]
     -- [step_bounded_needs_D_at_least_three] proves [D >= 3] -- but the
     theorem should not need that. *)
  assert (Hm1 : D ^ (b - 1) <= S D ^ (b - 1)) by (apply Nat.pow_le_mono_l; lia).
  assert (Hm2 : S D ^ (b - 1) <= S D ^ b) by (apply Nat.pow_le_mono_r; lia).
  lia.
Qed.

(** **The statement this half of the file exists for.** A bounded ratio
    settles Erdős's $1000 case, with the constant visible. *)

Theorem step_bounded_settles_k3 :
  forall D, IotaStepBounded D -> sunflower_conjecture_k_3.
Proof.
  intros D HS.
  apply (proj2 conjecture_k_3_iff_iota_exponential).
  exact (step_bounded_gives_iota_exponential D HS).
Qed.

Theorem submultiplicative_settles_k3 :
  forall D, IotaSubMultiplicative D -> sunflower_conjecture_k_3.
Proof.
  intros D HS.
  exact (step_bounded_settles_k3 D (submultiplicative_gives_step_bounded D HS)).
Qed.

(** With the constant spelled out: [c(3) = 2D]. Through
    [IotaRate.iota_bound_settles_k_3], so the factor [2b] of the sandwich
    is what turns [D] into [2D]. *)

Corollary step_bounded_gives_the_constant :
  forall D, IotaStepBounded D ->
    forall n, 1 <= n -> UpperBound n 3 (S ((2 * S D) ^ n)).
Proof.
  intros D HS n Hn.
  apply iota_bound_settles_k_3; [|exact Hn].
  intros b Hb H HU HD HI Hno.
  pose proof (step_bounded_gives_explicit_bound D HS b Hb H HU HD HI Hno) as Hle.
  assert (Hm1 : D ^ (b - 1) <= S D ^ (b - 1)) by (apply Nat.pow_le_mono_l; lia).
  assert (Hm2 : S D ^ (b - 1) <= S D ^ b) by (apply Nat.pow_le_mono_r; lia).
  lia.
Qed.

(** ** The cone

    A point not used by any member. Stated as a predicate rather than
    "outside a ground set", because [LowerBound] hands over a family on
    no named ground set at all. *)

Definition Fresh (p : nat) (F : Family) : Prop :=
  forall A, In A F -> ~ In p A.

Fixpoint maxall (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: l' => Nat.max x (maxall l')
  end.

Lemma maxall_ge : forall l x, In x l -> x <= maxall l.
Proof.
  induction l as [|y l IH]; intros x Hx; [inversion Hx|].
  destruct Hx as [E | Hx]; simpl; [subst; lia|].
  pose proof (IH x Hx); lia.
Qed.

Definition fresh_point (F : Family) : nat := S (maxall (concat F)).

Lemma fresh_point_is_fresh : forall F, Fresh (fresh_point F) F.
Proof.
  intros F A HA Hin.
  assert (Hc : In (fresh_point F) (concat F))
    by (apply in_concat; exists A; split; assumption).
  pose proof (maxall_ge (concat F) (fresh_point F) Hc) as Hle.
  unfold fresh_point in Hle; lia.
Qed.

(** The other way to certify freshness, for the concrete families
    below: a point outside a ground set is fresh for anything grounded
    there. *)

Lemma Fresh_of_Grounded :
  forall p F U, Grounded F U -> ~ In p U -> Fresh p F.
Proof. intros p F U HG Hp A HA Hin; exact (Hp (HG A HA p Hin)). Qed.

Definition cone (p : nat) (F : Family) : Family := map (fun A => p :: A) F.

Lemma cone_length : forall p F, length (cone p F) = length F.
Proof. intros p F; unfold cone; apply map_length. Qed.

Lemma in_cone_iff :
  forall p F B, In B (cone p F) <-> exists A, In A F /\ B = p :: A.
Proof.
  intros p F B; unfold cone; rewrite in_map_iff; split.
  - intros [A [E HA]]; exists A; split; [exact HA | symmetry; exact E].
  - intros [A [HA E]]; exists A; split; [symmetry; exact E | exact HA].
Qed.

Lemma cone_Uniform :
  forall m p F, Fresh p F -> Uniform m F -> Uniform (S m) (cone p F).
Proof.
  intros m p F Hfr HU; unfold Uniform; apply Forall_forall; intros B HB.
  apply (proj1 (in_cone_iff _ _ _)) in HB as [A [HA E]]; subst B.
  unfold Uniform in HU; rewrite Forall_forall in HU.
  destruct (HU A HA) as [Hlen Hnd].
  split; [simpl; lia | constructor; [exact (Hfr A HA) | exact Hnd]].
Qed.

Lemma SetEq_cons_mono :
  forall p A B, SetEq A B -> SetEq (p :: A) (p :: B).
Proof.
  intros p A B [H1 H2]; split; intros x [E | Hx];
    [ left; exact E | right; apply H1; exact Hx
    | left; exact E | right; apply H2; exact Hx ].
Qed.

Lemma SetEq_cons_cancel :
  forall p A B, ~ In p A -> ~ In p B -> SetEq (p :: A) (p :: B) -> SetEq A B.
Proof.
  intros p A B HA HB [H1 H2]; split; intros x Hx.
  - destruct (H1 x (or_intror Hx)) as [E | H];
      [exfalso; apply HA; rewrite E; exact Hx | exact H].
  - destruct (H2 x (or_intror Hx)) as [E | H];
      [exfalso; apply HB; rewrite E; exact Hx | exact H].
Qed.

Lemma cone_Distinct :
  forall p F, Fresh p F -> Distinct F -> Distinct (cone p F).
Proof.
  intros p F Hfr HD; unfold Distinct in *; revert Hfr.
  induction HD as [|A F Hni HD IH]; intros Hfr; simpl; [constructor|].
  constructor.
  - intros B HB Hseq.
    apply (proj1 (in_cone_iff _ _ _)) in HB as [B0 [HB0 E]]; subst B.
    apply (Hni B0 HB0).
    apply (SetEq_cons_cancel p A B0);
      [ apply Hfr; left; reflexivity
      | apply Hfr; right; exact HB0
      | exact Hseq ].
  - apply IH; intros X HX; apply Hfr; right; exact HX.
Qed.

(** Intersecting-ness comes for **free**, with no hypothesis whatever:
    every member contains [p]. That is the whole content of the cone, and
    the reason it says the intersecting hypothesis is worth one point of
    uniformity and nothing more. *)

Lemma cone_Intersecting : forall p F, Intersecting (cone p F).
Proof.
  intros p F A B HA HB Hdis.
  apply (proj1 (in_cone_iff _ _ _)) in HA as [A0 [_ EA]].
  apply (proj1 (in_cone_iff _ _ _)) in HB as [B0 [_ EB]].
  subst A B.
  apply (Hdis p); left; reflexivity.
Qed.

(** ** Sunflower-freeness survives the cone

    Three members of the cone have pairwise intersections
    [(A_i ∩ A_j) ∪ {p}]; those are all equal exactly when the
    [A_i ∩ A_j] are. Two small set-algebra lemmas do all of it. *)

Lemma filter_ext_on_list :
  forall (f g : nat -> bool) (l : list nat),
    (forall x, In x l -> f x = g x) -> filter f l = filter g l.
Proof.
  intros f g l H; induction l as [|a l IH]; [reflexivity|].
  simpl; rewrite (H a (or_introl eq_refl)).
  assert (IH' : filter f l = filter g l)
    by (apply IH; intros x Hx; apply H; right; exact Hx).
  destruct (g a); rewrite IH'; reflexivity.
Qed.

Lemma inter_cons_fresh :
  forall p A B, ~ In p A -> inter A (p :: B) = inter A B.
Proof.
  intros p A B Hp; unfold inter.
  apply filter_ext_on_list; intros x Hx.
  assert (Hxp : x <> p) by (intro E; subst; contradiction).
  destruct (in_dec_nat x (p :: B)) as [Hin | Hnin];
    destruct (in_dec_nat x B) as [Hin2 | Hnin2]; try reflexivity.
  - exfalso; destruct Hin as [E | H];
      [apply Hxp; symmetry; exact E | exact (Hnin2 H)].
  - exfalso; apply Hnin; right; exact Hin2.
Qed.

(** [simpl] is unusable here: [Sets.in_dec_nat] is transparent, so it
    unfolds into a nest of [Nat.eq_dec] matches and nothing matches
    afterwards. The head step is taken with [f] abstract instead. *)

Lemma filter_cons_true :
  forall (f : nat -> bool) a l, f a = true -> filter f (a :: l) = a :: filter f l.
Proof. intros f a l H; simpl; rewrite H; reflexivity. Qed.

Lemma inter_cone :
  forall p A B, ~ In p A -> inter (p :: A) (p :: B) = p :: inter A B.
Proof.
  intros p A B HA.
  assert (Hp : (fun x : nat => if in_dec_nat x (p :: B) then true else false) p
               = true).
  { destruct (in_dec_nat p (p :: B)) as [_ | Hnin];
      [reflexivity | exfalso; apply Hnin; left; reflexivity]. }
  unfold inter.
  rewrite (filter_cons_true _ p A Hp).
  f_equal.
  exact (inter_cons_fresh p A B HA).
Qed.

Lemma not_in_inter_l : forall p A B, ~ In p A -> ~ In p (inter A B).
Proof. intros p A B H Hin; apply in_inter_iff in Hin; tauto. Qed.

Theorem cone_no_sunflower :
  forall p F,
    Fresh p F -> ~ ContainsKSunflower 3 F -> ~ ContainsKSunflower 3 (cone p F).
Proof.
  intros p F Hfr Hno Hc.
  destruct (contains_sunflower_literal 3 (cone p F) Hc)
    as [S [core [Hincl [Hnd [Hlen Hsun]]]]].
  destruct S as [|X [|Y [|Z [|W S']]]]; simpl in Hlen; try discriminate.
  destruct Hsun as [Hsnd Hcore].
  assert (HXin : In X [X; Y; Z]) by (left; reflexivity).
  assert (HYin : In Y [X; Y; Z]) by (right; left; reflexivity).
  assert (HZin : In Z [X; Y; Z]) by (right; right; left; reflexivity).
  destruct (proj1 (in_cone_iff p F X) (Hincl X HXin)) as [A [HA EX]].
  destruct (proj1 (in_cone_iff p F Y) (Hincl Y HYin)) as [B [HB EY]].
  destruct (proj1 (in_cone_iff p F Z) (Hincl Z HZin)) as [C [HC EZ]].
  subst X Y Z.
  assert (HpA : ~ In p A) by exact (Hfr A HA).
  assert (HpB : ~ In p B) by exact (Hfr B HB).
  assert (HpC : ~ In p C) by exact (Hfr C HC).
  (* The three coned members are literally distinct. *)
  apply NoDup_cons_iff in Hnd as [Hni1 Hnd1].
  apply NoDup_cons_iff in Hnd1 as [Hni2 _].
  assert (HAB : p :: A <> p :: B)
    by (intro E; apply Hni1; left; symmetry; exact E).
  assert (HAC : p :: A <> p :: C)
    by (intro E; apply Hni1; right; left; symmetry; exact E).
  assert (HBC : p :: B <> p :: C)
    by (intro E; apply Hni2; left; symmetry; exact E).
  (* Peeling the apex off a pairwise intersection: [inter (p::u) (p::v)]
     is [p :: inter u v], so each clause of the sunflower says
     [p :: inter u v] is the core. *)
  assert (Hpeel : forall u v,
             In (p :: u) [p :: A; p :: B; p :: C] ->
             In (p :: v) [p :: A; p :: B; p :: C] ->
             p :: u <> p :: v -> ~ In p u ->
             SetEq (p :: inter u v) core).
  { intros u v Hu Hv Hne Hpu.
    rewrite <- (inter_cone p u v Hpu).
    exact (Hcore (p :: u) (p :: v) Hu Hv Hne). }
  (* ... and two such statements cancel the apex against each other. *)
  assert (Hcancel : forall u v u' v',
             ~ In p u -> ~ In p u' ->
             SetEq (p :: inter u v) core -> SetEq (p :: inter u' v') core ->
             SetEq (inter u v) (inter u' v')).
  { intros u v u' v' Hpu Hpu' H1 H2.
    apply (SetEq_cons_cancel p);
      [ exact (not_in_inter_l p u v Hpu)
      | exact (not_in_inter_l p u' v' Hpu')
      | exact (SetEq_trans H1 (SetEq_sym H2)) ]. }
  pose proof (Hpeel A B HXin HYin HAB HpA) as HABc.
  pose proof (Hpeel A C HXin HZin HAC HpA) as HACc.
  pose proof (Hpeel B C HYin HZin HBC HpB) as HBCc.
  (* And they are pairwise not *set*-equal, which is what [SetNoDup]
     asks: a set-equality upstairs would be one downstairs. *)
  assert (Hnse : forall u v,
             In (p :: u) [p :: A; p :: B; p :: C] ->
             In (p :: v) [p :: A; p :: B; p :: C] ->
             p :: u <> p :: v -> ~ SetEq u v).
  { intros u v Hu Hv Hne Hseq.
    exact (SetNoDup_pairwise Hsnd Hu Hv Hne (SetEq_cons_mono p u v Hseq)). }
  apply Hno.
  apply (@ContainsKSunflower_of_incl 3 [A; B; C] F (inter A B)).
  - intros U [E | [E | [E | []]]]; subst U; assumption.
  - reflexivity.
  - split.
    + constructor.
      { intros V [E | [E | []]]; subst V;
          [ exact (Hnse A B HXin HYin HAB)
          | exact (Hnse A C HXin HZin HAC) ]. }
      constructor.
      { intros V [E | []]; subst V.
        exact (Hnse B C HYin HZin HBC). }
      constructor.
      { intros V []. }
      constructor.
    + intros U V HU HV Hne.
      destruct HU as [E1 | [E1 | [E1 | []]]];
        destruct HV as [E2 | [E2 | [E2 | []]]];
        subst U V; try (exfalso; apply Hne; reflexivity).
      * apply SetEq_refl.
      * exact (Hcancel A C A B HpA HpA HACc HABc).
      * exact (inter_comm_SetEq B A).
      * exact (Hcancel B C A B HpB HpA HBCc HABc).
      * exact (SetEq_trans (inter_comm_SetEq C A)
                 (Hcancel A C A B HpA HpA HACc HABc)).
      * exact (SetEq_trans (inter_comm_SetEq C B)
                 (Hcancel B C A B HpB HpA HBCc HABc)).
Qed.

(** ** The cone lower bound: [g(m) <= iota(m+1)]

    The family arrives from [LowerBound] with the size stated as an
    equation, and the mutation [lowerbound-at-least] weakens that to an
    inequality. So the proof **trims** the family to length exactly [j]
    rather than passing it through, which is the rule
    [docs/testing.md] §4 states for exactly this shape of proof. *)

Theorem iota_at_least_g_pred :
  forall m j, LowerBound m 3 j -> IotaAtLeast (S m) j.
Proof.
  intros m j [F [HU [HD [Hlen Hno]]]].
  pose proof Hlen as Hge.
  set (G := firstn j F).
  assert (HinclG : incl G F) by (unfold G; apply incl_firstn).
  assert (HUG : Uniform m G) by exact (Uniform_sublist HU HinclG).
  assert (HDG : Distinct G)
    by exact (SetNoDup_incl HD (NoDup_firstn j (SetNoDup_NoDup HD)) HinclG).
  assert (HlenG : length G = j)
    by (unfold G; rewrite firstn_length_le; lia).
  assert (HnoG : ~ ContainsKSunflower 3 G)
    by (intro Hc; exact (Hno (contains_sunflower_incl HinclG Hc))).
  set (p := fresh_point G).
  assert (Hfr : Fresh p G) by exact (fresh_point_is_fresh G).
  exists (cone p G).
  split; [exact (cone_Uniform m p G Hfr HUG)|].
  split; [exact (cone_Distinct p G Hfr HDG)|].
  split; [exact (cone_Intersecting p G)|].
  split; [rewrite cone_length; lia|].
  exact (cone_no_sunflower p G Hfr HnoG).
Qed.

(** **The transfer.** An upper bound on [iota] at uniformity [m+1] is an
    upper bound on [g] at uniformity [m]. Compare
    [Intersecting.intersecting_link_bound], which is the same statement
    with a factor [b] and in the other direction. *)

Theorem iota_bound_bounds_g :
  forall m N, IotaAtMost (S m) N -> GAtMost m N.
Proof.
  intros m N Hiota F HU HD Hno.
  set (p := fresh_point F).
  assert (Hfr : Fresh p F) by exact (fresh_point_is_fresh F).
  pose proof (Hiota (cone p F)
                (cone_Uniform m p F Hfr HU)
                (cone_Distinct p F Hfr HD)
                (cone_Intersecting p F)
                (cone_no_sunflower p F Hfr Hno)) as Hle.
  rewrite cone_length in Hle; exact Hle.
Qed.

(** The second sandwich, in the *uniformity* rather than in the size:

    >  g(b-1)  <=  iota(b)  <=  b * g(b-1).

    The right half is [Intersecting.intersecting_link_bound]. Together
    with [IotaRate.iota_g_sandwich] this pins [iota] and [g] to each
    other in both variables. *)

Theorem iota_g_sandwich_shifted :
  forall m M,
    1 <= m ->
    GAtMost m M ->
    ((forall j, LowerBound m 3 j -> IotaAtLeast (S m) j)
     /\ IotaAtMost (S m) (S m * M)).
Proof.
  intros m M Hm Hg; split.
  - exact (iota_at_least_g_pred m).
  - intros H HU HD HI Hno.
    apply (intersecting_link_bound (S m) M H ltac:(lia) HU HD HI Hno).
    intros G HUG HDG HnoG.
    replace (S m - 1) with m in HUG by lia.
    exact (Hg G HUG HDG HnoG).
Qed.

(** ** What a bound on [iota(4)] would cost

    [docs/roadmap.md] §7 names "is [iota(4,10)] 28 or does it stay at
    27?" as the decisive experiment for [IotaGroundBounded], and §9
    records that neither the branch-and-bound nor the SAT layer decides
    it. The transfer says why that is not surprising: an affirmative
    answer *in the plateau sense* — a proof of [iota(4) <= 27] — would
    give [f(3,3) <= 28], where Erdős–Rado gives 49 and the best known
    lower bound here is [f(3,3) >= 21]
    ([Intersecting.lower_bound_3_3_20]).

    So the ladder is not a computation waiting for a bigger budget. It is
    at least as hard as a new bound on the first unknown sunflower
    number. *)

Theorem iota_four_at_most_27_would_beat_erdos_rado :
  IotaAtMost 4 27 -> UpperBound 3 3 28 /\ ~ UpperBound 3 3 20 /\ 28 < 49.
Proof.
  intros H27; split.
  - replace 28 with (S 27) by reflexivity.
    apply (upper_bound_of_sunflower_free_bound 3 27).
    intros F HU HD Hno.
    pose proof (iota_bound_bounds_g 3 27 H27 F HU HD Hno) as Hle; lia.
  - split; [exact no_upper_bound_3_3_20 | lia].
Qed.

(** The general shape of it, so the [b = 4] instance is not a special
    case: every upper bound on [iota] one uniformity up is an
    [UpperBound]. *)

Corollary iota_bound_gives_upper_bound :
  forall m N, 1 <= m -> IotaAtMost (S m) N -> UpperBound m 3 (S N).
Proof.
  intros m N Hm Hiota.
  apply (upper_bound_of_sunflower_free_bound m N).
  exact (iota_bound_bounds_g m N Hiota).
Qed.

(** ** The two ground-set hypotheses are not independent

    [IotaGround.both_ground_hypotheses_settle_k3] puts [GroundBounded]
    and [IotaGroundBounded] side by side and says "neither implies the
    other; what separates them is that one has a measurement behind it".
    The first half of that is wrong, and this is the correction.

    One direction needs nothing at all: an intersecting sunflower-free
    family *is* a sunflower-free family, and [IotaGroundBounded]'s
    existential does not ask its witness to be intersecting or even
    uniform. *)

Theorem ground_bounded_implies_iota_ground_bounded :
  forall c, GroundBounded c -> IotaGroundBounded c.
Proof.
  intros c HGB b H Hb HU HD HI Hno.
  (* [lia], not [assumption], on the size clause: the mutation
     [lowerbound-at-least] turns [LowerBound]'s equation into [>=], and
     [assumption] would be looking for a hypothesis of the wrong shape.
     The standing rule of [docs/testing.md] §4 applies to *producing* a
     [LowerBound] as much as to consuming one. *)
  assert (HL : LowerBound b 3 (length H)).
  { exists H; split; [exact HU|]; split; [exact HD|]; split; [lia | exact Hno]. }
  destruct (HGB b (length H) Hb HL)
    as [F [U [HunF [HdF [HlenF [HnoF [HndU [HG Hu]]]]]]]].
  exists F, U; repeat split; assumption.
Qed.

(** The other direction, through the cone. It is not literally
    [GroundBounded] — the uniformity shifts by one, so the bound is
    [c * (m + 1)] rather than [c * m] — but that is a change of constant
    and nothing else, and the conclusion the hypothesis exists to reach
    is identical. *)

Theorem iota_ground_bounded_bounds_the_general_row :
  forall c, IotaGroundBounded c ->
    forall m j, 1 <= m -> LowerBound m 3 j ->
      exists (F' : Family) (U : list nat),
        Distinct F' /\ length F' = j /\ ~ ContainsKSunflower 3 F'
        /\ NoDup U /\ Grounded F' U /\ length U <= c * (m + 1).
Proof.
  intros c HIGB m j Hm HL.
  destruct (iota_at_least_g_pred m j HL) as [H [HU [HD [HI [Hlen Hno]]]]].
  destruct (HIGB (S m) H ltac:(lia) HU HD HI Hno)
    as [H' [U [HD' [Hlen' [Hno' [HndU [HG Hu]]]]]]].
  (* [H'] has [length H] members and [length H] is at least [j], so the
     family of exactly [j] members is obtained by *trimming* -- the rule
     [docs/testing.md] §4 states for proofs that need an exact size, here
     for [IotaAtLeast] rather than for [LowerBound]. *)
  set (G := firstn j H').
  assert (Hincl : incl G H') by (unfold G; apply incl_firstn).
  exists G, U; repeat split.
  - exact (SetNoDup_incl HD' (NoDup_firstn j (SetNoDup_NoDup HD')) Hincl).
  - unfold G; rewrite firstn_length_le; lia.
  - intro Hc; exact (Hno' (contains_sunflower_incl Hincl Hc)).
  - exact HndU.
  - intros A HA; exact (HG A (Hincl A HA)).
  - lia.
Qed.

(** Hence the general row is exponentially bounded by the *intersecting*
    hypothesis alone, by counting — the same route
    [IotaGround.ground_bounded_settles_k3_by_counting] takes, now run
    from the hypothesis that has the measurement behind it. *)

Corollary iota_ground_bounded_bounds_g_by_counting :
  forall c, IotaGroundBounded c ->
    forall m j, 1 <= m -> LowerBound m 3 j -> j <= (2 ^ c) ^ (m + 1).
Proof.
  intros c HIGB m j Hm HL.
  destruct (iota_ground_bounded_bounds_the_general_row c HIGB m j Hm HL)
    as [F' [U [HD' [Hlen' [Hno' [HndU [HG Hu]]]]]]].
  assert (Hb : length F' <= 2 ^ length U)
    by (apply grounded_family_at_most_two_to_the_ground with (U := U); assumption).
  assert (Hmono : 2 ^ length U <= 2 ^ (c * (m + 1)))
    by (apply Nat.pow_le_mono_r; lia).
  rewrite <- Nat.pow_mul_r; lia.
Qed.

Theorem the_two_ground_hypotheses_are_not_independent :
  forall c,
    (GroundBounded c -> IotaGroundBounded c)
    /\ (IotaGroundBounded c ->
        forall m j, 1 <= m -> LowerBound m 3 j -> j <= (2 ^ c) ^ (m + 1)).
Proof.
  intros c; split;
    [ exact (ground_bounded_implies_iota_ground_bounded c)
    | exact (iota_ground_bounded_bounds_g_by_counting c) ].
Qed.

(** ** The universal reading of [IotaGroundBounded] is false too

    [IotaGround.v] says of [IotaGroundBounded]: "The data says the
    extremal intersecting sunflower-free family literally lives on
    [O(b)] points". That reading is false, for the same reason
    [IotaGround.the_universal_ground_reading_is_false] kills it for
    [GroundBounded] — and the witness is the cone of the very family that
    kills it there.

    [IotaGround.tree_paths_three] is eight triples on fourteen points,
    sunflower-free, and *not* intersecting (the paths through different
    children of the root are disjoint). Coning it fixes exactly that: the
    apex is the stem edge above the root. The result is eight 4-sets on
    fifteen points, intersecting, sunflower-free, and it does not fit on
    fourteen — against [4 * 4 = 16], so this instance alone does not
    refute [c = 4]. What it refutes is the *literal* reading, and the
    general construction has [2^(b-1)] members on [2^b - 1] points, which
    outgrows [c * b] for every [c]; [rust/tests/iota_structure.rs] checks
    it to [b = 7], where 64 members need 127 points against [7c].

    Note which way this cuts, exactly as there: it does **not** conflict
    with the flat [iota(3,g)] row, which measures the largest family *on*
    [g] points. *)

Definition cone_tree_paths_three : Family := cone 14 tree_paths_three.

Lemma cone_tree_paths_three_value :
  cone_tree_paths_three
  = [[14; 0; 2; 6]; [14; 0; 2; 7]; [14; 0; 3; 8]; [14; 0; 3; 9];
     [14; 1; 4; 10]; [14; 1; 4; 11]; [14; 1; 5; 12]; [14; 1; 5; 13]].
Proof. vm_compute; reflexivity. Qed.

Lemma tree_paths_three_fresh_at_14 : Fresh 14 tree_paths_three.
Proof.
  apply (Fresh_of_Grounded 14 tree_paths_three (seq 0 14));
    [exact tree_paths_three_grounded | rewrite in_seq; lia].
Qed.

Lemma cone_tree_paths_three_grounded : Grounded cone_tree_paths_three (seq 0 15).
Proof.
  unfold Grounded.
  apply (proj1 (groundedb_correct cone_tree_paths_three (seq 0 15))).
  vm_compute; reflexivity.
Qed.

Lemma cone_tree_paths_three_needs_fifteen :
  ~ Grounded cone_tree_paths_three (seq 0 14).
Proof.
  intro HG.
  assert (Hin : In [14; 1; 5; 13] cone_tree_paths_three) by (vm_compute; tauto).
  specialize (HG _ Hin 14 ltac:(vm_compute; tauto)).
  rewrite in_seq in HG; lia.
Qed.

Theorem the_universal_iota_ground_reading_is_false :
  Uniform 4 cone_tree_paths_three
  /\ Distinct cone_tree_paths_three
  /\ Intersecting cone_tree_paths_three
  /\ ~ ContainsKSunflower 3 cone_tree_paths_three
  /\ length cone_tree_paths_three = 8
  /\ Grounded cone_tree_paths_three (seq 0 15)
  /\ ~ Grounded cone_tree_paths_three (seq 0 14).
Proof.
  split; [apply uniformb_correct; vm_compute; reflexivity|].
  split; [apply distinctb_correct; vm_compute; reflexivity|].
  split; [apply intersectingb_correct; vm_compute; reflexivity|].
  split.
  { replace cone_tree_paths_three with (cone 14 tree_paths_three) by reflexivity.
    apply cone_no_sunflower;
      [exact tree_paths_three_fresh_at_14 | exact tree_paths_three_no_sunflower]. }
  split; [vm_compute; reflexivity|].
  split; [exact cone_tree_paths_three_grounded
        | exact cone_tree_paths_three_needs_fifteen].
Qed.

(** ** The diagnosis: only the empty core is cheap

    [Compression.only_the_empty_core_survives_compression] says shifting
    commutes with the [Y = ∅] clause of
    [LinkCharacterisation.sunflower_iff_link_matching] and with no other.
    The cone is the same phenomenon from the other side, and this is the
    lemma that makes it precise: coning **imposes** the empty-core clause
    and leaves every other clause literally where it was.

    [link [p] (cone p F) = F] — on the nose, not up to set equality. *)

Lemma filter_true_id : forall (l : list nat), filter (fun _ => true) l = l.
Proof. induction l as [|a l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma filter_cons_false :
  forall (f : nat -> bool) a l, f a = false -> filter f (a :: l) = filter f l.
Proof. intros f a l H; simpl; rewrite H; reflexivity. Qed.

Lemma filter_all_true_family :
  forall (f : list nat -> bool) (l : Family),
    (forall A, In A l -> f A = true) -> filter f l = l.
Proof.
  intros f l H; induction l as [|A l IH]; [reflexivity|]; simpl.
  rewrite (H A (or_introl eq_refl)); f_equal.
  apply IH; intros X HX; apply H; right; exact HX.
Qed.

Lemma map_id_on_family :
  forall (f : list nat -> list nat) (l : Family),
    (forall A, In A l -> f A = A) -> map f l = l.
Proof.
  intros f l H; induction l as [|A l IH]; [reflexivity|]; simpl.
  rewrite (H A (or_introl eq_refl)); f_equal.
  apply IH; intros X HX; apply H; right; exact HX.
Qed.

Lemma setminus_singleton_fresh :
  forall p A, ~ In p A -> setminus A [p] = A.
Proof.
  intros p A H; unfold setminus.
  rewrite (filter_ext_on_list (fun x => negb (memb x [p])) (fun _ => true) A).
  - apply filter_true_id.
  - intros x Hx.
    assert (Hxp : x <> p) by (intro E; subst; contradiction).
    assert (E : memb x [p] = false)
      by (apply memb_false_iff; intros [E' | []]; apply Hxp; symmetry; exact E').
    rewrite E; reflexivity.
Qed.

Lemma setminus_cons_self :
  forall p A, ~ In p A -> setminus (p :: A) [p] = A.
Proof.
  intros p A H.
  assert (Hm : negb (memb p [p]) = false).
  { assert (E : memb p [p] = true) by (apply memb_true_iff; left; reflexivity).
    rewrite E; reflexivity. }
  unfold setminus.
  rewrite (filter_cons_false (fun x => negb (memb x [p])) p A Hm).
  exact (setminus_singleton_fresh p A H).
Qed.

Lemma filter_containsb_cone :
  forall p F, filter (containsb [p]) (cone p F) = cone p F.
Proof.
  intros p F; apply filter_all_true_family; intros B HB.
  apply (proj1 (in_cone_iff _ _ _)) in HB as [A [_ E]]; subst B.
  rewrite containsb_singleton; apply memb_true_iff; left; reflexivity.
Qed.

Lemma map_setminus_cone :
  forall p F, Fresh p F -> map (fun A => setminus A [p]) (cone p F) = F.
Proof.
  intros p F Hfr; unfold cone; rewrite map_map.
  apply map_id_on_family; intros A HA.
  exact (setminus_cons_self p A (Hfr A HA)).
Qed.

Lemma link_of_cone :
  forall p F, Fresh p F -> link [p] (cone p F) = F.
Proof.
  intros p F Hfr; unfold link.
  rewrite filter_containsb_cone.
  exact (map_setminus_cone p F Hfr).
Qed.

(** The two operations, side by side. Shifting is a homomorphism for the
    empty-core clause and for no other; coning satisfies the empty-core
    clause outright and is the identity on every other clause. Both say
    the same thing about the conjunction: **the [Y = ∅] clause is the
    cheap one, and it is Erdős–Ko–Rado's.** *)

Theorem only_the_empty_core_is_cheap :
  (* the cone imposes the empty-core clause with no hypothesis ... *)
  (forall p F, Intersecting (cone p F))
  (* ... and is literally the identity on every other clause ... *)
  /\ (forall p F, Fresh p F -> link [p] (cone p F) = F)
  (* ... while the empty-core clause *is* intersecting-ness ... *)
  /\ (forall F : Family, Intersecting F -> ~ HasKDisjoint 2 (link [] F))
  (* ... and the general problem re-enters through the cone. *)
  /\ (forall m j, LowerBound m 3 j -> IotaAtLeast (S m) j).
Proof.
  split; [exact cone_Intersecting|].
  split; [exact link_of_cone|].
  split; [|exact iota_at_least_g_pred].
  intros F HI; rewrite link_nil.
  exact (intersecting_is_the_empty_core_at_two HI).
Qed.

(** ** Why a splitting argument cannot use the intersecting hypothesis

    The route to submultiplicativity is to partition the ground set into
    [X] and [Y], bucket the members of [F] by the trace [P = A ∩ X], and
    bound each fibre. The prediction written down before any of this was
    computed was that the fibres over a *nonempty* trace lose
    intersecting-ness, so they are bounded by [g] and not by [iota] — and
    the cone is the extremal witness for exactly that.

    Take [X = {p}]. The cone of a [g]-extremal family has one nonempty
    trace, namely [{p}], and its fibre is [link [p] (cone p F) = F]: the
    original family, which is a general sunflower-free family of the
    largest possible size and is **not** intersecting. So no bound on the
    fibres of a split can be a bound on [iota]; the best the split gives
    is

    >  iota(b)  <=  (number of traces) * g(b-1),

    which at [b] traces is [Intersecting.intersecting_link_bound] and
    Erdős–Rado's rate. Formally: for every sunflower-free family
    whatever, there is an intersecting sunflower-free family one
    uniformity up whose fibre over its own trace is that family. *)

Theorem the_split_fibres_are_not_intersecting :
  forall m (F : Family),
    Uniform m F -> Distinct F -> ~ ContainsKSunflower 3 F ->
    exists (p : nat) (H : Family),
      Uniform (S m) H /\ Distinct H /\ Intersecting H
      /\ ~ ContainsKSunflower 3 H
      /\ length H = length F
      /\ link [p] H = F.
Proof.
  intros m F HU HD Hno.
  set (p := fresh_point F).
  assert (Hfr : Fresh p F) by exact (fresh_point_is_fresh F).
  exists p, (cone p F).
  split; [exact (cone_Uniform m p F Hfr HU)|].
  split; [exact (cone_Distinct p F Hfr HD)|].
  split; [exact (cone_Intersecting p F)|].
  split; [exact (cone_no_sunflower p F Hfr Hno)|].
  split; [exact (cone_length p F) | exact (link_of_cone p F Hfr)].
Qed.

(** The numerical form of the same thing, and the reason it is fatal
    rather than merely inconvenient. Cone [F23.two_triangles], the family
    that attains [f(2,3) - 1 = 6]. The result is an intersecting
    3-uniform sunflower-free family of six members whose fibre over its
    own trace is [two_triangles] itself — which is **not** intersecting,
    and is twice the size of [iota(2) = 3].

    So the fibre bound in any split is a bound on [g], and the
    intersecting hypothesis is not available inside it. *)

Definition cone_two_triangles : Family := cone 6 two_triangles.

Lemma two_triangles_grounded : Grounded two_triangles (seq 0 6).
Proof.
  unfold Grounded.
  apply (proj1 (groundedb_correct two_triangles (seq 0 6))).
  vm_compute; reflexivity.
Qed.

Lemma two_triangles_fresh_at_6 : Fresh 6 two_triangles.
Proof.
  apply (Fresh_of_Grounded 6 two_triangles (seq 0 6));
    [exact two_triangles_grounded | rewrite in_seq; lia].
Qed.

Theorem the_fibre_bound_is_g_not_iota :
  Uniform 3 cone_two_triangles
  /\ Distinct cone_two_triangles
  /\ Intersecting cone_two_triangles
  /\ ~ ContainsKSunflower 3 cone_two_triangles
  /\ length cone_two_triangles = 6
  /\ link [6] cone_two_triangles = two_triangles
  /\ ~ Intersecting two_triangles
  /\ IotaAtMost 2 4.
Proof.
  assert (Hfr : Fresh 6 two_triangles) by exact two_triangles_fresh_at_6.
  split; [exact (cone_Uniform 2 6 two_triangles Hfr two_triangles_uniform)|].
  split; [exact (cone_Distinct 6 two_triangles Hfr two_triangles_distinct)|].
  split; [exact (cone_Intersecting 6 two_triangles)|].
  split; [exact (cone_no_sunflower 6 two_triangles Hfr
                   two_triangles_no_sunflower)|].
  split; [vm_compute; reflexivity|].
  split; [exact (link_of_cone 6 two_triangles Hfr)|].
  split; [|exact iota_two_at_most_four].
  (* Two disjoint triangles are not intersecting, and the reflective
     certificate says so in both directions, so a [false] here is
     evidence against [Intersecting] rather than merely a failed check. *)
  intro HI.
  pose proof (proj2 (intersectingb_correct two_triangles) HI) as E.
  vm_compute in E; discriminate.
Qed.

(** ** The constant in [IotaStepBounded] is at least three

    The same shape as [IotaGround.ground_bounded_needs_c_at_least_four]:
    the hypothesis is not vacuous, and the data already forces its
    constant up. [iota(2) <= 4] is proved above and [iota(3) >= 10] is
    [Intersecting.iota3], so [10 <= 4D].

    Two things this pins. The step hypothesis is **not** satisfiable at
    [D = 2], which the cone alone would have suggested is the boundary:
    [iota(b+1) >= g(b) >= 2 iota(b)] means every admissible [D] is at
    least 2. And it is a genuine restriction rather than something the
    kernel already knows, since the measured ratios [3.00, 3.33, 2.70]
    sit just above 3. *)

Lemma iota_three_at_least_ten : IotaAtLeast 3 10.
Proof.
  exists iota3.
  split; [exact iota3_uniform|].
  split; [exact iota3_distinct|].
  split; [exact iota3_intersecting|].
  split; [vm_compute; lia | exact iota3_no_sunflower].
Qed.

Theorem step_bounded_needs_D_at_least_three :
  forall D, IotaStepBounded D -> 3 <= D.
Proof.
  intros D HS.
  pose proof (HS 2 4 ltac:(lia) iota_two_at_most_four) as H3.
  pose proof (iota_at_least_le_at_most 3 10 (D * 4) iota_three_at_least_ten H3) as Hle.
  lia.
Qed.

(** And the cone gives the same lower bound on [D] from the *other*
    direction, without using [iota(3) = 10] at all: the doubling
    [Intersecting.doubling_lower_bound] and the cone compose to
    [iota(b+1) >= 2 iota(b)], so no [D < 2] can work whatever the values
    are. Recorded because it is the structural half of the same fact. *)

Theorem iota_at_least_doubles :
  forall b N, 1 <= b -> IotaAtLeast b N -> IotaAtLeast (S b) (2 * N).
Proof.
  intros b N Hb HAL.
  pose proof HAL as [H [HU [HD [HI [Hlen Hno]]]]].
  (* Antitonicity, not [rewrite Hlen]: the mutation [iotaatleast-at-least]
     turns the length equation into [>=]. *)
  apply (IotaAtLeast_antitone (S b) (2 * length H) (2 * N)); [lia|].
  apply (iota_at_least_g_pred b).
  exact (doubling_lower_bound b H Hb HU HD HI Hno).
Qed.

(** ** [iota(4) >= 27], and what the doubling makes of it

    The exhaustive maximum at nine points, transcribed from
    [rust/examples/iota_witnesses.rs] and re-derived here by the
    reflective detector, so the Coq side takes nothing on the search's
    word.

    **What it is.** The structural report
    ([rust/examples/iota_structure.rs]) identifies it: split the nine
    points into three triples [{0,1,5}], [{2,3,4}], [{6,7,8}] and take
    every union of a *pair* from one triple with a *pair* from a
    different one. Three choices of unordered pair of triples, times three
    pairs, times three pairs: 27. That is exactly the
    Abbott–Hanson–Sauer substitution
    [iota(2*2) >= iota(2) * iota(2)^2 = 3 * 9], with the triangle
    substituted into itself — and its automorphism group has order
    [1296 = 6 * 6^3], which is [Sym(3)] on the triples times [Sym(3)]
    inside each, i.e. precisely the symmetry the substitution predicts.
    Cross-checked against `nauty`.

    So the extremal intersecting family at [b = 4] **is** the 1972
    construction, and the substitution is not merely a good construction
    at this uniformity: it is optimal on nine points.

    Two consequences. First the doubling
    ([Intersecting.doubling_lower_bound]) gives [g(4) >= 54], hence
    [f(4,3) >= 55] where [Audit.f_4_3_at_least_37] reached 37. Second the
    truth boundary for [iota(4)] is trapped from below in the kernel:
    [~ IotaAtMost 4 26], the analogue of
    [Audit.iota_three_between_ten_and_eighteen]. *)

Definition iota4 : Family :=
  [[0; 1; 2; 3]; [0; 1; 2; 4]; [0; 1; 3; 4]; [0; 2; 3; 5]; [1; 2; 3; 5];
   [0; 2; 4; 5]; [1; 2; 4; 5]; [0; 3; 4; 5]; [1; 3; 4; 5];
   [0; 1; 6; 7]; [2; 3; 6; 7]; [2; 4; 6; 7]; [3; 4; 6; 7]; [0; 5; 6; 7]; [1; 5; 6; 7];
   [0; 1; 6; 8]; [2; 3; 6; 8]; [2; 4; 6; 8]; [3; 4; 6; 8]; [0; 5; 6; 8]; [1; 5; 6; 8];
   [0; 1; 7; 8]; [2; 3; 7; 8]; [2; 4; 7; 8]; [3; 4; 7; 8]; [0; 5; 7; 8]; [1; 5; 7; 8]].

Lemma iota4_uniform : Uniform 4 iota4.
Proof. apply uniformb_correct; vm_compute; reflexivity. Qed.

Lemma iota4_distinct : Distinct iota4.
Proof. apply distinctb_correct; vm_compute; reflexivity. Qed.

Lemma iota4_intersecting : Intersecting iota4.
Proof. apply intersectingb_correct; vm_compute; reflexivity. Qed.

Lemma iota4_no_sunflower : ~ ContainsKSunflower 3 iota4.
Proof.
  intro Hc.
  pose proof (sunflower3b_sound iota4 Hc) as E; vm_compute in E; discriminate.
Qed.

Lemma iota4_grounded : Grounded iota4 (seq 0 9).
Proof.
  unfold Grounded.
  apply (proj1 (groundedb_correct iota4 (seq 0 9))).
  vm_compute; reflexivity.
Qed.

Theorem iota_four_at_least_27 : IotaAtLeast 4 27.
Proof.
  exists iota4.
  split; [exact iota4_uniform|].
  split; [exact iota4_distinct|].
  split; [exact iota4_intersecting|].
  split; [vm_compute; lia | exact iota4_no_sunflower].
Qed.

(** The truth boundary for [iota(4)], from below. A definition that had
    become accidentally vacuous would fail this half. *)

Corollary not_iota_four_at_most_26 : ~ IotaAtMost 4 26.
Proof.
  intro H.
  pose proof (iota_at_least_le_at_most 4 27 26 iota_four_at_least_27 H); lia.
Qed.

(** [g(4) >= 54] and hence [f(4,3) >= 55]. The development's previous best
    at uniformity 4 was [Audit.f_4_3_at_least_37]. *)

Theorem lower_bound_4_3_54 : LowerBound 4 3 54.
Proof.
  replace 54 with (2 * length iota4) by (vm_compute; reflexivity).
  apply (doubling_lower_bound 4 iota4);
    [ lia | exact iota4_uniform | exact iota4_distinct
    | exact iota4_intersecting | exact iota4_no_sunflower ].
Qed.

Corollary no_upper_bound_4_3_54 : ~ UpperBound 4 3 54.
Proof.
  intro Hub.
  destruct lower_bound_4_3_54 as [F [HU [HD [Hlen Hno]]]].
  apply Hno, Hub; [exact HU | exact HD | lia].
Qed.

Corollary f_4_3_at_least_55_beats_37 :
  LowerBound 4 3 54 /\ ~ UpperBound 4 3 54 /\ 37 < 55.
Proof.
  split; [exact lower_bound_4_3_54|].
  split; [exact no_upper_bound_4_3_54 | lia].
Qed.

(** And raised to a power, as every value here is. The rate
    [54^(1/4) = 2.7108] does *not* beat the development's headline
    [20^(1/3) = 2.7144] — recorded as such. What is new is the value at
    uniformity 4, not the rate; the sandwich
    ([IotaRate.every_construction_is_within_2b_of_iota]) is why no
    construction at a fixed uniformity can do better than [iota] there. *)

Theorem lower_bound_f_n_3_via_iota_four :
  forall t, LowerBound (t * 4) 3 (54 ^ t).
Proof. intros t; apply lower_bound_power; [lia | exact lower_bound_4_3_54]. Qed.

Corollary the_rate_at_four_does_not_beat_the_rate_at_three :
  forall t, 1 <= t -> 54 ^ (3 * t) < 20 ^ (4 * t).
Proof.
  intros t Ht.
  rewrite !Nat.pow_mul_r.
  apply Nat.pow_lt_mono_l; [lia|].
  (* [157464 < 160000]. [simpl] blows the stack on unary nat at this
     size; the boolean test does not. *)
  apply Nat.ltb_lt; vm_compute; reflexivity.
Qed.
