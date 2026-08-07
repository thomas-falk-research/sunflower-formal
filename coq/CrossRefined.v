(** * CrossRefined.v -- a sharper cross-intersecting bound, and the
      four-family route to [r*(4,3) <= 5] closed by a witness.

    §26.4 named one constant as the whole gap between the unconditional
    [r*(4,3) <= 7] and [r*(4,3) <= 5]: [TauThreePieceAtMost 4 5 125], a
    4-uniform intersecting Rao(5)-spread family of covering number at
    least 3 has at most 125 members. It then *derived a route* to that
    constant — decompose against one member [M], bound the layers
    [1 + 16 + 60 = 77], and ask the one-point layer for

<<
      Sigma_x |A_x| <= 48,   A_x four pairwise cross-intersecting
                             3-uniform Rao(5)-spread families,
>>

    calling this "the gap, stated exactly". This file does two things.

    ** 1. That route is dead, and the write-up gets corrected

    [Sigma <= 48] is false, and not marginally. Four copies of one
    25-member star (a point [w] over a 5-regular link graph) are pairwise
    cross-intersecting, 3-uniform and Rao(5)-spread, with [Sigma = 100].

    The τ ≥ 3 hypothesis on [G] — which the four-family phrasing throws
    away — does cut that example down, because four families all through
    [w] make [{x,w}] a two-point cover of [G]. But it does not restore
    [48]: [hm16] below is a 16-member intersecting Rao(5)-spread family
    that is *not* a star, so four copies of it give [Sigma = 64] with no
    common point at all. And the [G] it builds, [g65], is a genuine
    4-uniform intersecting Rao(5)-spread family with covering number at
    least 3 and 65 members. So

<<
      TauThreePieceAtMost 4 5 K  ->  65 <= K,
>>

    which both closes the route and pins the open constant into the
    interval [[65, 125]] — a proof of [r*(4,3) <= 5] by this decomposition
    must land in that window, and cannot come from any four-family
    inequality alone.

    ** 2. What the two examples are instances of: two transfer lemmas

    The mechanism in both is the same, and it is general.

    - [star_saturation]: if [A] is pointed at [w] and *large* — more than
      [u·r^(u-2)] members — then every family cross-intersecting [A] is
      pointed at [w] too. A member [f] of the partner avoiding [w] would
      force every [C] in [A] to contain [{w,v}] for one of [f]'s [u]
      points, and the pair degree caps that at [r^(u-2)] each.

    - [greedy_bound] at [j = 2], already in [CrossIntersecting]: if [A] is
      *not* pointed, its partner has at most [u²·r^(u-2)] members.

    Between them these split the cross-intersecting pair four ways and
    give a bound with no [r >= u + 2] threshold at all:

<<
      |A| + |B|  <=  u · max(2u, r+1) · r^(u-2).
>>

    Both bounds are a coefficient times [r^(u-2)]. Against
    [cross_pair_bound]'s [(r-1)·r^(u-1) = r(r-1)·r^(u-2)] the refined one
    is strictly smaller exactly when [u·max(2u,r+1) < r(r-1)] — at
    [(u,r) = (3,5)], which is the [m = 4] row, 18 against 20, so 90
    against 100; at [u = 2] it is [2r+2] against the exhaustive truth
    [2r+1], where [cross_pair_bound] gives [r(r-1)]. The two are
    incomparable in general: at [u = 4, r = 6] the coefficients are 32
    against 30, so 1152 against 1080. Both are kept.

    The [u = 2] extremal configuration — one edge against the two full
    stars at its endpoints — is exactly the fourth case below, and the
    reason the refined bound is tight there is that [star_saturation]
    forbids the *large* pointed side. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower Pigeonhole Spread SpreadReduction
     DirectSum Reflect SpreadThreshold TwoCover TauThree CrossIntersecting.
Import ListNotations.

Set Implicit Arguments.

(** ** Pointed families

    [Pointed A w] is "[A] is contained in the star at [w]". A nonempty
    family is pointed exactly when its covering number is 1. *)

Definition Pointed (A : Family) (w : nat) : Prop :=
  forall C, In C A -> In w C.

(** ** Star saturation

    > A large pointed family drags its cross-intersecting partners into
    > the same star. *)

Lemma star_saturation :
  forall u r (A B : Family) w,
    Uniform u B ->
    RaoSpread u A r ->
    Pointed A w ->
    (forall e f, In e A -> In f B -> exists x, In x e /\ In x f) ->
    u * r ^ (u - 2) < length A ->
    Pointed B w.
Proof.
  intros u r A B w HUB HRA Hpt Hcross Hbig f Hf.
  destruct (in_dec Nat.eq_dec w f) as [Hin|Hout]; [exact Hin | exfalso].
  (* every member of [A] contains [w] and meets [f], and [w] is not in
     [f], so it contains one of the [u] pairs [{w,v}], [v] in [f] *)
  assert (Hcov : length A <= length (map (fun v => [w; v]) f) * r ^ (u - 2)).
  { apply cover_by_sets.
    - intros C HC.
      destruct (Hcross C f HC Hf) as [v [HvC Hvf]].
      exists [w; v]; split.
      + apply in_map_iff; exists v; split; [reflexivity | exact Hvf].
      + intros y Hy; destruct Hy as [<-|[<-|[]]];
          [apply Hpt; exact HC | exact HvC].
    - intros T HT; apply in_map_iff in HT as [v [<- Hvf]].
      assert (Hne : w <> v) by (intro E; subst v; contradiction).
      specialize (HRA [w; v] (pair_nodup Hne) ltac:(discriminate)).
      simpl in HRA; exact HRA. }
  rewrite map_length in Hcov.
  destruct (@uniform_mem u B f HUB Hf) as [Hlf _].
  rewrite Hlf in Hcov; lia.
Qed.

(** ** Reading the covering-number search as pointedness *)

Lemma pointed_of_cover :
  forall (A : Family),
    A <> [] -> covers_at_most A 1 = true -> exists w, Pointed A w.
Proof.
  intros A Hne H; destruct (small_cover_of _ _ H) as [S [Hlen Hcov]].
  destruct S as [|w S0].
  - exfalso; destruct A as [|C A0]; [contradiction|].
    destruct (Hcov C (or_introl eq_refl)) as [x [[] _]].
  - assert (ES : S0 = [])
      by (destruct S0; [reflexivity | simpl in Hlen; lia]).
    subst S0.
    exists w; intros C HC; destruct (Hcov C HC) as [x [Hx HxC]].
    destruct Hx as [E|[]]; rewrite E; exact HxC.
Qed.

Lemma not_pointed_of_search :
  forall (A : Family) w,
    covers_at_most A 1 = false -> exists C, In C A /\ ~ In w C.
Proof.
  intros A w H.
  destruct (@no_small_cover A 1 H [w] ltac:(simpl; lia)) as [C [HC Hmiss]].
  exists C; split; [exact HC | apply Hmiss; left; reflexivity].
Qed.

(** ** An arithmetic shim

    Every case below produces [|A| <= c·P] and [|B| <= d·P] for the same
    [P = r^(u-2)], and closes by a scalar inequality on [c + d]. *)

Lemma sum_scale :
  forall a b c d K P,
    a <= c * P -> b <= d * P -> c + d <= K -> a + b <= K * P.
Proof.
  intros a b c d K P Ha Hb Hk.
  apply Nat.le_trans with ((c + d) * P).
  - rewrite Nat.mul_add_distr_r; lia.
  - apply Nat.mul_le_mono_r; exact Hk.
Qed.

(** ** The refined cross-intersecting bound *)

(** The two ingredients, packaged at the two values of [j] that are used. *)

Lemma pow_pred_split :
  forall u r, 2 <= u -> r ^ (u - 1) = r * r ^ (u - 2).
Proof.
  intros u r Hu; replace (u - 1) with (S (u - 2)) by lia; reflexivity.
Qed.

Lemma partner_bound_one :
  forall u r (A B : Family),
    2 <= u -> A <> [] ->
    Uniform u A -> RaoSpread u B r ->
    (forall e f, In e A -> In f B -> exists w, In w e /\ In w f) ->
    length B <= u * r * r ^ (u - 2).
Proof.
  intros u r A B Hu Hne HUA HRB Hcross.
  assert (H : length B <= u ^ 1 * r ^ (u - 1)).
  { apply (@greedy_bound 1 A B u r ltac:(lia) HUA HRB Hcross).
    intros S HS.
    assert (ES : S = []) by (destruct S; [reflexivity | simpl in HS; lia]).
    subst S.
    destruct A as [|C A0]; [contradiction|].
    exists C; split; [left; reflexivity | intros y []]. }
  rewrite Nat.pow_1_r, (pow_pred_split r Hu), Nat.mul_assoc in H; exact H.
Qed.

(** > **The refined bound.** Two nonempty cross-intersecting families at
    > uniformity [u >= 2], each Rao(r)-spread, have at most
    > [u·max(2u, r+1)·r^(u-2)] members between them — with no lower bound
    > on [r] at all. *)

Theorem cross_pair_refined :
  forall u r (A B : Family),
    2 <= u ->
    Uniform u A -> Uniform u B ->
    RaoSpread u A r -> RaoSpread u B r ->
    (forall e f, In e A -> In f B -> exists w, In w e /\ In w f) ->
    A <> [] -> B <> [] ->
    length A + length B <= u * Nat.max (2 * u) (r + 1) * r ^ (u - 2).
Proof.
  intros u r A B Hu HUA HUB HRA HRB Hcross HAne HBne.
  assert (Hflip : forall e f, In e B -> In f A -> exists w, In w e /\ In w f).
  { intros e f He Hf; destruct (Hcross f e Hf He) as [w [H1 H2]];
      exists w; split; assumption. }
  assert (Epow : r ^ (u - 1) = r * r ^ (u - 2)) by (apply (@pow_pred_split u r Hu)).
  assert (Hml : 2 * u <= Nat.max (2 * u) (r + 1)) by apply Nat.le_max_l.
  assert (Hmr : r + 1 <= Nat.max (2 * u) (r + 1)) by apply Nat.le_max_r.
  (* the greedy bound at [j = 1], available on both sides *)
  assert (HgA : length A <= u * r * r ^ (u - 2))
    by (apply (@partner_bound_one u r B A Hu HBne HUB HRA Hflip)).
  assert (HgB : length B <= u * r * r ^ (u - 2))
    by (apply (@partner_bound_one u r A B Hu HAne HUA HRB Hcross)).
  (* the greedy bound at [j = 2], available when the other side is not
     pointed *)
  assert (Hsq : u ^ 2 = u * u)
    by (simpl; rewrite Nat.mul_1_r; reflexivity).
  assert (HnA : covers_at_most A 1 = false -> length B <= u * u * r ^ (u - 2)).
  { intros E.
    assert (H : length B <= u ^ 2 * r ^ (u - 2)).
    { apply (@greedy_bound 2 A B u r ltac:(lia) HUA HRB Hcross).
      intros S HS; apply (@no_small_cover A 1 E); lia. }
    rewrite Hsq in H; exact H. }
  assert (HnB : covers_at_most B 1 = false -> length A <= u * u * r ^ (u - 2)).
  { intros E.
    assert (H : length A <= u ^ 2 * r ^ (u - 2)).
    { apply (@greedy_bound 2 B A u r ltac:(lia) HUB HRA Hflip).
      intros S HS; apply (@no_small_cover B 1 E); lia. }
    rewrite Hsq in H; exact H. }
  (* the star bound, available when a side is pointed *)
  assert (Hstar : forall (F : Family) w, Pointed F w -> RaoSpread u F r ->
                    length F <= r * r ^ (u - 2)).
  { intros F w Hpt HRF.
    assert (H : length F <= 1 * r ^ (u - 1)).
    { apply (@cover_size_bound F u r 1 [w] HRF).
      - intros C HC; exists w; split; [left; reflexivity | apply Hpt; exact HC].
      - simpl; lia. }
    rewrite Epow in H; lia. }
  destruct (covers_at_most A 1) eqn:EA; destruct (covers_at_most B 1) eqn:EB.
  - (* both pointed: both are stars, and [2r <= u(r+1)] *)
    destruct (@pointed_of_cover A HAne EA) as [wA HA].
    destruct (@pointed_of_cover B HBne EB) as [wB HB].
    apply (@sum_scale (length A) (length B) r r
             (u * Nat.max (2 * u) (r + 1)) (r ^ (u - 2)));
      [exact (Hstar A wA HA HRA) | exact (Hstar B wB HB HRB) | nia].
  - (* [A] pointed, [B] not: star saturation forbids a large [A] *)
    destruct (@pointed_of_cover A HAne EA) as [wA HA].
    assert (HAsmall : length A <= u * r ^ (u - 2)).
    { destruct (le_lt_dec (length A) (u * r ^ (u - 2))) as [H|H];
        [exact H | exfalso].
      assert (HBpt : Pointed B wA)
        by (apply (@star_saturation u r A B wA HUB HRA HA Hcross); exact H).
      destruct (@not_pointed_of_search B wA EB) as [C [HC Hmiss]].
      apply Hmiss, HBpt, HC. }
    apply (@sum_scale (length A) (length B) u (u * r)
             (u * Nat.max (2 * u) (r + 1)) (r ^ (u - 2)));
      [exact HAsmall | exact HgB | nia].
  - (* mirror image *)
    destruct (@pointed_of_cover B HBne EB) as [wB HB].
    assert (HBsmall : length B <= u * r ^ (u - 2)).
    { destruct (le_lt_dec (length B) (u * r ^ (u - 2))) as [H|H];
        [exact H | exfalso].
      assert (HApt : Pointed A wB)
        by (apply (@star_saturation u r B A wB HUA HRB HB Hflip); exact H).
      destruct (@not_pointed_of_search A wB EA) as [C [HC Hmiss]].
      apply Hmiss, HApt, HC. }
    apply (@sum_scale (length A) (length B) (u * r) u
             (u * Nat.max (2 * u) (r + 1)) (r ^ (u - 2)));
      [exact HgA | exact HBsmall | nia].
  - (* neither pointed: the greedy tree at depth two, twice *)
    apply (@sum_scale (length A) (length B) (u * u) (u * u)
             (u * Nat.max (2 * u) (r + 1)) (r ^ (u - 2)));
      [exact (HnB eq_refl) | exact (HnA eq_refl) | nia].
Qed.

(** > **Where it is strictly sharper than [cross_pair_bound].** *)

Corollary cross_pair_refined_strict :
  forall u r (A B : Family),
    2 <= u -> 1 <= r ->
    u * Nat.max (2 * u) (r + 1) < (r - 1) * r ->
    Uniform u A -> Uniform u B ->
    RaoSpread u A r -> RaoSpread u B r ->
    (forall e f, In e A -> In f B -> exists w, In w e /\ In w f) ->
    A <> [] -> B <> [] ->
    length A + length B < (r - 1) * r ^ (u - 1).
Proof.
  intros u r A B Hu Hr Hlt HUA HUB HRA HRB Hcross HAne HBne.
  pose proof (@cross_pair_refined u r A B Hu HUA HUB HRA HRB Hcross HAne HBne) as H.
  assert (Epow : r ^ (u - 1) = r * r ^ (u - 2))
    by (replace (u - 1) with (S (u - 2)) by lia; reflexivity).
  assert (Hp : 1 <= r ^ (u - 2)) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  rewrite Epow, Nat.mul_assoc.
  apply Nat.le_lt_trans with (u * Nat.max (2 * u) (r + 1) * r ^ (u - 2));
    [exact H |].
  apply Nat.mul_lt_mono_pos_r; [lia | exact Hlt].
Qed.

(** The row that matters: at [u = 3] — which is [m = 4] — and [r = 5],
    18 against 20, so 90 against 100. *)

Corollary cross_pair_refined_at_three_five :
  forall (A B : Family),
    Uniform 3 A -> Uniform 3 B ->
    RaoSpread 3 A 5 -> RaoSpread 3 B 5 ->
    (forall e f, In e A -> In f B -> exists w, In w e /\ In w f) ->
    A <> [] -> B <> [] ->
    length A + length B <= 90.
Proof.
  intros A B HUA HUB HRA HRB Hcross HAne HBne.
  pose proof (@cross_pair_refined 3 5 A B ltac:(lia) HUA HUB HRA HRB
                Hcross HAne HBne) as H.
  vm_compute in H; exact H.
Qed.

(** ** A one-point analogue of [TwoCover.covers_dec_search]

    Deciding "some single point covers [G]" is the same finite search one
    level down: a point in no member covers nothing. *)

Lemma unpointed_dec_search :
  forall (G : Family) w,
    existsb (fun a => forallb (fun C => memb a C) G) (concat G) = false ->
    G <> [] ->
    exists C, In C G /\ ~ In w C.
Proof.
  intros G w Hsearch HGne.
  destruct (in_dec Nat.eq_dec w (concat G)) as [Hw|Hw].
  - pose proof (existsb_false_forall _ _ _ Hsearch w Hw) as E.
    destruct (existsb (fun C => negb (memb w C)) G) eqn:Ex.
    + apply existsb_exists in Ex as [C [HC Hneg]].
      apply Bool.negb_true_iff in Hneg.
      exists C; split;
        [exact HC | intros Hin; apply memb_true_iff in Hin; congruence].
    + exfalso.
      assert (Hall : forallb (fun C => memb w C) G = true).
      { apply forallb_forall; intros C HC.
        pose proof (existsb_false_forall _ _ _ Ex C HC) as E2.
        apply Bool.negb_false_iff in E2; exact E2. }
      congruence.
  - destruct G as [|M G0]; [contradiction|].
    exists M; split; [left; reflexivity|].
    intros Hin; apply Hw, (proj2 (in_concat (M :: G0) w));
      exists M; split; [left; reflexivity | exact Hin].
Qed.

(** ** The two objects

    [hm16] is a Hilton–Milner shape: the triple [B = {4,5,6}] together
    with the 15 triples [{12, i, y}], [i] in [B] and [y] in
    [Y = {7,...,11}]. Every star member meets [B], so it is intersecting;
    [deg{12,i} = 5], [deg{12,y} = 3] and [deg{12} = 15], so it is
    Rao(5)-spread; and [B] misses 12 while [{12,4,7}] misses 5, so it is
    pointed at nothing.

    [g65] hangs one copy of [hm16] on each point of [M = {0,1,2,3}] and
    adds [M]. Distinct points of [M] force the tails to meet, which they
    do because [hm16] is intersecting; and [B] not containing 12 is
    exactly what stops [{x,12}] from being a two-point cover. *)

Definition hm16 : Family :=
  [4;5;6] :: flat_map (fun i => map (fun y => [12; i; y]) [7;8;9;10;11]) [4;5;6].

Definition g65 : Family :=
  [0;1;2;3] :: flat_map (fun x => map (fun T => x :: T) hm16) [0;1;2;3].

Definition ground13 : list nat := [0;1;2;3;4;5;6;7;8;9;10;11;12].

Lemma hm16_length : length hm16 = 16.
Proof. vm_compute; reflexivity. Qed.

Lemma g65_length : length g65 = 65.
Proof. vm_compute; reflexivity. Qed.

Lemma hm16_uniform : Uniform 3 hm16.
Proof. apply uniformb_correct; vm_compute; reflexivity. Qed.

Lemma hm16_distinct : Distinct hm16.
Proof. apply distinctb_correct; vm_compute; reflexivity. Qed.

Lemma hm16_rao : RaoSpread 3 hm16 5.
Proof.
  apply (@rao_spreadb_correct 3 hm16 5 ground13).
  - apply nodupb_correct; vm_compute; reflexivity.
  - apply Forall_forall; intros A HA.
    destruct (@uniform_mem 3 hm16 A hm16_uniform HA) as [_ Hnd]; exact Hnd.
  - apply groundedb_correct; vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

Lemma hm16_int :
  forall C D, In C hm16 -> In D hm16 -> exists x, In x C /\ In x D.
Proof. apply int_b_correct; vm_compute; reflexivity. Qed.

Lemma hm16_unpointed : forall w, exists C, In C hm16 /\ ~ In w C.
Proof.
  intros w; apply (@unpointed_dec_search hm16 w);
    [vm_compute; reflexivity | discriminate].
Qed.

Lemma g65_uniform : Uniform 4 g65.
Proof. apply uniformb_correct; vm_compute; reflexivity. Qed.

Lemma g65_distinct : Distinct g65.
Proof. apply distinctb_correct; vm_compute; reflexivity. Qed.

Lemma g65_rao : RaoSpread 4 g65 5.
Proof.
  apply (@rao_spreadb_correct 4 g65 5 ground13).
  - apply nodupb_correct; vm_compute; reflexivity.
  - apply Forall_forall; intros A HA.
    destruct (@uniform_mem 4 g65 A g65_uniform HA) as [_ Hnd]; exact Hnd.
  - apply groundedb_correct; vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

Lemma g65_int :
  forall C D, In C g65 -> In D g65 -> exists x, In x C /\ In x D.
Proof. apply int_b_correct; vm_compute; reflexivity. Qed.

Lemma g65_tau : forall p q, exists C, In C g65 /\ ~ In p C /\ ~ In q C.
Proof.
  intros p q; apply (@covers_dec_search g65 p q);
    [vm_compute; reflexivity | discriminate].
Qed.

(** ** The constant is at least 65

    > Any [K] for which "a 4-uniform intersecting Rao(5)-spread family of
    > covering number at least 3 has at most [K] members" holds satisfies
    > [65 <= K]. *)

Theorem tau_three_piece_at_least_sixty_five :
  forall K, TauThreePieceAtMost 4 5 K -> 65 <= K.
Proof.
  intros K H.
  pose proof (H g65 g65_uniform g65_rao g65_distinct g65_int g65_tau) as Hb.
  rewrite g65_length in Hb; exact Hb.
Qed.

(** And so the interval for the open constant is [[65, 125]]: [125] would
    give [r*(4,3) <= 5] by [r_star_four_at_most_five_from_tau_three], and
    nothing below 65 is provable. *)

(** ** The four-family route, closed

    > Four pairwise cross-intersecting 3-uniform Rao(5)-spread families,
    > none of them pointed, with 64 members between them. *)

Theorem four_unpointed_cross_families_exceed_forty_eight :
  exists A0 A1 A2 A3 : Family,
    (forall X, In X [A0;A1;A2;A3] ->
       Uniform 3 X /\ Distinct X /\ RaoSpread 3 X 5 /\
       (forall w, exists C, In C X /\ ~ In w C)) /\
    (forall X Y, In X [A0;A1;A2;A3] -> In Y [A0;A1;A2;A3] ->
       forall C D, In C X -> In D Y -> exists x, In x C /\ In x D) /\
    48 < length A0 + length A1 + length A2 + length A3.
Proof.
  assert (Hall : forall X, In X [hm16; hm16; hm16; hm16] -> X = hm16)
    by (intros X HX; destruct HX as [<-|[<-|[<-|[<-|[]]]]]; reflexivity).
  exists hm16, hm16, hm16, hm16.
  refine (conj _ (conj _ _)).
  - intros X HX; rewrite (Hall X HX).
    exact (conj hm16_uniform
             (conj hm16_distinct (conj hm16_rao hm16_unpointed))).
  - intros X Y HX HY C D HC HD.
    rewrite (Hall X HX) in HC; rewrite (Hall Y HY) in HD.
    exact (hm16_int HC HD).
  - rewrite hm16_length; lia.
Qed.

(** ** Print Assumptions

    Everything above is closed under the global context; the file adds no
    axiom and no admitted statement. *)
