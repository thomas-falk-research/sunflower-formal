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

    calling this "the gap, stated exactly". This file does three things.

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
    forbids the *large* pointed side.

    ** 3. What the sharper bound buys: [I2(3,5) = 16], exactly

    [CrossIntersecting.two_cover_split] now factors the two-point-cover
    argument out of [two_cover_star_extremal], so a second consumer can
    feed it a different pair bound.

    At [u = 2] the pair bound can be made exact, at every [r >= 2].
    Three ingredients:

    - [pair_partner_bound]: two members of one side that differ as sets
      cap the other at [max(r+1, 4)] -- a star at their shared point plus
      the one edge joining the other two, or the four crossing pairs if
      they are disjoint;
    - [triangle_bound]: a graph that pairwise intersects and is pointed at
      nothing *is* a triangle, so it has three edges, not the four the
      greedy tree allows -- and so does anything cross-intersecting it,
      because meeting all three edges of a triangle means being one of
      them;
    - [disjoint_squeeze]: a graph with two disjoint edges forces its
      partner into the four crossing pairs, and if all four occur then
      only two edges can meet every one of them.

    The last two combine into [unpointed_pair_bound]: if *neither* side is
    a star the two have at most six edges between them, with no reference
    to [r] at all -- the keys are pairs, and a pair has degree at most
    [r^0 = 1] whatever [r] is.

    With [star_saturation] and [partner_bound_one] that gives
    [cross_pair_two_exact]: for [r >= 2],

<<
      |A| + |B|  <=  max(2r+1, 6),
>>

    which is the exhaustive truth at every [r >= 2]. Both branches are
    attained and neither is slack: [2r+1] by one edge against the two full
    stars at its endpoints, from [r = 3] on; 6 by two disjoint edges
    against the four crossing edges, which is what [r = 2] gives, and
    [cross_pair_two_six_is_attained] exhibits it.

    Feeding *that* to the split gives [nonstar_three_bound]: for
    [r >= 3], a 3-uniform intersecting Rao(r)-spread family that is not a
    star has at most [max(3r+1, 16)] members. At [r = 5] both branches
    read 16, and [hm16] attains it, so [I2(3,5) = 16] exactly.

    Neither of the earlier pair bounds reaches this. [cross_pair_bound]
    gives 20 at [u = 2, r = 5], so the branch would come out at
    [20 + 5 = 25] -- the star bound [r^(m-1)], no information about
    non-stars at all. [cross_pair_refined] gives 12, hence 17, one too
    many. Only the exact bound closes it. *)

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

(** ** The pair bound at uniformity two, exactly

    [cross_pair_refined] gives [2r+2] at [u = 2] and the exhaustive search
    in [rust/tests/cross_intersecting.rs] says the truth is [2r+1]. That
    one closes, and closing it closes [I2(3,5)] below.

    The new ingredient is [pair_partner_bound]: *two* members of one side,
    not equal as sets, pin the other side at [r+3]. Everything else is
    [star_saturation], [partner_bound_one] and [greedy_bound] at [j = 2],
    already here. *)

Lemma two_sets_subset_eq :
  forall e1 e2,
    length e1 = 2 -> NoDup e1 -> length e2 = 2 ->
    Subset e1 e2 -> SetEq e1 e2.
Proof.
  intros e1 e2 Hl1 Hnd1 Hl2 Hsub.
  destruct e1 as [|p1 [|p2 [|? ?]]]; simpl in Hl1; try discriminate.
  destruct e2 as [|q1 [|q2 [|? ?]]]; simpl in Hl2; try discriminate.
  assert (Hp : p1 <> p2)
    by (inversion Hnd1 as [|? ? Hni ?]; subst; intro E; apply Hni;
        left; symmetry; exact E).
  assert (H1 : In p1 [q1; q2]) by (apply Hsub; left; reflexivity).
  assert (H2 : In p2 [q1; q2]) by (apply Hsub; right; left; reflexivity).
  split; [exact Hsub|].
  destruct H1 as [E1|[E1|[]]]; destruct H2 as [E2|[E2|[]]]; subst;
    try (exfalso; apply Hp; reflexivity);
    intros x [<-|[<-|[]]]; simpl; tauto.
Qed.

Lemma member_outside :
  forall e1 e2,
    length e1 = 2 -> NoDup e1 -> length e2 = 2 ->
    ~ SetEq e1 e2 -> exists b, In b e1 /\ ~ In b e2.
Proof.
  intros e1 e2 Hl1 Hnd1 Hl2 Hne.
  destruct e1 as [|p1 [|p2 [|? ?]]]; simpl in Hl1; try discriminate.
  destruct (in_dec Nat.eq_dec p1 e2) as [H1|H1];
    [| exists p1; split; [left; reflexivity | exact H1]].
  destruct (in_dec Nat.eq_dec p2 e2) as [H2|H2];
    [| exists p2; split; [right; left; reflexivity | exact H2]].
  exfalso; apply Hne.
  apply (@two_sets_subset_eq [p1; p2] e2 ltac:(reflexivity) Hnd1 Hl2).
  intros x [<-|[<-|[]]]; assumption.
Qed.

(** > **Lemma P.** Two members of [A] that differ as sets cap [B] at
    > [max(r+1, 4)]: a star at their shared point plus the one edge
    > joining the other two, or the four crossing pairs if they are
    > disjoint. At [r >= 3] the first dominates; at [r = 2] the second
    > does. *)

Lemma pair_partner_bound :
  forall r (A B : Family) e1 e2,
    Uniform 2 A -> RaoSpread 2 B r ->
    In e1 A -> In e2 A -> ~ SetEq e1 e2 ->
    (forall e f, In e A -> In f B -> exists w, In w e /\ In w f) ->
    length B <= Nat.max (r + 1) 4.
Proof.
  intros r A B e1 e2 HUA HRB H1 H2 Hne Hcross.
  destruct (@uniform_mem 2 A e1 HUA H1) as [Hl1 Hnd1].
  destruct (@uniform_mem 2 A e2 HUA H2) as [Hl2 Hnd2].
  (* b in e1 outside e2, and d in e2 outside e1 *)
  destruct (member_outside Hl1 Hnd1 Hl2 Hne) as [b [Hbe1 Hbe2]].
  destruct (member_outside Hl2 Hnd2 Hl1 ltac:(intro E; apply Hne, SetEq_sym; exact E))
    as [d [Hde2 Hde1]].
  (* name the other element of each *)
  assert (Hx : exists x, In x e1 /\ forall f, In f B -> In b f \/ In x f).
  { destruct e1 as [|p1 [|p2 [|? ?]]]; simpl in Hl1; try discriminate.
    destruct Hbe1 as [Eb|[Eb|[]]]; subst.
    - exists p2; split; [right; left; reflexivity|].
      intros f Hf; destruct (Hcross _ f H1 Hf) as [w [[<-|[<-|[]]] Hwf]]; tauto.
    - exists p1; split; [left; reflexivity|].
      intros f Hf; destruct (Hcross _ f H1 Hf) as [w [[<-|[<-|[]]] Hwf]]; tauto. }
  assert (Hy : exists y, In y e2 /\ forall f, In f B -> In d f \/ In y f).
  { destruct e2 as [|q1 [|q2 [|? ?]]]; simpl in Hl2; try discriminate.
    destruct Hde2 as [Ed|[Ed|[]]]; subst.
    - exists q2; split; [right; left; reflexivity|].
      intros f Hf; destruct (Hcross _ f H2 Hf) as [w [[<-|[<-|[]]] Hwf]]; tauto.
    - exists q1; split; [left; reflexivity|].
      intros f Hf; destruct (Hcross _ f H2 Hf) as [w [[<-|[<-|[]]] Hwf]]; tauto. }
  destruct Hx as [x [Hxe1 Hbx]].
  destruct Hy as [y [Hye2 Hdy]].
  assert (Hbd : b <> d) by (intro E; subst; contradiction).
  assert (Hby : b <> y) by (intro E; subst; contradiction).
  assert (Hxd : x <> d) by (intro E; subst; contradiction).
  assert (Hd1 : deg [b;d] B <= 1)
    by (specialize (HRB [b;d] (pair_nodup Hbd) ltac:(discriminate)); simpl in HRB;
        exact HRB).
  assert (Hd2 : deg [b;y] B <= 1)
    by (specialize (HRB [b;y] (pair_nodup Hby) ltac:(discriminate)); simpl in HRB;
        exact HRB).
  assert (Hd3 : deg [x;d] B <= 1)
    by (specialize (HRB [x;d] (pair_nodup Hxd) ltac:(discriminate)); simpl in HRB;
        exact HRB).
  (* the two members either share a vertex or they do not, and the sharp
     bound differs: [r+1] from a star plus one edge, [4] from the four
     crossing pairs. Both are at most [r+1] once [r >= 3]. *)
  destruct (Nat.eq_dec x y) as [Exy|Exy].
  - (* they share [x]: the partner is a star at [x] plus the edge [b d] *)
    subst y.
    pose proof (@cover_by_sets_sum [[x];[b;d]] B) as Hb.
    simpl in Hb.
    assert (Hcov : forall C, In C B -> exists T, In T [[x];[b;d]] /\ Subset T C).
    { intros C HC.
      destruct (in_dec Nat.eq_dec x C) as [Hx'|Hx'].
      - exists [x]; split; [left; reflexivity | intros z [<-|[]]; assumption].
      - exists [b;d]; split; [right; left; reflexivity|].
        destruct (Hbx C HC) as [Hb'|Hc']; [| contradiction].
        destruct (Hdy C HC) as [Hd'|Hc']; [| contradiction].
        intros z [<-|[<-|[]]]; assumption. }
    specialize (Hb Hcov).
    assert (Hd4 : deg [x] B <= r)
      by (pose proof (@rao_point 2 r B x HRB) as H; simpl in H; lia).
    lia.
  - (* they do not: four crossing pairs, each of degree at most one *)
    pose proof (@cover_by_sets_sum [[b;d];[b;y];[x;d];[x;y]] B) as Hb.
    simpl in Hb.
    assert (Hcov : forall C, In C B ->
                     exists T, In T [[b;d];[b;y];[x;d];[x;y]] /\ Subset T C).
    { intros C HC.
      destruct (Hbx C HC) as [Hb'|Hx']; destruct (Hdy C HC) as [Hd'|Hy'].
      - exists [b;d]; split; [left; reflexivity | intros z [<-|[<-|[]]]; assumption].
      - exists [b;y]; split;
          [right; left; reflexivity | intros z [<-|[<-|[]]]; assumption].
      - exists [x;d]; split;
          [right; right; left; reflexivity | intros z [<-|[<-|[]]]; assumption].
      - exists [x;y]; split;
          [right; right; right; left; reflexivity
           | intros z [<-|[<-|[]]]; assumption]. }
    specialize (Hb Hcov).
    assert (Hd4 : deg [x;y] B <= 1)
      by (specialize (HRB [x;y] (pair_nodup Exy) ltac:(discriminate)); simpl in HRB;
          exact HRB).
    lia.
Qed.

(** ** Two facts about graphs that the [r = 3] row needs

    At [r = 3] the target is 7, and the crude "neither side pointed gives
    four each" is 8. Two structural facts close it, and neither mentions
    [r]: a graph that pairwise intersects and is pointed at nothing *is* a
    triangle, and a graph with two disjoint edges squeezes its partner. *)

Lemma two_elem_only :
  forall (e : list nat) (a d z : nat),
    length e = 2 -> NoDup e -> In a e -> In d e -> a <> d -> In z e ->
    z = a \/ z = d.
Proof.
  intros e a d z Hl Hnd Ha Hd Had Hz.
  destruct e as [|p [|q [|? ?]]]; simpl in Hl; try discriminate.
  assert (Hpq : p <> q)
    by (inversion Hnd as [|? ? Hni ?]; subst; intro E; apply Hni;
        left; symmetry; exact E).
  destruct Ha as [Ea|[Ea|[]]]; destruct Hd as [Ed|[Ed|[]]]; subst;
    try (exfalso; apply Had; reflexivity);
    destruct Hz as [Ez|[Ez|[]]]; subst; tauto.
Qed.

(** Covering a graph by two or three pairs, each of degree at most one. *)

Lemma pair_key_deg :
  forall r (B : Family) k,
    RaoSpread 2 B r -> NoDup k -> length k = 2 -> deg k B <= 1.
Proof.
  intros r B k HR Hnd Hl.
  specialize (HR k Hnd ltac:(destruct k; [simpl in Hl; discriminate | discriminate])).
  rewrite Hl in HR; simpl in HR; exact HR.
Qed.

Lemma two_keys_bound :
  forall r (B : Family) k1 k2,
    RaoSpread 2 B r ->
    NoDup k1 -> length k1 = 2 -> NoDup k2 -> length k2 = 2 ->
    (forall C, In C B -> Subset k1 C \/ Subset k2 C) ->
    length B <= 2.
Proof.
  intros r B k1 k2 HR N1 L1 N2 L2 Hcov.
  pose proof (@cover_by_sets_sum [k1;k2] B) as Hb; simpl in Hb.
  assert (H : forall C, In C B -> exists T, In T [k1;k2] /\ Subset T C).
  { intros C HC; destruct (Hcov C HC) as [H|H];
      [exists k1; split; [left; reflexivity | exact H]
       | exists k2; split; [right; left; reflexivity | exact H]]. }
  specialize (Hb H).
  pose proof (@pair_key_deg r B k1 HR N1 L1).
  pose proof (@pair_key_deg r B k2 HR N2 L2).
  lia.
Qed.

Lemma three_keys_bound :
  forall r (B : Family) k1 k2 k3,
    RaoSpread 2 B r ->
    NoDup k1 -> length k1 = 2 -> NoDup k2 -> length k2 = 2 ->
    NoDup k3 -> length k3 = 2 ->
    (forall C, In C B -> Subset k1 C \/ Subset k2 C \/ Subset k3 C) ->
    length B <= 3.
Proof.
  intros r B k1 k2 k3 HR N1 L1 N2 L2 N3 L3 Hcov.
  pose proof (@cover_by_sets_sum [k1;k2;k3] B) as Hb; simpl in Hb.
  assert (H : forall C, In C B -> exists T, In T [k1;k2;k3] /\ Subset T C).
  { intros C HC; destruct (Hcov C HC) as [H|[H|H]];
      [exists k1; split; [left; reflexivity | exact H]
       | exists k2; split; [right; left; reflexivity | exact H]
       | exists k3; split; [right; right; left; reflexivity | exact H]]. }
  specialize (Hb H).
  pose proof (@pair_key_deg r B k1 HR N1 L1).
  pose proof (@pair_key_deg r B k2 HR N2 L2).
  pose proof (@pair_key_deg r B k3 HR N3 L3).
  lia.
Qed.

(** > **The triangle lemma.** A graph that pairwise intersects and is
    > pointed at nothing has at most three edges — it *is* a triangle —
    > and so does every graph cross-intersecting it, because anything
    > meeting all three edges of a triangle is one of them. *)

Lemma triangle_bound :
  forall r (A B : Family),
    Uniform 2 A -> Uniform 2 B -> RaoSpread 2 A r -> RaoSpread 2 B r ->
    (forall e f, In e A -> In f A -> exists w, In w e /\ In w f) ->
    (forall w, exists e, In e A /\ ~ In w e) ->
    (forall e f, In e A -> In f B -> exists w, In w e /\ In w f) ->
    length A <= 3 /\ length B <= 3.
Proof.
  intros r A B HUA HUB HRA HRB Hint Hns Hcross.
  destruct (Hns 0) as [e0 [He0 _]].
  destruct (@uniform_mem 2 A e0 HUA He0) as [Hl0 Hnd0].
  destruct e0 as [|x [|y [|? ?]]]; simpl in Hl0; try discriminate.
  rename He0 into H1.
  assert (Hxy : x <> y)
    by (inversion Hnd0 as [|? ? Hni ?]; subst; intro E; apply Hni;
        left; symmetry; exact E).
  destruct (Hns x) as [e2 [H2 Hx2]].
  destruct (Hns y) as [e3 [H3 Hy3]].
  destruct (@uniform_mem 2 A e2 HUA H2) as [Hl2 Hnd2].
  destruct (@uniform_mem 2 A e3 HUA H3) as [Hl3 Hnd3].
  assert (Hy2 : In y e2).
  { destruct (Hint _ e2 H1 H2) as [w [[<-|[<-|[]]] Hw2]];
      [contradiction | exact Hw2]. }
  assert (Hx3 : In x e3).
  { destruct (Hint _ e3 H1 H3) as [w [[<-|[<-|[]]] Hw3]];
      [exact Hw3 | contradiction]. }
  destruct (Hint e2 e3 H2 H3) as [z [Hz2 Hz3]].
  assert (Hzx : z <> x) by (intro E; subst z; contradiction).
  assert (Hzy : z <> y) by (intro E; subst z; contradiction).
  assert (Hxz : x <> z) by congruence.
  assert (Hyz : y <> z) by congruence.
  (* the covering only uses "meets [x;y], meets e2, meets e3" *)
  assert (Hkeys : forall C,
            (exists w, In w [x;y] /\ In w C) ->
            (exists w, In w e2 /\ In w C) ->
            (exists w, In w e3 /\ In w C) ->
            Subset [x;y] C \/ Subset [x;z] C \/ Subset [y;z] C).
  { intros C [w [[<-|[<-|[]]] HwC]] [v [Hv2 HvC]] [t [Ht3 HtC]].
    - destruct (@two_elem_only e2 y z v Hl2 Hnd2 Hy2 Hz2
                  ltac:(congruence) Hv2) as [<-|<-].
      + left; intros q [<-|[<-|[]]]; assumption.
      + right; left; intros q [<-|[<-|[]]]; assumption.
    - destruct (@two_elem_only e3 x z t Hl3 Hnd3 Hx3 Hz3
                  ltac:(congruence) Ht3) as [<-|<-].
      + left; intros q [<-|[<-|[]]]; assumption.
      + right; right; intros q [<-|[<-|[]]]; assumption. }
  split.
  - apply (@three_keys_bound r A [x;y] [x;z] [y;z] HRA
             (pair_nodup Hxy) eq_refl
             (pair_nodup Hxz) eq_refl
             (pair_nodup Hyz) eq_refl).
    intros C HC; apply Hkeys;
      [exact (Hint _ C H1 HC) | exact (Hint e2 C H2 HC) | exact (Hint e3 C H3 HC)].
  - apply (@three_keys_bound r B [x;y] [x;z] [y;z] HRB
             (pair_nodup Hxy) eq_refl
             (pair_nodup Hxz) eq_refl
             (pair_nodup Hyz) eq_refl).
    intros C HC; apply Hkeys;
      [exact (Hcross _ C H1 HC) | exact (Hcross e2 C H2 HC)
       | exact (Hcross e3 C H3 HC)].
Qed.

(** > **The disjoint-pair squeeze.** If [A] has two disjoint members then
    > either [B] misses one of the four crossing pairs — so three keys
    > cover it — or it has all four, and then only two edges can meet
    > every one of them, so [A] itself is down to two. *)

Lemma disjoint_squeeze :
  forall r (A B : Family) e1 e2,
    Uniform 2 A -> Uniform 2 B -> RaoSpread 2 A r -> RaoSpread 2 B r ->
    In e1 A -> In e2 A -> Disjoint e1 e2 ->
    (forall e f, In e A -> In f B -> exists w, In w e /\ In w f) ->
    length A <= 2 \/ length B <= 3.
Proof.
  intros r A B e1 e2 HUA HUB HRA HRB H1 H2 Hdis Hcross.
  destruct (@uniform_mem 2 A e1 HUA H1) as [Hl1 Hnd1].
  destruct (@uniform_mem 2 A e2 HUA H2) as [Hl2 Hnd2].
  destruct e1 as [|a [|b [|? ?]]]; simpl in Hl1; try discriminate.
  destruct e2 as [|c [|d [|? ?]]]; simpl in Hl2; try discriminate.
  assert (Hab : a <> b)
    by (inversion Hnd1 as [|? ? Hni ?]; subst; intro E; apply Hni;
        left; symmetry; exact E).
  assert (Hcd : c <> d)
    by (inversion Hnd2 as [|? ? Hni ?]; subst; intro E; apply Hni;
        left; symmetry; exact E).
  assert (Hcross4 : forall p q, In p [a;b] -> In q [c;d] -> p <> q)
    by (intros p q Hp Hq E; subst q; apply (Hdis p); assumption).
  assert (Hac : a <> c) by (apply Hcross4; simpl; tauto).
  assert (Had : a <> d) by (apply Hcross4; simpl; tauto).
  assert (Hbc : b <> c) by (apply Hcross4; simpl; tauto).
  assert (Hbd : b <> d) by (apply Hcross4; simpl; tauto).
  (* every member of B has one point in each of the two disjoint members *)
  assert (Hsplit : forall f, In f B -> (In a f \/ In b f) /\ (In c f \/ In d f)).
  { intros f Hf; split;
      [ destruct (Hcross _ f H1 Hf) as [w [[<-|[<-|[]]] Hwf]]; tauto
      | destruct (Hcross _ f H2 Hf) as [w [[<-|[<-|[]]] Hwf]]; tauto ]. }
  (* a member of B on a named crossing pair, or a three-key cover *)
  assert (Hcorner : forall p q, In p [a;b] -> In q [c;d] ->
            existsb (containsb [p;q]) B = false ->
            forall C, In C B -> ~ (In p C /\ In q C)).
  { intros p q Hp Hq E C HC [HpC HqC].
    assert (Hin : existsb (containsb [p;q]) B = true).
    { apply existsb_exists; exists C; split; [exact HC|].
      apply containsb_true_iff; intros t [<-|[<-|[]]]; assumption. }
    congruence. }
  destruct (existsb (containsb [a;c]) B) eqn:Eac; [| right ].
  2:{ apply (@three_keys_bound r B [a;d] [b;c] [b;d] HRB
               (pair_nodup Had) eq_refl (pair_nodup Hbc) eq_refl
               (pair_nodup Hbd) eq_refl).
      intros C HC; destruct (Hsplit C HC) as [[Ha|Hb'] [Hc|Hd']].
      - exfalso; apply (Hcorner a c ltac:(simpl; tauto) ltac:(simpl; tauto) Eac C HC);
          split; assumption.
      - left; intros t [<-|[<-|[]]]; assumption.
      - right; left; intros t [<-|[<-|[]]]; assumption.
      - right; right; intros t [<-|[<-|[]]]; assumption. }
  destruct (existsb (containsb [a;d]) B) eqn:Ead; [| right ].
  2:{ apply (@three_keys_bound r B [a;c] [b;c] [b;d] HRB
               (pair_nodup Hac) eq_refl (pair_nodup Hbc) eq_refl
               (pair_nodup Hbd) eq_refl).
      intros C HC; destruct (Hsplit C HC) as [[Ha|Hb'] [Hc|Hd']].
      - left; intros t [<-|[<-|[]]]; assumption.
      - exfalso; apply (Hcorner a d ltac:(simpl; tauto) ltac:(simpl; tauto) Ead C HC);
          split; assumption.
      - right; left; intros t [<-|[<-|[]]]; assumption.
      - right; right; intros t [<-|[<-|[]]]; assumption. }
  destruct (existsb (containsb [b;c]) B) eqn:Ebc; [| right ].
  2:{ apply (@three_keys_bound r B [a;c] [a;d] [b;d] HRB
               (pair_nodup Hac) eq_refl (pair_nodup Had) eq_refl
               (pair_nodup Hbd) eq_refl).
      intros C HC; destruct (Hsplit C HC) as [[Ha|Hb'] [Hc|Hd']].
      - left; intros t [<-|[<-|[]]]; assumption.
      - right; left; intros t [<-|[<-|[]]]; assumption.
      - exfalso; apply (Hcorner b c ltac:(simpl; tauto) ltac:(simpl; tauto) Ebc C HC);
          split; assumption.
      - right; right; intros t [<-|[<-|[]]]; assumption. }
  destruct (existsb (containsb [b;d]) B) eqn:Ebd; [| right ].
  2:{ apply (@three_keys_bound r B [a;c] [a;d] [b;c] HRB
               (pair_nodup Hac) eq_refl (pair_nodup Had) eq_refl
               (pair_nodup Hbc) eq_refl).
      intros C HC; destruct (Hsplit C HC) as [[Ha|Hb'] [Hc|Hd']].
      - left; intros t [<-|[<-|[]]]; assumption.
      - right; left; intros t [<-|[<-|[]]]; assumption.
      - right; right; intros t [<-|[<-|[]]]; assumption.
      - exfalso; apply (Hcorner b d ltac:(simpl; tauto) ltac:(simpl; tauto) Ebd C HC);
          split; assumption. }
  (* all four crossing pairs occur in B: then only [a;b] and [c;d] can
     meet every one of them *)
  left.
  assert (Hget : forall p q, existsb (containsb [p;q]) B = true ->
            exists f, In f B /\ In p f /\ In q f).
  { intros p q E; apply existsb_exists in E as [f [Hf Cf]].
    apply containsb_true_iff in Cf.
    exists f; repeat split;
      [exact Hf | apply Cf; left; reflexivity | apply Cf; right; left; reflexivity]. }
  destruct (Hget a c Eac) as [fac [Hfac [Hafac Hcfac]]].
  destruct (Hget a d Ead) as [fad [Hfad [Hafad Hdfad]]].
  destruct (Hget b c Ebc) as [fbc [Hfbc [Hbfbc Hcfbc]]].
  destruct (Hget b d Ebd) as [fbd [Hfbd [Hbfbd Hdfbd]]].
  destruct (@uniform_mem 2 B fac HUB Hfac) as [Llac Nac].
  destruct (@uniform_mem 2 B fad HUB Hfad) as [Llad Nad].
  destruct (@uniform_mem 2 B fbc HUB Hfbc) as [Llbc Nbc].
  destruct (@uniform_mem 2 B fbd HUB Hfbd) as [Llbd Nbd].
  apply (@two_keys_bound r A [a;b] [c;d] HRA
           (pair_nodup Hab) eq_refl (pair_nodup Hcd) eq_refl).
  intros C HC.
  destruct (@uniform_mem 2 A C HUA HC) as [LlC NC].
  (* C meets fac = {a,c} and fbd = {b,d} *)
  assert (Hone : In a C \/ In c C).
  { destruct (Hcross C fac HC Hfac) as [w [HwC Hwf]].
    destruct (@two_elem_only fac a c w Llac Nac Hafac Hcfac Hac Hwf) as [<-|<-];
      tauto. }
  assert (Htwo : In b C \/ In d C).
  { destruct (Hcross C fbd HC Hfbd) as [w [HwC Hwf]].
    destruct (@two_elem_only fbd b d w Llbd Nbd Hbfbd Hdfbd Hbd Hwf) as [<-|<-];
      tauto. }
  destruct Hone as [HaC|HcC]; destruct Htwo as [HbC|HdC].
  - left; intros t [<-|[<-|[]]]; assumption.
  - (* a and d in C: C meets fbc = {b,c}, but every point of C is a or d *)
    exfalso.
    destruct (Hcross C fbc HC Hfbc) as [w [HwC Hwf]].
    destruct (@two_elem_only fbc b c w Llbc Nbc Hbfbc Hcfbc Hbc Hwf) as [<-|<-].
    + destruct (@two_elem_only C a d w LlC NC HaC HdC Had HwC); congruence.
    + destruct (@two_elem_only C a d w LlC NC HaC HdC Had HwC); congruence.
  - (* c and b in C: C meets fad = {a,d}, but every point of C is c or b *)
    exfalso.
    destruct (Hcross C fad HC Hfad) as [w [HwC Hwf]].
    destruct (@two_elem_only fad a d w Llad Nad Hafad Hdfad Had Hwf) as [<-|<-].
    + destruct (@two_elem_only C c b w LlC NC HcC HbC
                  ltac:(congruence) HwC); congruence.
    + destruct (@two_elem_only C c b w LlC NC HcC HbC
                  ltac:(congruence) HwC); congruence.
  - right; intros t [<-|[<-|[]]]; assumption.
Qed.

(** > **Neither side a star gives six, at every [r].** No degree cap
    > appears: the keys are pairs, and a pair has degree at most
    > [r^0 = 1] whatever [r] is. *)

Lemma greedy_four :
  forall r (F H0 : Family),
    Uniform 2 F -> RaoSpread 2 H0 r ->
    (forall e f, In e F -> In f H0 -> exists w, In w e /\ In w f) ->
    (forall w, exists e, In e F /\ ~ In w e) ->
    length H0 <= 4.
Proof.
  intros r F H0 HUF HRH Hcross Hns.
  assert (H : length H0 <= 2 ^ 2 * r ^ (2 - 2)).
  { apply (@greedy_bound 2 F H0 2 r ltac:(lia) HUF HRH Hcross).
    intros S HS; destruct S as [|w S0].
    - destruct (Hns 0) as [e [He _]]; exists e; split; [exact He | intros y []].
    - assert (ES : S0 = []) by (destruct S0; [reflexivity | simpl in HS; lia]).
      subst S0.
      destruct (Hns w) as [e [He Hwe]]; exists e; split;
        [exact He | intros y [<-|[]]; subst; exact Hwe]. }
  assert (E4 : 2 ^ 2 * r ^ (2 - 2) = 4)
    by (rewrite Nat.sub_diag, Nat.pow_0_r, Nat.mul_1_r; reflexivity).
  rewrite E4 in H; exact H.
Qed.

Lemma unpointed_pair_bound :
  forall r (A B : Family),
    Uniform 2 A -> Uniform 2 B -> RaoSpread 2 A r -> RaoSpread 2 B r ->
    (forall e f, In e A -> In f B -> exists w, In w e /\ In w f) ->
    (forall w, exists e, In e A /\ ~ In w e) ->
    (forall w, exists f, In f B /\ ~ In w f) ->
    length A + length B <= 6.
Proof.
  intros r A B HUA HUB HRA HRB Hcross HnsA HnsB.
  assert (Hflip : forall e f, In e B -> In f A -> exists w, In w e /\ In w f).
  { intros e f He Hf; destruct (Hcross f e Hf He) as [w [Ha Hb]];
      exists w; split; assumption. }
  assert (H4A : length A <= 4) by (apply (@greedy_four r B A HUB HRA Hflip HnsB)).
  assert (H4B : length B <= 4) by (apply (@greedy_four r A B HUA HRB Hcross HnsA)).
  assert (Hint_of : forall (F : Family),
            existsb (fun e => existsb (fun f => disjointb e f) F) F = false ->
            forall e f, In e F -> In f F -> exists w, In w e /\ In w f).
  { intros F E e f He Hf.
    pose proof (existsb_false_forall _ _ _ E e He) as E1.
    pose proof (existsb_false_forall _ _ _ E1 f Hf) as E2.
    apply disjointb_false_iff in E2; exact E2. }
  destruct (existsb (fun e => existsb (fun f => disjointb e f) A) A) eqn:EDA.
  - apply existsb_exists in EDA as [e1 [He1 E1]].
    apply existsb_exists in E1 as [e2 [He2 E2]].
    apply disjointb_correct in E2.
    destruct (@disjoint_squeeze r A B e1 e2 HUA HUB HRA HRB He1 He2 E2 Hcross)
      as [HA2|HB3]; [lia|].
    destruct (existsb (fun e => existsb (fun f => disjointb e f) B) B) eqn:EDB.
    + apply existsb_exists in EDB as [f1 [Hf1 F1]].
      apply existsb_exists in F1 as [f2 [Hf2 F2]].
      apply disjointb_correct in F2.
      destruct (@disjoint_squeeze r B A f1 f2 HUB HUA HRB HRA Hf1 Hf2 F2 Hflip);
        lia.
    + destruct (@triangle_bound r B A HUB HUA HRB HRA
                  (Hint_of B EDB) HnsB Hflip); lia.
  - destruct (@triangle_bound r A B HUA HUB HRA HRB
                (Hint_of A EDA) HnsA Hcross); lia.
Qed.

(** > **The exact bound at [u = 2].** For every [r >= 2], two nonempty
    > cross-intersecting Rao(r)-spread graphs have at most
    > [max(2r+1, 6)] edges between them — and that is the truth at every
    > [r >= 2]. From [r = 3] on the extremal configuration is one edge
    > against the two full stars at its endpoints, [2r+1]; at [r = 2] it
    > is two disjoint edges against the four crossing edges, 6. *)

Theorem cross_pair_two_exact :
  forall r (A B : Family),
    2 <= r ->
    Uniform 2 A -> Uniform 2 B ->
    RaoSpread 2 A r -> RaoSpread 2 B r ->
    (forall e f, In e A -> In f B -> exists w, In w e /\ In w f) ->
    A <> [] -> B <> [] ->
    length A + length B <= Nat.max (2 * r + 1) 6.
Proof.
  intros r A B Hr HUA HUB HRA HRB Hcross HAne HBne.
  assert (Hflip : forall e f, In e B -> In f A -> exists w, In w e /\ In w f).
  { intros e f He Hf; destruct (Hcross f e Hf He) as [w [Ha Hb]];
      exists w; split; assumption. }
  assert (HDA : Distinct A) by (apply (@rao_uniform_distinct 2 r A ltac:(lia) HUA HRA)).
  assert (HDB : Distinct B) by (apply (@rao_uniform_distinct 2 r B ltac:(lia) HUB HRB)).
  assert (Htwo : forall (F : Family), Distinct F -> 2 <= length F ->
                   exists e1 e2, In e1 F /\ In e2 F /\ ~ SetEq e1 e2).
  { intros F HDF Hlen.
    destruct F as [|f1 [|f2 F0]]; simpl in Hlen; try lia.
    exists f1, f2; repeat split;
      [left; reflexivity | right; left; reflexivity |].
    inversion HDF as [|? ? Hdist ?]; subst.
    apply Hdist; left; reflexivity. }
  (* the one-sided bounds *)
  assert (HpA : length A <= 2 * r).
  { pose proof (@partner_bound_one 2 r B A ltac:(lia) HBne HUB HRA Hflip) as H.
    replace (2 - 2) with 0 in H by reflexivity.
    rewrite Nat.pow_0_r, Nat.mul_1_r in H; exact H. }
  assert (HpB : length B <= 2 * r).
  { pose proof (@partner_bound_one 2 r A B ltac:(lia) HAne HUA HRB Hcross) as H.
    replace (2 - 2) with 0 in H by reflexivity.
    rewrite Nat.pow_0_r, Nat.mul_1_r in H; exact H. }
  destruct (le_lt_dec (length A) 1) as [HA1|HA2]; [lia|].
  destruct (le_lt_dec (length B) 1) as [HB1|HB2]; [lia|].
  (* both sides have at least two members, so Lemma P applies both ways *)
  destruct (Htwo A HDA ltac:(lia)) as [a1 [a2 [Ha1 [Ha2 Hane]]]].
  destruct (Htwo B HDB ltac:(lia)) as [b1 [b2 [Hb1 [Hb2 Hbne]]]].
  assert (HqB : length B <= Nat.max (r + 1) 4)
    by (apply (@pair_partner_bound r A B a1 a2 HUA HRB Ha1 Ha2 Hane Hcross)).
  assert (HqA : length A <= Nat.max (r + 1) 4)
    by (apply (@pair_partner_bound r B A b1 b2 HUB HRA Hb1 Hb2 Hbne Hflip)).
  (* the star bound, when a side is pointed *)
  assert (Hstar : forall (F : Family) w, Pointed F w -> RaoSpread 2 F r ->
                    length F <= r).
  { intros F w Hpt HRF.
    assert (H : length F <= 1 * r ^ (2 - 1)).
    { apply (@cover_size_bound F 2 r 1 [w] HRF).
      - intros C HC; exists w; split; [left; reflexivity | apply Hpt; exact HC].
      - simpl; lia. }
    simpl in H; lia. }
  destruct (covers_at_most A 1) eqn:EA.
  - (* A is a star *)
    destruct (@pointed_of_cover A HAne EA) as [wA HA].
    destruct (le_lt_dec (length A) 2) as [HAle|HAgt]; [lia|].
    assert (HBpt : Pointed B wA).
    { apply (@star_saturation 2 r A B wA HUB HRA HA Hcross).
      replace (2 - 2) with 0 by reflexivity; rewrite Nat.pow_0_r; lia. }
    pose proof (Hstar A wA HA HRA); pose proof (Hstar B wA HBpt HRB); lia.
  - assert (HnsA : forall w, exists e, In e A /\ ~ In w e)
      by (intros w; apply (@not_pointed_of_search A w EA)).
    destruct (covers_at_most B 1) eqn:EB.
    + (* B is a star, A is not: a large B would drag A into it *)
      destruct (@pointed_of_cover B HBne EB) as [wB HB].
      destruct (le_lt_dec (length B) 2) as [HBle|HBgt]; [lia|].
      assert (HApt : Pointed A wB).
      { apply (@star_saturation 2 r B A wB HUA HRB HB Hflip).
        replace (2 - 2) with 0 by reflexivity; rewrite Nat.pow_0_r; lia. }
      destruct (HnsA wB) as [C [HC HwC]]; exfalso; apply HwC, HApt, HC.
    + (* neither is a star *)
      assert (HnsB : forall w, exists f, In f B /\ ~ In w f)
        by (intros w; apply (@not_pointed_of_search B w EB)).
      pose proof (@unpointed_pair_bound r A B HUA HUB HRA HRB Hcross HnsA HnsB); lia.
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

(** ** Both branches of the maximum are attained

    The [2r+1] branch is one edge against the two full stars at its
    endpoints, which needs [r >= 3] to beat 6. The 6 branch is the
    disjoint-pair configuration of [disjoint_squeeze] with both sides
    full — two disjoint edges against the four crossing edges — and at
    [r = 2] it is 6 against [2r+1 = 5], so dropping the 6 would make the
    theorem false. Degree two is exactly where all four crossing edges
    fit. *)

Definition cross_b (A B : Family) : bool :=
  forallb (fun e => forallb (fun f => negb (disjointb e f)) B) A.

Lemma cross_b_correct :
  forall A B, cross_b A B = true ->
    forall e f, In e A -> In f B -> exists w, In w e /\ In w f.
Proof.
  intros A B H e f He Hf; unfold cross_b in H.
  rewrite forallb_forall in H; specialize (H e He).
  rewrite forallb_forall in H; specialize (H f Hf).
  apply Bool.negb_true_iff in H; apply disjointb_false_iff in H; exact H.
Qed.

Definition c2a : Family := [[0;2];[1;3]].
Definition c2b : Family := [[0;1];[0;3];[1;2];[2;3]].

Theorem cross_pair_two_six_is_attained :
  Uniform 2 c2a /\ Uniform 2 c2b /\
  RaoSpread 2 c2a 2 /\ RaoSpread 2 c2b 2 /\
  (forall e f, In e c2a -> In f c2b -> exists w, In w e /\ In w f) /\
  c2a <> [] /\ c2b <> [] /\
  (forall w, exists e, In e c2a /\ ~ In w e) /\
  (forall w, exists f, In f c2b /\ ~ In w f) /\
  length c2a + length c2b = 6 /\
  2 * 2 + 1 < length c2a + length c2b.
Proof.
  assert (HUa : Uniform 2 c2a)
    by (apply uniformb_correct; vm_compute; reflexivity).
  assert (HUb : Uniform 2 c2b)
    by (apply uniformb_correct; vm_compute; reflexivity).
  assert (HRa : RaoSpread 2 c2a 2).
  { apply (@rao_spreadb_correct 2 c2a 2 [0;1;2;3]).
    - apply nodupb_correct; vm_compute; reflexivity.
    - apply Forall_forall; intros X HX.
      destruct (@uniform_mem 2 c2a X HUa HX) as [_ Hnd]; exact Hnd.
    - apply groundedb_correct; vm_compute; reflexivity.
    - vm_compute; reflexivity. }
  assert (HRb : RaoSpread 2 c2b 2).
  { apply (@rao_spreadb_correct 2 c2b 2 [0;1;2;3]).
    - apply nodupb_correct; vm_compute; reflexivity.
    - apply Forall_forall; intros X HX.
      destruct (@uniform_mem 2 c2b X HUb HX) as [_ Hnd]; exact Hnd.
    - apply groundedb_correct; vm_compute; reflexivity.
    - vm_compute; reflexivity. }
  repeat apply conj; try assumption.
  - apply cross_b_correct; vm_compute; reflexivity.
  - discriminate.
  - discriminate.
  - intros w; apply (@unpointed_dec_search c2a w);
      [vm_compute; reflexivity | discriminate].
  - intros w; apply (@unpointed_dec_search c2b w);
      [vm_compute; reflexivity | discriminate].
  - vm_compute; reflexivity.
  - vm_compute; lia.
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

(** ** [I2(m,r)]: the largest non-star intersecting Rao-spread family

    [I(m,r)] is the largest [m]-uniform intersecting Rao(r)-spread family
    and [StarExtremalAt] is the claim that a star attains it. Take the
    stars away and a different quantity appears, which §27.2's
    construction is built out of:

    > [I2(m,r)] — the largest such family that is **not** a star.

    At [m = 3] it is bounded by two disjoint arguments meeting at the
    covering number. If [tau <= 2], [CrossIntersecting.two_cover_split]
    splits the family against its cover into two cross-intersecting
    2-uniform tail families plus a both-points piece of at most
    [r^(m-2) = r], and [cross_pair_refined] at [u = 2] caps the tails at
    [2·max(4, r+1)] — which for [r >= 3] is [2r+2], so the whole family is
    at most [3r+2]. If [tau >= 3], [TauThree.tau_three_bound] gives 16
    with no Rao condition at all.

    [cross_pair_bound] cannot do this: at [u = 2], [r = 5] it gives 20,
    so the [tau <= 2] branch would come out at 25 — exactly the star
    bound [r^(m-1)], i.e. no information. The whole content of the
    theorem below is the refined pair bound. *)

Definition NonStar (A : Family) : Prop :=
  forall w, exists C, In C A /\ ~ In w C.

Lemma nonstar_not_pointed :
  forall A w, NonStar A -> ~ Pointed A w.
Proof.
  intros A w Hns Hpt; destruct (Hns w) as [C [HC HwC]]; apply HwC, Hpt, HC.
Qed.

Theorem nonstar_three_bound :
  forall r (A : Family),
    3 <= r ->
    Uniform 3 A -> Distinct A -> RaoSpread 3 A r ->
    (forall C D, In C A -> In D A -> exists x, In x C /\ In x D) ->
    NonStar A ->
    length A <= Nat.max (3 * r + 1) 16.
Proof.
  intros r A Hr HU HD HR Hint Hns.
  destruct (covers_at_most A 2) eqn:E.
  - (* covering number at most two: split against the cover *)
    destruct (small_cover_of _ _ E) as [S [Hlen Hcov]].
    destruct S as [|p [|q S']]; simpl in Hlen.
    + exfalso; destruct (Hns 0) as [C [HC _]].
      destruct (Hcov C HC) as [x [[] _]].
    + exfalso; destruct (Hns p) as [C [HC HpC]].
      destruct (Hcov C HC) as [x [[Ex|[]] HxC]]; subst x; contradiction.
    + assert (ES : S' = [])
        by (destruct S'; [reflexivity | simpl in Hlen; lia]).
      subst S'.
      assert (Hcov2 : forall C, In C A -> In p C \/ In q C).
      { intros C HC; destruct (Hcov C HC) as [x [[Ex|[Ex|[]]] HxC]];
          subst x; [left | right]; exact HxC. }
      destruct (Nat.eq_dec p q) as [Epq|Hpq].
      { exfalso; subst q; destruct (Hns p) as [C [HC HpC]].
        destruct (Hcov2 C HC); contradiction. }
      destruct (@two_cover_split 3 r A p q ltac:(lia) Hpq HU HR Hint Hcov2)
        as [[w Hw] | [X [Y [HUX [HUY [HRX [HRY [Hcross [HXne [HYne Hle]]]]]]]]]].
      { exfalso; exact (@nonstar_not_pointed A w Hns Hw). }
      pose proof (@cross_pair_two_exact r X Y ltac:(lia) HUX HUY HRX HRY
                    Hcross HXne HYne) as Hsum.
      replace (3 - 2) with 1 in Hle by reflexivity.
      rewrite Nat.pow_1_r in Hle.
      lia.
  - (* covering number at least three: Frankl's range, without Rao *)
    assert (Htau : forall p q, exists C, In C A /\ ~ In p C /\ ~ In q C).
    { intros p q.
      destruct (@no_small_cover A 2 E [p; q] ltac:(simpl; lia)) as [C [HC Hmiss]].
      exists C; repeat split;
        [exact HC | apply Hmiss; left; reflexivity
         | apply Hmiss; right; left; reflexivity]. }
    pose proof (tau_three_bound HU HD Hint Htau); lia.
Qed.

(** > **[I2(3,5) <= 16]**, the row the `m = 4` construction runs on — and
    > [hm16] attains it, so the value is exact. *)

Corollary nonstar_three_five_at_most_sixteen :
  forall (A : Family),
    Uniform 3 A -> Distinct A -> RaoSpread 3 A 5 ->
    (forall C D, In C A -> In D A -> exists x, In x C /\ In x D) ->
    NonStar A ->
    length A <= 16.
Proof.
  intros A HU HD HR Hint Hns.
  pose proof (@nonstar_three_bound 5 A ltac:(lia) HU HD HR Hint Hns) as H.
  vm_compute in H; exact H.
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

Lemma hm16_nonstar : NonStar hm16.
Proof. exact hm16_unpointed. Qed.

(** > **[I2(3,5) = 16]** — an exact value. [hm16] attains it and nothing
    > beats it. The two halves meet because [hm16] realises the two-cover
    > split exactly: at the cover [{4,12}] it has one member through 4
    > only, ten through 12 only and five through both, so [11 + 5], where
    > 11 is [cross_pair_two_exact]'s [2r+1] and 5 is the pair degree. *)

Theorem i2_three_five_is_sixteen :
  (Uniform 3 hm16 /\ Distinct hm16 /\ RaoSpread 3 hm16 5 /\
   (forall C D, In C hm16 -> In D hm16 -> exists x, In x C /\ In x D) /\
   NonStar hm16 /\ length hm16 = 16)
  /\ (forall A : Family,
         Uniform 3 A -> Distinct A -> RaoSpread 3 A 5 ->
         (forall C D, In C A -> In D A -> exists x, In x C /\ In x D) ->
         NonStar A -> length A <= 16).
Proof.
  split.
  - exact (conj hm16_uniform
             (conj hm16_distinct
                (conj hm16_rao
                   (conj (@hm16_int) (conj hm16_nonstar hm16_length))))).
  - exact (@nonstar_three_five_at_most_sixteen).
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
