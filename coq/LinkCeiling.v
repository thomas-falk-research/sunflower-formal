(** * LinkCeiling.v -- how big a sunflower-free family on [n] points can
      be, from the matching number of its links.

    [LinkCharacterisation.sunflower_iff_link_matching] says a family is
    3-sunflower-free exactly when no link carries three pairwise disjoint
    members. That is a statement about *links*; this file turns the top
    case of it into a statement about *degrees*, which is what a search
    can use.

    The link over a set [Y] of size [b-1] in a [b]-uniform family is
    **1-uniform**, and distinct singletons are automatically disjoint. So
    three members through [Y] are three pairwise disjoint members of that
    link, hence a sunflower:

<<
      |Y| = b - 1   =>   deg Y F <= 2.
>>

    Counting members against the [(b-1)]-subsets they contain — each
    member has exactly [b] of them, and there are [C(n, b-1)] available —
    turns this into

<<
      |F| <= (2/b) * C(n, b-1),
>>

    and the same argument one level down, where the link is a graph with
    maximum degree 2 and no 3-matching and so is at most two disjoint
    triangles, gives [|F| <= (6 / C(b,2)) * C(n, b-2)]. The arithmetic is
    `genprog::size_ceiling` and `rust/tests/genprog.rs` pins its values;
    what is proved here is the degree bound the arithmetic rests on,
    which is the part that is a theorem rather than a computation.

    Why it matters: the ceilings say [iota(5) >= 101] — the threshold
    that would beat Abbott–Hanson–Sauer — is impossible below twelve
    points, and that §9's [b = 5] SAT row, run at ground 10 where the
    ceiling is 72, was asked at a ground that could not answer it. See
    `docs/roadmap.md` §23. *)

From Coq Require Import List Arith Lia.
From Sunflower Require Import Sets Sunflower Spread SpreadReduction TwoUniform
     LinkCharacterisation.
Import ListNotations.

Set Implicit Arguments.

(** A 1-uniform distinct family is pairwise disjoint: its members are
    singletons, and two singletons that are not set-equal hold different
    points. *)

Lemma one_uniform_pairwise_disjoint :
  forall (G : Family),
    Uniform 1 G -> Distinct G -> PairwiseDisjoint G.
Proof.
  intros G HU HD A B HA HB Hne.
  unfold Uniform in HU; rewrite Forall_forall in HU.
  destruct (HU A HA) as [HlA _]; destruct (HU B HB) as [HlB _].
  destruct A as [|a [|? ?]]; simpl in HlA; try discriminate.
  destruct B as [|b [|? ?]]; simpl in HlB; try discriminate.
  intros x [E | []] [E' | []]; apply Hne; subst; reflexivity.
Qed.

(** ** The top link degree

    Three members through a [(b-1)]-set are a sunflower. *)

Theorem top_link_degree_at_most_two :
  forall b (F : Family) (Y : list nat),
    1 <= b ->
    Uniform b F -> Distinct F ->
    NoDup Y -> length Y = b - 1 ->
    ~ ContainsKSunflower 3 F ->
    deg Y F <= 2.
Proof.
  intros b F Y Hb HU HD HndY HlenY Hfree.
  destruct (le_lt_dec (deg Y F) 2) as [Hle | Hgt]; [exact Hle | exfalso].
  apply Hfree.
  apply (@link_matching_gives_sunflower 3 F Y).
  (* The link is 1-uniform and distinct, so any three of its members are
     three pairwise disjoint members. *)
  pose proof (@link_uniform b Y F HU HndY) as HLU.
  rewrite HlenY in HLU.
  replace (b - (b - 1)) with 1 in HLU by lia.
  pose proof (@link_distinct Y F HD) as HLD.
  exists (firstn 3 (link Y F)); repeat split.
  - apply incl_firstn.
  - apply NoDup_firstn, SetNoDup_NoDup; exact HLD.
  - apply firstn_length_le; rewrite length_link; lia.
  - intros A B HA HB Hne.
    apply (one_uniform_pairwise_disjoint HLU HLD);
      [ apply (incl_firstn 3); exact HA
      | apply (incl_firstn 3); exact HB
      | exact Hne ].
Qed.

(** The bound is attained: at [b = 3] the 2-(6,3,2) design has every pair
    in exactly two blocks, which is why [iota(3) = 10] is *exactly* the
    counting ceiling `(2/3)*C(6,2)` at its own ground set. At [b = 4] the
    ceiling at eight points is 28 and no such family exists — the
    exhaustive check is `the_ceiling_is_not_attained_at_uniformity_four`
    in `rust/tests/genprog.rs`. *)

Corollary top_link_degree_three_uniform :
  forall (F : Family) (Y : list nat),
    Uniform 3 F -> Distinct F ->
    NoDup Y -> length Y = 2 ->
    ~ ContainsKSunflower 3 F ->
    deg Y F <= 2.
Proof.
  intros F Y HU HD HndY HlenY Hfree.
  exact (@top_link_degree_at_most_two 3 F Y ltac:(lia) HU HD HndY HlenY Hfree).
Qed.
