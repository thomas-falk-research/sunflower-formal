(** * Palvolgyi's 2015 equality remark, carried as a hypothesis.

    On 23 December 2015, in comment 23193 on Gil Kalai's Polymath10
    post *"Polymath 10 Post 3: How are we doing?"*, Domotor Palvolgyi
    wrote (verbatim; the formulae are the LaTeX sources of the two
    rendered images in the comment):

    > A further possible simplification could be to try constructions
    > for intersecting families. If we denote the size of the largest
    > k-uniform intersecting family without an r-sunflower by
    > [f^{int}(k,r)], then we have [(r-1)\cdot f^{int}(k,r)\le f(k,r)].
    > In fact, if I understood well, it is even possible (though
    > unlikely) that equality holds for all values of k and r. This is
    > the case for all best constructions for r=3, but not for r=4,
    > k=3 (see our wiki and Abbott-Exoo).

    Two separate things are in that paragraph, and this development
    already had one of them.

    ** The inequality is [Intersecting.doubling_lower_bound]

    At [r = 3] the inequality reads [2 * iota(k) <= g(k)], which is
    exactly what [Intersecting.doubling_lower_bound] proves, by exactly
    the construction [Intersecting.double] implements: two disjoint
    copies. This module does not reprove it. It records that the
    statement is due to Palvolgyi in December 2015 and was re-derived
    here, and [docs/reading.md] row A17a carries the citation.

    ** The equality is new here, and is a conjecture its own proposer
       called unlikely

    At [r = 3] the equality reads [g(k) = 2 * iota(k)]. It holds at both
    known points -- [g(2) = 6 = 2 * 3] and [g(3) = 20 = 2 * 10] -- and
    nothing in this development bears on it either way. It is carried
    below as a [Prop], never as an axiom, exactly as
    [AbbottGardner.AbbottGardner1969] and [SliceRank.NaslundSawinBound]
    are, and for the same reason: a citation the kernel can check the
    consequences of is worth more than a citation in a comment.

    Note the last sentence of the quotation. Equality is *known to fail*
    at [r = 4, k = 3]. So this is a conjecture about three-sunflowers and
    nothing wider, and [PalvolgyiEquality] below is stated at [r = 3]
    only -- which is the only [r] this development has predicates for. *)

From Coq Require Import List Arith Lia.
Import ListNotations.

From Sunflower Require Import Sets Sunflower Intersecting IotaRate Product
                              AbbottGardner PureLink.

Set Implicit Arguments.

(** ** The statement

    The useful direction of [g = 2 * iota]: an upper bound on [iota]
    doubles to an upper bound on [g]. Paired with
    [Intersecting.doubling_lower_bound], which supplies [g >= 2 * iota]
    unconditionally, this is the equality.

    Stating it this way rather than as a bare equation is what makes it
    usable: [iota] and [g] are not functions here but the four relations
    [IotaAtLeast], [IotaAtMost], [LowerBound] and [GAtMost], and an
    equation between values would have to be threaded through witnesses
    that may not exist. *)

Definition PalvolgyiEquality : Prop :=
  forall b N, 1 <= b -> IotaAtMost b N -> GAtMost b (2 * N).

(** ** What the kernel can check about it

    Three things, and they are the same three that [AbbottGardner.v]
    checks about the 1969 value: that it is not vacuous, that it is
    consistent with what is proved, and what it buys. *)

(** *** It is not vacuous: it implies a theorem

    Abbott and Gardner proved [g(3) = 20] in 1969, and this development
    carries that as [AbbottGardner1969]. Palvolgyi's remark *implies*
    it, given the exhaustive [iota(3) = 10] that `rust/src/wide.rs`
    computes -- so the conjecture is at least as strong as a published
    theorem, and a refutation of it would have to leave that theorem
    standing. *)

Theorem palvolgyi_implies_abbott_gardner :
  PalvolgyiEquality -> IotaAtMost 3 10 -> AbbottGardner1969.
Proof.
  intros HP H10.
  unfold AbbottGardner1969.
  replace 20 with (2 * 10) by reflexivity.
  exact (HP 3 10 ltac:(lia) H10).
Qed.

(** *** It is pinned from below by an object

    [Intersecting.lower_bound_3_3_20] builds twenty 3-sets with no
    3-sunflower, so [GAtMost 3 19] is false. Palvolgyi's remark lands on
    [GAtMost 3 20] and cannot land lower: the conjecture predicts the
    exact value at [b = 3], and the prediction is checked against a
    family rather than against a citation. Had he written a smaller
    multiplier, this would not compile. *)

Theorem palvolgyi_pins_g_three_exactly :
  PalvolgyiEquality -> IotaAtMost 3 10 -> GAtMost 3 20 /\ ~ GAtMost 3 19.
Proof.
  intros HP H10.
  split.
  - exact (palvolgyi_implies_abbott_gardner HP H10).
  - exact AbbottGardner.gardner_value_is_not_vacuous.
Qed.

(** *** It is strictly stronger than the proved bound

    [PureLink.g_three_at_most_26] is unconditional. The conjecture beats
    it by six at [b = 3], which is the gap the 1969 citation is
    currently filling. *)

Theorem palvolgyi_beats_the_proved_bound_at_three :
  PalvolgyiEquality -> IotaAtMost 3 10 ->
  GAtMost 3 20 /\ GAtMost 3 26 /\ 20 < 26.
Proof.
  intros HP H10.
  split; [exact (palvolgyi_implies_abbott_gardner HP H10)|].
  split; [exact PureLink.g_three_at_most_26|lia].
Qed.

(** ** What it says one rung up

    At [b = 4] the conjecture is not yet sharp, because the upper bound
    on [iota(4)] is not. [PureLink.iota_four_at_most_71_if_iota_three_is_ten]
    gives 71, so the conjecture gives [g(4) <= 142] -- weaker than the
    proved [PureLink.g_four_at_most_142] it happens to match, and weaker
    than [AbbottGardner.g_four_at_most_130]. It becomes sharp exactly
    when [iota(4)] is decided, which is what the `iota(4,11)` ladder in
    `docs/roadmap.md` is for. *)

Theorem palvolgyi_at_four_needs_iota_four :
  PalvolgyiEquality -> IotaAtMost 3 10 -> GAtMost 4 142.
Proof.
  intros HP H10.
  replace 142 with (2 * 71) by reflexivity.
  exact (HP 4 71 ltac:(lia) (PureLink.iota_four_at_most_71_if_iota_three_is_ten H10)).
Qed.

(** *** And what deciding [iota(4)] would then buy

    If the ladder closes at 27 -- the value
    [Product.iota_four_at_least_27] already witnesses from below -- the
    conjecture says [g(4) = 54] exactly, and this development's best
    4-uniform construction, [Product.lower_bound_4_3_54], has exactly 54
    members. So the conjecture's content at [b = 4] is precisely *that
    the doubled substitution family is optimal*, and the two ends meet
    at the same number. That is the strongest reason to carry it: it
    turns the `iota(4)` ladder into a test of a named conjecture rather
    than only into a value. *)

Theorem palvolgyi_at_four_if_iota_four_is_27 :
  PalvolgyiEquality -> IotaAtMost 4 27 ->
  GAtMost 4 54 /\ LowerBound 4 3 54.
Proof.
  intros HP H27.
  split.
  - replace 54 with (2 * 27) by reflexivity.
    exact (HP 4 27 ltac:(lia) H27).
  - exact Product.lower_bound_4_3_54.
Qed.

(** ** How to kill it

    A single family refutes the conjecture: any [b] at which [iota(b)]
    is bounded above by [N] and some [b]-uniform sunflower-free family
    has [2 * N + 1] members. Nothing weaker will do -- an odd [g(b)]
    with [iota(b)] undetermined says nothing -- and this is the shape any
    future refutation has to take. *)

Theorem palvolgyi_refuted_by_one_family :
  forall b N,
    1 <= b -> IotaAtMost b N -> LowerBound b 3 (2 * N + 1) ->
    ~ PalvolgyiEquality.
Proof.
  intros b N Hb HN [F [HU [HD [Hlen Hno]]]] HP.
  pose proof (HP b N Hb HN F HU HD Hno) as Hle.
  lia.
Qed.

(** *** The refutation is out of reach at both decided rungs, and that
        is the honest reason this file proves no more

    At [b = 3] it needs a 21-member 3-uniform sunflower-free family, and
    [AbbottGardner.f_3_3_at_most_21] says every 21-member family
    contains a sunflower. At [b = 4] it needs 143 members against a
    proved ceiling of 142. Both are closed; the conjecture survives
    everything this development can currently throw at it. *)

Theorem no_refutation_at_three :
  AbbottGardner1969 -> ~ LowerBound 3 3 21.
Proof.
  intros HAG [F [HU [HD [Hlen Hno]]]].
  apply Hno.
  apply (AbbottGardner.f_3_3_at_most_21 HAG F HU HD).
  lia.
Qed.

Theorem no_refutation_at_four :
  IotaAtMost 3 10 -> ~ LowerBound 4 3 143.
Proof.
  intros H10 [F [HU [HD [Hlen Hno]]]].
  (* [F] is a strict implicit of [GAtMost] -- [IotaRate.v] sets
     [Implicit Arguments] -- so it must not be supplied here, whereas the
     [UpperBound] application above, from [Sunflower.v], takes it. *)
  pose proof (PureLink.g_four_at_most_142_if_iota_three_is_ten H10 HU HD Hno) as Hle.
  lia.
Qed.
