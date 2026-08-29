(** * The 1969 value of the first sunflower number, and what it buys

    [docs/roadmap.md] and [STATUS.md] have called [f(3,3)] *"the first
    unknown sunflower number"* since the [PureLink] session. It is not
    unknown. Kostochka's survey [Kos00], p. 4, rendered and read:

    <<
      Abbott and B. Gardner [2] proved in 1969 that f(3,3) = 20, and
      since then no other exact value of f(k,r) for k >= 3 and r >= 3
      became known.
    >>

    That is Kostochka's convention, in which [f(k,r)] is the *largest*
    family with no [Delta]-system of [r] sets — the introduction on p. 1
    defines it as *"the least cardinal so that any k-uniform family of
    more than f(k,r) sets contains a Delta-system consisting of r
    sets"*. So it is this development's [GAtMost 3], and it says
    [g(3) = 20] exactly, hence [f(3,3) = 21] in the convention of
    [Sunflower.UpperBound].

    The primary source ([2] = H. L. Abbott and B. Gardner, *On a
    combinatorial theorem of Erdos and Rado*, in W. T. Tutte, ed.,
    Recent progress in Combinatorics, Academic Press, 1969, 211-215) is
    not open access and was **not** read. What was read is the survey
    page, verbatim; and Bennett-Priestley (arXiv:2509.16355, p. 7,
    rendered) independently records that *"the precise answer is known
    for very small cases of r and w (e.g., [AG69b])"*, citing the same
    paper. `docs/reading.md` row A9 carries both, with their evidence
    classes.

    ** Why it is a hypothesis and not an axiom

    Exactly the discipline [SliceRank.NaslundSawinBound] and
    [Spread.SpreadYieldsDisjoint] already use: a value this development
    has not proved is carried as an explicit [Prop] on the statements
    that consume it, so [Print Assumptions] on everything below still
    reports [Closed under the global context] and the whole-library
    census is unchanged.

    ** Two things the kernel can check about it

    - [gardner_value_is_not_vacuous]: [GAtMost 3 19] is **false**, by the
      twenty-member family [Intersecting.lower_bound_3_3_20] already
      builds. So 20 is the truth boundary from below, checked here rather
      than cited, and a mis-transcription of the survey's number in the
      *low* direction would fail to compile.
    - [gardner_value_is_consistent_with_the_kernel]: it is not stronger
      than what is already proved — [PureLink.g_three_at_most_26] gives
      [GAtMost 3 26], and [20 <= 26].

    What no gate here can check is whether the survey sentence is true;
    it is a citation, and it is labelled as one. *)

From Coq Require Import List Arith Lia.
Import ListNotations.

From Sunflower Require Import Sets Sunflower Intersecting IotaRate PureLink
     F23 Product.

(** ** The value, named *)

(** [g(3) <= 20]: no 3-uniform family of distinct sets without a
    3-sunflower has more than twenty members. Abbott-Gardner 1969, via
    [Kos00] p. 4. *)
Definition AbbottGardner1969 : Prop := GAtMost 3 20.

(** ** The two kernel-side checks *)

(** The hypothesis is met with equality from below, and the witness is
    already in the development: doubling the ten-member [iota3] gives
    twenty 3-sets with no 3-sunflower. *)
Theorem gardner_value_is_not_vacuous : ~ GAtMost 3 19.
Proof.
  intros Hg.
  destruct lower_bound_3_3_20 as [F [HU [HD [Hlen Hno]]]].
  pose proof (Hg F HU HD Hno) as Hle.
  lia.
Qed.

(** And it is weaker than nothing the kernel already knows. *)
Theorem gardner_value_is_consistent_with_the_kernel :
  forall F, Uniform 3 F -> Distinct F -> ~ ContainsKSunflower 3 F ->
            AbbottGardner1969 -> length F <= 26.
Proof.
  intros F HU HD Hno Hag.
  pose proof (Hag F HU HD Hno) as Hle; lia.
Qed.

(** ** The first sunflower number, pinned

    [PureLink.f_3_3_at_most_27] and [Intersecting.lower_bound_3_3_20]
    trap [f(3,3)] in [[21, 27]]. The 1969 value closes the interval at
    its lower end — that is, **the lower bound this repository proves is
    the exact answer**, and the six-member gap was entirely on the upper
    side. *)

Theorem f_3_3_at_most_21 : AbbottGardner1969 -> UpperBound 3 3 21.
Proof.
  intro Hag.
  replace 21 with (S 20) by reflexivity.
  apply (upper_bound_of_sunflower_free_bound 3 20).
  exact Hag.
Qed.

Theorem f_3_3_is_exactly_21 :
  AbbottGardner1969 -> UpperBound 3 3 21 /\ ~ UpperBound 3 3 20.
Proof.
  intro Hag.
  split; [exact (f_3_3_at_most_21 Hag) | exact no_upper_bound_3_3_20].
Qed.

(** The same statement with the repository's own bound beside it, so the
    six that closes is visible in the type. *)
Theorem the_gap_at_f_3_3_was_entirely_above :
  AbbottGardner1969 ->
  UpperBound 3 3 21 /\ UpperBound 3 3 27 /\ ~ UpperBound 3 3 20 /\ 21 < 27.
Proof.
  intro Hag.
  repeat split;
    [ exact (f_3_3_at_most_21 Hag)
    | exact f_3_3_at_most_27
    | exact no_upper_bound_3_3_20
    | lia ].
Qed.

(** ** One rung up: what 20 buys at uniformity four

    [PureLink.iota_recursion_sharp] needs [b * (Ng + Ni) <= 2N + 1 + (b-2)].
    At [b = 4] with [Ng = 20] it runs with [N = 65] against the proved
    [iota(3) <= 13], and with [N = 59] against the exhaustively measured
    [iota(3) = 10]. Compare [PureLink.iota_four_at_most_77] and
    [iota_four_at_most_71_if_iota_three_is_ten], which are the same
    corollaries with [Ng = 26]. *)

Theorem iota_four_at_most_65 : AbbottGardner1969 -> IotaAtMost 4 65.
Proof.
  intro Hag.
  apply (@iota_recursion_sharp 4 20 13 65);
    [lia | exact Hag | exact iota_three_at_most_thirteen | lia].
Qed.

Theorem iota_four_at_most_59_if_iota_three_is_ten :
  AbbottGardner1969 -> IotaAtMost 3 10 -> IotaAtMost 4 59.
Proof.
  intros Hag H10.
  apply (@iota_recursion_sharp 4 20 10 59);
    [lia | exact Hag | exact H10 | lia].
Qed.

Theorem g_four_at_most_130 : AbbottGardner1969 -> GAtMost 4 130.
Proof.
  intro Hag.
  apply (@g_recursion_sharp 4 20 13 130);
    [lia | exact Hag | exact iota_three_at_most_thirteen | lia].
Qed.

(** The interval on [iota(4)], with both ends carried: the witnessed 27
    below ([Product.iota_four_at_least_27]) and the 1969-fed 59 above.
    [Sharp.AHSOptimal] needs [iota(4) <= 31], so the conditional interval
    is [[27, 59]] and the boundary 31/32 is still inside it. *)
Theorem iota_four_between_27_and_59 :
  AbbottGardner1969 -> IotaAtMost 3 10 ->
  ~ IotaAtMost 4 26 /\ IotaAtMost 4 59.
Proof.
  intros Hag H10.
  split;
    [ exact not_iota_four_at_most_26
    | exact (iota_four_at_most_59_if_iota_three_is_ten Hag H10) ].
Qed.

(** ** Closed, and it needs no hypothesis at all

    [docs/roadmap.md] §13.4 named this *"the most concrete thing left on
    the list"*:

    <<
      iota(4) >= 32, through the general row. By the cone, a 3-uniform
      sunflower-free family with 32 members gives iota(4) >= 32, refutes
      Sharp.AHSOptimal, and gives f(3,3) >= 33.
    >>

    The route was already dead when it was written. [Product.cone] needs
    a 3-uniform sunflower-free family of 32 members and
    [PureLink.g_three_at_most_26] says there is none — six short, with no
    hypothesis, no ground set and no search. The SAT run §13.4 records at
    [N(3,16) >= 30], 601 seconds and undecided, was asking a question the
    kernel in the same tree already answers. *)

Theorem no_three_uniform_sunflower_free_family_has_thirty_two_members :
  forall F, Uniform 3 F -> Distinct F -> ~ ContainsKSunflower 3 F ->
            length F < 32.
Proof.
  intros F HU HD Hno.
  pose proof (g_three_at_most_26 HU HD Hno) as Hle; lia.
Qed.

(** The same fact in the shape §13.4 used it: the cone from uniformity
    three cannot reach 32 at uniformity four, so it cannot refute
    [Sharp.AHSOptimal]. Stated against [GAtMost] so that it is visibly
    an arithmetic consequence of a bound rather than of the construction. *)
Theorem the_cone_route_to_iota_four_thirty_two_is_closed :
  forall N, GAtMost 3 N -> N < 32 ->
            forall F, Uniform 3 F -> Distinct F ->
                      ~ ContainsKSunflower 3 F -> length F < 32.
Proof.
  intros N Hg Hlt F HU HD Hno.
  pose proof (Hg F HU HD Hno) as Hle; lia.
Qed.

(** And with the 1969 value the margin is not six but twelve. *)
Theorem the_cone_route_is_twelve_short :
  AbbottGardner1969 ->
  forall F, Uniform 3 F -> Distinct F -> ~ ContainsKSunflower 3 F ->
            length F + 12 <= 32.
Proof.
  intros Hag F HU HD Hno.
  pose proof (Hag F HU HD Hno) as Hle; lia.
Qed.
