(** * The sharp reformulation: [L = sup_b iota(b)^(1/(b-1))]

    [IotaRate.conjecture_k_3_iff_iota_exponential] makes Erdős's $1000
    case equivalent to [iota(b) <= C^b]. This file shifts the exponent by
    one and names what the shift buys.

    ** Why the shift is the right normalisation

    The Abbott–Hanson–Sauer substitution gives
    [iota(ab) >= iota(a) iota(b)^a] — verified computationally in
    [rust/tests/intersecting.rs], not formalised here — and iterating it at
    [b^k] extracts a rate of [iota(b)^(1/(b-1))] per point, not
    [iota(b)^(1/b)]. That is the quantity the 1972 paper's constant
    [10^(1/2) = 3.162...] is a value of: it is [iota(3)^(1/(3-1))].

    So the sequence to watch is [iota(b)^(1/(b-1))], and by Fekete on the
    supermultiplicative [iota] ([Product.iota_supermultiplicative]) the
    conjecture at [k = 3] is the finiteness of its supremum. **No limit is
    taken here.** What is proved is the finitistic content, and it is an
    equivalence:

    >  sunflower_conjecture_k_3   <->   exists C, forall b >= 1, iota(b) <= C^(b-1)

    Both directions are arithmetic on top of
    [IotaRate.conjecture_k_3_iff_iota_exponential]; the only non-arithmetic
    ingredient is [Product.iota_one_at_most_one], which is what makes the
    [b = 1] case [iota(1) <= C^0 = 1] true rather than merely convenient.
    The substitution is **not** needed for the equivalence — it is needed
    only to know that [1/(b-1)] is the exponent the constructions actually
    achieve, which is a statement about lower bounds and is not claimed
    here.

    ** The sharp conjecture, named

    Measured, every value exhaustive:

    >  b       1      2      3       4
    >  iota    1      3     10      27   (on nine points)
    >  rate    -   3.000  3.162   3.000

    and every construction the repository can build sits at or below
    [3.162] ([rust/tests/sharp_conjecture.rs] rebuilds each one and checks
    it). So the sharp form of the conjecture is that the sequence is
    maximised at [b = 3]:

    >  AHSOptimal  :=  forall b >= 1,  iota(b)^2 <= 10^(b-1)

    — squared so that nothing leaves the integers. Equivalently
    [iota(b) <= 10^((b-1)/2)]; equivalently Abbott–Hanson–Sauer is optimal
    and [L = sqrt(10)]. It is met with **equality** at [b = 3], and
    [the_sharp_bound_is_attained_at_three] is that equality in the kernel.

    Three things follow, and they are why this is worth naming rather than
    merely believing:

    - [sharp_settles_k3]: it implies the conjecture at [k = 3], with the
      explicit constant [c(3) = 8] ([sharp_gives_the_constant]). The
      real-valued constant the sharp bound really gives is
      [2 sqrt(10) = 6.32...]; [8] is what stays inside [nat].
    - [sharp_beats_erdos_rado_at_three]: it gives [f(3,3) <= 32] against
      Erdős–Rado's 49 — a new bound on the **first unknown sunflower
      number**, from a hypothesis about uniformity 4.
    - [refutation_threshold] and the three instances below: it is
      falsifiable by a single family, and the threshold at every
      uniformity is a number. [b = 4] needs 32 members, [b = 6] needs 317,
      [b = 9] needs exactly one more than the substitution already gives.

    Nothing here is evidence *for* the sharp conjecture beyond the four
    exhaustive values and the fact that no construction in the repository
    reaches a threshold. It is a target with a number in it, which is what
    the cap-set programme had and this one has lacked.

    Zero axioms, zero admits. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower LowerBound Conjecture F23
     Intersecting IotaRate Product.
Import ListNotations.

(** ** Two pieces of arithmetic

    Both are used to move between a bound on [N] and a bound on [N * N],
    which is the whole reason the sharp conjecture can be stated without
    leaving [nat]. *)

Lemma sq_lt_mono_inv : forall n m, n * n < m * m -> n < m.
Proof. intros n m H; nia. Qed.

Lemma IotaAtMost_mono :
  forall b N M, N <= M -> IotaAtMost b N -> IotaAtMost b M.
Proof.
  intros b N M Hle Hn H HU HD HI Hno.
  pose proof (Hn H HU HD HI Hno) as H1; lia.
Qed.

(** ** The shifted exponent

    [IotaRate.IotaExponential] is [exists C, forall b >= 1, iota(b) <= C^b].
    This is the same statement with the exponent normalised the way the
    substitution normalises it. *)

(** The per-constant predicate first. Splitting it out is not cosmetic:
    it is what a search can falsify. [IotaShiftedAt 3] is a statement
    about a specific number, and [Audit.the_shifted_bound_at_three_is_false]
    refutes it from the witnessed [iota(3) >= 10] — which is exactly the
    finitistic content of "[L] is above 3". The existential form cannot be
    refuted by any family. *)

Definition IotaShiftedAt (C : nat) : Prop :=
  forall b, 1 <= b -> IotaAtMost b (C ^ (b - 1)).

Definition IotaExponentialShifted : Prop := exists C : nat, IotaShiftedAt C.

(** The two are equivalent, and the constant moves by a square. The
    forward direction is monotonicity; the backward one is the only place
    anything beyond arithmetic is used, and what it uses is
    [Product.iota_one_at_most_one] — [iota(1) = 1] is exactly what makes
    the [b = 1] instance [iota(1) <= C^0 = 1] true. *)

Theorem iota_exponential_shifted_iff :
  IotaExponentialShifted <-> IotaExponential.
Proof.
  split.
  - intros [C HC]; exists (S C); intros b Hb; unfold IotaShiftedAt in HC.
    apply (IotaAtMost_mono b (C ^ (b - 1))); [| exact (HC b Hb)].
    transitivity (S C ^ (b - 1)).
    + apply Nat.pow_le_mono_l; lia.
    + apply Nat.pow_le_mono_r; lia.
  - intros [C HC]; exists (S C * S C); unfold IotaShiftedAt; intros b Hb.
    destruct (Nat.eq_dec b 1) as [E | Hne].
    + subst b; simpl (1 - 1); rewrite Nat.pow_0_r.
      exact iota_one_at_most_one.
    + apply (IotaAtMost_mono b (C ^ b)); [| exact (HC b Hb)].
      (* [(S C * S C)^(b-1) = S C ^ (2 * (b-1))], and [b <= 2 * (b-1)]
         from [2 <= b]. *)
      replace (S C * S C) with (S C ^ 2) by (simpl; lia).
      rewrite <- Nat.pow_mul_r.
      transitivity (S C ^ b).
      * apply Nat.pow_le_mono_l; lia.
      * apply Nat.pow_le_mono_r; lia.
Qed.

(** **The statement this file exists for.** The sunflower conjecture at
    [k = 3] is exactly the boundedness of [iota(b)^(1/(b-1))]. *)

Theorem conjecture_k_3_iff_iota_shifted :
  sunflower_conjecture_k_3 <-> IotaExponentialShifted.
Proof.
  rewrite conjecture_k_3_iff_iota_exponential.
  symmetry; exact iota_exponential_shifted_iff.
Qed.

(** ** The sharp conjecture

    [Product.IotaAtLeast b N] is "some intersecting sunflower-free
    [b]-uniform family has exactly [N] members", so quantifying over [N]
    says [iota(b)^2 <= 10^(b-1)] without naming [iota] as a function —
    which it is not here, since its values are not known. *)

Definition AHSOptimal : Prop :=
  forall b N, 1 <= b -> IotaAtLeast b N -> N * N <= 10 ^ (b - 1).

(** The workhorse: the sharp bound turns into an ordinary [IotaAtMost] at
    every [M] whose successor's square clears [10^(b-1)]. That off-by-one
    is not cosmetic — at [b = 4] the bound is [N^2 <= 1000] and the
    largest [N] it permits is 31, whose square is 961 and does *not*
    clear 1000. *)

Theorem sharp_bounds_iota :
  AHSOptimal ->
  forall b M, 1 <= b -> 10 ^ (b - 1) < S M * S M -> IotaAtMost b M.
Proof.
  intros Hs b M Hb Hlt H HU HD HI Hno.
  (* The splits are written out. [repeat split] would close the size
     clause by [eq_refl] — [split] is [constructor], and [eq] has one —
     which is exactly the brittleness [docs/testing.md] §4 forbids: the
     mutation [iotaatleast-at-least] weakens that clause to [>=] and a
     proof closing it reflexively is sensitive to the shape of
     [IotaAtLeast] rather than to its content. [lia] proves either form. *)
  assert (Hwit : IotaAtLeast b (length H)).
  { exists H.
    split; [exact HU|].
    split; [exact HD|].
    split; [exact HI|].
    split; [lia|].
    exact Hno. }
  pose proof (Hs b (length H) Hb Hwit) as Hsq.
  assert (Hlt' : length H * length H < S M * S M) by lia.
  pose proof (sq_lt_mono_inv _ _ Hlt') as Hlt2; lia.
Qed.

(** ** What it settles

    [10^(b-1) <= 16^(b-1) = (4^(b-1))^2], so the sharp bound is in
    particular a bound of the shape [iota(b) <= C^(b-1)] with [C = 4].
    Base 4 rather than base 3 because [sqrt(10) = 3.162... > 3]:
    [the_sharp_bound_gives_a_base_four_bound] in
    [rust/tests/sharp_conjecture.rs] checks that base 3 does not suffice,
    so the choice is forced rather than lazy. *)

Theorem sharp_gives_base_four : AHSOptimal -> IotaShiftedAt 4.
Proof.
  intros Hs b Hb.
  apply (sharp_bounds_iota Hs b _ Hb).
  assert (H16 : 10 ^ (b - 1) <= 16 ^ (b - 1))
    by (apply Nat.pow_le_mono_l; lia).
  assert (Hsq : 16 ^ (b - 1) = 4 ^ (b - 1) * 4 ^ (b - 1)).
  { rewrite <- Nat.pow_mul_l; f_equal. }
  nia.
Qed.

Theorem sharp_gives_iota_shifted : AHSOptimal -> IotaExponentialShifted.
Proof. intros Hs; exists 4; exact (sharp_gives_base_four Hs). Qed.

Theorem sharp_settles_k3 : AHSOptimal -> sunflower_conjecture_k_3.
Proof.
  intros Hs; apply conjecture_k_3_iff_iota_shifted.
  exact (sharp_gives_iota_shifted Hs).
Qed.

(** The constant, visible. [IotaRate.iota_bound_settles_k_3] takes
    [iota(b) <= C^b] to [c(3) = 2C]; here [C = 4], so [c(3) = 8]. The
    sharp bound's real-valued constant is [2 sqrt(10) = 6.32...] — 8 is
    the price of staying in [nat] and no attempt is made to sharpen it,
    per [docs/roadmap.md]'s standing rule. *)

Corollary sharp_gives_the_constant :
  AHSOptimal -> forall n, 1 <= n -> UpperBound n 3 (S (8 ^ n)).
Proof.
  intros Hs n Hn.
  assert (HC : forall b, 1 <= b -> IotaAtMost b (4 ^ b)).
  { intros b Hb.
    apply (IotaAtMost_mono b (4 ^ (b - 1))); [| exact (sharp_gives_base_four Hs b Hb)].
    apply Nat.pow_le_mono_r; lia. }
  pose proof (iota_bound_settles_k_3 4 HC n Hn) as Hub.
  replace (8 ^ n) with ((2 * 4) ^ n) by (f_equal; lia).
  exact Hub.
Qed.

(** ** What it would buy at the first unknown sunflower number

    [Product.iota_bound_gives_upper_bound] transfers an [iota] bound one
    uniformity down. At [b = 4] the sharp bound permits at most 31
    members, so [f(3,3) <= 32] — against Erdős–Rado's 49, and against the
    best lower bound proved here, [f(3,3) >= 21]
    ([Intersecting.lower_bound_3_3_20]).

    Read as a hardness statement, this says the sharp conjecture is not a
    small refinement: proving it would settle a value nobody knows. Read
    as a research target, it says a *single* uniformity — [iota(4)] — is
    worth a new bound on [f(3,3)]. *)

Theorem sharp_forces_iota_four_at_most_31 : AHSOptimal -> IotaAtMost 4 31.
Proof. intros Hs; apply (sharp_bounds_iota Hs 4 31); [lia | vm_compute; lia]. Qed.

Theorem sharp_beats_erdos_rado_at_three :
  AHSOptimal -> UpperBound 3 3 32 /\ ~ UpperBound 3 3 20 /\ 32 < 49.
Proof.
  intros Hs; split.
  - replace 32 with (S 31) by reflexivity.
    apply (iota_bound_gives_upper_bound 3 31); [lia|].
    exact (sharp_forces_iota_four_at_most_31 Hs).
  - split; [exact no_upper_bound_3_3_20 | lia].
Qed.

(** And at [b = 3] it pins the value exactly: the measured
    [iota(3) = 10] is witnessed ([Product.iota_three_at_least_ten]), and
    the sharp bound permits no more. So [AHSOptimal] implies
    [iota(3) = 10] outright, where the development otherwise only has
    [10 <= iota(3) <= 18] ([Audit.iota_three_between_ten_and_eighteen]). *)

Theorem sharp_forces_iota_three_exactly_ten :
  AHSOptimal -> IotaAtMost 3 10 /\ IotaAtLeast 3 10.
Proof.
  intros Hs; split.
  - apply (sharp_bounds_iota Hs 3 10); [lia | vm_compute; lia].
  - exact iota_three_at_least_ten.
Qed.

(** ** Falsification

    The point of a sharp conjecture is that one family kills it. This is
    the interface a search should aim at, and the three instances below
    are the rungs [docs/roadmap.md] §12 tabulates. *)

Theorem refutation_threshold :
  forall b N, 1 <= b -> IotaAtLeast b N -> 10 ^ (b - 1) < N * N -> ~ AHSOptimal.
Proof.
  intros b N Hb Hwit Hlt Hs.
  pose proof (Hs b N Hb Hwit) as Hle; lia.
Qed.

(** [nat] is unary, so a power of ten cannot simply be handed to
    [vm_compute]: [10 ^ 5] is a hundred thousand constructors and [10 ^ 8]
    is a hundred million, and the first version of the two proofs below
    overflowed the stack rather than failing to be true. Splitting the
    exponent keeps every *computed* term at [10 ^ 4] or below and leaves
    the multiplication of numerals to [lia], which does it over [Z]. *)

Lemma pow10_split : forall i j, 10 ^ (i + j) = 10 ^ i * 10 ^ j.
Proof. intros i j; apply Nat.pow_add_r. Qed.

Corollary iota_four_at_least_32_refutes : IotaAtLeast 4 32 -> ~ AHSOptimal.
Proof.
  intros H; apply (refutation_threshold 4 32); [lia | exact H |].
  replace (4 - 1) with 3 by lia.
  replace (10 ^ 3) with 1000 by (vm_compute; reflexivity).
  lia.
Qed.

Corollary iota_six_at_least_317_refutes : IotaAtLeast 6 317 -> ~ AHSOptimal.
Proof.
  intros H; apply (refutation_threshold 6 317); [lia | exact H |].
  replace (6 - 1) with (2 + 3) by lia.
  rewrite pow10_split.
  replace (10 ^ 2) with 100 by (vm_compute; reflexivity).
  replace (10 ^ 3) with 1000 by (vm_compute; reflexivity).
  lia.
Qed.

(** ** The odd tower, where the substitution lands exactly on the bound

    At [b = 2j+1] the sharp bound reads [iota(b)^2 <= 10^(2j)], i.e.
    [iota(b) <= 10^j] — a round number, and exactly what the substitution
    delivers when it is iterated on [iota(3) = 10]. So at every odd
    uniformity the record falls at **one more set**, and the [b = 9] row
    of [docs/roadmap.md] §12 is the instance [j = 4]: 10000 members built,
    10001 needed.

    Stated for all [j] rather than at [j = 4] because the [j = 4] literals
    are past the point where [nat] numerals are ordinary terms — Coq
    interprets [10001] as an application of [Init.Nat.of_num_uint], which
    [lia] cannot see through. Carrying [10 ^ j] symbolically avoids the
    question entirely, and says more. *)

Theorem the_tower_misses_by_exactly_one :
  forall j, IotaAtLeast (2 * j + 1) (S (10 ^ j)) -> ~ AHSOptimal.
Proof.
  intros j H.
  apply (refutation_threshold (2 * j + 1) (S (10 ^ j))); [lia | exact H |].
  replace (2 * j + 1 - 1) with (j + j) by lia.
  rewrite pow10_split.
  generalize (10 ^ j); intros t; nia.
Qed.

Corollary iota_five_at_least_101_refutes : IotaAtLeast 5 101 -> ~ AHSOptimal.
Proof. exact (the_tower_misses_by_exactly_one 2). Qed.

Corollary iota_seven_at_least_1001_refutes : IotaAtLeast 7 1001 -> ~ AHSOptimal.
Proof. exact (the_tower_misses_by_exactly_one 3). Qed.

Corollary iota_nine_at_least_10001_refutes :
  IotaAtLeast 9 10001 -> ~ AHSOptimal.
Proof. exact (the_tower_misses_by_exactly_one 4). Qed.

(** ** Where the bound is attained, and where it is slack

    The equality at [b = 3] is the content of Abbott–Hanson–Sauer, and it
    is what fixes the constant at [sqrt(10)]: one more member there would
    refute the sharp conjecture outright. Everything else the development
    witnesses is strictly inside it.

    Note which way the [b = 3] row cuts. [iota(3) = 10] is exhaustive, so
    [iota_three_at_least_eleven] is *false*; what the theorem records is
    that the sharp bound has no slack at all there, so the whole
    conjecture rests on that one exhaustive computation being right. *)

Theorem the_sharp_bound_is_attained_at_three :
  10 * 10 = 10 ^ (3 - 1) /\ (IotaAtLeast 3 11 -> ~ AHSOptimal).
Proof.
  split; [vm_compute; reflexivity|].
  intros H; apply (refutation_threshold 3 11); [lia | exact H | vm_compute; lia].
Qed.

Theorem the_witnessed_values_are_inside_the_sharp_bound :
  3 * 3 <= 10 ^ (2 - 1) /\ 10 * 10 <= 10 ^ (3 - 1) /\ 27 * 27 <= 10 ^ (4 - 1).
Proof. repeat split; vm_compute; lia. Qed.
