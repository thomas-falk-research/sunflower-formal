(** * Counting.v -- Stage A of the spread lemma: the counting layer.

    `docs/roadmap.md` §1 stages the discharge of [ALWZ.Rao20_lemma2]
    through the *counting* proof — [ALWZ20] §2 as streamlined by
    Park–Pham, written out in Lovett's PCMI notes §3 (pp. 11–15) — and
    §1's Stage A is the arithmetic that proof needs and nothing else:

    - fixed-size subset enumeration, with its count;
    - a counting operator with "an injection implies an inequality" and
      additivity over disjoint predicates — stated at an *arbitrary*
      type, not at [list nat] as §1's sketch has it, because Claim 3.4
      counts **pairs** [(S,V)]; see [pairs] and [pairs_length] below,
      which are the whole of the Stage A / Stage B interface;
    - [C(n,j) <= 2^n];
    - **one binomial estimate**, and it is the only place in the whole
      proof where a rational would otherwise appear.

    Everything here is elementary and none of it mentions sunflowers,
    spreadness or families. That is deliberate: Stage A is the layer
    Stage B's encoding is *counted with*, and keeping it free of the
    problem is what makes it independently falsifiable —
    [rust/tests/counting.rs] checks every claim below against an
    independent implementation.

    ** The one estimate, and why it is stated with cleared denominators

    Lovett's Claim 3.4 needs, for a random subset [V] of [U] of fixed
    size [qN],

    <<
      C(N, qN + m)  <=  q^(-m) * C(N, qN).
    >>

    With [q = c/d] that is [c^m * C(N, j+m) <= d^m * C(N, j)] for
    [c*N <= d*j], which stays in [nat]. It comes from one step,
    [binom_step], iterated: the single-step ratio is
    [C(N,j+1)/C(N,j) = (N-j)/(j+1)], and [c*N <= d*j] makes that at most
    [d/c]. The step is proved from the absorption identity
    [binom_absorb], which is the only fiddly induction in the file.

    ** What Stage A does *not* do

    No probability, no measure, no limit. Lovett p. 11 derives the
    product-measure statement from the fixed-size one *"[t]ake now `U'`
    of growing size; the limiting distribution of `W` converges to
    `Bin(U,p)`"*, and §1's staging decision is to start at the fixed-size
    statement precisely so that limit never has to be formalised. So the
    layer here counts the size-[j] *layer* of the powerset, not the
    powerset.
*)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower Pigeonhole Spread.
Import ListNotations.

Set Implicit Arguments.

(** ** Binomial coefficients

    Pascal's recursion, in the orientation that makes
    [length (subsets_of_size j l)] a one-line induction: [binom n j] is
    the number of [j]-element sublists of an [n]-element list. *)

Fixpoint binom (n j : nat) : nat :=
  match n, j with
  | _, 0 => 1
  | 0, S _ => 0
  | S n', S j' => binom n' j' + binom n' (S j')
  end.

Lemma binom_zero : forall n, binom n 0 = 1.
Proof. intros [|n]; reflexivity. Qed.

Lemma binom_succ : forall n j, binom (S n) (S j) = binom n j + binom n (S j).
Proof. reflexivity. Qed.

Lemma binom_zero_above : forall n j, n < j -> binom n j = 0.
Proof.
  induction n as [|n IH]; intros j Hlt.
  - destruct j; [lia | reflexivity].
  - destruct j as [|j']; [lia|].
    rewrite binom_succ, (IH j' ltac:(lia)), (IH (S j') ltac:(lia)); reflexivity.
Qed.

Lemma binom_diag : forall n, binom n n = 1.
Proof.
  induction n as [|n IH]; [reflexivity|].
  rewrite binom_succ, IH, (@binom_zero_above n (S n) ltac:(lia)); lia.
Qed.

Lemma binom_one : forall n, binom n 1 = n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  rewrite binom_succ, binom_zero, IH; lia.
Qed.

(** *** The absorption identity

    [C(N, j+1) * (j+1) = C(N, j) * (N - j)]. Truncated subtraction is
    harmless: above the diagonal both sides are zero. This is the only
    place the file works for its arithmetic. *)

Lemma binom_absorb : forall N j, binom N (S j) * S j = binom N j * (N - j).
Proof.
  induction N as [|n IH]; intros j.
  - destruct j; simpl; lia.
  - destruct j as [|j'].
    + rewrite binom_succ, binom_zero, binom_one, binom_zero; lia.
    + rewrite (binom_succ n (S j')), (binom_succ n j').
      replace (S n - S j') with (n - j') by lia.
      destruct (le_lt_dec (S j') n) as [Hle | Hgt].
      * pose proof (IH j') as H1.
        pose proof (IH (S j')) as H2.
        assert (E : n - j' = S (n - S j')) by lia.
        rewrite E in H1 |- *.
        (* both sides are [binom n (S j')] times the same number *)
        nia.
      * rewrite (@binom_zero_above n (S j') ltac:(lia)).
        rewrite (@binom_zero_above n (S (S j')) ltac:(lia)).
        lia.
Qed.

Lemma one_le_two_pow : forall n, 1 <= 2 ^ n.
Proof. induction n as [|n IH]; simpl; lia. Qed.

Lemma binom_le_two_pow : forall n j, binom n j <= 2 ^ n.
Proof.
  induction n as [|n IH]; intros j.
  - destruct j; simpl; lia.
  - destruct j as [|j'].
    + rewrite binom_zero. simpl. pose proof (one_le_two_pow n); lia.
    + rewrite binom_succ.
      pose proof (IH j'); pose proof (IH (S j')).
      simpl (2 ^ S n); lia.
Qed.

(** [binom] is monotone in its first argument — Pascal's recursion adds
    a nonnegative term. Needed to bound `C(|S'|, m)` by `C(n, m)` when
    `|S'| <= n`, which is step 3 of Claim 3.4. *)

Lemma binom_succ_l : forall n j, binom n j <= binom (S n) j.
Proof.
  intros n j; destruct j as [|j'];
    [rewrite !binom_zero; lia | rewrite binom_succ; lia].
Qed.

Lemma binom_mono_l : forall n n' j, n <= n' -> binom n j <= binom n' j.
Proof.
  intros n n' j H; induction H as [|n'' Hle IH]; [lia|].
  eapply Nat.le_trans; [exact IH | apply binom_succ_l].
Qed.

(** ** The estimate

    One step first. Lovett's use has [j = qN] with [q = c/d], i.e.
    [c*N = d*j]; but the hypothesis that actually makes the argument run
    is one notch weaker, and the file states the weaker one because
    stating a non-minimal hypothesis leaves a gap for a later session to
    "discover". The single-step ratio is [C(N,j+1)/C(N,j) = (N-j)/(j+1)],
    and all the proof needs is [c*(N-j) <= d*(j+1)], for which
    [c*N <= d*(j+1)] is enough.

    **And [S j] is exactly the boundary.** Replacing it by [j+2] makes
    the statement false — [binom_ratio_needs_the_successor] below is the
    witness, and [rust/tests/counting.rs] finds 102 of them in a small
    box. So the hypothesis here is minimal for this argument. *)

Lemma binom_step :
  forall N j c d, c * N <= d * S j -> c * binom N (S j) <= d * binom N j.
Proof.
  intros N j c d Hcd.
  (* multiply through by [S j] and use absorption; [S j > 0] so the
     factor cancels *)
  apply (proj2 (Nat.mul_le_mono_pos_r (c * binom N (S j)) (d * binom N j)
                                      (S j) ltac:(lia))).
  assert (E : c * binom N (S j) * S j = c * (binom N (S j) * S j)) by ring.
  rewrite E, binom_absorb.
  (* goal: c * (binom N j * (N - j)) <= d * binom N j * S j *)
  assert (Hfac : c * (N - j) <= d * S j) by nia.
  assert (E2 : c * (binom N j * (N - j)) = binom N j * (c * (N - j))) by ring.
  assert (E3 : d * binom N j * S j = binom N j * (d * S j)) by ring.
  rewrite E2, E3.
  apply Nat.mul_le_mono_l; exact Hfac.
Qed.

(** [C(N, j+m) * c^m <= C(N, j) * d^m] -- Lovett Claim 3.4's binomial
    estimate, with [q = c/d] and denominators cleared. *)

Theorem binom_ratio :
  forall N j c d m,
    c * N <= d * S j ->
    c ^ m * binom N (j + m) <= d ^ m * binom N j.
Proof.
  intros N j c d m Hcd.
  induction m as [|m IH].
  - rewrite Nat.add_0_r; simpl; lia.
  - assert (Ej : j + S m = S (j + m)) by lia.
    rewrite Ej.
    assert (Hstep : c * binom N (S (j + m)) <= d * binom N (j + m))
      by (apply binom_step; nia).
    assert (E1 : c ^ S m * binom N (S (j + m))
                 = c ^ m * (c * binom N (S (j + m)))) by (simpl; ring).
    rewrite E1.
    eapply Nat.le_trans.
    + apply Nat.mul_le_mono_l; exact Hstep.
    + assert (E2 : c ^ m * (d * binom N (j + m))
                   = d * (c ^ m * binom N (j + m))) by ring.
      rewrite E2.
      assert (E3 : d ^ S m * binom N j = d * (d ^ m * binom N j))
        by (simpl; ring).
      rewrite E3.
      apply Nat.mul_le_mono_l; exact IH.
Qed.

(** Lovett's shape, [j = qN] with [q = c/d]: the threshold case, which is
    what Stage B will hand in. *)

Corollary binom_ratio_at_threshold :
  forall N j c d m,
    c * N <= d * j ->
    c ^ m * binom N (j + m) <= d ^ m * binom N j.
Proof. intros N j c d m H; apply binom_ratio; lia. Qed.

(** The hypothesis is minimal for this argument: one notch further and
    the estimate is false. [N = 1], [j = 0], [c = 2], [d = 1], [m = 1]
    satisfies [c*N <= d*(j+2)] and refutes the conclusion, since
    [C(1,1) = 1] against [C(1,0) = 1] with a factor of 2 in front. *)

Example binom_ratio_needs_the_successor :
  2 * 1 <= 1 * (0 + 2) /\ ~ (2 ^ 1 * binom 1 (0 + 1) <= 1 ^ 1 * binom 1 0).
Proof. split; simpl; lia. Qed.

(** ** The size-[j] layer of the powerset

    [Spread.subsets] enumerates every sublist; the layer is the filter by
    length, which is the cheap definition §1 asks for and gives
    membership for free. *)

Definition subsets_of_size (j : nat) (l : list nat) : list (list nat) :=
  filter (fun A => Nat.eqb (length A) j) (subsets l).

Lemma in_subsets_of_size :
  forall j l A,
    In A (subsets_of_size j l) <-> In A (subsets l) /\ length A = j.
Proof.
  intros j l A; unfold subsets_of_size; rewrite filter_In; split.
  - intros [H1 H2]; split; [exact H1 | apply Nat.eqb_eq; exact H2].
  - intros [H1 H2]; split; [exact H1 | apply Nat.eqb_eq; exact H2].
Qed.

Lemma subsets_of_size_incl :
  forall j l A, In A (subsets_of_size j l) -> Subset A l /\ length A = j.
Proof.
  intros j l A H; apply in_subsets_of_size in H as [H1 H2].
  split; [apply subsets_incl; exact H1 | exact H2].
Qed.

Lemma length_filter_map_cons :
  forall (p : list nat -> bool) (x : nat) (L : list (list nat)),
    length (filter p (map (cons x) L))
    = length (filter (fun A => p (x :: A)) L).
Proof.
  intros p x L; induction L as [|A L IH]; simpl; [reflexivity|].
  destruct (p (x :: A)); simpl; lia.
Qed.

Lemma length_subsets : forall l, length (subsets l) = 2 ^ length l.
Proof.
  induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite app_length, map_length, IH; lia.
Qed.

(** The count of the layer is the binomial coefficient. Note this needs
    no [NoDup]: [subsets] enumerates by *position*, so it is the number of
    length-[j] sublists of a list of length [n] either way. *)

Theorem length_subsets_of_size :
  forall l j, length (subsets_of_size j l) = binom (length l) j.
Proof.
  induction l as [|x l IH]; intros j.
  - destruct j as [|j']; reflexivity.
  - unfold subsets_of_size in *; simpl (subsets (x :: l)).
    rewrite filter_app, app_length, length_filter_map_cons.
    destruct j as [|j'].
    + (* no sublist of the form [x :: A] has length 0 *)
      simpl (length (x :: l)); rewrite binom_zero.
      assert (E : forall A : list nat,
                 Nat.eqb (length (x :: A)) 0 = false) by reflexivity.
      erewrite filter_ext by (intro A; apply E).
      assert (Enil : forall (L : list (list nat)),
                 filter (fun _ => false) L = []).
      { induction L; simpl; [reflexivity | assumption]. }
      rewrite Enil; simpl.
      specialize (IH 0); rewrite binom_zero in IH; exact IH.
    + simpl (length (x :: l)); rewrite binom_succ.
      assert (E : forall A : list nat,
                 Nat.eqb (length (x :: A)) (S j') = Nat.eqb (length A) j')
        by reflexivity.
      erewrite filter_ext by (intro A; apply E).
      rewrite (IH j'), (IH (S j')); reflexivity.
Qed.

(** *** The layer has no repeats

    Needed wherever the layer is the *domain* of an injection: a repeated
    element would make [count] over-count. [Spread.subsets_NoDup] says
    each enumerated sublist is [NoDup]; this says the enumeration is. *)

Lemma NoDup_app_disjoint :
  forall {T : Type} (A B : list T),
    NoDup A -> NoDup B -> (forall x, In x A -> ~ In x B) -> NoDup (A ++ B).
Proof.
  intros T A; induction A as [|a A IH]; intros B HA HB Hdisj; simpl; [exact HB|].
  inversion HA as [|? ? Hna HA']; subst.
  constructor.
  - intro Hin; apply in_app_or in Hin as [Hin | Hin].
    + apply Hna; exact Hin.
    + apply (Hdisj a (or_introl eq_refl)); exact Hin.
  - apply IH; [exact HA' | exact HB |].
    intros x Hx; apply Hdisj; right; exact Hx.
Qed.

Lemma subsets_NoDup_enum : forall l, NoDup l -> NoDup (subsets l).
Proof.
  induction l as [|x l IH]; intros Hnd; simpl.
  - constructor; [intros [] | constructor].
  - inversion Hnd as [|? ? Hxni Hnd']; subst.
    apply NoDup_app_disjoint.
    + (* [cons x] is injective *)
      apply (@NoDup_map_inv _ _ (fun A => match A with [] => [] | _ :: t => t end)).
      rewrite map_map; simpl.
      rewrite map_id; apply IH; exact Hnd'.
    + apply IH; exact Hnd'.
    + intros A HA HB.
      apply in_map_iff in HA as [A0 [E _]]; subst A.
      apply Hxni; apply (@subsets_incl l (x :: A0) HB); left; reflexivity.
Qed.

Lemma subsets_of_size_NoDup_enum :
  forall j l, NoDup l -> NoDup (subsets_of_size j l).
Proof.
  intros j l Hnd; unfold subsets_of_size.
  apply NoDup_filter, subsets_NoDup_enum; exact Hnd.
Qed.

(** ** Counting

    [count p L] is how many entries of [L] satisfy [p]. The two facts
    Stage B needs are that an injection between the counted parts gives
    an inequality, and that disjoint predicates add. *)

Definition count {A : Type} (p : A -> bool) (L : list A) : nat :=
  length (filter p L).

Lemma count_le_length : forall {A : Type} (p : A -> bool) (L : list A),
    count p L <= length L.
Proof. intros A p L; apply length_filter_le. Qed.

Lemma count_partition :
  forall {A : Type} (p : A -> bool) (L : list A),
    count p L + count (fun x => negb (p x)) L = length L.
Proof.
  intros A p L; unfold count; symmetry; apply length_filter_partition.
Qed.

Lemma count_disjoint_add :
  forall {A : Type} (p q : A -> bool) (L : list A),
    (forall x, p x = true -> q x = false) ->
    count p L + count q L = count (fun x => orb (p x) (q x)) L.
Proof.
  intros A p q L Hdisj; unfold count.
  induction L as [|x L IH]; simpl; [reflexivity|].
  destruct (p x) eqn:Ep.
  - rewrite (Hdisj x Ep); simpl; lia.
  - destruct (q x); simpl; lia.
Qed.

Lemma count_mono :
  forall {A : Type} (p q : A -> bool) (L : list A),
    (forall x, p x = true -> q x = true) -> count p L <= count q L.
Proof.
  intros A p q L Himp; unfold count.
  induction L as [|x L IH]; simpl; [lia|].
  destruct (p x) eqn:Ep.
  - rewrite (Himp x Ep); simpl; lia.
  - destruct (q x); simpl; lia.
Qed.

(** *** An injection implies an inequality

    This is the shape Claim 3.4's encoding is used in: the good pairs
    inject into an explicit product, so there are at most as many of
    them. Only the *domain* needs [NoDup] — the codomain is a list that
    may repeat, and the bound is still valid. *)

(** [NoDup_map_inj] is not in Coq 8.18's [List]; only the converse
    [NoDup_map_inv] is. Injectivity is needed only on the list itself. *)

Lemma NoDup_map_inj :
  forall {A B : Type} (f : A -> B) (l : list A),
    (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
    NoDup l -> NoDup (map f l).
Proof.
  intros A B f l; induction l as [|a l IH]; intros Hinj Hnd; simpl; [constructor|].
  inversion Hnd as [|? ? Hna Hnd']; subst.
  constructor.
  - intro Hin; apply in_map_iff in Hin as [b [E Hb]].
    apply Hna.
    rewrite (Hinj a b (or_introl eq_refl) (or_intror Hb) (eq_sym E)); exact Hb.
  - apply IH; [intros x y Hx Hy; apply Hinj; right; assumption | exact Hnd'].
Qed.

Theorem count_inj_le :
  forall {A B : Type} (p : A -> bool) (q : B -> bool) (f : A -> B)
         (L : list A) (M : list B),
    NoDup L ->
    (forall x, In x L -> p x = true -> In (f x) M /\ q (f x) = true) ->
    (forall x y, In x L -> In y L -> p x = true -> p y = true ->
                 f x = f y -> x = y) ->
    count p L <= count q M.
Proof.
  intros A B p q f L M HL Hmap Hinj; unfold count.
  assert (HLp : NoDup (filter p L)) by (apply NoDup_filter; exact HL).
  assert (Hincl : incl (map f (filter p L)) (filter q M)).
  { intros y Hy; apply in_map_iff in Hy as [x [E Hx]]; subst y.
    apply filter_In in Hx as [HxL Hxp].
    destruct (Hmap x HxL Hxp) as [HfM Hfq].
    apply filter_In; split; assumption. }
  assert (Hnd : NoDup (map f (filter p L))).
  { apply (@NoDup_map_inj A B f (filter p L)); [| exact HLp].
    intros x y Hx Hy E.
    apply filter_In in Hx as [HxL Hxp]; apply filter_In in Hy as [HyL Hyp].
    apply (Hinj x y HxL HyL Hxp Hyp E). }
  pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
  rewrite map_length in Hlen; exact Hlen.
Qed.

(** *** The sample space Claim 3.4 divides by

    The counting layer is polymorphic, and that is not decoration: Lovett's
    Claim 3.4 counts **pairs** [(S, V)] — a member of the family and a
    sampled subset of fixed size — so a [count] typed at [list nat] would
    not have served Stage B at all. The displayed ratio there is

    <<
      Pr[ |M(S,V)| >= n/2 ]  =  |B| / ( |F| * C(N, qN) )
    >>

    and the denominator is exactly the size of the pair enumeration
    below. This is the Stage A / Stage B interface. *)

Definition pairs (F : Family) (j : nat) (l : list nat)
  : list (list nat * list nat) := list_prod F (subsets_of_size j l).

Theorem pairs_length :
  forall F j l, length (pairs F j l) = length F * binom (length l) j.
Proof.
  intros F j l; unfold pairs.
  rewrite prod_length, length_subsets_of_size; reflexivity.
Qed.

(** And the shape a bound on [|B|] takes: any predicate on pairs counts
    at most the whole sample space. *)

Corollary count_pairs_le :
  forall (p : list nat * list nat -> bool) F j l,
    count p (pairs F j l) <= length F * binom (length l) j.
Proof.
  intros p F j l.
  eapply Nat.le_trans; [apply count_le_length | rewrite pairs_length; lia].
Qed.

(** ** The layer count, as Stage B will call it

    Two corollaries in the exact shape §1's Claim 3.4 needs: the size of
    the sample space is [C(N, j)], and the estimate transported onto it. *)

Corollary layer_count_le_two_pow :
  forall j l, length (subsets_of_size j l) <= 2 ^ length l.
Proof.
  intros j l; rewrite length_subsets_of_size; apply binom_le_two_pow.
Qed.

Corollary layer_ratio :
  forall (l : list nat) (j c d m : nat),
    c * length l <= d * j ->
    c ^ m * length (subsets_of_size (j + m) l)
    <= d ^ m * length (subsets_of_size j l).
Proof.
  intros l j c d m Hcd.
  rewrite !length_subsets_of_size.
  apply binom_ratio_at_threshold; exact Hcd.
Qed.

(** ** Differential examples

    The recursion and the enumeration are independent definitions of the
    same number, so agreeing is a check on both. [rust/tests/counting.rs]
    runs the same comparison over a range; these are the instances the
    kernel carries. *)

Example binom_row_six :
  (binom 6 0, binom 6 1, binom 6 2, binom 6 3, binom 6 4, binom 6 5,
   binom 6 6, binom 6 7) = (1, 6, 15, 20, 15, 6, 1, 0).
Proof. reflexivity. Qed.

Example layer_agrees_with_binom :
  length (subsets_of_size 3 [0;1;2;3;4;5]) = 20 /\ binom 6 3 = 20.
Proof. split; reflexivity. Qed.

Example powerset_is_two_pow : length (subsets [0;1;2;3]) = 2 ^ 4.
Proof. reflexivity. Qed.

(** The estimate at a concrete point: [q = 1/4], [N = 8], [j = 2],
    [m = 3]. The hypothesis is [1*8 <= 4*2], and the conclusion
    [binom 8 5 = 56] against [4^3 * binom 8 2 = 64*28 = 1792]. *)

Example ratio_at_a_quarter : 1 ^ 3 * binom 8 (2 + 3) <= 4 ^ 3 * binom 8 2.
Proof. apply binom_ratio; lia. Qed.

(** And the absorption identity where truncated subtraction bites: above
    the diagonal both sides are zero rather than the identity failing. *)

Example absorb_above_the_diagonal : binom 4 6 * 6 = binom 4 5 * (4 - 5).
Proof. reflexivity. Qed.

(** ** Fibred counting

    [count_inj_le] bounds a set by an injection into a *flat* list. Claim
    3.4's count is not flat: the encoding sends `(S,V)` to `(Z, M)`
    together with `S \ M`, and the range of that last component is the
    link of `M` — it *depends on the first component*. So the bound is

    <<
      |B|  <=  #{(Z,M)}  *  max_M |link M F|
    >>

    and the max is uniform only because the spread hypothesis is uniform.
    That shape is what this section provides. It was measured before it
    was written: [rust/tests/fragment_count.rs] checks that every fibre
    of `(S,V) |-> (Z,M)` has at most `deg M F` elements, over every
    family of at most three subsets of a four-element universe. *)

Definition dep_pairs {B C : Type} (Base : list B) (fib : B -> list C)
  : list (B * C) :=
  flat_map (fun b => map (fun c => (b, c)) (fib b)) Base.

Lemma in_dep_pairs :
  forall {B C : Type} (Base : list B) (fib : B -> list C) (b : B) (c : C),
    In (b, c) (dep_pairs Base fib) <-> In b Base /\ In c (fib b).
Proof.
  intros B C Base fib b c; unfold dep_pairs; split.
  - intros H; apply in_flat_map in H as [b' [Hb' Hin]].
    apply in_map_iff in Hin as [c' [E Hc']].
    inversion E; subst; split; assumption.
  - intros [Hb Hc]; apply in_flat_map; exists b; split; [exact Hb|].
    apply in_map_iff; exists c; split; [reflexivity | exact Hc].
Qed.

Lemma dep_pairs_length_le :
  forall {B C : Type} (Base : list B) (fib : B -> list C) (K : nat),
    (forall b, In b Base -> length (fib b) <= K) ->
    length (dep_pairs Base fib) <= length Base * K.
Proof.
  intros B C Base fib K; unfold dep_pairs.
  induction Base as [|b Base IH]; intros Hle; simpl; [lia|].
  rewrite app_length, map_length.
  assert (H1 : length (fib b) <= K) by (apply Hle; left; reflexivity).
  assert (H2 : length (flat_map (fun b0 => map (fun c => (b0, c)) (fib b0)) Base)
               <= length Base * K)
    by (apply IH; intros b0 Hb0; apply Hle; right; exact Hb0).
  lia.
Qed.

(** **The fibred bound.** [g] is the first coordinate, [h] the second;
    the pair is injective, [h x] lands in the fibre over [g x], and every
    fibre is capped by [K]. Only the domain needs [NoDup]. *)

Theorem count_fibred_le :
  forall {A B C : Type} (g : A -> B) (h : A -> C)
         (L : list A) (Base : list B) (fib : B -> list C) (K : nat),
    NoDup L ->
    (forall x, In x L -> In (g x) Base) ->
    (forall x, In x L -> In (h x) (fib (g x))) ->
    (forall x y, In x L -> In y L -> g x = g y -> h x = h y -> x = y) ->
    (forall b, In b Base -> length (fib b) <= K) ->
    length L <= length Base * K.
Proof.
  intros A B C g h L Base fib K HL Hg Hh Hinj Hfib.
  set (e := fun x : A => (g x, h x)).
  assert (Hincl : incl (map e L) (dep_pairs Base fib)).
  { intros p Hp; apply in_map_iff in Hp as [x [E Hx]]; subst p; unfold e.
    apply in_dep_pairs; split; [apply Hg; exact Hx | apply Hh; exact Hx]. }
  assert (Hnd : NoDup (map e L)).
  { apply (@NoDup_map_inj A (B * C) e L); [| exact HL].
    intros x y Hx Hy E; unfold e in E.
    inversion E as [[E1 E2]]; apply (Hinj x y Hx Hy E1 E2). }
  pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
  rewrite map_length in Hlen.
  eapply Nat.le_trans; [exact Hlen | apply dep_pairs_length_le; exact Hfib].
Qed.

(** ** The geometric sum

    Claim 3.4 ends by summing the per-[m] bound over [n/2 <= m <= n]:

    >  `Pr[...] <= sum_{m=n/2}^{n} 2^n (kq)^{-m} <= sum_{m=n/2}^{n}
    >  (4/kq)^m`, *"Taking `k = cq^{-1}` for large enough `c`, this is at
    >  most `100^{-n}`."*

    A decreasing geometric series is dominated by its first term, and in
    [nat] the clean statement of that is: if `2a <= b` then
    `sum_{s=0}^{i} a^s b^{i-s} <= 2 b^i`. The hypothesis is **minimal for
    the constant 2** — at `a = b = 1` the sum is `i+1`, unbounded — and
    `2a <= b+1` already fails there, which
    [rust/tests/counting.rs] pins. *)

Fixpoint geom (a b i : nat) : nat :=
  match i with
  | 0 => 1
  | S i' => b ^ (S i') + a * geom a b i'
  end.

Lemma geom_le : forall a b i, 2 * a <= b -> geom a b i <= 2 * b ^ i.
Proof.
  intros a b i Hab; induction i as [|i IH]; simpl; [lia|].
  assert (Hstep : a * geom a b i <= a * (2 * b ^ i))
    by (apply Nat.mul_le_mono_l; exact IH).
  assert (Hpow : b * b ^ i = b ^ i * b) by ring.
  nia.
Qed.

(** [sum_from x t i] is `x t + x (t+1) + ... + x (t+i)`, peeling from the
    front, which is the direction the induction below needs. *)

Fixpoint sum_from (x : nat -> nat) (t i : nat) : nat :=
  match i with
  | 0 => x t
  | S i' => x t + sum_from x (S t) i'
  end.

(** **The assembly.** Per-term bounds `b^m * x m <= a^m * C` on a range,
    with `2a <= b`, give a bound on the whole sum that is only twice the
    first term's. This is Claim 3.4's last step, with no denominators. *)

Theorem geom_assemble :
  forall (x : nat -> nat) (a b C : nat),
    2 * a <= b -> 1 <= b ->
    forall i t,
      (forall m, t <= m -> m <= t + i -> b ^ m * x m <= a ^ m * C) ->
      b ^ t * sum_from x t i <= 2 * a ^ t * C.
Proof.
  intros x a b C Hab Hb1 i.
  induction i as [|i IH]; intros t Hterm; simpl sum_from.
  - assert (H := Hterm t (Nat.le_refl t) ltac:(lia)); lia.
  - (* multiply the goal by [b], then cancel it *)
    apply (proj2 (Nat.mul_le_mono_pos_l
                    (b ^ t * sum_from x t (S i)) (2 * a ^ t * C) b ltac:(lia))).
    simpl sum_from.
    assert (Hhead : b ^ t * x t <= a ^ t * C)
      by (apply Hterm; lia).
    assert (Htail : b ^ (S t) * sum_from x (S t) i <= 2 * a ^ (S t) * C).
    { apply IH; intros m Hm1 Hm2; apply Hterm; lia. }
    assert (Ep : b ^ S t = b * b ^ t) by reflexivity.
    assert (Ea : a ^ S t = a * a ^ t) by reflexivity.
    rewrite Ep, Ea in Htail.
    (* b*(b^t*(x t + Sum)) = b*(b^t*x t) + (b*b^t)*Sum
                          <= b*(a^t*C)  + 2*a*a^t*C
                          <= b*a^t*C    + b*a^t*C    = b*(2*a^t*C) *)
    assert (Hexp : b * (b ^ t * (x t + sum_from x (S t) i))
                   = b * (b ^ t * x t) + b * b ^ t * sum_from x (S t) i)
      by ring.
    rewrite Hexp.
    assert (H1 : b * (b ^ t * x t) <= b * (a ^ t * C))
      by (apply Nat.mul_le_mono_l; exact Hhead).
    assert (H2 : 2 * (a * a ^ t) * C <= b * a ^ t * C) by nia.
    nia.
Qed.

(** ** Canonicalisation

    `docs/reading.md` rule 26, and `docs/roadmap.md` §31.9. A list carries
    order that a set does not, and [Spread.subsets] enumerates *ordered
    sublists*: so a set built by concatenation — `V ++ M`, say — is not in
    [subsets U] however small its elements, and carries no binomial count.

    One function fixes it, and it belongs here rather than at each point
    of use, because the alternative is paying for it three times:

    <<
      norm U A  =  filter (fun x => memb x A) U
    >>

    the sublist of [U] with the elements of [A]. It lands in [subsets U]
    by [Spread.filter_in_subsets], depends only on the *membership* of
    [A], has the same length as [A] when [A ⊆ U] and both are [NoDup],
    and is the identity on lists that are already ordered sublists. *)

Lemma memb_iff_eq : forall x A B, (In x A <-> In x B) -> memb x A = memb x B.
Proof.
  intros x A B H; destruct (memb x A) eqn:EA.
  - symmetry; apply memb_true_iff, H, memb_true_iff; exact EA.
  - symmetry; apply memb_false_iff; intro Hc.
    apply (proj1 (memb_false_iff x A) EA), H; exact Hc.
Qed.

Definition norm (U A : list nat) : list nat := filter (fun x => memb x A) U.

Lemma in_norm_iff : forall U A x, In x (norm U A) <-> In x U /\ In x A.
Proof.
  intros U A x; unfold norm; rewrite filter_In; split.
  - intros [H1 H2]; split; [exact H1 | apply memb_true_iff; exact H2].
  - intros [H1 H2]; split; [exact H1 | apply memb_true_iff; exact H2].
Qed.

Lemma norm_in_subsets : forall U A, In (norm U A) (subsets U).
Proof. intros U A; unfold norm; apply filter_in_subsets. Qed.

Lemma norm_NoDup : forall U A, NoDup U -> NoDup (norm U A).
Proof. intros U A H; unfold norm; apply NoDup_filter; exact H. Qed.

Lemma norm_SetEq : forall U A, Subset A U -> SetEq (norm U A) A.
Proof.
  intros U A Hsub; split; intros x Hx.
  - apply in_norm_iff in Hx as [_ H]; exact H.
  - apply in_norm_iff; split; [apply Hsub; exact Hx | exact Hx].
Qed.

Lemma memb_norm : forall U A x, Subset A U -> memb x (norm U A) = memb x A.
Proof.
  intros U A x Hsub; apply memb_iff_eq; split.
  - intros H; apply in_norm_iff in H as [_ H]; exact H.
  - intros H; apply in_norm_iff; split; [apply Hsub; exact H | exact H].
Qed.

Lemma norm_length :
  forall U A, NoDup U -> NoDup A -> Subset A U -> length (norm U A) = length A.
Proof.
  intros U A HU HA Hsub.
  destruct (@norm_SetEq U A Hsub) as [H1 H2].
  assert (L1 : length (norm U A) <= length A)
    by (apply NoDup_incl_length; [apply (@norm_NoDup U A HU) | exact H1]).
  assert (L2 : length A <= length (norm U A))
    by (apply NoDup_incl_length; [exact HA | exact H2]).
  lia.
Qed.

(** [setminus] reads its second argument only through membership, so
    normalising it changes nothing. *)

Lemma setminus_norm_r :
  forall X U A, Subset A U -> setminus X (norm U A) = setminus X A.
Proof.
  intros X U A Hsub; unfold setminus.
  apply filter_ext_eq; intros x; f_equal; apply memb_norm; exact Hsub.
Qed.

(** [norm] is the identity on lists that are already ordered sublists —
    which is what makes the decode of Claim 3.4 survive canonicalisation. *)

Lemma norm_idem : forall U V, NoDup U -> In V (subsets U) -> norm U V = V.
Proof.
  unfold norm; induction U as [|u U IH]; intros V Hnd HV; simpl in HV.
  - destruct HV as [E | []]; subst V; reflexivity.
  - inversion Hnd as [|? ? Hu Hnd']; subst.
    apply in_app_or in HV as [HV | HV].
    + apply in_map_iff in HV as [V' [E HV']]; subst V; simpl.
      assert (Eu : memb u (u :: V') = true)
        by (apply memb_true_iff; left; reflexivity).
      rewrite Eu; f_equal.
      rewrite (filter_ext_in (fun x => memb x (u :: V'))
                             (fun x => memb x V') U).
      * apply IH; assumption.
      * intros a Ha; apply memb_iff_eq; simpl; split.
        -- intros [E | H]; [subst a; contradiction | exact H].
        -- intros H; right; exact H.
    + simpl.
      assert (Eu : memb u V = false).
      { apply memb_false_iff; intro Hc.
        apply Hu; apply (@subsets_incl U V HV); exact Hc. }
      rewrite Eu; apply IH; assumption.
Qed.

(** And the payoff: a set living inside [U] has a canonical representative
    in the size-[j] layer, so it is counted by [binom]. *)

Theorem norm_in_layer :
  forall U A j,
    NoDup U -> NoDup A -> Subset A U -> length A = j ->
    In (norm U A) (subsets_of_size j U).
Proof.
  intros U A j HU HA Hsub Hlen.
  apply in_subsets_of_size; split.
  - apply norm_in_subsets.
  - rewrite (@norm_length U A HU HA Hsub); exact Hlen.
Qed.

(** *** The weighted form

    [count_fibred_le] needs one number [K] capping every fibre. Claim
    3.4's fibres are capped by the *spread* hypothesis, which caps
    `k^m · |F_M|` rather than `|F_M|` — so the usable form multiplies the
    cap through. This is what carries the `k^{-m}` saving of step 4. *)

Lemma dep_pairs_weighted_le :
  forall {B C : Type} (Base : list B) (fib : B -> list C) (w W : nat),
    (forall b, In b Base -> w * length (fib b) <= W) ->
    w * length (dep_pairs Base fib) <= length Base * W.
Proof.
  intros B C Base fib w W; unfold dep_pairs.
  induction Base as [|b Base IH]; intros Hle; simpl; [lia|].
  rewrite app_length, map_length.
  assert (H1 : w * length (fib b) <= W) by (apply Hle; left; reflexivity).
  assert (H2 : w * length (flat_map (fun b0 => map (fun c => (b0, c)) (fib b0)) Base)
               <= length Base * W)
    by (apply IH; intros b0 Hb0; apply Hle; right; exact Hb0).
  nia.
Qed.

Theorem count_fibred_weighted_le :
  forall {A B C : Type} (g : A -> B) (h : A -> C)
         (L : list A) (Base : list B) (fib : B -> list C) (w W : nat),
    NoDup L ->
    (forall x, In x L -> In (g x) Base) ->
    (forall x, In x L -> In (h x) (fib (g x))) ->
    (forall x y, In x L -> In y L -> g x = g y -> h x = h y -> x = y) ->
    (forall b, In b Base -> w * length (fib b) <= W) ->
    w * length L <= length Base * W.
Proof.
  intros A B C g h L Base fib w W HL Hg Hh Hinj Hfib.
  set (e := fun x : A => (g x, h x)).
  assert (Hincl : incl (map e L) (dep_pairs Base fib)).
  { intros p Hp; apply in_map_iff in Hp as [x [E Hx]]; subst p; unfold e.
    apply in_dep_pairs; split; [apply Hg; exact Hx | apply Hh; exact Hx]. }
  assert (Hnd : NoDup (map e L)).
  { apply (@NoDup_map_inj A (B * C) e L); [| exact HL].
    intros x y Hx Hy E; unfold e in E.
    inversion E as [[E1 E2]]; apply (Hinj x y Hx Hy E1 E2). }
  pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
  rewrite map_length in Hlen.
  assert (H1 : w * length L <= w * length (dep_pairs Base fib))
    by (apply Nat.mul_le_mono_l; exact Hlen).
  eapply Nat.le_trans; [exact H1 | apply dep_pairs_weighted_le; exact Hfib].
Qed.

(** *** Membership-only rewriting

    Three operations of [Spread] read a set argument only through
    membership, so a [SetEq] argument may be swapped inside them. That is
    what lets the canonical key be used where the original set was. *)

Lemma memb_setminus :
  forall x A T, memb x (setminus A T) = andb (memb x A) (negb (memb x T)).
Proof.
  intros x A T; destruct (memb x (setminus A T)) eqn:E.
  - apply memb_true_iff, in_setminus_iff in E as [H1 H2].
    rewrite (proj2 (memb_true_iff x A) H1), (proj2 (memb_false_iff x T) H2).
    reflexivity.
  - apply memb_false_iff in E.
    destruct (memb x A) eqn:EA; destruct (memb x T) eqn:ET; simpl; try reflexivity.
    exfalso; apply E, in_setminus_iff; split;
      [apply memb_true_iff; exact EA | apply memb_false_iff; exact ET].
Qed.

Lemma setminus_SetEq_r :
  forall A T1 T2, SetEq T1 T2 -> setminus A T1 = setminus A T2.
Proof.
  intros A T1 T2 [H1 H2]; unfold setminus; apply filter_ext_eq; intros x.
  f_equal; apply memb_iff_eq; split; [apply H1 | apply H2].
Qed.

Lemma filter_filter :
  forall {T : Type} (p q : T -> bool) (l : list T),
    filter p (filter q l) = filter (fun x => andb (q x) (p x)) l.
Proof.
  intros T p q l; induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (q a) eqn:Eq; simpl.
  - destruct (p a); simpl; [f_equal|]; exact IH.
  - exact IH.
Qed.

(** [setminus] commutes with [norm]: both are filters over [U]. *)

Lemma setminus_norm_l :
  forall U Z M, setminus (norm U Z) M = norm U (setminus Z M).
Proof.
  intros U Z M.
  transitivity (filter (fun x => andb (memb x Z) (negb (memb x M))) U).
  - unfold norm, setminus; apply filter_filter.
  - unfold norm; apply filter_ext_eq; intros x.
    rewrite memb_setminus; reflexivity.
Qed.
