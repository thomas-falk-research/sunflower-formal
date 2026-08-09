(** * Counting.v -- Stage A of the spread lemma: the counting layer.

    `docs/roadmap.md` §1 stages the discharge of [ALWZ.Rao20_lemma2]
    through the *counting* proof — [ALWZ20] §2 as streamlined by
    Park–Pham, written out in Lovett's PCMI notes §3 (pp. 11–15) — and
    §1's Stage A is the arithmetic that proof needs and nothing else:

    - fixed-size subset enumeration, with its count;
    - a counting operator with "an injection implies an inequality" and
      additivity over disjoint predicates;
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
From Sunflower Require Import Sets Pigeonhole Spread.
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
  forall (A B : list (list nat)),
    NoDup A -> NoDup B -> (forall x, In x A -> ~ In x B) -> NoDup (A ++ B).
Proof.
  induction A as [|a A IH]; intros B HA HB Hdisj; simpl; [exact HB|].
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

Definition count (p : list nat -> bool) (L : list (list nat)) : nat :=
  length (filter p L).

Lemma count_le_length : forall p L, count p L <= length L.
Proof. intros p L; apply length_filter_le. Qed.

Lemma count_partition :
  forall p L, count p L + count (fun A => negb (p A)) L = length L.
Proof.
  intros p L; unfold count; symmetry; apply length_filter_partition.
Qed.

Lemma count_disjoint_add :
  forall p q L,
    (forall A, p A = true -> q A = false) ->
    count p L + count q L = count (fun A => orb (p A) (q A)) L.
Proof.
  intros p q L Hdisj; unfold count.
  induction L as [|A L IH]; simpl; [reflexivity|].
  destruct (p A) eqn:Ep.
  - rewrite (Hdisj A Ep); simpl; lia.
  - destruct (q A); simpl; lia.
Qed.

Lemma count_mono :
  forall p q L, (forall A, p A = true -> q A = true) -> count p L <= count q L.
Proof.
  intros p q L Himp; unfold count.
  induction L as [|A L IH]; simpl; [lia|].
  destruct (p A) eqn:Ep.
  - rewrite (Himp A Ep); simpl; lia.
  - destruct (q A); simpl; lia.
Qed.

(** *** An injection implies an inequality

    This is the shape Claim 3.4's encoding is used in: the good pairs
    inject into an explicit product, so there are at most as many of
    them. Only the *domain* needs [NoDup] — the codomain is a list that
    may repeat, and the bound is still valid. *)

(** [NoDup_map_inj] is not in Coq 8.18's [List]; only the converse
    [NoDup_map_inv] is. Injectivity is needed only on the list itself. *)

Lemma NoDup_map_inj :
  forall (f : list nat -> list nat) (l : list (list nat)),
    (forall A B, In A l -> In B l -> f A = f B -> A = B) ->
    NoDup l -> NoDup (map f l).
Proof.
  induction l as [|a l IH]; intros Hinj Hnd; simpl; [constructor|].
  inversion Hnd as [|? ? Hna Hnd']; subst.
  constructor.
  - intro Hin; apply in_map_iff in Hin as [b [E Hb]].
    apply Hna.
    rewrite (Hinj a b (or_introl eq_refl) (or_intror Hb) (eq_sym E)); exact Hb.
  - apply IH; [intros A B HA HB; apply Hinj; right; assumption | exact Hnd'].
Qed.

Theorem count_inj_le :
  forall (p q : list nat -> bool) (f : list nat -> list nat)
         (L M : list (list nat)),
    NoDup L ->
    (forall A, In A L -> p A = true -> In (f A) M /\ q (f A) = true) ->
    (forall A B, In A L -> In B L -> p A = true -> p B = true ->
                 f A = f B -> A = B) ->
    count p L <= count q M.
Proof.
  intros p q f L M HL Hmap Hinj; unfold count.
  assert (HLp : NoDup (filter p L)) by (apply NoDup_filter; exact HL).
  assert (Hincl : incl (map f (filter p L)) (filter q M)).
  { intros B HB; apply in_map_iff in HB as [A [E HA]]; subst B.
    apply filter_In in HA as [HAL HAp].
    destruct (Hmap A HAL HAp) as [HfM Hfq].
    apply filter_In; split; assumption. }
  assert (Hnd : NoDup (map f (filter p L))).
  { apply (@NoDup_map_inj f (filter p L)); [| exact HLp].
    intros A B HA HB E.
    apply filter_In in HA as [HAL HAp]; apply filter_In in HB as [HBL HBp].
    apply (Hinj A B HAL HBL HAp HBp E). }
  pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
  rewrite map_length in Hlen; exact Hlen.
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
