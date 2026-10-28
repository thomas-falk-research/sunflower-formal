(** * The [10^(n/2)] rate: [AHS72]'s substitution, iterated

    [SubstitutionFree.substitute_iota_lower_bound] is one application of
    [AHS72] Lemma 6, [psi(ab) >= psi(a) psi(b)^a]. With the inner family
    fixed at [iota3] ([psi(3) = 10], grounded on six points) it is a step
    [psi(a) >= N  ==>  psi(3a) >= N * 10^a], and iterating the step [j]
    times gives

      [psi(a * 3^j) >= psi(a) * 10^(a (3^j - 1) / 2)]            ([iota_tower]).

    At [a = 1] this is [psi(3^j) >= 10^((3^j - 1)/2)], [AHS72] p. 388
    display (22) (printed with the exponent's typesetting lost, as
    "[psi(3^k) >= 10(3^k - 1)/2]"). Their (21) iterates the other way,
    with [iota3] outside: [psi(3^k) >= psi(3) psi(3^(k-1))^3].

    For general [n], [AHS72] (23) writes [n] in base 3. The same idea
    here, as an induction on [n = 3q + r] with [r < 3]: the step takes
    [psi(q)] to [psi(3q)], and [Product.iota_supermultiplicative] with
    [psi(r) >= 1] adds the digit. What is lost is exactly the base-3 digit
    sum [s(n)]:

      [psi(n) >= 10^((n - s(n)) / 2)]                         ([iota_base_three]),

    with [s(n) <= 2k] when [n < 3^k] ([digsum3_le]), hence
    [psi(n) >= 10^((n - 2k)/2)], the [10^((n - O(log n))/2)] of [AHS72]
    p. 388. [AHS72] (23) also keeps a factor [2^(l-1)] (from Lemmas 4–5,
    [psi(a+b) >= 2 psi(a) psi(b)]); that factor is not formalised here.
    [g(n) >= 2 psi(n)] ([Intersecting.doubling_lower_bound]) carries the
    bound to the sunflower side ([g_base_three]).

    Proof-shape rule ([docs/testing.md] §4): the length equation of every
    [IotaAtLeast] or [LowerBound] consumed here reaches only [lia] (often
    through [IotaAtLeast_antitone] or [Audit.LowerBound_antitone]), never
    [rewrite] or [exact], so the survivors [iotaatleast-at-least] and
    [lowerbound-at-least] stay survivors. This file comes after [Audit]
    in [_CoqProject] for [LowerBound_antitone]. *)

From Coq Require Import List Arith Lia PeanoNat NArith Wf_nat.
Import ListNotations.
From Sunflower Require Import Sets Sunflower Intersecting Product Substitution SubstitutionFree Audit.

Unset Implicit Arguments.

(** ** One step: substitute [iota3] into every point *)

Lemma length_iota3 : length iota3 = 10.
Proof. vm_compute; reflexivity. Qed.

Theorem iota_triple_step :
  forall a N, IotaAtLeast a N -> IotaAtLeast (a * 3) (N * 10 ^ a).
Proof.
  intros a N [H [HU [HD [HI [Hlen Hno]]]]].
  apply (IotaAtLeast_antitone (a * 3) (length H * length iota3 ^ a) (N * 10 ^ a)).
  - rewrite length_iota3; apply Nat.mul_le_mono_r; lia.
  - exact (substitute_iota_lower_bound a 3 6 H iota3 ltac:(lia) HU HD HI Hno
             iota3_uniform iota3_distinct iota3_intersecting iota3_no_sunflower
             iota3_grounded).
Qed.

(** ** The tower *)

Lemma iota_tower_exponent :
  forall j a N, IotaAtLeast a N ->
    exists e, 2 * e + a = a * 3 ^ j /\ IotaAtLeast (a * 3 ^ j) (N * 10 ^ e).
Proof.
  induction j as [|j IH]; intros a N HL.
  - exists 0; split; [simpl; lia|].
    replace (a * 3 ^ 0) with a by (simpl; lia).
    replace (N * 10 ^ 0) with N by (simpl; lia).
    exact HL.
  - destruct (IH a N HL) as [e [He HLe]].
    exists (e + a * 3 ^ j); split; [rewrite Nat.pow_succ_r'; nia|].
    replace (a * 3 ^ S j) with (a * 3 ^ j * 3) by (rewrite Nat.pow_succ_r'; nia).
    replace (N * 10 ^ (e + a * 3 ^ j)) with (N * 10 ^ e * 10 ^ (a * 3 ^ j))
      by (rewrite Nat.pow_add_r; lia).
    exact (iota_triple_step (a * 3 ^ j) (N * 10 ^ e) HLe).
Qed.

Lemma half_of_double : forall e x, 2 * e = x -> x / 2 = e.
Proof.
  intros e x <-; rewrite Nat.mul_comm; apply Nat.div_mul; lia.
Qed.

Theorem iota_tower :
  forall j a N, IotaAtLeast a N ->
    IotaAtLeast (a * 3 ^ j) (N * 10 ^ (a * (3 ^ j - 1) / 2)).
Proof.
  intros j a N HL.
  destruct (iota_tower_exponent j a N HL) as [e [He HLe]].
  replace (a * (3 ^ j - 1) / 2) with e; [exact HLe|].
  symmetry; apply half_of_double.
  rewrite Nat.mul_sub_distr_l, Nat.mul_1_r; lia.
Qed.

(** [psi(3^j) >= 10^((3^j - 1)/2)], [AHS72] p. 388 (22). *)

Corollary iota_three_power :
  forall j, IotaAtLeast (3 ^ j) (10 ^ ((3 ^ j - 1) / 2)).
Proof.
  intros j.
  pose proof (iota_tower j 1 1 iota_one_at_least_one) as H.
  replace (1 * 3 ^ j) with (3 ^ j) in H by lia.
  replace (1 * 10 ^ (1 * (3 ^ j - 1) / 2)) with (10 ^ ((3 ^ j - 1) / 2)) in H
    by (rewrite !Nat.mul_1_l; reflexivity).
  exact H.
Qed.

(** ** General [n]: base three

    [digsum3 n] is the sum of the base-3 digits of [n]. The fuel is [n]
    itself, which suffices because [n / 3 < n] for [n > 0]
    ([digsum3_step] is the defining equation). *)

Fixpoint digsum3_aux (fuel n : nat) : nat :=
  match fuel with
  | 0 => 0
  | S f => match n with
           | 0 => 0
           | _ => n mod 3 + digsum3_aux f (n / 3)
           end
  end.

Definition digsum3 (n : nat) : nat := digsum3_aux n n.

(** The definition computes the digit sum: [100 = 10201_3], [26 = 222_3],
    [27 = 1000_3], [80 = 2222_3]. *)

Lemma digsum3_values :
  digsum3 100 = 4 /\ digsum3 26 = 6 /\ digsum3 27 = 1 /\ digsum3 80 = 8.
Proof. vm_compute; repeat split. Qed.

Lemma digsum3_aux_enough :
  forall f g n, n <= f -> n <= g -> digsum3_aux f n = digsum3_aux g n.
Proof.
  induction f as [|f IH]; intros g n Hf Hg.
  - replace n with 0 by lia; destruct g; reflexivity.
  - destruct g as [|g]; [replace n with 0 by lia; reflexivity|].
    destruct n as [|n]; [reflexivity|].
    cbn [digsum3_aux]; f_equal.
    assert (S n / 3 < S n) by (apply Nat.div_lt; lia).
    apply IH; lia.
Qed.

Lemma digsum3_step : forall n, digsum3 n = n mod 3 + digsum3 (n / 3).
Proof.
  intros [|m]; [reflexivity|].
  unfold digsum3 at 1; cbn [digsum3_aux].
  f_equal; unfold digsum3.
  assert (S m / 3 < S m) by (apply Nat.div_lt; lia).
  apply digsum3_aux_enough; lia.
Qed.

Lemma digsum3_le : forall k n, n < 3 ^ k -> digsum3 n <= 2 * k.
Proof.
  induction k as [|k IH]; intros n Hn.
  - replace n with 0 by (simpl in Hn; lia); reflexivity.
  - rewrite digsum3_step.
    assert (Hm : n mod 3 < 3) by (apply Nat.mod_upper_bound; lia).
    assert (Hq : n / 3 < 3 ^ k)
      by (apply Nat.Div0.div_lt_upper_bound; rewrite <- Nat.pow_succ_r'; exact Hn).
    pose proof (IH (n / 3) Hq); lia.
Qed.

Lemma iota_at_least_one : forall q, 1 <= q -> IotaAtLeast q 1.
Proof.
  intros q Hq.
  pose proof (iota_at_least_power 1 1 q iota_one_at_least_one Hq) as H.
  rewrite Nat.mul_1_r, Nat.pow_1_l in H; exact H.
Qed.

Lemma iota_base_three_exponent :
  forall n, 1 <= n ->
    exists e, 2 * e + digsum3 n = n /\ IotaAtLeast n (10 ^ e).
Proof.
  induction n as [n IH] using lt_wf_ind; intros Hn.
  pose proof (Nat.div_mod_eq n 3) as Hdm.
  assert (Hr : n mod 3 < 3) by (apply Nat.mod_upper_bound; lia).
  set (q := n / 3) in *; set (r := n mod 3) in *.
  assert (Hds : digsum3 n = r + digsum3 q) by exact (digsum3_step n).
  destruct (Nat.eq_dec q 0) as [Eq | Eq].
  - (* one digit: [n = r], [s(n) = r], and [psi(r) >= 1 = 10^0] *)
    assert (H0 : digsum3 q = 0) by (rewrite Eq; reflexivity).
    exists 0; split; [lia|].
    exact (iota_at_least_one n Hn).
  - destruct (IH q ltac:(lia) ltac:(lia)) as [e [He HLe]].
    pose proof (iota_triple_step q (10 ^ e) HLe) as H3.
    rewrite <- Nat.pow_add_r in H3.
    exists (e + q); split; [lia|].
    destruct (Nat.eq_dec r 0) as [Er | Er].
    + replace n with (q * 3) by lia; exact H3.
    + pose proof (iota_supermultiplicative (q * 3) r _ 1 H3
                    (iota_at_least_one r ltac:(lia))) as HS.
      rewrite Nat.mul_1_r in HS.
      replace n with (q * 3 + r) by lia; exact HS.
Qed.

Theorem iota_base_three :
  forall n, 1 <= n -> IotaAtLeast n (10 ^ ((n - digsum3 n) / 2)).
Proof.
  intros n Hn.
  destruct (iota_base_three_exponent n Hn) as [e [He HL]].
  replace ((n - digsum3 n) / 2) with e; [exact HL|].
  symmetry; apply half_of_double; lia.
Qed.

(** The [O(log n)] form: [n < 3^k] has at most [k] digits. *)

Corollary iota_log_loss :
  forall k n, 1 <= n -> n < 3 ^ k -> IotaAtLeast n (10 ^ ((n - 2 * k) / 2)).
Proof.
  intros k n Hn Hk.
  apply (IotaAtLeast_antitone n (10 ^ ((n - digsum3 n) / 2))).
  - apply Nat.pow_le_mono_r; [lia|].
    apply Nat.div_le_mono; [lia|].
    pose proof (digsum3_le k n Hk); lia.
  - exact (iota_base_three n Hn).
Qed.

(** [g(n) >= 2 psi(n)]: the same rate for sunflower-free families. *)

Theorem g_base_three :
  forall n, 1 <= n -> LowerBound n 3 (2 * 10 ^ ((n - digsum3 n) / 2)).
Proof.
  intros n Hn.
  destruct (iota_base_three n Hn) as [H [HU [HD [HI [Hlen Hno]]]]].
  apply (@LowerBound_antitone n 3 (2 * length H)); [|lia].
  exact (doubling_lower_bound n H Hn HU HD HI Hno).
Qed.

(** ** Past base 3

    [psi(27 t) >= psi(t) 10^(13 t) >= 10^(13 t)] ([iota_tower] at
    [j = 3]), and [10^13 > 3^27]: [10^(13/27) = 3.030], against
    [20000^(1/9) = 3.005] from [SubstitutionFree.lower_bound_9_3_20000]
    and the limit [sqrt 10 = 3.162]. *)

Corollary iota_27t :
  forall t, 1 <= t -> IotaAtLeast (27 * t) (10 ^ (13 * t)).
Proof.
  intros t Ht.
  pose proof (iota_tower 3 t 1 (iota_at_least_one t Ht)) as H.
  (* [change], never [simpl]: [simpl] would unfold [t * 27] into a sum. *)
  change (3 ^ 3) with 27 in H.
  replace (t * (27 - 1) / 2) with (13 * t) in H
    by (replace (t * (27 - 1)) with (13 * t * 2) by lia; rewrite Nat.div_mul; lia).
  rewrite Nat.mul_1_l in H.
  replace (27 * t) with (t * 27) by lia; exact H.
Qed.

Corollary iota_27t_beats_three :
  forall t, 1 <= t -> 3 ^ (27 * t) < 10 ^ (13 * t).
Proof.
  intros t Ht.
  rewrite !Nat.pow_mul_r.
  apply Nat.pow_lt_mono_l; [lia|].
  (* Compared in binary: [10^13] in unary [nat] is out of reach. *)
  apply Nat.compare_lt_iff; rewrite Nat2N.inj_compare, !Nat2N.inj_pow.
  vm_compute; reflexivity.
Qed.
