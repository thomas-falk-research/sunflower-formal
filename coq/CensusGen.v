(** * Orderly generation with witness-checked pruning

    The mathematics of a certifying isomorph-free search
    (docs/census_certification.md, stage 2).  A family of sets is
    represented by the ascending sorted list of its rows' bitmasks
    ([N]); families of equal size are compared lexicographically.  A
    search adds one row at a time, larger than every row so far, and may
    prune a node only when an untrusted oracle supplies a relabelling
    that makes it strictly smaller, which is checked.  The hereditary
    lemma ([lexb_insert_last], [parent_minimal]) shows that the minimal
    member of every class survives whatever the oracle answers.

    This file: the order and the hereditary lemma. *)

From Coq Require Import List Arith NArith Lia Bool.
Import ListNotations.
Local Open Scope N_scope.

(** ** The order *)

(** Strict lexicographic order on lists of equal length. *)
Fixpoint lexb (A B : list N) : bool :=
  match A, B with
  | a :: A', b :: B' => (a <? b) || ((a =? b) && lexb A' B')
  | _, _ => false
  end.

Fixpoint insertN (x : N) (A : list N) : list N :=
  match A with
  | [] => [x]
  | a :: A' => if x <? a then x :: A else a :: insertN x A'
  end.

(** Sorting by insertion, left to right, so that appending a row is one
    more insertion ([sortN_app1]). *)
Definition sortN (A : list N) : list N := fold_left (fun acc x => insertN x acc) A [].

Lemma sortN_app1 : forall A y, sortN (A ++ [y]) = insertN y (sortN A).
Proof. intros A y; unfold sortN; rewrite fold_left_app; reflexivity. Qed.

Lemma in_insertN : forall x a A, In a (insertN x A) <-> x = a \/ In a A.
Proof.
  intros x a A; induction A as [| b A IH]; simpl; [tauto |].
  destruct (x <? b); simpl; [tauto |]. rewrite IH; tauto.
Qed.

Lemma in_sortN_acc : forall A acc a, In a (fold_left (fun acc x => insertN x acc) A acc) <-> In a A \/ In a acc.
Proof.
  induction A as [| x A IH]; intros acc a; simpl; [tauto |].
  rewrite IH, in_insertN; tauto.
Qed.

Lemma in_sortN : forall A a, In a (sortN A) <-> In a A.
Proof. intros A a; unfold sortN; rewrite in_sortN_acc; simpl; tauto. Qed.

Lemma lexb_irrefl : forall A, lexb A A = false.
Proof.
  induction A as [| a A IH]; simpl; [reflexivity |].
  rewrite N.ltb_irrefl, N.eqb_refl, IH; reflexivity.
Qed.

(** ** The hereditary lemma

    Insert a new row [x] (not already present) into [A], and append a
    row [y] larger than everything in [B]: if [A] precedes [B], the
    results keep that order.  This is the step "a relabelling that
    improves the parent improves the child": [A] is the relabelled
    parent, [B] the parent, [y] the child's largest row and [x] its
    image.  No sortedness is needed. *)
Lemma lexb_insert_last : forall A B x y,
  lexb A B = true -> ~ In x A -> (forall z, In z B -> z < y) ->
  lexb (insertN x A) (B ++ [y]) = true.
Proof.
  induction A as [| a A IH]; intros [| b B] x y Hl Hx Hy; simpl in Hl; try discriminate.
  assert (Hxa : x <> a) by (intro E; apply Hx; left; symmetry; exact E).
  apply orb_true_iff in Hl as [Hab | Hab].
  - apply N.ltb_lt in Hab. simpl.
    destruct (N.ltb_spec x a) as [Hxa' | Hxa'].
    + simpl. apply orb_true_iff; left. apply N.ltb_lt. lia.
    + simpl. apply orb_true_iff; left. apply N.ltb_lt. exact Hab.
  - apply andb_true_iff in Hab as [Eab Hl]. apply N.eqb_eq in Eab. subst b. simpl.
    destruct (N.ltb_spec x a) as [Hxa' | Hxa'].
    + simpl. apply orb_true_iff; left. apply N.ltb_lt. exact Hxa'.
    + simpl. rewrite N.ltb_irrefl, N.eqb_refl. simpl.
      apply IH; [exact Hl | intro H; apply Hx; right; exact H |].
      intros z Hz; apply Hy; right; exact Hz.
Qed.

(** ** Rows as bitmasks

    A row is a list of points; its key is its bitmask, which depends on
    the row as a set ([mask_ext]).  A family's key is the sorted list of
    its rows' keys. *)

Definition mask (l : list nat) : N := fold_right (fun x m => N.lor (N.shiftl 1 (N.of_nat x)) m) 0 l.

Definition inb (x : nat) (A : list nat) : bool := existsb (Nat.eqb x) A.

Lemma inb_iff : forall x A, inb x A = true <-> In x A.
Proof.
  intros x A; unfold inb; rewrite existsb_exists; split.
  - intros [y [Hy E]]; apply Nat.eqb_eq in E; subst; exact Hy.
  - intros H; exists x; split; [exact H | apply Nat.eqb_refl].
Qed.

Lemma mask_bit : forall l n, N.testbit (mask l) n = inb (N.to_nat n) l.
Proof.
  induction l as [| x l IH]; intros n.
  - apply N.bits_0.
  - change (mask (x :: l)) with (N.lor (N.shiftl 1 (N.of_nat x)) (mask l)).
    change (inb (N.to_nat n) (x :: l)) with (Nat.eqb (N.to_nat n) x || inb (N.to_nat n) l).
    rewrite N.lor_spec, (IH n), N.shiftl_1_l, N.pow2_bits_eqb. f_equal.
    destruct (N.eqb_spec (N.of_nat x) n) as [E | NE]; destruct (Nat.eqb_spec (N.to_nat n) x) as [E' | NE'];
      try reflexivity; exfalso.
    + apply NE'; subst; rewrite Nat2N.id; reflexivity.
    + apply NE; subst; apply N2Nat.id.
Qed.

Lemma mask_ext : forall a b, mask a = mask b <-> (forall x, In x a <-> In x b).
Proof.
  intros a b; split.
  - intros E x. rewrite <- !inb_iff.
    pose proof (mask_bit a (N.of_nat x)) as Ha; pose proof (mask_bit b (N.of_nat x)) as Hb.
    rewrite Nat2N.id in Ha, Hb. rewrite <- Ha, <- Hb, E. reflexivity.
  - intros H. apply N.bits_inj_iff. intros n.
    rewrite !mask_bit. destruct (inb (N.to_nat n) a) eqn:Ea; destruct (inb (N.to_nat n) b) eqn:Eb; try reflexivity.
    + apply inb_iff, H, inb_iff in Ea. congruence.
    + apply inb_iff, H, inb_iff in Eb. congruence.
Qed.

Definition key (F : list (list nat)) : list N := sortN (map mask F).

(** Relabelling by [g]: every point [x] becomes [g x]. *)
Definition rmapF (g : nat -> nat) (F : list (list nat)) : list (list nat) := map (map g) F.

(** [g] makes [F] strictly smaller in the order: a witness that [F] is
    not the minimal member of its class. *)
Definition improves (g : nat -> nat) (F : list (list nat)) : bool := lexb (key (rmapF g F)) (key F).

Lemma insertN_max : forall y A, (forall z, In z A -> z < y) -> insertN y A = A ++ [y].
Proof.
  intros y A; induction A as [| a A IH]; intros H; simpl; [reflexivity |].
  assert (Ha : a < y) by (apply H; left; reflexivity).
  destruct (N.ltb_spec y a) as [Hy | Hy]; [lia |].
  rewrite IH; [reflexivity |]. intros z Hz; apply H; right; exact Hz.
Qed.

Lemma key_app1 : forall F r, key (F ++ [r]) = insertN (mask r) (key F).
Proof. intros F r; unfold key; rewrite map_app; simpl; apply sortN_app1. Qed.

Lemma mask_map_inj : forall (g h : nat -> nat), (forall x, h (g x) = x) ->
  forall a b, mask (map g a) = mask (map g b) -> mask a = mask b.
Proof.
  intros g h Hhg a b E. apply mask_ext. intros x. apply mask_ext with (x := g x) in E.
  rewrite !in_map_iff in E. split; intros Hx.
  - destruct (proj1 E (ex_intro _ x (conj eq_refl Hx))) as [y [Ey Hy]].
    assert (Exy : y = x) by (rewrite <- (Hhg y), <- (Hhg x), Ey; reflexivity). subst y; exact Hy.
  - destruct (proj2 E (ex_intro _ x (conj eq_refl Hx))) as [y [Ey Hy]].
    assert (Exy : y = x) by (rewrite <- (Hhg y), <- (Hhg x), Ey; reflexivity). subst y; exact Hy.
Qed.

(** ** The hereditary lemma, for families

    Let [F = G ++ [r]] with [r] the largest row.  A relabelling (with an
    inverse on the left) that improves [G] improves [F]: so if [F] is
    minimal in its class, so is [G]. *)
Theorem parent_improves : forall (g h : nat -> nat), (forall x, h (g x) = x) ->
  forall G r, (forall s, In s G -> mask s < mask r) ->
  improves g G = true -> improves g (G ++ [r]) = true.
Proof.
  intros g h Hhg G r Hmax Hi. unfold improves in *.
  unfold rmapF; rewrite map_app; fold (rmapF g G); simpl.
  rewrite !key_app1.
  rewrite (insertN_max (mask r) (key G)).
  2: { intros z Hz. unfold key in Hz. rewrite in_sortN, in_map_iff in Hz. destruct Hz as [s [<- Hs]]. apply Hmax, Hs. }
  apply lexb_insert_last; [exact Hi | |].
  - intros Hin. unfold key, rmapF in Hin. rewrite in_sortN, map_map in Hin.
    apply in_map_iff in Hin as [s [E Hs]].
    apply (mask_map_inj g h Hhg) in E. pose proof (Hmax s Hs) as Hlt. rewrite E in Hlt. lia.
  - intros z Hz. unfold key in Hz. rewrite in_sortN, in_map_iff in Hz. destruct Hz as [s [<- Hs]]. apply Hmax, Hs.
Qed.

(** ** Sorted keys, and the order through its first difference

    For strictly sorted lists of equal length, [A] precedes [B] when the
    smallest element lying in exactly one of them lies in [A]
    ([lexb_first_diff]). *)

From Coq Require Import Sorting.Sorted.

Definition ssorted (A : list N) : Prop := StronglySorted N.lt A.

Lemma insertN_ssorted : forall x A, ssorted A -> ~ In x A -> ssorted (insertN x A).
Proof.
  intros x A; induction A as [| a A IH]; intros HA Hx; simpl.
  - repeat constructor.
  - inversion HA as [| ? ? HA' Ha]; subst.
    assert (Hxa : x <> a) by (intro E; apply Hx; left; symmetry; exact E).
    destruct (N.ltb_spec x a) as [Hlt | Hge].
    + constructor; [exact HA |]. constructor; [exact Hlt |].
      eapply Forall_impl; [| exact Ha]. intros z Hz; simpl in Hz; lia.
    + constructor; [apply IH; [exact HA' | intro H; apply Hx; right; exact H] |].
      apply Forall_forall. intros z Hz. apply in_insertN in Hz as [<- | Hz]; [lia |].
      rewrite Forall_forall in Ha; apply Ha, Hz.
Qed.

Lemma sortN_ssorted : forall A, NoDup A -> ssorted (sortN A).
Proof.
  intros A HA. unfold sortN.
  assert (H : forall acc, ssorted acc -> (forall z, In z acc -> ~ In z A) -> NoDup A ->
             ssorted (fold_left (fun acc x => insertN x acc) A acc)).
  { clear HA. induction A as [| x A IH]; intros acc Hacc Hdis Hnd; simpl; [exact Hacc |].
    inversion Hnd as [| ? ? Hx Hnd']; subst.
    apply IH; [| | exact Hnd'].
    - apply insertN_ssorted; [exact Hacc |]. intros Hin. apply (Hdis x Hin). left; reflexivity.
    - intros z Hz. apply in_insertN in Hz as [<- | Hz]; [exact Hx |].
      intros Hin; apply (Hdis z Hz); right; exact Hin. }
  apply H; [constructor | intros z [] | exact HA].
Qed.

Lemma lexb_first_diff : forall A B, ssorted A -> ssorted B -> length A = length B ->
  forall x, In x A -> ~ In x B -> (forall y, y < x -> (In y A <-> In y B)) ->
  lexb A B = true.
Proof.
  induction A as [| a A IH]; intros [| b B] HA HB Hlen x Hx HxB Hbelow; simpl in Hlen; try discriminate.
  - destruct Hx.
  - inversion HA as [| ? ? HA' Ha]; inversion HB as [| ? ? HB' Hb]; subst.
    rewrite Forall_forall in Ha, Hb. simpl.
    destruct (N.lt_trichotomy a b) as [Hab | [Eab | Hab]].
    + apply orb_true_iff; left; apply N.ltb_lt; exact Hab.
    + subst b. rewrite N.ltb_irrefl, N.eqb_refl; simpl.
      assert (Hxa : x <> a) by (intro E; subst; apply HxB; left; reflexivity).
      apply (IH B HA' HB' ltac:(lia) x).
      * destruct Hx as [E | Hx]; [congruence | exact Hx].
      * intro H; apply HxB; right; exact H.
      * intros y Hy. destruct (N.eq_dec y a) as [-> | Hya].
        -- split; intro H; [pose proof (Ha a H) | pose proof (Hb a H)]; lia.
        -- specialize (Hbelow y Hy). simpl in Hbelow. split; intro H.
           ++ destruct (proj1 Hbelow (or_intror H)) as [E | H']; [congruence | exact H'].
           ++ destruct (proj2 Hbelow (or_intror H)) as [E | H']; [congruence | exact H'].
    + exfalso.
      assert (Hxge : a <= x) by (destruct Hx as [<- | Hx]; [lia | pose proof (Ha x Hx); lia]).
      destruct (proj2 (Hbelow b ltac:(lia)) (or_introl eq_refl)) as [E | Hin]; [lia |].
      pose proof (Ha b Hin); lia.
Qed.
