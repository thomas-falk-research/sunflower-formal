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
From Coq Require FinFun.

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

(** ** Labels and witnesses *)

Local Close Scope N_scope.

(** One more than the largest label used ([0] for no labels). *)
Definition nl (F : list (list nat)) : nat := fold_right (fun x m => Nat.max (S x) m) 0 (concat F).

Lemma nl_bound : forall F x, In x (concat F) -> (x < nl F)%nat.
Proof.
  intros F x; unfold nl; generalize (concat F); intros l Hx.
  induction l as [| y l IH]; [destruct Hx |]. cbn [fold_right].
  destruct Hx as [<- | Hx].
  - eapply Nat.lt_le_trans; [| apply Nat.le_max_l]. apply Nat.lt_succ_diag_r.
  - eapply Nat.lt_le_trans; [exact (IH Hx) | apply Nat.le_max_r].
Qed.

(** A witness is a list [p], read as the map [x ↦ nth x p] below its
    length and the identity above; [is_permb] checks that it is a
    permutation of [0 .. length p − 1]. *)
Definition pf (p : list nat) (x : nat) : nat := if (x <? length p)%nat then nth x p 0%nat else x.

Fixpoint nodupb (l : list nat) : bool :=
  match l with [] => true | a :: l' => negb (inb a l') && nodupb l' end.

Lemma nodupb_NoDup : forall l, nodupb l = true -> NoDup l.
Proof.
  induction l as [| a l IH]; intros H; simpl in H; [constructor |].
  apply andb_true_iff in H as [H1 H2]. apply negb_true_iff in H1.
  constructor; [intro Hin; apply inb_iff in Hin; congruence | apply IH, H2].
Qed.

Definition is_permb (p : list nat) : bool := forallb (fun i => (i <? length p)%nat) p && nodupb p.

Fixpoint index_of (x : nat) (l : list nat) : nat :=
  match l with [] => 0 | a :: l' => if Nat.eqb a x then 0 else S (index_of x l') end.

Lemma nth_index_of : forall x l, In x l -> nth (index_of x l) l 0%nat = x.
Proof.
  intros x l; induction l as [| a l IH]; intros H; [destruct H |]. simpl.
  destruct (Nat.eqb_spec a x) as [E | NE]; [exact E |].
  destruct H as [E | H]; [congruence | apply IH, H].
Qed.

Lemma index_of_lt : forall x l, In x l -> (index_of x l < length l)%nat.
Proof.
  intros x l; induction l as [| a l IH]; intros H; [destruct H |]. simpl.
  destruct (Nat.eqb_spec a x) as [E | NE]; [lia |].
  destruct H as [E | H]; [congruence | specialize (IH H); lia].
Qed.

Lemma index_of_nth : forall l i, NoDup l -> (i < length l)%nat -> index_of (nth i l 0%nat) l = i.
Proof.
  induction l as [| a l IH]; intros i Hnd Hi; [simpl in Hi; lia |].
  inversion Hnd as [| ? ? Ha Hnd']; subst. destruct i as [| i]; simpl.
  - rewrite Nat.eqb_refl; reflexivity.
  - destruct (Nat.eqb_spec a (nth i l 0%nat)) as [E | NE].
    + exfalso; apply Ha. rewrite E. apply nth_In. simpl in Hi; lia.
    + f_equal. apply IH; [exact Hnd' | simpl in Hi; lia].
Qed.

Definition pinv (p : list nat) (x : nat) : nat := if (x <? length p)%nat then index_of x p else x.

Lemma is_permb_spec : forall p, is_permb p = true ->
  NoDup p /\ (forall i, In i p -> (i < length p)%nat) /\ (forall i, (i < length p)%nat -> In i p).
Proof.
  intros p H. unfold is_permb in H. apply andb_true_iff in H as [H1 H2].
  apply nodupb_NoDup in H2. rewrite forallb_forall in H1.
  assert (Hlt : forall i, In i p -> (i < length p)%nat) by (intros i Hi; apply Nat.ltb_lt, H1, Hi).
  split; [exact H2 | split; [exact Hlt |]].
  intros i Hi. assert (Hincl : incl (seq 0 (length p)) p).
  { apply (NoDup_length_incl H2); [rewrite seq_length; lia |].
    intros j Hj. apply in_seq. split; [lia | apply Hlt, Hj]. }
  apply Hincl, in_seq; lia.
Qed.

(** A checked witness is a bijection of the naturals. *)
Lemma pinv_pf : forall p, is_permb p = true -> forall x, pinv p (pf p x) = x.
Proof.
  intros p H x. destruct (is_permb_spec p H) as [Hnd [Hlt Hin]]. unfold pf, pinv.
  destruct (Nat.ltb_spec x (length p)) as [Hx | Hx].
  - assert (Hy : (nth x p 0 < length p)%nat) by (apply Hlt, nth_In, Hx).
    apply Nat.ltb_lt in Hy. rewrite Hy. apply index_of_nth; assumption.
  - apply Nat.ltb_ge in Hx. rewrite Hx. reflexivity.
Qed.

Lemma pf_pinv : forall p, is_permb p = true -> forall x, pf p (pinv p x) = x.
Proof.
  intros p H x. destruct (is_permb_spec p H) as [Hnd [Hlt Hin]]. unfold pf, pinv.
  destruct (Nat.ltb_spec x (length p)) as [Hx | Hx].
  - pose proof (Hin x Hx) as Hxp. pose proof (index_of_lt x p Hxp) as Hi.
    apply Nat.ltb_lt in Hi. rewrite Hi. apply nth_index_of, Hxp.
  - apply Nat.ltb_ge in Hx. rewrite Hx. reflexivity.
Qed.

(** Extending a witness by the identity does not change its action. *)
Lemma pf_extend : forall p m x, pf (p ++ seq (length p) m) x = pf p x.
Proof.
  intros p m x. unfold pf. rewrite app_length, seq_length.
  destruct (Nat.ltb_spec x (length p)) as [Hx | Hx].
  - assert (Hx' : (x < length p + m)%nat) by lia. apply Nat.ltb_lt in Hx'. rewrite Hx', app_nth1 by exact Hx. reflexivity.
  - destruct (Nat.ltb_spec x (length p + m)) as [Hx' | Hx']; [| reflexivity].
    rewrite app_nth2 by exact Hx. rewrite seq_nth by lia. lia.
Qed.

Lemma nodup_app : forall (a b : list nat), NoDup a -> NoDup b -> (forall x, In x a -> In x b -> False) -> NoDup (a ++ b).
Proof.
  induction a as [| x a IH]; intros b Ha Hb Hd; simpl; [exact Hb |].
  inversion Ha as [| ? ? Hx Ha']; subst. constructor.
  - intros Hin. apply in_app_iff in Hin as [Hin | Hin]; [contradiction | apply (Hd x); [left; reflexivity | exact Hin]].
  - apply IH; [exact Ha' | exact Hb |]. intros y Hy Hy'; apply (Hd y); [right; exact Hy | exact Hy'].
Qed.

Lemma is_permb_extend : forall p m, is_permb p = true -> is_permb (p ++ seq (length p) m) = true.
Proof.
  intros p m H. destruct (is_permb_spec p H) as [Hnd [Hlt _]].
  unfold is_permb. apply andb_true_iff; split.
  - apply forallb_forall. intros i Hi. apply Nat.ltb_lt. rewrite app_length, seq_length.
    apply in_app_iff in Hi as [Hi | Hi]; [specialize (Hlt i Hi); lia | apply in_seq in Hi; lia].
  - assert (Hnd' : NoDup (p ++ seq (length p) m)).
    { apply nodup_app; [exact Hnd | apply seq_NoDup |].
      intros i Hi Hi'. apply in_seq in Hi'. specialize (Hlt i Hi). lia. }
    clear -Hnd'. induction (p ++ seq (length p) m) as [| a l IH]; [reflexivity |].
    inversion Hnd' as [| ? ? Ha Hl]; subst. simpl. apply andb_true_iff; split.
    + apply negb_true_iff. destruct (inb a l) eqn:E; [apply inb_iff in E; contradiction | reflexivity].
    + apply IH, Hl.
Qed.

(** ** Minimal families have no gaps

    If a label [a] below the largest label [c] is unused, swapping [a]
    and [c] improves the family ([gap_improves]): rows without [c] are
    unchanged, rows with [c] drop below [2^c], and every original row
    with [c] is at least [2^c].  So a minimal family uses exactly the
    labels [0 .. nl F − 1]. *)

Lemma NoDup_nodupb : forall l, NoDup l -> nodupb l = true.
Proof.
  induction l as [| a l IH]; intros H; [reflexivity |].
  inversion H as [| ? ? Ha Hl]; subst. simpl. apply andb_true_iff; split.
  - apply negb_true_iff. destruct (inb a l) eqn:E; [apply inb_iff in E; contradiction | reflexivity].
  - apply IH, Hl.
Qed.

Definition swf (a c x : nat) : nat := if Nat.eqb x a then c else if Nat.eqb x c then a else x.

Definition swp (v a c : nat) : list nat := map (swf a c) (seq 0 v).

Lemma swf_invol : forall a c x, swf a c (swf a c x) = x.
Proof.
  intros a c x; unfold swf.
  destruct (Nat.eqb_spec x a) as [Ex | Ex]; destruct (Nat.eqb_spec x c) as [Ex' | Ex'].
  all: repeat (first [rewrite Nat.eqb_refl | match goal with |- context [Nat.eqb ?u ?w] => destruct (Nat.eqb_spec u w) end]); subst; try lia; reflexivity.
Qed.

Lemma pf_swp : forall v a c, (a < v)%nat -> (c < v)%nat -> forall x, pf (swp v a c) x = swf a c x.
Proof.
  intros v a c Ha Hc x. unfold pf, swp. rewrite map_length, seq_length.
  destruct (Nat.ltb_spec x v) as [Hx | Hx].
  - rewrite (nth_indep _ 0%nat (swf a c 0%nat)) by (rewrite map_length, seq_length; exact Hx).
    rewrite map_nth, seq_nth by exact Hx. reflexivity.
  - unfold swf. destruct (Nat.eqb_spec x a); [lia |]. destruct (Nat.eqb_spec x c); [lia | reflexivity].
Qed.

Lemma swp_perm : forall v a c, (a < v)%nat -> (c < v)%nat -> is_permb (swp v a c) = true.
Proof.
  intros v a c Ha Hc. unfold is_permb. apply andb_true_iff; split.
  - apply forallb_forall. intros i Hi. unfold swp in Hi. apply in_map_iff in Hi as [j [<- Hj]].
    apply in_seq in Hj. apply Nat.ltb_lt. unfold swp; rewrite map_length, seq_length. unfold swf.
    destruct (Nat.eqb j a); [lia |]. destruct (Nat.eqb j c); lia.
  - apply NoDup_nodupb. unfold swp. apply FinFun.Injective_map_NoDup; [| apply seq_NoDup].
    intros x y E. rewrite <- (swf_invol a c x), E, swf_invol; reflexivity.
Qed.

Local Open Scope N_scope.

Lemma lor_lt_pow : forall a b c, a < 2 ^ c -> b < 2 ^ c -> N.lor a b < 2 ^ c.
Proof.
  intros a b c Ha Hb.
  destruct (N.eq_dec a 0) as [-> | Ha0]; [rewrite N.lor_0_l; exact Hb |].
  destruct (N.eq_dec b 0) as [-> | Hb0]; [rewrite N.lor_0_r; exact Ha |].
  assert (Hl : 0 < N.lor a b).
  { destruct (N.eq_dec (N.lor a b) 0) as [E | NE]; [| lia]. apply N.lor_eq_0_l in E. contradiction. }
  apply N.log2_lt_pow2; [exact Hl |]. rewrite N.log2_lor. apply N.max_lub_lt.
  - apply N.log2_lt_pow2; [lia | exact Ha].
  - apply N.log2_lt_pow2; [lia | exact Hb].
Qed.

Lemma mask_lt_pow : forall l c, (forall x, In x l -> (x < c)%nat) -> mask l < 2 ^ N.of_nat c.
Proof.
  induction l as [| x l IH]; intros c H.
  - simpl. apply N.neq_0_lt_0, N.pow_nonzero; lia.
  - change (mask (x :: l)) with (N.lor (N.shiftl 1 (N.of_nat x)) (mask l)).
    apply lor_lt_pow; [| apply IH; intros y Hy; apply H; right; exact Hy].
    rewrite N.shiftl_1_l. apply N.pow_lt_mono_r; [lia |]. specialize (H x (or_introl eq_refl)). lia.
Qed.

Lemma mask_ge_pow : forall l c, In c l -> 2 ^ N.of_nat c <= mask l.
Proof.
  intros l c Hc. destruct (N.lt_ge_cases (mask l) (2 ^ N.of_nat c)) as [Hlt | Hge]; [exfalso | exact Hge].
  assert (Hb : N.testbit (mask l) (N.of_nat c) = true) by (rewrite mask_bit, Nat2N.id; apply inb_iff, Hc).
  destruct (N.eq_dec (mask l) 0) as [E | NE]; [rewrite E, N.bits_0 in Hb; discriminate |].
  rewrite N.bits_above_log2 in Hb; [discriminate |]. apply N.log2_lt_pow2; [lia | exact Hlt].
Qed.

Lemma nl_attained : forall F, (0 < nl F)%nat -> In (nl F - 1)%nat (concat F).
Proof.
  intros F; unfold nl; generalize (concat F); intros l.
  induction l as [| y l IH]; cbn [fold_right]; intros H; [lia |].
  destruct (Nat.le_ge_cases (S y) (fold_right (fun x m => Nat.max (S x) m) 0%nat l)) as [Hle | Hge].
  - rewrite Nat.max_r by exact Hle. right; apply IH; lia.
  - rewrite Nat.max_l by exact Hge. left; lia.
Qed.

Lemma length_insertN : forall x A, length (insertN x A) = S (length A).
Proof. intros x A; induction A as [| a A IH]; simpl; [reflexivity |]. destruct (x <? a)%N; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma length_sortN : forall A, length (sortN A) = length A.
Proof.
  intros A. unfold sortN. assert (H : forall acc, length (fold_left (fun acc x => insertN x acc) A acc) = (length A + length acc)%nat).
  { induction A as [| x A IH]; intros acc; simpl; [reflexivity |]. rewrite IH, length_insertN. lia. }
  rewrite H; simpl; lia.
Qed.

(** The least element of a nonempty list [y :: l]. *)
Definition minN (y : N) (l : list N) : N := fold_left N.min l y.

Lemma minN_spec : forall l y, In (minN y l) (y :: l) /\ (forall x, In x (y :: l) -> minN y l <= x).
Proof.
  induction l as [| z l IH]; intros y.
  - unfold minN; simpl. split; [left; reflexivity | intros x [E | []]; subst; lia].
  - change (minN y (z :: l)) with (minN (N.min y z) l).
    destruct (IH (N.min y z)) as [Hin Hle]. split.
    + destruct Hin as [E | Hin]; [| right; right; exact Hin].
      rewrite <- E. destruct (N.min_spec y z) as [[_ ->] | [_ ->]]; [left | right; left]; reflexivity.
    + intros x Hx.
      assert (Hm : minN (N.min y z) l <= N.min y z) by (apply Hle; left; reflexivity).
      destruct Hx as [E | [E | Hx]]; [subst x; lia | subst x; lia | apply Hle; right; exact Hx].
Qed.

Lemma in_key : forall F y, In y (key F) <-> exists s, In s F /\ y = mask s.
Proof.
  intros F y; unfold key; rewrite in_sortN, in_map_iff. split.
  - intros [s [E Hs]]; exists s; split; [exact Hs | symmetry; exact E].
  - intros [s [Hs E]]; exists s; split; [symmetry; exact E | exact Hs].
Qed.

Lemma NoDup_map_transfer : forall (A B : Type) (f g : A -> B) (l : list A),
  NoDup (map f l) -> (forall u v, In u l -> In v l -> g u = g v -> f u = f v) -> NoDup (map g l).
Proof.
  intros A B f g l; induction l as [| x l IH]; intros Hnd Hinj; simpl; [constructor |].
  inversion Hnd as [| ? ? Hx Hl]; subst. constructor.
  - intros Hin. apply in_map_iff in Hin as [y [E Hy]]. apply Hx.
    apply in_map_iff. exists y; split; [| exact Hy].
    apply Hinj; [right; exact Hy | left; reflexivity | exact E].
  - apply IH; [exact Hl |]. intros u v Hu Hv; apply Hinj; right; assumption.
Qed.

Theorem gap_improves : forall F a,
  NoDup (map mask F) -> (S a < nl F)%nat -> ~ In a (concat F) ->
  improves (pf (swp (nl F) a (nl F - 1))) F = true.
Proof.
  intros F a Hnd Ha Hun.
  set (c := (nl F - 1)%nat). assert (Hac : (a < c)%nat) by (unfold c; lia).
  set (t := pf (swp (nl F) a c)).
  assert (Ht : forall x, t x = swf a c x) by (intros x; unfold t; apply pf_swp; unfold c; lia).
  assert (Htt : forall x, t (t x) = x) by (intros x; rewrite !Ht; apply swf_invol).
  assert (Hc : In c (concat F)) by (apply nl_attained; lia).
  assert (Hlab : forall s x, In s F -> In x s -> (x <= c)%nat).
  { intros s x Hs Hx. assert (Hxc : In x (concat F)) by (apply in_concat; exists s; split; assumption).
    pose proof (nl_bound F x Hxc). unfold c; lia. }
  assert (Hna : forall s, In s F -> ~ In a s).
  { intros s Hs Has. apply Hun, in_concat. exists s; split; assumption. }
  assert (Hfix : forall s, In s F -> ~ In c s -> mask (map t s) = mask s).
  { intros s Hs Hcs. apply mask_ext. intros y. rewrite in_map_iff. split.
    - intros [z [<- Hz]]. rewrite Ht. unfold swf.
      destruct (Nat.eqb_spec z a) as [-> | _]; [exfalso; exact (Hna s Hs Hz) |].
      destruct (Nat.eqb_spec z c) as [-> | _]; [contradiction | exact Hz].
    - intros Hy. exists y; split; [| exact Hy]. rewrite Ht. unfold swf.
      destruct (Nat.eqb_spec y a) as [-> | _]; [exfalso; exact (Hna s Hs Hy) |].
      destruct (Nat.eqb_spec y c) as [-> | _]; [contradiction | reflexivity]. }
  assert (Hlow : forall s, In s F -> mask (map t s) < 2 ^ N.of_nat c \/ ~ In c s).
  { intros s Hs. destruct (in_dec Nat.eq_dec c s) as [Hcs | Hcs]; [left | right; exact Hcs].
    apply mask_lt_pow. intros y Hy. apply in_map_iff in Hy as [z [<- Hz]]. rewrite Ht. unfold swf.
    destruct (Nat.eqb_spec z a) as [-> | _]; [exfalso; exact (Hna s Hs Hz) |].
    destruct (Nat.eqb_spec z c) as [-> | Hzc]; [exact Hac |]. pose proof (Hlab s z Hs Hz). lia. }
  assert (Hlow' : forall s, In s F -> In c s -> mask (map t s) < 2 ^ N.of_nat c).
  { intros s Hs Hcs. destruct (Hlow s Hs) as [H | H]; [exact H | contradiction]. }
  (* the smallest changed row *)
  apply in_concat in Hc as [s0 [Hs0 Hcs0]].
  set (T := map (fun s => mask (map t s)) (filter (fun s => inb c s) F)).
  assert (HT0 : In (mask (map t s0)) T).
  { apply in_map_iff. exists s0; split; [reflexivity |]. apply filter_In; split; [exact Hs0 | apply inb_iff, Hcs0]. }
  destruct T as [| y0 rest] eqn:ET; [destruct HT0 |].
  destruct (minN_spec rest y0) as [Hxin Hxle]. set (x := minN y0 rest) in *.
  rewrite <- ET in Hxin, Hxle.
  assert (HxT : exists s1, In s1 F /\ In c s1 /\ x = mask (map t s1)).
  { unfold T in Hxin. apply in_map_iff in Hxin as [s1 [E Hs1]]. apply filter_In in Hs1 as [Hs1 Hc1].
    apply inb_iff in Hc1. exists s1; split; [exact Hs1 | split; [exact Hc1 | symmetry; exact E]]. }
  destruct HxT as [s1 [Hs1 [Hcs1 Ex]]].
  assert (Hxlow : x < 2 ^ N.of_nat c) by (rewrite Ex; apply Hlow', Hcs1; exact Hs1).
  assert (HxT' : forall s, In s F -> In c s -> x <= mask (map t s)).
  { intros s Hs Hcs. apply Hxle. unfold T. apply in_map_iff. exists s; split; [reflexivity |].
    apply filter_In; split; [exact Hs | apply inb_iff, Hcs]. }
  unfold improves.
  assert (HndA : NoDup (map mask (rmapF t F))).
  { unfold rmapF. rewrite map_map. apply (NoDup_map_transfer _ _ mask (fun s => mask (map t s)) F Hnd).
    intros u v _ _ E. apply (mask_map_inj t t Htt) in E; exact E. }
  apply (lexb_first_diff _ _ (sortN_ssorted _ HndA) (sortN_ssorted _ Hnd)) with (x := x).
  - unfold key. rewrite !length_sortN, !map_length. unfold rmapF; rewrite map_length; reflexivity.
  - apply in_key. exists (map t s1); split; [apply in_map, Hs1 | exact Ex].
  - intros Hin. apply in_key in Hin as [s [Hs E]].
    destruct (in_dec Nat.eq_dec c s) as [Hcs | Hcs].
    + pose proof (mask_ge_pow s c Hcs). lia.
    + apply (Hna s Hs). rewrite Ex in E. symmetry in E. apply mask_ext with (x := a) in E.
      apply E, in_map_iff. exists c; split; [| exact Hcs1]. rewrite Ht; unfold swf.
      destruct (Nat.eqb_spec c a) as [E' | _]; [lia | rewrite Nat.eqb_refl; reflexivity].
  - intros y Hy. change (In y (key (rmapF t F)) <-> In y (key F)). rewrite !in_key. split.
    + intros [s' [Hs' E]]. unfold rmapF in Hs'. apply in_map_iff in Hs' as [s [<- Hs]].
      destruct (in_dec Nat.eq_dec c s) as [Hcs | Hcs].
      * exfalso. pose proof (HxT' s Hs Hcs). lia.
      * exists s; split; [exact Hs | rewrite E; apply Hfix; assumption].
    + intros [s [Hs E]]. destruct (in_dec Nat.eq_dec c s) as [Hcs | Hcs].
      * exfalso. pose proof (mask_ge_pow s c Hcs). lia.
      * exists (map t s); split; [apply in_map, Hs | rewrite E; symmetry; apply Hfix; assumption].
Qed.
