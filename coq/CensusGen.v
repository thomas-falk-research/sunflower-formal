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

Definition rowmask (l : list nat) : N := fold_right (fun x m => N.lor (N.shiftl 1 (N.of_nat x)) m) 0 l.

Definition inb (x : nat) (A : list nat) : bool := existsb (Nat.eqb x) A.

Lemma inb_iff : forall x A, inb x A = true <-> In x A.
Proof.
  intros x A; unfold inb; rewrite existsb_exists; split.
  - intros [y [Hy E]]; apply Nat.eqb_eq in E; subst; exact Hy.
  - intros H; exists x; split; [exact H | apply Nat.eqb_refl].
Qed.

Lemma rowmask_bit : forall l n, N.testbit (rowmask l) n = inb (N.to_nat n) l.
Proof.
  induction l as [| x l IH]; intros n.
  - apply N.bits_0.
  - change (rowmask (x :: l)) with (N.lor (N.shiftl 1 (N.of_nat x)) (rowmask l)).
    change (inb (N.to_nat n) (x :: l)) with (Nat.eqb (N.to_nat n) x || inb (N.to_nat n) l).
    rewrite N.lor_spec, (IH n), N.shiftl_1_l, N.pow2_bits_eqb. f_equal.
    destruct (N.eqb_spec (N.of_nat x) n) as [E | NE]; destruct (Nat.eqb_spec (N.to_nat n) x) as [E' | NE'];
      try reflexivity; exfalso.
    + apply NE'; subst; rewrite Nat2N.id; reflexivity.
    + apply NE; subst; apply N2Nat.id.
Qed.

Lemma mask_ext : forall a b, rowmask a = rowmask b <-> (forall x, In x a <-> In x b).
Proof.
  intros a b; split.
  - intros E x. rewrite <- !inb_iff.
    pose proof (rowmask_bit a (N.of_nat x)) as Ha; pose proof (rowmask_bit b (N.of_nat x)) as Hb.
    rewrite Nat2N.id in Ha, Hb. rewrite <- Ha, <- Hb, E. reflexivity.
  - intros H. apply N.bits_inj_iff. intros n.
    rewrite !rowmask_bit. destruct (inb (N.to_nat n) a) eqn:Ea; destruct (inb (N.to_nat n) b) eqn:Eb; try reflexivity.
    + apply inb_iff, H, inb_iff in Ea. congruence.
    + apply inb_iff, H, inb_iff in Eb. congruence.
Qed.

Definition key (F : list (list nat)) : list N := sortN (map rowmask F).

(** Relabelling by [g]: every point [x] becomes [g x]. *)
Definition relab (g : nat -> nat) (F : list (list nat)) : list (list nat) := map (map g) F.

(** [g] makes [F] strictly smaller in the order: a witness that [F] is
    not the minimal member of its class. *)
Definition improves (g : nat -> nat) (F : list (list nat)) : bool := lexb (key (relab g F)) (key F).

Lemma insertN_max : forall y A, (forall z, In z A -> z < y) -> insertN y A = A ++ [y].
Proof.
  intros y A; induction A as [| a A IH]; intros H; simpl; [reflexivity |].
  assert (Ha : a < y) by (apply H; left; reflexivity).
  destruct (N.ltb_spec y a) as [Hy | Hy]; [lia |].
  rewrite IH; [reflexivity |]. intros z Hz; apply H; right; exact Hz.
Qed.

Lemma key_app1 : forall F r, key (F ++ [r]) = insertN (rowmask r) (key F).
Proof. intros F r; unfold key; rewrite map_app; simpl; apply sortN_app1. Qed.

Lemma mask_map_inj : forall (g h : nat -> nat), (forall x, h (g x) = x) ->
  forall a b, rowmask (map g a) = rowmask (map g b) -> rowmask a = rowmask b.
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
  forall G r, (forall s, In s G -> rowmask s < rowmask r) ->
  improves g G = true -> improves g (G ++ [r]) = true.
Proof.
  intros g h Hhg G r Hmax Hi. unfold improves in *.
  unfold relab; rewrite map_app; fold (relab g G); simpl.
  rewrite !key_app1.
  rewrite (insertN_max (rowmask r) (key G)).
  2: { intros z Hz. unfold key in Hz. rewrite in_sortN, in_map_iff in Hz. destruct Hz as [s [<- Hs]]. apply Hmax, Hs. }
  apply lexb_insert_last; [exact Hi | |].
  - intros Hin. unfold key, relab in Hin. rewrite in_sortN, map_map in Hin.
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

Fixpoint cg_nodupb (l : list nat) : bool :=
  match l with [] => true | a :: l' => negb (inb a l') && cg_nodupb l' end.

Lemma nodupb_NoDup : forall l, cg_nodupb l = true -> NoDup l.
Proof.
  induction l as [| a l IH]; intros H; simpl in H; [constructor |].
  apply andb_true_iff in H as [H1 H2]. apply negb_true_iff in H1.
  constructor; [intro Hin; apply inb_iff in Hin; congruence | apply IH, H2].
Qed.

Definition is_permb (p : list nat) : bool := forallb (fun i => (i <? length p)%nat) p && cg_nodupb p.

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

Lemma NoDup_nodupb : forall l, NoDup l -> cg_nodupb l = true.
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

Lemma mask_lt_pow : forall l c, (forall x, In x l -> (x < c)%nat) -> rowmask l < 2 ^ N.of_nat c.
Proof.
  induction l as [| x l IH]; intros c H.
  - simpl. apply N.neq_0_lt_0, N.pow_nonzero; lia.
  - change (rowmask (x :: l)) with (N.lor (N.shiftl 1 (N.of_nat x)) (rowmask l)).
    apply lor_lt_pow; [| apply IH; intros y Hy; apply H; right; exact Hy].
    rewrite N.shiftl_1_l. apply N.pow_lt_mono_r; [lia |]. specialize (H x (or_introl eq_refl)). lia.
Qed.

Lemma mask_ge_pow : forall l c, In c l -> 2 ^ N.of_nat c <= rowmask l.
Proof.
  intros l c Hc. destruct (N.lt_ge_cases (rowmask l) (2 ^ N.of_nat c)) as [Hlt | Hge]; [exfalso | exact Hge].
  assert (Hb : N.testbit (rowmask l) (N.of_nat c) = true) by (rewrite rowmask_bit, Nat2N.id; apply inb_iff, Hc).
  destruct (N.eq_dec (rowmask l) 0) as [E | NE]; [rewrite E, N.bits_0 in Hb; discriminate |].
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

Lemma in_key : forall F y, In y (key F) <-> exists s, In s F /\ y = rowmask s.
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
  NoDup (map rowmask F) -> (S a < nl F)%nat -> ~ In a (concat F) ->
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
  assert (Hfix : forall s, In s F -> ~ In c s -> rowmask (map t s) = rowmask s).
  { intros s Hs Hcs. apply mask_ext. intros y. rewrite in_map_iff. split.
    - intros [z [<- Hz]]. rewrite Ht. unfold swf.
      destruct (Nat.eqb_spec z a) as [-> | _]; [exfalso; exact (Hna s Hs Hz) |].
      destruct (Nat.eqb_spec z c) as [-> | _]; [contradiction | exact Hz].
    - intros Hy. exists y; split; [| exact Hy]. rewrite Ht. unfold swf.
      destruct (Nat.eqb_spec y a) as [-> | _]; [exfalso; exact (Hna s Hs Hy) |].
      destruct (Nat.eqb_spec y c) as [-> | _]; [contradiction | reflexivity]. }
  assert (Hlow : forall s, In s F -> rowmask (map t s) < 2 ^ N.of_nat c \/ ~ In c s).
  { intros s Hs. destruct (in_dec Nat.eq_dec c s) as [Hcs | Hcs]; [left | right; exact Hcs].
    apply mask_lt_pow. intros y Hy. apply in_map_iff in Hy as [z [<- Hz]]. rewrite Ht. unfold swf.
    destruct (Nat.eqb_spec z a) as [-> | _]; [exfalso; exact (Hna s Hs Hz) |].
    destruct (Nat.eqb_spec z c) as [-> | Hzc]; [exact Hac |]. pose proof (Hlab s z Hs Hz). lia. }
  assert (Hlow' : forall s, In s F -> In c s -> rowmask (map t s) < 2 ^ N.of_nat c).
  { intros s Hs Hcs. destruct (Hlow s Hs) as [H | H]; [exact H | contradiction]. }
  (* the smallest changed row *)
  apply in_concat in Hc as [s0 [Hs0 Hcs0]].
  set (T := map (fun s => rowmask (map t s)) (filter (fun s => inb c s) F)).
  assert (HT0 : In (rowmask (map t s0)) T).
  { apply in_map_iff. exists s0; split; [reflexivity |]. apply filter_In; split; [exact Hs0 | apply inb_iff, Hcs0]. }
  destruct T as [| y0 rest] eqn:ET; [destruct HT0 |].
  destruct (minN_spec rest y0) as [Hxin Hxle]. set (x := minN y0 rest) in *.
  rewrite <- ET in Hxin, Hxle.
  assert (HxT : exists s1, In s1 F /\ In c s1 /\ x = rowmask (map t s1)).
  { unfold T in Hxin. apply in_map_iff in Hxin as [s1 [E Hs1]]. apply filter_In in Hs1 as [Hs1 Hc1].
    apply inb_iff in Hc1. exists s1; split; [exact Hs1 | split; [exact Hc1 | symmetry; exact E]]. }
  destruct HxT as [s1 [Hs1 [Hcs1 Ex]]].
  assert (Hxlow : x < 2 ^ N.of_nat c) by (rewrite Ex; apply Hlow', Hcs1; exact Hs1).
  assert (HxT' : forall s, In s F -> In c s -> x <= rowmask (map t s)).
  { intros s Hs Hcs. apply Hxle. unfold T. apply in_map_iff. exists s; split; [reflexivity |].
    apply filter_In; split; [exact Hs | apply inb_iff, Hcs]. }
  unfold improves.
  assert (HndA : NoDup (map rowmask (relab t F))).
  { unfold relab. rewrite map_map. apply (NoDup_map_transfer _ _ rowmask (fun s => rowmask (map t s)) F Hnd).
    intros u v _ _ E. apply (mask_map_inj t t Htt) in E; exact E. }
  apply (lexb_first_diff _ _ (sortN_ssorted _ HndA) (sortN_ssorted _ Hnd)) with (x := x).
  - unfold key. rewrite !length_sortN, !map_length. unfold relab; rewrite map_length; reflexivity.
  - apply in_key. exists (map t s1); split; [apply in_map, Hs1 | exact Ex].
  - intros Hin. apply in_key in Hin as [s [Hs E]].
    destruct (in_dec Nat.eq_dec c s) as [Hcs | Hcs].
    + pose proof (mask_ge_pow s c Hcs). lia.
    + apply (Hna s Hs). rewrite Ex in E. symmetry in E. apply mask_ext with (x := a) in E.
      apply E, in_map_iff. exists c; split; [| exact Hcs1]. rewrite Ht; unfold swf.
      destruct (Nat.eqb_spec c a) as [E' | _]; [lia | rewrite Nat.eqb_refl; reflexivity].
  - intros y Hy. change (In y (key (relab t F)) <-> In y (key F)). rewrite !in_key. split.
    + intros [s' [Hs' E]]. unfold relab in Hs'. apply in_map_iff in Hs' as [s [<- Hs]].
      destruct (in_dec Nat.eq_dec c s) as [Hcs | Hcs].
      * exfalso. pose proof (HxT' s Hs Hcs). lia.
      * exists s; split; [exact Hs | rewrite E; apply Hfix; assumption].
    + intros [s [Hs E]]. destruct (in_dec Nat.eq_dec c s) as [Hcs | Hcs].
      * exfalso. pose proof (mask_ge_pow s c Hcs). lia.
      * exists (map t s); split; [apply in_map, Hs | rewrite E; symmetry; apply Hfix; assumption].
Qed.

(** ** Nodes are sorted lists of masks *)

(** The row of a rowmask: its set bits, ascending. *)
Definition bits (m : N) : list nat := filter (fun i => N.testbit m (N.of_nat i)) (seq 0 (N.to_nat (N.size m))).

Lemma in_bits : forall m i, In i (bits m) <-> N.testbit m (N.of_nat i) = true.
Proof.
  intros m i; unfold bits; rewrite filter_In, in_seq. split; [tauto |].
  intros H; split; [| exact H]. split; [lia |].
  destruct (Nat.lt_ge_cases i (N.to_nat (N.size m))) as [Hi | Hi]; [exact Hi | exfalso].
  rewrite N.bits_above_log2 in H; [discriminate |].
  destruct (N.eq_dec m 0) as [-> | Hm]; [rewrite N.bits_0 in H; discriminate |].
  rewrite N.size_log2 in Hi by exact Hm. lia.
Qed.

Lemma mask_bits : forall m, rowmask (bits m) = m.
Proof.
  intros m. apply N.bits_inj_iff. intros n. rewrite rowmask_bit.
  destruct (inb (N.to_nat n) (bits m)) eqn:E.
  - apply inb_iff, in_bits in E. rewrite N2Nat.id in E. symmetry; exact E.
  - destruct (N.testbit m n) eqn:E'; [| reflexivity].
    exfalso. assert (H : In (N.to_nat n) (bits m)) by (apply in_bits; rewrite N2Nat.id; exact E').
    apply inb_iff in H. congruence.
Qed.

Lemma bits_NoDup : forall m, NoDup (bits m).
Proof. intros m. unfold bits. apply NoDup_filter, seq_NoDup. Qed.

Definition fam (K : list N) : list (list nat) := map bits K.

Lemma ssorted_snoc : forall A y, ssorted (A ++ [y]) -> ssorted A /\ (forall z, In z A -> z < y).
Proof.
  induction A as [| a A IH]; intros y H; simpl in *.
  - split; [constructor | intros z []].
  - inversion H as [| ? ? H' Ha]; subst. destruct (IH y H') as [HA Hy]. split.
    + constructor; [exact HA |]. rewrite Forall_forall in Ha |- *. intros z Hz; apply Ha, in_app_iff; left; exact Hz.
    + intros z [<- | Hz]; [| apply Hy, Hz]. rewrite Forall_forall in Ha. apply Ha, in_app_iff; right; left; reflexivity.
Qed.

Lemma sortN_sorted_id : forall K, ssorted K -> sortN K = K.
Proof.
  intros K. induction K as [| y K IH] using rev_ind; intros H; [reflexivity |].
  apply ssorted_snoc in H as [HK Hlt]. rewrite sortN_app1, IH by exact HK.
  apply insertN_max, Hlt.
Qed.

Lemma key_fam : forall K, ssorted K -> key (fam K) = K.
Proof.
  intros K H. unfold key, fam. rewrite map_map.
  rewrite (map_ext _ (fun x => x)) by (intros; apply mask_bits). rewrite map_id. apply sortN_sorted_id, H.
Qed.

(** ** Candidate rows: all [k]-ksubsets *)

Local Close Scope N_scope.

Fixpoint ksubsets (k : nat) (l : list nat) : list (list nat) :=
  match k, l with
  | 0, _ => [[]]
  | S _, [] => []
  | S k', x :: l' => map (cons x) (ksubsets k' l') ++ ksubsets k l'
  end.

Lemma length_remove_in : forall x r, NoDup r -> In x r -> length (remove Nat.eq_dec x r) = pred (length r).
Proof.
  intros x r; induction r as [| y r IH]; intros Hnd Hx; [destruct Hx |].
  inversion Hnd as [| ? ? Hy Hr]; subst. simpl. destruct (Nat.eq_dec x y) as [-> | Hxy].
  - rewrite notin_remove by exact Hy. reflexivity.
  - destruct Hx as [E | Hx]; [congruence |]. simpl. rewrite IH by assumption.
    destruct r; [destruct Hx | reflexivity].
Qed.

Lemma NoDup_remove_nat : forall x r, NoDup r -> NoDup (remove Nat.eq_dec x r).
Proof.
  intros x r; induction r as [| y r IH]; intros H; simpl; [constructor |].
  inversion H as [| ? ? Hy Hr]; subst. destruct (Nat.eq_dec x y) as [_ | _]; [apply IH, Hr |].
  constructor; [| apply IH, Hr]. intros Hin. apply in_remove in Hin as [Hin _]. contradiction.
Qed.

(** Every [k]-set inside [l] is, as a set, one of [ksubsets k l]. *)
Lemma subsets_complete : forall l r, NoDup l -> NoDup r -> incl r l ->
  exists s, In s (ksubsets (length r) l) /\ (forall z, In z s <-> In z r).
Proof.
  induction l as [| x l IH]; intros r Hl Hr Hinc.
  - destruct r as [| y r]; [| exfalso; apply (Hinc y); left; reflexivity].
    exists []; split; [left; reflexivity | tauto].
  - inversion Hl as [| ? ? Hx Hl']; subst.
    destruct r as [| y0 r0] eqn:Er.
    + exists []; split; [simpl; left; reflexivity | tauto].
    + rewrite <- Er in *. assert (Hlr : length r = S (length r0)) by (rewrite Er; reflexivity).
      rewrite Hlr; simpl.
      destruct (in_dec Nat.eq_dec x r) as [Hxr | Hxr].
      * set (r' := remove Nat.eq_dec x r).
        assert (Hr' : NoDup r') by (apply NoDup_remove_nat, Hr).
        assert (Hlen : length r' = length r0) by (unfold r'; rewrite length_remove_in, Hlr by assumption; reflexivity).
        assert (Hinc' : incl r' l).
        { intros z Hz. apply in_remove in Hz as [Hz Hzx]. destruct (Hinc z Hz) as [E | H]; [congruence | exact H]. }
        destruct (IH r' Hl' Hr' Hinc') as [s [Hs Hse]]. rewrite Hlen in Hs.
        exists (x :: s); split.
        -- apply in_app_iff; left. apply in_map, Hs.
        -- intros z; simpl; rewrite Hse. split.
           ++ intros [<- | Hz]; [exact Hxr | apply in_remove in Hz; tauto].
           ++ intros Hz. destruct (Nat.eq_dec x z) as [E | NE]; [left; exact E |].
              right. apply in_in_remove; [intro E; apply NE; symmetry; exact E | exact Hz].
      * assert (Hinc' : incl r l).
        { intros z Hz. destruct (Hinc z Hz) as [E | H]; [subst; contradiction | exact H]. }
        destruct (IH r Hl' Hr Hinc') as [s [Hs Hse]]. rewrite Hlr in Hs.
        exists s; split; [apply in_app_iff; right; exact Hs | exact Hse].
Qed.

(** ** The search, and its completeness

    Generic in the row size [b], in a property [P] of families that is
    kept when the last row is removed, in a test [validb] that accepts
    every node whose family has [P], and in the oracle.  [level n] is the
    list of nodes with [n] rows; a node is expanded only if the oracle
    has no checked witness against it ([keep]).  [level_complete]: every
    minimal node whose family has [P] is in its level and is kept,
    whatever the oracle answers. *)

Section Search.
  Variable b : nat.
  Variable P : list (list nat) -> Prop.
  Variable validb : list N -> bool.
  Hypothesis validb_complete : forall K, P (fam K) -> validb K = true.
  Hypothesis P_hered : forall K y, P (fam (K ++ [y])) -> P (fam K).
  Variable oracle : list N -> option (list nat).

  Definition cand (K : list N) : list N := map rowmask (ksubsets b (seq 0 (nl (fam K) + b))).

  Definition children (K : list N) : list (list N) :=
    map (fun y => K ++ [y]) (filter (fun y => forallb (fun z => (z <? y)%N) K && validb (K ++ [y])) (cand K)).

  Definition keep (K : list N) : bool :=
    match oracle K with
    | Some p => negb (is_permb p && Nat.eqb (length p) (nl (fam K)) && improves (pf p) (fam K))
    | None => true
    end.

  Fixpoint level (n : nat) : list (list N) :=
    match n with
    | 0 => [[]]
    | S n' => flat_map children (filter keep (level n'))
    end.

  (** Minimal: no permutation of its label range improves it. *)
  Definition MinK (K : list N) : Prop :=
    forall p, is_permb p = true -> length p = nl (fam K) -> improves (pf p) (fam K) = false.

  Lemma keep_min : forall K, MinK K -> keep K = true.
  Proof.
    intros K H. unfold keep. destruct (oracle K) as [p |]; [| reflexivity].
    destruct (is_permb p) eqn:Ep; [| reflexivity].
    destruct (Nat.eqb_spec (length p) (nl (fam K))) as [El | _]; [| reflexivity].
    rewrite (H p Ep El). reflexivity.
  Qed.

  Lemma nl_mono : forall F G, incl (concat F) (concat G) -> nl F <= nl G.
  Proof.
    intros F G H. destruct (nl F) as [| n] eqn:E; [lia |].
    assert (Hin : In (nl F - 1) (concat F)) by (apply nl_attained; lia).
    rewrite E in Hin. apply H, nl_bound in Hin. lia.
  Qed.

  Lemma rmapF_ext : forall g g' F, (forall x, g x = g' x) -> relab g F = relab g' F.
  Proof. intros g g' F H. unfold relab. apply map_ext. intros r. apply map_ext, H. Qed.

  Lemma improves_ext : forall g g' F, (forall x, g x = g' x) -> improves g F = improves g' F.
  Proof. intros g g' F H. unfold improves. rewrite (rmapF_ext g g' F H). reflexivity. Qed.

  Lemma ssorted_NoDup : forall K, ssorted K -> NoDup K.
  Proof.
    induction K as [| a K IH]; intros H; [constructor |].
    inversion H as [| ? ? HK Ha]; subst. constructor; [| apply IH, HK].
    intros Hin. rewrite Forall_forall in Ha. specialize (Ha a Hin). lia.
  Qed.

  Lemma map_mask_fam : forall K, map rowmask (fam K) = K.
  Proof.
    intros K. unfold fam. rewrite map_map. rewrite (map_ext _ (fun x => x)) by (intros; apply mask_bits). apply map_id.
  Qed.

  Lemma fam_app1 : forall K y, fam (K ++ [y]) = fam K ++ [bits y].
  Proof. intros K y; unfold fam; rewrite map_app; reflexivity. Qed.

  (** The parent of a minimal node is minimal. *)
  Lemma MinK_parent : forall K y, ssorted (K ++ [y]) -> MinK (K ++ [y]) -> MinK K.
  Proof.
    intros K y Hs Hmin p Hp Hl. destruct (improves (pf p) (fam K)) eqn:Ei; [exfalso | reflexivity].
    apply ssorted_snoc in Hs as [HK Hy].
    set (m := nl (fam (K ++ [y])) - length p).
    assert (Hle : nl (fam K) <= nl (fam (K ++ [y]))).
    { apply nl_mono. unfold fam; rewrite map_app, concat_app. intros z Hz; apply in_app_iff; left; exact Hz. }
    set (p' := p ++ seq (length p) m).
    assert (Hp' : is_permb p' = true) by apply is_permb_extend, Hp.
    assert (Hl' : length p' = nl (fam (K ++ [y]))) by (unfold p', m; rewrite app_length, seq_length; lia).
    assert (Hi : improves (pf p') (fam K) = true) by (rewrite (improves_ext _ (pf p)) by apply pf_extend; exact Ei).
    assert (Hi' : improves (pf p') (fam K ++ [bits y]) = true).
    { apply (parent_improves (pf p') (pinv p') (pinv_pf p' Hp')); [| exact Hi].
      intros s Hs. unfold fam in Hs. apply in_map_iff in Hs as [z [<- Hz]]. rewrite !mask_bits. apply Hy, Hz. }
    rewrite <- fam_app1 in Hi'. rewrite (Hmin p' Hp' Hl') in Hi'. discriminate.
  Qed.

  (** A minimal node uses every label below [nl]. *)
  Lemma MinK_no_gap : forall K, ssorted K -> MinK K -> forall i, i < nl (fam K) -> In i (concat (fam K)).
  Proof.
    intros K Hs Hmin i Hi. destruct (in_dec Nat.eq_dec i (concat (fam K))) as [H | H]; [exact H | exfalso].
    destruct (Nat.eq_dec i (nl (fam K) - 1)) as [E | NE].
    - apply H. rewrite E. apply nl_attained. lia.
    - assert (Hg := gap_improves (fam K) i).
      rewrite map_mask_fam in Hg. specialize (Hg (ssorted_NoDup K Hs) ltac:(lia) H).
      rewrite (Hmin _ (swp_perm (nl (fam K)) i (nl (fam K) - 1) ltac:(lia) ltac:(lia))) in Hg; [discriminate |].
      unfold swp; rewrite map_length, seq_length; reflexivity.
  Qed.

  (** The largest row of a minimal node is a candidate of its parent. *)
  Lemma last_in_cand : forall K y, ssorted (K ++ [y]) -> MinK (K ++ [y]) -> length (bits y) = b ->
    In y (cand K).
  Proof.
    intros K y Hs Hmin Hb.
    assert (HminK : MinK K) by (apply (MinK_parent K y Hs Hmin)).
    set (v := nl (fam K)). set (w := nl (fam (K ++ [y]))).
    assert (Hcat : concat (fam (K ++ [y])) = concat (fam K) ++ bits y) by (unfold fam; rewrite map_app, concat_app; simpl; rewrite app_nil_r; reflexivity).
    (* the labels in [v, w) are all in the new row *)
    assert (Hnew : incl (seq v (w - v)) (bits y)).
    { intros i Hi. apply in_seq in Hi.
      assert (Hu : In i (concat (fam (K ++ [y])))) by (apply (MinK_no_gap _ Hs Hmin); lia).
      rewrite Hcat in Hu. apply in_app_iff in Hu as [Hu | Hu]; [| exact Hu].
      apply nl_bound in Hu. fold v in Hu. lia. }
    assert (Hw : w <= v + b).
    { pose proof (NoDup_incl_length (seq_NoDup (w - v) v) Hnew) as H. rewrite seq_length, Hb in H. lia. }
    assert (Hrow : incl (bits y) (seq 0 (v + b))).
    { intros i Hi. apply in_seq. split; [lia |].
      assert (Hu : In i (concat (fam (K ++ [y])))) by (rewrite Hcat; apply in_app_iff; right; exact Hi).
      apply nl_bound in Hu. fold w in Hu. lia. }
    destruct (subsets_complete (seq 0 (v + b)) (bits y) (seq_NoDup _ _) (bits_NoDup y) Hrow) as [s [Hs' Hse]].
    rewrite Hb in Hs'. unfold cand. fold v. apply in_map_iff. exists s; split; [| exact Hs'].
    rewrite <- (mask_bits y). apply mask_ext, Hse.
  Qed.

  Theorem level_complete : forall K, ssorted K -> (forall m, In m K -> length (bits m) = b) ->
    P (fam K) -> MinK K -> In K (level (length K)) /\ keep K = true.
  Proof.
    induction K as [| y K IH] using rev_ind; intros Hs Hb HP Hmin.
    - split; [left; reflexivity | apply keep_min, Hmin].
    - split; [| apply keep_min, Hmin].
      assert (HK := Hs). apply ssorted_snoc in HK as [HK Hy].
      destruct (IH HK (fun m Hm => Hb m (proj2 (in_app_iff _ _ _) (or_introl Hm))) (P_hered K y HP)
                  (MinK_parent K y Hs Hmin)) as [Hin Hkeep].
      rewrite app_length, Nat.add_comm. simpl.
      apply in_flat_map. exists K; split; [apply filter_In; split; assumption |].
      unfold children. apply in_map_iff. exists y; split; [reflexivity |].
      apply filter_In; split.
      + apply last_in_cand; [exact Hs | exact Hmin | apply Hb, in_app_iff; right; left; reflexivity].
      + apply andb_true_iff; split; [| apply validb_complete, HP].
        apply forallb_forall. intros z Hz. apply N.ltb_lt, Hy, Hz.
  Qed.
End Search.

(** ** Every family has a minimal relabelling

    The relabelling with the least key among all permutations of the
    label range ([argmin]) is minimal ([MinK]): any improvement of it
    would compose to a permutation beating the least key. *)

Lemma lexb_trans : forall A B C, lexb A B = true -> lexb B C = true -> lexb A C = true.
Proof.
  induction A as [| a A IH]; intros [| b B] [| c C] H1 H2; simpl in *; try discriminate.
  apply orb_true_iff in H1 as [H1 | H1]; apply orb_true_iff in H2 as [H2 | H2].
  - apply N.ltb_lt in H1, H2. apply orb_true_iff; left; apply N.ltb_lt; lia.
  - apply andb_true_iff in H2 as [E _]. apply N.eqb_eq in E; subst. rewrite H1; reflexivity.
  - apply andb_true_iff in H1 as [E _]. apply N.eqb_eq in E; subst. rewrite H2; reflexivity.
  - apply andb_true_iff in H1 as [E1 H1]; apply andb_true_iff in H2 as [E2 H2].
    apply N.eqb_eq in E1, E2; subst. rewrite N.ltb_irrefl, N.eqb_refl, (IH B C H1 H2). reflexivity.
Qed.

(** Strictly sorted lists with the same elements are equal. *)
Lemma ssorted_ext : forall A B, ssorted A -> ssorted B -> (forall x, In x A <-> In x B) -> A = B.
Proof.
  induction A as [| a A IH]; intros [| b B] HA HB H.
  - reflexivity.
  - exfalso. apply (proj2 (H b)). left; reflexivity.
  - exfalso. apply (proj1 (H a)). left; reflexivity.
  - inversion HA as [| ? ? HA' Ha]; inversion HB as [| ? ? HB' Hb]; subst. rewrite Forall_forall in Ha, Hb.
    assert (Eab : a = b).
    { destruct (proj1 (H a) (or_introl eq_refl)) as [E | Ha']; [symmetry; exact E |].
      destruct (proj2 (H b) (or_introl eq_refl)) as [E | Hb']; [exact E |].
      pose proof (Hb a Ha'); pose proof (Ha b Hb'); lia. }
    subst b. f_equal. apply IH; [exact HA' | exact HB' |]. intros x. split; intros Hx.
    + destruct (proj1 (H x) (or_intror Hx)) as [E | Hx']; [subst; pose proof (Ha x Hx); lia | exact Hx'].
    + destruct (proj2 (H x) (or_intror Hx)) as [E | Hx']; [subst; pose proof (Hb x Hx); lia | exact Hx'].
Qed.

(** The key of a family depends only on the set of its rows' masks. *)
Lemma key_ext : forall F G, NoDup (map rowmask F) -> NoDup (map rowmask G) ->
  (forall m, In m (map rowmask F) <-> In m (map rowmask G)) -> key F = key G.
Proof.
  intros F G HF HG H. apply ssorted_ext; [apply sortN_ssorted, HF | apply sortN_ssorted, HG |].
  intros x. unfold key. rewrite !in_sortN. apply H.
Qed.

From Coq Require Import Permutation.

Lemma lexb_total : forall A B, length A = length B -> A = B \/ lexb A B = true \/ lexb B A = true.
Proof.
  induction A as [| a A IH]; intros [| b B] H; simpl in H; try discriminate; [left; reflexivity |].
  simpl. destruct (N.lt_trichotomy a b) as [Hab | [-> | Hab]].
  - right; left. apply orb_true_iff; left; apply N.ltb_lt, Hab.
  - rewrite N.ltb_irrefl, N.eqb_refl. simpl.
    destruct (IH B ltac:(lia)) as [-> | [H1 | H1]]; [left; reflexivity | right; left; exact H1 | right; right; exact H1].
  - right; right. apply orb_true_iff; left; apply N.ltb_lt, Hab.
Qed.

Fixpoint inserts (x : nat) (l : list nat) : list (list nat) :=
  match l with
  | [] => [[x]]
  | y :: l' => (x :: l) :: map (cons y) (inserts x l')
  end.

Fixpoint perms (l : list nat) : list (list nat) :=
  match l with [] => [[]] | x :: l' => flat_map (inserts x) (perms l') end.

Lemma in_inserts : forall x p1 p2, In (p1 ++ x :: p2) (inserts x (p1 ++ p2)).
Proof.
  intros x p1 p2; induction p1 as [| y p1 IH]; simpl.
  - destruct p2; simpl; left; reflexivity.
  - right. apply in_map, IH.
Qed.

Lemma inserts_perm : forall x l q, In q (inserts x l) -> Permutation (x :: l) q.
Proof.
  intros x l; induction l as [| y l IH]; intros q H; simpl in H.
  - destruct H as [<- | []]. reflexivity.
  - destruct H as [<- | H]; [reflexivity |].
    apply in_map_iff in H as [q' [<- Hq']]. specialize (IH q' Hq').
    transitivity (y :: x :: l); [apply perm_swap | apply perm_skip, IH].
Qed.

Lemma perms_complete : forall l p, Permutation l p -> In p (perms l).
Proof.
  induction l as [| x l IH]; intros p H.
  - apply Permutation_nil in H. subst. left; reflexivity.
  - assert (Hx : In x p) by (apply (Permutation_in x H); left; reflexivity).
    apply in_split in Hx as [p1 [p2 ->]].
    apply Permutation_cons_app_inv in H. simpl. apply in_flat_map.
    exists (p1 ++ p2); split; [apply IH, H | apply in_inserts].
Qed.

Lemma perms_sound : forall l p, In p (perms l) -> Permutation l p.
Proof.
  induction l as [| x l IH]; intros p H; simpl in H.
  - destruct H as [<- | []]. reflexivity.
  - apply in_flat_map in H as [q [Hq Hp]]. apply inserts_perm in Hp.
    transitivity (x :: q); [apply perm_skip, IH, Hq | exact Hp].
Qed.

Lemma is_permb_seq : forall p, is_permb p = true -> Permutation (seq 0 (length p)) p.
Proof.
  intros p H. destruct (is_permb_spec p H) as [Hnd [Hlt Hin]].
  apply NoDup_Permutation; [apply seq_NoDup | exact Hnd |].
  intros x. rewrite in_seq. split; [intros [_ Hx]; apply Hin, Hx | intros Hx; split; [lia | apply Hlt, Hx]].
Qed.

Lemma seq_is_permb : forall p, Permutation (seq 0 (length p)) p -> is_permb p = true.
Proof.
  intros p H. unfold is_permb. apply andb_true_iff; split.
  - apply forallb_forall. intros i Hi. apply Nat.ltb_lt.
    apply (Permutation_in i (Permutation_sym H)) in Hi. apply in_seq in Hi. lia.
  - apply NoDup_nodupb. apply (Permutation_NoDup H), seq_NoDup.
Qed.

(** Composition of witnesses of the same length. *)
Definition comp (q p : list nat) : list nat := map (pf q) p.

Lemma pf_lt : forall p x, is_permb p = true -> x < length p -> pf p x < length p.
Proof.
  intros p x H Hx. destruct (is_permb_spec p H) as [_ [Hlt _]]. unfold pf.
  apply Nat.ltb_lt in Hx as Hx'. rewrite Hx'. apply Hlt, nth_In, Hx.
Qed.

Lemma pf_comp : forall q p, length q = length p -> forall x, pf (comp q p) x = pf q (pf p x).
Proof.
  intros q p Hl x. unfold pf at 1 3, comp. rewrite map_length.
  destruct (Nat.ltb_spec x (length p)) as [Hx | Hx].
  - rewrite (nth_indep _ 0 (pf q 0)) by (rewrite map_length; exact Hx). rewrite map_nth. reflexivity.
  - unfold pf. rewrite Hl. apply Nat.ltb_ge in Hx as Hx'. rewrite Hx'. reflexivity.
Qed.

Lemma comp_is_permb : forall q p, is_permb q = true -> is_permb p = true -> length q = length p ->
  is_permb (comp q p) = true.
Proof.
  intros q p Hq Hp Hl. destruct (is_permb_spec p Hp) as [Hnd [Hlt _]].
  unfold is_permb, comp. apply andb_true_iff; split.
  - apply forallb_forall. intros i Hi. apply in_map_iff in Hi as [j [<- Hj]]. apply Nat.ltb_lt.
    rewrite map_length, <- Hl. apply pf_lt; [exact Hq | rewrite Hl; apply Hlt, Hj].
  - apply NoDup_nodupb. apply FinFun.Injective_map_NoDup; [| exact Hnd].
    intros x y E. rewrite <- (pinv_pf q Hq x), E, pinv_pf by exact Hq. reflexivity.
Qed.

Definition rkey (F : list (list nat)) (p : list nat) : list N := key (relab (pf p) F).

Fixpoint argmin (F : list (list nat)) (best : list nat) (l : list (list nat)) : list nat :=
  match l with
  | [] => best
  | p :: l' => argmin F (if lexb (rkey F p) (rkey F best) then p else best) l'
  end.

Lemma rkey_length : forall F p, length (rkey F p) = length F.
Proof. intros F p. unfold rkey, key, relab. rewrite length_sortN, !map_length. reflexivity. Qed.

Lemma argmin_spec : forall F l best,
  In (argmin F best l) (best :: l) /\
  (forall p, In p (best :: l) -> lexb (rkey F p) (rkey F (argmin F best l)) = false).
Proof.
  intros F l; induction l as [| p0 l IH]; intros best; simpl.
  - split; [left; reflexivity | intros p [E | []]; subst; apply lexb_irrefl].
  - destruct (lexb (rkey F p0) (rkey F best)) eqn:Ep0.
    + destruct (IH p0) as [Hin Hle]. set (m := argmin F p0 l) in *. split.
      * destruct Hin as [E | Hin]; [right; left; exact E | right; right; exact Hin].
      * intros p Hp'. destruct Hp' as [E | [E | Hp]]; [subst p | subst p |].
        -- destruct (lexb (rkey F best) (rkey F m)) eqn:E; [exfalso | reflexivity].
           pose proof (lexb_trans _ _ _ Ep0 E) as H. rewrite (Hle p0 (or_introl eq_refl)) in H. discriminate.
        -- apply Hle; left; reflexivity.
        -- apply Hle; right; exact Hp.
    + destruct (IH best) as [Hin Hle]. set (m := argmin F best l) in *. split.
      * destruct Hin as [E | Hin]; [left; exact E | right; right; exact Hin].
      * intros p Hp'. destruct Hp' as [E | [E | Hp]]; [subst p | subst p |].
        -- apply Hle; left; reflexivity.
        -- destruct (lexb (rkey F p0) (rkey F m)) eqn:E; [exfalso | reflexivity].
           pose proof (Hle best (or_introl eq_refl)) as Hb.
           destruct (lexb_total (rkey F p0) (rkey F best) ltac:(rewrite !rkey_length; reflexivity)) as [Eq | [H1 | H1]].
           ++ rewrite Eq, Hb in E. discriminate.
           ++ congruence.
           ++ pose proof (lexb_trans _ _ _ H1 E) as H2. rewrite Hb in H2. discriminate.
        -- apply Hle; right; exact Hp.
Qed.

Lemma seteq_map : forall (g : nat -> nat) a b, (forall z, In z a <-> In z b) ->
  forall y, In y (map g a) <-> In y (map g b).
Proof.
  intros g a b H y. rewrite !in_map_iff. split; intros [z [E Hz]]; exists z; split; try exact E; apply H, Hz.
Qed.

Lemma bits_mask_seteq : forall s z, In z (bits (rowmask s)) <-> In z s.
Proof. intros s. apply mask_ext. rewrite mask_bits. reflexivity. Qed.

Theorem minimal_relabel : forall F, NoDup (map rowmask F) ->
  exists p, is_permb p = true /\ length p = nl F /\ MinK (key (relab (pf p) F)).
Proof.
  intros F HF.
  set (v := nl F). set (l := perms (seq 0 v)). set (ps := argmin F (seq 0 v) l).
  destruct (argmin_spec F l (seq 0 v)) as [Hin Hle]. fold ps in Hin, Hle.
  assert (Hps : Permutation (seq 0 v) ps) by (destruct Hin as [E | Hin]; [rewrite <- E; reflexivity | apply perms_sound, Hin]).
  assert (Hlen : length ps = v) by (rewrite <- (Permutation_length Hps), seq_length; reflexivity).
  assert (Hpp : is_permb ps = true) by (apply seq_is_permb; rewrite Hlen; exact Hps).
  exists ps; split; [exact Hpp | split; [exact Hlen |]].
  set (K := key (relab (pf ps) F)).
  assert (HndA : NoDup (map rowmask (relab (pf ps) F))).
  { unfold relab; rewrite map_map. apply (NoDup_map_transfer _ _ rowmask _ F HF).
    intros u w _ _ E. apply (mask_map_inj (pf ps) (pinv ps) (pinv_pf ps Hpp)), E. }
  assert (HK : ssorted K) by (apply sortN_ssorted, HndA).
  intros q Hq Hlq. destruct (improves (pf q) (fam K)) eqn:Ei; [exfalso | reflexivity].
  (* the labels of [K] are below [v] *)
  assert (Hlab : forall x, In x (concat (fam K)) -> x < v).
  { intros x Hx. apply in_concat in Hx as [t [Ht Hx]]. unfold fam in Ht. apply in_map_iff in Ht as [k [<- Hk]].
    apply in_key in Hk as [s [Hs Ek]]. unfold relab in Hs. apply in_map_iff in Hs as [s0 [<- Hs0]].
    rewrite Ek in Hx. apply bits_mask_seteq, in_map_iff in Hx as [y [<- Hy]].
    rewrite <- Hlen. apply pf_lt; [exact Hpp |]. rewrite Hlen. apply nl_bound, in_concat. exists s0; split; assumption. }
  assert (Hnl : nl (fam K) <= v).
  { destruct (nl (fam K)) as [| n] eqn:E; [lia |].
    assert (Ha : In (nl (fam K) - 1) (concat (fam K))) by (apply nl_attained; lia).
    apply Hlab in Ha. lia. }
  set (q' := q ++ seq (length q) (v - length q)).
  assert (Hq' : is_permb q' = true) by (apply is_permb_extend, Hq).
  assert (Hlq' : length q' = v) by (unfold q'; rewrite app_length, seq_length; lia).
  assert (Hqq : forall x, pf q' x = pf q x) by (intros x; apply pf_extend).
  set (r := comp q' ps).
  assert (Hr : is_permb r = true) by (apply comp_is_permb; [exact Hq' | exact Hpp | lia]).
  assert (Hlr : length r = v) by (unfold r, comp; rewrite map_length; exact Hlen).
  assert (Hrl : In r (seq 0 v :: l)) by (right; apply perms_complete; rewrite <- Hlr; apply is_permb_seq, Hr).
  specialize (Hle r Hrl).
  assert (Hrf : forall x, pf r x = pf q (pf ps x)) by (intros x; unfold r; rewrite pf_comp by lia; apply Hqq).
  unfold improves in Ei. rewrite key_fam in Ei by exact HK.
  assert (Ek : key (relab (pf q) (fam K)) = rkey F r).
  { apply key_ext.
    - unfold relab; rewrite map_map. apply (NoDup_map_transfer _ _ rowmask _ (fam K)).
      + rewrite map_mask_fam. apply ssorted_NoDup, HK.
      + intros u w _ _ E. apply (mask_map_inj (pf q) (pinv q) (pinv_pf q Hq)), E.
    - unfold relab; rewrite map_map. apply (NoDup_map_transfer _ _ rowmask _ F HF).
      intros u w _ _ E. apply (mask_map_inj (pf r) (pinv r) (pinv_pf r Hr)), E.
    - intros m. rewrite !in_map_iff. split.
      + intros [s' [Em Hs']]. unfold relab in Hs'. apply in_map_iff in Hs' as [t [<- Ht]].
        unfold fam in Ht. apply in_map_iff in Ht as [k [<- Hk]].
        apply in_key in Hk as [s [Hs Ek]]. unfold relab in Hs. apply in_map_iff in Hs as [s0 [<- Hs0]].
        exists (map (pf r) s0); split; [| apply in_map, Hs0]. rewrite <- Em. apply mask_ext. intros y.
        rewrite (seteq_map (pf q) (bits k) (map (pf ps) s0)) by (intros z; rewrite Ek; apply bits_mask_seteq).
        rewrite map_map. rewrite (map_ext (pf r) (fun x => pf q (pf ps x))) by exact Hrf. reflexivity.
      + intros [s' [Em Hs']]. unfold relab in Hs'. apply in_map_iff in Hs' as [s0 [<- Hs0]].
        set (k := rowmask (map (pf ps) s0)).
        exists (map (pf q) (bits k)); split.
        * rewrite <- Em. apply mask_ext. intros y.
          rewrite (seteq_map (pf q) (bits k) (map (pf ps) s0)) by (intros z; apply bits_mask_seteq).
          rewrite map_map. rewrite (map_ext (pf r) (fun x => pf q (pf ps x))) by exact Hrf. reflexivity.
        * unfold relab. apply in_map. unfold fam. apply in_map. apply in_key.
          exists (map (pf ps) s0); split; [apply in_map, Hs0 | reflexivity]. }
  rewrite Ek in Ei. unfold rkey in Hle at 2. fold K in Hle. congruence.
Qed.
