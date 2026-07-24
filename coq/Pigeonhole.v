(** * Pigeonhole.v -- The counting lemma used by Erdős–Rado.

    [pigeonhole_family]: if every set in a family [F] meets a finite set
    [X], and [|F| > |X| * K], then some element [x ∈ X] is contained in
    strictly more than [K] sets of [F].

    The proof is by induction on [X]. No external dependencies beyond
    [Sets.v]. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets.
Import ListNotations.

Set Implicit Arguments.

(** ** Basic length bound on filter (stdlib's filter_length is the
    partition identity, which lia doesn't see through easily). *)

Lemma length_filter_le :
  forall {A : Type} (f : A -> bool) (l : list A),
    length (filter f l) <= length l.
Proof.
  intros A f l; induction l as [|a l IH]; simpl; [lia|].
  destruct (f a); simpl; lia.
Qed.

(** ** A partition identity on list length *)

Lemma length_filter_partition :
  forall {A : Type} (f : A -> bool) (l : list A),
    length l = length (filter f l) + length (filter (fun x => negb (f x)) l).
Proof.
  intros A f l; induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (f a); simpl; lia.
Qed.

(** ** Filtering by membership preserves containment under sub-filtering *)

Lemma filter_memb_subfilter :
  forall (x : nat) (F : list (list nat)) (g : list nat -> bool),
    length (filter (fun A => memb x A) (filter g F))
    <= length (filter (fun A => memb x A) F).
Proof.
  intros x F g; induction F as [|A F IH]; simpl; [lia|].
  destruct (g A) eqn:HgA; simpl.
  - destruct (memb x A); simpl; lia.
  - destruct (memb x A); simpl; lia.
Qed.

(** ** Main pigeonhole lemma

    Hypotheses:
      - every set [A ∈ F] contains some element of [X];
      - [|F| > |X| * K].
    Conclusion: some [x ∈ X] is in more than [K] sets of [F].          *)

Theorem pigeonhole_family :
  forall (F : list (list nat)) (X : list nat) (K : nat),
    (forall A, In A F -> exists x, In x A /\ In x X) ->
    length F > length X * K ->
    exists x, In x X /\
              length (filter (fun A => memb x A) F) > K.
Proof.
  intros F X. revert F.
  induction X as [|x0 X' IH]; intros F K Hcover Hsize.
  - (* X = [] : every A meets [], impossible if F nonempty *)
    simpl in Hsize.
    destruct F as [|A F]; [simpl in Hsize; lia|].
    destruct (Hcover A (or_introl eq_refl)) as [x [_ Hx]].
    inversion Hx.
  - (* X = x0 :: X' *)
    simpl in Hsize.
    destruct (le_lt_dec
                (length (filter (fun A => memb x0 A) F))
                K) as [Hlow | Hhigh].
    + (* count of x0 is small : recurse on F' := F minus sets containing x0 *)
      pose (F' := filter (fun A => negb (memb x0 A)) F).
      assert (HsizeF : length F = length (filter (fun A => memb x0 A) F)
                                  + length F').
      { apply length_filter_partition. }
      assert (HsizeF' : length F' > length X' * K) by lia.
      assert (Hcover' : forall A, In A F' ->
                                  exists x, In x A /\ In x X').
      { unfold F'; intros A HA. apply filter_In in HA as [HAF Hneg].
        apply Bool.negb_true_iff in Hneg.
        rewrite memb_false_iff in Hneg.
        destruct (Hcover A HAF) as [x [HxA HxX]].
        destruct HxX as [E | HxX'].
        - subst x; contradiction.
        - exists x; auto. }
      destruct (IH F' K Hcover' HsizeF') as [x [HxX' Hcount]].
      exists x. split; [right; exact HxX'|].
      eapply Nat.lt_le_trans; [exact Hcount|].
      apply filter_memb_subfilter.
    + (* count of x0 is already > K : take x = x0 *)
      exists x0; split; [left; reflexivity | exact Hhigh].
Qed.

(** ** Helper: the family restricted to sets containing [x] *)

Definition contains_x (x : nat) (F : list (list nat)) : list (list nat) :=
  filter (fun A => memb x A) F.

Lemma contains_x_correct : forall x F A,
    In A (contains_x x F) <-> In A F /\ In x A.
Proof.
  intros; unfold contains_x; rewrite filter_In; split; intros [Ha Hb].
  - rewrite memb_true_iff in Hb; split; auto.
  - split; [exact Ha | apply memb_true_iff; exact Hb].
Qed.

Lemma contains_x_length : forall x F,
    length (contains_x x F) = length (filter (fun A => memb x A) F).
Proof. reflexivity. Qed.
