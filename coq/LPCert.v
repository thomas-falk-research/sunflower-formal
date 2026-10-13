(** * LPCert: kernel-checked bounds for integer linear programs

    A small, self-contained checker, independent of the rest of this
    library.  Variables are integers, [x : nat -> Z].  The constraints are
    integer linear rows [a·x ≤ b], given by any function [rowf] from a tag
    type (an explicit list of rows is the case [tag := nat], [rowf := nth]).
    A certificate is a tree:

    - a node branches on an integer linear form: [a·x ≤ f] on the left,
      [a·x ≥ f + 1] on the right, so the two children cover every integer
      point of the parent;
    - a leaf gives a scale [K ≥ 0] and multipliers [y ≥ 0] on rows in force
      (the problem's rows and the branching rows on the path), with
      [K·c_j = (Σ y·a)_j] for every variable [j], or [K·c_j ≤ (Σ y·a)_j]
      for a variable declared nonnegative ([nonneg j = true]), and
      [Σ y·b < K·T].

    [tree_sound]: if [check] accepts a tree for [c] and [T], every integer
    point satisfying all the rows, and nonnegative on the declared
    variables, has [c·x < T]; a tree all of whose leaves have [K = 0]
    proves that there is no such point.  The arithmetic is
    exact ([Z]); there is no floating point and nothing is assumed. *)

From Coq Require Import ZArith List Lia Bool FMapPositive.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Sparse vectors and their values *)

Definition svec := list (nat * Z).

(** [dot v x]: the value of the linear form [v] at [x].  Repeated indices
    add up. *)
Definition dot (v : svec) (x : nat -> Z) : Z :=
  fold_right (fun p s => snd p * x (fst p) + s) 0 v.

(** The coefficient of [x_j] in [v]. *)
Fixpoint sget (v : svec) (j : nat) : Z :=
  match v with
  | [] => 0
  | p :: v' => (if Nat.eqb (fst p) j then snd p else 0) + sget v' j
  end.

Definition zsum (l : list Z) : Z := fold_right Z.add 0 l.

(** All indices of [v] are below [n]. *)
Definition idx_ok (n : nat) (v : svec) : bool := forallb (fun p => Nat.ltb (fst p) n) v.

Definition neg (v : svec) : svec := map (fun p => (fst p, - snd p)) v.

Lemma zsum_cons : forall a l, zsum (a :: l) = a + zsum l.
Proof. reflexivity. Qed.

Lemma zsum_app : forall l1 l2, zsum (l1 ++ l2) = zsum l1 + zsum l2.
Proof. induction l1 as [| a l1 IH]; intros l2; simpl; [lia | unfold zsum in *; simpl; rewrite IH; lia]. Qed.

Lemma zsum_map_add : forall {A} (f g : A -> Z) l,
  zsum (map (fun a => f a + g a) l) = zsum (map f l) + zsum (map g l).
Proof. intros A f g l; induction l as [| a l IH]; [reflexivity | cbn [map]; rewrite !zsum_cons, IH; lia]. Qed.

Lemma zsum_map_ext : forall {A} (f g : A -> Z) l,
  (forall a, In a l -> f a = g a) -> zsum (map f l) = zsum (map g l).
Proof.
  intros A f g l H; induction l as [| a l IH]; [reflexivity |].
  cbn [map]; rewrite !zsum_cons, (H a (or_introl eq_refl)), IH; [reflexivity |].
  intros b Hb; apply H; right; exact Hb.
Qed.

Lemma zsum_map_zero : forall {A} (l : list A), zsum (map (fun _ => 0) l) = 0.
Proof. intros A l; induction l as [| a l IH]; [reflexivity | cbn [map]; rewrite zsum_cons, IH; reflexivity]. Qed.

Lemma zsum_map_scale : forall {A} (k : Z) (f : A -> Z) l,
  zsum (map (fun a => k * f a) l) = k * zsum (map f l).
Proof. intros A k f l; induction l as [| a l IH]; [simpl; lia | cbn [map]; rewrite !zsum_cons, IH; lia]. Qed.

Lemma zsum_map_le : forall {A} (f g : A -> Z) l,
  (forall a, In a l -> f a <= g a) -> zsum (map f l) <= zsum (map g l).
Proof.
  intros A f g l H; induction l as [| a l IH]; [simpl; lia |].
  cbn [map]; rewrite !zsum_cons.
  pose proof (H a (or_introl eq_refl)). assert (zsum (map f l) <= zsum (map g l)) by (apply IH; intros b Hb; apply H; right; exact Hb). lia.
Qed.

Lemma zsum_exchange : forall {A B} (g : A -> B -> Z) (la : list A) (lb : list B),
  zsum (map (fun a => zsum (map (fun b => g a b) lb)) la)
  = zsum (map (fun b => zsum (map (fun a => g a b) la)) lb).
Proof.
  intros A B g la lb; induction la as [| a la IH].
  - cbn [map]. change (zsum []) with 0. symmetry.
    induction lb as [| b lb IHb]; [reflexivity | cbn [map]; rewrite zsum_cons, IHb; reflexivity].
  - cbn [map]. rewrite zsum_cons, IH.
    rewrite (zsum_map_ext (fun b => zsum (map (fun a0 => g a0 b) (a :: la)))
                          (fun b => g a b + zsum (map (fun a0 => g a0 b) la))) by reflexivity.
    rewrite zsum_map_add; reflexivity.
Qed.

Lemma dot_neg : forall v x, dot (neg v) x = - dot v x.
Proof. intros v x; induction v as [| [i a] v IH]; simpl; [reflexivity | unfold dot in *; simpl in *; rewrite IH; lia]. Qed.

(** One coefficient, summed over [0..n-1]. *)
Lemma zsum_indicator : forall (i : nat) (a : Z) (x : nat -> Z) (l : list nat),
  NoDup l -> In i l ->
  zsum (map (fun j => (if Nat.eqb i j then a else 0) * x j) l) = a * x i.
Proof.
  intros i a x l Hnd Hin; induction l as [| j l IH]; [inversion Hin |].
  inversion Hnd as [| ? ? Hj Hnd']; subst. cbn [map]; rewrite zsum_cons.
  destruct (Nat.eqb_spec i j) as [E | NE].
  - subst j. rewrite (zsum_map_ext _ (fun _ => 0)); [rewrite zsum_map_zero; lia |].
    intros k Hk. destruct (Nat.eqb_spec i k); [subst; contradiction | lia].
  - destruct Hin as [E | Hin]; [subst; contradiction |]. rewrite IH by assumption. lia.
Qed.

(** A form with indices below [n] is the dense sum over [0..n-1]. *)
Lemma dot_dense : forall n v x, idx_ok n v = true ->
  dot v x = zsum (map (fun j => sget v j * x j) (seq 0 n)).
Proof.
  intros n v x Hok; induction v as [| [i a] v IH].
  - change (dot [] x) with 0.
    rewrite (zsum_map_ext (fun j => sget [] j * x j) (fun _ => 0)) by (intros; reflexivity).
    rewrite zsum_map_zero; reflexivity.
  - unfold idx_ok in Hok; simpl in Hok; apply andb_true_iff in Hok as [Hi Hok].
    apply Nat.ltb_lt in Hi.
    change (dot ((i, a) :: v) x) with (a * x i + dot v x). rewrite IH by exact Hok.
    cbn [sget fst snd].
    rewrite (zsum_map_ext (fun j => ((if Nat.eqb i j then a else 0) + sget v j) * x j)
                          (fun j => (if Nat.eqb i j then a else 0) * x j + sget v j * x j)) by (intros; lia).
    rewrite zsum_map_add, zsum_indicator; [reflexivity | apply seq_NoDup | apply in_seq; lia].
Qed.

(** ** Accumulating sparse vectors

    The leaf check adds up its rows into a finite map from indices to
    coefficients ([PositiveMap], index [j] at key [Pos.of_succ_nat j]), at
    a cost of [O(log n)] per stored coefficient, and then reads one
    coefficient per variable.  [zget_zcomb] says what the map holds: the
    coefficient-wise sum, in terms of [sget]. *)

Definition zmap := PositiveMap.t Z.

Definition zget (m : zmap) (j : nat) : Z :=
  match PositiveMap.find (Pos.of_succ_nat j) m with Some z => z | None => 0 end.

Definition zadd (m : zmap) (j : nat) (a : Z) : zmap :=
  PositiveMap.add (Pos.of_succ_nat j) (zget m j + a) m.

(** [m + y·v] *)
Fixpoint zaddv (y : Z) (v : svec) (m : zmap) : zmap :=
  match v with [] => m | p :: v' => zaddv y v' (zadd m (fst p) (y * snd p)) end.

Lemma zget_empty : forall j, zget (PositiveMap.empty Z) j = 0.
Proof. intros j; unfold zget; rewrite PositiveMap.gempty; reflexivity. Qed.

Lemma zget_zadd : forall m i a j, zget (zadd m i a) j = zget m j + (if Nat.eqb i j then a else 0).
Proof.
  intros m i a j; unfold zadd. destruct (Nat.eqb_spec i j) as [E | NE].
  - subst j. unfold zget at 1. rewrite PositiveMap.gss. lia.
  - unfold zget at 1. rewrite PositiveMap.gso.
    + fold (zget m j); lia.
    + intro E; apply NE; symmetry; apply SuccNat2Pos.inj; exact E.
Qed.

Lemma zget_zaddv : forall y v m j, zget (zaddv y v m) j = zget m j + y * sget v j.
Proof.
  intros y v; induction v as [| [i a] v IH]; intros m j; simpl; [lia |].
  rewrite IH, zget_zadd. destruct (Nat.eqb i j); lia.
Qed.

(** ** Rows, tags and trees *)

Definition row : Type := (svec * Z)%type.

(** [sat r x]: [x] satisfies the row [a·x ≤ b]. *)
Definition sat (r : row) (x : nat -> Z) : Prop := dot (fst r) x <= snd r.

Definition trivial_row : row := ([], 0).

Lemma sat_trivial : forall x, sat trivial_row x.
Proof. intros x; unfold sat; simpl; lia. Qed.

Section Check.
  Variable tag : Type.
  Variable rowf : tag -> row.
  (** The variables known to be nonnegative.  For them the leaf may leave
      slack in the coefficient comparison. *)
  Variable nonneg : nat -> bool.

  (** A multiplier names a problem row, or the [k]-th branching row on
      the path to the leaf. *)
  Inductive rtag : Type := Base (t : tag) | Br (k : nat).

  Inductive tree : Type :=
  | Leaf (K : Z) (ys : list (rtag * Z))
  | Node (a : svec) (f : Z) (l r : tree).

  Definition rget (P : list row) (rt : rtag) : row :=
    match rt with Base t => rowf t | Br k => nth k P trivial_row end.

  (** The combination [Σ y·a] of the multiplied rows, as a map. *)
  Fixpoint zcomb (rs : list (row * Z)) (m : zmap) : zmap :=
    match rs with [] => m | q :: rs' => zcomb rs' (zaddv (snd q) (fst (fst q)) m) end.

  (** The coefficient comparison reads [K·c_j] and [(Σ y·a)_j] from maps
      ([zget_zcomb] below: they are [K * sget c j] and
      [zsum (map (fun q => snd q * sget (fst (fst q)) j) rs)]). *)
  Definition leafcheck (n : nat) (c : svec) (T : Z) (P : list row) (K : Z) (ys : list (rtag * Z)) : bool :=
    let rs := map (fun p => (rget P (fst p), snd p)) ys in
    let cm := zaddv K c (PositiveMap.empty Z) in
    let am := zcomb rs (PositiveMap.empty Z) in
    (0 <=? K) && forallb (fun q => 0 <=? snd q) rs && idx_ok n c
    && forallb (fun q => idx_ok n (fst (fst q))) rs
    && forallb (fun j => let lhs := zget cm j in
                         let rhs := zget am j in
                         if nonneg j then lhs <=? rhs else lhs =? rhs) (seq 0 n)
    && (zsum (map (fun q => snd q * snd (fst q)) rs) <? K * T).

  Fixpoint check (n : nat) (c : svec) (T : Z) (P : list row) (tr : tree) : bool :=
    match tr with
    | Leaf K ys => leafcheck n c T P K ys
    | Node a f l r => check n c T (P ++ [(a, f)]) l && check n c T (P ++ [(neg a, - f - 1)]) r
    end.

  Lemma zget_zcomb : forall rs m j,
    zget (zcomb rs m) j = zget m j + zsum (map (fun q => snd q * sget (fst (fst q)) j) rs).
  Proof.
    intros rs; induction rs as [| q rs IH]; intros m j; simpl; [unfold zsum; simpl; lia |].
    rewrite IH, zget_zaddv. unfold zsum; simpl. symmetry; apply Z.add_assoc.
  Qed.

  Variable x : nat -> Z.
  Hypothesis Hrows : forall t, sat (rowf t) x.
  Hypothesis Hnonneg : forall j, nonneg j = true -> 0 <= x j.

  Lemma rget_sat : forall P rt, (forall r, In r P -> sat r x) -> sat (rget P rt) x.
  Proof.
    intros P [t | k] HP; simpl; [apply Hrows |].
    destruct (Nat.lt_ge_cases k (length P)) as [Hk | Hk].
    - apply HP; apply nth_In; exact Hk.
    - rewrite nth_overflow by exact Hk. apply sat_trivial.
  Qed.

  Lemma leaf_sound : forall n c T P K ys,
    (forall r, In r P -> sat r x) -> leafcheck n c T P K ys = true -> dot c x < T.
  Proof.
    intros n c T P K ys HP Hc. unfold leafcheck in Hc. cbv zeta in Hc.
    set (rs := map (fun p => (rget P (fst p), snd p)) ys) in *.
    apply andb_true_iff in Hc as [Hc Hb]; apply andb_true_iff in Hc as [Hc Hcoef];
    apply andb_true_iff in Hc as [Hc Hidx]; apply andb_true_iff in Hc as [Hc Hcidx];
    apply andb_true_iff in Hc as [HK Hy].
    apply Z.leb_le in HK; apply Z.ltb_lt in Hb; rewrite forallb_forall in Hy, Hidx, Hcoef.
    assert (Hsat : forall q, In q rs -> sat (fst q) x).
    { intros q Hq; unfold rs in Hq; apply in_map_iff in Hq as [p [E _]]; subst q; apply rget_sat; exact HP. }
    (* K (c·x) ≤ Σ_q y_q (a_q·x): termwise, with equality on the free
       variables and slack times a nonnegative x_j on the others *)
    assert (E : K * dot c x <= zsum (map (fun q => snd q * dot (fst (fst q)) x) rs)).
    { rewrite (dot_dense n c x Hcidx), <- zsum_map_scale.
      apply Z.le_trans with (zsum (map (fun j => zsum (map (fun q => snd q * sget (fst (fst q)) j * x j) rs)) (seq 0 n))).
      - apply zsum_map_le. intros j Hj. specialize (Hcoef j Hj). cbv zeta in Hcoef.
        rewrite zget_zaddv, zget_zcomb, !zget_empty, !Z.add_0_l in Hcoef.
        rewrite (zsum_map_ext (fun q => snd q * sget (fst (fst q)) j * x j)
                              (fun q => x j * (snd q * sget (fst (fst q)) j))) by (intros; lia).
        rewrite zsum_map_scale, Z.mul_assoc.
        destruct (nonneg j) eqn:Enn.
        + apply Z.leb_le in Hcoef. pose proof (Hnonneg j Enn). rewrite (Z.mul_comm (x j)).
          apply Z.mul_le_mono_nonneg_r; assumption.
        + apply Z.eqb_eq in Hcoef. rewrite Hcoef; lia.
      - rewrite zsum_exchange. apply Z.eq_le_incl. apply zsum_map_ext; intros q Hq.
        rewrite (dot_dense n (fst (fst q)) x (Hidx q Hq)), <- zsum_map_scale.
        apply zsum_map_ext; intros j _; lia. }
    assert (Hle : zsum (map (fun q => snd q * dot (fst (fst q)) x) rs) <= zsum (map (fun q => snd q * snd (fst q)) rs)).
    { apply zsum_map_le; intros q Hq. apply Z.mul_le_mono_nonneg_l.
      - apply Z.leb_le; exact (Hy q Hq).
      - exact (Hsat q Hq). }
    assert (H : K * dot c x < K * T) by lia.
    destruct (Z.eq_dec K 0) as [E0 | NE0]; [subst K; lia |].
    apply (Z.mul_lt_mono_pos_l K); [lia | exact H].
  Qed.

  Lemma check_sound : forall n c T tr P,
    (forall r, In r P -> sat r x) -> check n c T P tr = true -> dot c x < T.
  Proof.
    intros n c T tr; induction tr as [K ys | a f l IHl r IHr]; intros P HP Hc; simpl in Hc.
    - exact (leaf_sound n c T P K ys HP Hc).
    - apply andb_true_iff in Hc as [Hl Hr].
      destruct (Z.le_gt_cases (dot a x) f) as [Hf | Hf].
      + eapply IHl; [| exact Hl].
        intros q Hq; apply in_app_iff in Hq as [Hq | [E | []]]; [apply HP; exact Hq | subst q; unfold sat; simpl; lia].
      + eapply IHr; [| exact Hr].
        intros q Hq; apply in_app_iff in Hq as [Hq | [E | []]]; [apply HP; exact Hq |].
        subst q; unfold sat; simpl; rewrite dot_neg; lia.
  Qed.
End Check.

Arguments Base {tag} t.
Arguments Br {tag} k.
Arguments Leaf {tag} K ys.
Arguments Node {tag} a f l r.

(** ** The theorem *)

(** If [check] accepts [tr] (from the empty path), every integer point
    satisfying all the rows has [c·x < T]. *)
Theorem tree_sound :
  forall (tag : Type) (rowf : tag -> row) (nonneg : nat -> bool) (n : nat) (c : svec) (T : Z) (tr : tree tag),
    check tag rowf nonneg n c T [] tr = true ->
    forall x : nat -> Z, (forall t, sat (rowf t) x) -> (forall j, nonneg j = true -> 0 <= x j) ->
    dot c x < T.
Proof.
  intros tag rowf nonneg n c T tr Hc x Hx Hnn.
  exact (check_sound tag rowf nonneg x Hx Hnn n c T tr [] (fun r H => match H with end) Hc).
Qed.

(** A tree whose every leaf has [K = 0] (checked against any [T]) shows
    the rows have no integer solution: it is accepted for [c = 0] and
    [T = 0], and [0 < 0] is false. *)
Corollary infeasible_of_tree :
  forall (tag : Type) (rowf : tag -> row) (nonneg : nat -> bool) (n : nat) (tr : tree tag),
    check tag rowf nonneg n [] 0 [] tr = true ->
    forall x : nat -> Z, (forall j, nonneg j = true -> 0 <= x j) -> ~ (forall t, sat (rowf t) x).
Proof.
  intros tag rowf nonneg n tr Hc x Hnn Hx. pose proof (tree_sound tag rowf nonneg n [] 0 tr Hc x Hx Hnn) as H.
  simpl in H; lia.
Qed.

(** An explicit list of rows is the case [tag := nat]. *)
Definition list_rows (rows : list row) : nat -> row := fun k => nth k rows trivial_row.

Corollary tree_sound_list :
  forall (rows : list row) (nonneg : nat -> bool) (n : nat) (c : svec) (T : Z) (tr : tree nat),
    check nat (list_rows rows) nonneg n c T [] tr = true ->
    forall x : nat -> Z, (forall r, In r rows -> sat r x) -> (forall j, nonneg j = true -> 0 <= x j) ->
    dot c x < T.
Proof.
  intros rows nonneg n c T tr Hc x Hx Hnn. apply (tree_sound nat (list_rows rows) nonneg n c T tr Hc x); [| exact Hnn].
  intros k; unfold list_rows. destruct (Nat.lt_ge_cases k (length rows)) as [Hk | Hk].
  - apply Hx; apply nth_In; exact Hk.
  - rewrite nth_overflow by exact Hk; apply sat_trivial.
Qed.

(** No variable declared nonnegative: the pure equality form. *)
Definition free : nat -> bool := fun _ => false.

(** The variables listed in [l] are declared nonnegative. *)
Definition nonneg_of (l : list nat) : nat -> bool := fun j => existsb (Nat.eqb j) l.

Lemma nonneg_of_spec : forall l j, nonneg_of l j = true -> In j l.
Proof.
  intros l j H. unfold nonneg_of in H. apply existsb_exists in H.
  destruct H as [i [Hi Hj]]. apply Nat.eqb_eq in Hj. subst i. exact Hi.
Qed.

(** The list form with the nonnegative variables given as a list. *)
Corollary tree_sound_list_nn :
  forall (rows : list row) (l : list nat) (n : nat) (c : svec) (T : Z) (tr : tree nat),
    check nat (list_rows rows) (nonneg_of l) n c T [] tr = true ->
    forall x : nat -> Z, (forall r, In r rows -> sat r x) -> (forall j, In j l -> 0 <= x j) ->
    dot c x < T.
Proof.
  intros rows l n c T tr Hc x Hx Hl. apply (tree_sound_list rows (nonneg_of l) n c T tr Hc x Hx).
  intros j Hj. apply Hl, nonneg_of_spec, Hj.
Qed.
