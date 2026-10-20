(** * LRAT: kernel-checked unsatisfiability proofs

    A small checker for LRAT proofs of propositional unsatisfiability,
    independent of the rest of this library.  A literal is a nonzero
    integer ([v] or [−v] for the variable [v]), a clause a list of
    literals, a CNF a list of clauses numbered [1, 2, …].  A proof is a
    list of steps:

    - [Add i C hs]: the clause [C], numbered [i], follows by reverse unit
      propagation along the hint chain [hs]: assume every literal of [C]
      false; each hinted clause in turn must then have all its literals
      false but one, which becomes true, until one hinted clause has all
      its literals false;
    - [Del is]: the clauses numbered [is] are forgotten.

    [lrat_sound]: if [lrat_check] accepts a proof for a CNF, no
    valuation satisfies the CNF.  Only reverse-unit-propagation steps are
    supported (no RAT steps); a step that is not justified is rejected.
    The arithmetic and the data structures are exact and finite; nothing
    is assumed. *)

From Coq Require Import ZArith List Bool Lia FMapPositive.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Valuations and clauses *)

Definition lit := Z.
Definition clause := list lit.

(** The variable of a literal ([0] has none and is never true). *)
Definition var (l : lit) : positive := Z.to_pos (Z.abs l).

(** [l] is true under the valuation [v]. *)
Definition lit_true (v : positive -> bool) (l : lit) : bool :=
  if 0 <? l then v (var l) else if l <? 0 then negb (v (var l)) else false.

Definition clause_sat (v : positive -> bool) (C : clause) : bool := existsb (lit_true v) C.

Definition cnf_sat (v : positive -> bool) (F : list clause) : bool := forallb (clause_sat v) F.

(** ** Partial assignments

    A partial assignment maps a variable to [true] or [false]; [atrue a l]:
    [l] is assigned true, [afalse a l]: [l] is assigned false. *)

Definition assign := PositiveMap.t bool.

Definition aval (a : assign) (l : lit) : option bool :=
  if 0 <? l then PositiveMap.find (var l) a
  else if l <? 0 then option_map negb (PositiveMap.find (var l) a) else Some false.

(** Make [l] true; [None] if [l] is already false (a conflict). *)
Definition aset (a : assign) (l : lit) : option assign :=
  match aval a l with
  | Some true => Some a
  | Some false => None
  | None => Some (PositiveMap.add (var l) (0 <? l) a)
  end.

(** [a] agrees with [v] on every assigned literal. *)
Definition agrees (a : assign) (v : positive -> bool) : Prop :=
  forall l b, aval a l = Some b -> lit_true v l = b.

(** ** Reverse unit propagation *)

(** Assume every literal of [C] false; [None]: [C] contains a literal and
    its negation (a tautology), which is a conflict at once. *)
Fixpoint negate_all (a : assign) (C : clause) : option assign :=
  match C with
  | [] => Some a
  | l :: C' => match aset a (- l) with Some a' => negate_all a' C' | None => None end
  end.

(** The status of a hinted clause under [a]: [inl true] conflict (every
    literal false), [inr u] exactly one literal [u] not false and it is
    unassigned (a unit), [inl false] otherwise. *)
Fixpoint unit_status (a : assign) (D : clause) (u : option lit) : option (option lit) :=
  (* [None]: give up (a literal is true, or two are unassigned);
     [Some None]: all false so far; [Some (Some u)]: one unassigned so far *)
  match D with
  | [] => Some u
  | l :: D' =>
      match aval a l with
      | Some false => unit_status a D' u
      | Some true => None
      | None => match u with None => unit_status a D' (Some l) | Some _ => None end
      end
  end.

Definition db := PositiveMap.t clause.

Fixpoint rup_chain (d : db) (a : assign) (hs : list positive) : bool :=
  match hs with
  | [] => false
  | h :: hs' =>
      match PositiveMap.find h d with
      | None => false
      | Some D =>
          match unit_status a D None with
          | Some None => true                         (* conflict *)
          | Some (Some u) =>
              match aset a u with Some a' => rup_chain d a' hs' | None => false end
          | None => false
          end
      end
  end.

(** A clause to add may not contain [0]. *)
Definition rup (d : db) (C : clause) (hs : list positive) : bool :=
  forallb (fun l => negb (l =? 0)) C &&
  match negate_all (PositiveMap.empty bool) C with
  | None => true
  | Some a => rup_chain d a hs
  end.

(** ** Proofs *)

Inductive step : Type :=
| Add (i : positive) (C : clause) (hs : list positive)
| Del (is : list positive).

(** Check the steps; [true] once the empty clause has been added. *)
Fixpoint check_steps (d : db) (ps : list step) : bool :=
  match ps with
  | [] => false
  | Add i C hs :: ps' =>
      rup d C hs && (match C with [] => true | _ => check_steps (PositiveMap.add i C d) ps' end)
  | Del is :: ps' => check_steps (fold_left (fun d i => PositiveMap.remove i d) is d) ps'
  end.

(** The CNF's clauses, numbered from 1. *)
Fixpoint load (d : db) (n : positive) (F : list clause) : db :=
  match F with [] => d | C :: F' => load (PositiveMap.add n C d) (Pos.succ n) F' end.

Definition lrat_check (F : list clause) (ps : list step) : bool :=
  check_steps (load (PositiveMap.empty clause) 1 F) ps.

(** ** Soundness *)

Lemma var_eq_lit : forall v l, l <> 0 -> lit_true v l = true -> v (var l) = (0 <? l).
Proof.
  intros v l Hl H. unfold lit_true in H.
  destruct (Z.ltb_spec 0 l) as [Hp | Hp]; [exact H |].
  destruct (Z.ltb_spec l 0) as [Hn | Hn]; [| lia]. apply negb_true_iff in H. exact H.
Qed.

Lemma aval_empty : forall l b, aval (PositiveMap.empty bool) l = Some b -> b = false /\ l = 0.
Proof.
  intros l b H. unfold aval in H. rewrite PositiveMap.gempty in H.
  destruct (Z.ltb_spec 0 l); [discriminate |]. destruct (Z.ltb_spec l 0); [discriminate |].
  injection H; intros; split; [congruence | lia].
Qed.

Lemma agrees_empty : forall v, agrees (PositiveMap.empty bool) v.
Proof.
  intros v l b H. apply aval_empty in H as [-> ->]. reflexivity.
Qed.

Lemma aval_zero : forall a, aval a 0 = Some false.
Proof. intros a; reflexivity. Qed.

Lemma lit_true_zero : forall v, lit_true v 0 = false.
Proof. intros v; reflexivity. Qed.

Lemma var_inj_sign : forall l l', l <> 0 -> l' <> 0 -> var l = var l' -> l = l' \/ l = - l'.
Proof.
  intros l l' H1 H2 E. unfold var in E. apply Z2Pos.inj in E; [lia | lia | lia].
Qed.

Lemma aset_agrees : forall a v l a', agrees a v -> lit_true v l = true -> aset a l = Some a' -> agrees a' v.
Proof.
  intros a v l a' Ha Hl Hs. unfold aset in Hs.
  destruct (aval a l) as [[|] |] eqn:E; [injection Hs; intros <-; exact Ha | discriminate |].
  injection Hs; intros <-.
  assert (Hl0 : l <> 0) by (intro Z0; subst; discriminate).
  pose proof (var_eq_lit v l Hl0 Hl) as Hv.
  intros l' b H'. destruct (Z.eq_dec l' 0) as [-> | Hl'0]; [rewrite aval_zero in H'; injection H'; intros <-; reflexivity |].
  unfold aval in H'.
  destruct (Pos.eq_dec (var l') (var l)) as [Ev | Ev].
  - rewrite Ev, PositiveMap.gss in H'. unfold lit_true. rewrite Ev, Hv.
    destruct (Z.ltb_spec 0 l'); [injection H'; auto |].
    destruct (Z.ltb_spec l' 0); [| lia]. simpl in H'. injection H'; auto.
  - rewrite PositiveMap.gso in H' by exact Ev. apply Ha. unfold aval. exact H'.
Qed.

Lemma lit_neg : forall v l, l <> 0 -> lit_true v (- l) = negb (lit_true v l).
Proof.
  intros v l Hl. unfold lit_true. assert (Ev : var (- l) = var l) by (unfold var; f_equal; lia).
  rewrite Ev. destruct (Z.ltb_spec 0 l); destruct (Z.ltb_spec 0 (- l)); destruct (Z.ltb_spec (- l) 0); destruct (Z.ltb_spec l 0);
    try lia; rewrite ?negb_involutive; reflexivity.
Qed.

(** Assuming the literals of a clause false that [v] falsifies keeps
    agreement, and cannot conflict when the clause has no [0]. *)
Lemma negate_all_agrees : forall C a v, agrees a v -> clause_sat v C = false ->
  forallb (fun l => negb (l =? 0)) C = true ->
  exists a', negate_all a C = Some a' /\ agrees a' v.
Proof.
  induction C as [| l C IH]; intros a v Ha Hc Hz; simpl in *; [exists a; split; [reflexivity | exact Ha] |].
  apply orb_false_iff in Hc as [Hl Hc]. apply andb_true_iff in Hz as [Hl0 Hz].
  apply negb_true_iff, Z.eqb_neq in Hl0.
  assert (Hneg : lit_true v (- l) = true) by (rewrite lit_neg by exact Hl0; rewrite Hl; reflexivity).
  destruct (aset a (- l)) as [a1 |] eqn:E.
  - apply (IH a1 v); [apply (aset_agrees a v (- l) a1 Ha Hneg E) | exact Hc | exact Hz].
  - exfalso. unfold aset in E. destruct (aval a (- l)) as [[|] |] eqn:E'; try discriminate.
    apply Ha in E'. congruence.
Qed.

Lemma unit_status_spec : forall a D u r, unit_status a D u = Some r ->
  forall l, In l D -> aval a l = Some false \/ (aval a l = None /\ r = Some l /\ u = None) \/ (aval a l = None /\ r = Some l).
Proof.
  intros a D; induction D as [| x D IH]; intros u r H l Hl; [destruct Hl |]. simpl in H.
  destruct (aval a x) as [[|] |] eqn:Ex; [discriminate | |].
  - destruct Hl as [<- | Hl]; [left; exact Ex | apply (IH u r H l Hl)].
  - destruct u as [w |]; [discriminate |].
    destruct Hl as [<- | Hl].
    + right; right. split; [exact Ex |].
      (* the accumulator, once set, is returned unchanged or the call fails *)
      clear IH. revert r H. induction D as [| y D IHD]; intros r H; simpl in H; [injection H; auto |].
      destruct (aval a y) as [[|] |]; [discriminate | apply IHD, H | discriminate].
    + destruct (IH (Some x) r H l Hl) as [A | [[A [B C]] | [A B]]].
      * left; exact A.
      * discriminate.
      * right; right; split; assumption.
Qed.

Lemma unit_status_none : forall a D u, unit_status a D u = Some None -> u = None.
Proof.
  intros a D; induction D as [| x D IH]; intros u H; simpl in H; [injection H; auto |].
  destruct (aval a x) as [[|] |]; [discriminate | apply (IH u H) |].
  destruct u; [discriminate |]. apply IH in H. discriminate.
Qed.

Lemma unit_status_some : forall a D u w, unit_status a D u = Some (Some w) -> u = Some w \/ (In w D /\ aval a w = None).
Proof.
  intros a D; induction D as [| x D IH]; intros u w H; simpl in H; [injection H; auto |].
  destruct (aval a x) as [[|] |] eqn:Ex; [discriminate | |].
  - destruct (IH u w H) as [E | [Hi Hw]]; [left; exact E | right; split; [right; exact Hi | exact Hw]].
  - destruct u; [discriminate |]. destruct (IH (Some x) w H) as [E | [Hi Hw]].
    + injection E; intros <-. right; split; [left; reflexivity | exact Ex].
    + right; split; [right; exact Hi | exact Hw].
Qed.

Definition db_sat (d : db) (v : positive -> bool) : Prop :=
  forall i D, PositiveMap.find i d = Some D -> clause_sat v D = true.

Lemma rup_chain_sound : forall d v hs a, db_sat d v -> agrees a v -> rup_chain d a hs = true -> False.
Proof.
  intros d v hs; induction hs as [| h hs IH]; intros a Hd Ha H; simpl in H; [discriminate |].
  destruct (PositiveMap.find h d) as [D |] eqn:Ef; [| discriminate].
  pose proof (Hd h D Ef) as HD. unfold clause_sat in HD. apply existsb_exists in HD as [t [Ht Htv]].
  destruct (unit_status a D None) as [[w |] |] eqn:Es; try discriminate.
  - destruct (aset a w) as [a1 |] eqn:Eset; [| discriminate].
    (* every literal of [D] other than [w] is false; so [w] is true under [v] *)
    assert (Hw : lit_true v w = true).
    { destruct (unit_status_spec a D None (Some w) Es t Ht) as [Hf | [[_ [E _]] | [_ E]]].
      - apply Ha in Hf. congruence.
      - injection E; intros ->; exact Htv.
      - injection E; intros ->; exact Htv. }
    exact (IH a1 Hd (aset_agrees a v w a1 Ha Hw Eset) H).
  - destruct (unit_status_spec a D None None Es t Ht) as [Hf | [[_ [E _]] | [_ E]]]; try discriminate.
    apply Ha in Hf. congruence.
Qed.

Lemma rup_sound : forall d v C hs, db_sat d v -> rup d C hs = true -> clause_sat v C = true.
Proof.
  intros d v C hs Hd H. unfold rup in H. apply andb_true_iff in H as [Hz H].
  destruct (clause_sat v C) eqn:Ec; [reflexivity | exfalso].
  destruct (negate_all_agrees C (PositiveMap.empty bool) v (agrees_empty v) Ec Hz) as [a [Ea Ha]].
  rewrite Ea in H. exact (rup_chain_sound d v hs a Hd Ha H).
Qed.

Lemma db_sat_add : forall d v i C, db_sat d v -> clause_sat v C = true -> db_sat (PositiveMap.add i C d) v.
Proof.
  intros d v i C Hd HC j D H. destruct (Pos.eq_dec j i) as [-> | Ne].
  - rewrite PositiveMap.gss in H. injection H; intros <-; exact HC.
  - rewrite PositiveMap.gso in H by exact Ne. apply (Hd j D H).
Qed.

Lemma db_sat_remove : forall d v is, db_sat d v -> db_sat (fold_left (fun d i => PositiveMap.remove i d) is d) v.
Proof.
  intros d v is; revert d; induction is as [| i is IH]; intros d Hd; simpl; [exact Hd |].
  apply IH. intros j D H. destruct (Pos.eq_dec j i) as [-> | Ne].
  - rewrite PositiveMap.grs in H. discriminate.
  - rewrite PositiveMap.gro in H by exact Ne. apply (Hd j D H).
Qed.

Lemma check_steps_sound : forall ps d v, db_sat d v -> check_steps d ps = true -> False.
Proof.
  induction ps as [| p ps IH]; intros d v Hd H; simpl in H; [discriminate |].
  destruct p as [i C hs | is].
  - apply andb_true_iff in H as [Hr H]. pose proof (rup_sound d v C hs Hd Hr) as HC.
    destruct C as [| l C'].
    + simpl in HC. discriminate.
    + exact (IH _ v (db_sat_add d v i _ Hd HC) H).
  - exact (IH _ v (db_sat_remove d v is Hd) H).
Qed.

Lemma load_sat : forall F d n v, db_sat d v -> cnf_sat v F = true -> db_sat (load d n F) v.
Proof.
  induction F as [| C F IH]; intros d n v Hd HF; simpl; [exact Hd |].
  simpl in HF. apply andb_true_iff in HF as [HC HF]. apply IH; [apply db_sat_add; assumption | exact HF].
Qed.

(** An accepted proof refutes the CNF: no valuation satisfies it. *)
Theorem lrat_sound : forall F ps, lrat_check F ps = true -> forall v, cnf_sat v F = false.
Proof.
  intros F ps H v. destruct (cnf_sat v F) eqn:E; [exfalso | reflexivity].
  apply (check_steps_sound ps (load (PositiveMap.empty clause) 1 F) v); [| exact H].
  apply load_sat; [| exact E]. intros i D Hf. rewrite PositiveMap.gempty in Hf. discriminate.
Qed.

(** ** Constructors for generated proofs

    Everything as [Z], so that a generated proof is one list of integer
    literals; ids are converted with [Z.to_pos].  They only build steps:
    an id that names no clause makes the step fail, so they cannot make
    a wrong proof pass. *)
Definition A (i : Z) (C : list Z) (hs : list Z) : step := Add (Z.to_pos i) C (map Z.to_pos hs).
Definition D (is : list Z) : step := Del (map Z.to_pos is).
