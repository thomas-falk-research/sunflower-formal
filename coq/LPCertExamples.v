(** * LPCert: worked examples and rejected certificates

    Each example is decided by [vm_compute] in the kernel.  The negative
    examples tamper with a valid certificate in one way each and show the
    checker rejects it. *)

From Coq Require Import ZArith List Lia.
Import ListNotations.
From Sunflower Require Import LPCert.
Local Open Scope Z_scope.

(** ** 1. A bound from one leaf

    Rows: [x0 + x1 ≤ 1], [-x0 ≤ 0], [-x1 ≤ 0].  Claim: [x0 + x1 < 2].
    Certificate: [K = 1], one unit of the first row. *)
Definition rows1 : list row := [([(0%nat, 1); (1%nat, 1)], 1); ([(0%nat, -1)], 0); ([(1%nat, -1)], 0)].
Definition c1 : svec := [(0%nat, 1); (1%nat, 1)].
Definition t1 : tree nat := Leaf 1 [(Base 0%nat, 1)].

Example ex1_ok : check nat (list_rows rows1) free 2 c1 2 [] t1 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem ex1 : forall x : nat -> Z, (forall r, In r rows1 -> sat r x) -> dot c1 x < 2.
Proof. intros x Hx. exact (tree_sound_list rows1 free 2 c1 2 t1 ex1_ok x Hx (fun j H => False_ind _ (Bool.diff_false_true H))). Qed.

(** ** 2. Integrality matters: [2·x0 = 1] has no integer solution

    Rows: [2·x0 ≤ 1], [-2·x0 ≤ -1].  The linear relaxation is feasible
    ([x0 = 1/2]), so no single leaf can refute it; the tree branches on
    [x0 ≤ 0] / [x0 ≥ 1] and refutes each side with [K = 0]. *)
Definition rows2 : list row := [([(0%nat, 2)], 1); ([(0%nat, -2)], -1)].
Definition t2 : tree nat :=
  Node [(0%nat, 1)] 0
    (Leaf 0 [(Br 0%nat, 2); (Base 1%nat, 1)])      (* 2·(x0 ≤ 0) + (-2·x0 ≤ -1) : 0 ≤ -1 *)
    (Leaf 0 [(Base 0%nat, 1); (Br 0%nat, 2)]).     (* (2·x0 ≤ 1) + 2·(-x0 ≤ -1) : 0 ≤ -1 *)

Example ex2_ok : check nat (list_rows rows2) free 1 [] 0 [] t2 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem ex2 : forall x : nat -> Z, ~ (forall r, In r rows2 -> sat r x).
Proof.
  intros x Hx. apply (infeasible_of_tree nat (list_rows rows2) free 1 t2 ex2_ok x (fun j H => False_ind _ (Bool.diff_false_true H))).
  intros k; unfold list_rows. destruct (Nat.lt_ge_cases k (length rows2)) as [Hk | Hk].
  - apply Hx; apply nth_In; exact Hk.
  - rewrite nth_overflow by exact Hk; apply sat_trivial.
Qed.

(** No single leaf refutes [rows2]: with [K = 0], [y0·2 − y1·2 = 0] forces
    [y0 = y1], and then [y0·1 + y1·(−1) = 0], not [< 0].  Checked here
    for the natural candidate. *)
Example ex2_no_single_leaf : check nat (list_rows rows2) free 1 [] 0 [] (Leaf 0 [(Base 0%nat, 1); (Base 1%nat, 1)]) = false.
Proof. vm_compute. reflexivity. Qed.

(** ** 3. Declared nonnegative variables

    Rows: [x0 + x1 ≤ 1] only.  Claim: [x0 < 2] for every [x] with [x1 ≥ 0].
    Certificate: [K = 1], one unit of the row.  The coefficient of [x1] is
    [0] in [K·c] and [1] in the row, so the leaf is accepted only because
    [x1] is declared nonnegative ([0 ≤ 1] for it instead of [0 = 1]).
    Without the declaration the claim is false ([x = (5, −4)]), and the
    same certificate is rejected. *)
Definition rows3 : list row := [([(0%nat, 1); (1%nat, 1)], 1)].
Definition c3 : svec := [(0%nat, 1)].
Definition t3 : tree nat := Leaf 1 [(Base 0%nat, 1)].

Example ex3_ok : check nat (list_rows rows3) (nonneg_of [1%nat]) 2 c3 2 [] t3 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem ex3 : forall x : nat -> Z, (forall r, In r rows3 -> sat r x) -> 0 <= x 1%nat -> dot c3 x < 2.
Proof.
  intros x Hx H1. apply (tree_sound_list_nn rows3 [1%nat] 2 c3 2 t3 ex3_ok x Hx).
  intros j [<- | []]; exact H1.
Qed.

(** The declaration withheld: rejected. *)
Example rej_undeclared : check nat (list_rows rows3) free 2 c3 2 [] t3 = false.
Proof. vm_compute. reflexivity. Qed.

(** The declaration on the wrong variable: rejected. *)
Example rej_wrong_declared : check nat (list_rows rows3) (nonneg_of [0%nat]) 2 c3 2 [] t3 = false.
Proof. vm_compute. reflexivity. Qed.

(** And the claim does need it: a point of the rows with [x1 < 0] and
    [x0 ≥ 2]. *)
Example ex3_needs_nonneg :
  let x := fun j : nat => match j with 0%nat => 5 | _ => -4 end in
  (forall r, In r rows3 -> sat r x) /\ 2 <= dot c3 x.
Proof.
  cbv zeta. split.
  - intros r [<- | []]. unfold sat, dot; simpl; lia.
  - unfold dot; simpl; lia.
Qed.

(** ** 4. Rejected certificates *)

(** A multiplier changed: the coefficients no longer match. *)
Example rej_coefficient : check nat (list_rows rows2) free 1 [] 0 []
  (Node [(0%nat, 1)] 0 (Leaf 0 [(Br 0%nat, 1); (Base 1%nat, 1)]) (Leaf 0 [(Base 0%nat, 1); (Br 0%nat, 2)])) = false.
Proof. vm_compute. reflexivity. Qed.

(** A negative multiplier, which would flip an inequality. *)
Example rej_negative : check nat (list_rows rows1) free 2 c1 1 [] (Leaf 1 [(Base 0%nat, 1); (Base 1%nat, -1)]) = false.
Proof. vm_compute. reflexivity. Qed.

(** A negative scale. *)
Example rej_scale : check nat (list_rows rows1) free 2 c1 2 [] (Leaf (-1) [(Base 0%nat, -1)]) = false.
Proof. vm_compute. reflexivity. Qed.

(** The bound one too strong: [x0 + x1 < 1] is false at [x = (1, 0)]. *)
Example rej_bound : check nat (list_rows rows1) free 2 c1 1 [] t1 = false.
Proof. vm_compute. reflexivity. Qed.

(** A dimension that hides a coefficient: with [n = 1] the objective's
    [x1] term lies outside the checked range, so [idx_ok] refuses it. *)
Example rej_dimension : check nat (list_rows rows1) free 1 c1 2 [] t1 = false.
Proof. vm_compute. reflexivity. Qed.

(** A branching row that is not on the path ([Br 5]) is the trivial row
    [0 ≤ 0]; it contributes nothing and cannot help. *)
Example rej_phantom_branch : check nat (list_rows rows2) free 1 [] 0 [] (Leaf 0 [(Br 5%nat, 1)]) = false.
Proof. vm_compute. reflexivity. Qed.
