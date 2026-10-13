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

Example ex1_ok : check nat (list_rows rows1) 2 c1 2 [] t1 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem ex1 : forall x : nat -> Z, (forall r, In r rows1 -> sat r x) -> dot c1 x < 2.
Proof. exact (tree_sound_list rows1 2 c1 2 t1 ex1_ok). Qed.

(** ** 2. Integrality matters: [2·x0 = 1] has no integer solution

    Rows: [2·x0 ≤ 1], [-2·x0 ≤ -1].  The linear relaxation is feasible
    ([x0 = 1/2]), so no single leaf can refute it; the tree branches on
    [x0 ≤ 0] / [x0 ≥ 1] and refutes each side with [K = 0]. *)
Definition rows2 : list row := [([(0%nat, 2)], 1); ([(0%nat, -2)], -1)].
Definition t2 : tree nat :=
  Node [(0%nat, 1)] 0
    (Leaf 0 [(Br 0%nat, 2); (Base 1%nat, 1)])      (* 2·(x0 ≤ 0) + (-2·x0 ≤ -1) : 0 ≤ -1 *)
    (Leaf 0 [(Base 0%nat, 1); (Br 0%nat, 2)]).     (* (2·x0 ≤ 1) + 2·(-x0 ≤ -1) : 0 ≤ -1 *)

Example ex2_ok : check nat (list_rows rows2) 1 [] 0 [] t2 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem ex2 : forall x : nat -> Z, ~ (forall r, In r rows2 -> sat r x).
Proof.
  intros x Hx. apply (infeasible_of_tree nat (list_rows rows2) 1 t2 ex2_ok x).
  intros k; unfold list_rows. destruct (Nat.lt_ge_cases k (length rows2)) as [Hk | Hk].
  - apply Hx; apply nth_In; exact Hk.
  - rewrite nth_overflow by exact Hk; apply sat_trivial.
Qed.

(** No single leaf refutes [rows2]: with [K = 0], [y0·2 − y1·2 = 0] forces
    [y0 = y1], and then [y0·1 + y1·(−1) = 0], not [< 0].  Checked here
    for the natural candidate. *)
Example ex2_no_single_leaf : check nat (list_rows rows2) 1 [] 0 [] (Leaf 0 [(Base 0%nat, 1); (Base 1%nat, 1)]) = false.
Proof. vm_compute. reflexivity. Qed.

(** ** 3. Rejected certificates *)

(** A multiplier changed: the coefficients no longer match. *)
Example rej_coefficient : check nat (list_rows rows2) 1 [] 0 []
  (Node [(0%nat, 1)] 0 (Leaf 0 [(Br 0%nat, 1); (Base 1%nat, 1)]) (Leaf 0 [(Base 0%nat, 1); (Br 0%nat, 2)])) = false.
Proof. vm_compute. reflexivity. Qed.

(** A negative multiplier, which would flip an inequality. *)
Example rej_negative : check nat (list_rows rows1) 2 c1 1 [] (Leaf 1 [(Base 0%nat, 1); (Base 1%nat, -1)]) = false.
Proof. vm_compute. reflexivity. Qed.

(** A negative scale. *)
Example rej_scale : check nat (list_rows rows1) 2 c1 2 [] (Leaf (-1) [(Base 0%nat, -1)]) = false.
Proof. vm_compute. reflexivity. Qed.

(** The bound one too strong: [x0 + x1 < 1] is false at [x = (1, 0)]. *)
Example rej_bound : check nat (list_rows rows1) 2 c1 1 [] t1 = false.
Proof. vm_compute. reflexivity. Qed.

(** A dimension that hides a coefficient: with [n = 1] the objective's
    [x1] term lies outside the checked range, so [idx_ok] refuses it. *)
Example rej_dimension : check nat (list_rows rows1) 1 c1 2 [] t1 = false.
Proof. vm_compute. reflexivity. Qed.

(** A branching row that is not on the path ([Br 5]) is the trivial row
    [0 ≤ 0]; it contributes nothing and cannot help. *)
Example rej_phantom_branch : check nat (list_rows rows2) 1 [] 0 [] (Leaf 0 [(Br 5%nat, 1)]) = false.
Proof. vm_compute. reflexivity. Qed.
