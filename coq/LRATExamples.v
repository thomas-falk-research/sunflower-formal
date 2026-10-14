(** * LRAT: a worked example and rejected proofs

    The pigeonhole principle for four pigeons and three holes, refuted
    from CaDiCaL's LRAT proof ([tools/lrat/lrat.py]), and proofs tampered
    in one way each, all rejected.  Each example is decided by
    [vm_compute]. *)

From Coq Require Import ZArith List.
Import ListNotations.
From Sunflower Require Import LRAT.
Local Open Scope Z_scope.

(** Variables [3p + h + 1]: pigeon [p] sits in hole [h]. *)
Definition php43 : list clause :=
  [[1; 2; 3];
   [4; 5; 6];
   [7; 8; 9];
   [10; 11; 12];
   [-1; -4];
   [-1; -7];
   [-1; -10];
   [-4; -7];
   [-4; -10];
   [-7; -10];
   [-2; -5];
   [-2; -8];
   [-2; -11];
   [-5; -8];
   [-5; -11];
   [-8; -11];
   [-3; -6];
   [-3; -9];
   [-3; -12];
   [-6; -9];
   [-6; -12];
   [-9; -12]].

Definition php43_proof : list step :=
  [A 23 [-11; -12] [22; 19; 13; 16; 1; 3; 6];
   A 24 [-7; -12] [21; 19; 6; 8; 1; 2; 11];
   A 25 [-12] [19; 21; 22; 24; 3; 12; 14; 1; 2; 5];
   A 26 [-8] [25; 12; 14; 16; 4; 7; 9; 1; 2; 17];
   A 27 [-7] [25; 6; 8; 10; 4; 13; 15; 1; 2; 17];
   A 28 [9] [27; 26; 3];
   A 29 [-3] [28; 18];
   A 30 [-6] [28; 20];
   A 31 [-1] [30; 25; 5; 7; 2; 4; 15];
   A 32 [2] [31; 29; 1];
   A 33 [-5] [32; 11];
   A 34 [-11] [32; 13];
   A 35 [4] [33; 30; 2];
   A 36 [10] [34; 25; 4];
   A 37 [] [35; 36; 9]].

Lemma php43_ok : lrat_check php43 php43_proof = true.
Proof. vm_compute. reflexivity. Qed.

Theorem php43_unsat : forall v, cnf_sat v php43 = false.
Proof. exact (lrat_sound php43 php43_proof php43_ok). Qed.

(** ** Rejected proofs *)

(** The proof cut before the empty clause. *)
Example rej_truncated : lrat_check php43 (firstn 14 php43_proof) = false.
Proof. vm_compute. reflexivity. Qed.

(** The empty clause at once, every input clause as a hint: no unit
    propagation reaches a conflict without the intermediate steps. *)
Example rej_shortcut : lrat_check php43 [A 100 [] [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22]] = false.
Proof. vm_compute. reflexivity. Qed.

(** A hint naming no clause. *)
Example rej_missing : lrat_check php43 (A 23 [-11; -12] ([22; 19; 13; 16; 1; 3] ++ [999]) :: tl php43_proof) = false.
Proof. vm_compute. reflexivity. Qed.

(** A clause containing [0] is never added (it would read as a
    tautology). *)
Example rej_zero : lrat_check [[1]; [-1]] [A 3 [0] []; A 4 [] [1; 2]] = false.
Proof. vm_compute. reflexivity. Qed.

(** The smallest refutation, for contrast: [x] and [¬x]. *)
Example ok_unit : lrat_check [[1]; [-1]] [A 3 [] [1; 2]] = true.
Proof. vm_compute. reflexivity. Qed.
