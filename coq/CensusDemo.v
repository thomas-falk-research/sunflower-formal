(** * The census pipeline end to end, at [b = 2]

    [ι(2) ≤ 3] from [CensusSearch.iota_of_search]: the generic search,
    run by [vm_compute] with the concrete node test [validb 2] and no
    oracle at all (no node is ever pruned), finds no node at level 4.
    The levels have 1, 1, 4, 2 and 0 nodes.  This exercises every
    definition of the pipeline on an instance small enough to need no
    pruning; larger instances need an oracle (docs/census_certification.md,
    stages 3–4). *)

From Coq Require Import List NArith.
Import ListNotations.
From Sunflower Require Import IotaRate CensusSearch.
From Sunflower Require CensusGen.

Example census_demo_levels :
  map (fun n => length (CensusGen.level 2 (validb 2) (fun _ => None) n)) [0; 1; 2; 3; 4] = [1; 1; 4; 2; 0].
Proof. vm_compute. reflexivity. Qed.

Example census_demo_level4 : CensusGen.level 2 (validb 2) (fun _ => None) 4 = [].
Proof. vm_compute. reflexivity. Qed.

Theorem iota_two_by_search : IotaAtMost 2 3.
Proof.
  apply (iota_of_search 2 (validb 2) (fun _ => None) 3 (validb_complete 2)).
  intros K H. rewrite census_demo_level4 in H. destruct H.
Qed.
