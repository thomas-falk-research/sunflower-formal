(** * The eleven finer classes at link size 23, and the descent from 23

    The classes that §64's LP cannot certify (indices 1722, 1726, 10590
    to 10597 and 14708 of [classes_23_27.txt.gz]) each carry a
    branch-and-bound tree checked by [Link23.classcheck].  With the LP
    census of sizes 23–27 ([LinkCerts23.cls23_all]) this gives the
    descent at 23 and [g(4) ≤ 78], conditional on [ι(4) ≤ 27] and on the
    census being complete ([Census2 … 23]).  See docs/roadmap.md §69. *)

From Coq Require Import List Lia.
Import ListNotations.
From Sunflower Require Import Sunflower IotaRate LinkCombine LinkLP Link23 LinkCerts23
  Link23c1722 Link23c1726 Link23c10590 Link23c10591 Link23c10592 Link23c10593 Link23c10594 Link23c10595 Link23c10596 Link23c10597 Link23c14708.

Definition link23_all : list (Family * tree) :=
  [(l23_1722_D, l23_1722_t)] ++
  [(l23_1726_D, l23_1726_t)] ++
  [(l23_10590_D, l23_10590_t)] ++
  [(l23_10591_D, l23_10591_t)] ++
  [(l23_10592_D, l23_10592_t)] ++
  [(l23_10593_D, l23_10593_t)] ++
  [(l23_10594_D, l23_10594_t)] ++
  [(l23_10595_D, l23_10595_t)] ++
  [(l23_10596_D, l23_10596_t)] ++
  [(l23_10597_D, l23_10597_t)] ++
  [(l23_14708_D, l23_14708_t)].

Lemma trees_okb_app :
  forall a b, trees_okb a = true -> trees_okb b = true -> trees_okb (a ++ b) = true.
Proof. intros a b Ha Hb; unfold trees_okb in *; rewrite forallb_app, Ha, Hb; reflexivity. Qed.

Lemma link23_all_ok : trees_okb link23_all = true.
Proof.
  unfold link23_all.
  apply trees_okb_app; [exact l23_1722_ok |].
  apply trees_okb_app; [exact l23_1726_ok |].
  apply trees_okb_app; [exact l23_10590_ok |].
  apply trees_okb_app; [exact l23_10591_ok |].
  apply trees_okb_app; [exact l23_10592_ok |].
  apply trees_okb_app; [exact l23_10593_ok |].
  apply trees_okb_app; [exact l23_10594_ok |].
  apply trees_okb_app; [exact l23_10595_ok |].
  apply trees_okb_app; [exact l23_10596_ok |].
  apply trees_okb_app; [exact l23_10597_ok |].
  exact l23_14708_ok.
Qed.

(** The descent at link size 23 and above. *)
Theorem descent_23 :
  IotaAtMost 4 27 -> Census2 cls23_all link23_all 23 -> LinkDescent 4 23 54.
Proof.
  intros Hi Hc.
  apply (descent_of_census2 Hi cls23_all link23_all 23 ltac:(lia)); [| exact link23_all_ok | exact Hc].
  intros Dk ck Hin; exact (reps_okb_entry cls23_all Dk ck cls23_all_ok Hin).
Qed.

Theorem g_four_at_most_78_of_census_23 :
  IotaAtMost 4 27 -> Census2 cls23_all link23_all 23 -> MeetingBound 4 56 -> GAtMost 4 78.
Proof.
  intros Hi Hc Hm.
  pose proof (g_at_most_of_descent_and_meeting 4 23 54 56 (descent_23 Hi Hc) Hm) as H.
  replace (Nat.max 54 (23 - 1 + 56)) with 78 in H by reflexivity. exact H.
Qed.
