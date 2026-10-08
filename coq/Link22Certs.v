(** * Link size 22 in the kernel, and the descent from 22

    The 69,616 link classes of size 22 ([classes_22.txt.gz]) each carry a
    branch-and-bound tree over the finer model of [Link23], checked by
    [classcheck] in 36 shards ([Link22s0] to [Link22s35]).  With the
    LP census of sizes 23–27 and the eleven trees at 23 this gives the
    descent at 22 and [g(4) ≤ 77], conditional on [ι(4) ≤ 27] and on the
    census being complete from 22 up.  See docs/roadmap.md §70. *)

From Coq Require Import List Lia.
Import ListNotations.
From Sunflower Require Import Sunflower IotaRate LinkCombine LinkLP Link23 LinkCerts23 Link23Certs
  Link22s0 Link22s1 Link22s2 Link22s3 Link22s4 Link22s5 Link22s6 Link22s7 Link22s8 Link22s9 Link22s10 Link22s11 Link22s12 Link22s13 Link22s14 Link22s15 Link22s16 Link22s17 Link22s18 Link22s19 Link22s20 Link22s21 Link22s22 Link22s23 Link22s24 Link22s25 Link22s26 Link22s27 Link22s28 Link22s29 Link22s30 Link22s31 Link22s32 Link22s33 Link22s34 Link22s35.

Definition link22_all : list (Family * tree) :=
  l22s0_all ++
  l22s1_all ++
  l22s2_all ++
  l22s3_all ++
  l22s4_all ++
  l22s5_all ++
  l22s6_all ++
  l22s7_all ++
  l22s8_all ++
  l22s9_all ++
  l22s10_all ++
  l22s11_all ++
  l22s12_all ++
  l22s13_all ++
  l22s14_all ++
  l22s15_all ++
  l22s16_all ++
  l22s17_all ++
  l22s18_all ++
  l22s19_all ++
  l22s20_all ++
  l22s21_all ++
  l22s22_all ++
  l22s23_all ++
  l22s24_all ++
  l22s25_all ++
  l22s26_all ++
  l22s27_all ++
  l22s28_all ++
  l22s29_all ++
  l22s30_all ++
  l22s31_all ++
  l22s32_all ++
  l22s33_all ++
  l22s34_all ++
  l22s35_all.

Lemma link22_all_ok : trees_okb link22_all = true.
Proof.
  unfold link22_all.
  apply trees_okb_app; [exact l22s0_all_ok |].
  apply trees_okb_app; [exact l22s1_all_ok |].
  apply trees_okb_app; [exact l22s2_all_ok |].
  apply trees_okb_app; [exact l22s3_all_ok |].
  apply trees_okb_app; [exact l22s4_all_ok |].
  apply trees_okb_app; [exact l22s5_all_ok |].
  apply trees_okb_app; [exact l22s6_all_ok |].
  apply trees_okb_app; [exact l22s7_all_ok |].
  apply trees_okb_app; [exact l22s8_all_ok |].
  apply trees_okb_app; [exact l22s9_all_ok |].
  apply trees_okb_app; [exact l22s10_all_ok |].
  apply trees_okb_app; [exact l22s11_all_ok |].
  apply trees_okb_app; [exact l22s12_all_ok |].
  apply trees_okb_app; [exact l22s13_all_ok |].
  apply trees_okb_app; [exact l22s14_all_ok |].
  apply trees_okb_app; [exact l22s15_all_ok |].
  apply trees_okb_app; [exact l22s16_all_ok |].
  apply trees_okb_app; [exact l22s17_all_ok |].
  apply trees_okb_app; [exact l22s18_all_ok |].
  apply trees_okb_app; [exact l22s19_all_ok |].
  apply trees_okb_app; [exact l22s20_all_ok |].
  apply trees_okb_app; [exact l22s21_all_ok |].
  apply trees_okb_app; [exact l22s22_all_ok |].
  apply trees_okb_app; [exact l22s23_all_ok |].
  apply trees_okb_app; [exact l22s24_all_ok |].
  apply trees_okb_app; [exact l22s25_all_ok |].
  apply trees_okb_app; [exact l22s26_all_ok |].
  apply trees_okb_app; [exact l22s27_all_ok |].
  apply trees_okb_app; [exact l22s28_all_ok |].
  apply trees_okb_app; [exact l22s29_all_ok |].
  apply trees_okb_app; [exact l22s30_all_ok |].
  apply trees_okb_app; [exact l22s31_all_ok |].
  apply trees_okb_app; [exact l22s32_all_ok |].
  apply trees_okb_app; [exact l22s33_all_ok |].
  apply trees_okb_app; [exact l22s34_all_ok |].
  exact l22s35_all_ok.
Qed.

(** The descent at link size 22 and above. *)
Theorem descent_22 :
  IotaAtMost 4 27 -> Census2 cls23_all (link23_all ++ link22_all) 22 -> LinkDescent 4 22 54.
Proof.
  intros Hi Hc.
  apply (descent_of_census2 Hi cls23_all (link23_all ++ link22_all) 22 ltac:(lia));
    [| apply trees_okb_app; [exact link23_all_ok | exact link22_all_ok] | exact Hc].
  intros Dk ck Hin; exact (reps_okb_entry cls23_all Dk ck cls23_all_ok Hin).
Qed.

Theorem g_four_at_most_77_of_census_22 :
  IotaAtMost 4 27 -> Census2 cls23_all (link23_all ++ link22_all) 22 -> MeetingBound 4 56 -> GAtMost 4 77.
Proof.
  intros Hi Hc Hm.
  pose proof (g_at_most_of_descent_and_meeting 4 22 54 56 (descent_22 Hi Hc) Hm) as H.
  replace (Nat.max 54 (22 - 1 + 56)) with 77 in H by reflexivity. exact H.
Qed.
