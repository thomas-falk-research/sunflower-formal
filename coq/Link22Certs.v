(** * Link size 22 in the kernel, and the descent from 22

    The 69,616 link classes of size 22 ([classes_22.txt.gz]) each carry a
    branch-and-bound tree over the finer model of [Link23], checked by
    [classcheck] in 150 shards ([Link22s0] to [Link22s149]).  With the
    LP census of sizes 23–27 and the eleven trees at 23 this gives the
    descent at 22 and [g(4) ≤ 77], conditional on [ι(4) ≤ 27] and on the
    census being complete from 22 up.  See docs/roadmap.md §70. *)

From Coq Require Import List Lia.
Import ListNotations.
From Sunflower Require Import Sunflower IotaRate LinkCombine LinkLP Link23 LinkCerts23 Link23Certs
  Link22s0 Link22s1 Link22s2 Link22s3 Link22s4 Link22s5 Link22s6 Link22s7 Link22s8 Link22s9 Link22s10 Link22s11 Link22s12 Link22s13 Link22s14 Link22s15 Link22s16 Link22s17 Link22s18 Link22s19 Link22s20 Link22s21 Link22s22 Link22s23 Link22s24 Link22s25 Link22s26 Link22s27 Link22s28 Link22s29 Link22s30 Link22s31 Link22s32 Link22s33 Link22s34 Link22s35 Link22s36 Link22s37 Link22s38 Link22s39 Link22s40 Link22s41 Link22s42 Link22s43 Link22s44 Link22s45 Link22s46 Link22s47 Link22s48 Link22s49 Link22s50 Link22s51 Link22s52 Link22s53 Link22s54 Link22s55 Link22s56 Link22s57 Link22s58 Link22s59 Link22s60 Link22s61 Link22s62 Link22s63 Link22s64 Link22s65 Link22s66 Link22s67 Link22s68 Link22s69 Link22s70 Link22s71 Link22s72 Link22s73 Link22s74 Link22s75 Link22s76 Link22s77 Link22s78 Link22s79 Link22s80 Link22s81 Link22s82 Link22s83 Link22s84 Link22s85 Link22s86 Link22s87 Link22s88 Link22s89 Link22s90 Link22s91 Link22s92 Link22s93 Link22s94 Link22s95 Link22s96 Link22s97 Link22s98 Link22s99 Link22s100 Link22s101 Link22s102 Link22s103 Link22s104 Link22s105 Link22s106 Link22s107 Link22s108 Link22s109 Link22s110 Link22s111 Link22s112 Link22s113 Link22s114 Link22s115 Link22s116 Link22s117 Link22s118 Link22s119 Link22s120 Link22s121 Link22s122 Link22s123 Link22s124 Link22s125 Link22s126 Link22s127 Link22s128 Link22s129 Link22s130 Link22s131 Link22s132 Link22s133 Link22s134 Link22s135 Link22s136 Link22s137 Link22s138 Link22s139 Link22s140 Link22s141 Link22s142 Link22s143 Link22s144 Link22s145 Link22s146 Link22s147 Link22s148 Link22s149.

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
  l22s35_all ++
  l22s36_all ++
  l22s37_all ++
  l22s38_all ++
  l22s39_all ++
  l22s40_all ++
  l22s41_all ++
  l22s42_all ++
  l22s43_all ++
  l22s44_all ++
  l22s45_all ++
  l22s46_all ++
  l22s47_all ++
  l22s48_all ++
  l22s49_all ++
  l22s50_all ++
  l22s51_all ++
  l22s52_all ++
  l22s53_all ++
  l22s54_all ++
  l22s55_all ++
  l22s56_all ++
  l22s57_all ++
  l22s58_all ++
  l22s59_all ++
  l22s60_all ++
  l22s61_all ++
  l22s62_all ++
  l22s63_all ++
  l22s64_all ++
  l22s65_all ++
  l22s66_all ++
  l22s67_all ++
  l22s68_all ++
  l22s69_all ++
  l22s70_all ++
  l22s71_all ++
  l22s72_all ++
  l22s73_all ++
  l22s74_all ++
  l22s75_all ++
  l22s76_all ++
  l22s77_all ++
  l22s78_all ++
  l22s79_all ++
  l22s80_all ++
  l22s81_all ++
  l22s82_all ++
  l22s83_all ++
  l22s84_all ++
  l22s85_all ++
  l22s86_all ++
  l22s87_all ++
  l22s88_all ++
  l22s89_all ++
  l22s90_all ++
  l22s91_all ++
  l22s92_all ++
  l22s93_all ++
  l22s94_all ++
  l22s95_all ++
  l22s96_all ++
  l22s97_all ++
  l22s98_all ++
  l22s99_all ++
  l22s100_all ++
  l22s101_all ++
  l22s102_all ++
  l22s103_all ++
  l22s104_all ++
  l22s105_all ++
  l22s106_all ++
  l22s107_all ++
  l22s108_all ++
  l22s109_all ++
  l22s110_all ++
  l22s111_all ++
  l22s112_all ++
  l22s113_all ++
  l22s114_all ++
  l22s115_all ++
  l22s116_all ++
  l22s117_all ++
  l22s118_all ++
  l22s119_all ++
  l22s120_all ++
  l22s121_all ++
  l22s122_all ++
  l22s123_all ++
  l22s124_all ++
  l22s125_all ++
  l22s126_all ++
  l22s127_all ++
  l22s128_all ++
  l22s129_all ++
  l22s130_all ++
  l22s131_all ++
  l22s132_all ++
  l22s133_all ++
  l22s134_all ++
  l22s135_all ++
  l22s136_all ++
  l22s137_all ++
  l22s138_all ++
  l22s139_all ++
  l22s140_all ++
  l22s141_all ++
  l22s142_all ++
  l22s143_all ++
  l22s144_all ++
  l22s145_all ++
  l22s146_all ++
  l22s147_all ++
  l22s148_all ++
  l22s149_all.

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
  apply trees_okb_app; [exact l22s35_all_ok |].
  apply trees_okb_app; [exact l22s36_all_ok |].
  apply trees_okb_app; [exact l22s37_all_ok |].
  apply trees_okb_app; [exact l22s38_all_ok |].
  apply trees_okb_app; [exact l22s39_all_ok |].
  apply trees_okb_app; [exact l22s40_all_ok |].
  apply trees_okb_app; [exact l22s41_all_ok |].
  apply trees_okb_app; [exact l22s42_all_ok |].
  apply trees_okb_app; [exact l22s43_all_ok |].
  apply trees_okb_app; [exact l22s44_all_ok |].
  apply trees_okb_app; [exact l22s45_all_ok |].
  apply trees_okb_app; [exact l22s46_all_ok |].
  apply trees_okb_app; [exact l22s47_all_ok |].
  apply trees_okb_app; [exact l22s48_all_ok |].
  apply trees_okb_app; [exact l22s49_all_ok |].
  apply trees_okb_app; [exact l22s50_all_ok |].
  apply trees_okb_app; [exact l22s51_all_ok |].
  apply trees_okb_app; [exact l22s52_all_ok |].
  apply trees_okb_app; [exact l22s53_all_ok |].
  apply trees_okb_app; [exact l22s54_all_ok |].
  apply trees_okb_app; [exact l22s55_all_ok |].
  apply trees_okb_app; [exact l22s56_all_ok |].
  apply trees_okb_app; [exact l22s57_all_ok |].
  apply trees_okb_app; [exact l22s58_all_ok |].
  apply trees_okb_app; [exact l22s59_all_ok |].
  apply trees_okb_app; [exact l22s60_all_ok |].
  apply trees_okb_app; [exact l22s61_all_ok |].
  apply trees_okb_app; [exact l22s62_all_ok |].
  apply trees_okb_app; [exact l22s63_all_ok |].
  apply trees_okb_app; [exact l22s64_all_ok |].
  apply trees_okb_app; [exact l22s65_all_ok |].
  apply trees_okb_app; [exact l22s66_all_ok |].
  apply trees_okb_app; [exact l22s67_all_ok |].
  apply trees_okb_app; [exact l22s68_all_ok |].
  apply trees_okb_app; [exact l22s69_all_ok |].
  apply trees_okb_app; [exact l22s70_all_ok |].
  apply trees_okb_app; [exact l22s71_all_ok |].
  apply trees_okb_app; [exact l22s72_all_ok |].
  apply trees_okb_app; [exact l22s73_all_ok |].
  apply trees_okb_app; [exact l22s74_all_ok |].
  apply trees_okb_app; [exact l22s75_all_ok |].
  apply trees_okb_app; [exact l22s76_all_ok |].
  apply trees_okb_app; [exact l22s77_all_ok |].
  apply trees_okb_app; [exact l22s78_all_ok |].
  apply trees_okb_app; [exact l22s79_all_ok |].
  apply trees_okb_app; [exact l22s80_all_ok |].
  apply trees_okb_app; [exact l22s81_all_ok |].
  apply trees_okb_app; [exact l22s82_all_ok |].
  apply trees_okb_app; [exact l22s83_all_ok |].
  apply trees_okb_app; [exact l22s84_all_ok |].
  apply trees_okb_app; [exact l22s85_all_ok |].
  apply trees_okb_app; [exact l22s86_all_ok |].
  apply trees_okb_app; [exact l22s87_all_ok |].
  apply trees_okb_app; [exact l22s88_all_ok |].
  apply trees_okb_app; [exact l22s89_all_ok |].
  apply trees_okb_app; [exact l22s90_all_ok |].
  apply trees_okb_app; [exact l22s91_all_ok |].
  apply trees_okb_app; [exact l22s92_all_ok |].
  apply trees_okb_app; [exact l22s93_all_ok |].
  apply trees_okb_app; [exact l22s94_all_ok |].
  apply trees_okb_app; [exact l22s95_all_ok |].
  apply trees_okb_app; [exact l22s96_all_ok |].
  apply trees_okb_app; [exact l22s97_all_ok |].
  apply trees_okb_app; [exact l22s98_all_ok |].
  apply trees_okb_app; [exact l22s99_all_ok |].
  apply trees_okb_app; [exact l22s100_all_ok |].
  apply trees_okb_app; [exact l22s101_all_ok |].
  apply trees_okb_app; [exact l22s102_all_ok |].
  apply trees_okb_app; [exact l22s103_all_ok |].
  apply trees_okb_app; [exact l22s104_all_ok |].
  apply trees_okb_app; [exact l22s105_all_ok |].
  apply trees_okb_app; [exact l22s106_all_ok |].
  apply trees_okb_app; [exact l22s107_all_ok |].
  apply trees_okb_app; [exact l22s108_all_ok |].
  apply trees_okb_app; [exact l22s109_all_ok |].
  apply trees_okb_app; [exact l22s110_all_ok |].
  apply trees_okb_app; [exact l22s111_all_ok |].
  apply trees_okb_app; [exact l22s112_all_ok |].
  apply trees_okb_app; [exact l22s113_all_ok |].
  apply trees_okb_app; [exact l22s114_all_ok |].
  apply trees_okb_app; [exact l22s115_all_ok |].
  apply trees_okb_app; [exact l22s116_all_ok |].
  apply trees_okb_app; [exact l22s117_all_ok |].
  apply trees_okb_app; [exact l22s118_all_ok |].
  apply trees_okb_app; [exact l22s119_all_ok |].
  apply trees_okb_app; [exact l22s120_all_ok |].
  apply trees_okb_app; [exact l22s121_all_ok |].
  apply trees_okb_app; [exact l22s122_all_ok |].
  apply trees_okb_app; [exact l22s123_all_ok |].
  apply trees_okb_app; [exact l22s124_all_ok |].
  apply trees_okb_app; [exact l22s125_all_ok |].
  apply trees_okb_app; [exact l22s126_all_ok |].
  apply trees_okb_app; [exact l22s127_all_ok |].
  apply trees_okb_app; [exact l22s128_all_ok |].
  apply trees_okb_app; [exact l22s129_all_ok |].
  apply trees_okb_app; [exact l22s130_all_ok |].
  apply trees_okb_app; [exact l22s131_all_ok |].
  apply trees_okb_app; [exact l22s132_all_ok |].
  apply trees_okb_app; [exact l22s133_all_ok |].
  apply trees_okb_app; [exact l22s134_all_ok |].
  apply trees_okb_app; [exact l22s135_all_ok |].
  apply trees_okb_app; [exact l22s136_all_ok |].
  apply trees_okb_app; [exact l22s137_all_ok |].
  apply trees_okb_app; [exact l22s138_all_ok |].
  apply trees_okb_app; [exact l22s139_all_ok |].
  apply trees_okb_app; [exact l22s140_all_ok |].
  apply trees_okb_app; [exact l22s141_all_ok |].
  apply trees_okb_app; [exact l22s142_all_ok |].
  apply trees_okb_app; [exact l22s143_all_ok |].
  apply trees_okb_app; [exact l22s144_all_ok |].
  apply trees_okb_app; [exact l22s145_all_ok |].
  apply trees_okb_app; [exact l22s146_all_ok |].
  apply trees_okb_app; [exact l22s147_all_ok |].
  apply trees_okb_app; [exact l22s148_all_ok |].
  exact l22s149_all_ok.
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
