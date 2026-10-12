(** * Link size 22 in the kernel, and the descent from 22

    The 69,616 link classes of size 22 ([classes_22.txt.gz]) each carry a
    branch-and-bound tree over the finer model of [Link23], checked by
    [classcheck_m] in 133 modules ([Link22s0] to
    [Link22s132]).  Each shard exports its class list and proves every
    class [CheckedClass]; the certificates stay inside that opaque proof.
    With the LP census of sizes 23–27 and the eleven trees at 23 this
    gives the descent at 22 and [g(4) ≤ 77], conditional on [ι(4) ≤ 27]
    and on the census being complete from 22 up ([CensusL classes22 22]).
    See docs/roadmap.md §70–§71. *)

From Coq Require Import List Lia.
Import ListNotations.
From Sunflower Require Import Sunflower IotaRate LinkCombine LinkLP Link23 LinkCerts23 Link23Certs
  Link22s0 Link22s1 Link22s2 Link22s3 Link22s4 Link22s5 Link22s6 Link22s7 Link22s8 Link22s9 Link22s10 Link22s11 Link22s12 Link22s13 Link22s14 Link22s15 Link22s16 Link22s17 Link22s18 Link22s19 Link22s20 Link22s21 Link22s22 Link22s23 Link22s24 Link22s25 Link22s26 Link22s27 Link22s28 Link22s29 Link22s30 Link22s31 Link22s32 Link22s33 Link22s34 Link22s35 Link22s36 Link22s37 Link22s38 Link22s39 Link22s40 Link22s41 Link22s42 Link22s43 Link22s44 Link22s45 Link22s46 Link22s47 Link22s48 Link22s49 Link22s50 Link22s51 Link22s52 Link22s53 Link22s54 Link22s55 Link22s56 Link22s57 Link22s58 Link22s59 Link22s60 Link22s61 Link22s62 Link22s63 Link22s64 Link22s65 Link22s66 Link22s67 Link22s68 Link22s69 Link22s70 Link22s71 Link22s72 Link22s73 Link22s74 Link22s75 Link22s76 Link22s77 Link22s78 Link22s79 Link22s80 Link22s81 Link22s82 Link22s83 Link22s84 Link22s85 Link22s86 Link22s87 Link22s88 Link22s89 Link22s90 Link22s91 Link22s92 Link22s93 Link22s94 Link22s95 Link22s96 Link22s97 Link22s98 Link22s99 Link22s100 Link22s101 Link22s102 Link22s103 Link22s104 Link22s105 Link22s106 Link22s107 Link22s108 Link22s109 Link22s110 Link22s111 Link22s112 Link22s113 Link22s114 Link22s115 Link22s116 Link22s117 Link22s118 Link22s119 Link22s120 Link22s121 Link22s122 Link22s123 Link22s124 Link22s125 Link22s126 Link22s127 Link22s128 Link22s129 Link22s130 Link22s131 Link22s132.

(** Every certified link class of size 22 to 27. *)
Definition classes22 : list Family :=
  map fst cls23_all ++
  map fst link23_all ++
  l22s0_classes ++
  l22s1_classes ++
  l22s2_classes ++
  l22s3_classes ++
  l22s4_classes ++
  l22s5_classes ++
  l22s6_classes ++
  l22s7_classes ++
  l22s8_classes ++
  l22s9_classes ++
  l22s10_classes ++
  l22s11_classes ++
  l22s12_classes ++
  l22s13_classes ++
  l22s14_classes ++
  l22s15_classes ++
  l22s16_classes ++
  l22s17_classes ++
  l22s18_classes ++
  l22s19_classes ++
  l22s20_classes ++
  l22s21_classes ++
  l22s22_classes ++
  l22s23_classes ++
  l22s24_classes ++
  l22s25_classes ++
  l22s26_classes ++
  l22s27_classes ++
  l22s28_classes ++
  l22s29_classes ++
  l22s30_classes ++
  l22s31_classes ++
  l22s32_classes ++
  l22s33_classes ++
  l22s34_classes ++
  l22s35_classes ++
  l22s36_classes ++
  l22s37_classes ++
  l22s38_classes ++
  l22s39_classes ++
  l22s40_classes ++
  l22s41_classes ++
  l22s42_classes ++
  l22s43_classes ++
  l22s44_classes ++
  l22s45_classes ++
  l22s46_classes ++
  l22s47_classes ++
  l22s48_classes ++
  l22s49_classes ++
  l22s50_classes ++
  l22s51_classes ++
  l22s52_classes ++
  l22s53_classes ++
  l22s54_classes ++
  l22s55_classes ++
  l22s56_classes ++
  l22s57_classes ++
  l22s58_classes ++
  l22s59_classes ++
  l22s60_classes ++
  l22s61_classes ++
  l22s62_classes ++
  l22s63_classes ++
  l22s64_classes ++
  l22s65_classes ++
  l22s66_classes ++
  l22s67_classes ++
  l22s68_classes ++
  l22s69_classes ++
  l22s70_classes ++
  l22s71_classes ++
  l22s72_classes ++
  l22s73_classes ++
  l22s74_classes ++
  l22s75_classes ++
  l22s76_classes ++
  l22s77_classes ++
  l22s78_classes ++
  l22s79_classes ++
  l22s80_classes ++
  l22s81_classes ++
  l22s82_classes ++
  l22s83_classes ++
  l22s84_classes ++
  l22s85_classes ++
  l22s86_classes ++
  l22s87_classes ++
  l22s88_classes ++
  l22s89_classes ++
  l22s90_classes ++
  l22s91_classes ++
  l22s92_classes ++
  l22s93_classes ++
  l22s94_classes ++
  l22s95_classes ++
  l22s96_classes ++
  l22s97_classes ++
  l22s98_classes ++
  l22s99_classes ++
  l22s100_classes ++
  l22s101_classes ++
  l22s102_classes ++
  l22s103_classes ++
  l22s104_classes ++
  l22s105_classes ++
  l22s106_classes ++
  l22s107_classes ++
  l22s108_classes ++
  l22s109_classes ++
  l22s110_classes ++
  l22s111_classes ++
  l22s112_classes ++
  l22s113_classes ++
  l22s114_classes ++
  l22s115_classes ++
  l22s116_classes ++
  l22s117_classes ++
  l22s118_classes ++
  l22s119_classes ++
  l22s120_classes ++
  l22s121_classes ++
  l22s122_classes ++
  l22s123_classes ++
  l22s124_classes ++
  l22s125_classes ++
  l22s126_classes ++
  l22s127_classes ++
  l22s128_classes ++
  l22s129_classes ++
  l22s130_classes ++
  l22s131_classes ++
  l22s132_classes.

Lemma classes22_checked : forall D, In D classes22 -> CheckedAny D.
Proof.
  unfold classes22.
  apply checked_app; [exact (checked_reps cls23_all cls23_all_ok) |].
  apply checked_app; [exact (checked_trees link23_all link23_all_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s0_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s1_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s2_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s3_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s4_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s5_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s6_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s7_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s8_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s9_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s10_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s11_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s12_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s13_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s14_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s15_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s16_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s17_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s18_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s19_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s20_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s21_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s22_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s23_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s24_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s25_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s26_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s27_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s28_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s29_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s30_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s31_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s32_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s33_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s34_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s35_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s36_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s37_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s38_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s39_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s40_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s41_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s42_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s43_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s44_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s45_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s46_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s47_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s48_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s49_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s50_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s51_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s52_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s53_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s54_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s55_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s56_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s57_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s58_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s59_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s60_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s61_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s62_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s63_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s64_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s65_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s66_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s67_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s68_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s69_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s70_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s71_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s72_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s73_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s74_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s75_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s76_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s77_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s78_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s79_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s80_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s81_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s82_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s83_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s84_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s85_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s86_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s87_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s88_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s89_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s90_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s91_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s92_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s93_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s94_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s95_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s96_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s97_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s98_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s99_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s100_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s101_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s102_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s103_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s104_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s105_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s106_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s107_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s108_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s109_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s110_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s111_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s112_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s113_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s114_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s115_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s116_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s117_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s118_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s119_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s120_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s121_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s122_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s123_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s124_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s125_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s126_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s127_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s128_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s129_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s130_ok) |].
  apply checked_app; [exact (checked_hinted _ l22s131_ok) |].
  exact (checked_hinted _ l22s132_ok).
Qed.

(** The descent at link size 22 and above. *)
Theorem descent_22 :
  IotaAtMost 4 27 -> CensusL classes22 22 -> LinkDescent 4 22 54.
Proof. intros Hi Hc; exact (descent_of_censusL Hi classes22 22 ltac:(lia) classes22_checked Hc). Qed.

Theorem g_four_at_most_77_of_census_22 :
  IotaAtMost 4 27 -> CensusL classes22 22 -> MeetingBound 4 56 -> GAtMost 4 77.
Proof.
  intros Hi Hc Hm.
  pose proof (g_at_most_of_descent_and_meeting 4 22 54 56 (descent_22 Hi Hc) Hm) as H.
  replace (Nat.max 54 (22 - 1 + 56)) with 77 in H by reflexivity. exact H.
Qed.
