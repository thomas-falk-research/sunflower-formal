(** * One premise instead of two: the census implies [ι(4) ≤ 27]

    [Covered] preserves the number of distinct members, and every class
    of [classes21] has at most 27 members (decided by [vm_compute]), so a
    family of 28 or more members would be covered by a listed class of
    the same size, which does not exist.  Hence [CensusL classes21 21]
    implies [IotaAtMost 4 27] ([iota_of_census]), and [g(4) ≤ 76] rests on
    the census and the meeting bound alone ([g_four_at_most_76_of_census]).
    Both premises came from the same search, so this does not reduce trust
    in substance; it makes the assumption one precise statement.  See
    docs/census_certification.md, stage 1. *)

From Coq Require Import List Lia Arith.
Import ListNotations.
From Sunflower Require Import Sets Sunflower IotaRate LinkCombine DirectSum LinkLP Link23 Link21Certs.

Lemma Covered_length : forall D Dk, Distinct D -> Distinct Dk -> Covered D Dk -> length D = length Dk.
Proof.
  intros D Dk HD HDk [g [h [Hhg [Hgh [S1 S2]]]]].
  rewrite <- (rmapF_length g Dk).
  apply length_SetEq_families; [exact HD | apply (rmapF_Distinct g h Hhg), HDk | exact S1 | exact S2].
Qed.

(** Every listed class has at most 27 members. *)
Lemma classes21_at_most_27 : forallb (fun D => Nat.leb (length D) 27) classes21 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem iota_of_census : CensusL classes21 21 -> IotaAtMost 4 27.
Proof.
  intros Hc H HU HD HI Hno.
  destruct (le_lt_dec (length H) 27) as [Hl | Hl]; [exact Hl | exfalso].
  destruct (Hc H HU HD HI Hno ltac:(lia)) as [Dk [Hin Hcov]].
  destruct (classes21_checked Dk Hin) as [_ [HDk _]].
  pose proof (Covered_length H Dk HD HDk Hcov) as E.
  pose proof classes21_at_most_27 as Hs. rewrite forallb_forall in Hs.
  specialize (Hs Dk Hin). apply Nat.leb_le in Hs. lia.
Qed.

(** [g(4) ≤ 76] from the census and the meeting bound alone. *)
Theorem g_four_at_most_76_of_census : CensusL classes21 21 -> MeetingBound 4 56 -> GAtMost 4 76.
Proof.
  intros Hc Hm. exact (g_four_at_most_76_of_census_21 (iota_of_census Hc) Hc Hm).
Qed.
