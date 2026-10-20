(** * Combining the link descent with the meeting-neighbourhood bound

    [docs/roadmap.md] §67.  Two facts about 4-uniform 3-sunflower-free
    families have been established separately and never combined:

    - the link descent of §62–§65: if some member [R] is disjoint from at
      least 23 other members, then [|F| ≤ 54]  (proved there given
      [ι(4) ≤ 27] and the validated link census, by certificates checked
      outside the kernel);
    - [ABCDN26] Proposition 6.5: for every member [R], at most 56 members
      meet [R], counting [R] itself.

    Every member either meets [R] or is disjoint from it, so for a family
    with a member disjoint from at most 22 others, [|F| ≤ 22 + 56 = 78],
    and otherwise [|F| ≤ 54].  Hence [g(4) ≤ 78], on exactly the
    hypotheses of the two inputs.  Neither input is proved in this kernel;
    both enter as explicit premises, so [Print Assumptions] is closed and
    the theorem says precisely what the two inputs buy together. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Sunflower Require Import Sets Sunflower Intersecting IotaRate Stability4.

(** Members of [F] that meet [R]; [R] itself is among them when nonempty.
    This is [ABCDN26]'s [N_F[R]]. *)
Definition Meeting (R : list nat) (F : Family) : Family :=
  filter (fun C => negb (disjointb R C)) F.

Lemma meeting_disjoint_partition :
  forall R F, length (DisjointFrom R F) + length (Meeting R F) = length F.
Proof.
  intros R F; unfold DisjointFrom, Meeting.
  apply filter_partition_length_family.
Qed.

(** The descent, as a hypothesis: a link of at least 23 members caps the
    family at 54. *)
Definition LinkDescent (b N M : nat) : Prop :=
  forall (F : Family) (R : list nat),
    Uniform b F -> Distinct F -> ~ ContainsKSunflower 3 F -> In R F ->
    N <= length (DisjointFrom R F) -> length F <= M.

(** The meeting-neighbourhood bound, as a hypothesis: at most [H] members
    meet any given member. *)
Definition MeetingBound (b H : nat) : Prop :=
  forall (F : Family) (R : list nat),
    Uniform b F -> Distinct F -> ~ ContainsKSunflower 3 F -> In R F ->
    length (Meeting R F) <= H.

(** The abstract combination. *)
Theorem g_at_most_of_descent_and_meeting :
  forall b N M H,
    LinkDescent b N M -> MeetingBound b H ->
    GAtMost b (Nat.max M (N - 1 + H)).
Proof.
  intros b N M H Hdesc Hmeet F HU HD Hno.
  destruct F as [| R F'] eqn:EF.
  - simpl; lia.
  - assert (HR : In R F) by (rewrite EF; left; reflexivity).
    rewrite <- EF in *.
    destruct (le_lt_dec N (length (DisjointFrom R F))) as [Hge | Hlt].
    + pose proof (Hdesc F R HU HD Hno HR Hge); lia.
    + pose proof (Hmeet F R HU HD Hno HR) as Hm.
      pose proof (meeting_disjoint_partition R F) as Hp.
      lia.
Qed.

(** The instance at uniformity 4: descent threshold 23 to a cap of 54,
    meeting bound 56, conclusion 78. *)
Corollary g_four_at_most_78 :
  LinkDescent 4 23 54 -> MeetingBound 4 56 -> GAtMost 4 78.
Proof.
  intros Hd Hm.
  pose proof (g_at_most_of_descent_and_meeting 4 23 54 56 Hd Hm) as H.
  replace (Nat.max 54 (23 - 1 + 56)) with 78 in H by reflexivity.
  exact H.
Qed.

(** Sanity: the combination is not vacuous and 78 is what the arithmetic
    gives, not less.  With the descent threshold at 23 the bound cannot be
    lowered by this argument alone: a family with a 22-member link and 56
    members meeting [R] would have exactly 78 members. *)
Lemma seventy_eight_is_the_arithmetic : 22 + 56 = 78.
Proof. reflexivity. Qed.

(** The published route, in the same shape: [ι(4) ≤ 27] bounds every link
    by 27, so with the meeting bound 56 the family has at most 83 members
    ([ABCDN26] Theorem 6.9).  Recorded so the two routes sit side by side. *)
Theorem g_four_at_most_83_of_iota :
  IotaAtMost 4 27 -> MeetingBound 4 56 -> GAtMost 4 83.
Proof.
  intros Hiota Hm F HU HD Hno.
  destruct F as [| R F'] eqn:EF; [simpl; lia |].
  assert (HR : In R F) by (rewrite EF; left; reflexivity).
  rewrite <- EF in *.
  pose proof (Hm F R HU HD Hno HR) as Hmeet.
  pose proof (meeting_disjoint_partition R F) as Hp.
  destruct (DisjointFrom R F) as [| C D'] eqn:ED.
  - simpl in Hp; lia.
  - (* R is nonempty: it is 4-uniform. *)
    assert (Hz : exists z, In z R).
    { destruct R as [| z R'].
      - exfalso. unfold Uniform in HU. rewrite Forall_forall in HU.
        specialize (HU [] HR). unfold UniformSet in HU. simpl in HU. lia.
      - exists z; left; reflexivity. }
    rewrite <- ED in *.
    pose proof (DisjointFrom_length_le 4 27 F R Hiota HU HD Hno HR Hz).
    lia.
Qed.
