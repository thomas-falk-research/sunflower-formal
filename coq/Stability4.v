(** * Stability4.v — a member disjoint from 27 others caps the family at 54

    [docs/roadmap.md] §61 reduced Palvolgyi's equality [g(4) = 54] in its
    *stability case* — some member [R] is disjoint from 27 others — to a
    joint bound on the members outside the Abbott–Hanson family, and left
    it open. This file closes it, and the argument is shorter than the
    reduction was.

    ** The one new fact: trace saturation

    Call a family [A] **trace-saturated** at uniformity [b] when every
    [b]-set [S] that meets some member of [A] *and* has a point in no
    member of [A] forms a 3-sunflower with two members of [A]. As with
    [Maximal.v], [S] interacts with [A] only through its trace on the
    ground set, so this is a finite question about traces, and
    [saturated_of_certificate] turns a `forallb` over the sublists of the
    ground set into the statement for every [S] on every ground set.

    [iota4_trace_saturated]: the Abbott–Hanson family is trace-saturated.
    Each of the 129 nonempty traces of size at most 3 on its nine points
    has two members [C1], [C2] with [T ∩ C1 = T ∩ C2 = C1 ∩ C2]. This is
    strictly more than maximality ([Maximal.iota4_is_maximal_intersecting]
    forbids only sets meeting *every* member); here even a set meeting
    *one* member is forbidden, as long as it also leaves the nine points.

    ** The consequence

    [length_le_of_trace_saturated_link]: if [F] is sunflower-free,
    [R ∈ F], the members disjoint from [R] form a nonempty trace-saturated
    family [D], and [IotaAtMost b N], then [|F| <= |D| + N]. Every member
    outside [D] meets [R], which lies outside every member of [D], so by
    saturation it cannot meet [D] at all; two such members that were
    disjoint would make three pairwise disjoint sets with any member of
    [D]; so they form an intersecting family, of size at most [N].

    [stability_at_four]: under [IotaAtMost 4 27], a sunflower-free family
    of 4-sets in which the members disjoint from some [R] are a relabelled
    copy of [Product.iota4] has at most [54] members. Nothing is assumed
    about the ground set.

    ** What this does and does not give

    [IotaAtMost 4 27] is a hypothesis: it is VALIDATED by two independent
    exhaustive searches ([docs/ladder/iota4_replication/]), not proved.
    So is the uniqueness of the 27-member family, which is what turns
    "[R] is disjoint from 27 members" into the relabelled-copy hypothesis
    here. With both, a family beating 54 has every member disjoint from at
    most 26 others. That is the whole content: [g(4) = 54] stays open.

    Zero axioms, zero admits. *)

From Coq Require Import List Arith Lia Bool.
From Coq Require Import PeanoNat FinFun.
From Sunflower Require Import Sets Sunflower LowerBound HallCore F23
     Intersecting IotaRate SliceRank DirectSum Product Reflect.
Import ListNotations.

(** ** Definitions *)

(** The members of [F] disjoint from [R]: the neighbourhood of [R] in the
    disjointness graph. *)
Definition DisjointFrom (R : list nat) (F : Family) : Family :=
  filter (fun C => disjointb R C) F.

(** Stated for every list [S]: no ground set appears. *)
Definition TraceSaturated (b : nat) (A : Family) : Prop :=
  forall S : list nat,
    UniformSet b S ->
    (exists y C, In y S /\ In C A /\ In y C) ->
    (exists x, In x S /\ forall C, In C A -> ~ In x C) ->
    ContainsKSunflower 3 (S :: A).

(** ** Two small facts about [ContainsKSunflower] *)

Lemma ContainsKSunflower_SubFamilySetEq :
  forall k F G, ContainsKSunflower k F -> SubFamilySetEq F G ->
                ContainsKSunflower k G.
Proof.
  intros k F G [S [HSF HK]] HFG; exists S; split; [| exact HK].
  intros A HA.
  destruct (HSF A HA) as [B [HB EAB]].
  destruct (HFG B HB) as [C [HC EBC]].
  exists C; split; [exact HC | exact (SetEq_trans EAB EBC)].
Qed.

Arguments ContainsKSunflower_SubFamilySetEq {k F G}.

Lemma ContainsKSunflower_rmapF :
  forall g h, (forall x, h (g x) = x) -> (forall x, g (h x) = x) ->
  forall F, ContainsKSunflower 3 F -> ContainsKSunflower 3 (rmapF g F).
Proof.
  intros g h Hgh Hhg F Hc.
  destruct (contains_3_sunflower_dec (rmapF g F)) as [H | H]; [exact H |].
  exfalso; apply (rmapF_no_sunflower h g Hhg 3) in H; apply H.
  assert (E : rmapF h (rmapF g F) = F).
  { unfold rmapF, rmap; rewrite map_map.
    rewrite (map_ext (fun A => map h (map g A)) (fun A => A)); [apply map_id |].
    intros A; rewrite map_map.
    rewrite (map_ext (fun x => h (g x)) (fun x => x) Hgh); apply map_id. }
  rewrite E; exact Hc.
Qed.

(** ** The certificate *)

Definition saturation_witnessb (T : list nat) (A : Family) : bool :=
  existsb (fun C1 =>
    existsb (fun C2 =>
      negb (seteqb C1 C2)
      && seteqb (inter T C1) (inter C1 C2)
      && seteqb (inter T C2) (inter C1 C2)) A) A.

(** Every nonempty trace of size below [b] has a witness pair. *)
Definition saturation_certificate (b : nat) (A : Family) (U : list nat) : bool :=
  forallb
    (fun T => implb (negb (Nat.eqb (length T) 0) && Nat.ltb (length T) b)
                    (saturation_witnessb T A))
    (sublists U).

(** Every point of [U] is in some member. Needed so that a point of [S]
    in no member is also a point outside [U], which is what caps the
    trace at [b - 1] points. *)
Definition coversb (A : Family) (U : list nat) : bool :=
  forallb (fun x => existsb (fun C => memb x C) A) U.

Lemma seteqb_false_of_point :
  forall A B x, In x A -> ~ In x B -> seteqb A B = false.
Proof.
  intros A B x HA HB.
  destruct (seteqb A B) eqn:E; [| reflexivity].
  exfalso; apply seteqb_correct in E; apply HB, (proj1 E), HA.
Qed.

Theorem saturated_of_certificate :
  forall b A U,
    NoDup U -> Grounded A U -> coversb A U = true ->
    saturation_certificate b A U = true ->
    TraceSaturated b A.
Proof.
  intros b A U HndU Hgr Hcov Hcert S [HlenS HndS] [y [C [HyS [HC HyC]]]]
         [x [HxS Hxout]].
  set (T := filter (fun z => memb z S) U).
  assert (HTsub : In T (sublists U)) by apply filter_in_sublists.
  assert (HTnd : NoDup T)
    by (eapply sublists_NoDup_members; [exact HndU | exact HTsub]).
  assert (HinT : forall z, In z T <-> In z U /\ In z S).
  { intros z; unfold T; rewrite filter_In, memb_true_iff; tauto. }
  (* x is in no member, hence (by covering) not in U, hence not in T *)
  assert (HxU : ~ In x U).
  { intros HxU.
    pose proof (proj1 (forallb_forall _ _) Hcov x HxU) as Hc; cbv beta in Hc.
    apply existsb_exists in Hc as [C' [HC' Hm]].
    apply memb_true_iff in Hm; exact (Hxout C' HC' Hm). }
  assert (HTlen : length T < b).
  { assert (Hnd2 : NoDup (x :: T))
      by (constructor; [intro H; apply HxU, (proj1 (proj1 (HinT x) H)) | exact HTnd]).
    assert (Hincl : incl (x :: T) S).
    { intros z [Ez | Hz]; [subst z; exact HxS | exact (proj2 (proj1 (HinT z) Hz))]. }
    pose proof (NoDup_incl_length Hnd2 Hincl) as Hl; simpl in Hl; lia. }
  assert (HTne : length T <> 0).
  { assert (HyT : In y T) by (apply HinT; split; [exact (Hgr C HC y HyC) | exact HyS]).
    destruct T; [inversion HyT | discriminate]. }
  (* the trace of S on a member is the trace of T on it *)
  assert (Htr : forall C', In C' A -> SetEq (inter S C') (inter T C')).
  { intros C' HC'; split; intros z Hz; apply in_inter_iff in Hz as [Hz1 Hz2];
      apply in_inter_iff; split; try exact Hz2.
    - apply HinT; split; [exact (Hgr C' HC' z Hz2) | exact Hz1].
    - exact (proj2 (proj1 (HinT z) Hz1)). }
  pose proof (proj1 (forallb_forall _ _) Hcert T HTsub) as Hw; cbv beta in Hw.
  assert (Hpre : negb (Nat.eqb (length T) 0) && Nat.ltb (length T) b = true).
  { apply andb_true_iff; split.
    - apply negb_true_iff, Nat.eqb_neq; exact HTne.
    - apply Nat.ltb_lt; exact HTlen. }
  rewrite Hpre in Hw; simpl in Hw.
  apply existsb_exists in Hw as [C1 [HC1 Hw]].
  apply existsb_exists in Hw as [C2 [HC2 Hw]].
  apply andb_true_iff in Hw as [Hw E2]; apply andb_true_iff in Hw as [Hne E1].
  apply seteqb_correct in E1; apply seteqb_correct in E2.
  apply sunflower3b_complete.
  apply existsb_exists; exists S; split; [left; reflexivity |].
  apply existsb_exists; exists C1; split; [right; exact HC1 |].
  apply existsb_exists; exists C2; split; [right; exact HC2 |].
  unfold sunflower_tripleb.
  rewrite (seteqb_false_of_point S C1 x HxS (Hxout C1 HC1)).
  rewrite (seteqb_false_of_point S C2 x HxS (Hxout C2 HC2)).
  rewrite Hne; simpl.
  assert (Q1 : SetEq (inter S C1) (inter C1 C2)) by exact (SetEq_trans (Htr C1 HC1) E1).
  assert (Q2 : SetEq (inter S C2) (inter C1 C2)) by exact (SetEq_trans (Htr C2 HC2) E2).
  apply andb_true_iff; split; apply seteqb_correct.
  - exact (SetEq_trans Q1 (SetEq_sym Q2)).
  - exact Q1.
Qed.

(** ** The Abbott–Hanson family is trace-saturated *)

Lemma iota4_saturation_certificate :
  saturation_certificate 4 iota4 (seq 0 9) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma iota4_covers : coversb iota4 (seq 0 9) = true.
Proof. vm_compute; reflexivity. Qed.

Theorem iota4_trace_saturated : TraceSaturated 4 iota4.
Proof.
  apply (saturated_of_certificate 4 iota4 (seq 0 9)).
  - exact (seq_NoDup 9 0).
  - exact iota4_grounded.
  - exact iota4_covers.
  - exact iota4_saturation_certificate.
Qed.

(** ** Transport along a relabelling and set-equality of members *)

Theorem TraceSaturated_transport :
  forall g h b A B,
    (forall x, h (g x) = x) -> (forall x, g (h x) = x) ->
    SubFamilySetEq B (rmapF g A) -> SubFamilySetEq (rmapF g A) B ->
    TraceSaturated b A -> TraceSaturated b B.
Proof.
  intros g h b A B Hgh Hhg HBA HAB Hsat S [HlenS HndS]
         [y [C [HyS [HC HyC]]]] [x [HxS Hxout]].
  assert (Hc : ContainsKSunflower 3 (map h S :: A)).
  { apply Hsat.
    - split; [rewrite map_length; exact HlenS |].
      apply Injective_map_NoDup; [| exact HndS].
      intros u v E; rewrite <- (Hhg u), <- (Hhg v), E; reflexivity.
    - destruct (HBA C HC) as [C' [HC' [HCC' _]]].
      unfold rmapF, rmap in HC'; apply in_map_iff in HC' as [C0 [E HC0]]; subst C'.
      apply HCC', in_map_iff in HyC as [c [Ec Hc0]].
      exists c, C0; repeat split; [| exact HC0 | exact Hc0].
      apply in_map_iff; exists y; split; [rewrite <- Ec; apply Hgh | exact HyS].
    - exists (h x); split; [apply in_map; exact HxS |].
      intros C0 HC0 Hin.
      assert (HgC : In (map g C0) (rmapF g A))
        by (unfold rmapF, rmap; apply in_map; exact HC0).
      destruct (HAB _ HgC) as [C' [HC' [Hsub _]]].
      apply (Hxout C' HC'), Hsub, in_map_iff; exists (h x); split;
        [apply Hhg | exact Hin]. }
  apply (ContainsKSunflower_rmapF g h Hgh Hhg) in Hc.
  assert (ES : map g (map h S) = S).
  { rewrite map_map, (map_ext (fun x => g (h x)) (fun x => x) Hhg); apply map_id. }
  simpl in Hc; unfold rmap in Hc; rewrite ES in Hc.
  apply (ContainsKSunflower_SubFamilySetEq Hc).
  intros D [ED | HD]; [subst D; exists S; split; [left; reflexivity | apply SetEq_refl] |].
  destruct (HAB D HD) as [D' [HD' E]]; exists D'; split; [right; exact HD' | exact E].
Qed.

(** ** The counting theorem *)

Lemma filter_partition_length_family :
  forall (p : list nat -> bool) (F : Family),
    length (filter p F) + length (filter (fun C => negb (p C)) F) = length F.
Proof.
  intros p F; induction F as [| a F IH]; simpl; [reflexivity |].
  destruct (p a); simpl; lia.
Qed.

(** Three pairwise disjoint sets, the first two nonempty, are a
    3-sunflower with empty core. *)
Lemma three_disjoint_sunflower :
  forall F S1 S2 C,
    In S1 F -> In S2 F -> In C F ->
    (exists z, In z S1) -> (exists z, In z S2) ->
    Disjoint S1 S2 -> Disjoint S1 C -> Disjoint S2 C ->
    ContainsKSunflower 3 F.
Proof.
  intros F S1 S2 C H1 H2 H3 [z1 Hz1] [z2 Hz2] D12 D13 D23.
  apply (@ContainsKSunflower_of_incl 3 [S1; S2; C] F []).
  - intros X [E | [E | [E | []]]]; subst X; assumption.
  - reflexivity.
  - split.
    + constructor.
      * intros X [E | [E | []]] HE; subst X.
        -- exact (D12 z1 Hz1 (proj1 HE z1 Hz1)).
        -- exact (D13 z1 Hz1 (proj1 HE z1 Hz1)).
      * constructor; [| constructor; [intros _ [] | constructor]].
        intros X [E | []] HE; subst X; exact (D23 z2 Hz2 (proj1 HE z2 Hz2)).
    + assert (Hd : forall X Y, Disjoint X Y -> SetEq (inter X Y) []).
      { intros X Y HXY; rewrite (Disjoint_inter_empty HXY); apply SetEq_refl. }
      intros X Y [EX | [EX | [EX | []]]] [EY | [EY | [EY | []]]] Hne;
        subst X Y; try (exfalso; apply Hne; reflexivity); apply Hd;
        solve [assumption | apply Disjoint_sym; assumption].
Qed.

Theorem length_le_of_trace_saturated_link :
  forall b N F R,
    IotaAtMost b N ->
    Uniform b F -> Distinct F -> ~ ContainsKSunflower 3 F -> In R F ->
    DisjointFrom R F <> [] ->
    TraceSaturated b (DisjointFrom R F) ->
    length F <= length (DisjointFrom R F) + N.
Proof.
  intros b N F R Hiota HU HD Hno HR Hne Hsat.
  assert (HC0 : exists C, In C (DisjointFrom R F)).
  { destruct (DisjointFrom R F) as [| C0 D0];
      [exfalso; exact (Hne eq_refl) | exists C0; left; reflexivity]. }
  set (D := DisjointFrom R F) in *.
  set (M := filter (fun C => negb (disjointb R C)) F).
  assert (HinD : forall C, In C D <-> In C F /\ Disjoint R C).
  { intros C; unfold D, DisjointFrom; rewrite filter_In, disjointb_correct; tauto. }
  assert (HinM : forall S, In S M -> In S F /\ exists z, In z R /\ In z S).
  { intros S HS; unfold M in HS; apply filter_In in HS as [HS Hb].
    apply negb_true_iff, disjointb_false_iff in Hb; split; assumption. }
  (* every member meeting R misses every member of D *)
  assert (Hsep : forall S C, In S M -> In C D -> Disjoint S C).
  { intros S C HS HC u HuS HuC.
    destruct (HinM S HS) as [HSF [z [HzR HzS]]].
    apply Hno.
    apply (ContainsKSunflower_SubFamilySetEq (F := S :: D)).
    - apply Hsat.
      + unfold Uniform in HU; rewrite Forall_forall in HU; exact (HU S HSF).
      + exists u, C; repeat split; assumption.
      + exists z; split; [exact HzS |].
        intros C' HC' HzC'; exact (proj2 (proj1 (HinD C') HC') z HzR HzC').
    - apply SubFamilySetEq_incl; intros X [E | HX]; [subst X; exact HSF |].
      exact (proj1 (proj1 (HinD X) HX)). }
  assert (HMle : length M <= N).
  { apply Hiota.
    - apply (Uniform_sublist HU); intros X HX; exact (proj1 (HinM X HX)).
    - apply SetNoDup_filter; exact HD.
    - intros S1 S2 H1 H2 Hdis.
      destruct HC0 as [C HC].
      destruct (HinM S1 H1) as [HF1 [z1 [_ Hz1]]].
      destruct (HinM S2 H2) as [HF2 [z2 [_ Hz2]]].
      apply Hno; apply (three_disjoint_sunflower F S1 S2 C HF1 HF2
        (proj1 (proj1 (HinD C) HC)) (ex_intro _ z1 Hz1) (ex_intro _ z2 Hz2)
        Hdis (Hsep S1 C H1 HC) (Hsep S2 C H2 HC)).
    - intros Hc; apply Hno; apply (ContainsKSunflower_SubFamilySetEq Hc).
      apply SubFamilySetEq_incl; intros X HX; exact (proj1 (HinM X HX)). }
  pose proof (filter_partition_length_family (fun C => disjointb R C) F) as Hp.
  change (length D + length M = length F) in Hp; lia.
Qed.

(** The link of any member is itself intersecting (two disjoint members
    of it and [R] would be three pairwise disjoint sets), so it too is
    capped by [N]. *)
Lemma DisjointFrom_length_le :
  forall b N F R,
    IotaAtMost b N -> Uniform b F -> Distinct F -> ~ ContainsKSunflower 3 F ->
    In R F -> (exists z, In z R) ->
    length (DisjointFrom R F) <= N.
Proof.
  intros b N F R Hiota HU HD Hno HR [z Hz].
  assert (HinD : forall C, In C (DisjointFrom R F) <-> In C F /\ Disjoint R C).
  { intros C; unfold DisjointFrom; rewrite filter_In, disjointb_correct; tauto. }
  apply Hiota.
  - apply (Uniform_sublist HU); intros X HX; exact (proj1 (proj1 (HinD X) HX)).
  - apply SetNoDup_filter; exact HD.
  - intros C1 C2 H1 H2 Hdis.
    apply HinD in H1 as [HF1 HR1]; apply HinD in H2 as [HF2 HR2].
    destruct C1 as [| c1 C1'].
    + (* an empty member would be set-equal to nothing else; but Uniform b
         with b fixed makes all members the same length *)
      assert (Hl : length R = length ([] : list nat)).
      { unfold Uniform in HU; rewrite Forall_forall in HU.
        rewrite (proj1 (HU R HR)), (proj1 (HU [] HF1)); reflexivity. }
      destruct R; [inversion Hz | discriminate].
    + destruct C2 as [| c2 C2'].
      * assert (Hl : length R = length ([] : list nat)).
        { unfold Uniform in HU; rewrite Forall_forall in HU.
          rewrite (proj1 (HU R HR)), (proj1 (HU [] HF2)); reflexivity. }
        destruct R; [inversion Hz | discriminate].
      * apply Hno; apply (three_disjoint_sunflower F (c1 :: C1') (c2 :: C2') R
          HF1 HF2 HR (ex_intro _ c1 (or_introl eq_refl))
          (ex_intro _ c2 (or_introl eq_refl)) Hdis
          (Disjoint_sym HR1) (Disjoint_sym HR2)).
  - intros Hc; apply Hno; apply (ContainsKSunflower_SubFamilySetEq Hc).
    apply SubFamilySetEq_incl; intros X HX; exact (proj1 (proj1 (HinD X) HX)).
Qed.

(** ** The stability case of Palvolgyi's equality at [b = 4] *)

Theorem stability_at_four :
  IotaAtMost 4 27 ->
  forall (g h : nat -> nat) (F : Family) (R : list nat),
    (forall x, h (g x) = x) -> (forall x, g (h x) = x) ->
    Uniform 4 F -> Distinct F -> ~ ContainsKSunflower 3 F -> In R F ->
    SubFamilySetEq (DisjointFrom R F) (rmapF g iota4) ->
    SubFamilySetEq (rmapF g iota4) (DisjointFrom R F) ->
    length F <= 54.
Proof.
  intros Hiota g h F R Hgh Hhg HU HD Hno HR H1 H2.
  assert (Hne : DisjointFrom R F <> []).
  { intros E.
    assert (Hin : In (map g [0; 1; 2; 3]) (rmapF g iota4))
      by (unfold rmapF, rmap; apply in_map; left; reflexivity).
    destruct (H2 _ Hin) as [C [HC _]]; rewrite E in HC; inversion HC. }
  assert (HRne : exists z, In z R).
  { unfold Uniform in HU; rewrite Forall_forall in HU.
    destruct (HU R HR) as [Hl _].
    destruct R as [| r R']; [discriminate | exists r; left; reflexivity]. }
  pose proof (length_le_of_trace_saturated_link 4 27 F R Hiota HU HD Hno HR Hne
    (TraceSaturated_transport g h 4 iota4 (DisjointFrom R F) Hgh Hhg H1 H2
       iota4_trace_saturated)) as H.
  pose proof (DisjointFrom_length_le 4 27 F R Hiota HU HD Hno HR HRne) as H'.
  lia.
Qed.

(** ** Sanity: the hypotheses are satisfiable, and the bound is attained

    [Intersecting.double iota4] puts one copy of [iota4] on the even
    numbers and one on the odd numbers. Its first member [R] is disjoint
    from exactly the odd copy, which is [iota4] relabelled by the
    bijection [swap18] below ([i < 9 ↦ 2i+1], [9 ≤ i < 18 ↦ 2(i-9)],
    identity above). So every hypothesis of [stability_at_four] holds on
    a 54-member family, the theorem is not vacuous, and 54 cannot be
    lowered. (Added after the independent review, which found that an
    earlier version of this comment claimed the check without making it.) *)

Definition swap18 (x : nat) : nat :=
  if x <? 9 then 2 * x + 1 else if x <? 18 then 2 * (x - 9) else x.

Definition swap18_inv (y : nat) : nat :=
  if y <? 18 then (if Nat.even y then 9 + Nat.div2 y else Nat.div2 y) else y.

Lemma swap18_left : forall x, swap18_inv (swap18 x) = x.
Proof.
  intro x; destruct (x <? 18) eqn:E.
  - apply Nat.ltb_lt in E; do 18 (destruct x as [| x]; [reflexivity |]); lia.
  - apply Nat.ltb_ge in E; unfold swap18, swap18_inv.
    replace (x <? 9) with false by (symmetry; apply Nat.ltb_ge; lia).
    replace (x <? 18) with false by (symmetry; apply Nat.ltb_ge; lia).
    replace (x <? 18) with false by (symmetry; apply Nat.ltb_ge; lia).
    reflexivity.
Qed.

Lemma swap18_right : forall y, swap18 (swap18_inv y) = y.
Proof.
  intro y; destruct (y <? 18) eqn:E.
  - apply Nat.ltb_lt in E; do 18 (destruct y as [| y]; [reflexivity |]); lia.
  - apply Nat.ltb_ge in E; unfold swap18, swap18_inv.
    replace (y <? 18) with false by (symmetry; apply Nat.ltb_ge; lia).
    replace (y <? 9) with false by (symmetry; apply Nat.ltb_ge; lia).
    replace (y <? 18) with false by (symmetry; apply Nat.ltb_ge; lia).
    reflexivity.
Qed.

Theorem stability_hypotheses_satisfiable :
  let F := Intersecting.double iota4 in
  let R := map ev [0; 1; 2; 3] in
  Uniform 4 F /\ Distinct F /\ ~ ContainsKSunflower 3 F /\ In R F /\
  DisjointFrom R F = rmapF swap18 iota4 /\ length F = 54.
Proof.
  cbv zeta; split; [| split; [| split; [| split; [| split]]]].
  - apply uniformb_correct; vm_compute; reflexivity.
  - apply distinctb_correct; vm_compute; reflexivity.
  - intro Hc; pose proof (sunflower3b_sound _ Hc) as E; vm_compute in E; discriminate.
  - vm_compute; left; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

(** The certificate is not vacuous: a single member is not saturated
    (the trace [{0}] has no witness pair). *)
Example single_member_not_saturated :
  saturation_certificate 4 [[0; 1; 2; 3]] (seq 0 4) = false.
Proof. vm_compute; reflexivity. Qed.
