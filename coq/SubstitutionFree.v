(** * The substitution is sunflower-free: [g(ab) >= g(a) * iota(b)^a]

    [AHS72] (Abbott–Hanson–Sauer, J. Combin. Theory Ser. A 12 (1972)
    381–389), Lemma 6, p. 387: [psi(ab) >= psi(a) psi(b)^a], where
    [psi] is this development's [iota]. The first half of its proof —
    "First we show that F* ∈ P(ab)" — uses the outer family only through
    sunflower-freeness and the inner families through sunflower-freeness
    *and intersection*, so it proves [g(ab) >= g(a) * iota(b)^a], the form
    `docs/roadmap.md` §5 has used throughout (`docs/reading.md` A3).

    **The printed argument has a gap, repaired here.** On p. 388 it takes
    "a least integer m … such that F^(1), F^(2), F^(3) are all distinct",
    the three inner members in block [m]. That block need not exist: with
    two blocks, the patterns [(A,A,B)] and [(C,D,D)] give three distinct
    sets with no block of three distinct inner members. The repair is
    [triple_collapse] below: in every block the three inner members have
    pairwise equal intersections, and then either they are pairwise
    distinct (a sunflower of the inner family, excluded) or two of them
    are equal and *uniformity* forces the third to equal them too. The
    same lemma, applied to the outer members, replaces the paper's
    "we must therefore have F1 = F2 = F3".

    Nothing here is a new fact about sunflowers; what is new is that
    [LowerBound 9 3 20000], which [IotaRate] has carried as a hypothesis
    since §18.2, is now a theorem, and with it
    [IotaRate.substitution_would_refute_the_flat_threshold_at_nine] and
    [IotaRate.substitution_would_force_c_three_at_least_four] hold
    unconditionally. *)

From Coq Require Import List Arith Lia.
Import ListNotations.

From Sunflower Require Import Sets Sunflower LowerBound Reflect Intersecting IotaRate
                             SliceRank SpreadReduction Counting Product Substitution.

Unset Implicit Arguments.

(** ** Blocks *)

Lemma block_inj :
  forall w v v' u u', u < w -> u' < w -> v * w + u = v' * w + u' -> v = v' /\ u = u'.
Proof.
  intros w v v' u u' Hu Hu' E.
  destruct (Nat.lt_trichotomy v v') as [Hlt | [Heq | Hgt]].
  - exfalso.
    assert (v * w + w <= v' * w) by (replace (v * w + w) with (S v * w) by lia;
                                     apply Nat.mul_le_mono_r; lia).
    lia.
  - subst v'; split; [reflexivity | lia].
  - exfalso.
    assert (v' * w + w <= v * w) by (replace (v' * w + w) with (S v' * w) by lia;
                                     apply Nat.mul_le_mono_r; lia).
    lia.
Qed.

Lemma grounded_lt :
  forall I w M u, Grounded I (seq 0 w) -> In M I -> In u M -> u < w.
Proof.
  intros I w M u HG HM Hu.
  pose proof (HG M HM u Hu) as H; apply in_seq in H; lia.
Qed.

Lemma in_assemble_iff :
  forall w T f x,
    In x (assemble w T f) <-> exists v u, In v T /\ In u (f v) /\ x = v * w + u.
Proof.
  intros w T f x; unfold assemble; rewrite in_concat_map; split.
  - intros [v [Hv Hx]]; apply in_place_iff in Hx as [u [Hu E]].
    exists v, u; repeat split; assumption.
  - intros [v [u [Hv [Hu E]]]]; exists v; split; [exact Hv|].
    apply in_place_iff; exists u; split; assumption.
Qed.

(** What a member of the substitution has in block [v], read as an inner
    set: the inner member placed there, if [v] is one of its blocks, and
    nothing otherwise. *)

Lemma in_trace_assemble :
  forall w I T f v u,
    Grounded I (seq 0 w) -> (forall x, In x T -> In (f x) I) ->
    In u (trace w v (assemble w T f)) <-> In v T /\ In u (f v).
Proof.
  intros w I T f v u HG Hf; rewrite in_trace_iff, in_assemble_iff; split.
  - intros [[v' [u' [Hv' [Hu' E]]]] Hu].
    pose proof (@grounded_lt _ _ _ _ HG (Hf v' Hv') Hu') as Hu'w.
    destruct (block_inj _ _ _ _ _ Hu Hu'w E) as [-> ->]; split; assumption.
  - intros [Hv Hu]; split.
    + exists v, u; repeat split; assumption.
    + exact (@grounded_lt _ _ _ _ HG (Hf v Hv) Hu).
Qed.

Lemma in_trace_inter :
  forall w v A B u,
    In u (trace w v (inter A B)) <-> In u (trace w v A) /\ In u (trace w v B).
Proof.
  intros w v A B u; rewrite !in_trace_iff, in_inter_iff; tauto.
Qed.

Lemma in_trace_SetEq :
  forall w v A B u, SetEq A B -> (In u (trace w v A) <-> In u (trace w v B)).
Proof.
  intros w v A B u [HAB HBA]; rewrite !in_trace_iff; split;
    intros [H1 H2]; split; auto.
Qed.

(** ** Members of the substitution *)

Lemma in_assemble_all_inv :
  forall w I T X,
    NoDup T -> In X (assemble_all w I T) ->
    exists f, (forall v, In v T -> In (f v) I) /\ X = assemble w T f.
Proof.
  intros w I T; induction T as [|v T IH]; intros X HT HX; simpl in HX.
  - destruct HX as [E | []]; subst X.
    exists (fun _ => []); split; [intros v [] | reflexivity].
  - inversion HT as [|? ? Hv HT']; subst.
    apply in_flat_map in HX as [M [HM HX]].
    apply in_map_iff in HX as [rest [E Hrest]]; subst X.
    destruct (IH rest HT' Hrest) as [f [Hf Er]]; subst rest.
    exists (fun x => if Nat.eq_dec x v then M else f x); split.
    + intros x [E | Hx].
      * subst x; destruct (Nat.eq_dec v v) as [_ | C]; [exact HM | congruence].
      * destruct (Nat.eq_dec x v) as [E | _]; [subst x; contradiction | apply Hf; exact Hx].
    + unfold assemble; simpl.
      destruct (Nat.eq_dec v v) as [_ | C]; [| congruence].
      f_equal; f_equal; apply map_ext_in; intros x Hx.
      destruct (Nat.eq_dec x v) as [E | _]; [subst x; contradiction | reflexivity].
Qed.

Lemma in_substitute_inv :
  forall a w O I X,
    Uniform a O -> In X (substitute w O I) ->
    exists T f, In T O /\ (forall v, In v T -> In (f v) I) /\ X = assemble w T f.
Proof.
  intros a w O I X HU HX; unfold substitute in HX.
  apply in_flat_map in HX as [T [HT HX]].
  assert (HTn : NoDup T) by (exact (proj2 (proj1 (Forall_forall _ _) HU T HT))).
  destruct (in_assemble_all_inv w I T X HTn HX) as [f [Hf E]].
  exists T, f; repeat split; assumption.
Qed.

(** ** The collapse lemma, which carries the repair

    Three members of a sunflower-free uniform family whose pairwise
    intersections agree are equal as sets. *)

(** Decidability of [SetEq] is [LowerBound.seteqb]. *)

Lemma seteqb_true : forall A B, seteqb A B = true -> SetEq A B.
Proof. intros A B H; apply seteqb_correct; exact H. Qed.

Lemma seteqb_false : forall A B, seteqb A B = false -> ~ SetEq A B.
Proof.
  intros A B H HS; apply seteqb_correct in HS; rewrite HS in H; discriminate.
Qed.

Lemma uniform_incl_SetEq :
  forall n A B, UniformSet n A -> UniformSet n B -> Subset A B -> SetEq A B.
Proof.
  intros n A B [HlA HnA] [HlB HnB] HAB; split; [exact HAB|].
  apply (NoDup_length_incl HnA); [lia | exact HAB].
Qed.

Lemma triple_collapse :
  forall n F X Y Z,
    UniformSet n X -> UniformSet n Y -> UniformSet n Z ->
    In X F -> In Y F -> In Z F ->
    ~ ContainsKSunflower 3 F ->
    (forall x, In x X /\ In x Y <-> In x X /\ In x Z) ->
    (forall x, In x X /\ In x Y <-> In x Y /\ In x Z) ->
    SetEq X Y /\ SetEq X Z.
Proof.
  intros n F X Y Z HX HY HZ HXF HYF HZF Hno H1 H2.
  destruct (seteqb X Y) eqn:EXY.
  - apply seteqb_true in EXY as HXY; split; [exact HXY|].
    apply (uniform_incl_SetEq _ _ _ HX HZ); intros x Hx.
    assert (Hxy : In x X /\ In x Y) by (split; [exact Hx | apply (proj1 HXY); exact Hx]).
    apply H1 in Hxy; tauto.
  - apply seteqb_false in EXY as NXY.
    destruct (seteqb X Z) eqn:EXZ.
    + apply seteqb_true in EXZ as HXZ; exfalso; apply NXY.
      apply (uniform_incl_SetEq _ _ _ HX HY); intros x Hx.
      assert (Hxz : In x X /\ In x Z) by (split; [exact Hx | apply (proj1 HXZ); exact Hx]).
      apply H1 in Hxz; tauto.
    + apply seteqb_false in EXZ as NXZ.
      destruct (seteqb Y Z) eqn:EYZ.
      * apply seteqb_true in EYZ as HYZ; exfalso; apply NXY; apply SetEq_sym.
        apply (uniform_incl_SetEq _ _ _ HY HX); intros y Hy.
        assert (Hyz : In y Y /\ In y Z) by (split; [exact Hy | apply (proj1 HYZ); exact Hy]).
        apply H2 in Hyz; tauto.
      * apply seteqb_false in EYZ as NYZ; exfalso; apply Hno.
        exists [X; Y; Z]; split.
        { intros A HA; exists A; split; [| apply SetEq_refl].
          destruct HA as [<- | [<- | [<- | []]]]; assumption. }
        split; [reflexivity|]; exists (inter X Y); split.
        { constructor.
          - intros B [<- | [<- | []]]; assumption.
          - constructor; [intros B [<- | []]; assumption|].
            constructor; [intros B [] | constructor]. }
        assert (E12 : SetEq (inter X Y) (inter X Y)) by apply SetEq_refl.
        assert (E13 : SetEq (inter X Z) (inter X Y))
          by (split; intros x Hx; apply in_inter_iff; apply in_inter_iff in Hx;
              apply H1; exact Hx).
        assert (E23 : SetEq (inter Y Z) (inter X Y))
          by (split; intros x Hx; apply in_inter_iff; apply in_inter_iff in Hx;
              apply H2; exact Hx).
        assert (Hsym : forall A B, SetEq (inter A B) (inter X Y) ->
                                   SetEq (inter B A) (inter X Y))
          by (intros A B H; eapply SetEq_trans; [apply inter_comm_SetEq | exact H]).
        intros A B HA HB Hne.
        destruct HA as [<- | [<- | [<- | []]]];
          destruct HB as [<- | [<- | [<- | []]]];
          first [ congruence | exact E12 | exact E13 | exact E23
                | apply Hsym; first [exact E12 | exact E13 | exact E23] ].
Qed.

Lemma assemble_SetEq :
  forall w T T' f f',
    SetEq T T' -> (forall v, In v T -> SetEq (f v) (f' v)) ->
    SetEq (assemble w T f) (assemble w T' f').
Proof.
  intros w T T' f f' [HT HT'] Hf; split; intros x Hx;
    apply in_assemble_iff in Hx as [v [u [Hv [Hu E]]]];
    apply in_assemble_iff; exists v, u.
  - repeat split; [apply HT; exact Hv | apply (proj1 (Hf v Hv)); exact Hu | exact E].
  - assert (HvT : In v T) by (apply HT'; exact Hv).
    repeat split; [exact HvT | apply (proj2 (Hf v HvT)); exact Hu | exact E].
Qed.

(** ** The theorem *)

Theorem substitute_no_sunflower :
  forall a b w O I,
    Uniform a O -> ~ ContainsKSunflower 3 O ->
    Uniform b I -> Intersecting I -> ~ ContainsKSunflower 3 I ->
    Grounded I (seq 0 w) ->
    ~ ContainsKSunflower 3 (substitute w O I).
Proof.
  intros a b w O I HUO HnoO HUI HII HnoI HG [S [HSF [Hlen [core [HSnd Hcore]]]]].
  destruct S as [|A1 [|A2 [|A3 [|A4 S]]]]; simpl in Hlen; try discriminate.
  clear Hlen.
  (* the three members, decomposed *)
  destruct (HSF A1 ltac:(simpl; tauto)) as [X1 [HX1 E1]].
  destruct (HSF A2 ltac:(simpl; tauto)) as [X2 [HX2 E2]].
  destruct (HSF A3 ltac:(simpl; tauto)) as [X3 [HX3 E3]].
  destruct (in_substitute_inv _ _ _ _ _ HUO HX1) as [T1 [f1 [HT1 [Hf1 ->]]]].
  destruct (in_substitute_inv _ _ _ _ _ HUO HX2) as [T2 [f2 [HT2 [Hf2 ->]]]].
  destruct (in_substitute_inv _ _ _ _ _ HUO HX3) as [T3 [f3 [HT3 [Hf3 ->]]]].
  (* the three members are pairwise distinct sets *)
  inversion HSnd as [|? ? Hd1 HSnd']; subst.
  inversion HSnd' as [|? ? Hd2 _]; subst.
  assert (N12 : ~ SetEq A1 A2) by (apply Hd1; simpl; tauto).
  assert (N13 : ~ SetEq A1 A3) by (apply Hd1; simpl; tauto).
  assert (N23 : ~ SetEq A2 A3) by (apply Hd2; simpl; tauto).
  assert (D12 : A1 <> A2) by (intro E; subst; apply N12; apply SetEq_refl).
  assert (D13 : A1 <> A3) by (intro E; subst; apply N13; apply SetEq_refl).
  assert (D23 : A2 <> A3) by (intro E; subst; apply N23; apply SetEq_refl).
  assert (C12 := Hcore A1 A2 ltac:(simpl; tauto) ltac:(simpl; tauto) D12).
  assert (C13 := Hcore A1 A3 ltac:(simpl; tauto) ltac:(simpl; tauto) D13).
  assert (C23 := Hcore A2 A3 ltac:(simpl; tauto) ltac:(simpl; tauto) D23).
  (* block contents of the pairwise intersections *)
  assert (Blk : forall Ai Aj Ti Tj fi fj v u,
             SetEq Ai (assemble w Ti fi) -> SetEq Aj (assemble w Tj fj) ->
             (forall x, In x Ti -> In (fi x) I) -> (forall x, In x Tj -> In (fj x) I) ->
             (In u (trace w v (inter Ai Aj)) <->
              (In v Ti /\ In u (fi v)) /\ (In v Tj /\ In u (fj v)))).
  { intros Ai Aj Ti Tj fi fj v u Ei Ej Hfi Hfj.
    rewrite in_trace_inter, (in_trace_SetEq w v _ _ u Ei), (in_trace_SetEq w v _ _ u Ej),
      (in_trace_assemble _ _ _ _ v u HG Hfi), (in_trace_assemble _ _ _ _ v u HG Hfj).
    tauto. }
  assert (Same : forall P Q v u, SetEq P core -> SetEq Q core ->
             In u (trace w v P) <-> In u (trace w v Q)).
  { intros P Q v u HP HQ.
    rewrite (in_trace_SetEq w v _ _ u HP), (in_trace_SetEq w v _ _ u HQ); tauto. }
  (* occupied blocks: v is in Ti and Tj exactly when block v of the
     intersection is nonempty, because the inner family is intersecting *)
  assert (Occ : forall Ai Aj Ti Tj fi fj v,
             SetEq Ai (assemble w Ti fi) -> SetEq Aj (assemble w Tj fj) ->
             (forall x, In x Ti -> In (fi x) I) -> (forall x, In x Tj -> In (fj x) I) ->
             (In v Ti /\ In v Tj <-> exists u, In u (trace w v (inter Ai Aj)))).
  { intros Ai Aj Ti Tj fi fj v Ei Ej Hfi Hfj; split.
    - intros [Hvi Hvj].
      assert (Hnd : ~ Disjoint (fi v) (fj v)) by (apply HII; [apply Hfi | apply Hfj]; assumption).
      destruct (Exists_dec (fun u => In u (fj v)) (fi v) (fun u => in_dec_nat u (fj v)))
        as [Hex | Hnex].
      + apply Exists_exists in Hex as [u [Hu Huj]].
        exists u; apply (Blk Ai Aj Ti Tj fi fj v u Ei Ej Hfi Hfj); tauto.
      + exfalso; apply Hnd; intros u Hu Huj; apply Hnex.
        apply Exists_exists; exists u; split; assumption.
    - intros [u Hu]; apply (Blk Ai Aj Ti Tj fi fj v u Ei Ej Hfi Hfj) in Hu; tauto. }
  (* the outer members collapse *)
  assert (HUT : forall T, In T O -> UniformSet a T)
    by (intros T HT; exact (proj1 (Forall_forall _ _) HUO T HT)).
  destruct (triple_collapse _ _ _ _ _ (HUT T1 HT1) (HUT T2 HT2) (HUT T3 HT3) HT1 HT2 HT3 HnoO)
    as [ET12 ET13].
  { intros v; rewrite (Occ A1 A2 T1 T2 f1 f2 v E1 E2 Hf1 Hf2),
                      (Occ A1 A3 T1 T3 f1 f3 v E1 E3 Hf1 Hf3).
    split; intros [u Hu]; exists u; [apply (Same _ _ v u C12 C13) | apply (Same _ _ v u C13 C12)];
      exact Hu. }
  { intros v; rewrite (Occ A1 A2 T1 T2 f1 f2 v E1 E2 Hf1 Hf2),
                      (Occ A2 A3 T2 T3 f2 f3 v E2 E3 Hf2 Hf3).
    split; intros [u Hu]; exists u; [apply (Same _ _ v u C12 C23) | apply (Same _ _ v u C23 C12)];
      exact Hu. }
  (* the inner members collapse in every block *)
  assert (HUM : forall M, In M I -> UniformSet b M)
    by (intros M HM; exact (proj1 (Forall_forall _ _) HUI M HM)).
  assert (Inner : forall v, In v T1 -> SetEq (f1 v) (f2 v) /\ SetEq (f1 v) (f3 v)).
  { intros v Hv1.
    assert (Hv2 : In v T2) by (apply (proj1 ET12); exact Hv1).
    assert (Hv3 : In v T3) by (apply (proj1 ET13); exact Hv1).
    pose proof (Hf1 v Hv1) as HM1; pose proof (Hf2 v Hv2) as HM2; pose proof (Hf3 v Hv3) as HM3.
    apply (triple_collapse _ _ _ _ _ (HUM _ HM1) (HUM _ HM2) (HUM _ HM3) HM1 HM2 HM3 HnoI).
    - intros u.
      pose proof (proj1 (Blk A1 A2 T1 T2 f1 f2 v u E1 E2 Hf1 Hf2)) as P12.
      pose proof (proj2 (Blk A1 A2 T1 T2 f1 f2 v u E1 E2 Hf1 Hf2)) as Q12.
      pose proof (proj1 (Blk A1 A3 T1 T3 f1 f3 v u E1 E3 Hf1 Hf3)) as P13.
      pose proof (proj2 (Blk A1 A3 T1 T3 f1 f3 v u E1 E3 Hf1 Hf3)) as Q13.
      pose proof (Same _ _ v u C12 C13) as S.
      split; intros [Ha Hb].
      + assert (H := P13 (proj1 S (Q12 (conj (conj Hv1 Ha) (conj Hv2 Hb))))); tauto.
      + assert (H := P12 (proj2 S (Q13 (conj (conj Hv1 Ha) (conj Hv3 Hb))))); tauto.
    - intros u.
      pose proof (proj1 (Blk A1 A2 T1 T2 f1 f2 v u E1 E2 Hf1 Hf2)) as P12.
      pose proof (proj2 (Blk A1 A2 T1 T2 f1 f2 v u E1 E2 Hf1 Hf2)) as Q12.
      pose proof (proj1 (Blk A2 A3 T2 T3 f2 f3 v u E2 E3 Hf2 Hf3)) as P23.
      pose proof (proj2 (Blk A2 A3 T2 T3 f2 f3 v u E2 E3 Hf2 Hf3)) as Q23.
      pose proof (Same _ _ v u C12 C23) as S.
      split; intros [Ha Hb].
      + assert (H := P23 (proj1 S (Q12 (conj (conj Hv1 Ha) (conj Hv2 Hb))))); tauto.
      + assert (H := P12 (proj2 S (Q23 (conj (conj Hv2 Ha) (conj Hv3 Hb))))); tauto. }
  (* so the first two members are the same set *)
  apply N12.
  eapply SetEq_trans; [exact E1|].
  eapply SetEq_trans; [| apply SetEq_sym; exact E2].
  apply assemble_SetEq; [exact ET12 | intros v Hv; exact (proj1 (Inner v Hv))].
Qed.

(** ** Size, uniformity and distinctness of the substitution

    These are the bookkeeping half of [LowerBound]: the family has
    [|O| * |I|^a] members, each of size [a * b], pairwise distinct as
    sets. *)

Lemma length_flat_map_const :
  forall (g : list nat -> list nat -> list nat) (L I : Family),
    length (flat_map (fun M => map (g M) L) I) = length I * length L.
Proof.
  intros g L I; induction I as [|M I IH]; simpl; [reflexivity|].
  rewrite app_length, map_length, IH; reflexivity.
Qed.

Lemma length_assemble_all :
  forall w I T, length (assemble_all w I T) = length I ^ length T.
Proof.
  intros w I T; induction T as [|v T IH]; simpl; [reflexivity|].
  rewrite (length_flat_map_const (fun M rest => place w v M ++ rest)), IH; reflexivity.
Qed.

Lemma length_substitute :
  forall a w O I, Uniform a O -> length (substitute w O I) = length O * length I ^ a.
Proof.
  intros a w O I HU; unfold substitute.
  induction O as [|T O IH]; simpl; [reflexivity|].
  inversion HU as [|? ? [HlT _] HU']; subst.
  rewrite app_length, length_assemble_all, (IH HU'); reflexivity.
Qed.

Lemma NoDup_place : forall w v M, NoDup M -> NoDup (place w v M).
Proof.
  intros w v M HM; unfold place; apply NoDup_map_inj; [intros x y _ _ E; lia | exact HM].
Qed.

Lemma UniformSet_assemble :
  forall b w T f,
    NoDup T ->
    (forall v, In v T -> UniformSet b (f v)) ->
    (forall v u, In v T -> In u (f v) -> u < w) ->
    UniformSet (length T * b) (assemble w T f).
Proof.
  intros b w T f; induction T as [|v T IH]; intros HT Hf Hw; [split; [reflexivity | constructor]|].
  inversion HT as [|? ? Hv HT']; subst.
  destruct (IH HT' (fun x Hx => Hf x (or_intror Hx)) (fun x u Hx => Hw x u (or_intror Hx)))
    as [Hlen Hnd].
  destruct (Hf v (or_introl eq_refl)) as [Hlv Hndv].
  unfold assemble in *; simpl; split.
  - rewrite app_length, Hlen; unfold place; rewrite map_length, Hlv; lia.
  - apply NoDup_app_disjoint; [apply NoDup_place; exact Hndv | exact Hnd |].
    intros x Hx Hy.
    apply in_place_iff in Hx as [u [Hu ->]].
    apply in_concat_map in Hy as [v' [Hv' Hy]].
    apply in_place_iff in Hy as [u' [Hu' E]].
    pose proof (Hw v u (or_introl eq_refl) Hu) as Hlt.
    pose proof (Hw v' u' (or_intror Hv') Hu') as Hlt'.
    destruct (block_inj _ _ _ _ _ Hlt Hlt' E) as [-> _]; contradiction.
Qed.

Lemma Uniform_substitute :
  forall a b w O I,
    Uniform a O -> Uniform b I -> Grounded I (seq 0 w) ->
    Uniform (a * b) (substitute w O I).
Proof.
  intros a b w O I HUO HUI HG; apply Forall_forall; intros X HX.
  destruct (in_substitute_inv _ _ _ _ _ HUO HX) as [T [f [HT [Hf ->]]]].
  destruct (proj1 (Forall_forall _ _) HUO T HT) as [HlT HnT].
  rewrite <- HlT; apply UniformSet_assemble; [exact HnT | |].
  - intros v Hv; exact (proj1 (Forall_forall _ _) HUI (f v) (Hf v Hv)).
  - intros v u Hv Hu; exact (@grounded_lt _ _ _ _ HG (Hf v Hv) Hu).
Qed.

(** Decoding: a member of the substitution determines its outer member
    and, block by block, its inner members, up to set equality. *)

Lemma assemble_SetEq_inv :
  forall w I T T' f f',
    Grounded I (seq 0 w) -> (forall M, In M I -> M <> []) ->
    (forall x, In x T -> In (f x) I) -> (forall x, In x T' -> In (f' x) I) ->
    SetEq (assemble w T f) (assemble w T' f') ->
    SetEq T T' /\ (forall v, In v T -> SetEq (f v) (f' v)).
Proof.
  intros w I T T' f f' HG Hne Hf Hf' HE.
  assert (Tr : forall v u, In v T /\ In u (f v) <-> In v T' /\ In u (f' v)).
  { intros v u.
    rewrite <- (in_trace_assemble w I T f v u HG Hf),
            <- (in_trace_assemble w I T' f' v u HG Hf').
    apply in_trace_SetEq; exact HE. }
  assert (Occ : forall v, In v T -> In v T').
  { intros v Hv; destruct (f v) as [|u M] eqn:Ef; [exfalso; apply (Hne (f v) (Hf v Hv)); exact Ef|].
    apply (proj1 (Tr v u)); rewrite Ef; split; [exact Hv | left; reflexivity]. }
  assert (Occ' : forall v, In v T' -> In v T).
  { intros v Hv; destruct (f' v) as [|u M] eqn:Ef; [exfalso; apply (Hne (f' v) (Hf' v Hv)); exact Ef|].
    apply (proj2 (Tr v u)); rewrite Ef; split; [exact Hv | left; reflexivity]. }
  split; [split; intros v Hv; [apply Occ | apply Occ']; exact Hv|].
  intros v Hv; split; intros u Hu.
  - apply (proj1 (Tr v u)); split; assumption.
  - apply (proj2 (Tr v u)); split; [apply Occ; exact Hv | exact Hu].
Qed.

Lemma substitute_SetEq_eq :
  forall a b w O I X Y,
    1 <= b -> Uniform a O -> Distinct O -> Uniform b I -> Distinct I ->
    Grounded I (seq 0 w) ->
    In X (substitute w O I) -> In Y (substitute w O I) -> SetEq X Y -> X = Y.
Proof.
  intros a b w O I X Y Hb HUO HDO HUI HDI HG HX HY HE.
  assert (Hne : forall M, In M I -> M <> []).
  { intros M HM E; subst M.
    destruct (proj1 (Forall_forall _ _) HUI [] HM) as [Hl _]; simpl in Hl; lia. }
  destruct (in_substitute_inv _ _ _ _ _ HUO HX) as [T [f [HT [Hf ->]]]].
  destruct (in_substitute_inv _ _ _ _ _ HUO HY) as [T' [f' [HT' [Hf' ->]]]].
  destruct (assemble_SetEq_inv w I T T' f f' HG Hne Hf Hf' HE) as [ET Ef].
  pose proof (SetNoDup_setEq_eq HDO HT HT' ET) as <-.
  unfold assemble; f_equal; apply map_ext_in; intros v Hv; f_equal.
  exact (SetNoDup_setEq_eq HDI (Hf v Hv) (Hf' v Hv) (Ef v Hv)).
Qed.

Lemma SetNoDup_of_NoDup :
  forall F, NoDup F -> (forall A B, In A F -> In B F -> SetEq A B -> A = B) -> SetNoDup F.
Proof.
  induction F as [|A F IH]; intros HN HE; [constructor|].
  inversion HN as [|? ? HA HN']; subst.
  constructor.
  - intros B HB HAB.
    assert (A = B) by (apply HE; [left; reflexivity | right; exact HB | exact HAB]).
    subst B; contradiction.
  - apply IH; [exact HN' |].
    intros X Y HX HY; apply HE; right; assumption.
Qed.

Lemma NoDup_flat_map_disj :
  forall (X : Type) (g : X -> Family) (L : list X),
    NoDup L -> (forall x, In x L -> NoDup (g x)) ->
    (forall x y A, In x L -> In y L -> In A (g x) -> In A (g y) -> x = y) ->
    NoDup (flat_map g L).
Proof.
  intros X g L; induction L as [|x L IH]; intros HN Hg Hd; simpl; [constructor|].
  inversion HN as [|? ? Hx HN']; subst.
  apply NoDup_app_disjoint.
  - apply Hg; left; reflexivity.
  - apply IH; [exact HN' | intros y Hy; apply Hg; right; exact Hy |].
    intros y z A Hy Hz HA HB; apply (Hd y z A); [right | right |..]; assumption.
  - intros A HA HB; apply in_flat_map in HB as [y [Hy HAy]].
    assert (x = y) by (apply (Hd x y A); [left; reflexivity | right; exact Hy | exact HA | exact HAy]).
    subst y; contradiction.
Qed.

Lemma NoDup_assemble_all :
  forall w I T,
    NoDup T -> SetNoDup I -> Grounded I (seq 0 w) ->
    NoDup (assemble_all w I T).
Proof.
  intros w I T; induction T as [|v T IH]; intros HT HDI HG; simpl;
    [constructor; [intros [] | constructor]|].
  inversion HT as [|? ? Hv HT']; subst.
  apply NoDup_flat_map_disj; [apply SetNoDup_NoDup; exact HDI | |].
  - intros M _; apply NoDup_map_inj; [| apply IH; assumption].
    intros r r' _ _ E; apply app_inv_head in E; exact E.
  - intros M M' A HM HM' HA HA'.
    apply in_map_iff in HA as [r [Er Hr]]; apply in_map_iff in HA' as [r' [Er' Hr']].
    destruct (in_assemble_all_inv w I T r HT' Hr) as [h [Hh ->]].
    destruct (in_assemble_all_inv w I T r' HT' Hr') as [h' [Hh' ->]].
    (* block v of A is M and also M' *)
    assert (Tv : forall N k u, In N I -> (forall x, In x T -> In (k x) I) ->
                   In u (trace w v (place w v N ++ assemble w T k)) <-> In u N).
    { intros N k u HN Hk.
      set (k' := fun x => if Nat.eq_dec x v then N else k x).
      assert (Ek : place w v N ++ assemble w T k = assemble w (v :: T) k').
      { unfold assemble, k'; simpl; destruct (Nat.eq_dec v v) as [_ | C]; [| congruence].
        f_equal; f_equal; apply map_ext_in; intros x Hx.
        destruct (Nat.eq_dec x v) as [E | _]; [subst x; contradiction | reflexivity]. }
      assert (Hk' : forall x, In x (v :: T) -> In (k' x) I).
      { intros x [<- | Hx]; unfold k'.
        - destruct (Nat.eq_dec v v) as [_ | C]; [exact HN | congruence].
        - destruct (Nat.eq_dec x v) as [E | _]; [subst x; contradiction | apply Hk; exact Hx]. }
      rewrite Ek, (in_trace_assemble w I (v :: T) k' v u HG Hk').
      unfold k'; destruct (Nat.eq_dec v v) as [_ | C]; [| congruence].
      split; [intros [_ H]; exact H | intros H; split; [left; reflexivity | exact H]]. }
    apply (SetNoDup_setEq_eq HDI HM HM').
    split; intros u Hu.
    + apply (Tv M' h' u HM' Hh'); rewrite Er'; rewrite <- Er.
      apply (Tv M h u HM Hh); exact Hu.
    + apply (Tv M h u HM Hh); rewrite Er; rewrite <- Er'.
      apply (Tv M' h' u HM' Hh'); exact Hu.
Qed.

Lemma Distinct_substitute :
  forall a b w O I,
    1 <= b -> Uniform a O -> Distinct O -> Uniform b I -> Distinct I ->
    Grounded I (seq 0 w) ->
    Distinct (substitute w O I).
Proof.
  intros a b w O I Hb HUO HDO HUI HDI HG.
  apply SetNoDup_of_NoDup.
  - unfold substitute; apply NoDup_flat_map_disj; [apply SetNoDup_NoDup; exact HDO | |].
    + intros T HT; apply NoDup_assemble_all; [| exact HDI | exact HG].
      exact (proj2 (proj1 (Forall_forall _ _) HUO T HT)).
    + intros T T' A HT HT' HA HA'.
      assert (HAs : In A (substitute w O I)) by (apply in_flat_map; exists T; split; assumption).
      assert (Hne : forall M, In M I -> M <> []).
      { intros M HM E; subst M.
        destruct (proj1 (Forall_forall _ _) HUI [] HM) as [Hl _]; simpl in Hl; lia. }
      destruct (in_assemble_all_inv w I T A (proj2 (proj1 (Forall_forall _ _) HUO T HT)) HA)
        as [f [Hf EA]].
      destruct (in_assemble_all_inv w I T' A (proj2 (proj1 (Forall_forall _ _) HUO T' HT')) HA')
        as [f' [Hf' EA']].
      assert (HE : SetEq (assemble w T f) (assemble w T' f'))
        by (rewrite <- EA, <- EA'; apply SetEq_refl).
      destruct (assemble_SetEq_inv w I T T' f f' HG Hne Hf Hf' HE) as [ET _].
      exact (SetNoDup_setEq_eq HDO HT HT' ET).
  - intros A B HA HB; exact (substitute_SetEq_eq a b w O I A B Hb HUO HDO HUI HDI HG HA HB).
Qed.

(** ** The lower bound *)

Theorem substitute_lower_bound :
  forall a b w O I,
    1 <= b ->
    Uniform a O -> Distinct O -> ~ ContainsKSunflower 3 O ->
    Uniform b I -> Distinct I -> Intersecting I -> ~ ContainsKSunflower 3 I ->
    Grounded I (seq 0 w) ->
    LowerBound (a * b) 3 (length O * length I ^ a).
Proof.
  intros a b w O I Hb HUO HDO HnoO HUI HDI HII HnoI HG.
  exists (substitute w O I); repeat split.
  - exact (Uniform_substitute a b w O I HUO HUI HG).
  - exact (Distinct_substitute a b w O I Hb HUO HDO HUI HDI HG).
  (* [rewrite; lia], not [exact]: the mutations [lowerbound-at-least] and
     [iotaatleast-at-least] turn this equation into [>=] (docs/testing.md §4). *)
  - rewrite (length_substitute a w O I HUO); lia.
  - exact (substitute_no_sunflower a b w O I HUO HnoO HUI HII HnoI HG).
Qed.

(** ** The instance [IotaRate] has been waiting for

    The outer family is any 20-member 3-uniform sunflower-free family
    ([Intersecting.lower_bound_3_3_20], the doubled [iota3]); the inner
    family is [iota3] itself, intersecting, on the six points [0..5].
    [20 * 10^3 = 20000 = 3^9 + 317]. *)

Theorem lower_bound_9_3_20000 : LowerBound 9 3 (3 ^ 9 + 317).
Proof.
  (* The outer family is named, [double iota3], rather than taken from
     [lower_bound_3_3_20]: under the mutation [lowerbound-at-least] that
     lemma only says "at least 20", and the count would not go through. *)
  replace (3 ^ 9 + 317) with (length (double iota3) * length iota3 ^ 3)
    by (vm_compute; reflexivity).
  exact (substitute_lower_bound 3 3 6 (double iota3) iota3 ltac:(lia)
           (double_Uniform 3 iota3 iota3_uniform)
           (double_Distinct 3 iota3 ltac:(lia) iota3_uniform iota3_distinct)
           (double_no_sunflower 3 iota3 ltac:(lia) iota3_uniform iota3_distinct
              iota3_intersecting iota3_no_sunflower)
           iota3_uniform iota3_distinct iota3_intersecting iota3_no_sunflower
           iota3_grounded).
Qed.

(** [IotaRate]'s two conditional corollaries, now unconditional: the flat
    spread threshold [r = 3] fails at uniformity 9, and any constant
    witnessing [Conjecture.spread_conjecture] has [c 3 >= 4]. *)

Corollary flat_threshold_fails_at_nine : ~ SpreadYieldsDisjoint 9 3 3.
Proof.
  exact (substitution_would_refute_the_flat_threshold_at_nine lower_bound_9_3_20000).
Qed.

Corollary spread_constant_at_three_is_at_least_four :
  forall c : nat -> nat,
    (forall k, 2 <= k -> 1 <= c k) ->
    (forall n k, 1 <= n -> 2 <= k -> SpreadYieldsDisjoint n k (c k)) ->
    4 <= c 3.
Proof.
  exact (substitution_would_force_c_three_at_least_four lower_bound_9_3_20000).
Qed.

(** ** [AHS72] Lemma 6 as printed: [psi(ab) >= psi(a) * psi(b)^a]

    If the outer family is intersecting too, so is the substitution: two
    members share an outer block, and there the two inner members meet.
    With [triple_collapse] this is the whole of Lemma 6, both halves. *)

Lemma Intersecting_substitute :
  forall a w O I,
    Uniform a O -> Intersecting O -> Intersecting I -> Grounded I (seq 0 w) ->
    Intersecting (substitute w O I).
Proof.
  intros a w O I HUO HIO HII HG X Y HX HY HD.
  destruct (in_substitute_inv _ _ _ _ _ HUO HX) as [T [f [HT [Hf ->]]]].
  destruct (in_substitute_inv _ _ _ _ _ HUO HY) as [T' [f' [HT' [Hf' ->]]]].
  apply (HIO T T' HT HT'); intros v Hv Hv'.
  apply (HII (f v) (f' v) (Hf v Hv) (Hf' v Hv')); intros u Hu Hu'.
  apply (HD (v * w + u)); apply in_assemble_iff; exists v, u; repeat split; assumption.
Qed.

Theorem substitute_iota_lower_bound :
  forall a b w O I,
    1 <= b ->
    Uniform a O -> Distinct O -> Intersecting O -> ~ ContainsKSunflower 3 O ->
    Uniform b I -> Distinct I -> Intersecting I -> ~ ContainsKSunflower 3 I ->
    Grounded I (seq 0 w) ->
    IotaAtLeast (a * b) (length O * length I ^ a).
Proof.
  intros a b w O I Hb HUO HDO HIO HnoO HUI HDI HII HnoI HG.
  exists (substitute w O I); repeat split.
  - exact (Uniform_substitute a b w O I HUO HUI HG).
  - exact (Distinct_substitute a b w O I Hb HUO HDO HUI HDI HG).
  - exact (Intersecting_substitute a w O I HUO HIO HII HG).
  (* [rewrite; lia], not [exact]: the mutations [lowerbound-at-least] and
     [iotaatleast-at-least] turn this equation into [>=] (docs/testing.md §4). *)
  - rewrite (length_substitute a w O I HUO); lia.
  - exact (substitute_no_sunflower a b w O I HUO HnoO HUI HII HnoI HG).
Qed.

(** [psi(9) >= psi(3)^4 = 10000], [AHS72]'s [a = b = 3] instance: the
    [b = 9] rung of the tower, one short of the [10001] that
    [Sharp.iota_nine_at_least_10001_refutes] would need. *)

Theorem iota_nine_at_least_10000 : IotaAtLeast 9 (10 * 10 ^ 3).
Proof.
  exact (substitute_iota_lower_bound 3 3 6 iota3 iota3 ltac:(lia)
           iota3_uniform iota3_distinct iota3_intersecting iota3_no_sunflower
           iota3_uniform iota3_distinct iota3_intersecting iota3_no_sunflower
           iota3_grounded).
Qed.
