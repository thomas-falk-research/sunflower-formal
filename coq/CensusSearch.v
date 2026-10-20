(** * A census from a search: the generic search of [CensusGen] specialised
      to intersecting 3-sunflower-free families

    [census_of_search]: if every node the search keeps at levels
    [lo .. hi] is covered by a class of [L], and no node is kept at level
    [hi + 1], then every intersecting 3-sunflower-free [b]-uniform family
    of at least [lo] distinct members is covered by a class of [L]
    ([CensusB b L lo]; [CensusB 4] is [Link23.CensusL]).  The oracle is
    arbitrary; the test [validb] only has to accept every valid node.
    [iota_of_search] is the case [L = []].  See
    docs/census_certification.md, stage 2. *)

From Coq Require Import List Arith NArith Lia Bool.
Import ListNotations.
From Sunflower Require Import Sets Sunflower Intersecting DirectSum Stability4 Product IotaRate LinkLP Link23.
From Sunflower Require CensusGen.

(** ** The property and the census statement *)

Definition PB (b : nat) (F : Family) : Prop :=
  Uniform b F /\ Distinct F /\ Intersecting F /\ ~ ContainsKSunflower 3 F.

Definition CensusB (b : nat) (L : list Family) (lo : nat) : Prop :=
  forall D : Family,
    Uniform b D -> Distinct D -> Intersecting D -> ~ ContainsKSunflower 3 D ->
    lo <= length D -> exists Dk, In Dk L /\ Covered D Dk.

Lemma CensusB_4 : forall L lo, CensusB 4 L lo <-> CensusL L lo.
Proof. intros L lo; split; intros H; exact H. Qed.

(** ** Relabelling facts *)

Lemma SubFamilySetEq_trans' : forall S F G, SubFamilySetEq S F -> SubFamilySetEq F G -> SubFamilySetEq S G.
Proof.
  intros S F G H1 H2 A HA. destruct (H1 A HA) as [B [HB E1]]. destruct (H2 B HB) as [C [HC E2]].
  exists C; split; [exact HC | eapply SetEq_trans; [exact E1 | exact E2]].
Qed.

Lemma SubFamilySetEq_map : forall (g : nat -> nat) A B, SubFamilySetEq A B -> SubFamilySetEq (rmapF g A) (rmapF g B).
Proof.
  intros g A B H X HX. unfold rmapF in HX. apply in_map_iff in HX as [X0 [<- HX0]].
  destruct (H X0 HX0) as [Y0 [HY0 [E1 E2]]]. exists (rmap g Y0); split; [apply in_map, HY0 |].
  split; intros x Hx; unfold rmap in *; apply in_map_iff in Hx as [y [<- Hy]]; apply in_map; [apply E1 | apply E2]; exact Hy.
Qed.

Lemma rmapF_comp : forall (g1 g2 : nat -> nat) F, rmapF g1 (rmapF g2 F) = rmapF (fun x => g1 (g2 x)) F.
Proof. intros g1 g2 F. unfold rmapF, rmap. rewrite map_map. apply map_ext. intros A. apply map_map. Qed.

Lemma Covered_trans : forall A B C, Covered A B -> Covered B C -> Covered A C.
Proof.
  intros A B C [g1 [h1 [E1 [E1' [S1 S1']]]]] [g2 [h2 [E2 [E2' [S2 S2']]]]].
  exists (fun x => g1 (g2 x)), (fun x => h2 (h1 x)). split; [intros x; rewrite E1, E2; reflexivity |].
  split; [intros x; rewrite E2', E1'; reflexivity |]. rewrite <- rmapF_comp. split.
  - apply (SubFamilySetEq_trans' _ _ _ S1). apply SubFamilySetEq_map, S2.
  - apply (SubFamilySetEq_trans' _ (rmapF g1 B)); [apply SubFamilySetEq_map, S2' | exact S1'].
Qed.

(** ** Masks and sets *)

Lemma rmapF_eq : forall g F, CensusGen.relab g F = rmapF g F.
Proof. reflexivity. Qed.

Lemma SetEq_mask : forall a b, SetEq a b <-> CensusGen.rowmask a = CensusGen.rowmask b.
Proof.
  intros a b. rewrite CensusGen.mask_ext. split.
  - intros [H1 H2] x; split; [apply H1 | apply H2].
  - intros H; split; intros x Hx; apply H, Hx.
Qed.

Lemma NoDup_mask_of_Distinct : forall D, Distinct D -> NoDup (map CensusGen.rowmask D).
Proof.
  intros D H. induction H as [| A F Hni Hsnd IH]; simpl; constructor; [| exact IH].
  intros Hin. apply in_map_iff in Hin as [B [E HB]]. apply (Hni B HB). apply SetEq_mask. symmetry; exact E.
Qed.

Lemma Distinct_of_NoDup_mask : forall F, NoDup (map CensusGen.rowmask F) -> Distinct F.
Proof.
  induction F as [| A F IH]; intros H; simpl in H; constructor.
  - inversion H as [| ? ? HA _]; subst. intros B HB E. apply HA. apply in_map_iff. exists B; split; [| exact HB].
    symmetry; apply SetEq_mask, E.
  - inversion H; subst. apply IH; assumption.
Qed.

Lemma bits_seteq : forall s, SetEq (CensusGen.bits (CensusGen.rowmask s)) s.
Proof. intros s. split; intros x Hx; apply CensusGen.bits_mask_seteq; [exact Hx | exact Hx]. Qed.

(** ** Every valid family has a minimal node *)

Lemma length_seteq_NoDup : forall a b, NoDup a -> NoDup b -> SetEq a b -> length a = length b.
Proof.
  intros a b Ha Hb [H1 H2]. apply Nat.le_antisymm; apply NoDup_incl_length; assumption.
Qed.

Lemma node_of_family : forall b D, PB b D ->
  exists K, CensusGen.ssorted K /\ (forall m, In m K -> length (CensusGen.bits m) = b) /\
            PB b (CensusGen.fam K) /\ CensusGen.MinK K /\ length K = length D /\ Covered D (CensusGen.fam K).
Proof.
  intros b D [HU [HD [HI Hno]]].
  pose proof (NoDup_mask_of_Distinct D HD) as HndD.
  destruct (CensusGen.minimal_relabel D HndD) as [p [Hp [_ Hmin]]].
  set (g := CensusGen.pf p). set (h := CensusGen.pinv p).
  assert (Hhg : forall x, h (g x) = x) by (intros x; apply CensusGen.pinv_pf, Hp).
  assert (Hgh : forall x, g (h x) = x) by (intros x; apply CensusGen.pf_pinv, Hp).
  set (K := CensusGen.key (CensusGen.relab g D)).
  assert (HndA : NoDup (map CensusGen.rowmask (CensusGen.relab g D))).
  { unfold CensusGen.relab; rewrite map_map. apply (CensusGen.NoDup_map_transfer _ _ CensusGen.rowmask _ D HndD).
    intros u w _ _ E. apply (CensusGen.mask_map_inj g h Hhg), E. }
  assert (HK : CensusGen.ssorted K) by (apply CensusGen.sortN_ssorted, HndA).
  (* rows of the node and rows of the relabelled family correspond *)
  assert (Hrow : forall m, In m K -> exists s, In s D /\ m = CensusGen.rowmask (map g s)).
  { intros m Hm. apply CensusGen.in_key in Hm as [s' [Hs' E]]. unfold CensusGen.relab in Hs'.
    apply in_map_iff in Hs' as [s [<- Hs]]. exists s; split; [exact Hs | exact E]. }
  assert (Hrow' : forall s, In s D -> In (CensusGen.rowmask (map g s)) K).
  { intros s Hs. apply CensusGen.in_key. exists (map g s); split; [unfold CensusGen.relab; apply in_map, Hs | reflexivity]. }
  assert (Hcov : Covered D (CensusGen.fam K)).
  { exists h, g. split; [exact Hgh | split; [exact Hhg |]]. split.
    - intros s Hs. exists (rmap h (CensusGen.bits (CensusGen.rowmask (map g s)))). split.
      + unfold rmapF, CensusGen.fam. apply in_map, in_map, Hrow', Hs.
      + split; intros x Hx; unfold rmap in *.
        * apply in_map_iff. exists (g x); split; [apply Hhg |]. apply CensusGen.bits_mask_seteq, in_map, Hx.
        * apply in_map_iff in Hx as [y [<- Hy]]. apply CensusGen.bits_mask_seteq, in_map_iff in Hy as [z [<- Hz]].
          rewrite Hhg; exact Hz.
    - intros X HX. unfold rmapF, CensusGen.fam in HX. rewrite map_map in HX.
      apply in_map_iff in HX as [m [<- Hm]]. destruct (Hrow m Hm) as [s [Hs ->]].
      exists s; split; [exact Hs |]. split; intros x Hx; unfold rmap in *.
      + apply in_map_iff in Hx as [y [<- Hy]]. apply CensusGen.bits_mask_seteq, in_map_iff in Hy as [z [<- Hz]].
        rewrite Hhg; exact Hz.
      + apply in_map_iff. exists (g x); split; [apply Hhg |]. apply CensusGen.bits_mask_seteq, in_map, Hx. }
  assert (Hlen : forall m, In m K -> length (CensusGen.bits m) = b).
  { intros m Hm. destruct (Hrow m Hm) as [s [Hs ->]]. pose proof HU as HU'. unfold Uniform in HU'. rewrite Forall_forall in HU'.
    destruct (HU' s Hs) as [Hl Hnd].
    rewrite (length_seteq_NoDup _ (map g s) (CensusGen.bits_NoDup _)).
    - rewrite map_length; exact Hl.
    - apply FinFun.Injective_map_NoDup; [intros x y E; rewrite <- (Hhg x), E, Hhg; reflexivity | exact Hnd].
    - apply bits_seteq. }
  exists K. split; [exact HK | split; [exact Hlen | split; [| split; [exact Hmin | split; [| exact Hcov]]]]].
  - destruct Hcov as [g' [h' [E1 [E2 [S1 S2]]]]]. split; [| split; [| split]].
    + unfold Uniform. apply Forall_forall. intros r Hr. unfold CensusGen.fam in Hr. apply in_map_iff in Hr as [m [<- Hm]].
      split; [apply Hlen, Hm | apply CensusGen.bits_NoDup].
    + apply Distinct_of_NoDup_mask. rewrite CensusGen.map_mask_fam. apply CensusGen.ssorted_NoDup, HK.
    + intros A B HA HB Hdis.
      assert (HA' : In (rmap h A) (rmapF h (CensusGen.fam K))) by (apply in_map, HA).
      assert (HB' : In (rmap h B) (rmapF h (CensusGen.fam K))) by (apply in_map, HB).
      (* the rows of [fam K] relabelled by [h] are rows of [D] up to set equality *)
      assert (Hs : forall X, In X (CensusGen.fam K) -> exists s, In s D /\ SetEq (rmap h X) s).
      { intros X HX. unfold CensusGen.fam in HX. apply in_map_iff in HX as [m [<- Hm]].
        destruct (Hrow m Hm) as [s [Hs ->]]. exists s; split; [exact Hs |].
        split; intros x Hx; unfold rmap in *.
        - apply in_map_iff in Hx as [y [<- Hy]]. apply CensusGen.bits_mask_seteq, in_map_iff in Hy as [z [<- Hz]].
          rewrite Hhg; exact Hz.
        - apply in_map_iff. exists (g x); split; [apply Hhg |]. apply CensusGen.bits_mask_seteq, in_map, Hx. }
      destruct (Hs A HA) as [sA [HsA EA]]. destruct (Hs B HB) as [sB [HsB EB]].
      apply (HI sA sB HsA HsB). intros x HxA HxB.
      apply (Hdis (g x)).
      * apply EA in HxA. unfold rmap in HxA. apply in_map_iff in HxA as [y [Ey Hy]]. rewrite <- Ey, Hgh; exact Hy.
      * apply EB in HxB. unfold rmap in HxB. apply in_map_iff in HxB as [y [Ey Hy]]. rewrite <- Ey, Hgh; exact Hy.
    + intros Hc. apply Hno. apply (ContainsKSunflower_rmapF h g Hgh Hhg) in Hc.
      apply (ContainsKSunflower_SubFamilySetEq Hc). intros X HX.
      unfold rmapF in HX. apply in_map_iff in HX as [Y [<- HY]]. unfold CensusGen.fam in HY.
      apply in_map_iff in HY as [m [<- Hm]]. destruct (Hrow m Hm) as [s [Hs ->]].
      exists s; split; [exact Hs |]. split; intros x Hx; unfold rmap in *.
      * apply in_map_iff in Hx as [y [<- Hy]]. apply CensusGen.bits_mask_seteq, in_map_iff in Hy as [z [<- Hz]].
        rewrite Hhg; exact Hz.
      * apply in_map_iff. exists (g x); split; [apply Hhg |]. apply CensusGen.bits_mask_seteq, in_map, Hx.
  - unfold K, CensusGen.key, CensusGen.relab. rewrite CensusGen.length_sortN, !map_length. reflexivity.
Qed.

(** ** The property is kept under removing the last row *)

Lemma PB_incl : forall b F G, PB b F -> NoDup G -> incl G F -> PB b G.
Proof.
  intros b F G [HU [HD [HI Hno]]] Hnd Hinc. split; [| split; [| split]].
  - unfold Uniform in *. rewrite Forall_forall in *. intros A HA; apply HU, Hinc, HA.
  - eapply SetNoDup_incl; eassumption.
  - eapply Intersecting_incl; eassumption.
  - intros Hc. apply Hno. apply (ContainsKSunflower_SubFamilySetEq Hc). apply SubFamilySetEq_incl, Hinc.
Qed.

Lemma PB_hered : forall b K y, PB b (CensusGen.fam (K ++ [y])) -> PB b (CensusGen.fam K).
Proof.
  intros b K y H. rewrite CensusGen.fam_app1 in H. apply (PB_incl b _ _ H).
  - destruct H as [_ [HD _]]. apply SetNoDup_NoDup in HD. apply NoDup_app_remove_r in HD. exact HD.
  - intros A HA. apply in_app_iff; left; exact HA.
Qed.

(** ** The census from a search *)

Theorem census_of_search : forall b validb oracle (L : list Family) lo hi,
  (forall K, PB b (CensusGen.fam K) -> validb K = true) ->
  (forall K, In K (CensusGen.level b validb oracle (S hi)) -> CensusGen.keep oracle K = false) ->
  (forall n K, lo <= n -> n <= hi -> In K (CensusGen.level b validb oracle n) ->
     CensusGen.keep oracle K = true -> exists Dk, In Dk L /\ Covered (CensusGen.fam K) Dk) ->
  CensusB b L lo.
Proof.
  intros b validb oracle L lo hi Hv Hend Hcov D HU HD HI Hno Hlo.
  assert (HP : PB b D) by (split; [exact HU | split; [exact HD | split; assumption]]).
  assert (Hsmall : length D <= hi).
  { destruct (le_lt_dec (length D) hi) as [H | H]; [exact H | exfalso].
    set (D' := firstn (S hi) D).
    assert (Hinc : incl D' D).
    { intros A HA. rewrite <- (firstn_skipn (S hi) D). apply in_app_iff; left; exact HA. }
    assert (Hnd : NoDup D').
    { apply SetNoDup_NoDup in HD. rewrite <- (firstn_skipn (S hi) D) in HD. apply NoDup_app_remove_r in HD. exact HD. }
    assert (HP' : PB b D') by (apply (PB_incl b D D' HP Hnd Hinc)).
    assert (Hl' : length D' = S hi) by (unfold D'; apply firstn_length_le; lia).
    destruct (node_of_family b D' HP') as [K [HK [Hb [HPK [Hmin [Hlen _]]]]]].
    destruct (CensusGen.level_complete b (PB b) validb Hv (PB_hered b) oracle K HK Hb HPK Hmin) as [Hin Hkeep].
    rewrite Hlen, Hl' in Hin. rewrite (Hend K Hin) in Hkeep. discriminate. }
  destruct (node_of_family b D HP) as [K [HK [Hb [HPK [Hmin [Hlen Hc]]]]]].
  destruct (CensusGen.level_complete b (PB b) validb Hv (PB_hered b) oracle K HK Hb HPK Hmin) as [Hin Hkeep].
  rewrite Hlen in Hin.
  destruct (Hcov (length D) K Hlo Hsmall Hin Hkeep) as [Dk [HDk HcK]].
  exists Dk; split; [exact HDk | apply (Covered_trans _ _ _ Hc HcK)].
Qed.

(** No family of [N + 1] members: the census with no classes. *)
Corollary iota_of_search : forall b validb oracle N,
  (forall K, PB b (CensusGen.fam K) -> validb K = true) ->
  (forall K, In K (CensusGen.level b validb oracle (S N)) -> CensusGen.keep oracle K = false) ->
  IotaAtMost b N.
Proof.
  intros b validb oracle N Hv Hend H HU HD HI Hno.
  destruct (le_lt_dec (length H) N) as [Hl | Hl]; [exact Hl | exfalso].
  destruct (census_of_search b validb oracle [] (S N) N Hv Hend
              ltac:(intros n K Hn1 Hn2; lia) H HU HD HI Hno Hl) as [Dk [[] _]].
Qed.

(** ** A concrete node test, and its completeness

    [validb b] looks at the newest row [y] of a node: it has [b] points,
    it meets every earlier row, and no two earlier rows [z ≠ w] form a
    sunflower with it (equal pairwise intersections, read off the masks
    by [N.land]).  [validb_complete]: every node whose family is valid
    passes. *)

Definition validb (b : nat) (K : list N) : bool :=
  match rev K with
  | [] => true
  | y :: rK =>
      let K' := rev rK in
      Nat.eqb (length (CensusGen.bits y)) b
      && forallb (fun z => negb (N.eqb (N.land z y) 0)) K'
      && forallb (fun z => forallb (fun w =>
            negb (negb (N.eqb z w) && N.eqb (N.land z w) (N.land z y) && N.eqb (N.land z y) (N.land w y))) K') K'
  end.

Lemma in_bits_land : forall u v x, In x (CensusGen.bits (N.land u v)) <-> In x (CensusGen.bits u) /\ In x (CensusGen.bits v).
Proof.
  intros u v x. rewrite !CensusGen.in_bits, N.land_spec. apply andb_true_iff.
Qed.

Lemma inter_bits : forall u v, SetEq (inter (CensusGen.bits u) (CensusGen.bits v)) (CensusGen.bits (N.land u v)).
Proof.
  intros u v. split; intros x Hx.
  - unfold inter in Hx. apply filter_In in Hx as [Hu Hv]. destruct (in_dec_nat x (CensusGen.bits v)) as [Hv' | _]; [| discriminate].
    apply in_bits_land; split; assumption.
  - apply in_bits_land in Hx as [Hu Hv]. unfold inter. apply filter_In; split; [exact Hu |].
    destruct (in_dec_nat x (CensusGen.bits v)) as [_ | Hn]; [reflexivity | contradiction].
Qed.

Lemma bits_mask_eq : forall u v, SetEq (CensusGen.bits u) (CensusGen.bits v) -> u = v.
Proof.
  intros u v H. rewrite <- (CensusGen.mask_bits u), <- (CensusGen.mask_bits v). apply SetEq_mask, H.
Qed.

Lemma SetNoDup_last : forall A B, SetNoDup (A ++ [B]) -> forall X, In X A -> ~ SetEq X B.
Proof.
  induction A as [| C A IH]; intros B H X HX; [destruct HX |].
  inversion H as [| ? ? Hni Hs]; subst. destruct HX as [<- | HX].
  - apply Hni, in_app_iff; right; left; reflexivity.
  - apply (IH B Hs X HX).
Qed.

Lemma validb_complete : forall b K, PB b (CensusGen.fam K) -> validb b K = true.
Proof.
  intros b K HP. unfold validb. destruct (rev K) as [| y rK] eqn:E; [reflexivity |].
  assert (EK : K = rev rK ++ [y]) by (rewrite <- (rev_involutive K), E; reflexivity).
  set (K' := rev rK) in *. cbv zeta.
  rewrite EK, CensusGen.fam_app1 in HP. destruct HP as [HU [HD [HI Hno]]].
  set (F := CensusGen.fam K' ++ [CensusGen.bits y]) in *.
  assert (Hy : In (CensusGen.bits y) F) by (apply in_app_iff; right; left; reflexivity).
  assert (Hz : forall z, In z K' -> In (CensusGen.bits z) F) by (intros z Hz; apply in_app_iff; left; apply in_map, Hz).
  assert (Hdy : forall z, In z K' -> z <> y).
  { intros z Hzk Ezy. subst z. apply (SetNoDup_last _ _ HD (CensusGen.bits y)); [apply in_map, Hzk | apply SetEq_refl]. }
  apply andb_true_iff; split; [apply andb_true_iff; split |].
  - apply Nat.eqb_eq. unfold Uniform in HU. rewrite Forall_forall in HU. apply (HU _ Hy).
  - apply forallb_forall. intros z Hzk. apply negb_true_iff. destruct (N.eqb_spec (N.land z y) 0) as [E0 | _]; [exfalso | reflexivity].
    apply (HI _ _ (Hz z Hzk) Hy). intros x Hx1 Hx2.
    assert (Hx : In x (CensusGen.bits (N.land z y))) by (apply in_bits_land; split; assumption).
    rewrite E0 in Hx. unfold CensusGen.bits in Hx. simpl in Hx. exact Hx.
  - apply forallb_forall. intros z Hzk. apply forallb_forall. intros w Hwk. apply negb_true_iff.
    destruct (N.eqb_spec z w) as [_ | Hzw]; [reflexivity |]. simpl.
    destruct (N.eqb_spec (N.land z w) (N.land z y)) as [E1 | _]; [| reflexivity].
    destruct (N.eqb_spec (N.land z y) (N.land w y)) as [E2 | _]; [exfalso | reflexivity].
    apply Hno. set (A := CensusGen.bits z). set (B := CensusGen.bits w). set (C := CensusGen.bits y).
    set (core := CensusGen.bits (N.land z w)).
    assert (Hne : forall u v, u <> v -> ~ SetEq (CensusGen.bits u) (CensusGen.bits v)).
    { intros u v Huv Hs. apply Huv, bits_mask_eq, Hs. }
    assert (Hpair : forall u v, (u = z \/ u = w \/ u = y) -> (v = z \/ v = w \/ v = y) -> u <> v ->
              SetEq (inter (CensusGen.bits u) (CensusGen.bits v)) core).
    { intros u v Hu Hv Huv. eapply SetEq_trans; [apply inter_bits |]. unfold core.
      assert (Hl : N.land u v = N.land z w).
      { destruct Hu as [-> | [-> | ->]]; destruct Hv as [-> | [-> | ->]]; try (exfalso; apply Huv; reflexivity).
        - reflexivity.
        - symmetry; exact E1.
        - rewrite N.land_comm. reflexivity.
        - rewrite <- E2, <- E1. reflexivity.
        - rewrite N.land_comm, <- E1. reflexivity.
        - rewrite N.land_comm, <- E2, <- E1. reflexivity. }
      rewrite Hl. apply SetEq_refl. }
    exists [A; B; C]. split.
    + apply SubFamilySetEq_incl. intros X [<- | [<- | [<- | []]]]; [apply Hz, Hzk | apply Hz, Hwk | exact Hy].
    + split; [reflexivity |]. exists core. split.
      * constructor; [| constructor; [| constructor; [| constructor]]].
        -- intros X [<- | [<- | []]]; [apply Hne, Hzw | apply Hne, Hdy, Hzk].
        -- intros X [<- | []]. apply Hne, Hdy, Hwk.
        -- intros X [].
      * intros X Y HX HY HXY.
        destruct HX as [<- | [<- | [<- | []]]]; destruct HY as [<- | [<- | [<- | []]]];
          try (exfalso; apply HXY; reflexivity).
        all: apply Hpair; [auto | auto |];
             first [ exact Hzw | intro Euv; apply Hzw; symmetry; exact Euv
                   | exact (Hdy z Hzk) | intro Euv; apply (Hdy z Hzk); symmetry; exact Euv
                   | exact (Hdy w Hwk) | intro Euv; apply (Hdy w Hwk); symmetry; exact Euv ].
Qed.
