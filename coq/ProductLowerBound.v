(** * ProductLowerBound.v -- The exponential lower bound f(n,k) >= (k-1)^n + 1.

    The standard product-family construction (Erdős–Rado 1960):
    [n] disjoint blocks of [t = k-1] fresh values each (block [i]
    occupies [[i*t, (i+1)*t)]); the family consists of all [t^n]
    transversals picking exactly one value per block.  Members are
    strictly descending lists, hence canonical: set-equality
    collapses to literal equality.

    No [k]-sunflower exists, by induction on [n]: among [k] petals
    there are only [t = k-1] possible top-block values, so two
    distinct petals share their top value [x] (pigeonhole); [x] then
    lies in the sunflower core, hence in EVERY petal, and since each
    member holds exactly one top-block value, all petals begin with
    [x].  Stripping [x] projects the sunflower onto the
    [(n-1)]-block family with core [core minus x], contradicting the
    induction hypothesis.

    Together with [ErdosRado.v] the function is now bracketed

        (k-1)^n + 1  <=  f(n, k)  <=  (k-1)^n * n! + 1,

    replacing the weaker [f(n, k) >= k] of [LowerBound.v].  This
    closes the "not formalized here" item for the exponential lower
    bound in STATUS.md.

    Citation: P. Erdős, R. Rado, "Intersection theorems for systems
    of sets", J. London Math. Soc. 35 (1960), 85-90 (the lower-bound
    remark; the construction is folklore).

    Zero axioms, zero admits; [Print Assumptions
    lower_bound_exponential] reports "Closed under the global
    context". *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower LowerBound.
Import ListNotations.

(** ** Generic helpers *)

Lemma NoDup_app_intro :
  forall (X : Type) (l1 l2 : list X),
    NoDup l1 -> NoDup l2 ->
    (forall x, In x l1 -> ~ In x l2) ->
    NoDup (l1 ++ l2).
Proof.
  intros X l1 l2 H1 H2 Hdis;
    induction H1 as [|x l1 Hni H1 IH]; simpl; [exact H2|].
  constructor.
  - rewrite in_app_iff. intros [Hx | Hx]; [exact (Hni Hx)|].
    apply (Hdis x); [left; reflexivity | exact Hx].
  - apply IH. intros y Hy; apply Hdis; right; exact Hy.
Qed.

Lemma flat_map_length_const :
  forall (X Y : Type) (f : X -> list Y) (l : list X) (c : nat),
    (forall x, In x l -> length (f x) = c) ->
    length (flat_map f l) = length l * c.
Proof.
  intros X Y f l c H; induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite app_length. rewrite (H x (or_introl eq_refl)).
  rewrite IH; [lia | intros y Hy; apply H; right; exact Hy].
Qed.

Lemma NoDup_map_inj_on :
  forall (X Y : Type) (f : X -> Y) (l : list X),
    NoDup l ->
    (forall a b, In a l -> In b l -> f a = f b -> a = b) ->
    NoDup (map f l).
Proof.
  intros X Y f l Hnd Hinj; induction Hnd as [|a l Hni Hnd IH]; simpl;
    [constructor|].
  constructor.
  - intro Hin. apply in_map_iff in Hin as [b [E Hb]].
    assert (a = b)
      by (apply Hinj; [left; reflexivity | right; exact Hb | symmetry; exact E]).
    subst b; contradiction.
  - apply IH. intros a0 b0 Ha0 Hb0 E.
    apply Hinj; [right; exact Ha0 | right; exact Hb0 | exact E].
Qed.

Lemma NoDup_flat_map_disjoint :
  forall (X : Type) (f : nat -> list X) (l : list nat),
    NoDup l ->
    (forall x, In x l -> NoDup (f x)) ->
    (forall x y a, In x l -> In y l -> x <> y -> In a (f x) -> In a (f y) -> False) ->
    NoDup (flat_map f l).
Proof.
  intros X f l Hnd Hf Hdis;
    induction Hnd as [|x l Hni Hnd IH]; simpl; [constructor|].
  apply NoDup_app_intro.
  - apply Hf; left; reflexivity.
  - apply IH.
    + intros y Hy; apply Hf; right; exact Hy.
    + intros x0 y0 a0 Hx0 Hy0 Hne Hax Hay.
      exact (Hdis x0 y0 a0 (or_intror Hx0) (or_intror Hy0) Hne Hax Hay).
  - intros a Ha Hain.
    apply in_flat_map in Hain as [y [Hy Hay]].
    assert (Hne : x <> y) by (intro E; subst y; contradiction).
    exact (Hdis x y a (or_introl eq_refl) (or_intror Hy) Hne Ha Hay).
Qed.

Lemma not_NoDup_map :
  forall (f : list nat -> nat) (S : list (list nat)),
    NoDup S -> ~ NoDup (map f S) ->
    exists A B, In A S /\ In B S /\ A <> B /\ f A = f B.
Proof.
  intros f S Hnd; induction Hnd as [|A S Hni Hnd IH]; intros Hnot.
  - exfalso; apply Hnot; constructor.
  - destruct (in_dec Nat.eq_dec (f A) (map f S)) as [Hin | Hnotin].
    + apply in_map_iff in Hin as [B [E HB]].
      exists A, B. split; [left; reflexivity|].
      split; [right; exact HB|].
      split; [intro E'; subst B; contradiction | symmetry; exact E].
    + destruct IH as [A0 [B0 [H1 [H2 [H3 H4]]]]].
      { intro Hnd'. apply Hnot. simpl. constructor; assumption. }
      exists A0, B0.
      split; [right; exact H1|]. split; [right; exact H2|]. auto.
Qed.

Lemma map_into_small :
  forall (f : list nat -> nat) (S : list (list nat)) (vals : list nat),
    (forall A, In A S -> In (f A) vals) ->
    length vals < length S ->
    ~ NoDup (map f S).
Proof.
  intros f S vals Hin Hlen Hnd.
  assert (Hincl : incl (map f S) vals).
  { intros x Hx. apply in_map_iff in Hx as [A [E HA]].
    subst x. apply Hin; exact HA. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hle.
  rewrite map_length in Hle. lia.
Qed.

Lemma inter_SetEq_compat :
  forall A A' B B',
    SetEq A A' -> SetEq B B' -> SetEq (inter A B) (inter A' B').
Proof.
  intros A A' B B' [HA1 HA2] [HB1 HB2]; split; intros y Hy;
    apply in_inter_iff in Hy; destruct Hy as [H1 H2];
    apply in_inter_iff; split; auto.
Qed.

(** ** Canonicalising abstract sunflowers to literal subfamilies *)

Lemma SetNoDup_map_witness :
  forall (F S : Family),
    SetNoDup S -> SubFamilySetEq S F ->
    SetNoDup (map (witness F) S).
Proof.
  intros F S Hsnd Hsub;
    induction Hsnd as [|A S Hni Hsnd IH]; simpl; [constructor|].
  constructor.
  - intros B' HB' Hseq'.
    apply in_map_iff in HB' as [B [EB HB]].
    subst B'.
    assert (HAex : exists B0, In B0 F /\ SetEq A B0)
      by (apply Hsub; left; reflexivity).
    assert (HBex : exists B0, In B0 F /\ SetEq B B0)
      by (apply Hsub; right; exact HB).
    destruct (@witness_spec F A HAex) as [_ HseqA].
    destruct (@witness_spec F B HBex) as [_ HseqB].
    apply (Hni B HB).
    eapply SetEq_trans; [exact HseqA|].
    eapply SetEq_trans; [exact Hseq'|].
    apply SetEq_sym; exact HseqB.
  - apply IH. intros A0 HA0. apply Hsub. right. exact HA0.
Qed.

Lemma contains_sunflower_literal :
  forall k (F : Family),
    ContainsKSunflower k F ->
    exists S core, incl S F /\ NoDup S /\ length S = k /\ Sunflower S core.
Proof.
  intros k F [S0 [Hsub [Hlen [core [Hsnd Hcore]]]]].
  exists (map (witness F) S0), core.
  split; [apply map_witness_incl; exact Hsub|].
  split; [apply map_witness_NoDup; auto|].
  split; [rewrite map_length; exact Hlen|].
  split; [apply SetNoDup_map_witness; auto|].
  intros U V HU HV Hne.
  apply in_map_iff in HU as [A [EU HA]].
  apply in_map_iff in HV as [B [EV HB]].
  subst U V.
  assert (HAex : exists B0, In B0 F /\ SetEq A B0) by (apply Hsub; exact HA).
  assert (HBex : exists B0, In B0 F /\ SetEq B B0) by (apply Hsub; exact HB).
  destruct (@witness_spec F A HAex) as [_ HseqA].
  destruct (@witness_spec F B HBex) as [_ HseqB].
  assert (HABne : A <> B) by (intro E; subst B; apply Hne; reflexivity).
  pose proof (Hcore A B HA HB HABne) as Hc.
  eapply SetEq_trans; [|exact Hc].
  apply inter_SetEq_compat; apply SetEq_sym; assumption.
Qed.

(** ** The product family *)

Fixpoint prod_family (t n : nat) : Family :=
  match n with
  | 0 => [[]]
  | S n' => flat_map (fun j => map (cons (n' * t + j)) (prod_family t n'))
                     (seq 0 t)
  end.

Lemma in_prod_family_S :
  forall t n' A,
    In A (prod_family t (S n')) <->
    exists j B, j < t /\ In B (prod_family t n') /\ A = (n' * t + j) :: B.
Proof.
  intros t n' A; simpl. rewrite in_flat_map.
  split.
  - intros [j [Hj HA]]. apply in_seq in Hj.
    apply in_map_iff in HA as [B [E HB]].
    exists j, B. split; [lia | split; [exact HB | symmetry; exact E]].
  - intros [j [B [Hj [HB E]]]].
    exists j. split; [apply in_seq; lia|].
    apply in_map_iff. exists B. split; [symmetry; exact E | exact HB].
Qed.

Lemma prod_family_length :
  forall t n, length (prod_family t n) = t ^ n.
Proof.
  intros t n; induction n as [|n IH]; simpl; [reflexivity|].
  assert (Hfl : length
                  (flat_map (fun j => map (cons (n * t + j)) (prod_family t n))
                            (seq 0 t))
                = length (seq 0 t) * (t ^ n)).
  { apply flat_map_length_const. intros j Hj.
    rewrite map_length. exact IH. }
  rewrite Hfl, seq_length. reflexivity.
Qed.

Lemma prod_family_bounded :
  forall t n A y, In A (prod_family t n) -> In y A -> y < n * t.
Proof.
  intros t n; induction n as [|n IH]; intros A y HA Hy.
  - simpl in HA. destruct HA as [E | []]; subst A; inversion Hy.
  - apply in_prod_family_S in HA as [j [B [Hj [HB E]]]]; subst A.
    destruct Hy as [E | Hy].
    + subst y. nia.
    + specialize (IH B y HB Hy). nia.
Qed.

Lemma prod_family_len_nodup :
  forall t n A, In A (prod_family t n) -> length A = n /\ NoDup A.
Proof.
  intros t n; induction n as [|n IH]; intros A HA.
  - simpl in HA; destruct HA as [E | []]; subst A.
    split; [reflexivity | constructor].
  - apply in_prod_family_S in HA as [j [B [Hj [HB E]]]]; subst A.
    destruct (IH B HB) as [Hlen Hnd].
    split; [simpl; lia|].
    constructor; [|exact Hnd].
    intro Hin.
    pose proof (prod_family_bounded t n B (n * t + j) HB Hin). lia.
Qed.

(** Members are canonical: set-equality implies literal equality. *)

Lemma prod_family_seteq_eq :
  forall t n A B,
    In A (prod_family t n) -> In B (prod_family t n) -> SetEq A B -> A = B.
Proof.
  intros t n; induction n as [|n IH]; intros A B HA HB Hseq.
  - simpl in HA, HB.
    destruct HA as [EA | []]; destruct HB as [EB | []]; subst; reflexivity.
  - apply in_prod_family_S in HA as [j [A' [Hj [HA' EA]]]].
    apply in_prod_family_S in HB as [j' [B' [Hj' [HB' EB]]]].
    subst A B.
    assert (Hhd : n * t + j = n * t + j').
    { destruct Hseq as [H1 H2].
      assert (HinB : In (n * t + j) ((n * t + j') :: B'))
        by (apply H1; left; reflexivity).
      destruct HinB as [E | HinB]; [lia|].
      exfalso.
      pose proof (prod_family_bounded t n B' (n * t + j) HB' HinB). lia. }
    assert (Ej : j = j') by lia.
    subst j'.
    assert (Hseq' : SetEq A' B').
    { destruct Hseq as [H1 H2]. split; intros y Hy.
      - assert (HyB : In y ((n * t + j) :: B')) by (apply H1; right; exact Hy).
        destruct HyB as [E | HyB]; [|exact HyB].
        exfalso. rewrite <- E in Hy.
        pose proof (prod_family_bounded t n A' (n * t + j) HA' Hy). lia.
      - assert (HyA : In y ((n * t + j) :: A')) by (apply H2; right; exact Hy).
        destruct HyA as [E | HyA]; [|exact HyA].
        exfalso. rewrite <- E in Hy.
        pose proof (prod_family_bounded t n B' (n * t + j) HB' Hy). lia. }
    rewrite (IH A' B' HA' HB' Hseq'). reflexivity.
Qed.

Lemma prod_family_NoDup :
  forall t n, NoDup (prod_family t n).
Proof.
  intros t n; induction n as [|n IH]; simpl.
  - constructor; [intros [] | constructor].
  - apply NoDup_flat_map_disjoint.
    + apply seq_NoDup.
    + intros j Hj. apply NoDup_map_inj_on; [exact IH|].
      intros a b _ _ E. congruence.
    + intros j j' a Hj Hj' Hne Ha Ha'.
      apply in_map_iff in Ha as [A [EA HA]].
      apply in_map_iff in Ha' as [A' [EA' HA']].
      subst a. injection EA' as E1 E2.
      apply in_seq in Hj. apply in_seq in Hj'. lia.
Qed.

Lemma NoDup_canonical_SetNoDup :
  forall (F : Family),
    NoDup F ->
    (forall A B, In A F -> In B F -> SetEq A B -> A = B) ->
    SetNoDup F.
Proof.
  intros F Hnd Hcanon; induction Hnd as [|A F Hni Hnd IH]; [constructor|].
  constructor.
  - intros B HB Hseq.
    assert (E : A = B)
      by (apply Hcanon; [left; reflexivity | right; exact HB | exact Hseq]).
    subst B; contradiction.
  - apply IH. intros A0 B0 H1 H2; apply Hcanon; right; auto.
Qed.

Lemma prod_family_SetNoDup :
  forall t n, SetNoDup (prod_family t n).
Proof.
  intros t n; apply NoDup_canonical_SetNoDup; [apply prod_family_NoDup|].
  intros A B HA HB; apply (prod_family_seteq_eq t n); auto.
Qed.

Lemma prod_family_Uniform :
  forall t n, Uniform n (prod_family t n).
Proof.
  intros t n; apply Forall_forall; intros A HA.
  destruct (prod_family_len_nodup t n A HA) as [Hl Hn].
  exact (conj Hl Hn).
Qed.

(** ** The product family contains no k-sunflower *)

Lemma prod_family_no_literal_sunflower :
  forall t k, t < k -> 2 <= k ->
  forall n (S : list (list nat)) core,
    incl S (prod_family t n) -> NoDup S -> length S = k ->
    Sunflower S core -> False.
Proof.
  intros t k Htk Hk n; induction n as [|n IH];
    intros S core Hincl Hnd Hlen Hsun.
  - (* n = 0: the family has one member, but k >= 2 distinct petals. *)
    pose proof (NoDup_incl_length Hnd Hincl) as Hle.
    simpl in Hle. lia.
  - destruct Hsun as [Hsnd Hcore].
    assert (Hstruct : forall C, In C S ->
              exists jc C', jc < t /\ In C' (prod_family t n)
                            /\ C = (n * t + jc) :: C').
    { intros C HC. apply (proj1 (in_prod_family_S t n C)).
      apply Hincl. exact HC. }
    (* Pigeonhole on top-block values: k petals, t = k-1 values. *)
    assert (Hheads : forall A, In A S ->
              In (hd 0 A) (map (fun j => n * t + j) (seq 0 t))).
    { intros A HA.
      destruct (Hstruct A HA) as [j [B [Hj [HB EA]]]].
      rewrite EA. simpl.
      apply in_map_iff. exists j. split; [reflexivity | apply in_seq; lia]. }
    assert (Hpig : exists A B, In A S /\ In B S /\ A <> B /\ hd 0 A = hd 0 B).
    { apply (not_NoDup_map (hd 0) S Hnd).
      apply (map_into_small (hd 0) S (map (fun j => n * t + j) (seq 0 t))
               Hheads).
      rewrite map_length, seq_length. lia. }
    destruct Hpig as [A [B [HA [HB [HABne Hhd]]]]].
    destruct (Hstruct A HA) as [jA [A' [HjA [HA' EA]]]].
    destruct (Hstruct B HB) as [jB [B' [HjB [HB' EB]]]].
    rewrite EA, EB in Hhd. simpl in Hhd.
    set (x := n * t + jA).
    assert (HxA : In x A) by (rewrite EA; left; reflexivity).
    assert (HxB : In x B) by (rewrite EB; left; unfold x; lia).
    (* x lies in the core, hence in every petal. *)
    assert (Hxcore : In x core).
    { pose proof (Hcore A B HA HB HABne) as Hc.
      destruct Hc as [Hc1 _]. apply Hc1.
      apply in_inter_iff. split; assumption. }
    assert (Hxall : forall C, In C S -> In x C).
    { intros C HC.
      destruct (list_eq_dec Nat.eq_dec C A) as [E | NE]; [subst C; exact HxA|].
      assert (HACne : A <> C) by (intro E; apply NE; symmetry; exact E).
      pose proof (Hcore A C HA HC HACne) as Hc.
      destruct Hc as [_ Hc2].
      pose proof (Hc2 x Hxcore) as Hx.
      apply in_inter_iff in Hx. tauto. }
    assert (Hxbig : n * t <= x) by (unfold x; lia).
    (* Every petal's head is x. *)
    assert (Hheadx : forall C, In C S -> C = x :: tl C).
    { intros C HC.
      destruct (Hstruct C HC) as [jc [C' [Hjc [HC' EC]]]].
      pose proof (Hxall C HC) as HxC. rewrite EC in HxC.
      destruct HxC as [E | HxC'].
      - rewrite EC. simpl. rewrite E. reflexivity.
      - exfalso.
        pose proof (prod_family_bounded t n C' x HC' HxC'). lia. }
    (* Strip the shared head and recurse. *)
    set (S2 := map (@tl nat) S).
    assert (Hincl2 : incl S2 (prod_family t n)).
    { intros T HT. unfold S2 in HT.
      apply in_map_iff in HT as [C [ET HC]].
      destruct (Hstruct C HC) as [jc [C' [Hjc [HC' EC]]]].
      subst T. rewrite EC. simpl. exact HC'. }
    assert (Hnd2 : NoDup S2).
    { unfold S2. apply NoDup_map_inj_on; [exact Hnd|].
      intros C D HC HD E.
      assert (ECx := Hheadx C HC). assert (EDx := Hheadx D HD).
      rewrite ECx, EDx, E. reflexivity. }
    assert (Hlen2 : length S2 = k) by (unfold S2; rewrite map_length; exact Hlen).
    assert (Hsun2 : Sunflower S2 (rem_elt x core)).
    { split.
      - apply (@SetNoDup_incl S2 (prod_family t n));
          [apply prod_family_SetNoDup | exact Hnd2 | exact Hincl2].
      - intros U V HU HV Hne.
        unfold S2 in HU, HV.
        apply in_map_iff in HU as [C [EU HC]].
        apply in_map_iff in HV as [D [EV HD]].
        subst U V.
        assert (HCD : C <> D) by (intro E; subst D; apply Hne; reflexivity).
        pose proof (Hcore C D HC HD HCD) as Hc.
        assert (HCx := Hheadx C HC). assert (HDx := Hheadx D HD).
        assert (HndC : NoDup C).
        { destruct (prod_family_len_nodup t (Datatypes.S n) C (Hincl C HC))
            as [_ Hn']. exact Hn'. }
        assert (HndD : NoDup D).
        { destruct (prod_family_len_nodup t (Datatypes.S n) D (Hincl D HD))
            as [_ Hn']. exact Hn'. }
        assert (HxnotC : ~ In x (tl C)).
        { intro Hx. rewrite HCx in HndC.
          inversion HndC; subst; contradiction. }
        assert (HxnotD : ~ In x (tl D)).
        { intro Hx. rewrite HDx in HndD.
          inversion HndD; subst; contradiction. }
        split; intros y Hy.
        + apply in_inter_iff in Hy as [HyC HyD].
          apply in_rem_iff. split.
          * destruct Hc as [Hc1 _]. apply Hc1. apply in_inter_iff.
            split; [rewrite HCx; right; exact HyC
                   | rewrite HDx; right; exact HyD].
          * intro E; subst y; contradiction.
        + apply in_rem_iff in Hy as [Hyc Hyx].
          destruct Hc as [_ Hc2].
          pose proof (Hc2 y Hyc) as Hy2.
          apply in_inter_iff in Hy2 as [HyC HyD].
          apply in_inter_iff. split.
          * rewrite HCx in HyC.
            destruct HyC as [E | HyC'];
              [exfalso; apply Hyx; symmetry; exact E | exact HyC'].
          * rewrite HDx in HyD.
            destruct HyD as [E | HyD'];
              [exfalso; apply Hyx; symmetry; exact E | exact HyD']. }
    exact (IH S2 (rem_elt x core) Hincl2 Hnd2 Hlen2 Hsun2).
Qed.

(** ** Main theorem: [f(n, k) >= (k-1)^n + 1] *)

Theorem lower_bound_exponential :
  forall n k, 1 <= n -> 2 <= k -> LowerBound n k ((k - 1) ^ n).
Proof.
  intros n k Hn Hk.
  exists (prod_family (k - 1) n).
  split; [apply prod_family_Uniform|].
  split; [apply prod_family_SetNoDup|].
  split; [rewrite prod_family_length; lia|].
  intro Hcontains.
  destruct (contains_sunflower_literal k (prod_family (k - 1) n) Hcontains)
    as [S [core [Hincl [Hnd [Hlen Hsun]]]]].
  assert (Htk : k - 1 < k) by lia.
  exact (prod_family_no_literal_sunflower (k - 1) k Htk Hk n S core
           Hincl Hnd Hlen Hsun).
Qed.

(** The exponential lower bound dominates the trivial one. *)

Corollary exponential_dominates_trivial :
  forall n k, 1 <= n -> 2 <= k -> k - 1 <= (k - 1) ^ n.
Proof.
  intros n k Hn Hk.
  assert (H1 : (k - 1) ^ 1 <= (k - 1) ^ n)
    by (apply Nat.pow_le_mono_r; lia).
  rewrite Nat.pow_1_r in H1. exact H1.
Qed.
