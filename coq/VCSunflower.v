(** * VCSunflower.v -- The sunflower conjecture for families of bounded
      VC-dimension.

    Ge, Wang, Xu and Zhao (arXiv:2609.18995, July 2026) proved the
    Erdős–Rado conjecture for set systems of bounded VC-dimension: for
    fixed [d] and [r], every [l]-uniform family with VC-dimension at most
    [d] and more than [K(d,r)^l] members contains an [r]-sunflower. This
    file machine-checks that statement ([vc_sunflower_bound],
    [vc_sunflower_conjecture]) — the uniform form, their Theorem 1.1's
    "in particular"; the [l]-bounded form with the bound
    [Σ_{k ≤ l} (50dr)^k] is not formalised here.

    The proof follows theirs in outline — spread reduction, then a
    second-moment bound on the degrees of a spread family, then many
    pairwise disjoint members — but every analytic step is replaced by
    an elementary one over [nat], so that it can be done with the
    standard library alone:

    - their entropy lemma (2.3) becomes a *tail bound over traces*: the
      members whose trace on a point set [E] is larger than [t] are
      grouped by trace, each group is small by spreadness, and there are
      few groups by Sauer–Shelah ([trace_sum_bound]);
    - Sauer–Shelah itself is proved here, over canonical traces
      ([sauer_shelah]), with the crude bound [(M+1)^d] on the shatter
      function ([Phi_le_pow]);
    - their Caro–Wei step (Lemma 2.2 / 2.6) becomes a greedy induction
      whose invariant is [2 t S(F) < |F|^2], [S(F)] being the number of
      intersecting ordered pairs ([greedy_disjoint]);
    - their dyadic layering (Lemma 2.4) is kept, with every division
      cleared ([sum_deg_sq_bound]).

    The price of [(M+1)^d] in place of [(eM/d)^d] is the constant: the
    threshold proved here is [K = 2^s] with [s = 2d + 3 + log2((64d+8)r)],
    exponential in [d], against the source's [50dr]. For the conjecture
    restricted to bounded VC-dimension only the existence of a constant
    for each fixed [d] matters, and that is what is proved.

    What this is not: progress on the general conjecture. Every
    [n]-uniform family has VC-dimension at most [n] ([uniform_vc_le]),
    and the Erdős–Rado product construction attains it
    ([product_vc_full]), so that construction lies outside every fixed
    class this file covers. (Lower-bound constructions of small
    VC-dimension do exist — Balogh et al. settle [d = 1] — so this is a
    statement about the product construction, not about all of them.) *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat Wf_nat Permutation.
From Sunflower Require Import Sets Sunflower Pigeonhole ErdosRado Spread
  SpreadReduction ProductLowerBound.
Import ListNotations.

Set Implicit Arguments.

(** ** Sums *)

Definition sumf {A : Type} (f : A -> nat) (l : list A) : nat :=
  fold_right (fun x acc => f x + acc) 0 l.

Lemma sumf_app : forall {A} (f : A -> nat) l1 l2,
    sumf f (l1 ++ l2) = sumf f l1 + sumf f l2.
Proof.
  intros A f l1 l2; induction l1 as [|a l1 IH]; simpl; [reflexivity|].
  rewrite IH; lia.
Qed.

Lemma sumf_le : forall {A} (f g : A -> nat) l,
    (forall x, In x l -> f x <= g x) -> sumf f l <= sumf g l.
Proof.
  intros A f g l H; induction l as [|a l IH]; simpl; [lia|].
  assert (f a <= g a) by (apply H; left; reflexivity).
  assert (sumf f l <= sumf g l) by (apply IH; intros; apply H; right; assumption).
  lia.
Qed.

Lemma sumf_ext : forall {A} (f g : A -> nat) l,
    (forall x, In x l -> f x = g x) -> sumf f l = sumf g l.
Proof.
  intros A f g l H; induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite H by (left; reflexivity).
  rewrite IH by (intros; apply H; right; assumption). reflexivity.
Qed.

Lemma sumf_const : forall {A} (c : nat) (l : list A),
    sumf (fun _ => c) l = c * length l.
Proof.
  intros A c l; induction l as [|a l IH]; simpl; [lia|]. rewrite IH; lia.
Qed.

Lemma sumf_add : forall {A} (f g : A -> nat) l,
    sumf (fun x => f x + g x) l = sumf f l + sumf g l.
Proof.
  intros A f g l; induction l as [|a l IH]; simpl; [reflexivity|]. rewrite IH; lia.
Qed.

Lemma sumf_mul_l : forall {A} (c : nat) (f : A -> nat) l,
    sumf (fun x => c * f x) l = c * sumf f l.
Proof.
  intros A c f l; induction l as [|a l IH]; simpl; [lia|]. rewrite IH; lia.
Qed.

Lemma sumf_filter : forall {A} (p : A -> bool) (f : A -> nat) l,
    sumf f (filter p l) = sumf (fun x => if p x then f x else 0) l.
Proof.
  intros A p f l; induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (p a); simpl; rewrite IH; reflexivity.
Qed.

Lemma sumf_filter_le : forall {A} (p : A -> bool) (f : A -> nat) l,
    sumf f (filter p l) <= sumf f l.
Proof.
  intros A p f l; induction l as [|a l IH]; simpl; [lia|].
  destruct (p a); simpl; lia.
Qed.

Lemma sumf_partition : forall {A} (p : A -> bool) (f : A -> nat) l,
    sumf f l = sumf f (filter p l) + sumf f (filter (fun x => negb (p x)) l).
Proof.
  intros A p f l; induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (p a); simpl; rewrite IH; lia.
Qed.

(** Exchanging the order of a double sum. *)

Lemma sumf_swap : forall {A B} (g : A -> B -> nat) (l1 : list A) (l2 : list B),
    sumf (fun x => sumf (g x) l2) l1 = sumf (fun y => sumf (fun x => g x y) l1) l2.
Proof.
  intros A B g l1 l2; induction l1 as [|a l1 IH]; simpl.
  - induction l2; simpl; [reflexivity | rewrite <- IHl2; reflexivity].
  - rewrite IH. clear IH. induction l2 as [|b l2 IH2]; simpl; [reflexivity|].
    rewrite <- IH2. lia.
Qed.

Lemma sumf_perm : forall {A} (f : A -> nat) l l',
    Permutation l l' -> sumf f l = sumf f l'.
Proof.
  intros A f l l' H; induction H; simpl; lia.
Qed.

(** A sum over a duplicate-free sublist [A] of a duplicate-free list [U]
    is the sum over [U] of the terms indexed in [A]. *)

Lemma sumf_sub : forall (f : nat -> nat) (A U : list nat),
    NoDup A -> NoDup U -> incl A U ->
    sumf f A = sumf (fun x => if memb x A then f x else 0) U.
Proof.
  intros f A U HA HU Hinc.
  rewrite <- sumf_filter.
  apply sumf_perm, NoDup_Permutation; [exact HA | apply NoDup_filter, HU|].
  intros x; rewrite filter_In, memb_true_iff; split; [|tauto].
  intros Hx; split; [apply Hinc|]; exact Hx.
Qed.

(** ** Shattering and VC-dimension

    [D] is shattered by [F] when every subset of [D] is the trace
    [A ∩ D] of some member [A]. [VCdimLe d F] says no duplicate-free [D]
    of more than [d] points is shattered — the standard definition, with
    set equality where the list representation needs it. *)

Definition Shatters (F : Family) (D : list nat) : Prop :=
  forall B, Subset B D -> exists A, In A F /\ SetEq (inter A D) B.

Definition VCdimLe (d : nat) (F : Family) : Prop :=
  forall D, NoDup D -> Shatters F D -> length D <= d.

Lemma VCdimLe_mono : forall d d' F, d <= d' -> VCdimLe d F -> VCdimLe d' F.
Proof. intros d d' F Hle H D HD Hs; specialize (H D HD Hs); lia. Qed.

(** ** Sauer–Shelah over canonical traces

    A trace on the point list [E] is represented canonically: as the
    sublist of [E] it selects, in [E]'s order. [Phi d M] is the shatter
    function bound [Σ_{i ≤ d} C(M,i)], by its Pascal recurrence. *)

Definition Canon (E v : list nat) : Prop :=
  v = filter (fun x => memb x v) E.

Fixpoint Phi (d M : nat) : nat :=
  match M with
  | 0 => 1
  | S M' => Phi d M' + match d with 0 => 0 | S d' => Phi d' M' end
  end.

Lemma Phi_le_pow : forall M d, Phi d M <= (M + 1) ^ d.
Proof.
  induction M as [|M IH]; intros d; simpl.
  - rewrite Nat.pow_1_l; lia.
  - destruct d as [|d'].
    + specialize (IH 0); simpl in *; lia.
    + pose proof (IH (S d')) as H1; pose proof (IH d') as H2.
      assert (H3 : (M + 1) ^ d' <= (S (M + 1)) ^ d')
        by (apply Nat.pow_le_mono_l; lia).
      replace (S M + 1) with (S (M + 1)) by lia.
      simpl in *. nia.
Qed.

Definition inlb (w : list nat) (L : list (list nat)) : bool :=
  if in_dec (list_eq_dec Nat.eq_dec) w L then true else false.

Lemma inlb_true : forall w L, inlb w L = true <-> In w L.
Proof.
  intros w L; unfold inlb; destruct (in_dec _ w L); split; intros; auto; discriminate.
Qed.

Lemma NoDup_map_inj_on_list : forall {A B} (f : A -> B) (l : list A),
    NoDup l -> (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
    NoDup (map f l).
Proof.
  intros A B f l Hnd; induction Hnd as [|a l Hni Hnd IH]; intros Hinj; simpl;
    constructor.
  - intro Hin; apply in_map_iff in Hin as [y [E Hy]].
    assert (y = a) by (apply Hinj; [right | left | ]; auto).
    subst; contradiction.
  - apply IH; intros; apply Hinj; [right | right |]; auto.
Qed.

Lemma NoDup_app_disj : forall {A} (l1 l2 : list A),
    NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> In x l2 -> False) ->
    NoDup (l1 ++ l2).
Proof.
  intros A l1 l2 H1; induction H1 as [|a l1 Hni H1 IH]; intros H2 Hd; simpl; [exact H2|].
  constructor.
  - intro Hin; apply in_app_or in Hin as [Hin | Hin]; [contradiction|].
    apply (Hd a); [left; reflexivity | exact Hin].
  - apply IH; [exact H2|]. intros x Hx1 Hx2; apply (Hd x); [right|]; assumption.
Qed.

(** Canonical traces on [e :: E'] split by whether they contain [e]. *)

Lemma canon_cons_out : forall e E' v,
    Canon (e :: E') v -> memb e v = false -> Canon E' v.
Proof.
  intros e E' v Hc Hm; unfold Canon in *; simpl in Hc; rewrite Hm in Hc; exact Hc.
Qed.

Lemma canon_cons_in : forall e E' v,
    ~ In e E' -> Canon (e :: E') v -> memb e v = true ->
    v = e :: tl v /\ Canon E' (tl v) /\ ~ In e (tl v).
Proof.
  intros e E' v Hni Hc Hm; unfold Canon in *; simpl in Hc; rewrite Hm in Hc.
  set (w := filter (fun x => memb x v) E') in Hc.
  assert (Hw : tl v = w) by (rewrite Hc; reflexivity).
  assert (Hne : ~ In e w).
  { intro Hin; unfold w in Hin; apply filter_In in Hin as [Hin _]; contradiction. }
  repeat split.
  - rewrite Hw; exact Hc.
  - rewrite Hw. unfold Canon.
    transitivity (filter (fun x => memb x v) E'); [reflexivity|].
    apply filter_ext_in. intros x Hx.
    destruct (memb x v) eqn:Ev.
    + symmetry; apply memb_true_iff. apply filter_In; split; [exact Hx | exact Ev].
    + symmetry; apply memb_false_iff. intro Hin; apply filter_In in Hin as [_ Hin].
      rewrite Ev in Hin; discriminate.
  - rewrite Hw; exact Hne.
Qed.

Lemma canon_nil : forall v, Canon [] v -> v = [].
Proof. intros v H; unfold Canon in H; simpl in H; exact H. Qed.

Lemma shatters_nil : forall V w, In w V -> Shatters V [].
Proof.
  intros V w Hw B HB; exists w; split; [exact Hw|].
  split; intros x Hx.
  - apply in_inter_iff in Hx as [_ []].
  - destruct (HB x Hx).
Qed.

Theorem sauer_shelah : forall E d V,
    NoDup E -> NoDup V -> (forall v, In v V -> Canon E v) ->
    (forall D, NoDup D -> incl D E -> Shatters V D -> length D <= d) ->
    length V <= Phi d (length E).
Proof.
  induction E as [|e E' IH]; intros d V HE HV Hc Hvc.
  - (* every trace on the empty list is [[]] *)
    simpl. destruct V as [|v [|v' V']]; simpl; [lia | lia |].
    exfalso.
    rewrite (canon_nil (Hc v (or_introl eq_refl))) in HV.
    rewrite (canon_nil (Hc v' (or_intror (or_introl eq_refl)))) in HV.
    inversion HV as [|? ? Hni _]; apply Hni; left; reflexivity.
  - inversion HE as [|? ? HeE' HE']; subst.
    set (Vn := filter (fun v => negb (memb e v)) V).
    set (Ve := filter (fun v => memb e v) V).
    set (We := map (@tl nat) Ve).
    set (Vu := Vn ++ filter (fun w => negb (inlb w Vn)) We).
    set (Vi := filter (fun w => inlb w Vn) We).
    assert (HlenV : length V = length Vn + length Ve).
    { unfold Vn, Ve. rewrite (length_filter_partition (fun v => memb e v) V). lia. }
    assert (HVe_shape : forall v, In v Ve ->
               v = e :: tl v /\ Canon E' (tl v) /\ ~ In e (tl v)).
    { intros v Hv; unfold Ve in Hv; apply filter_In in Hv as [HvV Hm].
      apply canon_cons_in; auto. }
    assert (HWe_in : forall w, In w We -> In (e :: w) V /\ Canon E' w /\ ~ In e w).
    { intros w Hw; unfold We in Hw; apply in_map_iff in Hw as [v [Ew Hv]]; subst w.
      destruct (HVe_shape v Hv) as [Hs [Hcw Hnw]].
      repeat split; auto.
      rewrite <- Hs. unfold Ve in Hv; apply filter_In in Hv; tauto. }
    assert (HVn_in : forall w, In w Vn -> In w V /\ Canon E' w /\ ~ In e w).
    { intros w Hw; unfold Vn in Hw; apply filter_In in Hw as [HwV Hm].
      apply Bool.negb_true_iff in Hm.
      repeat split; auto.
      - eapply canon_cons_out; [apply Hc; exact HwV | exact Hm].
      - apply memb_false_iff; exact Hm. }
    assert (HlenWe : length We = length Ve) by (unfold We; apply map_length).
    assert (HWe_nd : NoDup We).
    { unfold We. apply NoDup_map_inj_on_list.
      - unfold Ve; apply NoDup_filter; exact HV.
      - intros x y Hx Hy Exy.
        destruct (HVe_shape x Hx) as [Hx' _]; destruct (HVe_shape y Hy) as [Hy' _].
        rewrite Hx', Hy', Exy; reflexivity. }
    assert (HVn_nd : NoDup Vn) by (unfold Vn; apply NoDup_filter; exact HV).
    assert (Hlen_ui : length Vn + length We = length Vu + length Vi).
    { unfold Vu, Vi. rewrite app_length.
      rewrite (length_filter_partition (fun w => inlb w Vn) We). lia. }
    assert (HVu_nd : NoDup Vu).
    { unfold Vu. apply NoDup_app_disj; [exact HVn_nd | apply NoDup_filter, HWe_nd |].
      intros w Hw1 Hw2. apply filter_In in Hw2 as [_ Hb].
      apply Bool.negb_true_iff in Hb.
      assert (inlb w Vn = true) by (apply inlb_true; exact Hw1).
      congruence. }
    assert (HVi_nd : NoDup Vi) by (unfold Vi; apply NoDup_filter, HWe_nd).
    (* the union shatters only what [V] shatters *)
    assert (HVu_vc : forall D, NoDup D -> incl D E' -> Shatters Vu D -> length D <= d).
    { intros D HD HDE Hs. apply Hvc; [exact HD | intros x Hx; right; apply HDE, Hx |].
      intros B HB. destruct (Hs B HB) as [w [Hw Heq]].
      unfold Vu in Hw; apply in_app_or in Hw as [Hw | Hw].
      - exists w; split; [apply (HVn_in w Hw) | exact Heq].
      - apply filter_In in Hw as [Hw _].
        destruct (HWe_in w Hw) as [HeV _].
        exists (e :: w); split; [exact HeV|].
        assert (HeD : ~ In e D) by (intro HeD; apply HeE', HDE, HeD).
        eapply SetEq_trans; [|exact Heq].
        split; intros x Hx; apply in_inter_iff in Hx as [Hx1 Hx2];
          apply in_inter_iff; split; auto.
        + destruct Hx1 as [Hx1 | Hx1]; [subst; contradiction | exact Hx1].
        + right; exact Hx1. }
    (* the intersection shatters [D] only if [V] shatters [e :: D] *)
    assert (HVi_sh : forall D, incl D E' -> Shatters Vi D -> Shatters V (e :: D)).
    { intros D HDE Hs B HB.
      assert (HB' : Subset (rem_elt e B) D).
      { intros x Hx; apply in_rem_iff in Hx as [Hx Hxe].
        destruct (HB x Hx) as [E0 | Hx']; [congruence | exact Hx']. }
      destruct (Hs (rem_elt e B) HB') as [w [Hw Heq]].
      unfold Vi in Hw; apply filter_In in Hw as [HwWe HwVn].
      apply inlb_true in HwVn.
      destruct (HWe_in w HwWe) as [HeV [_ Hnew]].
      destruct (HVn_in w HwVn) as [HwV _].
      destruct (in_dec Nat.eq_dec e B) as [HeB | HeB].
      - exists (e :: w); split; [exact HeV|].
        split; intros x Hx.
        + apply in_inter_iff in Hx as [[Ex | Hx1] Hx2]; [subst; exact HeB|].
          destruct Hx2 as [Ex | Hx2]; [subst; contradiction|].
          assert (In x (inter w D)) by (apply in_inter_iff; auto).
          apply Heq in H. apply in_rem_iff in H; tauto.
        + apply in_inter_iff. destruct (Nat.eq_dec x e) as [Ex | Hxe].
          * subst; split; left; reflexivity.
          * assert (In x (rem_elt e B)) by (apply in_rem_iff; auto).
            apply Heq in H. apply in_inter_iff in H as [H1 H2].
            split; right; assumption.
      - exists w; split; [exact HwV|].
        split; intros x Hx.
        + apply in_inter_iff in Hx as [Hx1 Hx2].
          destruct Hx2 as [Ex | Hx2]; [subst; contradiction|].
          assert (In x (inter w D)) by (apply in_inter_iff; auto).
          apply Heq in H. apply in_rem_iff in H; tauto.
        + assert (Hxe : x <> e) by (intro; subst; contradiction).
          assert (In x (rem_elt e B)) by (apply in_rem_iff; auto).
          apply Heq in H. apply in_inter_iff in H as [H1 H2].
          apply in_inter_iff; split; [exact H1 | right; exact H2]. }
    assert (Hcu : forall v, In v Vu -> Canon E' v).
    { intros v Hv; unfold Vu in Hv; apply in_app_or in Hv as [Hv | Hv].
      - apply (HVn_in v Hv).
      - apply filter_In in Hv as [Hv _]; apply (HWe_in v Hv). }
    assert (Hci : forall v, In v Vi -> Canon E' v).
    { intros v Hv; unfold Vi in Hv; apply filter_In in Hv as [Hv _]; apply (HWe_in v Hv). }
    pose proof (IH d Vu HE' HVu_nd Hcu HVu_vc) as Hu.
    assert (Hi : length Vi <= match d with 0 => 0 | S d' => Phi d' (length E') end).
    { destruct d as [|d'].
      - destruct (list_eq_dec (list_eq_dec Nat.eq_dec) Vi []) as [E0 | Hne];
          [rewrite E0; simpl; lia|].
        exfalso.
        assert (Hw : exists w, In w Vi).
        { clearbody Vi. destruct Vi as [|w Vi']; [congruence|].
          exists w; left; reflexivity. }
        destruct Hw as [w Hw].
        assert (Hs : Shatters V [e]).
        { apply HVi_sh; [intros x []|]. apply (shatters_nil Vi w Hw). }
        pose proof (Hvc [e] ltac:(constructor; [intros [] | constructor])
                      ltac:(intros x [Ex|[]]; subst; left; reflexivity) Hs).
        simpl in H; lia.
      - apply IH; [exact HE' | exact HVi_nd | exact Hci |].
        intros D HD HDE Hs.
        assert (HeD : ~ In e D) by (intro HeD; apply HeE', HDE, HeD).
        pose proof (Hvc (e :: D) ltac:(constructor; assumption)
                      ltac:(intros x [Ex | Hx]; [subst; left; reflexivity
                                                | right; apply HDE, Hx])
                      (HVi_sh D HDE Hs)).
        simpl in H; lia. }
    simpl. lia.
Qed.

(** ** Traces of a family on a point list *)

Definition tr (E A : list nat) : list nat := filter (fun x => memb x A) E.

Definition leq_dec := list_eq_dec Nat.eq_dec.

Definition Traces (E : list nat) (F : Family) : list (list nat) :=
  nodup leq_dec (map (tr E) F).

Lemma in_tr : forall x E A, In x (tr E A) <-> In x E /\ In x A.
Proof.
  intros x E A; unfold tr; rewrite filter_In, memb_true_iff; tauto.
Qed.

Lemma tr_canon : forall E A, Canon E (tr E A).
Proof.
  intros E A; unfold Canon, tr at 2. apply filter_ext_in. intros x Hx.
  destruct (memb x A) eqn:Ex.
  - symmetry; apply memb_true_iff, in_tr; split; [exact Hx | apply memb_true_iff, Ex].
  - symmetry; apply memb_false_iff; intro H; apply in_tr in H as [_ H].
    apply memb_true_iff in H; congruence.
Qed.

Lemma tr_NoDup : forall E A, NoDup E -> NoDup (tr E A).
Proof. intros; unfold tr; apply NoDup_filter; assumption. Qed.

Lemma traces_shatter : forall E F D,
    incl D E -> Shatters (Traces E F) D -> Shatters F D.
Proof.
  intros E F D HDE Hs B HB. destruct (Hs B HB) as [v [Hv Heq]].
  unfold Traces in Hv; apply nodup_In, in_map_iff in Hv as [A [Ev HA]]; subst v.
  exists A; split; [exact HA|].
  eapply SetEq_trans; [|exact Heq].
  split; intros x Hx; apply in_inter_iff in Hx as [Hx1 Hx2]; apply in_inter_iff.
  - split; [apply in_tr; split; [apply HDE, Hx2 | exact Hx1] | exact Hx2].
  - apply in_tr in Hx1; tauto.
Qed.

Theorem traces_count : forall d E F,
    NoDup E -> VCdimLe d F -> length (Traces E F) <= Phi d (length E).
Proof.
  intros d E F HE Hvc. apply sauer_shelah; [exact HE | apply NoDup_nodup | |].
  - intros v Hv; unfold Traces in Hv; apply nodup_In, in_map_iff in Hv as [A [Ev _]].
    subst v; apply tr_canon.
  - intros D HD HDE Hs. apply Hvc; [exact HD|]. apply (@traces_shatter E F D HDE Hs).
Qed.

(** ** Counting lemmas *)

Lemma length_filter_sumf : forall {A} (p : A -> bool) l,
    length (filter p l) = sumf (fun a => if p a then 1 else 0) l.
Proof.
  intros A p l; induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (p a); simpl; rewrite IH; reflexivity.
Qed.

Lemma length_filter_mono : forall {A} (p q : A -> bool) l,
    (forall a, In a l -> p a = true -> q a = true) ->
    length (filter p l) <= length (filter q l).
Proof.
  intros A p q l H; induction l as [|a l IH]; simpl; [lia|].
  assert (IH' : length (filter p l) <= length (filter q l))
    by (apply IH; intros; apply H; [right|]; assumption).
  destruct (p a) eqn:Ep.
  - rewrite (H a (or_introl eq_refl) Ep); simpl; lia.
  - destruct (q a); simpl; lia.
Qed.

(** Summing over a list by summing over its distinct values, each weighted
    by its multiplicity. *)

Lemma sumf_single : forall (g : list nat -> nat) (a : list nat) l,
    NoDup l -> In a l ->
    sumf (fun y => if leq_dec a y then g y else 0) l = g a.
Proof.
  intros g a l Hnd; induction Hnd as [|b l Hni Hnd IH]; intros Hin; [destruct Hin|].
  simpl. destruct (leq_dec a b) as [Eab | Nab].
  - subst b. rewrite (sumf_ext _ (fun _ => 0)); [rewrite sumf_const; lia|].
    intros y Hy. destruct (leq_dec a y); [subst; contradiction | reflexivity].
  - destruct Hin as [Eba | Hin]; [congruence|]. rewrite IH by exact Hin; lia.
Qed.

Lemma sumf_fibres : forall (g : list nat -> nat) (L : list (list nat)),
    sumf g L = sumf (fun y => g y * count_occ leq_dec L y) (nodup leq_dec L).
Proof.
  intros g L; induction L as [|a L IH]; simpl; [reflexivity|].
  destruct (in_dec leq_dec a L) as [Ha | Ha].
  - rewrite IH.
    rewrite (sumf_ext (fun y => g y * (if leq_dec a y then S (count_occ leq_dec L y)
                                          else count_occ leq_dec L y))
                      (fun y => g y * count_occ leq_dec L y
                                + (if leq_dec a y then g y else 0))).
    + rewrite sumf_add, sumf_single; [lia | apply NoDup_nodup | apply nodup_In, Ha].
    + intros y _; destruct (leq_dec a y); lia.
  - simpl. destruct (leq_dec a a) as [_ | C]; [|congruence].
    assert (H0 : count_occ leq_dec L a = 0) by (apply count_occ_not_In; exact Ha).
    rewrite H0, IH.
    f_equal; [lia|]. apply sumf_ext. intros y Hy.
    destruct (leq_dec a y) as [E0 | _]; [|reflexivity].
    subst; apply nodup_In in Hy; contradiction.
Qed.

Lemma count_occ_map_le_deg : forall E F y,
    count_occ leq_dec (map (tr E) F) y <= deg y F.
Proof.
  intros E F y. unfold deg.
  induction F as [|A F IH]; simpl; [lia|].
  destruct (leq_dec (tr E A) y) as [Ey | Ny].
  - assert (Hc : containsb y A = true).
    { apply containsb_true_iff; intros x Hx; subst y; apply in_tr in Hx; tauto. }
    rewrite Hc; simpl; lia.
  - destruct (containsb y A); simpl; lia.
Qed.

(** [s R^(t+1) <= (t+1) R^s] once [s > t] and [R >= 2]: the function
    [s / R^s] is decreasing. *)

Lemma pow_ratio : forall k t R, 2 <= R ->
    (t + 1 + k) * R ^ (t + 1) <= (t + 1) * R ^ (t + 1 + k).
Proof.
  induction k as [|k IH]; intros t R HR; [rewrite !Nat.add_0_r; lia|].
  specialize (IH t R HR).
  replace (t + 1 + S k) with (S (t + 1 + k)) by lia.
  rewrite Nat.pow_succ_r'.
  assert (R ^ (t + 1) <= R ^ (t + 1 + k)) by (apply Nat.pow_le_mono_r; lia).
  nia.
Qed.

(** Double counting: the degrees of the points of [E] add up to the total
    size of the traces on [E]. *)

Lemma sum_deg_tr : forall E F,
    sumf (fun x => deg [x] F) E = sumf (fun A => length (tr E A)) F.
Proof.
  intros E F.
  rewrite (sumf_ext (fun x => deg [x] F)
             (fun x => sumf (fun A => if memb x A then 1 else 0) F)).
  - rewrite <- sumf_swap. apply sumf_ext. intros A _.
    unfold tr; rewrite length_filter_sumf; reflexivity.
  - intros x _; unfold deg; rewrite length_filter_sumf. apply sumf_ext.
    intros A _. unfold containsb; simpl. destruct (memb x A); reflexivity.
Qed.

(** ** The trace tail bound — the entropy-free replacement for Lemma 2.3

    If a family is [R]-spread, [R >= 2], and has at most [R^t] traces on
    a duplicate-free point list [E], the degrees on [E] sum to at most
    [(2t+1)|F|]. Members with a trace of at most [t] points contribute at
    most [t] each. The rest are grouped by trace: a group with trace [τ]
    has at most [deg τ F <= |F|/R^|τ|] members, so contributes at most
    [|τ| |F| / R^|τ| <= (t+1)|F|/R^(t+1)], and there are at most [R^t]
    groups. *)

Theorem trace_sum_bound : forall E F R t,
    NoDup E -> Spread F R -> 2 <= R ->
    length (Traces E F) <= R ^ t ->
    sumf (fun x => deg [x] F) E <= (2 * t + 1) * length F.
Proof.
  intros E F R t HE Hsp HR Htr.
  rewrite sum_deg_tr.
  set (big := fun s => if t <? s then s else 0).
  set (small := fun s => if t <? s then 0 else s).
  rewrite (sumf_ext (fun A => length (tr E A))
             (fun A => small (length (tr E A)) + big (length (tr E A))))
    by (intros A _; unfold small, big; destruct (t <? length (tr E A)); lia).
  rewrite sumf_add.
  assert (Hs : sumf (fun A => small (length (tr E A))) F <= t * length F).
  { rewrite <- sumf_const. apply sumf_le. intros A _. unfold small.
    destruct (t <? length (tr E A)) eqn:Et; [lia|]. apply Nat.ltb_ge in Et; lia. }
  assert (Hb : R * sumf (fun A => big (length (tr E A))) F <= (t + 1) * length F).
  { assert (Hmap : forall (h : list nat -> nat) l,
               sumf h (map (tr E) l) = sumf (fun A => h (tr E A)) l)
      by (intros h l; induction l; simpl; [reflexivity | rewrite IHl; reflexivity]).
    rewrite <- (Hmap (fun y => big (length y)) F).
    rewrite sumf_fibres. fold (Traces E F).
    (* each fibre contributes at most (t+1)|F| / R^(t+1) *)
    assert (Hfib : forall y, In y (Traces E F) ->
               R ^ (t + 1) * (big (length y) * count_occ leq_dec (map (tr E) F) y)
               <= (t + 1) * length F).
    { intros y Hy. unfold big. destruct (t <? length y) eqn:Et; [|simpl; lia].
      apply Nat.ltb_lt in Et.
      unfold Traces in Hy; apply nodup_In, in_map_iff in Hy as [A [Ey _]].
      assert (Hynd : NoDup y) by (subst; apply tr_NoDup, HE).
      pose proof (Hsp y Hynd) as Hspy.
      pose proof (count_occ_map_le_deg E F y) as Hc.
      pose proof (pow_ratio (length y - (t + 1)) t HR) as Hr.
      replace (t + 1 + (length y - (t + 1))) with (length y) in Hr by lia.
      set (c := count_occ leq_dec (map (tr E) F) y) in *.
      assert (R ^ length y * c <= length F) by nia.
      nia. }
    assert (Hsum : R ^ (t + 1) *
              sumf (fun y => big (length y) * count_occ leq_dec (map (tr E) F) y)
                   (Traces E F) <= R ^ t * ((t + 1) * length F)).
    { rewrite <- sumf_mul_l.
      eapply Nat.le_trans; [apply (sumf_le _ (fun _ => (t + 1) * length F)); exact Hfib|].
      rewrite sumf_const. nia. }
    rewrite Nat.pow_add_r, Nat.pow_1_r in Hsum.
    assert (Hpos : 0 < R ^ t) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
    set (X := sumf _ (Traces E F)) in *.
    nia. }
  nia.
Qed.

(** ** Dyadic layers — the replacement for Lemma 2.4

    With [R = 2^s], every point of positive degree lies in exactly one
    layer [j], meaning [R 2^j deg(x) <= |F| < R 2^(j+1) deg(x)]. A layer
    has at most [M_j = R 2^(j+1) (2 t_j + 1)] points, [t_j = 2d(j+1)]:
    otherwise [M_j + 1] of its points would carry degree sum above
    [(2 t_j + 1)|F|], which [trace_sum_bound] forbids because
    Sauer–Shelah gives them at most [(M_j + 2)^d <= R^(t_j)] traces.
    Summing [deg^2] layer by layer gives the second-moment bound. *)

Lemma two_pow_ge : forall n, n + 1 <= 2 ^ n.
Proof.
  induction n as [|n IH]; simpl; lia.
Qed.

Lemma layer_exp : forall d s j,
    2 * d + 2 <= s ->
    (2 ^ s * 2 ^ (j + 1) * (2 * (2 * d * (j + 1)) + 1) + 2) ^ d
      <= (2 ^ s) ^ (2 * d * (j + 1)).
Proof.
  intros d s j Hs.
  set (t := 2 * d * (j + 1)).
  assert (H1 : 2 ^ s * 2 ^ (j + 1) * (2 * t + 1) + 2 <= 2 ^ (s + j + t + 2)).
  { assert (H2 : 2 * t + 2 <= 2 ^ (t + 1))
      by (pose proof (two_pow_ge t); rewrite Nat.pow_add_r; simpl; lia).
    replace (2 ^ (s + j + t + 2)) with (2 ^ s * 2 ^ (j + 1) * 2 ^ (t + 1))
      by (rewrite <- !Nat.pow_add_r; f_equal; lia).
    assert (HP : 2 <= 2 ^ s * 2 ^ (j + 1)).
    { assert (1 <= 2 ^ s) by (pose proof (two_pow_ge s); lia).
      assert (2 <= 2 ^ (j + 1)) by (pose proof (two_pow_ge (j + 1)); lia). nia. }
    set (P := 2 ^ s * 2 ^ (j + 1)) in *. set (Q := 2 ^ (t + 1)) in *.
    nia. }
  eapply Nat.le_trans; [apply Nat.pow_le_mono_l, H1|].
  rewrite <- !Nat.pow_mul_r. apply Nat.pow_le_mono_r; [lia|].
  unfold t.
  assert (H3 : s + j + 2 * d * (j + 1) + 2 <= 2 * s * (j + 1)).
  { assert (A : s <= s * (j + 1)) by (rewrite Nat.mul_add_distr_l; lia).
    assert (B : (2 * d + 2) * (j + 1) <= s * (j + 1)) by (apply Nat.mul_le_mono_r; lia).
    lia. }
  pose proof (Nat.mul_le_mono_l _ _ d H3). lia.
Qed.

Lemma layer_bounds : forall N R g,
    1 <= R -> 1 <= g -> R * g <= N ->
    R * g * 2 ^ Nat.log2 (N / (R * g)) <= N /\
    N < R * g * 2 ^ (S (Nat.log2 (N / (R * g)))) /\
    Nat.log2 (N / (R * g)) <= Nat.log2 N.
Proof.
  intros N R g HR Hg HRg.
  set (q := N / (R * g)).
  assert (Hq : 1 <= q).
  { unfold q. apply Nat.div_le_lower_bound; nia. }
  destruct (Nat.log2_spec q Hq) as [Hlo Hhi].
  assert (Hdiv1 : R * g * q <= N) by (unfold q; apply Nat.mul_div_le; nia).
  assert (Hdiv2 : N < R * g * S q).
  { unfold q. rewrite Nat.mul_succ_r.
    pose proof (Nat.div_mod N (R * g) ltac:(nia)).
    pose proof (Nat.mod_upper_bound N (R * g) ltac:(nia)). lia. }
  repeat split.
  - nia.
  - assert (S q <= 2 ^ S (Nat.log2 q)) by lia. nia.
  - apply Nat.log2_le_mono. unfold q. apply Nat.div_le_upper_bound; nia.
Qed.

Lemma sumf_single_nat : forall (c a : nat) l,
    NoDup l -> In a l -> sumf (fun j => if a =? j then c else 0) l = c.
Proof.
  intros c a l Hnd; induction Hnd as [|b l Hni Hnd IH]; intros Hin; [destruct Hin|].
  simpl. destruct (a =? b) eqn:Eab.
  - apply Nat.eqb_eq in Eab; subst b.
    rewrite (sumf_ext _ (fun _ => 0)); [rewrite sumf_const; lia|].
    intros y Hy. destruct (a =? y) eqn:E; [apply Nat.eqb_eq in E; subst; contradiction | reflexivity].
  - destruct Hin as [Eba | Hin]; [subst; rewrite Nat.eqb_refl in Eab; discriminate|].
    rewrite IH by exact Hin; lia.
Qed.

Lemma sum_by_value : forall (h g : nat -> nat) U J,
    (forall x, In x U -> h x <= J) ->
    sumf g U = sumf (fun j => sumf g (filter (fun x => h x =? j) U)) (seq 0 (S J)).
Proof.
  intros h g U J; induction U as [|x U IH]; intros HJ.
  - simpl. rewrite (sumf_const 0 (seq 1 J)); lia.
  - change (sumf g (x :: U)) with (g x + sumf g U).
    rewrite IH by (intros; apply HJ; right; assumption).
    rewrite (sumf_ext (fun j => sumf g (filter (fun y => h y =? j) (x :: U)))
                      (fun j => (if h x =? j then g x else 0)
                                + sumf g (filter (fun y => h y =? j) U))).
    + rewrite sumf_add, sumf_single_nat; [lia | apply seq_NoDup |].
      apply in_seq. pose proof (HJ x (or_introl eq_refl)). lia.
    + intros j _. simpl. destruct (h x =? j); simpl; lia.
Qed.

Lemma geo_sum1 : forall J,
    sumf (fun j => (j + 1) * 2 ^ (J - j)) (seq 0 (S J)) + J + 3 = 2 ^ (J + 2).
Proof.
  induction J as [|J IH]; [simpl; lia|].
  rewrite seq_S, sumf_app. simpl (sumf _ [0 + S J]).
  rewrite Nat.sub_diag, Nat.pow_0_r.
  rewrite (sumf_ext (fun j => (j + 1) * 2 ^ (S J - j))
             (fun j => 2 * ((j + 1) * 2 ^ (J - j)))).
  - rewrite sumf_mul_l. replace (S J + 2) with (S (J + 2)) by lia.
    rewrite Nat.pow_succ_r'. lia.
  - intros j Hj; apply in_seq in Hj.
    replace (S J - j) with (S (J - j)) by lia. rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma geo_sum0 : forall J,
    sumf (fun j => 2 ^ (J - j)) (seq 0 (S J)) + 1 = 2 ^ (J + 1).
Proof.
  induction J as [|J IH]; [simpl; lia|].
  rewrite seq_S, sumf_app. simpl (sumf _ [0 + S J]).
  rewrite Nat.sub_diag, Nat.pow_0_r.
  rewrite (sumf_ext (fun j => 2 ^ (S J - j)) (fun j => 2 * 2 ^ (J - j))).
  - rewrite sumf_mul_l. replace (S J + 1) with (S (J + 1)) by lia.
    rewrite Nat.pow_succ_r'. lia.
  - intros j Hj; apply in_seq in Hj.
    replace (S J - j) with (S (J - j)) by lia. rewrite Nat.pow_succ_r'. lia.
Qed.

Section Layers.

Variables (d s : nat) (F : Family).
Hypothesis Hvc : VCdimLe d F.
Hypothesis Hs : 2 * d + 2 <= s.
Hypothesis Hsp : Spread F (2 ^ s).

Let R := 2 ^ s.
Let N := length F.
Let dg (x : nat) := deg [x] F.

Lemma R_ge_2 : 2 <= R.
Proof.
  unfold R. pose proof (two_pow_ge s).
  assert (2 ^ 1 <= 2 ^ s) by (apply Nat.pow_le_mono_r; lia). simpl in *; lia.
Qed.

Lemma dg_spread : forall x, R * dg x <= N.
Proof.
  intros x. pose proof (Hsp (T := [x]) ltac:(constructor; [intros [] | constructor])).
  simpl in H. unfold R, dg, N. rewrite Nat.mul_1_r in H. exact H.
Qed.

Definition lay (x : nat) : nat := Nat.log2 (N / (R * dg x)).

(** The layer-size bound. *)

Lemma layer_size : forall U j,
    NoDup U ->
    (forall x, In x U -> N < R * 2 ^ (j + 1) * dg x) ->
    length U <= R * 2 ^ (j + 1) * (2 * (2 * d * (j + 1)) + 1).
Proof.
  intros U j HU Hbig.
  set (t := 2 * d * (j + 1)).
  set (Mj := R * 2 ^ (j + 1) * (2 * t + 1)).
  destruct (le_lt_dec (length U) Mj) as [Hle | Hlt]; [exact Hle|].
  exfalso.
  set (E := firstn (S Mj) U).
  assert (HElen : length E = S Mj) by (unfold E; rewrite firstn_length; lia).
  assert (HEnd : NoDup E) by (unfold E; apply NoDup_firstn, HU).
  assert (HEin : forall x, In x E -> N < R * 2 ^ (j + 1) * dg x)
    by (intros x Hx; apply Hbig, (incl_firstn (S Mj) U), Hx).
  assert (Htr : length (Traces E F) <= R ^ t).
  { eapply Nat.le_trans; [apply (@traces_count d E F HEnd Hvc)|].
    eapply Nat.le_trans; [apply Phi_le_pow|].
    rewrite HElen. replace (S Mj + 1) with (Mj + 2) by lia.
    unfold Mj, R, t. apply layer_exp; exact Hs. }
  pose proof (@trace_sum_bound E F R t HEnd Hsp R_ge_2 Htr) as Hsum.
  fold R in Hsum.
  assert (Hlow : length E * (N + 1) <= R * 2 ^ (j + 1) * sumf dg E).
  { replace (length E * (N + 1)) with (sumf (fun _ => N + 1) E)
      by (rewrite sumf_const; lia).
    rewrite <- sumf_mul_l.
    apply sumf_le. intros x Hx. specialize (HEin x Hx). lia. }
  unfold dg in Hlow. fold N in Hsum.
  rewrite HElen in Hlow.
  assert (R * 2 ^ (j + 1) * sumf (fun x => deg [x] F) E
          <= R * 2 ^ (j + 1) * ((2 * t + 1) * N)) by (apply Nat.mul_le_mono_l; exact Hsum).
  unfold Mj in *. nia.
Qed.

(** The second-moment bound. *)

Theorem sum_deg_sq_bound : forall U,
    NoDup U ->
    R * sumf (fun x => dg x * dg x) U <= (32 * d + 4) * (N * N).
Proof.
  intros U HU.
  set (U' := filter (fun x => 1 <=? dg x) U).
  assert (HU' : sumf (fun x => dg x * dg x) U = sumf (fun x => dg x * dg x) U').
  { unfold U'. rewrite sumf_filter. apply sumf_ext. intros x _.
    destruct (1 <=? dg x) eqn:E; [reflexivity|]. apply Nat.leb_gt in E.
    assert (dg x = 0) by lia. rewrite H; reflexivity. }
  rewrite HU'.
  assert (HU'nd : NoDup U') by (unfold U'; apply NoDup_filter, HU).
  assert (Hpos : forall x, In x U' -> 1 <= dg x).
  { intros x Hx; unfold U' in Hx; apply filter_In in Hx as [_ Hx].
    apply Nat.leb_le; exact Hx. }
  set (J := Nat.log2 N).
  assert (HJ : forall x, In x U' -> lay x <= J).
  { intros x Hx. apply (@layer_bounds N R (dg x) ltac:(pose proof R_ge_2; lia) (Hpos x Hx) (dg_spread x)). }
  rewrite (@sum_by_value lay (fun x => dg x * dg x) U' J HJ).
  set (Lj := fun j => filter (fun x => lay x =? j) U').
  fold Lj.
  (* one layer *)
  assert (Hlayer : forall j, j <= J ->
             R * 2 ^ j * sumf (fun x => dg x * dg x) (Lj j)
             <= 2 * (2 * (2 * d * (j + 1)) + 1) * (N * N)).
  { intros j Hj.
    assert (Hmem : forall x, In x (Lj j) ->
               R * dg x * 2 ^ j <= N /\ N < R * dg x * 2 ^ (S j)).
    { intros x Hx; unfold Lj in Hx; apply filter_In in Hx as [Hx Hl].
      apply Nat.eqb_eq in Hl.
      destruct (@layer_bounds N R (dg x) ltac:(pose proof R_ge_2; lia) (Hpos x Hx) (dg_spread x)) as [H1 [H2 _]].
      fold (lay x) in H1, H2. rewrite Hl in H1, H2. split; assumption. }
    assert (Hsz : length (Lj j) <= R * 2 ^ (j + 1) * (2 * (2 * d * (j + 1)) + 1)).
    { apply layer_size; [unfold Lj; apply NoDup_filter, HU'nd|].
      intros x Hx. destruct (Hmem x Hx) as [_ H2].
      replace (j + 1) with (S j) by lia. nia. }
    assert (Hsq : (R * 2 ^ j) * (R * 2 ^ j) * sumf (fun x => dg x * dg x) (Lj j)
                  <= length (Lj j) * (N * N)).
    { replace (length (Lj j) * (N * N)) with (sumf (fun _ => N * N) (Lj j))
        by (rewrite sumf_const; lia).
      rewrite <- sumf_mul_l.
      apply sumf_le. intros x Hx. destruct (Hmem x Hx) as [H1 _].
      assert (R * 2 ^ j * dg x <= N) by lia. nia. }
    assert (HRj : 1 <= R * 2 ^ j).
    { pose proof R_ge_2. pose proof (two_pow_ge j). nia. }
    rewrite Nat.pow_add_r in Hsz. simpl (2 ^ 1) in Hsz.
    set (X := sumf (fun x => dg x * dg x) (Lj j)) in *.
    set (Y := R * 2 ^ j) in *.
    assert (Y * (Y * X) <= Y * (2 * (2 * (2 * d * (j + 1)) + 1) * (N * N))).
    { unfold Y in *. nia. }
    apply Nat.mul_le_mono_pos_l in H; lia. }
  (* weight the layers by 2^(J-j) and sum *)
  assert (Hw : 2 ^ J * (R * sumf (fun j => sumf (fun x => dg x * dg x) (Lj j)) (seq 0 (S J)))
               <= 2 * (N * N) * sumf (fun j => (4 * d * (j + 1) + 1) * 2 ^ (J - j))
                                   (seq 0 (S J))).
  { rewrite <- !sumf_mul_l. apply sumf_le. intros j Hj. apply in_seq in Hj.
    specialize (Hlayer j ltac:(lia)).
    replace (2 ^ J) with (2 ^ (J - j) * 2 ^ j)
      by (rewrite <- Nat.pow_add_r; f_equal; lia).
    nia. }
  assert (Hg : sumf (fun j => (4 * d * (j + 1) + 1) * 2 ^ (J - j)) (seq 0 (S J))
               <= (16 * d + 2) * 2 ^ J).
  { rewrite (sumf_ext _ (fun j => 4 * d * ((j + 1) * 2 ^ (J - j)) + 2 ^ (J - j)))
      by (intros; lia).
    rewrite sumf_add, sumf_mul_l.
    pose proof (geo_sum1 J); pose proof (geo_sum0 J).
    rewrite Nat.pow_add_r in *. simpl (2 ^ 2) in *. simpl (2 ^ 1) in *. nia. }
  assert (Hpow : 1 <= 2 ^ J) by (pose proof (two_pow_ge J); lia).
  set (Z := R * sumf (fun j => sumf (fun x => dg x * dg x) (Lj j)) (seq 0 (S J))) in *.
  assert (2 ^ J * Z <= 2 ^ J * ((32 * d + 4) * (N * N))) by nia.
  apply Nat.mul_le_mono_pos_l in H; [|lia].
  unfold Z in H. rewrite <- sumf_mul_l in H. rewrite <- sumf_mul_l. exact H.
Qed.

End Layers.

(** ** Many disjoint members from few intersecting pairs — the
      replacement for Caro–Wei

    [Dm F A] counts the members of [F] meeting [A] (with multiplicity, and
    including [A] itself when [A] is nonempty); [SF F] sums it over [F],
    so it is the number of intersecting ordered pairs. Greedily take a
    member of least [Dm] and discard everything meeting it. The invariant
    [2 t SF(F) < |F|^2] survives the step with [t] lowered by one, because
    the step discards [D <= SF/|F|] members and [(N - D)^2 >= N^2 - 2ND]. *)

Definition Dm (F : Family) (A : list nat) : nat :=
  length (filter (fun B => negb (disjointb A B)) F).

Definition SF (F : Family) : nat := sumf (Dm F) F.

Lemma exists_min : forall (f : list nat -> nat) (l : list (list nat)),
    l <> [] -> exists a, In a l /\ forall b, In b l -> f a <= f b.
Proof.
  intros f l; induction l as [|a l IH]; intros Hne; [congruence|].
  destruct l as [|b l'].
  - exists a; split; [left; reflexivity|]. intros b [E|[]]; subst; lia.
  - destruct (IH ltac:(discriminate)) as [m [Hm Hmin]].
    destruct (le_lt_dec (f a) (f m)) as [Ha | Hm'].
    + exists a; split; [left; reflexivity|].
      intros c [E | Hc]; [subst; lia|]. specialize (Hmin c Hc); lia.
    + exists m; split; [right; exact Hm|].
      intros c [E | Hc]; [subst; lia|]. apply Hmin, Hc.
Qed.

Lemma length_filter_filter_le : forall {A} (p q : A -> bool) l,
    length (filter q (filter p l)) <= length (filter q l).
Proof.
  intros A p q l; induction l as [|a l IH]; simpl; [lia|].
  destruct (p a); simpl; destruct (q a); simpl; lia.
Qed.

Lemma SF_filter_le : forall p F, SF (filter p F) <= SF F.
Proof.
  intros p F; unfold SF.
  eapply Nat.le_trans.
  - apply (sumf_le _ (Dm F)). intros A _. unfold Dm. apply length_filter_filter_le.
  - apply sumf_filter_le.
Qed.

Lemma disjointb_self_nonempty : forall A, A <> [] -> disjointb A A = false.
Proof.
  intros A HA. apply disjointb_false_iff.
  destruct A as [|a A]; [congruence|]. exists a; split; left; reflexivity.
Qed.

Theorem greedy_disjoint : forall t F,
    (forall A, In A F -> A <> []) ->
    2 * t * SF F < length F * length F ->
    exists L, incl L F /\ NoDup L /\ length L = t /\ PairwiseDisjoint L.
Proof.
  induction t as [|t IH]; intros F Hne Hinv.
  - exists []; repeat split; [intros x [] | constructor | intros A B []].
  - assert (HF : F <> []) by (intro E; subst; simpl in Hinv; lia).
    destruct (@exists_min (Dm F) F HF) as [A [HA Hmin]].
    set (F' := filter (fun B => disjointb A B) F).
    set (D := Dm F A).
    assert (HNsplit : length F = length F' + D).
    { unfold F', D, Dm. rewrite (length_filter_partition (fun B => disjointb A B) F). lia. }
    assert (HND : length F * D <= SF F).
    { unfold SF. replace (length F * D) with (sumf (fun _ => D) F)
        by (rewrite sumf_const; lia).
      apply sumf_le. intros B HB. apply Hmin, HB. }
    assert (HSF' : SF F' <= SF F) by apply SF_filter_le.
    assert (Hinv' : 2 * t * SF F' < length F' * length F').
    { set (N' := length F') in *. set (S0 := SF F) in *. rewrite HNsplit in HND, Hinv.
      assert (2 * t * SF F' <= 2 * t * S0) by (apply Nat.mul_le_mono_l; exact HSF').
      nia. }
    assert (Hne' : forall B, In B F' -> B <> [])
      by (intros B HB; apply Hne; unfold F' in HB; apply filter_In in HB; tauto).
    destruct (IH F' Hne' Hinv') as [L [Hincl [Hnd [Hlen Hpd]]]].
    assert (HAL : ~ In A L).
    { intro HAL. apply Hincl in HAL. unfold F' in HAL.
      apply filter_In in HAL as [_ Hd].
      rewrite disjointb_self_nonempty in Hd; [discriminate | apply Hne, HA]. }
    assert (Hdisj : forall B, In B L -> Disjoint A B).
    { intros B HB. apply Hincl in HB. unfold F' in HB.
      apply filter_In in HB as [_ Hd]. apply disjointb_correct, Hd. }
    exists (A :: L); repeat split.
    + intros X [E | HX]; [subst; exact HA|].
      apply Hincl in HX. unfold F' in HX; apply filter_In in HX; tauto.
    + constructor; assumption.
    + simpl; lia.
    + intros X Y [EX | HX] [EY | HY] Hxy.
      * subst; congruence.
      * subst X; apply Hdisj, HY.
      * subst Y; apply Disjoint_sym, Hdisj, HX.
      * apply Hpd; assumption.
Qed.

(** [SF] is bounded by the second moment of the degrees. *)

Lemma le_sumf_in : forall {A} (f : A -> nat) x l, In x l -> f x <= sumf f l.
Proof.
  intros A f x l Hx; induction l as [|a l IH]; [destruct Hx|].
  simpl. destruct Hx as [E | Hx]; [subst; lia | specialize (IH Hx); lia].
Qed.

Lemma Dm_le_sum_deg : forall F A,
    Dm F A <= sumf (fun x => deg [x] F) A.
Proof.
  intros F A. unfold Dm. rewrite length_filter_sumf.
  eapply Nat.le_trans
    with (m := sumf (fun B => sumf (fun x => if memb x B then 1 else 0) A) F).
  - apply sumf_le. intros B _.
    destruct (disjointb A B) eqn:Ed; simpl; [lia|].
    apply disjointb_false_iff in Ed as [x [HxA HxB]].
    eapply Nat.le_trans; [|apply (le_sumf_in (fun x => if memb x B then 1 else 0) x A HxA)].
    apply memb_true_iff in HxB. rewrite HxB. lia.
  - rewrite sumf_swap. apply Nat.eq_le_incl, sumf_ext. intros x _.
    unfold deg. rewrite length_filter_sumf. apply sumf_ext. intros B _.
    unfold containsb; simpl. destruct (memb x B); reflexivity.
Qed.

Lemma SF_le_second_moment : forall F U,
    NoDup U -> (forall A, In A F -> NoDup A /\ incl A U) ->
    SF F <= sumf (fun x => deg [x] F * deg [x] F) U.
Proof.
  intros F U HU HF. unfold SF.
  eapply Nat.le_trans; [apply (sumf_le _ (fun A => sumf (fun x => deg [x] F) A));
                        intros; apply Dm_le_sum_deg|].
  rewrite (sumf_ext (fun A => sumf (fun x => deg [x] F) A)
             (fun A => sumf (fun x => if memb x A then deg [x] F else 0) U)).
  - rewrite sumf_swap. apply Nat.eq_le_incl, sumf_ext. intros x _.
    transitivity (sumf (fun A => deg [x] F * (if memb x A then 1 else 0)) F).
    + apply sumf_ext; intros A _; destruct (memb x A); lia.
    + rewrite sumf_mul_l. f_equal. unfold deg. rewrite length_filter_sumf.
      apply sumf_ext. intros A _. unfold containsb; simpl.
      destruct (memb x A); reflexivity.
  - intros A HA. destruct (HF A HA) as [HAnd HAU].
    apply sumf_sub; assumption.
Qed.

(** ** The spread lemma for bounded VC-dimension *)

Theorem vc_spread_disjoint : forall d s r m F,
    1 <= m -> Uniform m F -> VCdimLe d F ->
    Spread F (2 ^ s) -> 2 * d + 2 <= s -> (64 * d + 8) * r < 2 ^ s ->
    1 <= length F ->
    exists L, incl L F /\ NoDup L /\ length L = r /\ PairwiseDisjoint L.
Proof.
  intros d s r m F Hm HU Hvc Hsp Hs Hr HN.
  unfold Uniform in HU; rewrite Forall_forall in HU.
  apply greedy_disjoint.
  - intros A HA E; subst. destruct (HU [] HA) as [Hl _]; simpl in Hl; lia.
  - set (U := nodup Nat.eq_dec (concat F)).
    assert (HUnd : NoDup U) by apply NoDup_nodup.
    pose proof (SF_le_second_moment F HUnd) as H1.
    assert (H1' : SF F <= sumf (fun x => deg [x] F * deg [x] F) U).
    { apply H1. intros A HA. destruct (HU A HA) as [_ Hnd]. split; [exact Hnd|].
      intros x Hx. apply nodup_In, in_concat. exists A; split; assumption. }
    pose proof (@sum_deg_sq_bound d s F Hvc Hs Hsp U HUnd) as H2.
    simpl in H2.
    set (N := length F) in *. set (X := sumf _ U) in *. set (R := 2 ^ s) in *.
    assert (A1 : R * SF F <= R * X) by (apply Nat.mul_le_mono_l; exact H1').
    assert (A2 : R * SF F <= (32 * d + 4) * (N * N)) by lia.
    assert (A3 : 2 * r * (R * SF F) <= 2 * r * ((32 * d + 4) * (N * N)))
      by (apply Nat.mul_le_mono_l; exact A2).
    assert (HNN : 0 < N * N) by nia.
    assert (A4 : (64 * d + 8) * r * (N * N) < R * (N * N))
      by (apply Nat.mul_lt_mono_pos_r; [exact HNN | exact Hr]).
    destruct (le_lt_dec (N * N) (2 * r * SF F)) as [Hge | Hlt]; [exfalso | exact Hlt].
    assert (A5 : R * (N * N) <= R * (2 * r * SF F)) by (apply Nat.mul_le_mono_l; exact Hge).
    assert (E1 : R * (2 * r * SF F) = 2 * r * (R * SF F)) by ring.
    assert (E2 : 2 * r * ((32 * d + 4) * (N * N)) = (64 * d + 8) * r * (N * N)) by ring.
    lia.
Qed.

(** ** Links do not raise the VC-dimension *)

Lemma VCdimLe_link : forall d T F, VCdimLe d F -> VCdimLe d (link T F).
Proof.
  intros d T F Hvc D HD Hs. apply Hvc; [exact HD|].
  assert (HDT : forall y, In y D -> ~ In y T).
  { intros y Hy. destruct (Hs [y] ltac:(intros z [E|[]]; subst; exact Hy))
      as [A' [HA' Heq]].
    apply in_link_inv in HA' as [A [_ [_ E]]]; subst A'.
    assert (Hy' : In y (inter (setminus A T) D)) by (apply Heq; left; reflexivity).
    apply in_inter_iff in Hy' as [Hy' _]. apply in_setminus_iff in Hy'; tauto. }
  intros B HB. destruct (Hs B HB) as [A' [HA' Heq]].
  apply in_link_inv in HA' as [A [HAF [_ E]]]; subst A'.
  exists A; split; [exact HAF|].
  eapply SetEq_trans; [|exact Heq].
  split; intros x Hx; apply in_inter_iff in Hx as [Hx1 Hx2]; apply in_inter_iff;
    split; auto.
  - apply in_setminus_iff; split; [exact Hx1 | apply HDT, Hx2].
  - apply in_setminus_iff in Hx1; tauto.
Qed.

(** ** The reduction, restricted to bounded VC-dimension

    [SpreadReduction.spread_reduction] verbatim, carrying [VCdimLe d]
    through the recursion into links. *)

Definition VCUpperBound (d n k m : nat) : Prop :=
  forall F : Family,
    Uniform n F -> Distinct F -> VCdimLe d F -> length F >= m ->
    ContainsKSunflower k F.

Theorem vc_spread_reduction : forall d k r,
    2 <= k -> 1 <= r ->
    (forall m F, 1 <= m -> Uniform m F -> Distinct F -> VCdimLe d F ->
       r ^ m < length F -> RaoSpread m F r ->
       exists S, incl S F /\ NoDup S /\ length S = k /\ PairwiseDisjoint S) ->
    forall m, VCUpperBound d m k (S (r ^ m)).
Proof.
  intros d k r Hk Hr Hsyd m.
  induction m as [m IH] using lt_wf_ind.
  intros F HU HD Hvc Hsize.
  destruct m as [|m'].
  - exfalso.
    assert (H2 : 2 <= length F) by (simpl in Hsize; lia).
    destruct F as [|A [|B F'']]; simpl in H2; try lia.
    unfold Uniform in HU.
    inversion HU as [|? ? HUA HU']; subst.
    inversion HU' as [|? ? HUB HU'']; subst.
    destruct HUA as [HAlen _]; destruct HUB as [HBlen _].
    destruct A as [|a A0]; [|simpl in HAlen; lia].
    destruct B as [|b B0]; [|simpl in HBlen; lia].
    inversion HD as [|? ? Hni _]; subst.
    apply (Hni [] (or_introl eq_refl)); apply SetEq_refl.
  - destruct (rao_witness (S m') F r) as [T|] eqn:Ewit.
    + apply rao_witness_some in Ewit as [Hcand [Hne Hviol]].
      destruct (@in_cands_inv F T Hcand) as [A [HAF HTsub]].
      assert (HAnd : NoDup A).
      { unfold Uniform in HU; rewrite Forall_forall in HU.
        destruct (HU A HAF) as [_ Hnd]; exact Hnd. }
      assert (HAlen : length A = S m').
      { unfold Uniform in HU; rewrite Forall_forall in HU.
        destruct (HU A HAF) as [Hl _]; exact Hl. }
      assert (HTnd : NoDup T) by (apply (@subsets_NoDup A T HAnd HTsub)).
      assert (HTA : Subset T A) by (apply (@subsets_incl A T HTsub)).
      assert (HTlen : length T <= S m').
      { rewrite <- HAlen. apply NoDup_incl_length; assumption. }
      assert (HTpos : 1 <= length T).
      { destruct T as [|t T0]; [contradiction | simpl; lia]. }
      apply (@link_sunflower_lift T F k).
      assert (Hlt : S m' - length T < S m') by lia.
      apply (IH (S m' - length T) Hlt).
      * apply link_uniform; assumption.
      * apply link_distinct; exact HD.
      * apply VCdimLe_link; exact Hvc.
      * rewrite length_link; lia.
    + assert (HFnd : Forall (fun A : list nat => NoDup A) F).
      { unfold Uniform in HU. apply Forall_forall; intros A HA.
        rewrite Forall_forall in HU; destruct (HU A HA) as [_ Hnd]; exact Hnd. }
      assert (Hsp : RaoSpread (S m') F r)
        by (apply (@rao_witness_none (S m') F r HFnd Ewit)).
      assert (Hbig : r ^ (S m') < length F) by lia.
      destruct (Hsyd (S m') F ltac:(lia) HU HD Hvc Hbig Hsp)
        as [S0 [Hincl [Hnd0 [Hlen0 Hpd0]]]].
      exists S0; split.
      * apply SubFamilySetEq_incl; exact Hincl.
      * apply k_pairwise_disjoint_sunflower; assumption.
Qed.

(** ** The theorem *)

Definition vc_exponent (d k : nat) : nat :=
  2 * d + 3 + Nat.log2 ((64 * d + 8) * k).

Definition vc_K (d k : nat) : nat := 2 ^ vc_exponent d k.

Lemma vc_K_large : forall d k, 1 <= k ->
    2 * d + 2 <= vc_exponent d k /\ (64 * d + 8) * k < vc_K d k.
Proof.
  intros d k Hk. unfold vc_K, vc_exponent. split; [lia|].
  set (x := (64 * d + 8) * k).
  assert (Hx : 0 < x) by (unfold x; nia).
  destruct (Nat.log2_spec x Hx) as [_ Hhi].
  eapply Nat.lt_le_trans; [exact Hhi|].
  apply Nat.pow_le_mono_r; lia.
Qed.

(** **The Erdős–Rado sunflower conjecture for bounded VC-dimension.**
    Every [n]-uniform family of distinct sets with VC-dimension at most
    [d] and at least [K(d,k)^n + 1] members contains a [k]-sunflower,
    where [K(d,k) = 2^(2d + 3 + log2((64d+8)k))] does not depend on [n]. *)

Theorem vc_sunflower_bound : forall d k n,
    2 <= k -> VCUpperBound d n k (S (vc_K d k ^ n)).
Proof.
  intros d k n Hk.
  destruct (@vc_K_large d k ltac:(lia)) as [Hs Hr].
  apply vc_spread_reduction; [exact Hk | unfold vc_K; pose proof (two_pow_ge (vc_exponent d k)); lia |].
  intros m F Hm HU HD Hvc Hbig Hrao.
  assert (Hsp : Spread F (2 ^ vc_exponent d k)).
  { apply (@RaoSpread_Spread m F (vc_K d k) HU Hrao Hbig). }
  apply (@vc_spread_disjoint d (vc_exponent d k) k m F Hm HU Hvc Hsp Hs Hr).
  pose proof (two_pow_ge (vc_exponent d k * m)). rewrite Nat.pow_mul_r in *.
  unfold vc_K in Hbig. lia.
Qed.

(** The same, in the shape of [Conjecture.sunflower_conjecture]: for each
    [d] one function [c] of [k] alone. *)

Theorem vc_sunflower_conjecture : forall d,
  exists c : nat -> nat,
    forall n k, 2 <= k -> VCUpperBound d n k (S ((c k) ^ n)).
Proof.
  intros d. exists (vc_K d). intros n k Hk. apply vc_sunflower_bound, Hk.
Qed.

(** ** Audits of the statement

    The kernel checks the proof; these check that the statement says what
    it is meant to.

    - [VCdimLe] could be unsatisfiable by large families, making the
      theorem vacuous. [pointed_star_vc_one]: the pointed star [{0, i}],
      of every size, has VC-dimension at most 1 and satisfies every
      hypothesis; [kmatch_vc_one] below does the same at *every*
      uniformity, which rules out a definition that quietly caps it.
    - [VCdimLe] could hold of every family, which would make the theorem
      the full conjecture — a sure sign of a broken definition.
      [product_shatters]: the product family [prod_family t n] ([t^n]
      sets, with no 3-sunflower at [t = 2]) shatters [n] points, so its
      VC-dimension is exactly [n] ([uniform_vc_le]).
    - A clause of [Shatters] or [VCdimLe] could be decorative. The lemmas
      at the end of the file exhibit, for each clause, a family on which
      dropping it changes the answer.

    [vc_bound_coherent] is a sanity corollary, not an audit: it derives
    [(k-1)^n < K(n,k)^n + 1] from the new theorem and
    [lower_bound_exponential] together. A kernel-checked file cannot
    contain a contradictory pair, and the inequality is also plain
    arithmetic; what it checks is that the two statements compose at all. *)

Theorem uniform_vc_le : forall n F, Uniform n F -> VCdimLe n F.
Proof.
  intros n F HU D HD Hs.
  destruct (Hs D (Subset_refl D)) as [A [HA [_ HDA]]].
  unfold Uniform in HU; rewrite Forall_forall in HU.
  destruct (HU A HA) as [HAlen _]. rewrite <- HAlen.
  apply NoDup_incl_length; [exact HD|].
  intros x Hx. apply HDA in Hx. apply in_inter_iff in Hx; tauto.
Qed.

Definition pointed_star (M : nat) : Family := map (fun i => [0; S i]) (seq 0 M).

Lemma pointed_star_length : forall M, length (pointed_star M) = M.
Proof. intros M; unfold pointed_star; rewrite map_length, seq_length; reflexivity. Qed.

Lemma in_pointed_star : forall M A, In A (pointed_star M) -> exists i, A = [0; S i].
Proof.
  intros M A HA; unfold pointed_star in HA; apply in_map_iff in HA as [i [E _]].
  exists i; symmetry; exact E.
Qed.

Lemma pointed_star_Uniform : forall M, Uniform 2 (pointed_star M).
Proof.
  intros M; unfold Uniform; apply Forall_forall; intros A HA.
  destruct (in_pointed_star M A HA) as [i E]; subst.
  split; [reflexivity|]. constructor; [intros [E|[]]; discriminate | constructor; [intros [] | constructor]].
Qed.

Lemma pointed_star_Distinct : forall M, Distinct (pointed_star M).
Proof.
  intros M; unfold Distinct, pointed_star.
  assert (H : forall a, SetNoDup (map (fun i => [0; S i]) (seq a M))).
  { induction M as [|M IH]; intros a; simpl; [constructor|].
    constructor; [|apply IH].
    intros B HB [H1 H2].
    apply in_map_iff in HB as [i [E Hi]]; subst B. apply in_seq in Hi.
    assert (Hin : In (S i) [0; S a]) by (apply H2; right; left; reflexivity).
    destruct Hin as [E|[E|[]]]; [discriminate | injection E; lia]. }
  apply H.
Qed.

Theorem pointed_star_vc_one : forall M, VCdimLe 1 (pointed_star M).
Proof.
  intros M D HD Hs.
  destruct D as [|a [|b D']]; simpl; [lia | lia|]. exfalso.
  inversion HD as [|? ? Hab HD']; subst.
  destruct (in_dec Nat.eq_dec 0 (a :: b :: D')) as [H0 | H0].
  - destruct (Hs [] (Subset_nil _)) as [A [HA Heq]].
    destruct (in_pointed_star M A HA) as [i E]; subst A.
    assert (In 0 (inter [0; S i] (a :: b :: D'))) by (apply in_inter_iff; split; [left|]; auto).
    apply Heq in H; destruct H.
  - destruct (Hs [a; b] ltac:(intros x [E|[E|[]]]; subst; simpl; auto)) as [A [HA Heq]].
    destruct (in_pointed_star M A HA) as [i E]; subst A.
    assert (Ha : In a (inter [0; S i] (a :: b :: D'))) by (apply Heq; left; reflexivity).
    assert (Hb : In b (inter [0; S i] (a :: b :: D'))) by (apply Heq; right; left; reflexivity).
    apply in_inter_iff in Ha as [Ha _]; apply in_inter_iff in Hb as [Hb _].
    destruct Ha as [Ea|[Ea|[]]]; [subst; apply H0; left; reflexivity|].
    destruct Hb as [Eb|[Eb|[]]]; [subst; apply H0; right; left; reflexivity|].
    apply Hab; left; congruence.
Qed.

(** Every hypothesis of [vc_sunflower_bound], at every size. *)

Corollary vc_hypotheses_satisfiable : forall M,
    Uniform 2 (pointed_star M) /\ Distinct (pointed_star M) /\ VCdimLe 1 (pointed_star M) /\ length (pointed_star M) = M.
Proof.
  intros M; repeat split;
    [apply pointed_star_Uniform | apply pointed_star_Distinct | apply pointed_star_vc_one | apply pointed_star_length].
Qed.

Definition shatter_grid (t n : nat) : list nat := map (fun i => i * t) (seq 0 n).

Lemma shatter_grid_S : forall t n, shatter_grid t (S n) = shatter_grid t n ++ [n * t].
Proof. intros t n; unfold shatter_grid; rewrite seq_S, map_app; reflexivity. Qed.

Lemma shatter_grid_NoDup : forall t n, 1 <= t -> NoDup (shatter_grid t n).
Proof.
  intros t n Ht; unfold shatter_grid. apply NoDup_map_inj_on_list; [apply seq_NoDup|].
  intros x y _ _ E. nia.
Qed.

Lemma in_shatter_grid : forall t n x, In x (shatter_grid t n) <-> exists i, i < n /\ x = i * t.
Proof.
  intros t n x; unfold shatter_grid; rewrite in_map_iff; split.
  - intros [i [E Hi]]; apply in_seq in Hi; exists i; split; [lia | symmetry; exact E].
  - intros [i [Hi E]]; exists i; split; [symmetry; exact E | apply in_seq; lia].
Qed.

Theorem product_shatters : forall t n,
    2 <= t -> Shatters (prod_family t n) (shatter_grid t n).
Proof.
  intros t n Ht. induction n as [|n IH]; intros B HB.
  - exists []; split; [left; reflexivity|].
    split; intros x Hx; [apply in_inter_iff in Hx as [[] _] | apply HB in Hx; destruct Hx].
  - assert (HB' : Subset (rem_elt (n * t) B) (shatter_grid t n)).
    { intros x Hx; apply in_rem_iff in Hx as [Hx Hne].
      apply HB in Hx. rewrite shatter_grid_S in Hx. apply in_app_or in Hx as [Hx|[E|[]]];
        [exact Hx | congruence]. }
    destruct (IH _ HB') as [A [HA Heq]].
    set (j := if in_dec Nat.eq_dec (n * t) B then 0 else 1).
    exists ((n * t + j) :: A). split.
    + apply in_prod_family_S. exists j, A. repeat split; [unfold j; destruct (in_dec _ _ _); lia | exact HA].
    + assert (HAlt : forall y, In y A -> y < n * t)
        by (intros y Hy; apply (prod_family_bounded t n A y HA Hy)).
      rewrite shatter_grid_S.
      split; intros x Hx.
      * apply in_inter_iff in Hx as [Hx1 Hx2]. apply in_app_or in Hx2 as [Hx2 | [E|[]]].
        -- destruct Hx1 as [E | Hx1].
           ++ exfalso. rewrite <- E in Hx2. apply in_shatter_grid in Hx2 as [i [Hi Ei]].
              unfold j in Ei; destruct (in_dec _ _ _); nia.
           ++ assert (In x (inter A (shatter_grid t n))) by (apply in_inter_iff; auto).
              apply Heq in H. apply in_rem_iff in H; tauto.
        -- subst x. destruct Hx1 as [E | Hx1].
           ++ unfold j in E; destruct (in_dec Nat.eq_dec (n * t) B); [exact i | lia].
           ++ specialize (HAlt _ Hx1); lia.
      * apply in_inter_iff. destruct (Nat.eq_dec x (n * t)) as [Ex | Hne].
        -- subst x. split; [left; unfold j; destruct (in_dec _ _ _); [lia | contradiction]|].
           apply in_or_app; right; left; reflexivity.
        -- assert (In x (rem_elt (n * t) B)) by (apply in_rem_iff; auto).
           apply Heq in H. apply in_inter_iff in H as [H1 H2].
           split; [right; exact H1 | apply in_or_app; left; exact H2].
Qed.

(** So the product family's VC-dimension is exactly its uniformity, and no
    fixed [d] covers it once [n > d]. *)

Corollary product_vc_full : forall t n d,
    2 <= t -> d < n -> ~ VCdimLe d (prod_family t n).
Proof.
  intros t n d Ht Hdn Hvc.
  pose proof (Hvc (shatter_grid t n) (@shatter_grid_NoDup t n ltac:(lia)) (@product_shatters t n Ht)).
  unfold shatter_grid in H; rewrite map_length, seq_length in H; lia.
Qed.

(** The new upper bound and [ProductLowerBound]'s lower bound, composed
    on the same family (a sanity corollary; see the section header). *)

Theorem vc_bound_coherent : forall n k,
    1 <= n -> 2 <= k -> (k - 1) ^ n < S (vc_K n k ^ n).
Proof.
  intros n k Hn Hk.
  destruct (le_lt_dec (S (vc_K n k ^ n)) ((k - 1) ^ n)) as [Hge | Hlt]; [exfalso | exact Hlt].
  destruct (lower_bound_exponential n k Hn Hk) as [F [HU [HD [Hlen Hno]]]].
  apply Hno. apply (@vc_sunflower_bound n k n Hk F HU HD (@uniform_vc_le n F HU)). lia.
Qed.

(** *** A class member at every uniformity, and every clause of the
        definition load-bearing

    [pointed_star] has uniformity 2 only, so it cannot rule out a
    definition that quietly caps the uniformity. [kmatch k M] — a common
    kernel [{0..k-1}] plus the pairs [{k+2i, k+2i+1}] — has uniformity
    [k + 2] for every [k], [M] members, and VC-dimension at most 1. Its
    VC bound needs *all four* traces of a two-point set, so it also fails
    for a definition that tests shattering only on [B = []] and [B = D]
    (the pair [{k, k+1}] has exactly those two traces). *)

Definition kmatch (k M : nat) : Family :=
  map (fun i => seq 0 k ++ [k + 2 * i; k + 2 * i + 1]) (seq 0 M).

Lemma in_kmatch : forall k M A, In A (kmatch k M) ->
    exists i, i < M /\ A = seq 0 k ++ [k + 2 * i; k + 2 * i + 1].
Proof.
  intros k M A HA; unfold kmatch in HA; apply in_map_iff in HA as [i [E Hi]].
  apply in_seq in Hi. exists i; split; [lia | symmetry; exact E].
Qed.

Lemma in_kmember : forall k i x,
    In x (seq 0 k ++ [k + 2 * i; k + 2 * i + 1]) <->
    x < k \/ x = k + 2 * i \/ x = k + 2 * i + 1.
Proof.
  intros k i x; rewrite in_app_iff, in_seq; simpl; split.
  - intros [H | [H | [H | []]]]; lia.
  - intros [H | [H | H]]; [left; lia | right; left; lia | right; right; left; lia].
Qed.

Lemma kmatch_length : forall k M, length (kmatch k M) = M.
Proof. intros; unfold kmatch; rewrite map_length, seq_length; reflexivity. Qed.

Lemma kmatch_Uniform : forall k M, Uniform (k + 2) (kmatch k M).
Proof.
  intros k M; unfold Uniform; apply Forall_forall; intros A HA.
  destruct (in_kmatch k M A HA) as [i [_ E]]; subst A. split.
  - rewrite app_length, seq_length; reflexivity.
  - apply NoDup_app_disj; [apply seq_NoDup | |].
    + constructor; [intros [E|[]]; lia | constructor; [intros [] | constructor]].
    + intros x Hx1 Hx2. apply in_seq in Hx1. destruct Hx2 as [E|[E|[]]]; lia.
Qed.

Lemma kmatch_Distinct : forall k M, Distinct (kmatch k M).
Proof.
  intros k M; unfold Distinct, kmatch.
  assert (H : forall a, SetNoDup (map (fun i => seq 0 k ++ [k + 2 * i; k + 2 * i + 1])
                                      (seq a M))).
  { induction M as [|M IH]; intros a; simpl; [constructor|].
    constructor; [|apply IH].
    intros B HB [H1 H2]. apply in_map_iff in HB as [i [E Hi]]; subst B.
    apply in_seq in Hi.
    assert (Hin : In (k + 2 * i) (seq 0 k ++ [k + 2 * a; k + 2 * a + 1]))
      by (apply H2, in_kmember; right; left; reflexivity).
    apply in_kmember in Hin; lia. }
  apply H.
Qed.

Theorem kmatch_vc_one : forall k M, VCdimLe 1 (kmatch k M).
Proof.
  intros k M D HD Hs.
  destruct D as [|a [|b D']]; simpl; [lia | lia|]. exfalso.
  inversion HD as [|? ? Hab _]; subst.
  (* a kernel point cannot be missed, so neither [a] nor [b] is one *)
  assert (Hker : forall y, In y (a :: b :: D') -> k <= y).
  { intros y Hy. destruct (le_lt_dec k y) as [Hle | Hlt]; [exact Hle|].
    destruct (Hs [] (Subset_nil _)) as [A [HA Heq]].
    destruct (in_kmatch k M A HA) as [i [_ E]]; subst A.
    assert (In y (inter (seq 0 k ++ [k + 2 * i; k + 2 * i + 1]) (a :: b :: D')))
      by (apply in_inter_iff; split; [apply in_kmember; left; exact Hlt | exact Hy]).
    apply Heq in H; destruct H. }
  assert (Ha : k <= a) by (apply Hker; left; reflexivity).
  assert (Hb : k <= b) by (apply Hker; right; left; reflexivity).
  (* some member contains both, and some member contains [a] but not [b] *)
  destruct (Hs [a; b] ltac:(intros x [E|[E|[]]]; subst; simpl; auto)) as [A1 [HA1 Heq1]].
  destruct (in_kmatch k M A1 HA1) as [i [_ E1]]; subst A1.
  destruct (Hs [a] ltac:(intros x [E|[]]; subst; simpl; auto)) as [A2 [HA2 Heq2]].
  destruct (in_kmatch k M A2 HA2) as [j [_ E2]]; subst A2.
  assert (Ha1 : In a (inter (seq 0 k ++ [k + 2 * i; k + 2 * i + 1]) (a :: b :: D')))
    by (apply Heq1; left; reflexivity).
  assert (Hb1 : In b (inter (seq 0 k ++ [k + 2 * i; k + 2 * i + 1]) (a :: b :: D')))
    by (apply Heq1; right; left; reflexivity).
  assert (Ha2 : In a (inter (seq 0 k ++ [k + 2 * j; k + 2 * j + 1]) (a :: b :: D')))
    by (apply Heq2; left; reflexivity).
  apply in_inter_iff in Ha1 as [Ha1 _]; apply in_inter_iff in Hb1 as [Hb1 _].
  apply in_inter_iff in Ha2 as [Ha2 _].
  apply in_kmember in Ha1; apply in_kmember in Hb1; apply in_kmember in Ha2.
  assert (Hij : i = j) by lia. subst j.
  assert (Hb2 : In b (inter (seq 0 k ++ [k + 2 * i; k + 2 * i + 1]) (a :: b :: D'))).
  { apply in_inter_iff; split; [apply in_kmember; lia | right; left; reflexivity]. }
  apply Heq2 in Hb2. destruct Hb2 as [E|[]]. apply Hab; left; symmetry; exact E.
Qed.

Corollary vc_hypotheses_satisfiable_at_every_uniformity : forall n M, 2 <= n ->
    Uniform n (kmatch (n - 2) M) /\ Distinct (kmatch (n - 2) M) /\
    VCdimLe 1 (kmatch (n - 2) M) /\ length (kmatch (n - 2) M) = M.
Proof.
  intros n M Hn. replace n with (n - 2 + 2) at 1 by lia.
  repeat split; [apply kmatch_Uniform | apply kmatch_Distinct | apply kmatch_vc_one |
                 apply kmatch_length].
Qed.

(** Each clause of [Shatters]/[VCdimLe] is load-bearing, shown by a family
    on which dropping the clause changes the answer. These are semantic
    witnesses, independent of any proof script. *)

(** Only [B = []] and [B = D] tested: [{k, k+1}] passes, so the weakened
    VC bound of [kmatch] would be at least 2, against [kmatch_vc_one]. *)
Lemma two_trace_test_is_weaker : forall k,
    (exists A, In A (kmatch k 2) /\ SetEq (inter A [k; k + 1]) []) /\
    (exists A, In A (kmatch k 2) /\ SetEq (inter A [k; k + 1]) [k; k + 1]) /\
    ~ Shatters (kmatch k 2) [k; k + 1].
Proof.
  intros k. repeat split.
  - exists (seq 0 k ++ [k + 2 * 1; k + 2 * 1 + 1]). split.
    + unfold kmatch; simpl; right; left; reflexivity.
    + split; intros x Hx; [|destruct Hx].
      apply in_inter_iff in Hx as [H1 H2]. apply in_kmember in H1.
      destruct H2 as [E|[E|[]]]; lia.
  - exists (seq 0 k ++ [k + 2 * 0; k + 2 * 0 + 1]). split.
    + unfold kmatch; simpl; left; reflexivity.
    + split; intros x Hx.
      * apply in_inter_iff in Hx as [_ H2]; exact H2.
      * apply in_inter_iff; split; [apply in_kmember; destruct Hx as [E|[E|[]]]; lia | exact Hx].
  - intros Hs. pose proof (@kmatch_vc_one k 2 [k; k + 1]
                             ltac:(constructor; [intros [E|[]]; lia | constructor; [intros []|constructor]]) Hs).
    simpl in H; lia.
Qed.

(** Without [NoDup D], the set [{1}] shattered by [pointed_star 2] counts
    twice as [[1; 1]]. *)
Lemma nodup_clause_is_needed :
    Shatters (pointed_star 2) [1; 1] /\ ~ NoDup [1; 1] /\ VCdimLe 1 (pointed_star 2).
Proof.
  repeat split; [| intros H; inversion H as [|? ? Hn _]; apply Hn; left; reflexivity
                 | apply pointed_star_vc_one].
  intros B HB.
  destruct (in_dec Nat.eq_dec 1 B) as [H1 | H1].
  - exists [0; 1]; split; [unfold pointed_star; simpl; left; reflexivity|].
    split; intros x Hx.
    + apply in_inter_iff in Hx as [_ H2]. destruct H2 as [E|[E|[]]]; subst; exact H1.
    + pose proof (HB x Hx). apply in_inter_iff; split; destruct H as [E|[E|[]]]; subst; simpl; auto.
  - exists [0; 2]; split; [unfold pointed_star; simpl; right; left; reflexivity|].
    split; intros x Hx.
    + apply in_inter_iff in Hx as [H2 H3]. destruct H3 as [E|[E|[]]]; subst;
        destruct H2 as [E|[E|[]]]; discriminate.
    + exfalso. pose proof (HB x Hx). destruct H as [E|[E|[]]]; subst; contradiction.
Qed.

(** Only [A ∩ D ⊆ B] required: any member with an empty trace meets every
    [B], so fresh points [{5, 6}] would count as shattered. *)
Lemma trace_in_B_only_is_weaker :
    (forall B, Subset B [5; 6] ->
       exists A, In A (pointed_star 1) /\ Subset (inter A [5; 6]) B) /\
    ~ Shatters (pointed_star 1) [5; 6].
Proof.
  split.
  - intros B _. exists [0; 1]; split; [left; reflexivity|].
    intros x Hx. apply in_inter_iff in Hx as [H1 H2].
    destruct H1 as [E|[E|[]]]; subst; destruct H2 as [E|[E|[]]]; discriminate.
  - intros Hs. destruct (Hs [5] ltac:(intros x [E|[]]; subst; left; reflexivity))
      as [A [HA Heq]].
    unfold pointed_star in HA; simpl in HA. destruct HA as [E|[]]; subst A.
    assert (In 5 (inter [0; 1] [5; 6])) by (apply Heq; left; reflexivity).
    apply in_inter_iff in H as [[E|[E|[]]] _]; discriminate.
Qed.

(** Only [B ⊆ A ∩ D] required: the single member [{0,1}] contains every
    subset of [{0,1}], so [{0,1}] would count as shattered by one set. *)
Lemma B_in_trace_only_is_weaker :
    (forall B, Subset B [0; 1] ->
       exists A, In A (pointed_star 1) /\ Subset B (inter A [0; 1])) /\
    ~ Shatters (pointed_star 1) [0; 1].
Proof.
  split.
  - intros B HB. exists [0; 1]; split; [left; reflexivity|].
    intros x Hx. apply in_inter_iff; split; apply HB, Hx.
  - intros Hs. pose proof (@pointed_star_vc_one 1 [0; 1]
                             ltac:(constructor; [intros [E|[]]; discriminate | constructor; [intros []|constructor]]) Hs).
    simpl in H; lia.
Qed.
