(** * The link linear program of the descent, with kernel-checked certificates

    [docs/roadmap.md] §64 bounds a 4-uniform 3-sunflower-free family [F]
    by a linear program over the traces of its members on the point set
    [V] of a largest link [D = D(R)].  §64–§65 certify the LP for every
    link class of size 23–27 with exact rational dual certificates checked
    by a Python program.  This module moves the whole argument into the
    kernel:

    - the three constraint families (a), (b), (c) of §64 are proved as
      theorems about any such [F];
    - weak duality is proved for an integer dual certificate (a rational
      certificate scaled by a common denominator [cK]);
    - [certcheck] decides the certificate by computation on the link, so
      a concrete class is discharged by [vm_compute].

    The main theorem [link_lp_bound] assumes [IotaAtMost 4 27] (the
    validated [ι(4) ≤ 27]) and the choice of [R] as a member with a
    largest link, and concludes [|F| ≤ 54] from [certcheck = true].
    Nothing about the ground set is assumed. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Sunflower Require Import Sets Sunflower Intersecting IotaRate Spread
  Counting LowerBound PureLink Product Stability4 LinkCombine.

(** ** Sums over lists *)

Definition suml (l : list nat) : nat := fold_right Nat.add 0 l.

Lemma suml_app : forall a b, suml (a ++ b) = suml a + suml b.
Proof. intros a b; unfold suml; rewrite fold_right_app. induction a; simpl; lia. Qed.

Lemma suml_map_add :
  forall {X} (f g : X -> nat) (L : list X),
    suml (map (fun x => f x + g x) L) = suml (map f L) + suml (map g L).
Proof. intros X f g L; induction L; simpl; unfold suml in *; simpl; lia. Qed.

Lemma suml_map_mul_l :
  forall {X} (c : nat) (f : X -> nat) (L : list X),
    suml (map (fun x => c * f x) L) = c * suml (map f L).
Proof. intros X c f L; induction L; simpl; unfold suml in *; simpl; lia. Qed.

Lemma suml_map_le :
  forall {X} (f g : X -> nat) (L : list X),
    (forall x, In x L -> f x <= g x) ->
    suml (map f L) <= suml (map g L).
Proof.
  intros X f g L H; induction L as [| x L IH]; simpl; [lia |].
  unfold suml in *; simpl.
  pose proof (H x (or_introl eq_refl)).
  assert (IH' := IH (fun y Hy => H y (or_intror Hy))). lia.
Qed.

Lemma suml_map_ext :
  forall {X} (f g : X -> nat) (L : list X),
    (forall x, In x L -> f x = g x) -> suml (map f L) = suml (map g L).
Proof.
  intros X f g L H; induction L as [| x L IH]; simpl; [reflexivity |].
  unfold suml in *; simpl. rewrite (H x (or_introl eq_refl)).
  rewrite (IH (fun y Hy => H y (or_intror Hy))). reflexivity.
Qed.

(** Exchange of a double sum. *)
Lemma suml_cons : forall a l, suml (a :: l) = a + suml l.
Proof. reflexivity. Qed.

Lemma suml_exchange :
  forall {X Y} (g : X -> Y -> nat) (L1 : list X) (L2 : list Y),
    suml (map (fun x => suml (map (fun y => g x y) L2)) L1)
    = suml (map (fun y => suml (map (fun x => g x y) L1)) L2).
Proof.
  intros X Y g L1; induction L1 as [| x L1 IH]; intros L2.
  - unfold suml; simpl; induction L2 as [| y L2 IH2]; simpl; [reflexivity | exact IH2].
  - cbn [map]. rewrite suml_cons, IH.
    rewrite <- (suml_map_add (fun y => g x y) (fun y => suml (map (fun x0 => g x0 y) L1)) L2).
    apply suml_map_ext; intros y _; cbn [map]; rewrite suml_cons; reflexivity.
Qed.

(** A sum over a filtered list equals the sum over the whole list when the
    discarded terms are zero. *)
Lemma suml_map_filter_zero :
  forall {X} (p : X -> bool) (f : X -> nat) (L : list X),
    (forall x, In x L -> p x = false -> f x = 0) ->
    suml (map f (filter p L)) = suml (map f L).
Proof.
  intros X p f L H; induction L as [| x L IH]; simpl; [reflexivity |].
  destruct (p x) eqn:E.
  - unfold suml in *; simpl. rewrite IH; [reflexivity | intros y Hy; apply H; right; exact Hy].
  - unfold suml in *; simpl. rewrite (H x (or_introl eq_refl) E).
    rewrite IH; [lia | intros y Hy; apply H; right; exact Hy].
Qed.

(** ** Counting by key

    [length L = Σ_{k ∈ keys} #{x ∈ L : f x = k}] when the keys are
    distinct and cover the image of [f] on [L]; weighted version. *)

Section Keys.
  Context {X K : Type} (eqd : forall a b : K, {a = b} + {a <> b}) (f : X -> K).

  Definition keyb (k : K) (x : X) : bool := if eqd (f x) k then true else false.

  Lemma indicator_sum_zero :
    forall (keys : list K) (x : X) (g : K -> nat),
      ~ In (f x) keys ->
      suml (map (fun k => g k * (if eqd (f x) k then 1 else 0)) keys) = 0.
  Proof.
    intros keys x g; induction keys as [| k keys IH]; intros Hnin; cbn [map]; [reflexivity |].
    rewrite suml_cons. destruct (eqd (f x) k) as [E | NE].
    - exfalso; apply Hnin; left; symmetry; exact E.
    - rewrite IH; [lia | intro H; apply Hnin; right; exact H].
  Qed.

  Lemma indicator_sum_one :
    forall (keys : list K) (x : X) (g : K -> nat),
      NoDup keys -> In (f x) keys ->
      suml (map (fun k => g k * (if eqd (f x) k then 1 else 0)) keys) = g (f x).
  Proof.
    intros keys x g Hnd Hin; induction keys as [| k keys IH]; cbn [map]; [inversion Hin |].
    inversion Hnd as [| ? ? Hnk Hnd']; subst.
    rewrite suml_cons.
    destruct (eqd (f x) k) as [E | NE].
    - subst k. rewrite (indicator_sum_zero keys x g Hnk). lia.
    - destruct Hin as [E | Hin]; [subst; exfalso; apply NE; reflexivity |].
      rewrite (IH Hnd' Hin); lia.
  Qed.

  Lemma count_keyb_cons :
    forall (k : K) (x : X) (L : list X),
      count (keyb k) (x :: L) = (if eqd (f x) k then 1 else 0) + count (keyb k) L.
  Proof.
    intros k x L; unfold count, keyb; simpl; destruct (eqd (f x) k); reflexivity.
  Qed.

  Lemma count_by_keys_weighted :
    forall (keys : list K) (g : K -> nat) (L : list X),
      NoDup keys -> (forall x, In x L -> In (f x) keys) ->
      suml (map (fun k => g k * count (keyb k) L) keys) = suml (map (fun x => g (f x)) L).
  Proof.
    intros keys g L Hnd Hcov; induction L as [| x L IH].
    - cbn [map]. rewrite (suml_map_ext (fun k => g k * count (keyb k) []) (fun _ => 0))
        by (intros; unfold count; simpl; lia).
      clear; induction keys; cbn [map]; [reflexivity | rewrite suml_cons; assumption].
    - cbn [map]. rewrite suml_cons.
      rewrite <- (IH (fun y Hy => Hcov y (or_intror Hy))).
      rewrite <- (indicator_sum_one keys x g Hnd (Hcov x (or_introl eq_refl))).
      rewrite <- suml_map_add.
      apply suml_map_ext; intros k _. rewrite count_keyb_cons. lia.
  Qed.

  Lemma count_by_keys :
    forall (keys : list K) (L : list X),
      NoDup keys -> (forall x, In x L -> In (f x) keys) ->
      suml (map (fun k => count (keyb k) L) keys) = length L.
  Proof.
    intros keys L Hnd Hcov.
    pose proof (count_by_keys_weighted keys (fun _ => 1) L Hnd Hcov) as H.
    rewrite (suml_map_ext (fun k => 1 * count (keyb k) L) (fun k => count (keyb k) L)) in H
      by (intros; lia).
    rewrite H. clear. induction L; cbn [map]; [reflexivity | rewrite suml_cons; simpl; lia].
  Qed.
End Keys.

(** ** The objects *)

Definition points (D : Family) : list nat := nodup Nat.eq_dec (concat D).

(** The canonical trace of [S] on [V]: the sublist of [V] lying in [S]. *)
Definition tr (V S : list nat) : list nat := filter (fun x => memb x S) V.

(** Fast boolean set primitives.  [Sets.memb], and everything built on it
    ([inter], [seteqb], [disjointb]), goes through [in_dec] and is two orders
    of magnitude slower under [vm_compute]; the certificate check is pure
    computation, so it uses [Nat.eqb]-based versions, each proved
    equivalent. *)
Definition membf (x : nat) (A : list nat) : bool := existsb (Nat.eqb x) A.

Lemma membf_true_iff : forall x A, membf x A = true <-> In x A.
Proof.
  intros x A; unfold membf; rewrite existsb_exists; split.
  - intros [y [Hy E]]; apply Nat.eqb_eq in E; subst; exact Hy.
  - intros H; exists x; split; [exact H | apply Nat.eqb_refl].
Qed.

Definition disjf (A B : list nat) : bool := forallb (fun x => negb (membf x B)) A.

Lemma disjf_correct : forall A B, disjf A B = true <-> Disjoint A B.
Proof.
  intros A B; unfold disjf, Disjoint; rewrite forallb_forall; split.
  - intros H x HA HB; specialize (H x HA); apply negb_true_iff in H.
    apply membf_true_iff in HB; rewrite HB in H; discriminate.
  - intros H x HA; apply negb_true_iff.
    destruct (membf x B) eqn:E; [exfalso; apply membf_true_iff in E; exact (H x HA E) | reflexivity].
Qed.

Lemma disjf_nil_l : forall C, disjf [] C = true.
Proof. intro C; apply disjf_correct; apply Disjoint_nil_l. Qed.

Definition interb (A B : list nat) : list nat := filter (fun x => membf x B) A.

Lemma in_interb : forall A B x, In x (interb A B) <-> In x A /\ In x B.
Proof. intros; unfold interb; rewrite filter_In, membf_true_iff; tauto. Qed.

Definition seteqf (A B : list nat) : bool :=
  forallb (fun x => membf x B) A && forallb (fun x => membf x A) B.

Lemma seteqf_correct : forall A B, seteqf A B = true <-> SetEq A B.
Proof.
  intros A B; unfold seteqf, SetEq, Subset; rewrite andb_true_iff, forallb_forall, forallb_forall.
  split; intros [H1 H2]; split; intros x Hx.
  - apply membf_true_iff; apply H1; exact Hx.
  - apply membf_true_iff; apply H2; exact Hx.
  - apply membf_true_iff; apply H1; exact Hx.
  - apply membf_true_iff; apply H2; exact Hx.
Qed.

Lemma interb_SetEq_inter : forall A B, SetEq (interb A B) (inter A B).
Proof.
  intros A B; split; intros x H; [apply in_interb in H; apply in_inter_iff; exact H
                                 | apply in_inter_iff in H; apply in_interb; exact H].
Qed.

Definition witnessedb (T : list nat) (D : Family) : bool :=
  existsb (fun C1 =>
    existsb (fun C2 =>
      negb (seteqf C1 C2)
      && seteqf (interb T C1) (interb C1 C2)
      && seteqf (interb T C2) (interb C1 C2)) D) D.

(** Sublists of [l] with at most [k] elements, in the order of [Spread.subsets]
    but without generating the long ones. *)
Fixpoint subs_le (k : nat) (l : list nat) : list (list nat) :=
  match l with
  | [] => [[]]
  | x :: l' =>
      (match k with 0 => [] | S k' => map (cons x) (subs_le k' l') end) ++ subs_le k l'
  end.

Lemma subs_le_length : forall k l T, In T (subs_le k l) -> length T <= k.
Proof.
  intros k l; revert k; induction l as [| x l IH]; intros k T HT; simpl in HT.
  - destruct HT as [E | []]; subst; simpl; lia.
  - apply in_app_iff in HT as [HT | HT]; [| apply IH; exact HT].
    destruct k as [| k']; [inversion HT |].
    apply in_map_iff in HT as [T' [E HT']]; subst; simpl.
    apply le_n_S; apply IH; exact HT'.
Qed.

Lemma subs_le_Subset : forall k l T, In T (subs_le k l) -> Subset T l.
Proof.
  intros k l; revert k; induction l as [| x l IH]; intros k T HT; simpl in HT.
  - destruct HT as [E | []]; subst; apply Subset_nil.
  - apply in_app_iff in HT as [HT | HT].
    + destruct k as [| k']; [inversion HT |].
      apply in_map_iff in HT as [T' [E HT']]; subst.
      intros y [Hy | Hy]; [left; exact Hy | right; apply (IH k' T' HT'); exact Hy].
    + intros y Hy; right; apply (IH k T HT); exact Hy.
Qed.

Lemma filter_in_subs_le :
  forall (p : nat -> bool) (l : list nat) k,
    length (filter p l) <= k -> In (filter p l) (subs_le k l).
Proof.
  intros p l; induction l as [| x l IH]; intros k Hk; simpl in *.
  - left; reflexivity.
  - destruct (p x) eqn:E.
    + simpl in Hk. destruct k as [| k']; [lia |].
      apply in_app_iff; left; apply in_map; apply IH; lia.
    + apply in_app_iff; right; apply IH; exact Hk.
Qed.

Lemma subs_le_NoDup : forall k l, NoDup l -> NoDup (subs_le k l).
Proof.
  intros k l; revert k; induction l as [| x l IH]; intros k Hnd; simpl.
  - constructor; [intros [] | constructor].
  - inversion Hnd as [| ? ? Hnx Hnd']; subst.
    apply NoDup_app_disjoint.
    + destruct k as [| k']; [constructor |].
      apply NoDup_map_inj; [intros a b _ _ E; injection E; auto | apply IH; exact Hnd'].
    + apply IH; exact Hnd'.
    + intros T H1 H2. destruct k as [| k']; [inversion H1 |].
      apply in_map_iff in H1 as [T' [E _]]; subst.
      apply subs_le_Subset in H2. apply Hnx; apply H2; left; reflexivity.
Qed.

Definition traces (V : list nat) : list (list nat) :=
  filter (fun T => 1 <=? length T) (subs_le 3 V).

Definition unwit (D : Family) : list (list nat) :=
  filter (fun T => negb (witnessedb T D)) (traces (points D)).

Definition cap (T : list nat) : nat :=
  match length T with 1 => 26 | 2 => 6 | _ => 2 end.

(** An integer dual certificate: multipliers [cy] keyed by member of the
    link, [cz] keyed by trace, [cw], all scaled by [cK].  Keys are looked
    up by set equality, so the check depends on the link only as a family
    of sets (see [certcheck_transfer]). *)
Record cert := mkcert { cK : nat; cy : list (list nat * nat); cz : list (list nat * nat); cw : nat }.

Definition lookup (tab : list (list nat * nat)) (T : list nat) : nat :=
  match find (fun p => seteqf (fst p) T) tab with
  | Some p => snd p
  | None => 0
  end.

Definition yval (c : cert) (C : list nat) : nat := lookup (cy c) C.
Definition zval (c : cert) (T : list nat) : nat := lookup (cz c) T.

Definition ysum (D : Family) (c : cert) (p : list nat -> bool) : nat :=
  suml (map (fun C => if p C then yval c C else 0) D).

Definition certcheck (D : Family) (c : cert) (bound : nat) : bool :=
  let B := unwit D in
  (1 <=? cK c)
  && (cK c <=? ysum D c (fun _ => true) + cw c)
  && forallb (fun T => cK c <=? ysum D c (fun C => disjf T C) + zval c T) B
  && (length D * ysum D c (fun _ => true)
      + suml (map (fun T => cap T * zval c T) B)
      + 27 * cw c <=? cK c * bound).

(** ** Basic facts about links, meetings and traces *)

Lemma in_DisjointFrom :
  forall R F C, In C (DisjointFrom R F) <-> In C F /\ Disjoint R C.
Proof.
  intros R F C; unfold DisjointFrom; rewrite filter_In, disjointb_correct; tauto.
Qed.

Lemma in_Meeting :
  forall R F S, In S (Meeting R F) <-> In S F /\ ~ Disjoint R S.
Proof.
  intros R F S; unfold Meeting; rewrite filter_In.
  split.
  - intros [H1 H2]; split; [exact H1 |].
    intro Hd; apply disjointb_correct in Hd; rewrite Hd in H2; discriminate.
  - intros [H1 H2]; split; [exact H1 |].
    destruct (disjointb R S) eqn:E; [| reflexivity].
    exfalso; apply H2; apply disjointb_correct; exact E.
Qed.

Lemma in_points :
  forall D x, In x (points D) <-> exists C, In C D /\ In x C.
Proof.
  intros D x; unfold points; rewrite nodup_In, in_concat.
  split; intros [C [H1 H2]]; exists C; tauto.
Qed.

Lemma points_NoDup : forall D, NoDup (points D).
Proof. intro D; apply NoDup_nodup. Qed.

Lemma member_Subset_points : forall D C, In C D -> Subset C (points D).
Proof. intros D C HC x Hx; apply in_points; exists C; tauto. Qed.

Lemma in_tr : forall V S x, In x (tr V S) <-> In x V /\ In x S.
Proof. intros; unfold tr; rewrite filter_In, memb_true_iff; tauto. Qed.

Lemma tr_NoDup : forall V S, NoDup V -> NoDup (tr V S).
Proof. intros; apply NoDup_filter; assumption. Qed.

Lemma tr_in_subsets : forall V S, In (tr V S) (subsets V).
Proof. intros; apply filter_in_subsets. Qed.

Lemma Disjoint_tr_iff :
  forall V C S, Subset C V -> (Disjoint S C <-> Disjoint (tr V S) C).
Proof.
  intros V C S HCV; split; intros Hd x H1 H2.
  - apply in_tr in H1; apply (Hd x); tauto.
  - apply (Hd x); [apply in_tr; split; [apply HCV; exact H2 | exact H1] | exact H2].
Qed.

Lemma inter_tr_SetEq :
  forall V C S, Subset C V -> SetEq (inter S C) (inter (tr V S) C).
Proof.
  intros V C S HCV; split; intros x H; apply in_inter_iff in H; apply in_inter_iff.
  - split; [apply in_tr; split; [apply HCV |]; tauto | tauto].
  - destruct H as [H1 H2]; apply in_tr in H1; tauto.
Qed.

Lemma Disjoint_of_tr_nil :
  forall V C S, Subset C V -> tr V S = [] -> Disjoint S C.
Proof.
  intros V C S HCV Hnil x H1 H2.
  assert (In x (tr V S)) by (apply in_tr; split; [apply HCV; exact H2 | exact H1]).
  rewrite Hnil in H; inversion H.
Qed.

Lemma traces_NoDup : forall V, NoDup V -> NoDup (traces V).
Proof. intros; unfold traces; apply NoDup_filter; apply subs_le_NoDup; assumption. Qed.

Lemma nil_not_in_traces : forall V, ~ In [] (traces V).
Proof. intros V H; unfold traces in H; apply filter_In in H as [_ H]; simpl in H; discriminate. Qed.

Lemma in_traces :
  forall V T, In T (traces V) <-> In T (subs_le 3 V) /\ 1 <= length T.
Proof.
  intros V T; unfold traces; rewrite filter_In, Nat.leb_le; tauto.
Qed.

Lemma in_traces_length : forall V T, In T (traces V) -> 1 <= length T /\ length T <= 3.
Proof.
  intros V T H; apply in_traces in H as [H1 H2]; split; [exact H2 | apply subs_le_length in H1; exact H1].
Qed.

Lemma filter_filter_comm :
  forall {X} (p q : X -> bool) (L : list X),
    filter p (filter q L) = filter (fun x => p x && q x) L.
Proof.
  intros X p q L; induction L as [| x L IH]; simpl; [reflexivity |].
  destruct (q x) eqn:Eq; simpl; destruct (p x) eqn:Ep; simpl; rewrite IH; reflexivity.
Qed.

Lemma exists_in_of_nonnil :
  forall {X} (L : list X), L <> [] -> exists x, In x L.
Proof. intros X L H; destruct L as [| x L]; [exfalso; apply H; reflexivity | exists x; left; reflexivity]. Qed.

Lemma length_filter_impl :
  forall {X} (p q : X -> bool) (L : list X),
    (forall a, In a L -> p a = true -> q a = true) ->
    length (filter p L) <= length (filter q L).
Proof.
  intros X p q L H; induction L as [| a L IH]; simpl; [lia |].
  assert (IH' := IH (fun b Hb => H b (or_intror Hb))).
  destruct (p a) eqn:Ep.
  - rewrite (H a (or_introl eq_refl) Ep); simpl; lia.
  - destruct (q a); simpl; lia.
Qed.

Lemma SetNoDup_map :
  forall (f : list nat -> list nat) (L : Family),
    SetNoDup L ->
    (forall a b, In a L -> In b L -> SetEq (f a) (f b) -> SetEq a b) ->
    SetNoDup (map f L).
Proof.
  intros f L H; induction H as [| A L Hni Hsnd IH]; intros Hinj; simpl; [constructor |].
  constructor.
  - intros B HB Heq. apply in_map_iff in HB as [b [Hb Hbin]]; subst B.
    apply (Hni b Hbin). apply Hinj; [left; reflexivity | right; exact Hbin | exact Heq].
  - apply IH; intros a b Ha Hb; apply Hinj; right; assumption.
Qed.

(** ** The setting of §64 *)

Section Link.
  Variable F : Family.
  Variable R : list nat.
  Hypothesis HU : Uniform 4 F.
  Hypothesis HD : Distinct F.
  Hypothesis Hno : ~ ContainsKSunflower 3 F.
  Hypothesis HR : In R F.

  Let D := DisjointFrom R F.
  Let V := points D.
  Let M := Meeting R F.

  Lemma member_uniform : forall S, In S F -> length S = 4 /\ NoDup S.
  Proof. intros S HS; unfold Uniform in HU; rewrite Forall_forall in HU; exact (HU S HS). Qed.

  Lemma member_nonempty : forall S, In S F -> exists z, In z S.
  Proof.
    intros S HS; destruct (member_uniform S HS) as [HL _].
    destruct S as [| z S']; [simpl in HL; lia | exists z; left; reflexivity].
  Qed.

  Lemma R_not_in_V : forall r, In r R -> ~ In r V.
  Proof.
    intros r Hr HV. apply in_points in HV as [C [HC HrC]].
    apply in_DisjointFrom in HC as [_ Hd]. exact (Hd r Hr HrC).
  Qed.

  Lemma meeting_point : forall S, In S M -> exists r, In r R /\ In r S.
  Proof.
    intros S HS. apply in_Meeting in HS as [_ Hnd].
    destruct (disjointb R S) eqn:E.
    - exfalso; apply Hnd; apply disjointb_correct; exact E.
    - apply disjointb_false_iff in E; exact E.
  Qed.

  Lemma M_sub_F : forall S, In S M -> In S F.
  Proof. intros S HS; apply in_Meeting in HS; tauto. Qed.

  Lemma tr_length_le3 : forall S, In S M -> length (tr V S) <= 3.
  Proof.
    intros S HS. destruct (meeting_point S HS) as [r [HrR HrS]].
    destruct (member_uniform S (M_sub_F S HS)) as [HL HN].
    assert (Hincl : incl (tr V S) (rem_elt r S)).
    { intros x Hx; apply in_tr in Hx as [HxV HxS]; apply in_rem_iff; split; [exact HxS |].
      intro E; subst x; exact (R_not_in_V r HrR HxV). }
    pose proof (NoDup_incl_length (tr_NoDup V S (points_NoDup D)) Hincl) as H.
    rewrite length_rem_elt_in in H by assumption. lia.
  Qed.

  Lemma tr_in_traces : forall S, In S M -> tr V S <> [] -> In (tr V S) (traces V).
  Proof.
    intros S HS Hne. apply in_traces. split.
    - unfold tr; apply filter_in_subs_le; apply tr_length_le3; exact HS.
    - destruct (tr V S); [exfalso; apply Hne; reflexivity | simpl; lia].
  Qed.

  (** (b1): a witnessed trace carries no member. *)
  Lemma witnessed_no_member :
    forall S, In S M -> witnessedb (tr V S) D = true -> False.
  Proof.
    intros S HS Hw. unfold witnessedb in Hw.
    apply existsb_exists in Hw as [C1 [HC1 Hw]].
    apply existsb_exists in Hw as [C2 [HC2 Hw]].
    apply andb_true_iff in Hw as [Hw H3]; apply andb_true_iff in Hw as [H1 H2].
    apply seteqf_correct in H2; apply seteqf_correct in H3.
    assert (H2' : SetEq (inter (tr V S) C1) (inter C1 C2)).
    { eapply SetEq_trans; [apply SetEq_sym; apply interb_SetEq_inter |].
      eapply SetEq_trans; [exact H2 | apply interb_SetEq_inter]. }
    assert (H3' : SetEq (inter (tr V S) C2) (inter C1 C2)).
    { eapply SetEq_trans; [apply SetEq_sym; apply interb_SetEq_inter |].
      eapply SetEq_trans; [exact H3 | apply interb_SetEq_inter]. }
    clear H2 H3; rename H2' into H2; rename H3' into H3.
    assert (H12 : ~ SetEq C1 C2).
    { intro E; apply seteqf_correct in E; rewrite E in H1; discriminate. }
    pose proof (in_DisjointFrom R F C1) as [HC1' _]; specialize (HC1' HC1); destruct HC1' as [HC1F HdC1].
    pose proof (in_DisjointFrom R F C2) as [HC2' _]; specialize (HC2' HC2); destruct HC2' as [HC2F HdC2].
    destruct (meeting_point S HS) as [r [HrR HrS]].
    assert (HSC1 : ~ SetEq S C1) by (intros [Hs _]; exact (HdC1 r HrR (Hs r HrS))).
    assert (HSC2 : ~ SetEq S C2) by (intros [Hs _]; exact (HdC2 r HrR (Hs r HrS))).
    assert (HC1V : Subset C1 V) by (apply member_Subset_points; exact HC1).
    assert (HC2V : Subset C2 V) by (apply member_Subset_points; exact HC2).
    apply Hno.
    apply (@ContainsKSunflower_of_incl 3 [S; C1; C2] F (inter C1 C2)).
    - intros X [E | [E | [E | []]]]; subst X; [apply M_sub_F; exact HS | exact HC1F | exact HC2F].
    - reflexivity.
    - split.
      + constructor.
        * intros X [E | [E | []]] HE; subst X; [exact (HSC1 HE) | exact (HSC2 HE)].
        * constructor; [| constructor; [intros _ [] | constructor]].
          intros X [E | []] HE; subst X; exact (H12 HE).
      + assert (HS1 : SetEq (inter S C1) (inter C1 C2)).
        { eapply SetEq_trans; [apply inter_tr_SetEq; exact HC1V | exact H2]. }
        assert (HS2 : SetEq (inter S C2) (inter C1 C2)).
        { eapply SetEq_trans; [apply inter_tr_SetEq; exact HC2V | exact H3]. }
        intros X Y [EX | [EX | [EX | []]]] [EY | [EY | [EY | []]]] Hne; subst X Y;
          try (exfalso; apply Hne; reflexivity).
        * exact HS1.
        * exact HS2.
        * eapply SetEq_trans; [apply inter_comm_SetEq | exact HS1].
        * apply SetEq_refl.
        * eapply SetEq_trans; [apply inter_comm_SetEq | exact HS2].
        * apply inter_comm_SetEq.
  Qed.

  (** (a): members whose trace misses [C ∈ D] lie in the link of [C]. *)
  Lemma link_constraint :
    forall C, In C D ->
      count (fun S => disjf (tr V S) C) M <= length (DisjointFrom C F).
  Proof.
    intros C HC. unfold count, M, Meeting, DisjointFrom.
    rewrite filter_filter_comm.
    apply length_filter_impl.
    intros S _ H. apply andb_true_iff in H as [H1 _].
    apply disjf_correct in H1.
    apply disjointb_correct; apply Disjoint_sym.
    apply (Disjoint_tr_iff V C S); [apply member_Subset_points; exact HC | exact H1].
  Qed.

  (** (c): the members missing [V] form an intersecting family. *)
  Lemma m0_constraint :
    IotaAtMost 4 27 -> D <> [] ->
    count (fun S => if list_eq_dec Nat.eq_dec (tr V S) [] then true else false) M <= 27.
  Proof.
    intros Hiota Hne.
    set (M0 := filter (fun S => if list_eq_dec Nat.eq_dec (tr V S) [] then true else false) M).
    assert (HM0 : forall S, In S M0 -> In S M /\ tr V S = []).
    { intros S HS; unfold M0 in HS; apply filter_In in HS as [H1 H2]; split; [exact H1 |].
      destruct (list_eq_dec Nat.eq_dec (tr V S) []); [assumption | discriminate]. }
    assert (Hincl : incl M0 F) by (intros S HS; apply M_sub_F; apply HM0; exact HS).
    apply Hiota.
    - apply (Uniform_sublist HU Hincl).
    - unfold M0, M, Meeting; apply SetNoDup_filter; apply SetNoDup_filter; exact HD.
    - destruct (exists_in_of_nonnil D Hne) as [C HC].
      intros S1 S2 H1 H2 Hd.
      apply HM0 in H1 as [H1 T1]; apply HM0 in H2 as [H2 T2].
      assert (HCV : Subset C V) by (apply member_Subset_points; exact HC).
      apply Hno.
      apply (three_disjoint_sunflower F S1 S2 C (M_sub_F S1 H1) (M_sub_F S2 H2)).
      + apply in_DisjointFrom in HC; tauto.
      + apply member_nonempty; apply M_sub_F; exact H1.
      + apply member_nonempty; apply M_sub_F; exact H2.
      + exact Hd.
      + apply (Disjoint_of_tr_nil V C S1 HCV T1).
      + apply (Disjoint_of_tr_nil V C S2 HCV T2).
    - intro HK. apply Hno. eapply ContainsKSunflower_SubFamilySetEq; [exact HK |].
      apply SubFamilySetEq_incl; exact Hincl.
  Qed.
End Link.

(** ** (b): the cap on a trace class

    The members with trace [T] have outer parts that form a
    [(4 − |T|)]-uniform, distinct, sunflower-free family, so their number
    is at most [g(4 − |T|)]: 26, 6, 2 for [|T| = 1, 2, 3], the kernel's
    [PureLink.g_three_at_most_26], [PureLink.g_two_at_most_six] and
    [Product.g_one_at_most_two]. *)

Definition outer (T S : list nat) : list nat := filter (fun x => negb (memb x T)) S.

Lemma in_outer : forall T S x, In x (outer T S) <-> In x S /\ ~ In x T.
Proof.
  intros T S x; unfold outer; rewrite filter_In; split.
  - intros [H1 H2]; split; [exact H1 |].
    apply negb_true_iff in H2; apply memb_false_iff; exact H2.
  - intros [H1 H2]; split; [exact H1 |].
    apply negb_true_iff; apply memb_false_iff; exact H2.
Qed.

Lemma outer_SetEq : forall T a b, SetEq a b -> SetEq (outer T a) (outer T b).
Proof.
  intros T a b [H1 H2]; split; intros x Hx; apply in_outer in Hx as [Hx1 Hx2]; apply in_outer;
    split; [apply H1; exact Hx1 | exact Hx2 | apply H2; exact Hx1 | exact Hx2].
Qed.

Lemma outer_length :
  forall T S, NoDup T -> NoDup S -> Subset T S -> length (outer T S) + length T = length S.
Proof.
  intros T S HT HS HTS.
  pose proof (count_partition (fun x => memb x T) S) as Hp; unfold count in Hp.
  assert (E : length (filter (fun x => memb x T) S) = length T).
  { apply Nat.le_antisymm.
    - apply NoDup_incl_length; [apply NoDup_filter; exact HS |].
      intros x Hx; apply filter_In in Hx as [_ Hx]; apply memb_true_iff; exact Hx.
    - apply NoDup_incl_length; [exact HT |].
      intros x Hx; apply filter_In; split; [apply HTS; exact Hx | apply memb_true_iff; exact Hx]. }
  unfold outer. lia.
Qed.

Section Caps.
  Variable F : Family.
  Variable R : list nat.
  Hypothesis HU : Uniform 4 F.
  Hypothesis HD : Distinct F.
  Hypothesis Hno : ~ ContainsKSunflower 3 F.
  Hypothesis HR : In R F.

  Let D := DisjointFrom R F.
  Let V := points D.
  Let M := Meeting R F.

  Lemma trace_class_cap :
    forall T, In T (traces V) ->
      count (keyb (list_eq_dec Nat.eq_dec) (tr V) T) M <= cap T.
  Proof.
    intros T HT.
    set (MT := filter (keyb (list_eq_dec Nat.eq_dec) (tr V) T) M).
    assert (HMT : forall S, In S MT -> In S M /\ tr V S = T).
    { intros S HS; unfold MT in HS; apply filter_In in HS as [H1 H2]; split; [exact H1 |].
      unfold keyb in H2; destruct (list_eq_dec Nat.eq_dec (tr V S) T); [assumption | discriminate]. }
    change (length MT <= cap T).
    destruct MT as [| S0 MT'] eqn:EMT; [simpl; unfold cap; destruct (length T) as [|[|[|]]]; lia |].
    rewrite <- EMT in *.
    assert (HS0 : In S0 MT) by (rewrite EMT; left; reflexivity).
    assert (HTN : NoDup T).
    { destruct (HMT S0 HS0) as [_ E]; rewrite <- E; apply tr_NoDup; apply points_NoDup. }
    assert (HTsub : forall S, In S MT -> Subset T S).
    { intros S HS x Hx; destruct (HMT S HS) as [_ E]; rewrite <- E in Hx; apply in_tr in Hx; tauto. }
    assert (HMTF : forall S, In S MT -> In S F).
    { intros S HS; apply (M_sub_F F R); apply HMT; exact HS. }
    set (O := map (outer T) MT).
    apply in_traces_length in HT as [HT1 HT3].
    (* uniformity *)
    assert (HOU : Uniform (4 - length T) O).
    { unfold Uniform; apply Forall_forall; intros X HX.
      apply in_map_iff in HX as [S [E HS]]; subst X.
      destruct (member_uniform F HU S (HMTF S HS)) as [HL HN].
      split; [| apply NoDup_filter; exact HN].
      pose proof (outer_length T S HTN HN (HTsub S HS)). lia. }
    (* distinctness *)
    assert (HOD : Distinct O).
    { unfold O; apply SetNoDup_map.
      - unfold MT, M, Meeting; apply SetNoDup_filter; apply SetNoDup_filter; exact HD.
      - intros a b Ha Hb [H1 H2]; split; intros x Hx.
        + destruct (in_dec_nat x T) as [HxT | HxT]; [apply (HTsub b Hb); exact HxT |].
          assert (In x (outer T a)) by (apply in_outer; tauto).
          apply H1 in H; apply in_outer in H; tauto.
        + destruct (in_dec_nat x T) as [HxT | HxT]; [apply (HTsub a Ha); exact HxT |].
          assert (In x (outer T b)) by (apply in_outer; tauto).
          apply H2 in H; apply in_outer in H; tauto. }
    (* sunflower-freeness, by lifting *)
    assert (HOno : ~ ContainsKSunflower 3 O).
    { intros [Q [HQO [HQ3 [core HQ]]]].
      set (pick := fun A => match find (fun S => seteqb A (outer T S)) MT with
                            | Some S' => S' | None => [] end).
      assert (Hpick : forall A, In A Q -> In (pick A) MT /\ SetEq A (outer T (pick A))).
      { intros A HA. destruct (HQO A HA) as [B [HB HAB]].
        apply in_map_iff in HB as [S [HBS HS]]; subst B.
        unfold pick. destruct (find (fun S => seteqb A (outer T S)) MT) eqn:Ef.
        - apply find_some in Ef as [H1 H2]. apply seteqb_correct in H2. tauto.
        - exfalso. pose proof (find_none _ _ Ef S HS) as H'.
          cbv beta in H'. apply seteqb_correct in HAB. rewrite HAB in H'; discriminate. }
      apply Hno.
      apply (@ContainsKSunflower_of_incl 3 (map pick Q) F (T ++ core)).
      - intros X HX; apply in_map_iff in HX as [A [E HA]]; subst X.
        apply HMTF; apply Hpick; exact HA.
      - rewrite map_length; exact HQ3.
      - destruct HQ as [HQnd HQcore]. split.
        + apply SetNoDup_map; [exact HQnd |].
          intros A B HA HB HAB.
          destruct (Hpick A HA) as [_ EA]; destruct (Hpick B HB) as [_ EB].
          eapply SetEq_trans; [exact EA |].
          eapply SetEq_trans; [apply outer_SetEq; exact HAB | apply SetEq_sym; exact EB].
        + intros X Y HX HY Hne.
          apply in_map_iff in HX as [A [EX HA]]; apply in_map_iff in HY as [B [EY HB]]; subst X Y.
          assert (HAB : A <> B) by (intro E; apply Hne; subst; reflexivity).
          specialize (HQcore A B HA HB HAB).
          destruct (Hpick A HA) as [HpA EA]; destruct (Hpick B HB) as [HpB EB].
          split; intros x Hx.
          * apply in_inter_iff in Hx as [HxA HxB].
            apply in_app_iff.
            destruct (in_dec_nat x T) as [HxT | HxT]; [left; exact HxT | right].
            apply HQcore; apply in_inter_iff; split.
            -- apply EA; apply in_outer; tauto.
            -- apply EB; apply in_outer; tauto.
          * apply in_inter_iff. apply in_app_iff in Hx as [HxT | Hxc].
            -- split; [apply (HTsub _ HpA) | apply (HTsub _ HpB)]; exact HxT.
            -- apply HQcore in Hxc; apply in_inter_iff in Hxc as [HxA HxB].
               apply EA in HxA; apply in_outer in HxA.
               apply EB in HxB; apply in_outer in HxB. tauto. }
    assert (HOlen : length O = length MT) by (unfold O; apply map_length).
    rewrite <- HOlen.
    unfold cap.
    destruct (length T) as [|[|[|[|n]]]] eqn:ELT; try lia.
    - replace (4 - 1) with 3 in HOU by lia. apply g_three_at_most_26; assumption.
    - replace (4 - 2) with 2 in HOU by lia. apply g_two_at_most_six; assumption.
    - replace (4 - 3) with 1 in HOU by lia. apply g_one_at_most_two; assumption.
  Qed.
End Caps.

(** ** Weak duality, and the main theorem *)

Lemma count_zero :
  forall {X} (p : X -> bool) (L : list X),
    (forall x, In x L -> p x = true -> False) -> count p L = 0.
Proof.
  intros X p L H; unfold count; induction L as [| x L IH]; simpl; [reflexivity |].
  destruct (p x) eqn:E; [exfalso; exact (H x (or_introl eq_refl) E) |].
  apply IH; intros y Hy; apply H; right; exact Hy.
Qed.

Lemma suml_indicator_count :
  forall {X} (p : X -> bool) (L : list X),
    suml (map (fun x => if p x then 1 else 0) L) = count p L.
Proof.
  intros X p L; unfold count; induction L as [| x L IH]; cbn [map]; [reflexivity |].
  rewrite suml_cons; simpl; destruct (p x); simpl; lia.
Qed.

Lemma suml_map_mul_r :
  forall {X} (c : nat) (f : X -> nat) (L : list X),
    suml (map (fun x => f x * c) L) = suml (map f L) * c.
Proof.
  intros X c f L. rewrite Nat.mul_comm. rewrite <- (suml_map_mul_l c f L).
  apply suml_map_ext; intros; lia.
Qed.

Lemma suml_map_snd_combine :
  forall (D : Family) (y : list nat),
    length y = length D -> suml (map snd (combine D y)) = suml y.
Proof.
  intros D; induction D as [| C D IH]; intros y Hl; destruct y as [| a y];
    cbn [combine map length] in *; try (reflexivity || lia).
  rewrite suml_cons, suml_cons, IH; [reflexivity | lia].
Qed.

Lemma disjointb_nil_l : forall C, disjointb [] C = true.
Proof. intro C; apply disjointb_correct; apply Disjoint_nil_l. Qed.

Theorem link_lp_bound :
  IotaAtMost 4 27 ->
  forall (F : Family) (R : list nat) (c : cert),
    Uniform 4 F -> Distinct F -> ~ ContainsKSunflower 3 F -> In R F ->
    (forall C, In C F -> length (DisjointFrom C F) <= length (DisjointFrom R F)) ->
    DisjointFrom R F <> [] ->
    certcheck (DisjointFrom R F) c (54 - length (DisjointFrom R F)) = true ->
    length F <= 54.
Proof.
  intros Hiota F R c HU HD Hno HR Hmax Hne Hc.
  set (D := DisjointFrom R F) in *.
  set (V := points D) in *.
  set (M := Meeting R F) in *.
  set (B := unwit D) in *.
  set (K := cK c) in *.
  set (w := cw c) in *.
  set (Y := ysum D c (fun _ => true)) in *.
  set (eqd := list_eq_dec Nat.eq_dec).
  set (n := fun T => count (keyb eqd (tr V) T) M).
  set (m0 := n []).
  (* unpack the certificate *)
  unfold certcheck in Hc; fold B K w Y in Hc.
  apply andb_true_iff in Hc as [Hc H5]; apply andb_true_iff in Hc as [Hc H4];
    apply andb_true_iff in Hc as [H1 H3].
  apply Nat.leb_le in H1; apply Nat.leb_le in H3; apply Nat.leb_le in H5.
  rewrite forallb_forall in H4.
  assert (H4' : forall T, In T B -> K <= ysum D c (fun C => disjf T C) + zval c T).
  { intros T HT; specialize (H4 T HT); apply Nat.leb_le in H4; exact H4. }
  clear H4.
  (* the partition of M by trace *)
  assert (HVnd : NoDup V) by apply points_NoDup.
  assert (Hkeys : NoDup ([] :: traces V)).
  { constructor; [apply nil_not_in_traces | apply traces_NoDup; exact HVnd]. }
  assert (Hcov : forall S, In S M -> In (tr V S) ([] :: traces V)).
  { intros S HS. destruct (list_eq_dec Nat.eq_dec (tr V S) []) as [E | NE].
    - rewrite E; left; reflexivity.
    - right; apply (tr_in_traces F R HU S HS NE). }
  assert (Hwit0 : forall T, In T (traces V) -> witnessedb T D = true -> n T = 0).
  { intros T HT Hw. apply count_zero. intros S HS HkS.
    unfold keyb in HkS; destruct (eqd (tr V S) T) as [E | NE]; [| discriminate].
    rewrite <- E in Hw. exact (witnessed_no_member F R Hno S HS Hw). }
  assert (HBsub : forall T, In T B -> In T (traces V)).
  { intros T HT; unfold B, unwit in HT; apply filter_In in HT; tauto. }
  (* |M| = m0 + Σ_{T ∈ B} n T *)
  assert (HM : length M = m0 + suml (map n B)).
  { pose proof (count_by_keys eqd (tr V) ([] :: traces V) M Hkeys Hcov) as Hp.
    cbn [map] in Hp; rewrite suml_cons in Hp. fold m0 in Hp.
    rewrite <- Hp. f_equal. unfold B, unwit. symmetry.
    apply suml_map_filter_zero. intros T HT Hf; apply negb_false_iff in Hf.
    apply Hwit0; assumption. }
  (* (a) for each member of the link, through the key sum *)
  assert (Ha : forall C, In C D ->
            m0 + suml (map (fun T => if disjf T C then n T else 0) B) <= length D).
  { intros C HC.
    pose proof (count_by_keys_weighted eqd (tr V) ([] :: traces V)
                  (fun T => if disjf T C then 1 else 0) M Hkeys Hcov) as Hp.
    cbn [map] in Hp; rewrite suml_cons in Hp. rewrite disjf_nil_l in Hp.
    rewrite suml_indicator_count in Hp.
    assert (E1 : suml (map (fun k => (if disjf k C then 1 else 0) * count (keyb eqd (tr V) k) M) (traces V))
                 = suml (map (fun T => if disjf T C then n T else 0) B)).
    { unfold B, unwit; fold V. symmetry.
      rewrite (suml_map_filter_zero (fun T => negb (witnessedb T D))
                 (fun T => if disjf T C then n T else 0) (traces V)).
      - apply suml_map_ext; intros T _; unfold n; destruct (disjf T C); lia.
      - intros T HT Hf; apply negb_false_iff in Hf; rewrite (Hwit0 T HT Hf);
        destruct (disjf T C); reflexivity. }
    rewrite E1 in Hp. rewrite Nat.mul_1_l in Hp.
    assert (Hlink := link_constraint F R C HC). fold D V M in Hlink.
    assert (HCF : In C F) by (apply in_DisjointFrom in HC; tauto).
    specialize (Hmax C HCF). fold D in Hmax. unfold m0.
    change (n []) with (count (keyb eqd (tr V) []) M). lia. }
  (* (b) caps *)
  assert (Hb : forall T, In T B -> n T <= cap T).
  { intros T HT; apply (trace_class_cap F R HU HD Hno); apply HBsub; exact HT. }
  (* (c) *)
  assert (Hc0 : m0 <= 27) by (apply (m0_constraint F R HU HD Hno); assumption).
  (* weak duality *)
  assert (Hdual : K * length M <= length D * Y + suml (map (fun T => cap T * zval c T) B) + 27 * w).
  { rewrite HM. rewrite Nat.mul_add_distr_l.
    rewrite <- suml_map_mul_l.
    (* K * n T <= (ysum + zval) * n T on B *)
    assert (Hterm : suml (map (fun T => K * n T) B)
                    <= suml (map (fun T => ysum D c (fun C => disjf T C) * n T) B)
                       + suml (map (fun T => zval c T * n T) B)).
    { rewrite <- suml_map_add. apply suml_map_le; intros T HT.
      pose proof (H4' T HT). nia. }
    (* Σ_T ysum_T n_T = Σ_C yval C (Σ_T [disj] n_T) *)
    assert (Hex : suml (map (fun T => ysum D c (fun C => disjf T C) * n T) B)
                  = suml (map (fun C => yval c C * suml (map (fun T => if disjf T C then n T else 0) B)) D)).
    { unfold ysum.
      rewrite (suml_map_ext (fun T => suml (map (fun C => if disjf T C then yval c C else 0) D) * n T)
                            (fun T => suml (map (fun C => yval c C * (if disjf T C then n T else 0)) D)) B).
      - rewrite suml_exchange. apply suml_map_ext; intros C _.
        rewrite <- suml_map_mul_l. reflexivity.
      - intros T _. rewrite <- suml_map_mul_r. apply suml_map_ext; intros C _.
        destruct (disjf T C); lia. }
    (* Σ_C yval C (m0 + Σ_T ...) <= Σ_C yval C * Δ *)
    assert (HaS : suml (map (fun C => yval c C * (m0 + suml (map (fun T => if disjf T C then n T else 0) B))) D)
                  <= suml (map (fun C => yval c C * length D) D)).
    { apply suml_map_le; intros C HC. apply Nat.mul_le_mono_l. apply Ha; exact HC. }
    rewrite suml_map_mul_r in HaS.
    assert (HY : suml (map (yval c) D) = Y).
    { unfold Y, ysum. apply suml_map_ext; intros; reflexivity. }
    rewrite HY in HaS.
    assert (HaS' : suml (map (fun C => yval c C * (m0 + suml (map (fun T => if disjf T C then n T else 0) B))) D)
                   = suml (map (fun C => yval c C * m0) D)
                     + suml (map (fun C => yval c C * suml (map (fun T => if disjf T C then n T else 0) B)) D)).
    { rewrite <- suml_map_add. apply suml_map_ext; intros C _; lia. }
    rewrite suml_map_mul_r in HaS'. rewrite HY in HaS'.
    assert (Hz : suml (map (fun T => zval c T * n T) B) <= suml (map (fun T => cap T * zval c T) B)).
    { apply suml_map_le; intros T HT. pose proof (Hb T HT). nia. }
    pose proof (Nat.mul_le_mono_r _ _ m0 H3) as H3'.
    nia. }
  (* conclude *)
  assert (HF : length F = length D + length M) by (symmetry; apply meeting_disjoint_partition).
  assert (HDle : length D <= 54).
  { assert (Hiota' := DisjointFrom_length_le 4 27 F R Hiota HU HD Hno HR
                        (member_nonempty F HU R HR)). fold D in Hiota'. lia. }
  assert (HMle : K * length M <= K * (54 - length D)) by lia.
  apply Nat.mul_le_mono_pos_l in HMle; [lia | lia].
Qed.

(** ** Transfer: the check depends on the link only as a family of sets

    [certcheck D c b] evaluates on a list; a link class is given by a
    labelled representative.  The lemmas below show the check is invariant
    under replacing [D] by any [D'] that is the same family up to set
    equality of members (both without set-equal duplicates). *)

From Coq Require Import Permutation.

Lemma suml_Permutation : forall l l', Permutation l l' -> suml l = suml l'.
Proof.
  intros l l' H; induction H; unfold suml in *; simpl in *; lia.
Qed.

(** Mutually covering families without set-equal duplicates have
    permuted images under any [SetEq]-respecting function. *)
Lemma map_Permutation_of_SetEq :
  forall {X} (f : list nat -> X) (D D' : Family),
    (forall A B, In A D -> In B D' -> SetEq A B -> f A = f B) ->
    SetNoDup D -> SetNoDup D' ->
    SubFamilySetEq D D' -> SubFamilySetEq D' D ->
    Permutation (map f D) (map f D').
Proof.
  intros X f D; induction D as [| C D IH]; intros D' Hf HD HD' H1 H2.
  - destruct D' as [| C' D']; [constructor |].
    destruct (H2 C' (or_introl eq_refl)) as [B [[] _]].
  - inversion HD as [| ? ? HnC HDr]; subst.
    destruct (H1 C (or_introl eq_refl)) as [C' [HC' ECC']].
    destruct (in_split C' D' HC') as [L1 [L2 EL]]; subst D'.
    assert (HD'r : SetNoDup (L1 ++ L2)).
    { apply (@SetNoDup_incl (L1 ++ L2) (L1 ++ C' :: L2)); [exact HD' | |].
      - apply NoDup_remove_1 with (a := C'). apply SetNoDup_NoDup; exact HD'.
      - intros x Hx; apply in_app_iff in Hx as [Hx | Hx]; apply in_app_iff;
          [left; exact Hx | right; right; exact Hx]. }
    assert (HnC' : forall B, In B (L1 ++ L2) -> ~ SetEq C' B).
    { intros B HB E.
      (* two distinct members of D' set-equal: contradicts SetNoDup D' *)
      pose proof (@SetNoDup_setEq_eq (L1 ++ C' :: L2) C' B HD' HC') as Hq.
      assert (HB' : In B (L1 ++ C' :: L2)).
      { apply in_app_iff in HB as [HB | HB]; apply in_app_iff; [left; exact HB | right; right; exact HB]. }
      specialize (Hq HB' E); subst B.
      apply SetNoDup_NoDup in HD'. apply NoDup_remove_2 in HD'. exact (HD' HB). }
    simpl. rewrite map_app. simpl.
    rewrite (Hf C C' (or_introl eq_refl) HC' ECC').
    apply Permutation_cons_app. rewrite <- map_app.
    apply IH; try assumption.
    + intros A B HA HB E. apply Hf; [right; exact HA | | exact E].
      apply in_app_iff in HB as [HB | HB]; apply in_app_iff; [left; exact HB | right; right; exact HB].
    + intros A HA. destruct (H1 A (or_intror HA)) as [B [HB EAB]].
      apply in_app_iff in HB as [HB | [HB | HB]].
      * exists B; split; [apply in_app_iff; left; exact HB | exact EAB].
      * subst B. exfalso. apply (HnC A HA).
        eapply SetEq_trans; [exact ECC' | apply SetEq_sym; exact EAB].
      * exists B; split; [apply in_app_iff; right; exact HB | exact EAB].
    + intros B HB. destruct (H2 B) as [A [HA EBA]].
      { apply in_app_iff in HB as [HB | HB]; apply in_app_iff; [left; exact HB | right; right; exact HB]. }
      destruct HA as [HA | HA].
      * subst A. exfalso. apply (HnC' B HB).
        eapply SetEq_trans; [apply SetEq_sym; exact ECC' | apply SetEq_sym; exact EBA].
      * exists A; split; [exact HA | exact EBA].
Qed.

Lemma suml_map_SetEq :
  forall (f : list nat -> nat) (D D' : Family),
    (forall A B, In A D -> In B D' -> SetEq A B -> f A = f B) ->
    SetNoDup D -> SetNoDup D' ->
    SubFamilySetEq D D' -> SubFamilySetEq D' D ->
    suml (map f D) = suml (map f D').
Proof. intros; apply suml_Permutation; apply map_Permutation_of_SetEq; assumption. Qed.

Lemma length_SetEq_families :
  forall (D D' : Family),
    SetNoDup D -> SetNoDup D' -> SubFamilySetEq D D' -> SubFamilySetEq D' D ->
    length D = length D'.
Proof.
  intros D D' HD HD' H1 H2.
  pose proof (map_Permutation_of_SetEq (fun _ => tt) D D' (fun _ _ _ _ _ => eq_refl) HD HD' H1 H2) as H.
  apply Permutation_length in H. rewrite map_length, map_length in H. exact H.
Qed.

(** Two sublists of a duplicate-free list with the same elements are equal. *)
Lemma subs_le_SetEq_eq :
  forall k l T1 T2,
    NoDup l -> In T1 (subs_le k l) -> In T2 (subs_le k l) -> SetEq T1 T2 -> T1 = T2.
Proof.
  intros k l; revert k; induction l as [| x l IH]; intros k T1 T2 Hnd H1 H2 E; simpl in *.
  - destruct H1 as [H1 | []]; destruct H2 as [H2 | []]; subst; reflexivity.
  - inversion Hnd as [| ? ? Hnx Hnd']; subst.
    assert (Hnot : forall k T, In T (subs_le k l) -> ~ In x T).
    { intros k0 T HT Hx; apply Hnx; apply (subs_le_Subset k0 l T HT); exact Hx. }
    apply in_app_iff in H1 as [H1 | H1]; apply in_app_iff in H2 as [H2 | H2].
    + destruct k as [| k']; [inversion H1 |].
      apply in_map_iff in H1 as [T1' [E1 H1]]; apply in_map_iff in H2 as [T2' [E2 H2]]; subst.
      f_equal. apply (IH k' T1' T2' Hnd' H1 H2).
      assert (N1 : ~ In x T1') by (apply (Hnot k' T1' H1)).
      assert (N2 : ~ In x T2') by (apply (Hnot k' T2' H2)).
      destruct E as [E1 E2]; split; intros y Hy.
      * assert (H : In y (x :: T2')) by (apply E1; right; exact Hy).
        destruct H as [H | H]; [subst; contradiction | exact H].
      * assert (H : In y (x :: T1')) by (apply E2; right; exact Hy).
        destruct H as [H | H]; [subst; contradiction | exact H].
    + destruct k as [| k']; [inversion H1 |].
      apply in_map_iff in H1 as [T1' [E1 H1]]; subst.
      exfalso. apply (Hnot _ T2 H2). apply E; left; reflexivity.
    + destruct k as [| k']; [inversion H2 |].
      apply in_map_iff in H2 as [T2' [E2 H2]]; subst.
      exfalso. apply (Hnot _ T1 H1). apply E; left; reflexivity.
    + apply (IH k T1 T2 Hnd' H1 H2 E).
Qed.

Lemma subs_le_elem_NoDup : forall k l T, NoDup l -> In T (subs_le k l) -> NoDup T.
Proof.
  intros k l; revert k; induction l as [| x l IH]; intros k T Hnd HT; simpl in HT.
  - destruct HT as [E | []]; subst; constructor.
  - inversion Hnd as [| ? ? Hnx Hnd']; subst.
    apply in_app_iff in HT as [HT | HT]; [| apply (IH k T Hnd' HT)].
    destruct k as [| k']; [inversion HT |].
    apply in_map_iff in HT as [T' [E HT']]; subst.
    constructor; [| apply (IH k' T' Hnd' HT')].
    intro Hx; apply Hnx; apply (subs_le_Subset k' l T' HT'); exact Hx.
Qed.

Lemma SetNoDup_of_pairwise :
  forall (L : Family),
    NoDup L -> (forall A B, In A L -> In B L -> SetEq A B -> A = B) -> SetNoDup L.
Proof.
  intros L H; induction H as [| A L HnA HL IH]; intros Hpw; constructor.
  - intros B HB E. apply HnA. rewrite (Hpw A B (or_introl eq_refl) (or_intror HB) E). exact HB.
  - apply IH; intros a b Ha Hb; apply Hpw; right; assumption.
Qed.

Lemma traces_SetNoDup : forall V, NoDup V -> SetNoDup (traces V).
Proof.
  intros V HV. apply SetNoDup_of_pairwise; [apply traces_NoDup; exact HV |].
  intros A B HA HB E. apply in_traces in HA as [HA _]; apply in_traces in HB as [HB _].
  apply (subs_le_SetEq_eq 3 V A B HV HA HB E).
Qed.

(** *** Set-equality compatibility of the primitives *)

Lemma seteqf_SetEq_r : forall A C C', SetEq C C' -> seteqf A C = seteqf A C'.
Proof.
  intros A C C' E.
  destruct (seteqf A C) eqn:E1; destruct (seteqf A C') eqn:E2; try reflexivity.
  - apply seteqf_correct in E1. exfalso.
    assert (H : seteqf A C' = true) by (apply seteqf_correct; eapply SetEq_trans; [exact E1 | exact E]).
    rewrite H in E2; discriminate.
  - apply seteqf_correct in E2. exfalso.
    assert (H : seteqf A C = true)
      by (apply seteqf_correct; eapply SetEq_trans; [exact E2 | apply SetEq_sym; exact E]).
    rewrite H in E1; discriminate.
Qed.

Lemma lookup_SetEq : forall tab C C', SetEq C C' -> lookup tab C = lookup tab C'.
Proof.
  intros tab C C' E; unfold lookup; induction tab as [| p tab IH]; simpl; [reflexivity |].
  rewrite (seteqf_SetEq_r (fst p) C C' E). destruct (seteqf (fst p) C'); [reflexivity | exact IH].
Qed.

Lemma Disjoint_SetEq_l : forall A A' B, SetEq A A' -> Disjoint A B -> Disjoint A' B.
Proof. intros A A' B [_ H2] Hd x Hx HB; exact (Hd x (H2 x Hx) HB). Qed.

Lemma Disjoint_SetEq_r : forall A B B', SetEq B B' -> Disjoint A B -> Disjoint A B'.
Proof. intros A B B' [_ H2] Hd x HA Hx; exact (Hd x HA (H2 x Hx)). Qed.

Lemma disjf_SetEq : forall T T' C C', SetEq T T' -> SetEq C C' -> disjf T C = disjf T' C'.
Proof.
  intros T T' C C' ET EC.
  destruct (disjf T C) eqn:E1; destruct (disjf T' C') eqn:E2; try reflexivity; exfalso.
  - apply disjf_correct in E1.
    assert (H : disjf T' C' = true).
    { apply disjf_correct. eapply Disjoint_SetEq_r; [exact EC |]. eapply Disjoint_SetEq_l; [exact ET | exact E1]. }
    rewrite H in E2; discriminate.
  - apply disjf_correct in E2.
    assert (H : disjf T C = true).
    { apply disjf_correct. eapply Disjoint_SetEq_r; [apply SetEq_sym; exact EC |].
      eapply Disjoint_SetEq_l; [apply SetEq_sym; exact ET | exact E2]. }
    rewrite H in E1; discriminate.
Qed.

Lemma inter_SetEq_compat :
  forall A A' B B', SetEq A A' -> SetEq B B' -> SetEq (inter A B) (inter A' B').
Proof.
  intros A A' B B' [HA1 HA2] [HB1 HB2]; split; intros x H; apply in_inter_iff in H as [H1 H2];
    apply in_inter_iff; auto.
Qed.

Lemma witnessedb_spec :
  forall T D,
    witnessedb T D = true <->
    exists C1 C2, In C1 D /\ In C2 D /\ ~ SetEq C1 C2 /\
                  SetEq (inter T C1) (inter C1 C2) /\ SetEq (inter T C2) (inter C1 C2).
Proof.
  intros T D; unfold witnessedb; split.
  - intros H. apply existsb_exists in H as [C1 [HC1 H]].
    apply existsb_exists in H as [C2 [HC2 H]].
    apply andb_true_iff in H as [H H3]; apply andb_true_iff in H as [H1 H2].
    apply seteqf_correct in H2; apply seteqf_correct in H3.
    exists C1, C2; split; [exact HC1 | split; [exact HC2 | split; [| split]]].
    + intro E; apply seteqf_correct in E; rewrite E in H1; discriminate.
    + eapply SetEq_trans; [apply SetEq_sym; apply interb_SetEq_inter |].
      eapply SetEq_trans; [exact H2 | apply interb_SetEq_inter].
    + eapply SetEq_trans; [apply SetEq_sym; apply interb_SetEq_inter |].
      eapply SetEq_trans; [exact H3 | apply interb_SetEq_inter].
  - intros [C1 [C2 [HC1 [HC2 [Hne [H2 H3]]]]]].
    apply existsb_exists; exists C1; split; [exact HC1 |].
    apply existsb_exists; exists C2; split; [exact HC2 |].
    apply andb_true_iff; split; [apply andb_true_iff; split |].
    + destruct (seteqf C1 C2) eqn:E; [exfalso; apply Hne; apply seteqf_correct; exact E | reflexivity].
    + apply seteqf_correct.
      eapply SetEq_trans; [apply interb_SetEq_inter |].
      eapply SetEq_trans; [exact H2 | apply SetEq_sym; apply interb_SetEq_inter].
    + apply seteqf_correct.
      eapply SetEq_trans; [apply interb_SetEq_inter |].
      eapply SetEq_trans; [exact H3 | apply SetEq_sym; apply interb_SetEq_inter].
Qed.

Lemma witnessedb_transfer :
  forall T T' D D',
    SetEq T T' -> SubFamilySetEq D D' ->
    witnessedb T D = true -> witnessedb T' D' = true.
Proof.
  intros T T' D D' ET HDD' H.
  apply witnessedb_spec in H as [C1 [C2 [HC1 [HC2 [Hne [H2 H3]]]]]].
  destruct (HDD' C1 HC1) as [C1' [HC1' E1]]; destruct (HDD' C2 HC2) as [C2' [HC2' E2]].
  apply witnessedb_spec. exists C1', C2'; split; [exact HC1' | split; [exact HC2' | split; [| split]]].
  - intro E; apply Hne. eapply SetEq_trans; [exact E1 |].
    eapply SetEq_trans; [exact E | apply SetEq_sym; exact E2].
  - eapply SetEq_trans; [apply inter_SetEq_compat; [apply SetEq_sym; exact ET | apply SetEq_sym; exact E1] |].
    eapply SetEq_trans; [exact H2 | apply inter_SetEq_compat; assumption].
  - eapply SetEq_trans; [apply inter_SetEq_compat; [apply SetEq_sym; exact ET | apply SetEq_sym; exact E2] |].
    eapply SetEq_trans; [exact H3 | apply inter_SetEq_compat; assumption].
Qed.

Lemma witnessedb_SetEq :
  forall T T' D D',
    SetEq T T' -> SubFamilySetEq D D' -> SubFamilySetEq D' D ->
    witnessedb T D = witnessedb T' D'.
Proof.
  intros T T' D D' ET H1 H2.
  destruct (witnessedb T D) eqn:E1; destruct (witnessedb T' D') eqn:E2; try reflexivity.
  - rewrite (witnessedb_transfer T T' D D' ET H1 E1) in E2; discriminate.
  - rewrite (witnessedb_transfer T' T D' D (SetEq_sym ET) H2 E2) in E1; discriminate.
Qed.

Lemma points_SetEq :
  forall D D', SubFamilySetEq D D' -> SubFamilySetEq D' D -> SetEq (points D) (points D').
Proof.
  intros D D' H1 H2; split; intros x Hx; apply in_points in Hx as [C [HC HxC]]; apply in_points.
  - destruct (H1 C HC) as [C' [HC' [E _]]]; exists C'; split; [exact HC' | apply E; exact HxC].
  - destruct (H2 C HC) as [C' [HC' [E _]]]; exists C'; split; [exact HC' | apply E; exact HxC].
Qed.

(** Every unwitnessed trace of [D] has a set-equal unwitnessed trace of
    [D'], namely its canonical trace on [points D']. *)
Lemma unwit_transfer :
  forall D D' T,
    SubFamilySetEq D D' -> SubFamilySetEq D' D ->
    In T (unwit D) -> In (tr (points D') T) (unwit D') /\ SetEq T (tr (points D') T).
Proof.
  intros D D' T H1 H2 HT.
  unfold unwit in HT; apply filter_In in HT as [HT Hw]; apply negb_true_iff in Hw.
  apply in_traces in HT as [HT Hlen].
  assert (HTV : Subset T (points D)) by (apply (subs_le_Subset 3 (points D) T HT)).
  assert (HTnd : NoDup T) by (apply (subs_le_elem_NoDup 3 (points D) T (points_NoDup D) HT)).
  pose proof (points_SetEq D D' H1 H2) as [HV1 HV2].
  assert (E : SetEq T (tr (points D') T)).
  { split; intros x Hx.
    - apply in_tr; split; [apply HV1; apply HTV; exact Hx | exact Hx].
    - apply in_tr in Hx; tauto. }
  split; [| exact E].
  unfold unwit; apply filter_In; split.
  - apply in_traces; split.
    + apply subs_le_length in HT.
      assert (length (tr (points D') T) <= length T).
      { apply NoDup_incl_length; [apply tr_NoDup; apply points_NoDup |].
        intros x Hx; apply in_tr in Hx; tauto. }
      apply (filter_in_subs_le (fun x => memb x T) (points D') 3).
      change (length (tr (points D') T) <= 3). lia.
    + destruct T as [| t T']; [simpl in Hlen; lia |].
      assert (In t (tr (points D') (t :: T'))) by (apply E; left; reflexivity).
      destruct (tr (points D') (t :: T')); [inversion H | simpl; lia].
  - apply negb_true_iff. rewrite <- (witnessedb_SetEq T _ D D' E H1 H2). exact Hw.
Qed.

Lemma unwit_SetNoDup : forall D, SetNoDup (unwit D).
Proof. intro D; unfold unwit; apply SetNoDup_filter; apply traces_SetNoDup; apply points_NoDup. Qed.

Lemma unwit_elem_NoDup : forall D T, In T (unwit D) -> NoDup T.
Proof.
  intros D T HT; unfold unwit in HT; apply filter_In in HT as [HT _]; apply in_traces in HT as [HT _].
  apply (subs_le_elem_NoDup 3 (points D) T (points_NoDup D) HT).
Qed.

Lemma cap_SetEq : forall T T', NoDup T -> NoDup T' -> SetEq T T' -> cap T = cap T'.
Proof.
  intros T T' H1 H2 [E1 E2]; unfold cap.
  assert (length T = length T').
  { apply Nat.le_antisymm; apply NoDup_incl_length; assumption. }
  rewrite H; reflexivity.
Qed.

(** The transfer theorem. *)
Theorem certcheck_transfer :
  forall D D' c b,
    SetNoDup D -> SetNoDup D' -> SubFamilySetEq D D' -> SubFamilySetEq D' D ->
    certcheck D' c b = true -> certcheck D c b = true.
Proof.
  intros D D' c b HD HD' H1 H2 Hc.
  assert (Hlen : length D = length D') by (apply length_SetEq_families; assumption).
  assert (HY : forall p p', (forall C C', SetEq C C' -> p C = p' C') ->
                 ysum D c p = ysum D' c p').
  { intros p p' Hp; unfold ysum.
    rewrite (suml_map_ext (fun C => if p C then yval c C else 0) (fun C => if p' C then yval c C else 0) D)
      by (intros C _; rewrite (Hp C C (SetEq_refl C)); reflexivity).
    apply suml_map_SetEq; try assumption.
    intros A B _ _ E. rewrite <- (Hp A A (SetEq_refl A)). rewrite (Hp A B E).
    unfold yval; rewrite (lookup_SetEq (cy c) A B E). reflexivity. }
  assert (HU1 : SubFamilySetEq (unwit D) (unwit D')).
  { intros T HT; destruct (unwit_transfer D D' T H1 H2 HT) as [HT' E]; exists (tr (points D') T); tauto. }
  assert (HU2 : SubFamilySetEq (unwit D') (unwit D)).
  { intros T HT; destruct (unwit_transfer D' D T H2 H1 HT) as [HT' E]; exists (tr (points D) T); tauto. }
  unfold certcheck in *.
  apply andb_true_iff in Hc as [Hc H5]; apply andb_true_iff in Hc as [Hc H4];
    apply andb_true_iff in Hc as [H1' H3].
  rewrite forallb_forall in H4.
  apply andb_true_iff; split; [apply andb_true_iff; split; [apply andb_true_iff; split |] |].
  - exact H1'.
  - rewrite (HY (fun _ => true) (fun _ => true)) by reflexivity. exact H3.
  - apply forallb_forall. intros T HT.
    destruct (HU1 T HT) as [T' [HT' E]].
    specialize (H4 T' HT').
    rewrite (HY (fun C => disjf T C) (fun C => disjf T' C))
      by (intros C C' EC; apply disjf_SetEq; assumption).
    unfold zval; rewrite (lookup_SetEq (cz c) T T' E). exact H4.
  - rewrite (HY (fun _ => true) (fun _ => true)) by reflexivity.
    rewrite Hlen.
    assert (HS : suml (map (fun T => cap T * zval c T) (unwit D))
                 = suml (map (fun T => cap T * zval c T) (unwit D'))).
    { apply suml_map_SetEq; [| apply unwit_SetNoDup | apply unwit_SetNoDup | exact HU1 | exact HU2].
      intros A B HA HB E.
      rewrite (cap_SetEq A B (unwit_elem_NoDup D A HA) (unwit_elem_NoDup D' B HB) E).
      unfold zval; rewrite (lookup_SetEq (cz c) A B E). reflexivity. }
    rewrite HS. exact H5.
Qed.

(** ** From a labelled class representative to any family

    A link class is given by a representative [Dk] on concrete labels, with
    a certificate [ck].  For a family [F] whose link at [R] is [Dk] up to a
    relabelling [g] (with inverse [h]), relabel [F] by [h]: its link at
    [rmap h R] is then the same family of sets as [Dk], so
    [certcheck_transfer] moves the certificate over and [link_lp_bound]
    applies. *)

From Sunflower Require Import DirectSum.

Section Relabelling.
  Variable g h : nat -> nat.
  Hypothesis Hgh : forall x, h (g x) = x.
  Hypothesis Hhg : forall x, g (h x) = x.

  Lemma Disjoint_rmap : forall A B, Disjoint (rmap g A) (rmap g B) <-> Disjoint A B.
  Proof.
    intros A B; split; intros Hd x HA HB.
    - apply (Hd (g x)); apply in_map; assumption.
    - unfold rmap in HA, HB. apply in_map_iff in HA as [a [Ea Ha]]; apply in_map_iff in HB as [b [Eb Hb]].
      assert (a = b) by (rewrite <- (Hgh a), <- (Hgh b), Ea, Eb; reflexivity).
      subst b. exact (Hd a Ha Hb).
  Qed.

  Lemma DisjointFrom_rmapF :
    forall R F, DisjointFrom (rmap g R) (rmapF g F) = rmapF g (DisjointFrom R F).
  Proof.
    intros R F; unfold DisjointFrom, rmapF; induction F as [| C F IH]; simpl; [reflexivity |].
    assert (E : disjointb (rmap g R) (rmap g C) = disjointb R C).
    { destruct (disjointb R C) eqn:E1.
      - apply disjointb_correct; apply Disjoint_rmap; apply disjointb_correct; exact E1.
      - destruct (disjointb (rmap g R) (rmap g C)) eqn:E2; [| reflexivity].
        apply disjointb_correct in E2; apply (proj1 (Disjoint_rmap R C)) in E2; apply disjointb_correct in E2.
        rewrite E2 in E1; discriminate. }
    rewrite E. destruct (disjointb R C); simpl; rewrite IH; reflexivity.
  Qed.

  Lemma SubFamilySetEq_rmapF :
    forall A B, SubFamilySetEq A B -> SubFamilySetEq (rmapF g A) (rmapF g B).
  Proof.
    intros A B H X HX. unfold rmapF in HX; apply in_map_iff in HX as [X0 [E HX0]]; subst X.
    destruct (H X0 HX0) as [Y0 [HY0 EY]].
    exists (rmap g Y0); split; [apply in_map; exact HY0 |].
    destruct EY as [E1 E2]; split; intros x Hx; unfold rmap in *;
      apply in_map_iff in Hx as [y [Ey Hy]]; subst; apply in_map; auto.
  Qed.

  Lemma rmapF_inverse : forall D, rmapF h (rmapF g D) = D.
  Proof.
    intros D; unfold rmapF; rewrite map_map.
    rewrite (map_ext (fun A => rmap h (rmap g A)) (fun A => A)); [apply map_id |].
    intros A; apply (rmap_left_inverse g h Hgh).
  Qed.
End Relabelling.

(** A member whose link is as large as any. *)
Lemma exists_max_link :
  forall (F : Family), F <> [] ->
    exists R, In R F /\ forall C, In C F -> length (DisjointFrom C F) <= length (DisjointFrom R F).
Proof.
  intros F Hne.
  assert (H : forall (L : list (list nat)), L <> [] ->
            exists R, In R L /\ forall C, In C L -> length (DisjointFrom C F) <= length (DisjointFrom R F)).
  { intros L; induction L as [| A L IH]; intros HL; [exfalso; apply HL; reflexivity |].
    destruct L as [| B L'].
    - exists A; split; [left; reflexivity | intros C [E | []]; subst; lia].
    - destruct (IH ltac:(discriminate)) as [R [HR Hmax]].
      destruct (le_lt_dec (length (DisjointFrom A F)) (length (DisjointFrom R F))) as [Hle | Hlt].
      + exists R; split; [right; exact HR |].
        intros C [E | HC]; [subst; exact Hle | apply Hmax; exact HC].
      + exists A; split; [left; reflexivity |].
        intros C [E | HC]; [subst; lia | pose proof (Hmax C HC); lia]. }
  apply H; exact Hne.
Qed.

(** The link of a nonempty member of a sunflower-free family is intersecting. *)
Lemma DisjointFrom_Intersecting :
  forall F R, Uniform 4 F -> ~ ContainsKSunflower 3 F -> In R F ->
    Intersecting (DisjointFrom R F).
Proof.
  intros F R HU Hno HR C1 C2 H1 H2 Hd.
  apply in_DisjointFrom in H1 as [H1 D1]; apply in_DisjointFrom in H2 as [H2 D2].
  apply Hno. apply (three_disjoint_sunflower F C1 C2 R H1 H2 HR).
  - apply (member_nonempty F HU C1 H1).
  - apply (member_nonempty F HU C2 H2).
  - exact Hd.
  - apply Disjoint_sym; exact D1.
  - apply Disjoint_sym; exact D2.
Qed.

(** The per-class theorem. *)
Theorem class_bound :
  IotaAtMost 4 27 ->
  forall (Dk : Family) (ck : cert),
    SetNoDup Dk -> certcheck Dk ck (54 - length Dk) = true ->
    forall (F : Family) (R : list nat) (g h : nat -> nat),
      (forall x, h (g x) = x) -> (forall x, g (h x) = x) ->
      Uniform 4 F -> Distinct F -> ~ ContainsKSunflower 3 F -> In R F ->
      (forall C, In C F -> length (DisjointFrom C F) <= length (DisjointFrom R F)) ->
      DisjointFrom R F <> [] ->
      SubFamilySetEq (DisjointFrom R F) (rmapF g Dk) ->
      SubFamilySetEq (rmapF g Dk) (DisjointFrom R F) ->
      length F <= 54.
Proof.
  intros Hiota Dk ck HDk Hck F R g h Hgh Hhg HU HD Hno HR Hmax Hne H1 H2.
  set (F' := rmapF h F). set (R' := rmap h R).
  assert (HU' : Uniform 4 F') by (apply (rmapF_Uniform h g Hhg); exact HU).
  assert (HD' : Distinct F') by (apply (rmapF_Distinct h g Hhg); exact HD).
  assert (Hno' : ~ ContainsKSunflower 3 F').
  { intro Hc. apply Hno. apply (ContainsKSunflower_rmapF g h Hgh Hhg) in Hc.
    unfold F' in Hc. rewrite (rmapF_inverse h g Hhg) in Hc. exact Hc. }
  assert (HR' : In R' F') by (apply in_map; exact HR).
  assert (HDF : DisjointFrom R' F' = rmapF h (DisjointFrom R F)) by apply (DisjointFrom_rmapF h g Hhg).
  assert (Hmax' : forall C, In C F' -> length (DisjointFrom C F') <= length (DisjointFrom R' F')).
  { intros C HC. unfold F' in HC; apply in_map_iff in HC as [C0 [E HC0]]; subst C.
    rewrite HDF. unfold F'. rewrite (DisjointFrom_rmapF h g Hhg). rewrite (rmapF_length h), (rmapF_length h).
    apply Hmax; exact HC0. }
  assert (Hne' : DisjointFrom R' F' <> []).
  { rewrite HDF. intro E. apply Hne. destruct (DisjointFrom R F); [reflexivity | discriminate]. }
  assert (HS1 : SubFamilySetEq (DisjointFrom R' F') Dk).
  { rewrite HDF. apply (SubFamilySetEq_rmapF h) in H1.
    rewrite (rmapF_inverse g h Hgh) in H1. exact H1. }
  assert (HS2 : SubFamilySetEq Dk (DisjointFrom R' F')).
  { rewrite HDF. apply (SubFamilySetEq_rmapF h) in H2.
    rewrite (rmapF_inverse g h Hgh) in H2. exact H2. }
  assert (HSD' : SetNoDup (DisjointFrom R' F')) by (unfold DisjointFrom; apply SetNoDup_filter; exact HD').
  assert (Hlen : length (DisjointFrom R' F') = length Dk) by (apply length_SetEq_families; assumption).
  assert (Hck' : certcheck (DisjointFrom R' F') ck (54 - length (DisjointFrom R' F')) = true).
  { rewrite Hlen. apply (certcheck_transfer _ Dk); assumption. }
  pose proof (link_lp_bound Hiota F' R' ck HU' HD' Hno' HR' Hmax' Hne' Hck') as H.
  unfold F' in H; rewrite (rmapF_length h) in H; exact H.
Qed.

(** ** The descent, conditional on a census

    [Census reps lo]: every intersecting 3-sunflower-free family of at
    least [lo] distinct 4-sets is, up to relabelling, one of the
    representatives.  This is what the exhaustive search of §60 found and
    is NOT proved here.  [reps_ok reps]: every representative is distinct
    and carries a checked certificate — decided by [vm_compute]. *)

Definition Census (reps : list (Family * cert)) (lo : nat) : Prop :=
  forall D : Family,
    Uniform 4 D -> Distinct D -> Intersecting D -> ~ ContainsKSunflower 3 D ->
    lo <= length D ->
    exists Dk ck (g h : nat -> nat),
      In (Dk, ck) reps /\ (forall x, h (g x) = x) /\ (forall x, g (h x) = x) /\
      SubFamilySetEq D (rmapF g Dk) /\ SubFamilySetEq (rmapF g Dk) D.

Definition setnodupb (D : Family) : bool :=
  let fix go (L : Family) : bool :=
    match L with
    | [] => true
    | A :: L' => forallb (fun B => negb (seteqf A B)) L' && go L'
    end in go D.

Lemma setnodupb_correct : forall D, setnodupb D = true -> SetNoDup D.
Proof.
  intros D; induction D as [| A D IH]; intros H; simpl in H; [constructor |].
  apply andb_true_iff in H as [H1 H2]. constructor; [| apply IH; exact H2].
  rewrite forallb_forall in H1. intros B HB E. specialize (H1 B HB).
  apply negb_true_iff in H1. apply seteqf_correct in E. rewrite E in H1; discriminate.
Qed.

Definition reps_okb (reps : list (Family * cert)) : bool :=
  forallb (fun p => setnodupb (fst p) && certcheck (fst p) (snd p) (54 - length (fst p))) reps.

Theorem descent_of_census :
  IotaAtMost 4 27 ->
  forall reps lo, 1 <= lo -> reps_okb reps = true -> Census reps lo -> LinkDescent 4 lo 54.
Proof.
  intros Hiota reps lo Hlo1 Hok Hcen F R HU HD Hno HR Hlo.
  assert (HFne : F <> []) by (intro E; rewrite E in HR; inversion HR).
  destruct (exists_max_link F HFne) as [R0 [HR0 Hmax]].
  set (D := DisjointFrom R0 F).
  assert (HDlo : lo <= length D) by (unfold D; pose proof (Hmax R HR); lia).
  assert (HDne : D <> []).
  { intro E. pose proof (Hmax R HR) as H. unfold D in E. rewrite E in H. simpl in H. lia. }
  assert (HDU : Uniform 4 D).
  { apply (Uniform_sublist HU); intros C HC; apply in_DisjointFrom in HC; tauto. }
  assert (HDD : Distinct D) by (unfold D, DisjointFrom; apply SetNoDup_filter; exact HD).
  assert (HDI : Intersecting D) by (apply DisjointFrom_Intersecting; assumption).
  assert (HDno : ~ ContainsKSunflower 3 D).
  { intro Hc; apply Hno; eapply ContainsKSunflower_SubFamilySetEq; [exact Hc |].
    apply SubFamilySetEq_incl; intros C HC; apply in_DisjointFrom in HC; tauto. }
  destruct (Hcen D HDU HDD HDI HDno HDlo) as [Dk [ck [g [h [Hin [Hgh [Hhg [H1 H2]]]]]]]].
  unfold reps_okb in Hok; rewrite forallb_forall in Hok.
  specialize (Hok (Dk, ck) Hin); simpl in Hok; apply andb_true_iff in Hok as [Hnd Hck].
  apply setnodupb_correct in Hnd.
  exact (class_bound Hiota Dk ck Hnd Hck F R0 g h Hgh Hhg HU HD Hno HR0 Hmax HDne H1 H2).
Qed.

(** With the census of sizes 25–27 and [ABCDN26]'s meeting bound: a 24-member
    link and 56 meeting members give [24 + 56 = 80]. *)
Corollary g_four_at_most_80_of_census :
  IotaAtMost 4 27 ->
  forall reps, reps_okb reps = true -> Census reps 25 -> MeetingBound 4 56 -> GAtMost 4 80.
Proof.
  intros Hiota reps Hok Hcen Hm.
  pose proof (g_at_most_of_descent_and_meeting 4 25 54 56 (descent_of_census Hiota reps 25 ltac:(lia) Hok Hcen) Hm) as H.
  replace (Nat.max 54 (25 - 1 + 56)) with 80 in H by reflexivity. exact H.
Qed.
