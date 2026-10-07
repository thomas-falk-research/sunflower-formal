(** * The finer link model of §65, in the kernel

    For a 4-uniform 3-sunflower-free [F] with a member [R] whose link
    [D] is largest, every member outside [D ∪ {R}] has a type
    [(T, P)]: its canonical trace [T] on [V = points D] (empty or an
    unwitnessed trace) and its canonical profile [P] on [R] (nonempty,
    and a proper part of [R] when [T] is empty).  [tools/iota4/link23.py]
    bounds the type counts by an integer program whose rows are
    consequences of sunflower-freeness and of [D] being largest; §65
    certified eleven link classes at size 23 with exact branch-and-bound
    trees over that program.  This module proves the rows for the actual
    counts ([Link23.rows_valid]) and checks such trees by computation
    ([treecheck]), so that [bound_of_tree] turns a checked tree into
    [|F| ≤ 54].  See docs/roadmap.md §69. *)

From Coq Require Import List Arith NArith Lia Bool.
Import ListNotations.
From Sunflower Require Import Sets Sunflower Intersecting IotaRate Spread
  Counting LowerBound PureLink Product Stability4 DirectSum LinkCombine LinkLP.

(** ** Types *)

(** Profiles are positional: a profile is a nonempty set of positions
    [0..3] into [R], so that the type list and every row depend on the
    link [D] alone, and a class check is a closed computation. *)
Definition POS : list nat := [0; 1; 2; 3].

Definition PROF : list (list nat) :=
  filter (fun P => 1 <=? length P) (subs_le 4 POS).

(** The positions of [R] lying in [S]. *)
Definition prof (R S : list nat) : list nat :=
  filter (fun k => memb (nth k R 0) S) POS.

(** The labels of a positional profile. *)
Definition lab (R P : list nat) : list nat := map (fun k => nth k R 0) P.

Definition ltype := (list nat * list nat)%type.    (* (trace on V, positional profile) *)

(** The type list, in a fixed order: M1 types (unwitnessed trace, any
    profile, together at most 4 points) then M0 types (empty trace,
    proper profile). *)
Definition types (D : Family) : list ltype :=
  flat_map (fun T => map (fun P => (T, P))
                         (filter (fun P => length T + length P <=? 4) PROF))
           (unwit D)
  ++ map (fun P => ([], P)) (filter (fun P => length P <=? 3) PROF).

Definition typeof (V R S : list nat) : ltype := (tr V S, prof R S).

Definition ltype_eq_dec : forall a b : ltype, {a = b} + {a <> b}.
Proof. decide equality; apply list_eq_dec; apply Nat.eq_dec. Defined.

(** Members other than [R] that meet [R]. *)
Definition Others (R : list nat) (F : Family) : Family :=
  filter (fun S => negb (seteqf S R)) (Meeting R F).

(** The count of members of type [t]. *)
Definition tcount (V R : list nat) (M : Family) (t : ltype) : nat :=
  count (keyb ltype_eq_dec (typeof V R) t) M.

Lemma in_PROF : forall P, In P PROF <-> In P (subs_le 4 POS) /\ 1 <= length P.
Proof. intros; unfold PROF; rewrite filter_In, Nat.leb_le; tauto. Qed.

Lemma POS_NoDup : NoDup POS.
Proof. unfold POS; repeat constructor; simpl; lia. Qed.

Lemma PROF_NoDup : NoDup PROF.
Proof. unfold PROF; apply NoDup_filter; apply subs_le_NoDup; apply POS_NoDup. Qed.

Lemma in_PROF_pos : forall P k, In P PROF -> In k P -> k < 4.
Proof.
  intros P k HP Hk; apply in_PROF in HP as [HP _]; apply (subs_le_Subset 4 POS P HP) in Hk.
  unfold POS in Hk; simpl in Hk; lia.
Qed.

Lemma in_PROF_NoDup : forall P, In P PROF -> NoDup P.
Proof. intros P HP; apply in_PROF in HP as [HP _]; exact (subs_le_elem_NoDup 4 POS P POS_NoDup HP). Qed.

Lemma in_prof : forall R S k, In k (prof R S) <-> k < 4 /\ In (nth k R 0) S.
Proof.
  intros R S k; unfold prof; rewrite filter_In, memb_true_iff; unfold POS; simpl.
  split; intros [H1 H2]; split; try assumption; lia.
Qed.

Lemma prof_NoDup : forall R S, NoDup (prof R S).
Proof. intros; unfold prof; apply NoDup_filter; apply POS_NoDup. Qed.

Lemma in_lab : forall R P x, In x (lab R P) <-> exists k, In k P /\ x = nth k R 0.
Proof.
  intros R P x; unfold lab; rewrite in_map_iff; split.
  - intros [k [E Hk]]; exists k; auto.
  - intros [k [Hk E]]; exists k; auto.
Qed.

Lemma lab_length : forall R P, length (lab R P) = length P.
Proof. intros; unfold lab; apply map_length. Qed.

Lemma in_Others : forall R F S, In S (Others R F) <-> In S (Meeting R F) /\ ~ SetEq S R.
Proof.
  intros; unfold Others; rewrite filter_In, negb_true_iff; split.
  - intros [H1 H2]; split; [exact H1 | intro E; apply seteqf_correct in E; rewrite E in H2; discriminate].
  - intros [H1 H2]; split; [exact H1 |].
    destruct (seteqf S R) eqn:E; [exfalso; apply H2; apply seteqf_correct; exact E | reflexivity].
Qed.

Lemma types_NoDup : forall D, NoDup (types D).
Proof.
  intros D; unfold types.
  assert (HU : NoDup (unwit D)) by (apply SetNoDup_NoDup; apply unwit_SetNoDup).
  pose proof PROF_NoDup as HP.
  apply NoDup_app_disjoint.
  - induction (unwit D) as [| T Ts IH]; cbn [flat_map]; [constructor |].
    inversion HU as [| ? ? HnT HU']; subst.
    apply NoDup_app_disjoint.
    + apply NoDup_map_inj; [intros a b _ _ E; injection E; auto | apply NoDup_filter; exact HP].
    + apply IH; exact HU'.
    + intros x H1 H2. apply in_map_iff in H1 as [P [E _]]; subst x.
      apply in_flat_map in H2 as [T' [HT' H2]]. apply in_map_iff in H2 as [P' [E _]].
      injection E; intros _ ET; subst T'. exact (HnT HT').
  - apply NoDup_map_inj; [intros a b _ _ E; injection E; auto | apply NoDup_filter; exact HP].
  - intros x H1 H2. apply in_flat_map in H1 as [T [HT H1]]. apply in_map_iff in H1 as [P [E _]]; subst x.
    apply in_map_iff in H2 as [P' [E _]]. injection E; intros _ ET; subst T.
    unfold unwit in HT; apply filter_In in HT as [HT _]; apply in_traces_length in HT; simpl in HT; lia.
Qed.

(** [typeof] depends on the member only as a set. *)
Lemma memb_SetEq : forall S S' x, SetEq S S' -> memb x S = memb x S'.
Proof.
  intros S S' x [H1 H2].
  destruct (memb x S) eqn:E1; destruct (memb x S') eqn:E2; try reflexivity; exfalso.
  - apply memb_true_iff in E1; apply memb_false_iff in E2; auto.
  - apply memb_false_iff in E1; apply memb_true_iff in E2; auto.
Qed.

Lemma typeof_SetEq : forall V R S S', SetEq S S' -> typeof V R S = typeof V R S'.
Proof.
  intros V R S S' H; unfold typeof, tr, prof; f_equal; apply filter_ext; intros x; apply memb_SetEq; exact H.
Qed.

(** ** Rows

    A row is a coefficient function on types and a right-hand side; the
    rows of the §65 program are named by tags, and [rowc] builds the row
    of a tag, or the trivial row [0 ≤ 0] when the tag is malformed. *)

Definition ub_of (t : ltype) : nat :=
  match t with
  | ([], P) => match length P with 3 => 1 | 2 => 3 | _ => 26 end
  | (T, P) => match 4 - (length T + length P) with 0 => 1 | 1 => 2 | _ => 6 end
  end.

Definition leqb (a b : list nat) : bool := if list_eq_dec Nat.eq_dec a b then true else false.
Definition nilb (l : list nat) : bool := match l with [] => true | _ => false end.
Definition inlb (a : list nat) (L : list (list nat)) : bool := existsb (leqb a) L.
Definition dett (t : ltype) : bool := length (fst t) + length (snd t) =? 4.
Definition eqt (t a : ltype) : nat := if ltype_eq_dec t a then 1 else 0.
Definition dflt : ltype := ([], []).

(** Type [t] is certainly disjoint from the determined type [a]. *)
Definition detdis (a t : ltype) : bool := disjf (fst t) (fst a) && disjf (snd t) (snd a).

(** A member of the determined type [a] and one of type [b] would form a
    3-sunflower: with [R] (equal profiles, disjoint traces), with a link
    member [C] (both traces meet [C] in the common trace part, profiles
    disjoint), or with a link member avoiding both (all disjoint). *)
Definition exclb (D : Family) (a b : ltype) : bool :=
  let TT := interb (fst a) (fst b) in
  let PP := interb (snd a) (snd b) in
  (seteqf (snd a) (snd b) && nilb TT)
  || (nilb PP && existsb (fun C => seteqf (interb (fst a) C) TT && seteqf (interb (fst b) C) TT) D)
  || (nilb TT && nilb PP && existsb (fun C => disjf (fst a) C && disjf (fst b) C) D).

Inductive tag : Type :=
| RCap (T : list nat)          (* members with trace [T]: at most [cap T] *)
| RLink (C : list nat)         (* members missing [C ∈ D]: at most [|D| − 1] *)
| RStar (k : nat)              (* members through position [k] of [R]: at most 25 *)
| RDet (i : nat)               (* type [i] determined: its link has at most [|D|] members *)
| RExcl (i j : nat).           (* type [i] determined: it excludes type [j] *)

Definition row : Type := ((ltype -> nat) * nat)%type.
Definition trivial_row : row := (fun _ => 0, 0).

Definition rowc (D : Family) (U : list (list nat)) (ts : list ltype) (big : nat) (tg : tag) : row :=
  match tg with
  | RCap T => if inlb T U then (fun t => Nat.b2n (leqb (fst t) T), cap T) else trivial_row
  | RLink C => if inlb C D then (fun t => Nat.b2n (disjf (fst t) C), length D - 1) else trivial_row
  | RStar k => if k <? 4 then (fun t => Nat.b2n (membf k (snd t)), 25) else trivial_row
  | RDet i =>
      if i <? length ts then
        let a := nth i ts dflt in
        if dett a then (fun t => big * eqt t a + Nat.b2n (detdis a t),
                        length D - count (fun C => disjf (fst a) C) D + big)
        else trivial_row
      else trivial_row
  | RExcl i j =>
      if (i <? length ts) && (j <? length ts) && negb (i =? j) then
        let a := nth i ts dflt in
        let b := nth j ts dflt in
        if dett a && exclb D a b then (fun t => ub_of b * eqt t a + eqt t b, ub_of b)
        else trivial_row
      else trivial_row
  end.

Definition rowsat (ts : list ltype) (x : ltype -> nat) (r : row) : Prop :=
  suml (map (fun t => fst r t * x t) ts) <= snd r.

Lemma leqb_true_iff : forall a b, leqb a b = true <-> a = b.
Proof. intros a b; unfold leqb; destruct (list_eq_dec Nat.eq_dec a b); split; intros; congruence. Qed.

Lemma inlb_true_iff : forall a L, inlb a L = true <-> In a L.
Proof.
  intros a L; unfold inlb; rewrite existsb_exists; split.
  - intros [b [Hb E]]; apply leqb_true_iff in E; subst; exact Hb.
  - intros Ha; exists a; split; [exact Ha | apply leqb_true_iff; reflexivity].
Qed.

Lemma nilb_true_iff : forall l, nilb l = true <-> l = [].
Proof. intros [| a l]; simpl; split; intros; congruence. Qed.

Lemma suml_b2n : forall {X} (p : X -> bool) (L : list X),
  suml (map (fun x => Nat.b2n (p x)) L) = count p L.
Proof.
  intros X p L; induction L as [| x L IH]; [reflexivity |].
  cbn [map]; rewrite suml_cons; unfold count in *; simpl; destruct (p x); simpl; lia.
Qed.

Lemma suml_zero : forall {X} (L : list X), suml (map (fun _ => 0) L) = 0.
Proof. intros X L; induction L; [reflexivity | cbn [map]; rewrite suml_cons; assumption]. Qed.

Lemma suml_eqt : forall (ts : list ltype) (a : ltype) (f : ltype -> nat),
  NoDup ts -> In a ts -> suml (map (fun t => eqt t a * f t) ts) = f a.
Proof.
  intros ts a f Hnd Ha; induction ts as [| t ts IH]; [inversion Ha |].
  inversion Hnd as [| ? ? Hnt Hnd']; subst. cbn [map]; rewrite suml_cons. unfold eqt at 1.
  destruct (ltype_eq_dec t a) as [E | NE].
  - subst t. rewrite (suml_map_ext (fun t => eqt t a * f t) (fun _ => 0)).
    + rewrite suml_zero; lia.
    + intros t Ht; unfold eqt; destruct (ltype_eq_dec t a) as [E | NE]; [subst; contradiction | lia].
  - destruct Ha as [E | Ha]; [subst; contradiction |]. rewrite (IH Hnd' Ha); lia.
Qed.

Lemma trivial_row_sat : forall ts x, rowsat ts x trivial_row.
Proof. intros ts x; unfold rowsat, trivial_row; simpl; rewrite suml_zero; lia. Qed.

(** ** The setting *)

Section Model.
  Variable F : Family.
  Variable R : list nat.
  Hypothesis HU : Uniform 4 F.
  Hypothesis HD : Distinct F.
  Hypothesis Hno : ~ ContainsKSunflower 3 F.
  Hypothesis HR : In R F.

  Let D := DisjointFrom R F.
  Let V := points D.
  Let M := Others R F.

  Lemma R_nodup : NoDup R.
  Proof. destruct (member_uniform F HU R HR); assumption. Qed.

  Lemma R_len : length R = 4.
  Proof. destruct (member_uniform F HU R HR); assumption. Qed.

  Lemma M_in_F : forall S, In S M -> In S F.
  Proof. intros S HS; apply in_Others in HS as [HS _]; apply in_Meeting in HS; tauto. Qed.

  Lemma M_meets_R : forall S, In S M -> exists r, In r R /\ In r S.
  Proof.
    intros S HS; apply in_Others in HS as [HS _]; apply (meeting_point F R S HS).
  Qed.

  Lemma M_not_R : forall S, In S M -> S <> R.
  Proof. intros S HS E; apply in_Others in HS as [_ H]; apply H; subst; apply SetEq_refl. Qed.

  Lemma M_SetNoDup : SetNoDup M.
  Proof. unfold M, Others, Meeting; repeat apply SetNoDup_filter; exact HD. Qed.

  (** [V] and [R] are disjoint. *)
  Lemma V_R_disjoint : forall x, In x V -> ~ In x R.
  Proof. intros x HV HRx; exact (R_not_in_V F R x HRx HV). Qed.

  (** Labels of positions. *)
  Lemma nth_R_in : forall k, k < 4 -> In (nth k R 0) R.
  Proof. intros k Hk; apply nth_In; rewrite R_len; exact Hk. Qed.

  Lemma nth_R_inj : forall j k, j < 4 -> k < 4 -> nth j R 0 = nth k R 0 -> j = k.
  Proof.
    intros j k Hj Hk E. pose proof R_len as HL. pose proof R_nodup as HN.
    rewrite (NoDup_nth R 0) in HN; apply HN; lia.
  Qed.

  Lemma in_R_nth : forall x, In x R -> exists k, k < 4 /\ x = nth k R 0.
  Proof.
    intros x Hx. destruct (In_nth R x 0 Hx) as [k [Hk E]]. exists k; rewrite R_len in Hk; auto.
  Qed.

  Lemma lab_Subset_R : forall P, (forall k, In k P -> k < 4) -> Subset (lab R P) R.
  Proof. intros P HP x Hx; apply in_lab in Hx as [k [Hk E]]; subst; apply nth_R_in; auto. Qed.

  Lemma lab_NoDup : forall P, NoDup P -> (forall k, In k P -> k < 4) -> NoDup (lab R P).
  Proof.
    intros P HN HP; unfold lab; apply NoDup_map_inj; [| exact HN].
    intros j k Hj Hk E; apply nth_R_inj; auto.
  Qed.

  Lemma lab_prof_iff : forall S x, In x (lab R (prof R S)) <-> In x R /\ In x S.
  Proof.
    intros S x; rewrite in_lab; split.
    - intros [k [Hk E]]; apply in_prof in Hk as [Hk HkS]; subst; split; [apply nth_R_in; auto | exact HkS].
    - intros [HxR HxS]; destruct (in_R_nth x HxR) as [k [Hk E]]; exists k; split; [| exact E].
      apply in_prof; subst; auto.
  Qed.

  Lemma prof_pos : forall S k, In k (prof R S) -> k < 4.
  Proof. intros S k Hk; apply in_prof in Hk; tauto. Qed.

  (** Disjointness and set equality of profiles, read positionally. *)
  Lemma lab_Disjoint : forall P P',
    (forall k, In k P -> k < 4) -> (forall k, In k P' -> k < 4) ->
    (Disjoint P P' <-> Disjoint (lab R P) (lab R P')).
  Proof.
    intros P P' HP HP'; split.
    - intros Hd x H1 H2; apply in_lab in H1 as [j [Hj E1]]; apply in_lab in H2 as [k [Hk E2]]; subst.
      assert (j = k) by (apply nth_R_inj; auto). subst. exact (Hd k Hj Hk).
    - intros Hd k H1 H2. apply (Hd (nth k R 0)); apply in_lab; exists k; auto.
  Qed.

  Lemma lab_Subset : forall P P',
    (forall k, In k P -> k < 4) -> (forall k, In k P' -> k < 4) ->
    (Subset P P' <-> Subset (lab R P) (lab R P')).
  Proof.
    intros P P' HP HP'; split.
    - intros Hs x Hx; apply in_lab in Hx as [k [Hk E]]; subst; apply in_lab; exists k; auto.
    - intros Hs k Hk. assert (In (nth k R 0) (lab R P')) by (apply Hs; apply in_lab; exists k; auto).
      apply in_lab in H as [j [Hj E]]. assert (j = k) by (apply nth_R_inj; auto). subst; exact Hj.
  Qed.

  (** The profile of a member is nonempty. *)
  Lemma profile_nonempty : forall S, In S M -> 1 <= length (prof R S).
  Proof.
    intros S HS. destruct (M_meets_R S HS) as [r [HrR HrS]].
    destruct (in_R_nth r HrR) as [k [Hk E]].
    assert (In k (prof R S)) by (apply in_prof; subst; auto).
    destruct (prof R S); [inversion H | simpl; lia].
  Qed.

  Lemma trace_lab_NoDup : forall S, NoDup (tr V S ++ lab R (prof R S)).
  Proof.
    intros S. apply NoDup_app_disjoint; [apply tr_NoDup; apply points_NoDup | |].
    - apply lab_NoDup; [apply prof_NoDup | apply prof_pos].
    - intros x H1 H2; apply in_tr in H1; apply lab_prof_iff in H2; apply (V_R_disjoint x); tauto.
  Qed.

  Lemma trace_lab_incl : forall S, incl (tr V S ++ lab R (prof R S)) S.
  Proof.
    intros S x Hx; apply in_app_iff in Hx as [Hx | Hx]; [apply in_tr in Hx | apply lab_prof_iff in Hx]; tauto.
  Qed.

  (** Trace and profile together fit in the member. *)
  Lemma trace_profile_le4 : forall S, In S M -> length (tr V S) + length (prof R S) <= 4.
  Proof.
    intros S HS. destruct (member_uniform F HU S (M_in_F S HS)) as [HL HN].
    pose proof (NoDup_incl_length (trace_lab_NoDup S) (trace_lab_incl S)) as H.
    rewrite app_length, lab_length in H. lia.
  Qed.

  (** A member whose profile is all of [R] is [R]. *)
  Lemma full_profile_is_R : forall S, In S M -> length (prof R S) <= 3.
  Proof.
    intros S HS.
    destruct (le_lt_dec (length (prof R S)) 3) as [H | H]; [exact H | exfalso].
    assert (Hall : forall k, k < 4 -> In k (prof R S)).
    { intros k Hk.
      assert (Hle : length (prof R S) <= length POS).
      { apply NoDup_incl_length; [apply prof_NoDup | intros j Hj; apply in_prof in Hj as [Hj _]; unfold POS; simpl; lia]. }
      simpl in Hle.
      assert (E : length (prof R S) = 4) by lia.
      destruct (in_dec_nat k (prof R S)) as [Hin | Hnin]; [exact Hin | exfalso].
      assert (incl (prof R S) (rem_elt k POS)).
      { intros y Hy; apply in_rem_iff; split; [apply in_prof in Hy as [Hy _]; unfold POS; simpl; lia |].
        intro Eyk; subst; exact (Hnin Hy). }
      pose proof (NoDup_incl_length (prof_NoDup R S) H0) as H1.
      rewrite length_rem_elt_in in H1; [simpl in H1; lia | apply POS_NoDup | unfold POS; simpl; lia]. }
    assert (HRS : Subset R S).
    { intros x Hx; destruct (in_R_nth x Hx) as [k [Hk E]]; subst.
      pose proof (Hall k Hk) as Hk'; apply in_prof in Hk'; tauto. }
    destruct (member_uniform F HU S (M_in_F S HS)) as [HL HN].
    assert (HSR : SetEq S R).
    { split; [| exact HRS]. intros x Hx.
      destruct (in_dec_nat x R) as [| Hnot]; [assumption | exfalso].
      assert (incl (x :: R) S) by (intros y [Ey | Hy]; [subst; exact Hx | apply HRS; exact Hy]).
      assert (NoDup (x :: R)) by (constructor; [exact Hnot | apply R_nodup]).
      pose proof (NoDup_incl_length H1 H0) as H2. simpl in H2. rewrite HL in H2.
      pose proof R_len as HRl. lia. }
    apply in_Others in HS as [_ Hne]; exact (Hne HSR).
  Qed.

  (** Every member of [M] has a type in the list. *)
  Lemma typeof_in_types : forall S, In S M -> In (typeof V R S) (types D).
  Proof.
    intros S HS. unfold typeof, types. apply in_app_iff.
    assert (HP : In (prof R S) PROF).
    { apply in_PROF; split; [| apply profile_nonempty; exact HS].
      apply (filter_in_subs_le (fun k => memb (nth k R 0) S) POS 4).
      change (length (prof R S) <= 4). pose proof (full_profile_is_R S HS); lia. }
    destruct (list_eq_dec Nat.eq_dec (tr V S) []) as [E | NE].
    - right. rewrite E. apply in_map_iff. exists (prof R S); split; [reflexivity |].
      apply filter_In; split; [exact HP | apply Nat.leb_le; apply full_profile_is_R; exact HS].
    - left. apply in_flat_map. exists (tr V S); split.
      + unfold unwit; apply filter_In; split.
        * apply (tr_in_traces F R HU S); [apply in_Others in HS; tauto | exact NE].
        * apply negb_true_iff.
          destruct (witnessedb (tr V S) D) eqn:Ew; [| reflexivity].
          exfalso. apply (witnessed_no_member F R Hno S); [apply in_Others in HS; tauto | exact Ew].
      + apply in_map_iff. exists (prof R S); split; [reflexivity |].
        apply filter_In; split; [exact HP | apply Nat.leb_le; apply trace_profile_le4; exact HS].
  Qed.

  (** The type counts sum to [|M|]. *)
  Lemma tcount_sum : suml (map (tcount V R M) (types D)) = length M.
  Proof.
    unfold tcount. apply (count_by_keys ltype_eq_dec (typeof V R) (types D) M).
    - apply types_NoDup.
    - intros S HS; apply typeof_in_types; exact HS.
  Qed.

  Lemma Others_length : length M + 1 = length (Meeting R F).
  Proof.
    unfold M, Others.
    pose proof (count_partition (fun S => negb (seteqf S R)) (Meeting R F)) as Hp; unfold count in Hp.
    assert (length (filter (fun S => negb (negb (seteqf S R))) (Meeting R F)) = 1).
    { assert (Hin : forall S, In S (filter (fun S => negb (negb (seteqf S R))) (Meeting R F)) <-> S = R).
      { intros S; rewrite filter_In, negb_involutive; split.
        - intros [H1 H2]; apply seteqf_correct in H2.
          apply in_Meeting in H1 as [H1 _]. apply (SetNoDup_setEq_eq HD H1 HR H2).
        - intros E; subst S; split; [apply in_Meeting; split; [exact HR |] | apply seteqf_correct; apply SetEq_refl].
          intro Hd. destruct (member_nonempty F HU R HR) as [z Hz]. exact (Hd z Hz Hz). }
      assert (HND : NoDup (filter (fun S => negb (negb (seteqf S R))) (Meeting R F))).
      { apply NoDup_filter; apply SetNoDup_NoDup; unfold Meeting; apply SetNoDup_filter; exact HD. }
      destruct (filter (fun S => negb (negb (seteqf S R))) (Meeting R F)) as [| A [| B L]] eqn:E.
      - exfalso. exact (proj2 (Hin R) eq_refl).
      - reflexivity.
      - exfalso. assert (A = R) by (apply Hin; left; reflexivity).
        assert (B = R) by (apply Hin; right; left; reflexivity).
        subst. inversion HND as [| ? ? Hn _]; apply Hn; left; reflexivity. }
    lia.
  Qed.

  (** ** Lifting through a fixed part

      Members containing a fixed set [X] have outer parts [S ∖ X] that
      form a distinct, [(4 − |X|)]-uniform, sunflower-free family, so
      their number is bounded by [g(4 − |X|)].  This generalises
      [LinkLP.trace_class_cap] from a canonical trace to any [X]. *)

  Definition subsetf (X S : list nat) : bool := forallb (fun x => membf x S) X.

  Lemma subsetf_correct : forall X S, subsetf X S = true <-> Subset X S.
  Proof.
    intros X S; unfold subsetf, Subset; rewrite forallb_forall; split; intros H x Hx;
      [apply membf_true_iff; apply H; exact Hx | apply membf_true_iff; apply H; exact Hx].
  Qed.

  Lemma superset_count_le :
    forall X Mb, NoDup X -> length X <= 3 -> GAtMost (4 - length X) Mb ->
      count (subsetf X) F <= Mb.
  Proof.
    intros X Mb HXnd HX3 Hg.
    set (MX := filter (subsetf X) F).
    assert (HMX : forall S, In S MX -> In S F /\ Subset X S).
    { intros S HS; unfold MX in HS; apply filter_In in HS as [H1 H2]; split; [exact H1 | apply subsetf_correct; exact H2]. }
    change (length MX <= Mb).
    set (O := map (outer X) MX).
    assert (HOU : Uniform (4 - length X) O).
    { unfold Uniform; apply Forall_forall; intros Y HY.
      apply in_map_iff in HY as [S [E HS]]; subst Y.
      destruct (HMX S HS) as [HSF HXS].
      destruct (member_uniform F HU S HSF) as [HL HN].
      split; [| apply NoDup_filter; exact HN].
      pose proof (outer_length X S HXnd HN HXS). lia. }
    assert (HOD : Distinct O).
    { unfold O; apply SetNoDup_map.
      - unfold MX; apply SetNoDup_filter; exact HD.
      - intros a b Ha Hb [H1 H2]; destruct (HMX a Ha) as [_ HXa]; destruct (HMX b Hb) as [_ HXb].
        split; intros x Hx.
        + destruct (in_dec_nat x X) as [HxX | HxX]; [apply HXb; exact HxX |].
          assert (In x (outer X a)) by (apply in_outer; tauto).
          apply H1 in H; apply in_outer in H; tauto.
        + destruct (in_dec_nat x X) as [HxX | HxX]; [apply HXa; exact HxX |].
          assert (In x (outer X b)) by (apply in_outer; tauto).
          apply H2 in H; apply in_outer in H; tauto. }
    assert (HOno : ~ ContainsKSunflower 3 O).
    { intros [Q [HQO [HQ3 [core HQ]]]].
      set (pick := fun A => match find (fun S => seteqb A (outer X S)) MX with
                            | Some S' => S' | None => [] end).
      assert (Hpick : forall A, In A Q -> In (pick A) MX /\ SetEq A (outer X (pick A))).
      { intros A HA. destruct (HQO A HA) as [B [HB HAB]].
        apply in_map_iff in HB as [S [HBS HS]]; subst B.
        unfold pick. destruct (find (fun S => seteqb A (outer X S)) MX) eqn:Ef.
        - apply find_some in Ef as [H1 H2]. apply seteqb_correct in H2. tauto.
        - exfalso. pose proof (find_none _ _ Ef S HS) as H'.
          cbv beta in H'. apply seteqb_correct in HAB. rewrite HAB in H'; discriminate. }
      apply Hno.
      apply (@ContainsKSunflower_of_incl 3 (map pick Q) F (X ++ core)).
      - intros Y HY; apply in_map_iff in HY as [A [E HA]]; subst Y.
        apply HMX; apply Hpick; exact HA.
      - rewrite map_length; exact HQ3.
      - destruct HQ as [HQnd HQcore]. split.
        + apply SetNoDup_map; [exact HQnd |].
          intros A B HA HB HAB.
          destruct (Hpick A HA) as [_ EA]; destruct (Hpick B HB) as [_ EB].
          eapply SetEq_trans; [exact EA |].
          eapply SetEq_trans; [apply outer_SetEq; exact HAB | apply SetEq_sym; exact EB].
        + intros Y Z HY HZ Hne.
          apply in_map_iff in HY as [A [EY HA]]; apply in_map_iff in HZ as [B [EZ HB]]; subst Y Z.
          assert (HAB : A <> B) by (intro E; apply Hne; subst; reflexivity).
          specialize (HQcore A B HA HB HAB).
          destruct (Hpick A HA) as [HpA EA]; destruct (Hpick B HB) as [HpB EB].
          destruct (HMX _ HpA) as [_ HXA]; destruct (HMX _ HpB) as [_ HXB].
          split; intros x Hx.
          * apply in_inter_iff in Hx as [HxA HxB].
            apply in_app_iff.
            destruct (in_dec_nat x X) as [HxX | HxX]; [left; exact HxX | right].
            apply HQcore; apply in_inter_iff; split.
            -- apply EA; apply in_outer; tauto.
            -- apply EB; apply in_outer; tauto.
          * apply in_inter_iff. apply in_app_iff in Hx as [HxX | Hxc].
            -- split; [apply HXA | apply HXB]; exact HxX.
            -- apply HQcore in Hxc; apply in_inter_iff in Hxc as [HxA HxB].
               apply EA in HxA; apply in_outer in HxA.
               apply EB in HxB; apply in_outer in HxB. tauto. }
    assert (HOlen : length O = length MX) by (unfold O; apply map_length).
    rewrite <- HOlen. apply Hg; assumption.
  Qed.

  (** Two distinct members cannot both contain a 4-set. *)
  Lemma superset4_count_le :
    forall X, NoDup X -> length X = 4 -> count (subsetf X) F <= 1.
  Proof.
    intros X HXnd HX4. unfold count.
    assert (Hall : forall S, In S (filter (subsetf X) F) -> SetEq S X).
    { intros S HS; apply filter_In in HS as [HSF HXS]; apply subsetf_correct in HXS.
      destruct (member_uniform F HU S HSF) as [HL HN].
      split; [| exact HXS]. intros x Hx.
      destruct (in_dec_nat x X) as [| Hnot]; [assumption | exfalso].
      assert (incl (x :: X) S) by (intros y [Ey | Hy]; [subst; exact Hx | apply HXS; exact Hy]).
      assert (NoDup (x :: X)) by (constructor; assumption).
      pose proof (NoDup_incl_length H0 H) as H1; simpl in H1; lia. }
    assert (HND : SetNoDup (filter (subsetf X) F)) by (apply SetNoDup_filter; exact HD).
    destruct (filter (subsetf X) F) as [| A [| B L]]; [simpl; lia | simpl; lia | exfalso].
    inversion HND as [| ? ? Hn _]; subst. apply (Hn B (or_introl eq_refl)).
    eapply SetEq_trans; [apply Hall; left; reflexivity | apply SetEq_sym; apply Hall; right; left; reflexivity].
  Qed.

  (** ** The upper bounds on single types *)

  (** A member of type [(T, P)] contains [T ++ lab R P]. *)
  Lemma type_superset :
    forall S T P, typeof V R S = (T, P) -> Subset (T ++ lab R P) S.
  Proof.
    intros S T P E; unfold typeof in E; injection E; intros EP ET; subst.
    intros x Hx; apply (trace_lab_incl S); exact Hx.
  Qed.

  Lemma type_nodup :
    forall S T P, typeof V R S = (T, P) -> NoDup (T ++ lab R P).
  Proof.
    intros S T P E; unfold typeof in E; injection E; intros EP ET; subst. apply trace_lab_NoDup.
  Qed.

  (** A determined member is exactly its trace and profile. *)
  Lemma type_exact :
    forall S T P, In S M -> typeof V R S = (T, P) -> length T + length P = 4 ->
      Subset S (T ++ lab R P).
  Proof.
    intros S T P HS E HL.
    destruct (member_uniform F HU S (M_in_F S HS)) as [HSL HSN].
    apply NoDup_length_incl; [apply (type_nodup S T P E) | | apply (type_superset S T P E)].
    rewrite app_length, lab_length; lia.
  Qed.

  Lemma tcount_le_superset :
    forall T P, tcount V R M (T, P) <= count (subsetf (T ++ lab R P)) F.
  Proof.
    intros T P. unfold tcount, M, Others, Meeting, count.
    rewrite filter_filter_comm, filter_filter_comm.
    apply length_filter_impl. intros S HSF H.
    apply andb_true_iff in H as [H1 H2]; apply andb_true_iff in H1 as [H1 H3].
    unfold keyb in H1; destruct (ltype_eq_dec (typeof V R S) (T, P)) as [E | NE]; [| discriminate].
    apply subsetf_correct. apply (type_superset S T P E).
  Qed.

  (** The M0 caps at profile sizes 2 and 3 use that the outer parts are
      pairwise intersecting: two disjoint outer parts would make a
      sunflower with [R] and core [P]. *)
  Lemma m0_outer_intersecting :
    forall P S1 S2, In S1 M -> In S2 M -> S1 <> S2 ->
      typeof V R S1 = ([], P) -> typeof V R S2 = ([], P) ->
      ~ Disjoint (outer (lab R P) S1) (outer (lab R P) S2).
  Proof.
    intros P S1 S2 H1 H2 Hne E1 E2 Hd.
    set (PL := lab R P) in *.
    unfold typeof in E1, E2; injection E1; injection E2; intros EP2 ET2 EP1 ET1.
    assert (HP1 : forall x, In x S1 -> In x R -> In x PL) by (intros x Hx HxR; unfold PL; rewrite <- EP1; apply lab_prof_iff; tauto).
    assert (HP2 : forall x, In x S2 -> In x R -> In x PL) by (intros x Hx HxR; unfold PL; rewrite <- EP2; apply lab_prof_iff; tauto).
    assert (HPR : Subset PL R) by (intros x Hx; unfold PL in Hx; rewrite <- EP1 in Hx; apply lab_prof_iff in Hx; tauto).
    assert (HPS1 : Subset PL S1) by (intros x Hx; unfold PL in Hx; rewrite <- EP1 in Hx; apply lab_prof_iff in Hx; tauto).
    assert (HPS2 : Subset PL S2) by (intros x Hx; unfold PL in Hx; rewrite <- EP2 in Hx; apply lab_prof_iff in Hx; tauto).
    assert (HSR1 : ~ SetEq S1 R) by (apply in_Others in H1; tauto).
    assert (HSR2 : ~ SetEq S2 R) by (apply in_Others in H2; tauto).
    assert (HS12 : ~ SetEq S1 S2).
    { intro E; apply Hne; apply (SetNoDup_setEq_eq HD (M_in_F S1 H1) (M_in_F S2 H2) E). }
    apply Hno.
    apply (@ContainsKSunflower_of_incl 3 [S1; S2; R] F PL).
    - intros Y [E | [E | [E | []]]]; subst Y; [apply M_in_F; exact H1 | apply M_in_F; exact H2 | exact HR].
    - reflexivity.
    - split.
      + constructor.
        * intros Y [E | [E | []]] HE; subst Y; [exact (HS12 HE) | exact (HSR1 HE)].
        * constructor; [| constructor; [intros _ [] | constructor]].
          intros Y [E | []] HE; subst Y; exact (HSR2 HE).
      + assert (H12 : SetEq (inter S1 S2) PL).
        { split; intros x Hx.
          - apply in_inter_iff in Hx as [Hx1 Hx2].
            destruct (in_dec_nat x PL) as [| HxP]; [assumption | exfalso].
            apply (Hd x); apply in_outer; tauto.
          - apply in_inter_iff; split; [apply HPS1 | apply HPS2]; exact Hx. }
        assert (H1R : SetEq (inter S1 R) PL).
        { split; intros x Hx; [apply in_inter_iff in Hx as [Hx1 Hx2]; apply HP1; assumption |
                               apply in_inter_iff; split; [apply HPS1 | apply HPR]; exact Hx]. }
        assert (H2R : SetEq (inter S2 R) PL).
        { split; intros x Hx; [apply in_inter_iff in Hx as [Hx1 Hx2]; apply HP2; assumption |
                               apply in_inter_iff; split; [apply HPS2 | apply HPR]; exact Hx]. }
        intros Y Z [EY | [EY | [EY | []]]] [EZ | [EZ | [EZ | []]]] Hne'; subst Y Z;
          try (exfalso; apply Hne'; reflexivity).
        * exact H12.
        * exact H1R.
        * eapply SetEq_trans; [apply inter_comm_SetEq | exact H12].
        * exact H2R.
        * eapply SetEq_trans; [apply inter_comm_SetEq | exact H1R].
        * eapply SetEq_trans; [apply inter_comm_SetEq | exact H2R].
  Qed.

  (** Lifting a sunflower of outer parts back to [F]. *)
  Lemma outer_sunflower_lift :
    forall (X : list nat) (MX : Family),
      (forall S, In S MX -> In S F /\ Subset X S) ->
      ContainsKSunflower 3 (map (outer X) MX) -> False.
  Proof.
    intros X MX HMX [Q [HQO [HQ3 [core HQ]]]].
    set (pick := fun A => match find (fun S => seteqb A (outer X S)) MX with
                          | Some S' => S' | None => [] end).
    assert (Hpick : forall A, In A Q -> In (pick A) MX /\ SetEq A (outer X (pick A))).
    { intros A HA. destruct (HQO A HA) as [B [HB HAB]].
      apply in_map_iff in HB as [S [HBS HS]]; subst B.
      unfold pick. destruct (find (fun S => seteqb A (outer X S)) MX) eqn:Ef.
      - apply find_some in Ef as [H1 H2]. apply seteqb_correct in H2. tauto.
      - exfalso. pose proof (find_none _ _ Ef S HS) as H'.
        cbv beta in H'. apply seteqb_correct in HAB. rewrite HAB in H'; discriminate. }
    apply Hno.
    apply (@ContainsKSunflower_of_incl 3 (map pick Q) F (X ++ core)).
    - intros Y HY; apply in_map_iff in HY as [A [E HA]]; subst Y.
      apply HMX; apply Hpick; exact HA.
    - rewrite map_length; exact HQ3.
    - destruct HQ as [HQnd HQcore]. split.
      + apply SetNoDup_map; [exact HQnd |].
        intros A B HA HB HAB.
        destruct (Hpick A HA) as [_ EA]; destruct (Hpick B HB) as [_ EB].
        eapply SetEq_trans; [exact EA |].
        eapply SetEq_trans; [apply outer_SetEq; exact HAB | apply SetEq_sym; exact EB].
      + intros Y Z HY HZ Hne.
        apply in_map_iff in HY as [A [EY HA]]; apply in_map_iff in HZ as [B [EZ HB]]; subst Y Z.
        assert (HAB : A <> B) by (intro E; apply Hne; subst; reflexivity).
        specialize (HQcore A B HA HB HAB).
        destruct (Hpick A HA) as [HpA EA]; destruct (Hpick B HB) as [HpB EB].
        destruct (HMX _ HpA) as [_ HXA]; destruct (HMX _ HpB) as [_ HXB].
        split; intros x Hx.
        * apply in_inter_iff in Hx as [HxA HxB].
          apply in_app_iff.
          destruct (in_dec_nat x X) as [HxX | HxX]; [left; exact HxX | right].
          apply HQcore; apply in_inter_iff; split.
          -- apply EA; apply in_outer; tauto.
          -- apply EB; apply in_outer; tauto.
        * apply in_inter_iff. apply in_app_iff in Hx as [HxX | Hxc].
          -- split; [apply HXA | apply HXB]; exact HxX.
          -- apply HQcore in Hxc; apply in_inter_iff in Hxc as [HxA HxB].
             apply EA in HxA; apply in_outer in HxA.
             apply EB in HxB; apply in_outer in HxB. tauto.
  Qed.

  Lemma m0_count_le :
    forall P N, In P PROF -> 2 <= length P -> length P <= 3 -> IotaAtMost (4 - length P) N ->
      tcount V R M ([], P) <= N.
  Proof.
    intros P N HPP HP2 HP3 Hiota.
    set (PL := lab R P).
    set (MP := filter (keyb ltype_eq_dec (typeof V R) ([], P)) M).
    assert (HMP : forall S, In S MP -> In S M /\ typeof V R S = ([], P)).
    { intros S HS; unfold MP in HS; apply filter_In in HS as [H1 H2]; split; [exact H1 |].
      unfold keyb in H2; destruct (ltype_eq_dec (typeof V R S) ([], P)); [assumption | discriminate]. }
    change (length MP <= N).
    assert (HPnd : NoDup PL) by (apply lab_NoDup; [apply in_PROF_NoDup; exact HPP | intros k Hk; apply (in_PROF_pos P k HPP Hk)]).
    assert (HPL : length PL = length P) by apply lab_length.
    assert (HPsub : forall S, In S MP -> Subset PL S).
    { intros S HS x Hx; destruct (HMP S HS) as [_ E]; unfold typeof in E; injection E; intros EP _.
      unfold PL in Hx; rewrite <- EP in Hx; apply lab_prof_iff in Hx; tauto. }
    set (O := map (outer PL) MP).
    assert (HOlen : length O = length MP) by (unfold O; apply map_length).
    rewrite <- HOlen. apply Hiota.
    - unfold Uniform; apply Forall_forall; intros Y HY.
      apply in_map_iff in HY as [S [E HS]]; subst Y.
      destruct (HMP S HS) as [HSM _].
      destruct (member_uniform F HU S (M_in_F S HSM)) as [HL HN].
      split; [| apply NoDup_filter; exact HN].
      pose proof (outer_length PL S HPnd HN (HPsub S HS)). lia.
    - unfold O; apply SetNoDup_map.
      + unfold MP; apply SetNoDup_filter; apply M_SetNoDup.
      + intros a b Ha Hb [H1 H2]; split; intros x Hx.
        * destruct (in_dec_nat x PL) as [HxP | HxP]; [apply (HPsub b Hb); exact HxP |].
          assert (In x (outer PL a)) by (apply in_outer; tauto).
          apply H1 in H; apply in_outer in H; tauto.
        * destruct (in_dec_nat x PL) as [HxP | HxP]; [apply (HPsub a Ha); exact HxP |].
          assert (In x (outer PL b)) by (apply in_outer; tauto).
          apply H2 in H; apply in_outer in H; tauto.
    - intros A B HA HB Hd.
      apply in_map_iff in HA as [S1 [E1 H1]]; apply in_map_iff in HB as [S2 [E2 H2]]; subst A B.
      destruct (HMP S1 H1) as [HS1 T1]; destruct (HMP S2 H2) as [HS2 T2].
      destruct (list_eq_dec Nat.eq_dec S1 S2) as [E | NE].
      + subst S2. destruct (member_uniform F HU S1 (M_in_F S1 HS1)) as [HL HN].
        pose proof (outer_length PL S1 HPnd HN (HPsub S1 H1)).
        destruct (outer PL S1) as [| z o] eqn:Eo; [simpl in H; lia |].
        exact (Hd z (or_introl eq_refl) (or_introl eq_refl)).
      + exact (m0_outer_intersecting P S1 S2 HS1 HS2 NE T1 T2 Hd).
    - intro HK. apply (outer_sunflower_lift PL MP); [| exact HK].
      intros S HS; split; [apply M_in_F; apply HMP; exact HS | apply HPsub; exact HS].
  Qed.

  (** Every type count respects its upper bound. *)
  Theorem tcount_le_ub : forall t, In t (types D) -> tcount V R M t <= ub_of t.
  Proof.
    intros [T P] Ht. unfold types in Ht; apply in_app_iff in Ht as [Ht | Ht].
    - (* M1 *)
      apply in_flat_map in Ht as [T' [HT' Ht]]; apply in_map_iff in Ht as [P' [E HP']].
      injection E; intros; subst P' T'.
      apply filter_In in HP' as [HP' Hle]; apply Nat.leb_le in Hle.
      assert (HTne : T <> []).
      { intro E0; subst; unfold unwit in HT'; apply filter_In in HT' as [HT' _];
        apply in_traces_length in HT'; simpl in HT'; lia. }
      assert (HTnd : NoDup T).
      { unfold unwit in HT'; apply filter_In in HT' as [HT' _]; apply in_traces in HT' as [HT' _].
        apply (subs_le_elem_NoDup 3 V T (points_NoDup D) HT'). }
      assert (HPnd : NoDup (lab R P)).
      { apply lab_NoDup; [apply in_PROF_NoDup; exact HP' | intros k Hk; apply (in_PROF_pos P k HP' Hk)]. }
      assert (HTP : NoDup (T ++ lab R P)).
      { apply NoDup_app_disjoint; [exact HTnd | exact HPnd |].
        intros x H1 H2. unfold unwit in HT'; apply filter_In in HT' as [HT' _]; apply in_traces in HT' as [HT' _].
        apply (subs_le_Subset 3 V T HT') in H1.
        apply (lab_Subset_R P (fun k Hk => in_PROF_pos P k HP' Hk)) in H2. exact (V_R_disjoint x H1 H2). }
      assert (Hlen : length (T ++ lab R P) = length T + length P) by (rewrite app_length, lab_length; reflexivity).
      assert (HP1 : 1 <= length P) by (apply in_PROF in HP'; tauto).
      pose proof (tcount_le_superset T P) as Hs.
      assert (HT1 : 1 <= length T) by (destruct T; [exfalso; apply HTne; reflexivity | simpl; lia]).
      assert (HT3 : length T <= 3).
      { unfold unwit in HT'; apply filter_In in HT' as [HT' _]; apply in_traces_length in HT'; lia. }
      unfold ub_of. destruct T as [| t0 T0]; [exfalso; apply HTne; reflexivity |].
      remember (4 - (length (t0 :: T0) + length P)) as e eqn:Ee.
      destruct e as [| [| e']].
      + pose proof (superset4_count_le ((t0 :: T0) ++ lab R P) HTP ltac:(lia)). lia.
      + pose proof (superset_count_le ((t0 :: T0) ++ lab R P) 2 HTP ltac:(lia)) as H.
        replace (4 - length ((t0 :: T0) ++ lab R P)) with 1 in H by lia.
        pose proof (H g_one_at_most_two). lia.
      + pose proof (superset_count_le ((t0 :: T0) ++ lab R P) 6 HTP ltac:(lia)) as H.
        replace (4 - length ((t0 :: T0) ++ lab R P)) with 2 in H by lia.
        pose proof (H g_two_at_most_six). lia.
    - (* M0 *)
      apply in_map_iff in Ht as [P' [E HP']]; injection E; intros; subst P' T.
      apply filter_In in HP' as [HP' Hle]; apply Nat.leb_le in Hle.
      assert (HP1 : 1 <= length P) by (apply in_PROF in HP'; tauto).
      assert (HPnd : NoDup (lab R P)).
      { apply lab_NoDup; [apply in_PROF_NoDup; exact HP' | intros k Hk; apply (in_PROF_pos P k HP' Hk)]. }
      unfold ub_of.
      destruct (length P) as [| [| [| [| n]]]] eqn:EL; try lia.
      + pose proof (tcount_le_superset [] P) as Hs; simpl in Hs.
        pose proof (superset_count_le (lab R P) 26 HPnd ltac:(rewrite lab_length; lia)) as H.
        rewrite lab_length, EL in H. pose proof (H g_three_at_most_26). lia.
      + pose proof (m0_count_le P 3 HP' ltac:(lia) ltac:(lia)) as H. rewrite EL in H.
        apply H. exact iota_two_at_most_three.
      + pose proof (m0_count_le P 1 HP' ltac:(lia) ltac:(lia)) as H. rewrite EL in H.
        apply H. exact iota_one_at_most_one.
  Qed.

  (** ** The rows for the actual counts *)

  Hypothesis Hmax : forall C, In C F -> length (DisjointFrom C F) <= length D.

  Lemma row_sum : forall (g : ltype -> nat),
    suml (map (fun t => g t * tcount V R M t) (types D)) = suml (map (fun S => g (typeof V R S)) M).
  Proof.
    intros g. unfold tcount. apply (count_by_keys_weighted ltype_eq_dec (typeof V R)).
    - apply types_NoDup.
    - intros S HS; apply typeof_in_types; exact HS.
  Qed.

  Lemma count_M_le : forall p : list nat -> bool, p R = true -> count p M + 1 <= count p (Meeting R F).
  Proof.
    intros p HpR. unfold count.
    assert (HND : NoDup (R :: filter p M)).
    { constructor; [intro H; apply filter_In in H as [H _]; exact (M_not_R R H eq_refl) |].
      apply NoDup_filter; apply SetNoDup_NoDup; apply M_SetNoDup. }
    assert (Hincl : incl (R :: filter p M) (filter p (Meeting R F))).
    { intros S [E | HS].
      - subst S; apply filter_In; split; [| exact HpR].
        apply in_Meeting; split; [exact HR |].
        intro Hd; destruct (member_nonempty F HU R HR) as [z Hz]; exact (Hd z Hz Hz).
      - apply filter_In in HS as [HS Hp]; apply filter_In; split; [apply in_Others in HS; tauto | exact Hp]. }
    pose proof (NoDup_incl_length HND Hincl) as H; simpl in H; lia.
  Qed.

  Lemma count_Meeting_le_F : forall p, count p (Meeting R F) <= count p F.
  Proof.
    intros p; unfold count, Meeting; rewrite filter_filter_comm; apply length_filter_impl.
    intros S _ H; apply andb_true_iff in H; tauto.
  Qed.

  Lemma tr_V_R : tr V R = [].
  Proof.
    destruct (tr V R) as [| z l] eqn:E; [reflexivity | exfalso].
    assert (In z (tr V R)) by (rewrite E; left; reflexivity).
    apply in_tr in H as [H1 H2]; exact (V_R_disjoint z H1 H2).
  Qed.

  Lemma member_of_type : forall a, 1 <= tcount V R M a -> exists Sa, In Sa M /\ typeof V R Sa = a.
  Proof.
    intros a Hpos. unfold tcount, count in Hpos.
    destruct (filter (keyb ltype_eq_dec (typeof V R) a) M) as [| Sa L] eqn:E; [simpl in Hpos; lia |].
    assert (In Sa (filter (keyb ltype_eq_dec (typeof V R) a) M)) by (rewrite E; left; reflexivity).
    apply filter_In in H as [H1 H2]; unfold keyb in H2.
    destruct (ltype_eq_dec (typeof V R Sa) a); [eauto | discriminate].
  Qed.

  (** Per trace. *)
  Lemma cap_row : forall T, In T (unwit D) ->
    suml (map (fun t => Nat.b2n (leqb (fst t) T) * tcount V R M t) (types D)) <= cap T.
  Proof.
    intros T HT. rewrite row_sum, suml_b2n.
    assert (HT' : In T (traces V)) by (unfold unwit in HT; apply filter_In in HT; tauto).
    pose proof (trace_class_cap F R HU HD Hno T HT') as H.
    eapply Nat.le_trans; [| exact H].
    unfold count, M, Others. rewrite filter_filter_comm. apply length_filter_impl.
    intros S _ H'. apply andb_true_iff in H' as [H1 _]. unfold keyb; unfold leqb in H1; exact H1.
  Qed.

  (** Per link member. *)
  Lemma link_row : forall C, In C D ->
    suml (map (fun t => Nat.b2n (disjf (fst t) C) * tcount V R M t) (types D)) + 1 <= length D.
  Proof.
    intros C HC. rewrite row_sum, suml_b2n.
    assert (HCF : In C F) by (apply in_DisjointFrom in HC; tauto).
    pose proof (link_constraint F R C HC) as H. fold D V in H.
    pose proof (Hmax C HCF) as H0.
    pose proof (count_M_le (fun S => disjf (tr V S) C)) as H2.
    assert (H3 : disjf (tr V R) C = true) by (rewrite tr_V_R; reflexivity).
    specialize (H2 H3).
    change (count (fun S => disjf (tr V S) C) M + 1 <= length D). lia.
  Qed.

  (** Per star. *)
  Lemma star_row : forall k, k < 4 ->
    suml (map (fun t => Nat.b2n (membf k (snd t)) * tcount V R M t) (types D)) + 1 <= 26.
  Proof.
    intros k Hk. rewrite row_sum, suml_b2n.
    set (r := nth k R 0).
    assert (HrR : In r R) by (apply nth_R_in; exact Hk).
    assert (Hr3 : count (subsetf [r]) F <= 26).
    { pose proof (superset_count_le [r] 26 ltac:(constructor; [intros [] | constructor]) ltac:(simpl; lia)) as H.
      simpl in H. apply H. exact g_three_at_most_26. }
    pose proof (count_M_le (fun S => membf k (prof R S))) as H1.
    assert (HpR : membf k (prof R R) = true) by (apply membf_true_iff; apply in_prof; split; [exact Hk | exact HrR]).
    specialize (H1 HpR).
    pose proof (count_Meeting_le_F (fun S => membf k (prof R S))) as H2.
    assert (H3 : count (fun S => membf k (prof R S)) F <= count (subsetf [r]) F).
    { unfold count; apply length_filter_impl; intros S _ H. apply membf_true_iff in H; apply in_prof in H as [_ H].
      apply subsetf_correct; intros y [E | []]; subst y; exact H. }
    change (count (fun S => membf k (prof R S)) M + 1 <= 26). lia.
  Qed.

  (** Determined members. *)
  Lemma det_disjoint : forall Sa S, In Sa M -> In S M ->
    length (fst (typeof V R Sa)) + length (snd (typeof V R Sa)) = 4 ->
    detdis (typeof V R Sa) (typeof V R S) = true -> Disjoint Sa S.
  Proof.
    intros Sa S HSa HS HL Hd x HxA HxS.
    unfold detdis in Hd; apply andb_true_iff in Hd as [H1 H2]; apply disjf_correct in H1; apply disjf_correct in H2.
    simpl in H1, H2, HL.
    pose proof (type_exact Sa (tr V Sa) (prof R Sa) HSa eq_refl HL x HxA) as Hx.
    apply in_app_iff in Hx as [Hx | Hx].
    - apply in_tr in Hx as [HxV _]. apply (H1 x); [apply in_tr; tauto | apply in_tr; tauto].
    - apply lab_prof_iff in Hx as [HxR _]. destruct (in_R_nth x HxR) as [k [Hk E]].
      apply (H2 k); apply in_prof; subst; auto.
  Qed.

  Lemma det_link_disjoint : forall Sa C, In Sa M -> In C D ->
    length (fst (typeof V R Sa)) + length (snd (typeof V R Sa)) = 4 ->
    disjf (fst (typeof V R Sa)) C = true -> Disjoint Sa C.
  Proof.
    intros Sa C HSa HC HL Hd x HxA HxC. apply disjf_correct in Hd. simpl in Hd, HL.
    pose proof (type_exact Sa (tr V Sa) (prof R Sa) HSa eq_refl HL x HxA) as Hx.
    apply in_app_iff in Hx as [Hx | Hx].
    - exact (Hd x Hx HxC).
    - apply lab_prof_iff in Hx as [HxR _]. apply in_DisjointFrom in HC as [_ HdC]. exact (HdC x HxR HxC).
  Qed.

  Lemma det_row : forall a, length (fst a) + length (snd a) = 4 -> 1 <= tcount V R M a ->
    suml (map (fun t => Nat.b2n (detdis a t) * tcount V R M t) (types D))
      + count (fun C => disjf (fst a) C) D <= length D.
  Proof.
    intros a HL Hpos. rewrite row_sum, suml_b2n.
    destruct (member_of_type a Hpos) as [Sa [HSa Ea]]. subst a.
    set (L := filter (fun S => detdis (typeof V R Sa) (typeof V R S)) M
              ++ filter (fun C => disjf (fst (typeof V R Sa)) C) D).
    assert (HLlen : length L = count (fun S => detdis (typeof V R Sa) (typeof V R S)) M
                               + count (fun C => disjf (fst (typeof V R Sa)) C) D)
      by (unfold L, count; apply app_length).
    rewrite <- HLlen.
    assert (HND : NoDup L).
    { unfold L; apply NoDup_app_disjoint.
      - apply NoDup_filter; apply SetNoDup_NoDup; apply M_SetNoDup.
      - apply NoDup_filter; apply SetNoDup_NoDup; unfold D, DisjointFrom; apply SetNoDup_filter; exact HD.
      - intros S H1 H2; apply filter_In in H1 as [H1 _]; apply filter_In in H2 as [H2 _].
        destruct (M_meets_R S H1) as [r [HrR HrS]]. apply in_DisjointFrom in H2 as [_ Hd]. exact (Hd r HrR HrS). }
    assert (Hincl : incl L (DisjointFrom Sa F)).
    { intros S HS; unfold L in HS; apply in_app_iff in HS as [HS | HS];
        apply filter_In in HS as [HS Hp]; apply in_DisjointFrom; split.
      - apply M_in_F; exact HS.
      - apply (det_disjoint Sa S HSa HS HL Hp).
      - apply in_DisjointFrom in HS; tauto.
      - apply (det_link_disjoint Sa S HSa HS HL Hp). }
    pose proof (NoDup_incl_length HND Hincl). pose proof (Hmax Sa (M_in_F Sa HSa)). lia.
  Qed.

  (** Exclusions. *)
  Lemma three_sunflower : forall A B C core, In A F -> In B F -> In C F ->
    ~ SetEq A B -> ~ SetEq A C -> ~ SetEq B C ->
    SetEq (inter A B) core -> SetEq (inter A C) core -> SetEq (inter B C) core -> False.
  Proof.
    intros A B C core HA HB HC NAB NAC NBC IAB IAC IBC. apply Hno.
    apply (@ContainsKSunflower_of_incl 3 [A; B; C] F core).
    - intros Y [E | [E | [E | []]]]; subst Y; assumption.
    - reflexivity.
    - split.
      + constructor.
        * intros Y [E | [E | []]] HE; subst Y; [exact (NAB HE) | exact (NAC HE)].
        * constructor; [| constructor; [intros _ [] | constructor]].
          intros Y [E | []] HE; subst Y; exact (NBC HE).
      + intros Y Z [EY | [EY | [EY | []]]] [EZ | [EZ | [EZ | []]]] Hne; subst Y Z;
          try (exfalso; apply Hne; reflexivity); try assumption;
          (eapply SetEq_trans; [apply inter_comm_SetEq | assumption]).
  Qed.

  Lemma inter_R : forall S, SetEq (inter S R) (lab R (prof R S)).
  Proof.
    intros S; split; intros x Hx; [apply in_inter_iff in Hx; apply lab_prof_iff; tauto
                                 | apply lab_prof_iff in Hx; apply in_inter_iff; tauto].
  Qed.

  Lemma inter_C : forall S C, In C D -> SetEq (inter S C) (interb (tr V S) C).
  Proof.
    intros S C HC; split; intros x Hx.
    - apply in_inter_iff in Hx as [H1 H2]; apply in_interb; split; [| exact H2].
      apply in_tr; split; [apply (member_Subset_points D C HC); exact H2 | exact H1].
    - apply in_interb in Hx as [H1 H2]; apply in_tr in H1; apply in_inter_iff; tauto.
  Qed.

  Lemma lab_SetEq : forall P P', SetEq P P' -> SetEq (lab R P) (lab R P').
  Proof.
    intros P P' [H1 H2]; split; intros x Hx; apply in_lab in Hx as [k [Hk E]]; apply in_lab; exists k; auto.
  Qed.

  Lemma inter_det : forall Sa Sb, In Sa M -> In Sb M ->
    length (fst (typeof V R Sa)) + length (snd (typeof V R Sa)) = 4 ->
    SetEq (inter Sa Sb) (interb (tr V Sa) (tr V Sb) ++ lab R (interb (prof R Sa) (prof R Sb))).
  Proof.
    intros Sa Sb HSa HSb HL; simpl in HL. split; intros x Hx.
    - apply in_inter_iff in Hx as [HxA HxB].
      pose proof (type_exact Sa (tr V Sa) (prof R Sa) HSa eq_refl HL x HxA) as Hx.
      apply in_app_iff; apply in_app_iff in Hx as [Hx | Hx].
      + left; apply in_interb; split; [exact Hx | apply in_tr in Hx; apply in_tr; tauto].
      + right. apply in_lab in Hx as [k [Hk E]]; apply in_lab; exists k; split; [| exact E].
        apply in_interb; split; [exact Hk |]. apply in_prof in Hk as [Hk _]; apply in_prof; subst; auto.
    - apply in_inter_iff. apply in_app_iff in Hx as [Hx | Hx].
      + apply in_interb in Hx as [H1 H2]; apply in_tr in H1; apply in_tr in H2; tauto.
      + apply in_lab in Hx as [k [Hk E]]; apply in_interb in Hk as [H1 H2];
          apply in_prof in H1; apply in_prof in H2; subst; tauto.
  Qed.

  Lemma not_SetEq_M_D : forall S C, In S M -> In C D -> ~ SetEq S C.
  Proof.
    intros S C HS HC [H1 _]. destruct (M_meets_R S HS) as [r [HrR HrS]].
    apply in_DisjointFrom in HC as [_ Hd]. exact (Hd r HrR (H1 r HrS)).
  Qed.

  Lemma excl_row : forall a b, a <> b -> length (fst a) + length (snd a) = 4 ->
    exclb D a b = true -> 1 <= tcount V R M a -> tcount V R M b = 0.
  Proof.
    intros a b Hab HL Hx Hpos.
    destruct (member_of_type a Hpos) as [Sa [HSa Ea]].
    destruct (tcount V R M b) as [| nb] eqn:Eb; [reflexivity | exfalso].
    destruct (member_of_type b ltac:(lia)) as [Sb [HSb Eb']].
    assert (Hne : ~ SetEq Sa Sb).
    { intro E; apply Hab; rewrite <- Ea, <- Eb'; apply typeof_SetEq; exact E. }
    assert (HaF : In Sa F) by (apply M_in_F; exact HSa).
    assert (HbF : In Sb F) by (apply M_in_F; exact HSb).
    assert (HaR : ~ SetEq Sa R) by (apply in_Others in HSa; tauto).
    assert (HbR : ~ SetEq Sb R) by (apply in_Others in HSb; tauto).
    pose proof (inter_det Sa Sb HSa HSb ltac:(rewrite Ea; exact HL)) as Hab'.
    subst a b. unfold exclb, typeof in Hx, HL. cbn [fst snd] in Hx, HL.
    apply orb_true_iff in Hx as [Hx | Hx]; [apply orb_true_iff in Hx as [Hx | Hx] |].
    - (* with R *)
      apply andb_true_iff in Hx as [H1 H2]; apply seteqf_correct in H1; apply nilb_true_iff in H2.
      rewrite H2 in Hab'. simpl in Hab'.
      apply (three_sunflower Sa Sb R (lab R (prof R Sa)) HaF HbF HR Hne HaR HbR).
      + eapply SetEq_trans; [exact Hab' |]. apply lab_SetEq.
        split; intros k Hk; [apply in_interb in Hk; tauto | apply in_interb; split; [exact Hk | apply H1; exact Hk]].
      + apply inter_R.
      + eapply SetEq_trans; [apply inter_R |]. apply lab_SetEq; apply SetEq_sym; exact H1.
    - (* with a link member *)
      apply andb_true_iff in Hx as [H1 H2]; apply nilb_true_iff in H1.
      apply existsb_exists in H2 as [C [HC H2]]; apply andb_true_iff in H2 as [H2 H3].
      apply seteqf_correct in H2; apply seteqf_correct in H3.
      rewrite H1 in Hab'. simpl in Hab'. rewrite app_nil_r in Hab'.
      assert (HCF : In C F) by (apply in_DisjointFrom in HC; tauto).
      apply (three_sunflower Sa Sb C (interb (tr V Sa) (tr V Sb)) HaF HbF HCF Hne
               (not_SetEq_M_D Sa C HSa HC) (not_SetEq_M_D Sb C HSb HC)).
      + exact Hab'.
      + eapply SetEq_trans; [apply inter_C; exact HC | exact H2].
      + eapply SetEq_trans; [apply inter_C; exact HC | exact H3].
    - (* three pairwise disjoint *)
      apply andb_true_iff in Hx as [H1 H2]; apply andb_true_iff in H1 as [H1 H1'].
      apply nilb_true_iff in H1; apply nilb_true_iff in H1'.
      apply existsb_exists in H2 as [C [HC H2]]; apply andb_true_iff in H2 as [H2 H3].
      apply disjf_correct in H2; apply disjf_correct in H3.
      rewrite H1, H1' in Hab'. simpl in Hab'.
      assert (HCF : In C F) by (apply in_DisjointFrom in HC; tauto).
      apply (three_sunflower Sa Sb C [] HaF HbF HCF Hne
               (not_SetEq_M_D Sa C HSa HC) (not_SetEq_M_D Sb C HSb HC)).
      + exact Hab'.
      + eapply SetEq_trans; [apply inter_C; exact HC |].
        split; intros x Hx; [apply in_interb in Hx as [Hx1 Hx2]; exfalso; exact (H2 x Hx1 Hx2) | inversion Hx].
      + eapply SetEq_trans; [apply inter_C; exact HC |].
        split; intros x Hx; [apply in_interb in Hx as [Hx1 Hx2]; exfalso; exact (H3 x Hx1 Hx2) | inversion Hx].
  Qed.

  (** A determined type in the list has cap 1. *)
  Lemma ub_of_det : forall a, In a (types D) -> dett a = true -> ub_of a = 1.
  Proof.
    intros [T P] Ha Hd. unfold dett in Hd; simpl in Hd; apply Nat.eqb_eq in Hd.
    unfold types in Ha; apply in_app_iff in Ha as [Ha | Ha].
    - apply in_flat_map in Ha as [T' [HT' Ha]]; apply in_map_iff in Ha as [P' [E _]]; injection E; intros; subst.
      destruct T as [| t0 T0].
      + exfalso. unfold unwit in HT'; apply filter_In in HT' as [HT' _]; apply in_traces_length in HT'; simpl in HT'; lia.
      + unfold ub_of. replace (4 - (length (t0 :: T0) + length P)) with 0 by lia. reflexivity.
    - apply in_map_iff in Ha as [P' [E HP']]; injection E; intros; subst.
      apply filter_In in HP' as [_ Hle]; apply Nat.leb_le in Hle; simpl in Hd; lia.
  Qed.

  Definition bigof (ts : list ltype) : nat := suml (map ub_of ts) + 1.

  (** Every tagged row holds for the actual counts. *)
  Theorem rows_valid : forall tg, rowsat (types D) (tcount V R M) (rowc D (unwit D) (types D) (bigof (types D)) tg).
  Proof.
    intros tg. unfold rowc. destruct tg as [T | C | k | i | i j].
    - destruct (inlb T (unwit D)) eqn:E; [| apply trivial_row_sat].
      apply inlb_true_iff in E. unfold rowsat; cbn [fst snd]; unfold ltype in *. apply cap_row; exact E.
    - destruct (inlb C D) eqn:E; [| apply trivial_row_sat].
      apply inlb_true_iff in E. unfold rowsat; cbn [fst snd]; unfold ltype in *. pose proof (link_row C E) as H; unfold ltype in H. lia.
    - destruct (k <? 4) eqn:E; [| apply trivial_row_sat].
      apply Nat.ltb_lt in E. unfold rowsat; cbn [fst snd]; unfold ltype in *. pose proof (star_row k E) as H; unfold ltype in H. lia.
    - destruct (i <? length (types D)) eqn:Ei; [| apply trivial_row_sat].
      apply Nat.ltb_lt in Ei. set (a := nth i (types D) dflt).
      assert (Ha : In a (types D)) by (apply nth_In; exact Ei).
      destruct (dett a) eqn:Ed; [| apply trivial_row_sat].
      unfold rowsat; cbn [fst snd]; unfold ltype in *.
      pose proof (ub_of_det a Ha Ed) as Hub1. unfold dett in Ed; apply Nat.eqb_eq in Ed.
      rewrite (suml_map_ext (fun t => (bigof (types D) * eqt t a + Nat.b2n (detdis a t)) * tcount V R M t)
                            (fun t => bigof (types D) * (eqt t a * tcount V R M t) + Nat.b2n (detdis a t) * tcount V R M t))
        by (intros; lia).
      rewrite suml_map_add, suml_map_mul_l, (suml_eqt (types D) a _ (types_NoDup D) Ha).
      assert (Hcnt : count (fun C => disjf (fst a) C) D <= length D) by apply count_le_length.
      pose proof (tcount_le_ub a Ha) as Hua. rewrite Hub1 in Hua.
      destruct (tcount V R M a) as [| [| na]] eqn:Ea; [| | lia].
      + (* absent: the row is slack by [big] *)
        assert (Hle : suml (map (fun t => Nat.b2n (detdis a t) * tcount V R M t) (types D)) <= suml (map ub_of (types D))).
        { apply suml_map_le; intros t Ht. pose proof (tcount_le_ub t Ht). destruct (detdis a t); simpl; lia. }
        unfold bigof in *. lia.
      + pose proof (det_row a Ed ltac:(lia)) as H. lia.
    - destruct ((i <? length (types D)) && (j <? length (types D)) && negb (i =? j)) eqn:Eij; [| apply trivial_row_sat].
      apply andb_true_iff in Eij as [Eij Ene]; apply andb_true_iff in Eij as [Ei Ej].
      apply Nat.ltb_lt in Ei; apply Nat.ltb_lt in Ej; apply negb_true_iff in Ene; apply Nat.eqb_neq in Ene.
      set (a := nth i (types D) dflt). set (b := nth j (types D) dflt).
      assert (Ha : In a (types D)) by (apply nth_In; exact Ei).
      assert (Hb : In b (types D)) by (apply nth_In; exact Ej).
      assert (Hab : a <> b).
      { intro E. apply Ene. pose proof (types_NoDup D) as HN. rewrite (NoDup_nth (types D) dflt) in HN. apply HN; assumption. }
      destruct (dett a && exclb D a b) eqn:Ed; [| apply trivial_row_sat].
      apply andb_true_iff in Ed as [Ed Ex].
      unfold rowsat; cbn [fst snd]; unfold ltype in *.
      pose proof (ub_of_det a Ha Ed) as Hub1. unfold dett in Ed; apply Nat.eqb_eq in Ed.
      rewrite (suml_map_ext (fun t => (ub_of b * eqt t a + eqt t b) * tcount V R M t)
                            (fun t => ub_of b * (eqt t a * tcount V R M t) + eqt t b * tcount V R M t))
        by (intros; lia).
      rewrite suml_map_add, suml_map_mul_l, (suml_eqt (types D) a _ (types_NoDup D) Ha),
        (suml_eqt (types D) b _ (types_NoDup D) Hb).
      pose proof (tcount_le_ub a Ha) as Hua. rewrite Hub1 in Hua.
      pose proof (tcount_le_ub b Hb) as Hub.
      destruct (tcount V R M a) as [| [| na]] eqn:Ea; [lia | | lia].
      pose proof (excl_row a b Hab Ed Ex ltac:(lia)) as H. lia.
  Qed.
End Model.

(** ** Dual certificates and branch-and-bound trees

    A leaf carries integer multipliers scaled by [lK]: [ly] on tagged
    rows, [lu] on the upper bounds [hi], [lv] on the lower bounds [lo].
    Weak duality in the natural numbers: if for every type [j]
    [lK + v_j ≤ Σ_r y_r a_rj + u_j] and
    [Σ_r y_r b_r + Σ_j u_j hi_j < Σ_j v_j lo_j + lK·T], then every count
    vector within the bounds has [Σ_j x_j < T] ([lK = 0] is the Farkas
    form: the bounds are infeasible).  A node splits a variable [i] at
    [f]: [x_i ≤ f] on the left, [x_i ≥ f + 1] on the right. *)

Record leaf : Type := mkleaf { lK : nat; ly : list (tag * nat); lu : list nat; lv : list nat }.

(** The certificates are stored with binary numbers ([N]): multipliers
    reach the thousands, and unary arithmetic would not do. *)
Record leafN : Type := mkleafN { lKN : N; lyN : list (tag * N); luN : list N; lvN : list N }.
Definition leaf_of_N (c : leafN) : leaf :=
  mkleaf (N.to_nat (lKN c)) (map (fun p => (fst p, N.to_nat (snd p))) (lyN c))
         (map N.to_nat (luN c)) (map N.to_nat (lvN c)).

Inductive tree : Type := Leaf (c : leafN) | Node (i f : nat) (l r : tree).

Definition sumN (l : list N) : N := fold_right N.add 0%N l.

Lemma sumN_to_nat : forall l, N.to_nat (sumN l) = suml (map N.to_nat l).
Proof.
  induction l as [| a l IH]; [reflexivity |].
  unfold sumN in *; cbn [fold_right map]; rewrite N2Nat.inj_add, IH; reflexivity.
Qed.

Lemma N_le_to_nat : forall a b, (a <= b)%N -> N.to_nat a <= N.to_nat b.
Proof. intros a b H; unfold N.le in H; rewrite N2Nat.inj_compare in H; apply Nat.compare_le_iff; exact H. Qed.

Lemma N_lt_to_nat : forall a b, (a < b)%N -> N.to_nat a < N.to_nat b.
Proof. intros a b H; unfold N.lt in H; rewrite N2Nat.inj_compare in H; apply Nat.compare_lt_iff; exact H. Qed.

Lemma nth_map_to_nat : forall l j, nth j (map N.to_nat l) 0 = N.to_nat (nth j l 0%N).
Proof. intros l j; apply (map_nth N.to_nat l 0%N j). Qed.

Fixpoint set_nth (i v : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | a :: l' => match i with 0 => v :: l' | S i' => a :: set_nth i' v l' end
  end.

Lemma nth_set_nth_same : forall i v l, i < length l -> nth i (set_nth i v l) 0 = v.
Proof.
  intros i v l; revert i; induction l as [| a l IH]; intros [| i] H; simpl in *; try lia;
    try reflexivity; try (apply IH; lia).
Qed.

Lemma nth_set_nth_other : forall i j v l, j <> i -> nth j (set_nth i v l) 0 = nth j l 0.
Proof.
  intros i j v l; revert i j; induction l as [| a l IH]; intros [| i] [| j] H; simpl; try reflexivity;
    try congruence. apply IH; congruence.
Qed.

Lemma set_nth_overflow : forall i v l, length l <= i -> set_nth i v l = l.
Proof.
  intros i v l; revert i; induction l as [| a l IH]; intros [| i] H; simpl in *; try lia; try reflexivity;
    try (rewrite IH by lia; reflexivity).
Qed.

Lemma suml_map_seq : forall {X} (d : X) (f : X -> nat) (l : list X),
  suml (map f l) = suml (map (fun j => f (nth j l d)) (seq 0 (length l))).
Proof.
  intros X d f l; induction l as [| a l IH]; [reflexivity |].
  cbn [length seq map nth]. rewrite suml_cons, suml_cons. f_equal.
  rewrite <- seq_shift, map_map. rewrite IH. apply suml_map_ext; intros j _; reflexivity.
Qed.

Section Dual.
  Variable ts : list ltype.
  Variable x : ltype -> nat.
  Variable rc : tag -> row.
  Hypothesis Hrows : forall tg, rowsat ts x (rc tg).

  (** The rows of a leaf, each built once. *)
  Definition lrows (ly : list (tag * nat)) : list (row * nat) := map (fun p => (rc (fst p), snd p)) ly.
  Definition ysum (rows : list (row * nat)) (t : ltype) : nat :=
    suml (map (fun q => snd q * fst (fst q) t) rows).
  Definition ybsum (rows : list (row * nat)) : nat :=
    suml (map (fun q => snd q * snd (fst q)) rows).

  Definition leafcheck_nat (lo hi : list nat) (T : nat) (c : leaf) : bool :=
    let rows := lrows (ly c) in
    let J := seq 0 (length ts) in
    forallb (fun j => lK c + nth j (lv c) 0 <=? ysum rows (nth j ts dflt) + nth j (lu c) 0) J
    && (ybsum rows + suml (map (fun j => nth j (lu c) 0 * nth j hi 0) J)
        <? suml (map (fun j => nth j (lv c) 0 * nth j lo 0) J) + lK c * T).

  (** The same check in binary arithmetic. *)
  Definition ysumN (rows : list (row * N)) (t : ltype) : N :=
    sumN (map (fun q => (snd q * N.of_nat (fst (fst q) t))%N) rows).
  Definition ybsumN (rows : list (row * N)) : N :=
    sumN (map (fun q => (snd q * N.of_nat (snd (fst q)))%N) rows).

  Definition leafcheck (lo hi : list nat) (T : nat) (c : leafN) : bool :=
    let rows := map (fun p => (rc (fst p), snd p)) (lyN c) in
    let J := seq 0 (length ts) in
    forallb (fun j => (lKN c + nth j (lvN c) 0 <=? ysumN rows (nth j ts dflt) + nth j (luN c) 0)%N) J
    && (ybsumN rows + sumN (map (fun j => (nth j (luN c) 0 * N.of_nat (nth j hi 0%nat))%N) J)
        <? sumN (map (fun j => (nth j (lvN c) 0 * N.of_nat (nth j lo 0%nat))%N) J) + lKN c * N.of_nat T)%N.

  Lemma leafcheck_to_nat : forall lo hi T c,
    leafcheck lo hi T c = true -> leafcheck_nat lo hi T (leaf_of_N c) = true.
  Proof.
    intros lo hi T c H. unfold leafcheck in H. unfold leafcheck_nat, leaf_of_N, lrows; cbn [lK ly lu lv].
    apply andb_true_iff in H as [H1 H2]. apply andb_true_iff. split.
    - rewrite forallb_forall in H1 |- *. intros j Hj. specialize (H1 j Hj).
      apply N.leb_le in H1. apply Nat.leb_le. apply N_le_to_nat in H1.
      rewrite N2Nat.inj_add, N2Nat.inj_add in H1.
      rewrite nth_map_to_nat, nth_map_to_nat. unfold ysum, ysumN in *.
      rewrite !sumN_to_nat, !map_map in H1.
      rewrite map_map; cbn [fst snd].
      rewrite (suml_map_ext (fun x => N.to_nat (snd x * N.of_nat (fst (rc (fst x)) (nth j ts dflt))))
                            (fun x => N.to_nat (snd x) * fst (rc (fst x)) (nth j ts dflt))) in H1
        by (intros p _; rewrite N2Nat.inj_mul, Nat2N.id; reflexivity).
      rewrite !map_map; cbn [fst snd]. exact H1.
    - apply N.ltb_lt in H2. apply Nat.ltb_lt. apply N_lt_to_nat in H2.
      rewrite N2Nat.inj_add, N2Nat.inj_add, N2Nat.inj_mul, Nat2N.id in H2.
      unfold ybsumN in H2.
      rewrite !sumN_to_nat, !map_map in H2.
      unfold ybsum. rewrite map_map; cbn [fst snd].
      rewrite (suml_map_ext (fun x => N.to_nat (snd x * N.of_nat (snd (rc (fst x)))))
                            (fun x => N.to_nat (snd x) * snd (rc (fst x)))) in H2
        by (intros p _; rewrite N2Nat.inj_mul, Nat2N.id; reflexivity).
      rewrite (suml_map_ext (fun j => N.to_nat (nth j (luN c) 0%N * N.of_nat (nth j hi 0)))
                            (fun j => nth j (map N.to_nat (luN c)) 0 * nth j hi 0)) in H2
        by (intros j _; rewrite N2Nat.inj_mul, Nat2N.id, nth_map_to_nat; reflexivity).
      rewrite (suml_map_ext (fun j => N.to_nat (nth j (lvN c) 0%N * N.of_nat (nth j lo 0)))
                            (fun j => nth j (map N.to_nat (lvN c)) 0 * nth j lo 0)) in H2
        by (intros j _; rewrite N2Nat.inj_mul, Nat2N.id, nth_map_to_nat; reflexivity).
      rewrite !map_map; cbn [fst snd]. exact H2.
  Qed.

  Fixpoint treecheck (lo hi : list nat) (T : nat) (tr : tree) : bool :=
    match tr with
    | Leaf c => leafcheck lo hi T c
    | Node i f l r =>
        treecheck lo (set_nth i (Nat.min f (nth i hi 0)) hi) T l
        && treecheck (set_nth i (Nat.max (S f) (nth i lo 0)) lo) hi T r
    end.

  Definition Bounded (lo hi : list nat) : Prop :=
    forall j, j < length ts -> nth j lo 0 <= x (nth j ts dflt) <= nth j hi 0.

  Lemma leaf_sound : forall lo hi T c,
    Bounded lo hi -> leafcheck_nat lo hi T c = true -> suml (map x ts) < T.
  Proof.
    intros lo hi T c Hb Hc. unfold leafcheck_nat in Hc. apply andb_true_iff in Hc as [H1 H2].
    rewrite forallb_forall in H1. apply Nat.ltb_lt in H2.
    set (xj := fun j => x (nth j ts dflt)) in *.
    set (J := seq 0 (length ts)) in *.
    set (rows := lrows (ly c)) in *.
    assert (HJ : forall j, In j J -> j < length ts) by (intros j Hj; apply in_seq in Hj; lia).
    assert (S1 : suml (map (fun j => (lK c + nth j (lv c) 0) * xj j) J)
                 <= suml (map (fun j => (ysum rows (nth j ts dflt) + nth j (lu c) 0) * xj j) J)).
    { apply suml_map_le; intros j Hj. apply Nat.mul_le_mono_r. apply Nat.leb_le. exact (H1 j Hj). }
    assert (S2 : suml (map (fun j => ysum rows (nth j ts dflt) * xj j) J) <= ybsum rows).
    { unfold ysum, ybsum.
      rewrite (suml_map_ext (fun j => suml (map (fun q => snd q * fst (fst q) (nth j ts dflt)) rows) * xj j)
                            (fun j => suml (map (fun q => snd q * (fst (fst q) (nth j ts dflt) * xj j)) rows)))
        by (intros j _; rewrite <- suml_map_mul_r; apply suml_map_ext; intros q _; lia).
      rewrite suml_exchange.
      apply suml_map_le; intros q Hq.
      rewrite suml_map_mul_l. apply Nat.mul_le_mono_l.
      unfold rows, lrows in Hq; apply in_map_iff in Hq as [p [E Hp]]; subst q; cbn [fst snd].
      pose proof (Hrows (fst p)) as Hr; unfold rowsat in Hr.
      rewrite (suml_map_seq dflt) in Hr. exact Hr. }
    assert (S3 : suml (map (fun j => nth j (lu c) 0 * xj j) J)
                 <= suml (map (fun j => nth j (lu c) 0 * nth j hi 0) J)).
    { apply suml_map_le; intros j Hj; apply Nat.mul_le_mono_l; apply Hb; apply HJ; exact Hj. }
    assert (S4 : suml (map (fun j => nth j (lv c) 0 * nth j lo 0) J)
                 <= suml (map (fun j => nth j (lv c) 0 * xj j) J)).
    { apply suml_map_le; intros j Hj; apply Nat.mul_le_mono_l; apply Hb; apply HJ; exact Hj. }
    assert (E1 : suml (map (fun j => (lK c + nth j (lv c) 0) * xj j) J)
                 = lK c * suml (map xj J) + suml (map (fun j => nth j (lv c) 0 * xj j) J)).
    { rewrite <- suml_map_mul_l, <- suml_map_add. apply suml_map_ext; intros; lia. }
    assert (E2 : suml (map (fun j => (ysum rows (nth j ts dflt) + nth j (lu c) 0) * xj j) J)
                 = suml (map (fun j => ysum rows (nth j ts dflt) * xj j) J)
                   + suml (map (fun j => nth j (lu c) 0 * xj j) J)).
    { rewrite <- suml_map_add. apply suml_map_ext; intros; lia. }
    assert (Hsum : suml (map x ts) = suml (map xj J)) by (apply (suml_map_seq dflt)).
    rewrite Hsum.
    assert (H : lK c * suml (map xj J) < lK c * T) by lia.
    destruct (lK c) as [| K']; [simpl in H; lia |].
    apply Nat.mul_lt_mono_pos_l in H; [exact H | lia].
  Qed.

  Lemma tree_sound : forall tr lo hi T,
    Bounded lo hi -> treecheck lo hi T tr = true -> suml (map x ts) < T.
  Proof.
    induction tr as [c | i f l IHl r IHr]; intros lo hi T Hb Hc; cbn [treecheck] in Hc.
    - exact (leaf_sound lo hi T (leaf_of_N c) Hb (leafcheck_to_nat lo hi T c Hc)).
    - apply andb_true_iff in Hc as [Hl Hr].
      destruct (le_lt_dec (x (nth i ts dflt)) f) as [Hle | Hgt].
      + apply (IHl lo (set_nth i (Nat.min f (nth i hi 0)) hi) T); [| exact Hl].
        intros j Hj. destruct (Hb j Hj) as [H1 H2]. split; [exact H1 |].
        destruct (Nat.eq_dec j i) as [E | NE].
        * subst j. destruct (le_lt_dec (length hi) i) as [Ho | Hi].
          -- rewrite set_nth_overflow by exact Ho. exact H2.
          -- rewrite nth_set_nth_same by exact Hi. apply Nat.min_glb; [exact Hle | exact H2].
        * rewrite nth_set_nth_other by exact NE. exact H2.
      + apply (IHr (set_nth i (Nat.max (S f) (nth i lo 0)) lo) hi T); [| exact Hr].
        intros j Hj. destruct (Hb j Hj) as [H1 H2]. split; [| exact H2].
        destruct (Nat.eq_dec j i) as [E | NE].
        * subst j. destruct (le_lt_dec (length lo) i) as [Ho | Hi].
          -- rewrite set_nth_overflow by exact Ho. exact H1.
          -- rewrite nth_set_nth_same by exact Hi. apply Nat.max_lub; [lia | exact H1].
        * rewrite nth_set_nth_other by exact NE. exact H1.
  Qed.
End Dual.

(** ** The class check and the bound it gives *)

(** The whole check for a link [D] and a tree: the counts are bounded
    below by 0 and above by [ub_of], and the tree must show
    [Σ x < 54 − |D|], i.e. [|D| + Σ x + 1 ≤ 54]. *)
Definition classcheck (D : Family) (tr : tree) : bool :=
  let U := unwit D in
  let ts := types D in
  treecheck ts (rowc D U ts (bigof ts)) (repeat 0 (length ts)) (map ub_of ts) (54 - length D) tr.

Theorem bound_of_tree :
  forall (F : Family) (R : list nat) (tr : tree),
    Uniform 4 F -> Distinct F -> ~ ContainsKSunflower 3 F -> In R F ->
    (forall C, In C F -> length (DisjointFrom C F) <= length (DisjointFrom R F)) ->
    classcheck (DisjointFrom R F) tr = true ->
    length F <= 54.
Proof.
  intros F R tr HU HD Hno HR Hmax Hc. unfold classcheck in Hc. cbv zeta in Hc.
  set (D := DisjointFrom R F) in *. set (V := points D) in *. set (M := Others R F) in *.
  pose proof (rows_valid F R HU HD Hno HR Hmax) as Hrows. cbv zeta in Hrows. fold D V M in Hrows.
  assert (Hb : Bounded (types D) (tcount V R M) (repeat 0 (length (types D))) (map ub_of (types D))).
  { intros j Hj. rewrite nth_repeat. split; [lia |].
    rewrite (List.nth_indep (map ub_of (types D)) 0 (ub_of dflt)) by (rewrite map_length; exact Hj).
    rewrite List.map_nth. apply tcount_le_ub; try assumption. apply nth_In; exact Hj. }
  pose proof (tree_sound (types D) (tcount V R M) _ Hrows tr _ _ _ Hb Hc) as H. clear Hc.
  assert (Hs : suml (map (tcount V R M) (types D)) = length M) by (apply tcount_sum; assumption).
  rewrite Hs in H.
  assert (Ho : length M + 1 = length (Meeting R F)) by (apply Others_length; assumption).
  pose proof (count_partition (fun C => disjointb R C) F) as Hp. unfold count in Hp.
  change (length D + length (Meeting R F) = length F) in Hp.
  lia.
Qed.

(** ** Transport to a canonical representative

    The check runs on a canonical link [Dk].  A family [F] whose largest
    link [D(R)] is [Dk] up to relabelling and set equality is rebuilt as
    [F2 := Dk ++ Meeting R' F'] over the relabelled [F']: [F2] has the
    same size and the same properties, and its link of [R'] is [Dk]. *)

Lemma filter_all : forall {X} (p : X -> bool) (l : list X),
  (forall a, In a l -> p a = true) -> filter p l = l.
Proof. intros X p l H; apply forallb_filter_id; apply forallb_forall; exact H. Qed.

Lemma filter_none : forall {X} (p : X -> bool) (l : list X),
  (forall a, In a l -> p a = false) -> filter p l = [].
Proof.
  intros X p l H; induction l as [| a l IH]; [reflexivity |].
  simpl; rewrite (H a (or_introl eq_refl)); apply IH; intros b Hb; apply H; right; exact Hb.
Qed.

Lemma Uniform_app : forall n A B, Uniform n A -> Uniform n B -> Uniform n (A ++ B).
Proof. intros n A B HA HB; unfold Uniform in *; apply Forall_app; split; assumption. Qed.

Lemma SubFamilySetEq_app : forall A B G,
  SubFamilySetEq A G -> SubFamilySetEq B G -> SubFamilySetEq (A ++ B) G.
Proof. intros A B G HA HB X HX; apply in_app_iff in HX as [HX | HX]; [apply HA | apply HB]; exact HX. Qed.

Lemma SubFamilySetEq_DisjointFrom : forall C C' A B,
  SubFamilySetEq A B -> SetEq C C' -> SubFamilySetEq (DisjointFrom C A) (DisjointFrom C' B).
Proof.
  intros C C' A B H E X HX. apply in_DisjointFrom in HX as [HX Hd]. destruct (H X HX) as [Y [HY EY]].
  exists Y; split; [| exact EY]. apply in_DisjointFrom; split; [exact HY |].
  intros x H1 H2; apply (Hd x); [apply E; exact H1 | apply EY; exact H2].
Qed.

Theorem finer_class_bound :
  forall (Dk : Family) (tr : tree),
    Uniform 4 Dk -> SetNoDup Dk -> classcheck Dk tr = true ->
    forall (F : Family) (R : list nat) (g h : nat -> nat),
      (forall x, h (g x) = x) -> (forall x, g (h x) = x) ->
      Uniform 4 F -> Distinct F -> ~ ContainsKSunflower 3 F -> In R F ->
      (forall C, In C F -> length (DisjointFrom C F) <= length (DisjointFrom R F)) ->
      SubFamilySetEq (DisjointFrom R F) (rmapF g Dk) ->
      SubFamilySetEq (rmapF g Dk) (DisjointFrom R F) ->
      length F <= 54.
Proof.
  intros Dk tr HUk HDk Hck F R g h Hgh Hhg HU HD Hno HR Hmax H1 H2.
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
  assert (HS1 : SubFamilySetEq (DisjointFrom R' F') Dk).
  { rewrite HDF. apply (SubFamilySetEq_rmapF h) in H1. rewrite (rmapF_inverse g h Hgh) in H1. exact H1. }
  assert (HS2 : SubFamilySetEq Dk (DisjointFrom R' F')).
  { rewrite HDF. apply (SubFamilySetEq_rmapF h) in H2. rewrite (rmapF_inverse g h Hgh) in H2. exact H2. }
  assert (HSD' : SetNoDup (DisjointFrom R' F')) by (unfold DisjointFrom; apply SetNoDup_filter; exact HD').
  assert (Hlen : length (DisjointFrom R' F') = length Dk) by (apply length_SetEq_families; assumption).
  (* the rebuilt family *)
  set (F2 := Dk ++ Meeting R' F').
  assert (HkR : forall C, In C Dk -> Disjoint R' C).
  { intros C HC. destruct (HS2 C HC) as [C' [HC' E]]. apply in_DisjointFrom in HC' as [_ Hd].
    intros x Hx HxC; apply (Hd x Hx); apply E; exact HxC. }
  assert (HF2 : SubFamilySetEq F2 F').
  { apply SubFamilySetEq_app.
    - intros C HC. destruct (HS2 C HC) as [C' [HC' E]]. apply in_DisjointFrom in HC' as [HC' _]. eauto.
    - apply SubFamilySetEq_incl; intros S HS; apply in_Meeting in HS; tauto. }
  assert (HF2' : SubFamilySetEq F' F2).
  { intros S HS. destruct (disjointb R' S) eqn:E.
    - apply disjointb_correct in E.
      assert (HSD : In S (DisjointFrom R' F')) by (apply in_DisjointFrom; tauto).
      destruct (HS1 S HSD) as [C [HC EC]]. exists C; split; [apply in_app_iff; left; exact HC | exact EC].
    - exists S; split; [| apply SetEq_refl]. apply in_app_iff; right.
      unfold Meeting; apply filter_In; split; [exact HS | rewrite E; reflexivity]. }
  assert (HU2 : Uniform 4 F2).
  { apply Uniform_app; [exact HUk |].
    apply (Uniform_sublist HU'); intros S HS; apply in_Meeting in HS; tauto. }
  assert (HD2 : Distinct F2).
  { apply SetNoDup_app; [exact HDk | unfold Meeting; apply SetNoDup_filter; exact HD' |].
    intros A B HA HB E. apply in_Meeting in HB as [_ HB]. apply HB.
    intros x Hx1 Hx2. apply (HkR A HA x Hx1). apply E; exact Hx2. }
  assert (Hno2 : ~ ContainsKSunflower 3 F2).
  { intro Hc; apply Hno'; exact (ContainsKSunflower_SubFamilySetEq Hc HF2). }
  assert (HR2 : In R' F2).
  { apply in_app_iff; right. apply in_Meeting; split; [exact HR' |].
    intro Hd. destruct (member_nonempty F' HU' R' HR') as [z Hz]. exact (Hd z Hz Hz). }
  assert (HDR2 : DisjointFrom R' F2 = Dk).
  { unfold F2, DisjointFrom. rewrite filter_app.
    rewrite (filter_all (fun C => disjointb R' C) Dk)
      by (intros C HC; apply disjointb_correct; apply HkR; exact HC).
    rewrite (filter_none (fun C => disjointb R' C) (Meeting R' F')); [apply app_nil_r |].
    intros S HS; apply in_Meeting in HS as [_ HS].
    destruct (disjointb R' S) eqn:E; [exfalso; apply HS; apply disjointb_correct; exact E | reflexivity]. }
  assert (Hmax2 : forall C, In C F2 -> length (DisjointFrom C F2) <= length (DisjointFrom R' F2)).
  { intros C HC. rewrite HDR2.
    destruct (HF2 C HC) as [C' [HC' E]].
    assert (Hl : length (DisjointFrom C F2) = length (DisjointFrom C' F')).
    { apply length_SetEq_families.
      - unfold DisjointFrom; apply SetNoDup_filter; exact HD2.
      - unfold DisjointFrom; apply SetNoDup_filter; exact HD'.
      - apply SubFamilySetEq_DisjointFrom; [exact HF2 | exact E].
      - apply SubFamilySetEq_DisjointFrom; [exact HF2' | apply SetEq_sym; exact E]. }
    rewrite Hl, <- Hlen. apply Hmax'; exact HC'. }
  assert (Hlen2 : length F2 = length F).
  { unfold F2. rewrite app_length.
    pose proof (count_partition (fun C => disjointb R' C) F') as Hp. unfold count in Hp.
    change (length (DisjointFrom R' F') + length (Meeting R' F') = length F') in Hp.
    rewrite Hlen in Hp. assert (HF'len : length F' = length F) by (unfold F'; apply rmapF_length). lia. }
  rewrite <- Hlen2.
  apply (bound_of_tree F2 R' tr HU2 HD2 Hno2 HR2 Hmax2). rewrite HDR2. exact Hck.
Qed.

(** ** The descent with both kinds of certificate

    [Census2 reps trees lo]: every intersecting 3-sunflower-free family
    of at least [lo] distinct 4-sets is, up to relabelling, either an
    LP-certified representative or a tree-certified one.  As with
    [LinkLP.Census], this is what the exhaustive search found and is NOT
    proved here. *)

Definition Covered (D Dk : Family) : Prop :=
  exists g h : nat -> nat,
    (forall x, h (g x) = x) /\ (forall x, g (h x) = x) /\
    SubFamilySetEq D (rmapF g Dk) /\ SubFamilySetEq (rmapF g Dk) D.

Definition Census2 (reps : list (Family * cert)) (trees : list (Family * tree)) (lo : nat) : Prop :=
  forall D : Family,
    Uniform 4 D -> Distinct D -> Intersecting D -> ~ ContainsKSunflower 3 D ->
    lo <= length D ->
    (exists Dk ck, In (Dk, ck) reps /\ Covered D Dk)
    \/ (exists Dk tr, In (Dk, tr) trees /\ Covered D Dk).

Fixpoint nodupb (l : list nat) : bool :=
  match l with [] => true | a :: l' => negb (membf a l') && nodupb l' end.

Lemma nodupb_correct : forall l, nodupb l = true -> NoDup l.
Proof.
  induction l as [| a l IH]; intros H; [constructor |].
  simpl in H; apply andb_true_iff in H as [H1 H2]; apply negb_true_iff in H1.
  constructor; [intro Hin; apply membf_true_iff in Hin; rewrite Hin in H1; discriminate | apply IH; exact H2].
Qed.

Definition uniform4b (D : Family) : bool := forallb (fun C => (length C =? 4) && nodupb C) D.

Lemma uniform4b_correct : forall D, uniform4b D = true -> Uniform 4 D.
Proof.
  intros D H; unfold uniform4b in H; rewrite forallb_forall in H; unfold Uniform; apply Forall_forall.
  intros C HC; specialize (H C HC); apply andb_true_iff in H as [H1 H2].
  split; [apply Nat.eqb_eq; exact H1 | apply nodupb_correct; exact H2].
Qed.

(** Every tree-certified representative is 4-uniform, distinct and passes
    its check — decided by [vm_compute]. *)
Definition trees_okb (trees : list (Family * tree)) : bool :=
  forallb (fun p => uniform4b (fst p) && setnodupb (fst p) && classcheck (fst p) (snd p)) trees.

Lemma trees_okb_entry : forall trees Dk tr, trees_okb trees = true -> In (Dk, tr) trees ->
  Uniform 4 Dk /\ SetNoDup Dk /\ classcheck Dk tr = true.
Proof.
  intros trees Dk tr Hok Hin. unfold trees_okb in Hok; rewrite forallb_forall in Hok.
  specialize (Hok (Dk, tr) Hin); simpl in Hok.
  apply andb_true_iff in Hok as [Hok H3]; apply andb_true_iff in Hok as [H1 H2].
  split; [apply uniform4b_correct; exact H1 | split; [apply setnodupb_correct; exact H2 | exact H3]].
Qed.

Theorem descent_of_census2 :
  IotaAtMost 4 27 ->
  forall reps trees lo, 1 <= lo ->
    (forall Dk ck, In (Dk, ck) reps -> SetNoDup Dk /\ certcheck Dk ck (54 - length Dk) = true) ->
    trees_okb trees = true ->
    Census2 reps trees lo -> LinkDescent 4 lo 54.
Proof.
  intros Hiota reps trees lo Hlo1 Hreps Htrees Hcen F R HU HD Hno HR Hlo.
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
  destruct (Hcen D HDU HDD HDI HDno HDlo) as [[Dk [ck [Hin [g [h [Hgh [Hhg [H1 H2]]]]]]]]
                                            | [Dk [tr [Hin [g [h [Hgh [Hhg [H1 H2]]]]]]]]].
  - destruct (Hreps Dk ck Hin) as [Hnd Hck].
    exact (class_bound Hiota Dk ck Hnd Hck F R0 g h Hgh Hhg HU HD Hno HR0 Hmax HDne H1 H2).
  - destruct (trees_okb_entry trees Dk tr Htrees Hin) as [HUk [HDk Hck]].
    exact (finer_class_bound Dk tr HUk HDk Hck F R0 g h Hgh Hhg HU HD Hno HR0 Hmax H1 H2).
Qed.
