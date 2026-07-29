(** * Compression.v — shifting, and why it is the wrong tool here.

    The [(i,j)]-shift is *the* instrument of extremal set theory. For
    [i < j] it replaces a member [A] by [(A \ {j}) ∪ {i}] whenever
    [j ∈ A], [i ∉ A], and the image is not already present. It preserves
    the size of the family, preserves uniformity, preserves
    intersecting-ness, and terminates — so any family compresses to a
    **left-compressed** one of the same size, supported on an initial
    segment of the ground set. Erdős–Ko–Rado, Hilton–Milner and most of
    Frankl's work are proved this way, and this development had never
    touched it.

    ** What this file proves

    Compression and sunflower-freeness are not merely a poor fit. They
    are opposed, and the theorem says by how much:

    - [compressed_lives_on_m_plus_one_points]: a left-compressed
      3-sunflower-free [m]-uniform family is supported on [{0,...,m}].
      Not [c*m] points for some constant — [m+1] points, exactly, with
      no dependence on the ground set it started on.
    - [compressed_bound]: hence it has at most [m+1] members. Against
      [g(b) >= 2*iota(b)], which is exponential. Compression does not
      cost a constant here; it collapses the problem from exponential to
      linear.
    - [compressed_bound_is_attained]: and [m+1] is attained, so the
      statement is sharp rather than merely true.

    ** Why that matters, stated as a theorem rather than a remark

    [SliceRank.v] names [GroundBounded c] — "an extremal sunflower-free
    [m]-uniform family can be realised on at most [c*m] points" — as the
    one missing fact that turns Naslund–Sawin into the sunflower
    conjecture at [k = 3]. Compression would deliver it outright:

    - [compression_would_give_ground_bounded]: if compression preserved
      sunflower-freeness, [GroundBounded 2] would follow;
    - [compression_would_settle_k3]: and with it, the conjecture at
      [k = 3], with the explicit constant [27^3].

    That is the "too good to be true" reading of the shifting method, and
    the implication really does hold. What fails is its hypothesis, and
    that failure is a theorem here rather than an observation:

    - [compression_does_not_preserve_sunflower_freeness]: it does not,
      and the proof is one line of arithmetic against [F23.f_2_3_lower],
      which exhibits six 2-uniform sunflower-free sets where compression
      permits three.
    - [shift_may_create_a_sunflower]: the smallest counterexample,
      reflectively. [{0,1}, {0,2}, {1,3}] is sunflower-free; its
      [(0,1)]-shift is the star [{0,1}, {0,2}, {0,3}]. Three members,
      which is the least a 3-sunflower can have — so shifting fails at
      the first opportunity it is given.

    ** The mechanism

    [LinkCharacterisation.sunflower_iff_link_matching] says a family is
    sunflower-free exactly when *every* link has matching number at most
    2. Shifting preserves that at the **empty** link — the standard fact
    that it does not increase the matching number — and destroys it at
    every other core, because shifting towards [i] is precisely the
    operation that inflates [deg i], and
    [IotaGround.link_degree_ground_bound] is precisely the theorem that
    caps [deg i]. Intersecting-ness is the *single* empty-link condition
    [nu <= 1], which is why the instrument works for Erdős–Ko–Rado and
    cannot work here.

    Measured exhaustively in [rust/tests/shifting.rs] before any of this
    was proved: the controls (size, uniformity, intersecting-ness,
    matching number) all pass, the smallest counterexample has three
    members, and the compressed maximum is [m+1] at every [m <= 6] and
    every ground set in range. *)

From Coq Require Import List Arith Lia Bool.
From Coq Require Import PeanoNat Permutation.
From Sunflower Require Import Sets Sunflower LowerBound Reflect F23 SliceRank.
Import ListNotations.

Set Implicit Arguments.

(** ** The shift, and its fixed points *)

(** The [(i,j)]-shift of one member: drop [j], add [i]. The guard "the
    image is not already in the family" belongs to the shift of the
    *family*; for the fixed-point condition below it is exactly what is
    being asserted, so it does not appear. *)

Definition shift_member (i j : nat) (A : list nat) : list nat :=
  i :: rem_elt j A.

(** [F] is **left-compressed** when it is a fixed point of every
    [(i,j)]-shift: whenever a member has [j] and lacks [i] with [i < j],
    the shifted set is already there.

    Membership is up to [SetEq], as everywhere in this development:
    families are families of sets, and [rem_elt] fixes an order. No
    ground set appears, which is what makes
    [compressed_lives_on_m_plus_one_points] a statement about the
    uniformity alone. *)

Definition LeftCompressed (F : Family) : Prop :=
  forall A i j,
    In A F -> i < j -> In j A -> ~ In i A ->
    exists B, In B F /\ SetEq B (shift_member i j A).

(** ** The chain the argument runs on

    [chain m t = {0, ..., m-2} ∪ {t}]. Three of these with distinct
    [t >= m-1] are a 3-sunflower with core [{0, ..., m-2}]: that is the
    whole obstruction, and everything below is the work of getting a
    compressed family to produce three of them. *)

Definition seg (n : nat) : list nat := seq 0 n.

Definition chain (m t : nat) : list nat := t :: seg (m - 1).

Lemma in_seg : forall n x, In x (seg n) <-> x < n.
Proof. intros n x; unfold seg; rewrite in_seq; lia. Qed.

Lemma seg_nodup : forall n, NoDup (seg n).
Proof. intro n; unfold seg; apply seq_NoDup. Qed.

Lemma seg_len : forall n, length (seg n) = n.
Proof. intro n; unfold seg; apply seq_length. Qed.

Lemma in_chain : forall m t x, In x (chain m t) <-> x = t \/ x < m - 1.
Proof.
  intros m t x; unfold chain; simpl; rewrite in_seg; split;
    (intros [E | L]; [left; congruence | right; exact L]).
Qed.

(** ** Two general-purpose helpers the standard library does not have *)

Lemma not_forall_exists :
  forall (P : nat -> Prop),
    (forall x, {P x} + {~ P x}) ->
    forall l, ~ Forall P l -> exists x, In x l /\ ~ P x.
Proof.
  intros P dec l; induction l as [|a l IH]; intro H.
  - exfalso; apply H; constructor.
  - destruct (dec a) as [Ha | Ha].
    + destruct IH as [x [Hx HPx]].
      * intro HF; apply H; constructor; assumption.
      * exists x; split; [right; exact Hx | exact HPx].
    + exists a; split; [left; reflexivity | exact Ha].
Qed.

Lemma NoDup_map_inj :
  forall (f : list nat -> nat) (l : Family),
    NoDup l ->
    (forall A B, In A l -> In B l -> f A = f B -> A = B) ->
    NoDup (map f l).
Proof.
  intros f l; induction l as [|a l IH]; simpl; intros Hnd Hinj; [constructor|].
  inversion Hnd as [| ? ? Hni Hnd']; subst.
  constructor.
  - intro Hin; apply in_map_iff in Hin as [b [Hfb Hb]].
    assert (E : a = b)
      by (apply Hinj; [left; reflexivity | right; exact Hb | symmetry; exact Hfb]).
    subst b; contradiction.
  - apply IH; [exact Hnd'|].
    intros A B HA HB; apply Hinj; right; assumption.
Qed.

(** ** Arithmetic on [list_sum], the potential that drives compression *)

Lemma list_sum_perm : forall l l' : list nat,
    Permutation l l' -> list_sum l = list_sum l'.
Proof. intros l l' H; induction H; simpl; lia. Qed.

Lemma setEq_NoDup_sum : forall A B,
    NoDup A -> NoDup B -> SetEq A B -> list_sum A = list_sum B.
Proof.
  intros A B HA HB [H1 H2].
  apply list_sum_perm, NoDup_Permutation; auto.
  intro x; split; [apply H1 | apply H2].
Qed.

Lemma list_sum_rem : forall x A,
    NoDup A -> In x A -> list_sum (rem_elt x A) + x = list_sum A.
Proof.
  intros x A HA Hin; induction HA as [| a l Hni Hnd IH]; [inversion Hin|].
  simpl in Hin; unfold rem_elt in *; simpl.
  destruct (Nat.eqb_spec a x) as [E | NE]; simpl.
  - subst a.
    assert (Hrem : filter (fun y => negb (Nat.eqb y x)) l = l).
    { clear -Hni. induction l as [|b l IHl]; simpl; [reflexivity|].
      destruct (Nat.eqb_spec b x) as [E | NE]; simpl.
      - subst b; exfalso; apply Hni; left; reflexivity.
      - f_equal; apply IHl; intro H; apply Hni; right; exact H. }
    rewrite Hrem; lia.
  - destruct Hin as [E | Hin']; [contradiction|].
    specialize (IH Hin'); simpl in IH |- *; lia.
Qed.

(** ** Step one: a compressed family contains the whole chain below any
       member

    From a member [A] and an element [t] of it large enough to head a
    chain, compression produces [chain m t]. The induction is on
    [list_sum A]: each shift strictly lowers it, which is exactly why the
    compression terminates in the first place. *)

Lemma compress_to_chain_aux :
  forall n F m,
    LeftCompressed F -> Uniform m F ->
    forall A, In A F -> list_sum A <= n ->
    forall t, In t A -> m - 1 <= t ->
      exists B, In B F /\ SetEq B (chain m t).
Proof.
  induction n as [n IH] using (well_founded_induction lt_wf).
  intros F m Hlc Hun A HA Hsum t Ht Hmt.
  assert (HUA : UniformSet m A)
    by (unfold Uniform in Hun; rewrite Forall_forall in Hun; auto).
  destruct HUA as [Hlen HndA].
  assert (HndR : NoDup (rem_elt t A)) by (apply rem_NoDup; exact HndA).
  assert (HlenR : length (rem_elt t A) = m - 1)
    by (rewrite length_rem_elt_in by assumption; lia).
  destruct (Forall_dec (fun y => y < m - 1) (fun y => lt_dec y (m - 1))
              (rem_elt t A)) as [Hall | Hsome].
  - (* Everything else is below m-1, and there are m-1 of them: A is the
       chain already. *)
    exists A; split; [exact HA|].
    rewrite Forall_forall in Hall.
    assert (Hsub : Subset (rem_elt t A) (seg (m - 1)))
      by (intros x Hx; rewrite in_seg; apply Hall; exact Hx).
    assert (Hseq : SetEq (rem_elt t A) (seg (m - 1))).
    { split; [exact Hsub|].
      apply NoDup_length_incl; [exact HndR | rewrite seg_len; lia | exact Hsub]. }
    split.
    + intros x Hx; rewrite in_chain.
      destruct (Nat.eq_dec x t) as [E | NE]; [left; exact E|].
      right; rewrite <- in_seg; apply Hseq, in_rem_iff; split; assumption.
    + intros x Hx; rewrite in_chain in Hx; destruct Hx as [E | L].
      * subst; exact Ht.
      * apply (rem_Subset t A); apply Hseq; rewrite in_seg; exact L.
  - (* Some other element is at least m-1, so A is not the chain, and
       some point below m-1 is missing. Shift. *)
    destruct (not_forall_exists (fun y => lt_dec y (m - 1)) Hsome)
      as [j [Hjin Hjge]].
    assert (Hjge' : m - 1 <= j) by lia.
    assert (HjA : In j A) by (apply (rem_Subset t A); exact Hjin).
    assert (Hjt : j <> t) by (rewrite in_rem_iff in Hjin; tauto).
    assert (Hi : exists i, i < m - 1 /\ ~ In i A).
    { destruct (Forall_dec (fun x => In x A) (fun x => in_dec_nat x A)
                  (seg (m - 1))) as [Hf | Hf].
      - (* seg (m-1) ⊆ A, so rem_elt t A = seg (m-1), contradicting j. *)
        exfalso; rewrite Forall_forall in Hf.
        assert (Hsub : Subset (seg (m - 1)) (rem_elt t A)).
        { intros x Hx; apply in_rem_iff; split; [apply Hf; exact Hx|].
          rewrite in_seg in Hx; lia. }
        assert (Hback : Subset (rem_elt t A) (seg (m - 1))).
        { apply NoDup_length_incl;
            [apply seg_nodup | rewrite seg_len; lia | exact Hsub]. }
        specialize (Hback j Hjin); rewrite in_seg in Hback; lia.
      - destruct (not_forall_exists (fun x => in_dec_nat x A) Hf)
          as [i [Hiin Hini]].
        exists i; rewrite in_seg in Hiin; split; [exact Hiin | exact Hini]. }
    destruct Hi as [i [Hilt Hini]].
    assert (Hij : i < j) by lia.
    destruct (Hlc A i j HA Hij HjA Hini) as [B [HB HBeq]].
    assert (HUB : UniformSet m B)
      by (unfold Uniform in Hun; rewrite Forall_forall in Hun; auto).
    destruct HUB as [HlenB HndB].
    assert (HndS : NoDup (shift_member i j A)).
    { unfold shift_member; constructor;
        [rewrite in_rem_iff; tauto | apply rem_NoDup; exact HndA]. }
    assert (Hrem : list_sum (rem_elt j A) + j = list_sum A)
      by (apply list_sum_rem; assumption).
    assert (HsumS : list_sum (shift_member i j A) + j = list_sum A + i)
      by (unfold shift_member; simpl; lia).
    assert (HsumB : list_sum B = list_sum (shift_member i j A))
      by (apply setEq_NoDup_sum; assumption).
    assert (HtB : In t B).
    { apply (proj2 HBeq); unfold shift_member; right.
      apply in_rem_iff; split; [exact Ht | intro E; subst; contradiction]. }
    assert (Hdrop : list_sum B < list_sum A) by lia.
    exact (IH (list_sum B) ltac:(lia) F m Hlc Hun B HB (Nat.le_refl _) t HtB Hmt).
Qed.

Lemma compress_to_chain :
  forall F m,
    LeftCompressed F -> Uniform m F ->
    forall A, In A F -> forall t, In t A -> m - 1 <= t ->
      exists B, In B F /\ SetEq B (chain m t).
Proof.
  intros F m Hlc Hun A HA t Ht Hmt.
  eapply compress_to_chain_aux with (A := A); eauto.
Qed.

(** ** Step two: three chains are a sunflower *)

Lemma chain_inter : forall m x y,
    m - 1 <= x -> m - 1 <= y -> x <> y ->
    SetEq (inter (chain m x) (chain m y)) (seg (m - 1)).
Proof.
  intros m x y Hx Hy Hne; split.
  - intros z Hz; rewrite in_inter_iff in Hz; destruct Hz as [H1 H2].
    rewrite in_chain in H1, H2; rewrite in_seg.
    destruct H1 as [E1 | L1]; [| exact L1].
    destruct H2 as [E2 | L2]; [subst; contradiction | lia].
  - intros z Hz; rewrite in_seg in Hz; rewrite in_inter_iff.
    split; rewrite in_chain; right; exact Hz.
Qed.

Lemma chain_not_setEq : forall m x y,
    m - 1 <= x -> x <> y -> ~ SetEq (chain m x) (chain m y).
Proof.
  intros m x y Hx Hne [H1 _].
  assert (Hin : In x (chain m x)) by (rewrite in_chain; left; reflexivity).
  specialize (H1 x Hin); rewrite in_chain in H1; lia.
Qed.

Lemma three_chains_are_a_sunflower : forall m x y z,
    m - 1 <= x -> m - 1 <= y -> m - 1 <= z ->
    x <> y -> x <> z -> y <> z ->
    Sunflower [chain m x; chain m y; chain m z] (seg (m - 1)).
Proof.
  intros m x y z Hx Hy Hz Hxy Hxz Hyz; split.
  - constructor.
    + intros B HB; simpl in HB; destruct HB as [E | [E | []]]; subst;
        apply chain_not_setEq; auto.
    + constructor.
      * intros B HB; simpl in HB; destruct HB as [E | []]; subst;
          apply chain_not_setEq; auto.
      * constructor.
        -- intros B HB; inversion HB.
        -- constructor.
  - intros A B HA HB Hne; simpl in HA, HB.
    destruct HA as [E1 | [E1 | [E1 | []]]];
      destruct HB as [E2 | [E2 | [E2 | []]]];
      subst; try (exfalso; apply Hne; reflexivity); apply chain_inter; auto.
Qed.

(** ** The theorem: a compressed sunflower-free family lives on [m+1]
       points *)

Theorem compressed_lives_on_m_plus_one_points :
  forall F m,
    1 <= m -> LeftCompressed F -> Uniform m F ->
    ~ ContainsKSunflower 3 F ->
    forall A, In A F -> Subset A (seg (S m)).
Proof.
  intros F m Hm Hlc Hun Hno A HA x Hx.
  rewrite in_seg.
  destruct (Nat.ltb_spec x (S m)) as [Hlt | Hge]; [exact Hlt|].
  exfalso.
  assert (Hxm : m - 1 <= x) by lia.
  assert (Hch : exists B, In B F /\ SetEq B (chain m x))
    by (apply compress_to_chain with (A := A); assumption).
  destruct Hch as [Bx [HBx HBxeq]].
  (* Step x down to m. *)
  assert (HxB : In x Bx)
    by (apply (proj2 HBxeq); rewrite in_chain; left; reflexivity).
  assert (HmB : ~ In m Bx).
  { intro Hin; apply (proj1 HBxeq) in Hin; rewrite in_chain in Hin; lia. }
  destruct (Hlc Bx m x HBx ltac:(lia) HxB HmB) as [Bm [HBm HBmeq]].
  assert (HBmchain : SetEq Bm (chain m m)).
  { eapply SetEq_trans; [exact HBmeq|]; split.
    - intros z Hz; unfold shift_member in Hz; simpl in Hz.
      rewrite in_chain; destruct Hz as [E | Hz]; [left; auto|].
      rewrite in_rem_iff in Hz; destruct Hz as [Hz Hzx].
      apply (proj1 HBxeq) in Hz; rewrite in_chain in Hz.
      destruct Hz as [E | L]; [contradiction | right; exact L].
    - intros z Hz; rewrite in_chain in Hz; unfold shift_member; simpl.
      destruct Hz as [E | L]; [left; auto|].
      right; rewrite in_rem_iff; split; [| lia].
      apply (proj2 HBxeq); rewrite in_chain; right; exact L. }
  (* Step m down to m-1. *)
  assert (HmBm : In m Bm)
    by (apply (proj2 HBmchain); rewrite in_chain; left; reflexivity).
  assert (Hm1Bm : ~ In (m - 1) Bm).
  { intro Hin; apply (proj1 HBmchain) in Hin; rewrite in_chain in Hin; lia. }
  destruct (Hlc Bm (m - 1) m HBm ltac:(lia) HmBm Hm1Bm) as [Bp [HBp HBpeq]].
  assert (HBpchain : SetEq Bp (chain m (m - 1))).
  { eapply SetEq_trans; [exact HBpeq|]; split.
    - intros z Hz; unfold shift_member in Hz; simpl in Hz.
      rewrite in_chain; destruct Hz as [E | Hz]; [left; auto|].
      rewrite in_rem_iff in Hz; destruct Hz as [Hz Hzm].
      apply (proj1 HBmchain) in Hz; rewrite in_chain in Hz.
      destruct Hz as [E | L]; [contradiction | right; exact L].
    - intros z Hz; rewrite in_chain in Hz; unfold shift_member; simpl.
      destruct Hz as [E | L]; [left; auto|].
      right; rewrite in_rem_iff; split; [| lia].
      apply (proj2 HBmchain); rewrite in_chain; right; exact L. }
  apply Hno.
  exists [chain m (m - 1); chain m m; chain m x]; split.
  - intros C HC; simpl in HC; destruct HC as [E | [E | [E | []]]]; subst.
    + exists Bp; split; [exact HBp | apply SetEq_sym; exact HBpchain].
    + exists Bm; split; [exact HBm | apply SetEq_sym; exact HBmchain].
    + exists Bx; split; [exact HBx | apply SetEq_sym; exact HBxeq].
  - split; [reflexivity|].
    exists (seg (m - 1)); apply three_chains_are_a_sunflower; lia.
Qed.

(** ** And therefore has at most [m + 1] members

    Every member is an [m]-subset of an [(m+1)]-set, so it is determined
    by the single point it omits. That map is injective on a [Distinct]
    family, so the family injects into [{0, ..., m}]. *)

Definition omitted (m : nat) (A : list nat) : nat :=
  hd 0 (filter (fun x => negb (memb x A)) (seg (S m))).

Lemma filter_partition_length :
  forall (p : nat -> bool) (l : list nat),
    length (filter p l) + length (filter (fun x => negb (p x)) l) = length l.
Proof.
  intros p l; induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (p a); simpl; lia.
Qed.

Lemma omitted_spec :
  forall m A,
    NoDup A -> length A = m -> Subset A (seg (S m)) ->
    filter (fun x => negb (memb x A)) (seg (S m)) = [omitted m A]
    /\ ~ In (omitted m A) A.
Proof.
  intros m A HndA HlenA Hsub.
  assert (Hkept : SetEq (filter (fun x => memb x A) (seg (S m))) A).
  { split.
    - intros x Hx; apply filter_In in Hx as [_ Hb]; rewrite memb_true_iff in Hb;
        exact Hb.
    - intros x Hx; apply filter_In; split;
        [apply Hsub; exact Hx | rewrite memb_true_iff; exact Hx]. }
  assert (Hkndup : NoDup (filter (fun x => memb x A) (seg (S m))))
    by (apply NoDup_filter, seg_nodup).
  assert (Hklen : length (filter (fun x => memb x A) (seg (S m))) = m).
  { assert (Hle : length (filter (fun x => memb x A) (seg (S m))) = length A).
    { apply Nat.le_antisymm.
      - apply NoDup_incl_length; [exact Hkndup | apply (proj1 Hkept)].
      - apply NoDup_incl_length; [exact HndA | apply (proj2 Hkept)]. }
    rewrite Hle; exact HlenA. }
  pose proof (filter_partition_length (fun x => memb x A) (seg (S m))) as Hpart.
  rewrite seg_len, Hklen in Hpart.
  destruct (filter (fun x => negb (memb x A)) (seg (S m))) as [| g rest] eqn:E;
    simpl in Hpart; [lia|].
  destruct rest; simpl in Hpart; [| lia].
  assert (Hom : omitted m A = g) by (unfold omitted; rewrite E; reflexivity).
  rewrite Hom; split; [reflexivity|].
  assert (Hg : In g (filter (fun x => negb (memb x A)) (seg (S m))))
    by (rewrite E; left; reflexivity).
  apply filter_In in Hg as [_ Hb]; apply Bool.negb_true_iff in Hb.
  rewrite memb_false_iff in Hb; exact Hb.
Qed.

Lemma omitted_injective :
  forall m A B,
    NoDup A -> length A = m -> Subset A (seg (S m)) ->
    NoDup B -> length B = m -> Subset B (seg (S m)) ->
    omitted m A = omitted m B -> SetEq A B.
Proof.
  intros m A B HndA HlA HsA HndB HlB HsB Heq.
  destruct (omitted_spec HndA HlA HsA) as [HfA HnA].
  destruct (omitted_spec HndB HlB HsB) as [HfB HnB].
  assert (Hstep : forall X Y,
             filter (fun x => negb (memb x X)) (seg (S m)) = [omitted m X] ->
             Subset Y (seg (S m)) -> ~ In (omitted m X) Y ->
             Subset Y X).
  { intros X Y HfX HsY HnY z Hz.
    destruct (in_dec_nat z X) as [Hin | Hin]; [exact Hin|].
    exfalso.
    assert (Hzin : In z (filter (fun x => negb (memb x X)) (seg (S m)))).
    { apply filter_In; split; [apply HsY; exact Hz|].
      apply Bool.negb_true_iff, memb_false_iff; exact Hin. }
    rewrite HfX in Hzin; simpl in Hzin; destruct Hzin as [E | []].
    subst z; apply HnY; exact Hz. }
  split.
  - apply (Hstep B A HfB HsA); rewrite <- Heq; exact HnA.
  - apply (Hstep A B HfA HsB); rewrite Heq; exact HnB.
Qed.

Theorem compressed_bound :
  forall F m,
    1 <= m -> LeftCompressed F -> Uniform m F -> Distinct F ->
    ~ ContainsKSunflower 3 F ->
    length F <= m + 1.
Proof.
  intros F m Hm Hlc Hun Hd Hno.
  assert (Hground : forall A, In A F -> Subset A (seg (S m))).
  { intros A HA; eapply compressed_lives_on_m_plus_one_points; eassumption. }
  assert (Huni : forall A, In A F -> UniformSet m A)
    by (unfold Uniform in Hun; rewrite Forall_forall in Hun; auto).
  assert (Hinj : NoDup (map (omitted m) F)).
  { apply NoDup_map_inj; [apply SetNoDup_NoDup; exact Hd|].
    intros A B HA HB Heq.
    destruct (Huni A HA) as [HlA HnA]; destruct (Huni B HB) as [HlB HnB].
    apply (SetNoDup_setEq_eq Hd HA HB).
    apply (omitted_injective HnA HlA (Hground A HA) HnB HlB (Hground B HB) Heq). }
  assert (Hincl : incl (map (omitted m) F) (seg (S m))).
  { intros y Hy; apply in_map_iff in Hy as [A [Heq HA]].
    destruct (Huni A HA) as [HlA HnA].
    destruct (omitted_spec HnA HlA (Hground A HA)) as [Hf _].
    assert (Hin : In (omitted m A) (filter (fun x => negb (memb x A)) (seg (S m))))
      by (rewrite Hf; left; reflexivity).
    apply filter_In in Hin as [Hin _]; subst y; exact Hin. }
  pose proof (NoDup_incl_length Hinj Hincl) as Hlen.
  rewrite map_length, seg_len in Hlen; lia.
Qed.

(** ** The bound is attained

    All [m]-subsets of an [(m+1)]-set is left-compressed, sunflower-free
    and of size [m+1]. Checked here at [m = 2] and [m = 3], reflectively
    and by hand; [rust/tests/shifting.rs] runs the same three checks to
    [m = 12], and [max_left_compressed] there confirms exhaustively that
    nothing larger exists on any ground set in range. *)

Definition triangle : Family := [[0;1]; [0;2]; [1;2]].

Lemma triangle_uniform : Uniform 2 triangle.
Proof. apply uniformb_correct; reflexivity. Qed.

Lemma triangle_distinct : Distinct triangle.
Proof. apply distinctb_correct; reflexivity. Qed.

Lemma triangle_no_sunflower : ~ ContainsKSunflower 3 triangle.
Proof. intro Hc; apply sunflower3b_sound in Hc; vm_compute in Hc; discriminate. Qed.

Ltac shift_seteq :=
  unfold shift_member, rem_elt; simpl;
  split; intros ? Hx; simpl in Hx |- *; tauto.

Lemma triangle_compressed : LeftCompressed triangle.
Proof.
  intros A i j HA Hij HjA HiA.
  simpl in HA; destruct HA as [E | [E | [E | []]]]; subst A;
    simpl in HjA; destruct HjA as [E | [E | []]]; subst j.
  - exfalso; lia.
  - assert (Hi : i = 0) by lia; subst i; exfalso; apply HiA; simpl; auto.
  - exfalso; lia.
  - destruct (Nat.eq_dec i 0) as [E | NE].
    + subst i; exfalso; apply HiA; simpl; auto.
    + assert (Hi : i = 1) by lia; subst i.
      exists [0;1]; split; [simpl; auto | shift_seteq].
  - assert (Hi : i = 0) by lia; subst i.
    exists [0;2]; split; [simpl; auto | shift_seteq].
  - destruct (Nat.eq_dec i 1) as [E | NE].
    + subst i; exfalso; apply HiA; simpl; auto.
    + assert (Hi : i = 0) by lia; subst i.
      exists [0;1]; split; [simpl; auto | shift_seteq].
Qed.

Theorem compressed_bound_is_attained :
  exists F, Uniform 2 F /\ Distinct F /\ LeftCompressed F
            /\ ~ ContainsKSunflower 3 F /\ length F = 2 + 1.
Proof.
  exists triangle; repeat split.
  - exact triangle_uniform.
  - exact triangle_distinct.
  - exact triangle_compressed.
  - exact triangle_no_sunflower.
Qed.

(** ** What compression would have bought, had it worked

    [SliceRank.GroundBounded c] is the one fact that turns Naslund–Sawin
    into the conjecture at [k = 3]. Compression would give it with
    [c = 2] — indeed on [m+1] points rather than [2m]. This is the "too
    good to be true" reading of the shifting method, and the implication
    really does hold; it is the hypothesis that fails. *)

Definition CompressionPreservesSunflowerFree : Prop :=
  forall m F,
    1 <= m -> Uniform m F -> Distinct F -> ~ ContainsKSunflower 3 F ->
    exists G,
      Uniform m G /\ Distinct G /\ length G = length F
      /\ ~ ContainsKSunflower 3 G /\ LeftCompressed G.

Theorem compression_would_give_ground_bounded :
  CompressionPreservesSunflowerFree -> GroundBounded 2.
Proof.
  intros HC m j Hm HL.
  destruct HL as [F [Hun [Hd [Hlen Hno]]]].
  destruct (HC m F Hm Hun Hd Hno) as [G [HunG [HdG [HlenG [HnoG HlcG]]]]].
  exists G, (seg (S m)).
  repeat split; try assumption.
  - lia.
  - apply seg_nodup.
  - intros A HA; eapply compressed_lives_on_m_plus_one_points; eassumption.
  - rewrite seg_len; lia.
Qed.

Theorem compression_would_settle_k3 :
  NaslundSawinBound -> CompressionPreservesSunflowerFree ->
  forall m j, 1 <= m -> LowerBound m 3 j -> j <= (27 ^ 3) ^ m.
Proof.
  intros NS HC m j Hm HL.
  exact (bounded_ground_set_settles_k3 NS 2 ltac:(lia)
           (compression_would_give_ground_bounded HC) m j Hm HL).
Qed.

(** ** But it does not preserve sunflower-freeness

    [F23.f_2_3_lower] exhibits six 2-uniform sunflower-free sets. A
    compressed family at uniformity 2 has at most three. *)

Theorem compression_does_not_preserve_sunflower_freeness :
  ~ CompressionPreservesSunflowerFree.
Proof.
  intro HC.
  destruct f_2_3_lower as [F [Hun [Hd [Hlen Hno]]]].
  destruct (HC 2 F ltac:(lia) Hun Hd Hno) as [G [HunG [HdG [HlenG [HnoG HlcG]]]]].
  assert (Hb : length G <= 2 + 1)
    by (apply compressed_bound with (m := 2); try assumption; lia).
  lia.
Qed.

(** The same refutation drawn through the *ground-set* half instead, so
    the two halves are independently load-bearing: compression would put
    six distinct 2-sets on three points, and there are only three. *)

Theorem compression_would_overfill_the_ground_set :
  ~ CompressionPreservesSunflowerFree.
Proof.
  intro HC.
  destruct f_2_3_lower as [F [Hun [Hd [Hlen Hno]]]].
  destruct (HC 2 F ltac:(lia) Hun Hd Hno) as [G [HunG [HdG [HlenG [HnoG HlcG]]]]].
  assert (Hg : forall A, In A G -> Subset A (seg 3)).
  { intros A HA.
    apply (compressed_lives_on_m_plus_one_points (F := G) (m := 2));
      try assumption; lia. }
  (* Six distinct 2-subsets of a 3-point ground set. There are three. *)
  assert (Hb : length G <= 2 + 1)
    by (apply compressed_bound with (m := 2); try assumption; lia).
  assert (Hcount : length (seg 3) = 3) by (rewrite seg_len; reflexivity).
  clear Hg Hcount; lia.
Qed.

(** ** The shift of a family, and the single shift that does it

    The operation itself, with the guard that makes it injective: a
    member moves only when the image is not already present. *)

Definition setmemb (A : list nat) (F : Family) : bool :=
  existsb (fun B => seteqb A B) F.

Definition shift_one (i j : nat) (F : Family) (A : list nat) : list nat :=
  if memb j A && negb (memb i A) && negb (setmemb (shift_member i j A) F)
  then shift_member i j A
  else A.

Definition shift_family (i j : nat) (F : Family) : Family :=
  map (shift_one i j F) F.

(** The controls, proved rather than measured: the shift keeps the size
    of the family and the size of every member. These are two of the
    four properties [rust/tests/shifting.rs] checks exhaustively, and
    they are what make the counterexample below say something — a shift
    that lost members or changed the uniformity would create sunflowers
    for a trivial reason. *)

Theorem shift_family_length : forall i j F,
    length (shift_family i j F) = length F.
Proof. intros i j F; unfold shift_family; apply map_length. Qed.

Lemma shift_member_uniform : forall i j A n,
    UniformSet n A -> In j A -> ~ In i A -> UniformSet n (shift_member i j A).
Proof.
  intros i j A n [Hlen Hnd] Hj Hi; unfold shift_member; split.
  - simpl; rewrite length_rem_elt_in by assumption.
    destruct A; simpl in *; [contradiction | lia].
  - constructor; [rewrite in_rem_iff; tauto | apply rem_NoDup; exact Hnd].
Qed.

Theorem shift_family_uniform : forall i j n F,
    Uniform n F -> Uniform n (shift_family i j F).
Proof.
  intros i j n F Hun; unfold Uniform, shift_family in *.
  rewrite Forall_forall in Hun |- *.
  intros A HA; apply in_map_iff in HA as [B [E HB]]; subst A.
  unfold shift_one.
  destruct (memb j B && negb (memb i B) && negb (setmemb (shift_member i j B) F))
    eqn:Eg; [| apply Hun; exact HB].
  apply Bool.andb_true_iff in Eg as [Eg _].
  apply Bool.andb_true_iff in Eg as [Ej Ei].
  apply shift_member_uniform; [apply Hun; exact HB | | ].
  - apply memb_true_iff; exact Ej.
  - apply memb_false_iff, Bool.negb_true_iff; exact Ei.
Qed.

(** The smallest counterexample there is: three members, which is the
    least a 3-sunflower can have, so shifting fails at the first
    opportunity it is given. [{0,1}, {0,2}, {1,3}] has pairwise
    intersections [{0}], [{1}] and [∅] — three different sets, so no
    sunflower. The [(0,1)]-shift moves only [{1,3}]: [{0,1}] contains
    [0] already and [{0,2}] does not contain [1]. The image [{0,3}] is
    absent, so the move happens, and the result is the star at [0]. *)

Definition shift_witness : Family := [[0;1]; [0;2]; [1;3]].

Lemma shift_witness_uniform : Uniform 2 shift_witness.
Proof. apply uniformb_correct; reflexivity. Qed.

Lemma shift_witness_distinct : Distinct shift_witness.
Proof. apply distinctb_correct; reflexivity. Qed.

Lemma shift_witness_no_sunflower : ~ ContainsKSunflower 3 shift_witness.
Proof. intro Hc; apply sunflower3b_sound in Hc; vm_compute in Hc; discriminate. Qed.

Lemma the_shift_is_the_star : shift_family 0 1 shift_witness = [[0;1]; [0;2]; [0;3]].
Proof. vm_compute; reflexivity. Qed.

Theorem shift_may_create_a_sunflower :
  ~ ContainsKSunflower 3 shift_witness
  /\ ContainsKSunflower 3 (shift_family 0 1 shift_witness)
  /\ length (shift_family 0 1 shift_witness) = length shift_witness
  /\ Uniform 2 (shift_family 0 1 shift_witness).
Proof.
  split; [exact shift_witness_no_sunflower |].
  split; [apply sunflower3b_complete; vm_compute; reflexivity |].
  split; [apply shift_family_length |].
  apply shift_family_uniform, shift_witness_uniform.
Qed.

(** Three members is the least possible: a 3-sunflower has three petals,
    so no family of two can acquire one. Together with the witness this
    says the failure is immediate — there is no range of small
    parameters in which compression is safe. *)

Theorem two_members_cannot_acquire_a_sunflower :
  forall F, length F <= 2 -> ~ ContainsKSunflower 3 F.
Proof. intros F Hlen; apply no_k_sunflower_short_family; lia. Qed.
