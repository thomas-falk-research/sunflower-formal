(** * LowerBound.v -- Lower bounds on f(n, k).

    Theorem [lower_bound_trivial]: [f(n, k) ≥ k] for [n ≥ 1] and
    [k ≥ 2]. Construction: take [k-1] pairwise-disjoint blocks of [n]
    consecutive integers each. The family has [k-1] members so no
    SetEq-distinct sub-family of size [k] can be witnessed by it.

    The standard *exponential* lower bound [f(n, k) ≥ (k-1)^n + 1]
    (Erdős–Rado 1960) is proved by the product-of-rows construction;
    it is fully formalized in [ProductLowerBound.v]
    ([lower_bound_exponential]), which reuses this file's [witness]
    machinery. Combined with the Erdős–Rado upper bound in
    [ErdosRado.v] the bracketing is
    [(k-1)^n + 1 ≤ f(n, k) ≤ (k-1)^n · n! + 1] for all
    [n ≥ 1, k ≥ 2]. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower.
Import ListNotations.

Set Implicit Arguments.

(** ** Decidable set-equality *)

Definition seteqb (A B : list nat) : bool :=
  forallb (fun x => memb x B) A && forallb (fun x => memb x A) B.

Lemma seteqb_correct : forall A B, seteqb A B = true <-> SetEq A B.
Proof.
  intros A B; unfold seteqb, SetEq, Subset; split.
  - intros Hand. apply Bool.andb_true_iff in Hand as [H1 H2].
    rewrite forallb_forall in H1, H2.
    split; intros x Hx.
    + specialize (H1 x Hx). apply memb_true_iff; exact H1.
    + specialize (H2 x Hx). apply memb_true_iff; exact H2.
  - intros [Hs1 Hs2]. apply Bool.andb_true_iff; split; apply forallb_forall.
    + intros x Hx; apply memb_true_iff. apply Hs1; exact Hx.
    + intros x Hx; apply memb_true_iff. apply Hs2; exact Hx.
Qed.

(** ** Witness: for [A ∈ S], pick the first [B ∈ F] set-equal to [A] *)

Definition witness (F : Family) (A : list nat) : list nat :=
  match find (seteqb A) F with
  | Some B => B
  | None => []
  end.

Lemma witness_spec : forall F A,
    (exists B, In B F /\ SetEq A B) ->
    In (witness F A) F /\ SetEq A (witness F A).
Proof.
  intros F A [B [HB Hseq]].
  unfold witness.
  destruct (find (seteqb A) F) as [B' |] eqn:Hfind.
  - apply find_some in Hfind as [HBF' Hseq'].
    split; [exact HBF' | apply seteqb_correct; exact Hseq'].
  - exfalso. assert (Hseq_b : seteqb A B = true) by (apply seteqb_correct; exact Hseq).
    pose proof (find_none _ F Hfind B HB) as Hneg.
    rewrite Hseq_b in Hneg; discriminate.
Qed.

(** ** SetNoDup S + SubFamilySetEq S F → length S ≤ length F *)

Lemma witness_injective : forall F S,
    SetNoDup S ->
    SubFamilySetEq S F ->
    forall A A', In A S -> In A' S -> witness F A = witness F A' -> A = A'.
Proof.
  intros F S Hsnd Hsub A A' HA HA' Heq.
  destruct (list_eq_dec Nat.eq_dec A A') as [E | NE]; [exact E|].
  exfalso.
  pose proof (@witness_spec F A (Hsub A HA)) as [_ HseqA].
  pose proof (@witness_spec F A' (Hsub A' HA')) as [_ HseqA'].
  rewrite <- Heq in HseqA'.
  pose proof (SetEq_trans HseqA (SetEq_sym HseqA')) as Hseq.
  apply (SetNoDup_pairwise Hsnd HA HA' NE); exact Hseq.
Qed.

Lemma map_witness_NoDup : forall F S,
    SetNoDup S ->
    SubFamilySetEq S F ->
    NoDup (map (witness F) S).
Proof.
  intros F S Hsnd Hsub.
  pose proof (SetNoDup_NoDup Hsnd) as HndS.
  induction HndS as [|A S' HniA HndS' IH]; simpl; [constructor|].
  inversion Hsnd as [|? ? HniA_set Hsnd']; subst.
  constructor.
  - intro Hin. apply in_map_iff in Hin as [A' [Hw HA'in]].
    assert (HAS : In A (A :: S')) by (left; reflexivity).
    assert (HA'S : In A' (A :: S')) by (right; exact HA'in).
    pose proof (@witness_injective F (A :: S') Hsnd Hsub A A' HAS HA'S (eq_sym Hw)) as E.
    subst A'; contradiction.
  - apply IH; [exact Hsnd'|].
    intros B HB. apply Hsub. right; exact HB.
Qed.

Lemma map_witness_incl : forall F S,
    SubFamilySetEq S F -> incl (map (witness F) S) F.
Proof.
  intros F S Hsub B HB.
  apply in_map_iff in HB as [A [Hw HA]].
  pose proof (@witness_spec F A (Hsub A HA)) as [HinF _].
  rewrite Hw in HinF; exact HinF.
Qed.

Lemma SubFamilySetEq_length :
  forall S F, SetNoDup S -> SubFamilySetEq S F -> length S <= length F.
Proof.
  intros S F Hsnd Hsub.
  rewrite <- (map_length (witness F) S).
  apply NoDup_incl_length.
  - apply map_witness_NoDup; auto.
  - apply map_witness_incl; auto.
Qed.

(** ** Short families cannot contain a k-sunflower *)

Theorem no_k_sunflower_short_family :
  forall (F : Family) k,
    length F < k ->
    ~ ContainsKSunflower k F.
Proof.
  intros F k Hlt [S [HSF [HSlen [core HSun]]]].
  destruct HSun as [HSnd _].
  pose proof (SubFamilySetEq_length HSnd HSF) as Hle.
  lia.
Qed.

(** ** The [k-1] disjoint blocks of size [n] *)

Fixpoint block (start length : nat) : list nat :=
  match length with
  | 0 => []
  | S length' => start :: block (S start) length'
  end.

Lemma block_length : forall start length, List.length (block start length) = length.
Proof.
  intros start l; revert start; induction l as [|l' IH]; intros; simpl; auto.
Qed.

Lemma in_block_iff : forall start length x,
    In x (block start length) <-> start <= x < start + length.
Proof.
  intros start length; revert start.
  induction length as [|l' IH]; intros start x; simpl.
  - split; [intros []|]. intros []; lia.
  - split.
    + intros [E | H]; [lia|]. apply IH in H; lia.
    + intros [Hge Hlt].
      destruct (Nat.eq_dec x start) as [E|NE]; [left; symmetry; exact E|].
      right. apply IH; lia.
Qed.

Lemma block_NoDup : forall start length, NoDup (block start length).
Proof.
  intros start l; revert start; induction l as [|l' IH]; intros start; simpl.
  - constructor.
  - constructor; [|apply IH].
    intro Hin; apply in_block_iff in Hin; lia.
Qed.

(** ** The trivial lower-bound family *)

Fixpoint disjoint_blocks (count n : nat) : Family :=
  match count with
  | 0 => []
  | S count' => block (count' * n) n :: disjoint_blocks count' n
  end.

Lemma disjoint_blocks_length : forall count n,
    List.length (disjoint_blocks count n) = count.
Proof.
  induction count as [|c IH]; intros; simpl; auto.
Qed.

Lemma in_disjoint_blocks_iff : forall count n A,
    In A (disjoint_blocks count n) <-> exists i, i < count /\ A = block (i * n) n.
Proof.
  intros count n A; induction count as [|c IH]; simpl.
  - split; [intros [] | intros [i [Hi _]]; lia].
  - split.
    + intros [E | H].
      * exists c; split; [lia | symmetry; exact E].
      * apply IH in H as [i [Hi HA]]. exists i; split; [lia | exact HA].
    + intros [i [Hi HA]].
      destruct (Nat.eq_dec i c) as [E | NE].
      * subst i; left; symmetry; exact HA.
      * right; apply IH. exists i; split; [lia | exact HA].
Qed.

Lemma disjoint_blocks_Uniform : forall count n,
    n >= 1 -> Uniform n (disjoint_blocks count n).
Proof.
  intros count n Hn. unfold Uniform.
  apply Forall_forall. intros A HA.
  apply in_disjoint_blocks_iff in HA as [i [Hi HA]].
  subst A. split; [apply block_length | apply block_NoDup].
Qed.

Lemma disjoint_blocks_pairwise_disjoint : forall count n,
    n >= 1 ->
    forall i j, i < count -> j < count -> i <> j ->
                Disjoint (block (i * n) n) (block (j * n) n).
Proof.
  intros count n Hn i j Hi Hj Hij.
  unfold Disjoint. intros x HxI HxJ.
  apply in_block_iff in HxI; apply in_block_iff in HxJ.
  destruct (Nat.lt_trichotomy i j) as [Hlt | [Heq | Hgt]]; [|contradiction|]; nia.
Qed.

Lemma block_nonempty : forall start n, n >= 1 -> block start n <> [].
Proof.
  intros start n Hn; destruct n; [lia | simpl; discriminate].
Qed.

Lemma disjoint_blocks_SetNoDup : forall count n,
    n >= 1 -> SetNoDup (disjoint_blocks count n).
Proof.
  intros count n Hn; induction count as [|c IH]; simpl; [constructor|].
  constructor.
  - intros B HB Hseq.
    apply in_disjoint_blocks_iff in HB as [i [Hi HA]]; subst B.
    assert (Hcne : c <> i) by lia.
    pose proof (@disjoint_blocks_pairwise_disjoint (S c) n Hn c i
                  (Nat.lt_succ_diag_r _) (Nat.lt_lt_succ_r _ _ Hi)
                  Hcne)
      as Hdis.
    (* Pick x = first element of block (c*n) n (it has one since n >= 1). *)
    pose (x := c * n).
    assert (Hxblk_c : In x (block (c * n) n)).
    { apply in_block_iff. unfold x; lia. }
    destruct Hseq as [Hs _].
    assert (Hxblk_i : In x (block (i * n) n)) by (apply Hs; exact Hxblk_c).
    apply (Hdis x); auto.
  - apply IH.
Qed.

(** ** Main theorem: [f(n, k) ≥ k] *)

Theorem lower_bound_trivial :
  forall n k, n >= 1 -> k >= 2 -> LowerBound n k (k - 1).
Proof.
  intros n k Hn Hk.
  unfold LowerBound.
  exists (disjoint_blocks (k - 1) n).
  split; [|split; [|split]].
  - apply disjoint_blocks_Uniform; exact Hn.
  - apply disjoint_blocks_SetNoDup; exact Hn.
  - apply disjoint_blocks_length.
  - apply no_k_sunflower_short_family.
    rewrite disjoint_blocks_length. lia.
Qed.

(** ** Restating: every [k]-sunflower has at least [k] sets *)

Corollary f_n_k_ge_k :
  forall n k, n >= 1 -> k >= 2 ->
              ~ UpperBound n k (k - 1).
Proof.
  intros n k Hn Hk Hup.
  destruct (lower_bound_trivial Hn Hk) as [F [HU [HD [Hlen Hno]]]].
  apply Hno. apply Hup; [exact HU | exact HD | lia].
Qed.
