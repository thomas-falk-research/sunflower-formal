(** * Fragment.v -- Stage B of the spread lemma: the minimal fragment,
      Claim 3.3, and the encoding of Claim 3.4.

    `docs/roadmap.md` §1 stages the discharge of [ALWZ.Rao20_lemma2]
    through the counting proof, [Lovett] §3. Stage A is
    [coq/Counting.v]. This is Stage B, and everything below is quoted
    from **rendered** pages (pp. 12–13; `pdftoppm -png -r 150`, the
    PDF's sha256 matching `docs/papers/manifest.json`):

    >  **Definition 3.2.** `M(S,V)` is a minimum-size element of
    >  `{S' \ V : S' ∈ F, S' ⊂ S ∪ V}`.
    >
    >  1. `M(S,V) ⊂ S`.
    >  2. `M(S,V)` is disjoint from `V`.
    >  3. `M(S,V) = ∅` iff there exists `S' ∈ F` with `S' ⊂ V`.
    >
    >  **Claim 3.3.** Let `F` be a family of sets, `S ∈ F`, and fix a set
    >  `V`. Define `Z = V ∪ M(S,V)` and `F' = {S' ∈ F : S' ⊂ Z}`. Then:
    >  1. `F'` is not empty.
    >  2. Any `S' ∈ F'` satisfies `S' \ V = M(S,V)`. In particular
    >  `M(S,V) ⊂ S'`.
    >
    >  **Claim 3.4** (the encoding). `φ(S,V) = (Z, S', M, S \ M)`.
    >  *"Note that we can decode `(S,V)` given `φ(S,V)` since
    >  `S = M ∪ (S \ M)` and `V = Z \ M`."*

    ** What was checked before any of this was proved

    [rust/tests/fragment.rs] runs the definition, the three
    observations, both parts of Claim 3.3, the decode and the
    injectivity over **every** family of at most three subsets of a
    three- or four-element universe, and at most four subsets of a
    two-element one — 32968 triples `(F,S,V)`, exhaustive. §1's
    instruction was explicit about this (*"the cost of finding out a
    lemma is false after half a session of proof is the main way this
    campaign goes wrong"*), and it is why the proofs below went in
    without a false start.

    ** Two things the rendered pages settle that a summary would not

    *"Breaking ties arbitrarily"* becomes **first in the enumeration**,
    which is what makes [minimal_fragment] a function rather than a
    choice. And the candidate family is never empty when [S ∈ F],
    because `S ⊂ S ∪ V` makes `S` its own candidate — so the definition
    needs no junk default and [minimal_fragment_in_cands] has no side
    condition beyond [In S F].

    ** The decode is literal in one component and set-level in the other

    `V = Z \ M` holds **on the nose** as lists: `Z` is built as
    `V ++ M` and `M` is disjoint from `V`, so removing `M` returns `V`
    unchanged. `S = M ∪ (S \ M)` cannot be literal — it reorders — so it
    is proved as [SetEq] and then upgraded to equality by
    [Sets.SetNoDup_setEq_eq], using nothing but [Distinct F] and
    [In S F]. That is [psi_phi], and it is the obligation §1 identified
    as *an equation, not a case analysis*.
*)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower Spread Counting.
Import ListNotations.

Set Implicit Arguments.

(** ** The candidate fragments

    `{S' \ V : S' ∈ F, S' ⊂ S ∪ V}`, as a list. [Spread.add_set S V] is
    `S ∪ V` and [Spread.containsb A B] decides `A ⊂ B`. *)

Definition frag_cands (F : Family) (S V : list nat) : list (list nat) :=
  map (fun A => setminus A V)
      (filter (fun A => containsb A (add_set S V)) F).

Lemma in_frag_cands :
  forall F S V C,
    In C (frag_cands F S V) <->
    exists A, In A F /\ Subset A (add_set S V) /\ C = setminus A V.
Proof.
  intros F S V C; unfold frag_cands; split.
  - intros H; apply in_map_iff in H as [A [E HA]].
    apply filter_In in HA as [HAF Hc].
    exists A; split; [exact HAF | split;
      [apply containsb_true_iff; exact Hc | symmetry; exact E]].
  - intros [A [HAF [Hsub E]]]; subst C.
    apply in_map_iff; exists A; split; [reflexivity|].
    apply filter_In; split; [exact HAF | apply containsb_true_iff; exact Hsub].
Qed.

(** [S] is always among its own candidates. *)

Lemma self_in_frag_cands :
  forall F S V, In S F -> In (setminus S V) (frag_cands F S V).
Proof.
  intros F S V HS; apply in_frag_cands.
  exists S; split; [exact HS | split; [| reflexivity]].
  intros x Hx; apply in_add_set_iff; left; exact Hx.
Qed.

(** ** Minimising, with ties broken by position

    Lovett's *"breaking ties arbitrarily"*. A strict [<?] keeps the
    earlier element, so this is "the first element of minimum length". *)

Fixpoint argmin_len (best : list nat) (l : list (list nat)) : list nat :=
  match l with
  | [] => best
  | A :: l' =>
      if length A <? length best then argmin_len A l' else argmin_len best l'
  end.

Lemma argmin_len_spec :
  forall l b,
    (argmin_len b l = b \/ In (argmin_len b l) l)
    /\ length (argmin_len b l) <= length b
    /\ (forall A, In A l -> length (argmin_len b l) <= length A).
Proof.
  induction l as [|A l IH]; intros b; simpl.
  - split; [left; reflexivity | split; [lia | intros ? []]].
  - destruct (Nat.ltb_spec (length A) (length b)) as [Hlt | Hge].
    + destruct (IH A) as [Hcase [Hle Hmin]].
      repeat split.
      * destruct Hcase as [E | Hin]; [right; left; symmetry; exact E
                                     | right; right; exact Hin].
      * lia.
      * intros C HC; destruct HC as [E | HC]; [subst C; exact Hle | apply Hmin; exact HC].
    + destruct (IH b) as [Hcase [Hle Hmin]].
      repeat split.
      * destruct Hcase as [E | Hin]; [left; exact E | right; right; exact Hin].
      * exact Hle.
      * intros C HC; destruct HC as [E | HC];
          [subst C; lia | apply Hmin; exact HC].
Qed.

(** ** Definition 3.2 *)

Definition minimal_fragment (F : Family) (S V : list nat) : list nat :=
  argmin_len (setminus S V) (frag_cands F S V).

Lemma minimal_fragment_in_cands :
  forall F S V, In S F -> In (minimal_fragment F S V) (frag_cands F S V).
Proof.
  intros F S V HS; unfold minimal_fragment.
  destruct (argmin_len_spec (frag_cands F S V) (setminus S V))
    as [[E | Hin] _].
  - rewrite E; apply self_in_frag_cands; exact HS.
  - exact Hin.
Qed.

Lemma minimal_fragment_le :
  forall F S V C,
    In C (frag_cands F S V) ->
    length (minimal_fragment F S V) <= length C.
Proof.
  intros F S V C HC; unfold minimal_fragment.
  destruct (argmin_len_spec (frag_cands F S V) (setminus S V))
    as [_ [_ Hmin]].
  apply Hmin; exact HC.
Qed.

(** ** The three observations *)

(** **Observation 1**: `M(S,V) ⊂ S`. *)

Theorem fragment_subset_S :
  forall F S V, In S F -> Subset (minimal_fragment F S V) S.
Proof.
  intros F S V HS.
  destruct (proj1 (in_frag_cands F S V _) (@minimal_fragment_in_cands F S V HS))
    as [A [HAF [Hsub E]]].
  rewrite E; intros x Hx.
  apply in_setminus_iff in Hx as [HxA HxV].
  destruct (proj1 (in_add_set_iff _ _ _) (Hsub x HxA)) as [HxS | HxV'];
    [exact HxS | contradiction].
Qed.

(** **Observation 2**: `M(S,V)` is disjoint from `V`. *)

Theorem fragment_disjoint_V :
  forall F S V, In S F -> Disjoint (minimal_fragment F S V) V.
Proof.
  intros F S V HS.
  destruct (proj1 (in_frag_cands F S V _) (@minimal_fragment_in_cands F S V HS))
    as [A [_ [_ E]]].
  rewrite E; apply setminus_disjoint.
Qed.

(** **Observation 3**: `M(S,V) = ∅` iff some member of `F` sits inside
    `V`. *)

Theorem fragment_nil_iff :
  forall F S V,
    In S F ->
    (minimal_fragment F S V = [] <-> exists A, In A F /\ Subset A V).
Proof.
  intros F S V HS; split.
  - intros Hnil.
    destruct (proj1 (in_frag_cands F S V _) (@minimal_fragment_in_cands F S V HS))
      as [A [HAF [_ E]]].
    exists A; split; [exact HAF|].
    intros x HxA.
    destruct (in_dec Nat.eq_dec x V) as [HxV | HxV]; [exact HxV | exfalso].
    assert (Hin : In x (setminus A V))
      by (apply in_setminus_iff; split; assumption).
    rewrite <- E, Hnil in Hin; inversion Hin.
  - intros [A [HAF Hsub]].
    assert (Hc : In (setminus A V) (frag_cands F S V)).
    { apply in_frag_cands; exists A; split; [exact HAF | split; [| reflexivity]].
      intros x Hx; apply in_add_set_iff; right; apply Hsub; exact Hx. }
    assert (Hempty : setminus A V = []).
    { destruct (setminus A V) as [|y r] eqn:Er; [reflexivity | exfalso].
      assert (Hy : In y (setminus A V)) by (rewrite Er; left; reflexivity).
      apply in_setminus_iff in Hy as [HyA HyV]; apply HyV, Hsub, HyA. }
    pose proof (@minimal_fragment_le F S V _ Hc) as Hle.
    rewrite Hempty in Hle; simpl in Hle.
    destruct (minimal_fragment F S V); [reflexivity | simpl in Hle; lia].
Qed.

(** ** Claim 3.3

    `Z = V ∪ M(S,V)` and `F' = {S' ∈ F : S' ⊂ Z}`. *)

Definition frag_Z (F : Family) (S V : list nat) : list nat :=
  add_set V (minimal_fragment F S V).

Definition frag_F' (F : Family) (Z : list nat) : Family :=
  filter (fun A => containsb A Z) F.

Lemma in_frag_F' :
  forall F Z A, In A (frag_F' F Z) <-> In A F /\ Subset A Z.
Proof.
  intros F Z A; unfold frag_F'; rewrite filter_In; split.
  - intros [H1 H2]; split; [exact H1 | apply containsb_true_iff; exact H2].
  - intros [H1 H2]; split; [exact H1 | apply containsb_true_iff; exact H2].
Qed.

(** [Z] is inside `S ∪ V`, which is what makes every member of [F'] a
    candidate for the minimal fragment. *)

Lemma frag_Z_subset :
  forall F S V, In S F -> Subset (frag_Z F S V) (add_set S V).
Proof.
  intros F S V HS x Hx; unfold frag_Z in Hx.
  apply in_add_set_iff in Hx as [HxV | HxM]; apply in_add_set_iff.
  - right; exact HxV.
  - left; apply (@fragment_subset_S F S V HS); exact HxM.
Qed.

(** **Claim 3.3 (1)**: `F'` is not empty — the witness is the member
    that realised the minimal fragment. *)

Theorem frag_F'_nonempty :
  forall F S V, In S F -> exists A, In A (frag_F' F (frag_Z F S V)).
Proof.
  intros F S V HS.
  destruct (proj1 (in_frag_cands F S V _) (@minimal_fragment_in_cands F S V HS))
    as [A [HAF [Hsub E]]].
  exists A; apply in_frag_F'; split; [exact HAF|].
  intros x HxA; unfold frag_Z; apply in_add_set_iff.
  destruct (in_dec Nat.eq_dec x V) as [HxV | HxV]; [left; exact HxV | right].
  rewrite E; apply in_setminus_iff; split; assumption.
Qed.

(** **Claim 3.3 (2)**: every member of `F'` has `S' \ V = M(S,V)`.

    Both inclusions: `S' ⊂ Z` gives `S' \ V ⊂ M` directly, and
    minimality gives `|M| ≤ |S' \ V|`; a subset of the same size is the
    whole thing. *)

Theorem frag_F'_fragment :
  forall F S V A,
    In S F -> Forall (fun B : list nat => NoDup B) F ->
    In A (frag_F' F (frag_Z F S V)) ->
    SetEq (setminus A V) (minimal_fragment F S V).
Proof.
  intros F S V A HS Hnd HA.
  apply in_frag_F' in HA as [HAF HAZ].
  (* [A] is a candidate, because [A ⊂ Z ⊂ S ∪ V] *)
  assert (Hcand : In (setminus A V) (frag_cands F S V)).
  { apply in_frag_cands; exists A; split; [exact HAF | split; [| reflexivity]].
    intros x Hx; apply (@frag_Z_subset F S V HS); apply HAZ; exact Hx. }
  (* one inclusion is immediate from [A ⊂ Z = V ∪ M] *)
  assert (Hsub : Subset (setminus A V) (minimal_fragment F S V)).
  { intros x Hx; apply in_setminus_iff in Hx as [HxA HxV].
    pose proof (HAZ x HxA) as HxZ; unfold frag_Z in HxZ.
    apply in_add_set_iff in HxZ as [HxV' | HxM]; [contradiction | exact HxM]. }
  (* and the other from minimality plus a length count *)
  pose proof (@minimal_fragment_le F S V _ Hcand) as Hlen.
  assert (HAnd : NoDup A) by (rewrite Forall_forall in Hnd; apply Hnd; exact HAF).
  assert (Hnd1 : NoDup (setminus A V)) by (apply setminus_NoDup; exact HAnd).
  assert (Heq : length (setminus A V) = length (minimal_fragment F S V)).
  { pose proof (NoDup_incl_length Hnd1 Hsub) as H1; lia. }
  split; [exact Hsub|].
  (* a [NoDup] subset of equal length is onto *)
  intros x Hx.
  destruct (in_dec Nat.eq_dec x (setminus A V)) as [Hin | Hnotin];
    [exact Hin | exfalso].
  assert (Hstrict : incl (x :: setminus A V) (minimal_fragment F S V)).
  { intros y Hy; destruct Hy as [<- | Hy]; [exact Hx | apply Hsub; exact Hy]. }
  assert (Hndx : NoDup (x :: setminus A V)) by (constructor; assumption).
  pose proof (NoDup_incl_length Hndx Hstrict) as H2; simpl in H2; lia.
Qed.

(** ** The encoding of Claim 3.4

    `φ(S,V) = (Z, S', M, S \ M)`. The second component is the first
    member of `F` inside `Z` — *"Fix `S' ∈ F'` arbitrarily (say, first in
    some pre-defined order)"* — and it is a function of `Z` alone, which
    is why it costs the count nothing. *)

Definition first_in (F : Family) (Z : list nat) : list nat :=
  hd [] (frag_F' F Z).

Definition phi (F : Family) (S V : list nat)
  : list nat * list nat * list nat * list nat :=
  let M := minimal_fragment F S V in
  (frag_Z F S V, first_in F (frag_Z F S V), M, setminus S M).

Definition psi (t : list nat * list nat * list nat * list nat)
  : list nat * list nat :=
  let '(Z, _, M, R) := t in (add_set M R, setminus Z M).

(** *** The [V] component decodes on the nose

    `Z` is literally `V ++ M` — [add_set V M] is `V ++ setminus M V`, and
    `M` is disjoint from `V` — so filtering `M` out of it returns `V`
    itself, not merely a set equal to it. *)

Lemma setminus_of_disjoint :
  forall A T, Disjoint A T -> setminus A T = A.
Proof.
  intros A T Hdisj; unfold setminus.
  induction A as [|a A IH]; simpl; [reflexivity|].
  destruct (memb a T) eqn:Em.
  - exfalso; apply (Hdisj a); [left; reflexivity | apply memb_true_iff; exact Em].
  - simpl; f_equal; apply IH.
    intros x Hx1 Hx2; apply (Hdisj x); [right; exact Hx1 | exact Hx2].
Qed.

Lemma setminus_app :
  forall A B T, setminus (A ++ B) T = setminus A T ++ setminus B T.
Proof. intros A B T; unfold setminus; apply filter_app. Qed.

Lemma setminus_self : forall A, setminus A A = [].
Proof.
  intros A; unfold setminus.
  assert (H : forall l, Subset l A -> filter (fun x => negb (memb x A)) l = []).
  { induction l as [|a l IH]; intros Hsub; simpl; [reflexivity|].
    destruct (memb a A) eqn:Em; simpl.
    - apply IH; intros y Hy; apply Hsub; right; exact Hy.
    - exfalso; apply (Bool.eq_true_false_abs (memb a A));
        [apply memb_true_iff; apply Hsub; left; reflexivity | exact Em]. }
  apply H; intros x Hx; exact Hx.
Qed.

Theorem frag_Z_minus_fragment :
  forall F S V,
    In S F -> setminus (frag_Z F S V) (minimal_fragment F S V) = V.
Proof.
  intros F S V HS; unfold frag_Z, add_set.
  rewrite (setminus_of_disjoint (@fragment_disjoint_V F S V HS)).
  rewrite setminus_app, setminus_self, app_nil_r.
  apply setminus_of_disjoint.
  intros x HxV HxM; apply (@fragment_disjoint_V F S V HS x); assumption.
Qed.

(** *** The [S] component decodes up to [SetEq], and [Distinct] closes
        the gap

    `M ∪ (S \ M)` reorders `S`, so it cannot be literally equal to it.
    It is [SetEq] to it whenever `M ⊂ S`, which is Observation 1, and
    [Sets.SetNoDup_setEq_eq] turns that into equality inside a
    [Distinct] family. *)

Lemma add_set_setminus_SetEq :
  forall M S, Subset M S -> SetEq (add_set M (setminus S M)) S.
Proof.
  intros M S Hsub; split.
  - intros x Hx; apply in_add_set_iff in Hx as [HxM | HxR].
    + apply Hsub; exact HxM.
    + apply in_setminus_iff in HxR as [HxS _]; exact HxS.
  - intros x Hx; apply in_add_set_iff.
    destruct (in_dec Nat.eq_dec x M) as [HxM | HxM]; [left; exact HxM | right].
    apply in_setminus_iff; split; assumption.
Qed.

(** *** The decode, stated correctly

    §1 records the obligation as *"`psi (phi (S,V)) = (S,V)`, which is a
    rewrite, not a case analysis"*. **In a list encoding that is not an
    equation, and the correction is worth stating.** Lovett's
    `S = M ∪ (S \ M)` is an identity of *sets*; as lists,
    [add_set M (setminus S M)] is `M ++ (S \ M)`, a permutation of `S`
    and not `S`. So the decode splits:

    - the `V` half **is** literal ([frag_Z_minus_fragment]);
    - the `S` half is [SetEq] and no more.

    What the count actually needs is not the decode but **injectivity**,
    and [SetEq] is enough for it: two pairs with the same code have the
    same `M` and the same `S \ M`, hence [SetEq] first components, and
    [Sets.SetNoDup_setEq_eq] upgrades that to equality *inside a
    [Distinct] family*. So the hypothesis the encoding needs is
    [Distinct F] — which §1 does not mention, because at the level of
    sets it is invisible. *)

Theorem psi_phi_V :
  forall F S V, In S F -> snd (psi (phi F S V)) = V.
Proof. intros F S V HS; simpl; apply (@frag_Z_minus_fragment F S V HS). Qed.

Theorem psi_phi_SetEq :
  forall F S V, In S F -> SetEq (fst (psi (phi F S V))) S.
Proof.
  intros F S V HS; simpl.
  apply add_set_setminus_SetEq; apply (@fragment_subset_S F S V HS).
Qed.

(** **Injectivity**, which is what Claim 3.4's count consumes. *)

Theorem phi_injective :
  forall F S1 V1 S2 V2,
    Distinct F -> In S1 F -> In S2 F ->
    phi F S1 V1 = phi F S2 V2 ->
    S1 = S2 /\ V1 = V2.
Proof.
  intros F S1 V1 S2 V2 HD H1 H2 Heq.
  assert (HV : V1 = V2).
  { rewrite <- (@psi_phi_V F S1 V1 H1), <- (@psi_phi_V F S2 V2 H2), Heq; reflexivity. }
  split; [| exact HV].
  (* both are SetEq to the *same* decoded list, because the code fixes
     both [M] and [S \ M] *)
  assert (Hfst : fst (psi (phi F S1 V1)) = fst (psi (phi F S2 V2)))
    by (rewrite Heq; reflexivity).
  assert (Hs1 : SetEq (fst (psi (phi F S1 V1))) S1)
    by (apply psi_phi_SetEq; exact H1).
  assert (Hs2 : SetEq (fst (psi (phi F S2 V2))) S2)
    by (apply psi_phi_SetEq; exact H2).
  rewrite Hfst in Hs1.
  apply (@SetNoDup_setEq_eq F); [exact HD | exact H1 | exact H2 |].
  apply (SetEq_trans (SetEq_sym Hs1) Hs2).
Qed.

(** And the corollary in the shape [Counting.count_inj_le] wants: on any
    list of pairs whose first components lie in a [Distinct] family,
    [phi] is injective. *)

Corollary phi_injective_on_pairs :
  forall (F : Family) (L : list (list nat * list nat)),
    Distinct F ->
    (forall p, In p L -> In (fst p) F) ->
    forall p1 p2, In p1 L -> In p2 L ->
      phi F (fst p1) (snd p1) = phi F (fst p2) (snd p2) -> p1 = p2.
Proof.
  intros F L HD Hin [S1 V1] [S2 V2] Hp1 Hp2 Heq.
  destruct (@phi_injective F S1 V1 S2 V2 HD (Hin _ Hp1) (Hin _ Hp2) Heq)
    as [E1 E2].
  simpl in *; subst; reflexivity.
Qed.

(** ** The junction with Stage A

    Two facts connect this file to [coq/Counting.v], and they are the
    two places Claim 3.4's count touches the arithmetic. *)

(** *** `|Z| = |V| + |M|`

    Literal, and it needs no [NoDup]: `Z` is built as [add_set V M] and
    `M` is disjoint from `V`, so it *is* `V ++ M`. This is why the `Z`
    component of the encoding ranges over the layer of size `qN + m`,
    and hence why step 1 of Claim 3.4 — *"the number of choices for `Z`
    is `C(N, qN+m) ≤ C(N,qN) q^{-m}`"* — is exactly
    [Counting.binom_ratio] with `q = c/d`. *)

Theorem frag_Z_length :
  forall F S V,
    In S F ->
    length (frag_Z F S V) = length V + length (minimal_fragment F S V).
Proof.
  intros F S V HS; unfold frag_Z, add_set.
  rewrite (setminus_of_disjoint (@fragment_disjoint_V F S V HS)).
  apply app_length.
Qed.

(** *** `S \ M` lives in the link of `M`

    Claim 3.4 step 5: *"Given `M = M(S,V)`, we have `M ⊂ S` and hence
    `S \ M ∈ F_M`."* [Spread.link] is `F_M`, and [Spread.length_link]
    says `|F_M| = deg M F` — which is the quantity a spread hypothesis
    caps. This is where the `k^{-m}` saving of step 4 comes from, and it
    is the only step that uses spreadness at all. *)

Theorem fragment_removed_in_link :
  forall F S V,
    In S F -> In (setminus S (minimal_fragment F S V)) (link (minimal_fragment F S V) F).
Proof.
  intros F S V HS; unfold link.
  apply in_map_iff; exists S; split; [reflexivity|].
  apply filter_In; split; [exact HS|].
  apply containsb_true_iff; apply (@fragment_subset_S F S V HS).
Qed.

(** *** The counting junction

    [Counting.count_inj_le] applied to [phi]. This is the shape Claim
    3.4 consumes: the bad pairs inject into the code space, so counting
    codes bounds counting pairs. Everything above [Distinct F] is
    bookkeeping; [Distinct F] is the hypothesis §1 did not record, and
    §30's write-up says why. *)

Theorem bad_pairs_le_codes :
  forall (F : Family) (L : list (list nat * list nat))
         (p : list nat * list nat -> bool)
         (q : list nat * list nat * list nat * list nat -> bool)
         (Codes : list (list nat * list nat * list nat * list nat)),
    Distinct F ->
    NoDup L ->
    (forall x, In x L -> In (fst x) F) ->
    (forall x, In x L -> p x = true ->
       In (phi F (fst x) (snd x)) Codes /\ q (phi F (fst x) (snd x)) = true) ->
    count p L <= count q Codes.
Proof.
  intros F L p q Codes HD HL Hfst Hmap.
  apply (@count_inj_le _ _ p q (fun x => phi F (fst x) (snd x)) L Codes).
  - exact HL.
  - exact Hmap.
  - intros x y Hx Hy _ _ E.
    apply (@phi_injective_on_pairs F L HD Hfst x y Hx Hy E).
Qed.

(** ** Claim 3.4's count, through the fibred lemma

    The encoding of Claim 3.4 has four components, but the *decode* uses
    only three of them — `ψ` never reads `S'`. That is not an oversight
    in Lovett: `S'` is there for the **count**, not for the decode. It is
    what bounds the number of `M`s — step 3 reads "given `S'`, there
    are at most `C(n,m)` options for `M ⊂ S'`" — and it costs nothing,
    because it is determined by `Z`.

    So for injectivity the encoding is a *pair*: a key `(Z, M)` and a
    remainder `S \ M`, with the remainder ranging over the link of `M`.
    That is exactly the shape [Counting.count_fibred_le] wants. *)

Definition frag_key (F : Family) (p : list nat * list nat)
  : list nat * list nat :=
  (frag_Z F (fst p) (snd p), minimal_fragment F (fst p) (snd p)).

Definition frag_rest (F : Family) (p : list nat * list nat) : list nat :=
  setminus (fst p) (minimal_fragment F (fst p) (snd p)).

(** The pair `(key, rest)` is injective — the same argument as
    [phi_injective], with `S'` dropped because it was never used. *)

Lemma frag_key_rest_injective :
  forall F p1 p2,
    Distinct F -> In (fst p1) F -> In (fst p2) F ->
    frag_key F p1 = frag_key F p2 ->
    frag_rest F p1 = frag_rest F p2 ->
    p1 = p2.
Proof.
  intros F [S1 V1] [S2 V2] HD H1 H2 Hkey Hrest.
  unfold frag_key, frag_rest in *; simpl in *.
  inversion Hkey as [[HZ HM]].
  (* V is recovered literally from (Z, M) *)
  assert (HV : V1 = V2).
  { rewrite <- (@frag_Z_minus_fragment F S1 V1 H1),
            <- (@frag_Z_minus_fragment F S2 V2 H2), HZ, HM; reflexivity. }
  (* S is recovered up to SetEq, and Distinct closes the gap *)
  assert (HS : S1 = S2).
  { apply (@SetNoDup_setEq_eq F); [exact HD | exact H1 | exact H2 |].
    apply (SetEq_trans
             (SetEq_sym (add_set_setminus_SetEq (@fragment_subset_S F S1 V1 H1)))).
    rewrite Hrest, HM.
    apply (add_set_setminus_SetEq (@fragment_subset_S F S2 V2 H2)). }
  rewrite HS, HV; reflexivity.
Qed.

(** **The fibred bound.** Any list of pairs whose keys land in [Base]
    and whose first components lie in a [Distinct] family is bounded by
    `|Base| * K`, where `K` caps the link of every key's fragment.

    [Base] is left abstract on purpose: bounding *it* by
    `C(N, j+m) * C(n, m)` is the remaining step, and §31.5a says exactly
    what stands in the way. *)

Theorem bad_pairs_fibred_bound :
  forall (F : Family) (L : list (list nat * list nat))
         (Base : list (list nat * list nat)) (K : nat),
    Distinct F -> NoDup L ->
    (forall p, In p L -> In (fst p) F) ->
    (forall p, In p L -> In (frag_key F p) Base) ->
    (forall q, In q Base -> length (link (snd q) F) <= K) ->
    length L <= length Base * K.
Proof.
  intros F L Base K HD HL Hfst Hkey Hfib.
  apply (@count_fibred_le _ _ _ (frag_key F) (frag_rest F) L Base
                          (fun q => link (snd q) F) K).
  - exact HL.
  - exact Hkey.
  - intros p Hp; unfold frag_key, frag_rest; simpl.
    apply (@fragment_removed_in_link F (fst p) (snd p) (Hfst p Hp)).
  - intros p1 p2 Hp1 Hp2 Ek Er.
    apply (@frag_key_rest_injective F p1 p2 HD (Hfst p1 Hp1) (Hfst p2 Hp2) Ek Er).
  - exact Hfib.
Qed.

(** *** Where spreadness enters, and it is the only place

    [Spread.Spread F k] is `k^|T| * deg T F <= |F|`, and
    [Spread.length_link] is `|link T F| = deg T F`. So a fragment of size
    [m] has its link capped by `|F| / k^m` — step 4 of Claim 3.4, which
    Lovett annotates "here is where we are using the assumption that `F`
    is `k`-spread!". *)

Lemma spread_caps_the_link :
  forall F k M,
    Spread F k -> NoDup M ->
    k ^ (length M) * length (link M F) <= length F.
Proof.
  intros F k M Hsp HM; rewrite length_link; apply Hsp; exact HM.
Qed.

(** **The per-`m` bound, cleared of denominators.** *)

Theorem bad_pairs_spread_bound :
  forall (F : Family) (L : list (list nat * list nat))
         (Base : list (list nat * list nat)) (K m k : nat),
    Distinct F -> NoDup L ->
    (forall p, In p L -> In (fst p) F) ->
    (forall p, In p L -> In (frag_key F p) Base) ->
    (forall q, In q Base -> length (link (snd q) F) <= K) ->
    k ^ m * K <= length F ->
    k ^ m * length L <= length Base * length F.
Proof.
  intros F L Base K m k HD HL Hfst Hkey Hfib Hspread.
  pose proof (@bad_pairs_fibred_bound F L Base K HD HL Hfst Hkey Hfib) as Hb.
  assert (H1 : k ^ m * length L <= k ^ m * (length Base * K))
    by (apply Nat.mul_le_mono_l; exact Hb).
  assert (H2 : k ^ m * (length Base * K) = length Base * (k ^ m * K)) by ring.
  assert (H3 : length Base * (k ^ m * K) <= length Base * length F)
    by (apply Nat.mul_le_mono_l; exact Hspread).
  lia.
Qed.
