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

(** ** Closing the count

    §31.9 named the last obstacle: the key's first component `Z = V ++ M`
    is not an *ordered sublist* of the universe, so it is not in
    [Counting.subsets_of_size] and carries no binomial count.
    [Counting.norm] is the fix, built once in the counting layer as rule
    26 asks. Everything below is bookkeeping on top of it. *)

(** [frag_F'] reads [Z] only through membership, so normalising [Z]
    leaves it — and therefore [first_in] — unchanged. *)

Lemma forallb_ext_pointwise :
  forall (f g : nat -> bool) (l : list nat),
    (forall x, f x = g x) -> forallb f l = forallb g l.
Proof.
  intros f g l H; induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite H, IH; reflexivity.
Qed.

Lemma frag_F'_norm :
  forall F U Z, Subset Z U -> frag_F' F (norm U Z) = frag_F' F Z.
Proof.
  intros F U Z Hsub; unfold frag_F'.
  apply filter_ext_eq; intros A; unfold containsb.
  apply forallb_ext_pointwise; intros x; apply (@memb_norm U Z x Hsub).
Qed.

Lemma first_in_norm :
  forall F U Z, Subset Z U -> first_in F (norm U Z) = first_in F Z.
Proof. intros F U Z H; unfold first_in; rewrite (frag_F'_norm F H); reflexivity. Qed.

(** The chosen member is a member. *)

Lemma first_in_in_F :
  forall F S V, In S F -> In (first_in F (frag_Z F S V)) F.
Proof.
  intros F S V HS; unfold first_in.
  destruct (@frag_F'_nonempty F S V HS) as [A HA].
  destruct (frag_F' F (frag_Z F S V)) as [|B L] eqn:E; [inversion HA|].
  simpl. assert (HB : In B (frag_F' F (frag_Z F S V)))
    by (rewrite E; left; reflexivity).
  apply in_frag_F' in HB as [HBF _]; exact HBF.
Qed.

(** Claim 3.3 (2)'s *"in particular `M(S,V) ⊂ S'`"*, at the chosen `S'`. *)

Lemma fragment_subset_first_in :
  forall F S V,
    In S F -> Forall (fun B : list nat => NoDup B) F ->
    Subset (minimal_fragment F S V) (first_in F (frag_Z F S V)).
Proof.
  intros F S V HS Hnd.
  unfold first_in.
  destruct (@frag_F'_nonempty F S V HS) as [A HA].
  destruct (frag_F' F (frag_Z F S V)) as [|B L] eqn:E; [inversion HA|].
  simpl.
  assert (HB : In B (frag_F' F (frag_Z F S V)))
    by (rewrite E; left; reflexivity).
  destruct (@frag_F'_fragment F S V B HS Hnd HB) as [_ H2].
  intros x Hx; apply H2 in Hx; apply in_setminus_iff in Hx as [H _]; exact H.
Qed.

(** [Z] lives in the universe and has no repeats, so [norm] applies. *)

Lemma frag_Z_subset_U :
  forall F S V U,
    In S F -> Subset S U -> Subset V U -> Subset (frag_Z F S V) U.
Proof.
  intros F S V U HS HSU HVU x Hx; unfold frag_Z in Hx.
  apply in_add_set_iff in Hx as [HxV | HxM].
  - apply HVU; exact HxV.
  - apply HSU, (@fragment_subset_S F S V HS); exact HxM.
Qed.

Lemma fragment_NoDup :
  forall F S V,
    In S F -> Forall (fun B : list nat => NoDup B) F ->
    NoDup (minimal_fragment F S V).
Proof.
  intros F S V HS Hnd.
  destruct (proj1 (in_frag_cands F S V _) (@minimal_fragment_in_cands F S V HS))
    as [A [HAF [_ E]]].
  rewrite E; apply setminus_NoDup.
  rewrite Forall_forall in Hnd; apply Hnd; exact HAF.
Qed.

Lemma frag_Z_NoDup :
  forall F S V,
    In S F -> Forall (fun B : list nat => NoDup B) F ->
    NoDup V -> NoDup (frag_Z F S V).
Proof.
  intros F S V HS Hnd HV; unfold frag_Z, add_set.
  rewrite (setminus_of_disjoint (@fragment_disjoint_V F S V HS)).
  apply NoDup_app_disjoint.
  - exact HV.
  - apply (@fragment_NoDup F S V HS Hnd).
  - intros x HxV HxM; apply (@fragment_disjoint_V F S V HS x); assumption.
Qed.

(** *** [link] and [add_set] read their set argument only through
        membership *)

Lemma containsb_SetEq :
  forall T1 T2 A, SetEq T1 T2 -> containsb T1 A = containsb T2 A.
Proof.
  intros T1 T2 A [H1 H2]; destruct (containsb T1 A) eqn:E1.
  - symmetry; apply containsb_true_iff.
    apply containsb_true_iff in E1; intros x Hx; apply E1, H2; exact Hx.
  - destruct (containsb T2 A) eqn:E2; [|reflexivity].
    exfalso; apply containsb_true_iff in E2.
    assert (HT1 : Subset T1 A) by (intros x Hx; apply E2, H1; exact Hx).
    rewrite (proj2 (containsb_true_iff T1 A) HT1) in E1; discriminate.
Qed.

Lemma link_SetEq : forall F T1 T2, SetEq T1 T2 -> link T1 F = link T2 F.
Proof.
  intros F T1 T2 Hseq; unfold link.
  rewrite (filter_ext_eq (containsb T1) (containsb T2) F
             (fun A => containsb_SetEq A Hseq)).
  apply map_ext; intros A; apply setminus_SetEq_r; exact Hseq.
Qed.

Lemma add_set_SetEq_l :
  forall M1 M2 R, SetEq M1 M2 -> SetEq (add_set M1 R) (add_set M2 R).
Proof.
  intros M1 M2 R [H1 H2]; split; intros x Hx;
    apply in_add_set_iff in Hx as [HxM | HxR]; apply in_add_set_iff.
  - left; apply H1; exact HxM.
  - right; exact HxR.
  - left; apply H2; exact HxM.
  - right; exact HxR.
Qed.

(** The chosen member's size is bounded by the family's uniformity, and
    the empty default is harmless. *)

Lemma first_in_length :
  forall F Z n, (forall A, In A F -> length A <= n) -> length (first_in F Z) <= n.
Proof.
  intros F Z n Hn; unfold first_in.
  destruct (frag_F' F Z) as [|B L] eqn:E; simpl; [lia|].
  apply Hn.
  assert (HB : In B (frag_F' F Z)) by (rewrite E; left; reflexivity).
  apply in_frag_F' in HB as [HBF _]; exact HBF.
Qed.

Lemma first_in_NoDup :
  forall F Z, Forall (fun B : list nat => NoDup B) F -> NoDup (first_in F Z).
Proof.
  intros F Z Hnd; unfold first_in.
  destruct (frag_F' F Z) as [|B L] eqn:E; simpl; [constructor|].
  assert (HB : In B (frag_F' F Z)) by (rewrite E; left; reflexivity).
  apply in_frag_F' in HB as [HBF _].
  rewrite Forall_forall in Hnd; apply Hnd; exact HBF.
Qed.

(** *** The canonical key, and the space it lives in *)

Definition frag_ckey (F : Family) (U : list nat) (p : list nat * list nat)
  : list nat * list nat :=
  let Z := norm U (frag_Z F (fst p) (snd p)) in
  (Z, norm (first_in F Z) (minimal_fragment F (fst p) (snd p))).

Definition frag_base (F : Family) (U : list nat) (j m : nat)
  : list (list nat * list nat) :=
  dep_pairs (subsets_of_size (j + m) U)
            (fun Z => subsets_of_size m (first_in F Z)).

(** Steps 1–3 of Claim 3.4's count: the key space has at most
    `C(N, j+m) * C(n, m)` elements. *)

Theorem frag_base_length :
  forall F U j m n,
    (forall A, In A F -> length A <= n) ->
    length (frag_base F U j m) <= binom (length U) (j + m) * binom n m.
Proof.
  intros F U j m n Hn; unfold frag_base.
  eapply Nat.le_trans.
  - apply (@dep_pairs_length_le _ _ (subsets_of_size (j + m) U)
             (fun Z => subsets_of_size m (first_in F Z)) (binom n m)).
    intros Z _; rewrite length_subsets_of_size.
    apply binom_mono_l; apply first_in_length; exact Hn.
  - rewrite length_subsets_of_size; apply Nat.le_refl.
Qed.

(** *** Injectivity survives canonicalisation

    The point of [norm]: `V` is still recovered *literally*, because
    `setminus (norm U Z) M = norm U (setminus Z M) = norm U V = V` — the
    last step by [Counting.norm_idem], since `V` is an ordered sublist of
    `U` by construction. `S` is still recovered only up to [SetEq], and
    [Distinct F] still closes it. *)

Lemma fragment_subset_first_in_norm :
  forall F S V U,
    In S F -> Forall (fun B : list nat => NoDup B) F ->
    Subset (frag_Z F S V) U ->
    Subset (minimal_fragment F S V) (first_in F (norm U (frag_Z F S V))).
Proof.
  intros F S V U HS Hnd HZU.
  rewrite (@first_in_norm F U (frag_Z F S V) HZU).
  apply (@fragment_subset_first_in F S V HS Hnd).
Qed.

Lemma frag_V_recovered :
  forall F S V U,
    In S F -> NoDup U -> In V (subsets U) ->
    setminus (norm U (frag_Z F S V)) (minimal_fragment F S V) = V.
Proof.
  intros F S V U HS HU HV.
  rewrite setminus_norm_l, (@frag_Z_minus_fragment F S V HS).
  apply (@norm_idem U V HU HV).
Qed.

Lemma frag_ckey_rest_injective :
  forall F U p1 p2,
    Distinct F -> NoDup U ->
    Forall (fun B : list nat => NoDup B) F ->
    (forall A, In A F -> Subset A U) ->
    In (fst p1) F -> In (fst p2) F ->
    In (snd p1) (subsets U) -> In (snd p2) (subsets U) ->
    frag_ckey F U p1 = frag_ckey F U p2 ->
    frag_rest F p1 = frag_rest F p2 ->
    p1 = p2.
Proof.
  intros F U [S1 V1] [S2 V2] HD HU Hnd HFU H1 H2 HV1 HV2 Hkey Hrest.
  unfold frag_ckey, frag_rest in *; simpl in *.
  pose proof (f_equal fst Hkey) as HZ; cbn [fst snd] in HZ.
  pose proof (f_equal snd Hkey) as HM; cbn [fst snd] in HM.
  assert (HZ1 : Subset (frag_Z F S1 V1) U)
    by (apply (@frag_Z_subset_U F S1 V1 U H1 (HFU S1 H1));
        intros x Hx; apply (@subsets_incl U V1 HV1); exact Hx).
  assert (HZ2 : Subset (frag_Z F S2 V2) U)
    by (apply (@frag_Z_subset_U F S2 V2 U H2 (HFU S2 H2));
        intros x Hx; apply (@subsets_incl U V2 HV2); exact Hx).
  (* the two fragments are set-equal *)
  assert (HMseq : SetEq (minimal_fragment F S1 V1) (minimal_fragment F S2 V2)).
  { assert (E1 : SetEq (norm (first_in F (norm U (frag_Z F S1 V1)))
                             (minimal_fragment F S1 V1))
                       (minimal_fragment F S1 V1))
      by (apply norm_SetEq;
          apply (@fragment_subset_first_in_norm F S1 V1 U H1 Hnd HZ1)).
    assert (E2 : SetEq (norm (first_in F (norm U (frag_Z F S2 V2)))
                             (minimal_fragment F S2 V2))
                       (minimal_fragment F S2 V2))
      by (apply norm_SetEq;
          apply (@fragment_subset_first_in_norm F S2 V2 U H2 Hnd HZ2)).
    assert (Hchain : SetEq (norm (first_in F (norm U (frag_Z F S1 V1)))
                                 (minimal_fragment F S1 V1))
                           (minimal_fragment F S2 V2))
      by (rewrite HM; exact E2).
    apply (SetEq_trans (SetEq_sym E1) Hchain). }
  (* V is recovered literally *)
  assert (HVeq : V1 = V2).
  { rewrite <- (@frag_V_recovered F S1 V1 U H1 HU HV1),
            <- (@frag_V_recovered F S2 V2 U H2 HU HV2), HZ.
    apply setminus_SetEq_r; exact HMseq. }
  (* S is recovered up to SetEq *)
  assert (HSeq : S1 = S2).
  { apply (@SetNoDup_setEq_eq F); [exact HD | exact H1 | exact H2 |].
    apply (SetEq_trans
             (SetEq_sym (add_set_setminus_SetEq (@fragment_subset_S F S1 V1 H1)))).
    apply (SetEq_trans (A := add_set (minimal_fragment F S1 V1)
                                     (setminus S1 (minimal_fragment F S1 V1)))
                       (B := add_set (minimal_fragment F S2 V2)
                                     (setminus S2 (minimal_fragment F S2 V2)))).
    - rewrite Hrest; apply add_set_SetEq_l; exact HMseq.
    - apply (add_set_setminus_SetEq (@fragment_subset_S F S2 V2 H2)). }
  rewrite HSeq, HVeq; reflexivity.
Qed.

(** ** Claim 3.4, per fragment size

    The four steps of the rendered page, assembled:

    - step 1, the `Z` component, lives in the layer of size `j+m`
      ([frag_Z_length] + [Counting.norm_in_layer]);
    - step 2, `S'` is a function of `Z`, is why the key is a *pair*;
    - step 3, `M ⊂ S'` with `|S'| ≤ n`, gives `C(n,m)`
      ([Counting.binom_mono_l]);
    - step 4, `S \ M ∈ F_M` with `|F_M| ≤ |F| k^{-m}`, is the fibre
      ([fragment_removed_in_link] + [spread_caps_the_link]).

    Nothing leaves [nat]: the `k^{-m}` is cleared to the left. *)

Theorem claim_3_4_per_m :
  forall (F : Family) (U : list nat) (L : list (list nat * list nat))
         (j m k n : nat),
    Distinct F -> NoDup U -> NoDup L ->
    (forall A, In A F -> Subset A U /\ NoDup A /\ length A <= n) ->
    Spread F k ->
    (forall p, In p L -> In (fst p) F) ->
    (forall p, In p L -> In (snd p) (subsets_of_size j U)) ->
    (forall p, In p L -> length (minimal_fragment F (fst p) (snd p)) = m) ->
    k ^ m * length L <= binom (length U) (j + m) * binom n m * length F.
Proof.
  intros F U L j m k n HD HU HL HF Hsp Hfst Hsnd Hm.
  assert (Hnd : Forall (fun B : list nat => NoDup B) F).
  { apply Forall_forall; intros A HA; destruct (HF A HA) as [_ [H _]]; exact H. }
  assert (HFU : forall A, In A F -> Subset A U)
    by (intros A HA; destruct (HF A HA) as [H _]; exact H).
  assert (Hlen : forall A, In A F -> length A <= n)
    by (intros A HA; destruct (HF A HA) as [_ [_ H]]; exact H).
  (* the V of every pair is an ordered sublist of U of length j *)
  assert (HVsub : forall p, In p L -> In (snd p) (subsets U)).
  { intros p Hp; apply (proj1 (in_subsets_of_size j U (snd p)) (Hsnd p Hp)). }
  assert (HVlen : forall p, In p L -> length (snd p) = j).
  { intros p Hp; apply (proj1 (in_subsets_of_size j U (snd p)) (Hsnd p Hp)). }
  (* Z lies in U and has no repeats *)
  assert (HZU : forall p, In p L -> Subset (frag_Z F (fst p) (snd p)) U).
  { intros p Hp; apply (@frag_Z_subset_U F (fst p) (snd p) U (Hfst p Hp)
                          (HFU _ (Hfst p Hp))).
    intros x Hx; apply (@subsets_incl U (snd p) (HVsub p Hp)); exact Hx. }
  (* the fragment is set-equal to its canonical form *)
  assert (HMseq : forall p, In p L ->
            SetEq (norm (first_in F (norm U (frag_Z F (fst p) (snd p))))
                        (minimal_fragment F (fst p) (snd p)))
                  (minimal_fragment F (fst p) (snd p))).
  { intros p Hp; apply norm_SetEq.
    apply (@fragment_subset_first_in_norm F (fst p) (snd p) U
             (Hfst p Hp) Hnd (HZU p Hp)). }
  eapply Nat.le_trans.
  - apply (@count_fibred_weighted_le _ _ _ (frag_ckey F U) (frag_rest F)
             L (frag_base F U j m) (fun q => link (snd q) F) (k ^ m) (length F)).
    + exact HL.
    + (* the key lands in the base *)
      intros p Hp; unfold frag_base; apply in_dep_pairs; split.
      * apply norm_in_layer; [exact HU | | apply (HZU p Hp) |].
        -- apply (@frag_Z_NoDup F (fst p) (snd p) (Hfst p Hp) Hnd).
           apply (@subsets_NoDup U (snd p) HU (HVsub p Hp)).
        -- rewrite (@frag_Z_length F (fst p) (snd p) (Hfst p Hp)),
                   (HVlen p Hp), (Hm p Hp); reflexivity.
      * apply norm_in_layer.
        -- apply first_in_NoDup; exact Hnd.
        -- apply (@fragment_NoDup F (fst p) (snd p) (Hfst p Hp) Hnd).
        -- apply (@fragment_subset_first_in_norm F (fst p) (snd p) U
                    (Hfst p Hp) Hnd (HZU p Hp)).
        -- apply (Hm p Hp).
    + (* the remainder lands in the fibre over the key *)
      intros p Hp; unfold frag_ckey, frag_rest; simpl.
      rewrite (@link_SetEq F _ _ (HMseq p Hp)).
      apply (@fragment_removed_in_link F (fst p) (snd p) (Hfst p Hp)).
    + (* injectivity *)
      intros p q Hp Hq Ek Er.
      apply (@frag_ckey_rest_injective F U p q HD HU Hnd HFU
               (Hfst p Hp) (Hfst q Hq) (HVsub p Hp) (HVsub q Hq) Ek Er).
    + (* the fibre cap, and it is the spread hypothesis *)
      intros q Hq; unfold frag_base in Hq.
      destruct q as [Z Mn]; apply in_dep_pairs in Hq as [_ HMn]; simpl.
      destruct (@subsets_of_size_incl m (first_in F Z) Mn HMn) as [_ Hmlen].
      assert (HMnd : NoDup Mn).
      { apply (@subsets_NoDup (first_in F Z) Mn (@first_in_NoDup F Z Hnd)).
        apply (proj1 (in_subsets_of_size m (first_in F Z) Mn) HMn). }
      pose proof (@spread_caps_the_link F k Mn Hsp HMnd) as H.
      rewrite Hmlen in H; exact H.
  - apply Nat.mul_le_mono_r.
    apply (@frag_base_length F U j m n Hlen).
Qed.

(** ** Claim 3.4, summed — the whole of it

    The rendered page ends:

    >  `Pr[|M(S,V)| ≥ n/2] = |B| / (|F| C(N,qN)) ≤ Σ_{m=n/2}^{n} 2^n
    >  (kq)^{-m} ≤ Σ_{m=n/2}^{n} (4/kq)^m`, and *"Taking `k = cq^{-1}`
    >  for large enough `c`, this is at most `100^{-n}`."*

    With `q = c/d` and denominators cleared throughout, that is the
    theorem below. Reading it back: divide by `(ck)^t` and by
    `C(N,j)·|F|`, and it says the bad pairs are at most
    `2·(4d/ck)^{n/2}` of the sample space — Lovett's `100^{-n}` once `c`
    is large, and §1's *do not chase the constant* applies.

    The hypothesis `n ≤ 2m` on the range is Lovett's `m ≥ n/2`, which is
    what turns `2^n` into `4^m`; `2·(4d) ≤ ck` is `kq ≥ 8`, the ratio the
    geometric sum needs. *)

Lemma two_pow_le_four_pow : forall n m, n <= 2 * m -> 2 ^ n <= 4 ^ m.
Proof.
  intros n m Hle.
  assert (E : 4 ^ m = 2 ^ (2 * m)).
  { rewrite Nat.pow_mul_r; reflexivity. }
  rewrite E; apply Nat.pow_le_mono_r; [lia | exact Hle].
Qed.

Theorem claim_3_4_summed :
  forall (F : Family) (U : list nat) (Lm : nat -> list (list nat * list nat))
         (j k n c d t i : nat),
    Distinct F -> NoDup U ->
    (forall A, In A F -> Subset A U /\ NoDup A /\ length A <= n) ->
    Spread F k ->
    (forall m, NoDup (Lm m)) ->
    (forall m p, In p (Lm m) -> In (fst p) F) ->
    (forall m p, In p (Lm m) -> In (snd p) (subsets_of_size j U)) ->
    (forall m p, In p (Lm m) ->
                 length (minimal_fragment F (fst p) (snd p)) = m) ->
    c * length U <= d * S j ->
    2 * (4 * d) <= c * k ->
    1 <= c * k ->
    (forall m, t <= m -> m <= t + i -> n <= 2 * m) ->
    (c * k) ^ t * sum_from (fun m => length (Lm m)) t i
    <= 2 * (4 * d) ^ t * (binom (length U) j * length F).
Proof.
  intros F U Lm j k n c d t i HD HU HF Hsp HLnd Hfst Hsnd Hm Hcd Hratio Hb1 Hrange.
  apply (@geom_assemble (fun m => length (Lm m)) (4 * d) (c * k)
                        (binom (length U) j * length F) Hratio Hb1 i t).
  intros m Ht1 Ht2.
  (* step: the per-m count, then the binomial estimate, then 2^n <= 4^m *)
  pose proof (@claim_3_4_per_m F U (Lm m) j m k n HD HU (HLnd m) HF Hsp
                (Hfst m) (Hsnd m) (Hm m)) as Hper.
  assert (Epow : (c * k) ^ m = c ^ m * k ^ m) by (apply Nat.pow_mul_l).
  assert (H1 : (c * k) ^ m * length (Lm m)
               <= c ^ m * (binom (length U) (j + m) * binom n m * length F)).
  { rewrite Epow.
    assert (E : c ^ m * k ^ m * length (Lm m)
                = c ^ m * (k ^ m * length (Lm m))) by ring.
    rewrite E; apply Nat.mul_le_mono_l; exact Hper. }
  assert (H2 : c ^ m * binom (length U) (j + m)
               <= d ^ m * binom (length U) j)
    by (apply binom_ratio; exact Hcd).
  assert (H3 : binom n m <= 4 ^ m).
  { eapply Nat.le_trans; [apply binom_le_two_pow|].
    apply two_pow_le_four_pow; apply Hrange; assumption. }
  assert (E4 : (4 * d) ^ m = 4 ^ m * d ^ m) by (apply Nat.pow_mul_l).
  rewrite E4.
  (* c^m * C(N,j+m) * C(n,m) * |F| <= d^m C(N,j) * 4^m * |F| *)
  assert (H4 : c ^ m * (binom (length U) (j + m) * binom n m * length F)
               <= (d ^ m * binom (length U) j) * (4 ^ m * length F)).
  { assert (E : c ^ m * (binom (length U) (j + m) * binom n m * length F)
                = (c ^ m * binom (length U) (j + m)) * (binom n m * length F))
      by ring.
    rewrite E.
    apply Nat.mul_le_mono; [exact H2 | apply Nat.mul_le_mono_r; exact H3]. }
  assert (E5 : d ^ m * binom (length U) j * (4 ^ m * length F)
               = 4 ^ m * d ^ m * (binom (length U) j * length F)) by ring.
  lia.
Qed.
