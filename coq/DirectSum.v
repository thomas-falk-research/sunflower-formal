(** * DirectSum.v -- The extremal function is supermultiplicative, and the
    first lower bound here that beats the product construction.

    Write [g(n,k) = f(n,k) - 1] for the largest number of [n]-sets with
    no [k]-sunflower. This file proves

    >  g(a + b, k)  >=  g(a, k) * g(b, k),

    as [lower_bound_sum]: a sunflower-free family of [a]-sets and one of
    [b]-sets, placed on disjoint ground sets, combine by unions into a
    sunflower-free family of [(a+b)]-sets of the product size.

    Iterating gives [lower_bound_power], and instantiating *that* at the
    development's own exact value [f(2,3) = 7] gives

    >  f(n, 3)  >=  6^(n/2) + 1  =  2.449...^n,

    against [ProductLowerBound.lower_bound_exponential]'s
    [(k-1)^n + 1 = 2^n + 1]. At every odd [k] the same instantiation at
    [CliqueLowerBound.two_cliques_lower_bound] gives

    >  f(n, k)  >=  (k(k-1))^(n/2) + 1,

    which beats [(k-1)^n + 1] by a factor [(k/(k-1))^(n/2)]
    ([cliques_beat_product]). Both are strict improvements on every
    lower bound previously in this repository, and the improvement
    compounds with [n].

    ** Why this is the right shape

    The combinatorial content is one case analysis. Suppose the union
    family contained a [k]-sunflower [C_1, ..., C_k] with core [Y].
    Split every [C_i] at the ground-set boundary as [A_i ++ B_i]. The
    pairwise intersections split too, so [A_i ∩ A_j] and [B_i ∩ B_j] are
    each constant over pairs. Then either

    * the [A_i] are pairwise distinct as sets, and they are a
      [k]-sunflower in the first family; or
    * two of them coincide, in which case the common value *is* the
      constant [A_i ∩ A_j], so it is contained in every [A_l] — and
      since all of them have size [a], *all* the [A_l] coincide. The
      [C_i] were distinct, so the [B_i] must be pairwise distinct, and
      they are a [k]-sunflower in the second family.

    Uniformity is doing real work in the second bullet: it is what turns
    "contained in" into "equal to". The statement is false without it,
    and the counterexample is two members a side —
    [Audit.uniformity_is_needed_in_the_direct_sum] pins it, and
    [rust/tests/direct_sum.rs] confirms it against an independent
    brute-force detector.

    ** What this is not

    This is the *direct sum*, [g(a+b) >= g(a)g(b)], which is the weakest
    of the classical product constructions. Abbott, Hanson and Sauer
    (JCTA 12 (1972) 381-389) get [f(n,3) >= 10^(n/2 - c log n)], i.e. a
    rate of [10^(1/2) = 3.162...] rather than [6^(1/2) = 2.449...], from
    a *substitution* recursion [g(ab) >= g(a) g(b)^a] — strictly stronger
    than the direct sum, which only gives [g(ab) >= g(b)^a]. See
    [docs/roadmap.md] for that as the next target; nothing in this file
    reaches it.

    ** Relabelling

    [LowerBound] hands back a family on an unspecified ground set, so
    before two of them can be summed one has to be moved out of the
    other's way. [Relabel] below does that for any injection with an
    explicit left inverse; the two used here are [x |-> 2x] and
    [x |-> 2x+1], which are disjoint by parity and need no computation
    of anybody's maximum.

    Depends on [ProductLowerBound] only for its generic list lemmas and
    [contains_sunflower_literal]; none of [prod_family]'s own theory is
    used, so [lower_bound_exponential_via_direct_sum] is a second proof
    of the exponential lower bound sharing only that canonicalisation
    step with the first.

    Zero axioms, zero admits. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower LowerBound ProductLowerBound
     CliqueLowerBound F23.
Import ListNotations.

(** ** Generic list helpers *)

Lemma existsb_false_forall :
  forall (X : Type) (g : X -> bool) (l : list X),
    existsb g l = false -> forall x, In x l -> g x = false.
Proof.
  intros X g l; induction l as [|y l IH]; simpl; intros E x Hx; [contradiction|].
  apply Bool.orb_false_iff in E as [E1 E2].
  destruct Hx as [Ex | Hx]; [subst y; exact E1 | exact (IH E2 x Hx)].
Qed.

Lemma firstn_app_exact :
  forall (A B : list nat), firstn (length A) (A ++ B) = A.
Proof.
  induction A as [|x A IH]; simpl; intros B; [reflexivity|].
  rewrite IH; reflexivity.
Qed.

Lemma skipn_app_exact :
  forall (A B : list nat), skipn (length A) (A ++ B) = B.
Proof.
  induction A as [|x A IH]; simpl; intros B; [reflexivity | apply IH].
Qed.

Lemma app_eq_same_length :
  forall (A1 B1 A2 B2 : list nat),
    length A1 = length A2 -> A1 ++ B1 = A2 ++ B2 -> A1 = A2 /\ B1 = B2.
Proof.
  induction A1 as [|x A1 IH]; intros B1 A2 B2 Hlen E.
  - destruct A2 as [|y A2]; simpl in Hlen;
      [split; [reflexivity | exact E] | discriminate].
  - destruct A2 as [|y A2]; simpl in Hlen; [discriminate|].
    simpl in E. injection E as Ex E.
    assert (Hl : length A1 = length A2) by lia.
    destruct (IH B1 A2 B2 Hl E) as [E1 E2].
    split; [rewrite Ex, E1; reflexivity | exact E2].
Qed.

(** A [NoDup] subset of the same size is the same set. *)

Lemma Subset_eq_length_SetEq :
  forall A B, NoDup A -> Subset A B -> length B <= length A -> SetEq A B.
Proof.
  intros A B Hnd Hsub Hle.
  split; [exact Hsub | exact (NoDup_length_incl Hnd Hle Hsub)].
Qed.

Lemma SetEq_map :
  forall (f : nat -> nat) A B, SetEq A B -> SetEq (map f A) (map f B).
Proof.
  intros f A B [H1 H2]; split; intros y Hy;
    apply in_map_iff in Hy as [x [Ex Hx]]; subst y;
    apply in_map_iff; exists x; split; auto.
Qed.

Lemma Disjoint_mono :
  forall A B A' B', Subset A A' -> Subset B B' -> Disjoint A' B' -> Disjoint A B.
Proof. intros A B A' B' Ha Hb Hd x HxA HxB; apply (Hd x); auto. Qed.

(** [SetNoDup] of an image, from a map that reflects set-equality on the
    source. This is the shape every distinctness obligation below takes:
    the source list is literally [NoDup], and the map is injective enough
    that set-equal images come from equal sources. *)

Lemma SetNoDup_map_reflect :
  forall (f : list nat -> list nat) (S : list (list nat)),
    NoDup S ->
    (forall C D, In C S -> In D S -> C <> D -> ~ SetEq (f C) (f D)) ->
    SetNoDup (map f S).
Proof.
  intros f S Hnd; induction Hnd as [|C S HniC Hnd IH]; simpl; intros Hcol;
    [constructor|].
  constructor.
  - intros B HB Hseq.
    apply in_map_iff in HB as [D [ED HD]]; subst B.
    apply (Hcol C D (or_introl eq_refl) (or_intror HD)); [|exact Hseq].
    intro E; subst D; contradiction.
  - apply IH; intros C0 D0 H1 H2; apply Hcol; right; assumption.
Qed.

Lemma NoDup_flat_map_gen :
  forall (X Y : Type) (f : X -> list Y) (l : list X),
    NoDup l ->
    (forall x, In x l -> NoDup (f x)) ->
    (forall x y c, In x l -> In y l -> x <> y ->
                   In c (f x) -> In c (f y) -> False) ->
    NoDup (flat_map f l).
Proof.
  intros X Y f l Hnd; induction Hnd as [|x l Hni Hnd IH]; simpl;
    intros Hf Hdis; [constructor|].
  apply NoDup_app_intro.
  - apply Hf; left; reflexivity.
  - apply IH.
    + intros y Hy; apply Hf; right; exact Hy.
    + intros x0 y0 c Hx0 Hy0 Hne Hcx Hcy.
      exact (Hdis x0 y0 c (or_intror Hx0) (or_intror Hy0) Hne Hcx Hcy).
  - intros c Hcx Hin.
    apply in_flat_map in Hin as [y [Hy Hcy]].
    assert (Hne : x <> y) by (intro E; subst y; contradiction).
    exact (Hdis x y c (or_introl eq_refl) (or_intror Hy) Hne Hcx Hcy).
Qed.

(** Decidable literal equality of sets, used only to make the case split
    in [sum_family_no_sunflower] constructive. *)

Definition eqb_list (A B : list nat) : bool :=
  if list_eq_dec Nat.eq_dec A B then true else false.

Lemma eqb_list_true_iff : forall A B, eqb_list A B = true <-> A = B.
Proof.
  intros A B; unfold eqb_list; destruct (list_eq_dec Nat.eq_dec A B) as [E | NE].
  - split; [intros _; exact E | reflexivity].
  - split; [discriminate | intro H; contradiction].
Qed.

Lemma eqb_list_false_iff : forall A B, eqb_list A B = false <-> A <> B.
Proof.
  intros A B; unfold eqb_list; destruct (list_eq_dec Nat.eq_dec A B) as [E | NE].
  - split; [discriminate | intro H; contradiction].
  - split; [intros _; exact NE | reflexivity].
Qed.

(** ** Relabelling the ground set

    Everything the conjecture is about is invariant under an injective
    renaming of the ground set. [Relabel] proves that for any [g] with an
    explicit left inverse [h]; the left inverse is what lets a sunflower
    in the image be transported back, which is the only direction that
    needs an argument. *)

Section Relabel.

Variable g : nat -> nat.
Variable h : nat -> nat.
Hypothesis Hgh : forall x, h (g x) = x.

Lemma relabel_inj : forall x y, g x = g y -> x = y.
Proof. intros x y E; rewrite <- (Hgh x), <- (Hgh y), E; reflexivity. Qed.

Definition rmap (A : list nat) : list nat := map g A.
Definition rmapF (F : Family) : Family := map rmap F.

Lemma rmap_left_inverse : forall A, map h (rmap A) = A.
Proof.
  intros A; unfold rmap; rewrite map_map.
  rewrite (map_ext (fun x : nat => h (g x)) (fun x : nat => x) Hgh).
  apply map_id.
Qed.

Lemma in_rmap_iff : forall x A, In x (rmap A) <-> exists y, In y A /\ x = g y.
Proof.
  intros x A; unfold rmap; rewrite in_map_iff; split.
  - intros [y [E Hy]]; exists y; split; [exact Hy | symmetry; exact E].
  - intros [y [Hy E]]; exists y; split; [symmetry; exact E | exact Hy].
Qed.

Lemma rmap_SetEq_iff : forall A B, SetEq (rmap A) (rmap B) <-> SetEq A B.
Proof.
  intros A B; split.
  - intros [H1 H2]; split; intros x Hx.
    + assert (Hg : In (g x) (rmap A))
        by (apply in_rmap_iff; exists x; split; [exact Hx | reflexivity]).
      apply H1, in_rmap_iff in Hg as [y [Hy E]].
      rewrite (relabel_inj x y E); exact Hy.
    + assert (Hg : In (g x) (rmap B))
        by (apply in_rmap_iff; exists x; split; [exact Hx | reflexivity]).
      apply H2, in_rmap_iff in Hg as [y [Hy E]].
      rewrite (relabel_inj x y E); exact Hy.
  - apply SetEq_map.
Qed.

Lemma rmap_inter :
  forall A B, SetEq (inter (rmap A) (rmap B)) (rmap (inter A B)).
Proof.
  intros A B; split; intros z Hz.
  - apply in_inter_iff in Hz as [HzA HzB].
    apply in_rmap_iff in HzA as [x [HxA Ex]].
    apply in_rmap_iff in HzB as [y [HyB Ey]].
    assert (Exy : x = y)
      by (apply relabel_inj; rewrite <- Ex, <- Ey; reflexivity).
    subst y.
    apply in_rmap_iff; exists x; split; [apply in_inter_iff; auto | exact Ex].
  - apply in_rmap_iff in Hz as [x [Hx Ex]].
    apply in_inter_iff in Hx as [HxA HxB].
    apply in_inter_iff; split; apply in_rmap_iff; exists x; auto.
Qed.

Lemma rmap_NoDup : forall A, NoDup A -> NoDup (rmap A).
Proof.
  intros A H; unfold rmap; apply NoDup_map_inj_on; [exact H|].
  intros x y _ _ E; exact (relabel_inj x y E).
Qed.

Lemma rmapF_length : forall F, length (rmapF F) = length F.
Proof. intros F; unfold rmapF; apply map_length. Qed.

Lemma rmapF_Uniform : forall n F, Uniform n F -> Uniform n (rmapF F).
Proof.
  intros n F HF; unfold rmapF, Uniform.
  apply Forall_forall; intros A HA.
  apply in_map_iff in HA as [A0 [E HA0]]; subst A.
  unfold Uniform in HF; rewrite Forall_forall in HF.
  destruct (HF A0 HA0) as [Hlen Hnd].
  split; [unfold rmap; rewrite map_length; exact Hlen
         | apply rmap_NoDup; exact Hnd].
Qed.

Lemma rmapF_Distinct : forall F, Distinct F -> Distinct (rmapF F).
Proof.
  intros F HF; unfold rmapF, Distinct.
  apply SetNoDup_map_reflect; [apply SetNoDup_NoDup; exact HF|].
  intros C D HC HD Hne Hseq.
  exact (SetNoDup_pairwise HF HC HD Hne (proj1 (rmap_SetEq_iff C D) Hseq)).
Qed.

(** The transport that matters: a sunflower upstairs is a sunflower
    downstairs. Canonicalising first ([contains_sunflower_literal]) makes
    every member of the witness *literally* [rmap A] for an [A] in the
    family, so [map h] recovers [A] on the nose. *)

Theorem rmapF_no_sunflower :
  forall k F, ~ ContainsKSunflower k F -> ~ ContainsKSunflower k (rmapF F).
Proof.
  intros k F Hno Hcon.
  apply (contains_sunflower_literal k (rmapF F)) in Hcon
    as [S [core [Hincl [Hnd [Hlen Hsun]]]]].
  destruct Hsun as [Hsnd Hcore].
  assert (Hshape : forall C, In C S -> In (map h C) F /\ rmap (map h C) = C).
  { intros C HC.
    specialize (Hincl C HC); unfold rmapF in Hincl.
    apply in_map_iff in Hincl as [A [E HA]]; subst C.
    rewrite rmap_left_inverse; split; [exact HA | reflexivity]. }
  apply Hno.
  apply (@ContainsKSunflower_of_incl k (map (fun C => map h C) S) F
           (map h core)).
  - intros U HU; apply in_map_iff in HU as [C [E HC]]; subst U.
    exact (proj1 (Hshape C HC)).
  - rewrite map_length; exact Hlen.
  - split.
    + apply SetNoDup_map_reflect; [exact Hnd|].
      intros C D HC HD Hne Hseq.
      destruct (Hshape C HC) as [_ EC].
      destruct (Hshape D HD) as [_ ED].
      apply (SetNoDup_pairwise Hsnd HC HD Hne).
      rewrite <- EC, <- ED; apply rmap_SetEq_iff; exact Hseq.
    + intros U V HU HV Hne.
      apply in_map_iff in HU as [C [EU HC]].
      apply in_map_iff in HV as [D [EV HD]].
      subst U V.
      assert (HCD : C <> D) by (intro E; subst D; apply Hne; reflexivity).
      pose proof (Hcore C D HC HD HCD) as Hc.
      destruct (Hshape C HC) as [_ EC].
      destruct (Hshape D HD) as [_ ED].
      assert (H1 : SetEq (inter (rmap (map h C)) (rmap (map h D))) core)
        by (rewrite EC, ED; exact Hc).
      assert (H2 : SetEq (rmap (inter (map h C) (map h D))) core)
        by (eapply SetEq_trans; [apply SetEq_sym; apply rmap_inter | exact H1]).
      pose proof (SetEq_map h _ _ H2) as H3.
      rewrite rmap_left_inverse in H3; exact H3.
Qed.

End Relabel.

(** The one interface used downstream, so the shape of the discharged
    section lemmas is fixed in exactly one place. *)

Theorem relabel_preserves :
  forall (g h : nat -> nat), (forall x, h (g x) = x) ->
  forall n k F,
    Uniform n F -> Distinct F -> ~ ContainsKSunflower k F ->
    Uniform n (rmapF g F) /\ Distinct (rmapF g F)
    /\ length (rmapF g F) = length F
    /\ ~ ContainsKSunflower k (rmapF g F).
Proof.
  intros g h Hgh n k F HU HD Hno.
  split; [apply (rmapF_Uniform g h Hgh); exact HU|].
  split; [apply (rmapF_Distinct g h Hgh); exact HD|].
  split; [apply rmapF_length|].
  apply (rmapF_no_sunflower g h Hgh); exact Hno.
Qed.

(** ** The two relabellings: even and odd points *)

Definition ev (x : nat) : nat := 2 * x.
Definition od (x : nat) : nat := S (2 * x).

Lemma div2_ev : forall x, Nat.div2 (ev x) = x.
Proof. intros x; unfold ev; apply Nat.div2_double. Qed.

Lemma div2_od : forall x, Nat.div2 (od x) = x.
Proof. intros x; unfold od; apply Nat.div2_succ_double. Qed.

Lemma ev_od_disjoint : forall A B, Disjoint (rmap ev A) (rmap od B).
Proof.
  intros A B x HA HB.
  apply in_map_iff in HA as [u [Eu _]].
  apply in_map_iff in HB as [v [Ev _]].
  unfold ev in Eu; unfold od in Ev; lia.
Qed.

(** ** The direct sum of two families on disjoint ground sets *)

Definition CrossDisjoint (F1 F2 : Family) : Prop :=
  forall A B, In A F1 -> In B F2 -> Disjoint A B.

Definition sum_family (F1 F2 : Family) : Family :=
  flat_map (fun A => map (fun B => A ++ B) F2) F1.

Lemma in_sum_family_iff :
  forall F1 F2 C,
    In C (sum_family F1 F2) <->
    exists A B, In A F1 /\ In B F2 /\ C = A ++ B.
Proof.
  intros F1 F2 C; unfold sum_family; rewrite in_flat_map; split.
  - intros [A [HA HC]]; apply in_map_iff in HC as [B [E HB]].
    exists A, B; split; [exact HA | split; [exact HB | symmetry; exact E]].
  - intros [A [B [HA [HB E]]]].
    exists A; split; [exact HA|].
    apply in_map_iff; exists B; split; [symmetry; exact E | exact HB].
Qed.

Lemma sum_family_length :
  forall F1 F2, length (sum_family F1 F2) = length F1 * length F2.
Proof.
  intros F1 F2; unfold sum_family.
  induction F1 as [|A F1 IH]; simpl; [reflexivity|].
  rewrite app_length, map_length, IH; reflexivity.
Qed.

(** Concatenations across a ground-set boundary split, both for
    set-equality and for intersection. These two lemmas are the whole
    reason the ground sets have to be disjoint. *)

Lemma app_SetEq_split :
  forall A1 B1 A2 B2,
    Disjoint A1 B2 -> Disjoint A2 B1 ->
    SetEq (A1 ++ B1) (A2 ++ B2) ->
    SetEq A1 A2 /\ SetEq B1 B2.
Proof.
  intros A1 B1 A2 B2 D1 D2 [H1 H2].
  split; split; intros x Hx.
  - assert (Hin : In x (A2 ++ B2)) by (apply H1, in_or_app; left; exact Hx).
    apply in_app_or in Hin as [H | H]; [exact H | exfalso; apply (D1 x); auto].
  - assert (Hin : In x (A1 ++ B1)) by (apply H2, in_or_app; left; exact Hx).
    apply in_app_or in Hin as [H | H]; [exact H | exfalso; apply (D2 x); auto].
  - assert (Hin : In x (A2 ++ B2)) by (apply H1, in_or_app; right; exact Hx).
    apply in_app_or in Hin as [H | H]; [exfalso; apply (D2 x); auto | exact H].
  - assert (Hin : In x (A1 ++ B1)) by (apply H2, in_or_app; right; exact Hx).
    apply in_app_or in Hin as [H | H]; [exfalso; apply (D1 x); auto | exact H].
Qed.

Lemma app_SetEq_intro :
  forall A1 B1 A2 B2,
    SetEq A1 A2 -> SetEq B1 B2 -> SetEq (A1 ++ B1) (A2 ++ B2).
Proof.
  intros A1 B1 A2 B2 [Ha1 Ha2] [Hb1 Hb2]; split; intros x Hx;
    apply in_app_or in Hx as [H | H]; apply in_or_app; auto.
Qed.

Lemma inter_app_split :
  forall A1 B1 A2 B2,
    Disjoint A1 B2 -> Disjoint A2 B1 ->
    SetEq (inter (A1 ++ B1) (A2 ++ B2)) (inter A1 A2 ++ inter B1 B2).
Proof.
  intros A1 B1 A2 B2 D1 D2; split; intros x Hx.
  - apply in_inter_iff in Hx as [H1 H2].
    apply in_app_or in H1 as [Ha1 | Hb1]; apply in_app_or in H2 as [Ha2 | Hb2].
    + apply in_or_app; left; apply in_inter_iff; auto.
    + exfalso; apply (D1 x); auto.
    + exfalso; apply (D2 x); auto.
    + apply in_or_app; right; apply in_inter_iff; auto.
  - apply in_app_or in Hx as [H | H]; apply in_inter_iff in H as [H1 H2];
      apply in_inter_iff; split; apply in_or_app; auto.
Qed.

(** Uniformity, distinctness and size of the sum. *)

Lemma sum_family_Uniform :
  forall a b F1 F2,
    Uniform a F1 -> Uniform b F2 -> CrossDisjoint F1 F2 ->
    Uniform (a + b) (sum_family F1 F2).
Proof.
  intros a b F1 F2 HU1 HU2 Hcross.
  unfold Uniform; apply Forall_forall; intros C HC.
  apply in_sum_family_iff in HC as [A [B [HA [HB E]]]]; subst C.
  unfold Uniform in HU1, HU2; rewrite Forall_forall in HU1, HU2.
  destruct (HU1 A HA) as [Hla Hnda].
  destruct (HU2 B HB) as [Hlb Hndb].
  split.
  - rewrite app_length, Hla, Hlb; reflexivity.
  - apply NoDup_app_intro; [exact Hnda | exact Hndb|].
    intros x HxA HxB; exact (Hcross A B HA HB x HxA HxB).
Qed.

Lemma sum_family_Distinct :
  forall a b F1 F2,
    Uniform a F1 -> Uniform b F2 ->
    Distinct F1 -> Distinct F2 -> CrossDisjoint F1 F2 ->
    Distinct (sum_family F1 F2).
Proof.
  intros a b F1 F2 HU1 HU2 HD1 HD2 Hcross.
  unfold Distinct; apply NoDup_canonical_SetNoDup.
  - unfold sum_family.
    apply NoDup_flat_map_gen.
    + apply SetNoDup_NoDup; exact HD1.
    + intros A HA.
      apply (@NoDup_map_inj_on (list nat) (list nat)
               (fun B : list nat => A ++ B) F2);
        [apply SetNoDup_NoDup; exact HD2|].
      intros B1 B2 _ _ E; exact (app_inv_head A B1 B2 E).
    + intros A1 A2 C HA1 HA2 Hne HC1 HC2.
      apply in_map_iff in HC1 as [B1 [E1 _]].
      apply in_map_iff in HC2 as [B2 [E2 _]].
      apply Hne.
      assert (Hl : length A1 = length A2).
      { unfold Uniform in HU1; rewrite Forall_forall in HU1.
        destruct (HU1 A1 HA1) as [H1 _]; destruct (HU1 A2 HA2) as [H2 _].
        rewrite H1, H2; reflexivity. }
      assert (E : A1 ++ B1 = A2 ++ B2) by (rewrite E1, E2; reflexivity).
      exact (proj1 (app_eq_same_length A1 B1 A2 B2 Hl E)).
  - intros C D HC HD Hseq.
    apply in_sum_family_iff in HC as [A1 [B1 [HA1 [HB1 EC]]]].
    apply in_sum_family_iff in HD as [A2 [B2 [HA2 [HB2 ED]]]].
    subst C D.
    destruct (app_SetEq_split A1 B1 A2 B2
                (Hcross A1 B2 HA1 HB2) (Hcross A2 B1 HA2 HB1) Hseq)
      as [HeqA HeqB].
    rewrite (SetNoDup_setEq_eq HD1 HA1 HA2 HeqA).
    rewrite (SetNoDup_setEq_eq HD2 HB1 HB2 HeqB).
    reflexivity.
Qed.

(** ** The main combinatorial theorem *)

(** Only the *first* family has to be uniform, and neither has to be
    distinct. The proof splits every member of the sum at position [a],
    which needs the members of [F1] to have that size and asks nothing
    at all about [F2]'s; distinctness of the witness comes from the
    sunflower itself, not from the families.

    The asymmetry is an artefact of splitting from the left, and not a
    fact about the construction: the two sums are the same family of
    sets with the halves swapped, so either side's uniformity is enough
    ([Audit.sum_family_no_sunflower_right], which needs the
    encoding-invariance lemma and so lives there). What is
    false is dropping uniformity from *both*, and
    [Audit.uniformity_is_needed_in_the_direct_sum] is the two-member
    counterexample. The asymmetric form is enumerated against a
    brute-force detector over 4756 pairs with [F2] ranging over families
    of arbitrary subsets in [rust/tests/direct_sum.rs].

    The three hypotheses dropped here were in the statement until the
    mutation runner reported that no proof was sensitive to them. *)

Theorem sum_family_no_sunflower :
  forall a k (F1 F2 : Family),
    2 <= k ->
    Uniform a F1 ->
    ~ ContainsKSunflower k F1 -> ~ ContainsKSunflower k F2 ->
    CrossDisjoint F1 F2 ->
    ~ ContainsKSunflower k (sum_family F1 F2).
Proof.
  intros a k F1 F2 Hk HU1 Hno1 Hno2 Hcross Hcon.
  apply (contains_sunflower_literal k (sum_family F1 F2)) in Hcon
    as [S [core [Hincl [Hnd [Hlen Hsun]]]]].
  destruct Hsun as [Hsnd Hcore].
  (* Every witness member splits at the ground-set boundary. *)
  assert (Hsplit : forall C, In C S ->
            In (firstn a C) F1 /\ In (skipn a C) F2
            /\ firstn a C ++ skipn a C = C).
  { intros C HC.
    specialize (Hincl C HC).
    apply in_sum_family_iff in Hincl as [A [B [HA [HB E]]]].
    assert (HlA : length A = a).
    { unfold Uniform in HU1; rewrite Forall_forall in HU1.
      exact (proj1 (HU1 A HA)). }
    subst C; rewrite <- HlA, firstn_app_exact, skipn_app_exact.
    split; [exact HA | split; [exact HB | reflexivity]]. }
  assert (HuA : forall C, In C S -> length (firstn a C) = a /\ NoDup (firstn a C)).
  { intros C HC.
    destruct (Hsplit C HC) as [HinF _].
    unfold Uniform in HU1; rewrite Forall_forall in HU1.
    exact (HU1 _ HinF). }
  assert (Hdis : forall C D, In C S -> In D S ->
                   Disjoint (firstn a C) (skipn a D)).
  { intros C D HC HD.
    destruct (Hsplit C HC) as [HA _].
    destruct (Hsplit D HD) as [_ [HB _]].
    exact (Hcross _ _ HA HB). }
  (* [k >= 2] gives a reference pair, which names the two half-cores. *)
  assert (Hpair : exists C0 D0, In C0 S /\ In D0 S /\ C0 <> D0).
  { destruct S as [|C0 [|D0 S']]; simpl in Hlen; try lia.
    inversion Hnd as [|x l Hni Hnd']; subst.
    exists C0, D0.
    split; [left; reflexivity|].
    split; [right; left; reflexivity|].
    intro E; subst D0; apply Hni; left; reflexivity. }
  destruct Hpair as [C0 [D0 [HC0 [HD0 Hne0]]]].
  remember (inter (firstn a C0) (firstn a D0)) as coreA eqn:EcoreA.
  remember (inter (skipn a C0) (skipn a D0)) as coreB eqn:EcoreB.
  (* Both halves of the intersection are constant over pairs. *)
  assert (Hcores : forall C D, In C S -> In D S -> C <> D ->
            SetEq (inter (firstn a C) (firstn a D)) coreA /\
            SetEq (inter (skipn a C) (skipn a D)) coreB).
  { intros C D HC HD Hne.
    destruct (Hsplit C HC) as [_ [_ EC]].
    destruct (Hsplit D HD) as [_ [_ ED]].
    destruct (Hsplit C0 HC0) as [_ [_ EC0]].
    destruct (Hsplit D0 HD0) as [_ [_ ED0]].
    pose proof (inter_app_split (firstn a C) (skipn a C) (firstn a D) (skipn a D)
                  (Hdis C D HC HD) (Hdis D C HD HC)) as Hsp.
    rewrite EC, ED in Hsp.
    pose proof (inter_app_split (firstn a C0) (skipn a C0)
                  (firstn a D0) (skipn a D0)
                  (Hdis C0 D0 HC0 HD0) (Hdis D0 C0 HD0 HC0)) as Hsp0.
    rewrite EC0, ED0, <- EcoreA, <- EcoreB in Hsp0.
    (* Both concatenations are set-equal to [core], hence to each other. *)
    assert (Hjoin : SetEq (inter (firstn a C) (firstn a D)
                           ++ inter (skipn a C) (skipn a D))
                          (coreA ++ coreB)).
    { eapply SetEq_trans; [apply SetEq_sym; exact Hsp|].
      eapply SetEq_trans; [exact (Hcore C D HC HD Hne)|].
      apply SetEq_sym.
      eapply SetEq_trans; [apply SetEq_sym; exact Hsp0|].
      exact (Hcore C0 D0 HC0 HD0 Hne0). }
    apply app_SetEq_split; [| | exact Hjoin].
    - apply (Disjoint_mono _ _ (firstn a C) (skipn a D0));
        [ apply inter_Subset_l
        | rewrite EcoreB; apply inter_Subset_r
        | exact (Hdis C D0 HC HD0) ].
    - apply (Disjoint_mono _ _ (firstn a C0) (skipn a C));
        [ rewrite EcoreA; apply inter_Subset_l
        | apply inter_Subset_l
        | exact (Hdis C0 C HC0 HC) ]. }
  (* Do two witness members share their first half, or not? *)
  destruct (existsb (fun C => existsb (fun D =>
              andb (negb (eqb_list C D)) (seteqb (firstn a C) (firstn a D))) S) S)
    eqn:Ecol.
  - (* Yes: then *all* first halves coincide, and the second halves are a
       sunflower in [F2]. *)
    apply existsb_exists in Ecol as [C1 [HC1 E1]].
    apply existsb_exists in E1 as [D1 [HD1' E1]].
    apply Bool.andb_true_iff in E1 as [Ene Eseq].
    apply Bool.negb_true_iff, eqb_list_false_iff in Ene.
    apply seteqb_correct in Eseq.
    assert (HcoreA_eq : SetEq coreA (firstn a C1)).
    { destruct (Hcores C1 D1 HC1 HD1' Ene) as [H _].
      apply SetEq_sym; eapply SetEq_trans; [| exact H].
      split; intros x Hx.
      - apply in_inter_iff; split; [exact Hx | exact (proj1 Eseq x Hx)].
      - apply in_inter_iff in Hx; tauto. }
    assert (Hall : forall E, In E S -> SetEq (firstn a C1) (firstn a E)).
    { intros E HE.
      destruct (list_eq_dec Nat.eq_dec C1 E) as [Eq | Nq];
        [subst E; apply SetEq_refl|].
      destruct (Hcores C1 E HC1 HE Nq) as [H _].
      assert (Hsub : Subset (firstn a C1) (firstn a E)).
      { intros x Hx.
        apply (proj2 HcoreA_eq) in Hx.
        apply (proj2 H) in Hx.
        apply in_inter_iff in Hx; tauto. }
      apply Subset_eq_length_SetEq; [| exact Hsub |].
      - exact (proj2 (HuA C1 HC1)).
      - rewrite (proj1 (HuA C1 HC1)), (proj1 (HuA E HE)); apply Nat.le_refl. }
    assert (HdistB : forall C D, In C S -> In D S -> C <> D ->
                       ~ SetEq (skipn a C) (skipn a D)).
    { intros C D HC HD Hne HseqB.
      apply (SetNoDup_pairwise Hsnd HC HD Hne).
      destruct (Hsplit C HC) as [_ [_ EC]].
      destruct (Hsplit D HD) as [_ [_ ED]].
      rewrite <- EC, <- ED.
      apply app_SetEq_intro; [| exact HseqB].
      eapply SetEq_trans; [apply SetEq_sym; exact (Hall C HC) | exact (Hall D HD)]. }
    apply Hno2.
    apply (@ContainsKSunflower_of_incl k (map (fun C => skipn a C) S) F2 coreB).
    + intros U HU; apply in_map_iff in HU as [C [E HC]]; subst U.
      exact (proj1 (proj2 (Hsplit C HC))).
    + rewrite map_length; exact Hlen.
    + split.
      * apply SetNoDup_map_reflect; [exact Hnd | exact HdistB].
      * intros U V HU HV Hne.
        apply in_map_iff in HU as [C [EU HC]].
        apply in_map_iff in HV as [D [EV HD]].
        subst U V.
        assert (HCD : C <> D) by (intro E; subst D; apply Hne; reflexivity).
        exact (proj2 (Hcores C D HC HD HCD)).
  - (* No: the first halves are already a sunflower in [F1]. *)
    apply Hno1.
    apply (@ContainsKSunflower_of_incl k (map (fun C => firstn a C) S) F1 coreA).
    + intros U HU; apply in_map_iff in HU as [C [E HC]]; subst U.
      exact (proj1 (Hsplit C HC)).
    + rewrite map_length; exact Hlen.
    + split.
      * apply SetNoDup_map_reflect; [exact Hnd|].
        intros C D HC HD Hne Hseq.
        pose proof (existsb_false_forall _ _ _ Ecol C HC) as E1.
        pose proof (existsb_false_forall _ _ _ E1 D HD) as E2.
        apply Bool.andb_false_iff in E2 as [E2 | E2].
        -- apply Bool.negb_false_iff, eqb_list_true_iff in E2; contradiction.
        -- apply seteqb_correct in Hseq; rewrite Hseq in E2; discriminate.
      * intros U V HU HV Hne.
        apply in_map_iff in HU as [C [EU HC]].
        apply in_map_iff in HV as [D [EV HD]].
        subst U V.
        assert (HCD : C <> D) by (intro E; subst D; apply Hne; reflexivity).
        exact (proj1 (Hcores C D HC HD HCD)).
Qed.

(** ** Supermultiplicativity of the extremal function *)

Theorem lower_bound_sum :
  forall a b k p q,
    2 <= k -> LowerBound a k p -> LowerBound b k q -> LowerBound (a + b) k (p * q).
Proof.
  intros a b k p q Hk [F1 [HU1 [HD1 [Hl1 Hn1]]]] [F2 [HU2 [HD2 [Hl2 Hn2]]]].
  destruct (relabel_preserves ev Nat.div2 div2_ev a k F1 HU1 HD1 Hn1)
    as [GU1 [GD1 [GL1 GN1]]].
  destruct (relabel_preserves od Nat.div2 div2_od b k F2 HU2 HD2 Hn2)
    as [GU2 [GD2 [GL2 GN2]]].
  assert (Hcross : CrossDisjoint (rmapF ev F1) (rmapF od F2)).
  { intros A B HA HB.
    unfold rmapF in HA, HB.
    apply in_map_iff in HA as [A0 [EA _]].
    apply in_map_iff in HB as [B0 [EB _]].
    subst A B; apply ev_od_disjoint. }
  exists (sum_family (rmapF ev F1) (rmapF od F2)).
  split; [exact (sum_family_Uniform a b _ _ GU1 GU2 Hcross)|].
  split; [exact (sum_family_Distinct a b _ _ GU1 GU2 GD1 GD2 Hcross)|].
  split.
  (* [nia], not [rewrite ...; reflexivity]: the mutation
     [lowerbound-at-least] turns these length equations into [>=], and a
     proof that rewrites with them is sensitive to the *shape* of
     [LowerBound] rather than to its content. *)
  - rewrite sum_family_length, GL1, GL2; nia.
  - exact (sum_family_no_sunflower a k _ _ Hk GU1 GN1 GN2 Hcross).
Qed.

(** The empty family of the empty set: one [0]-set, no [k]-sunflower for
    [k >= 2]. This is the base of the iteration, and it is what makes
    [lower_bound_power] hold at [t = 0] rather than only [t >= 1]. *)

Lemma lower_bound_zero : forall k, 2 <= k -> LowerBound 0 k 1.
Proof.
  intros k Hk.
  exists [[]].
  split; [|split; [|split]].
  - apply Forall_forall; intros A HA.
    destruct HA as [E | []]; subst A; split; [reflexivity | constructor].
  - constructor; [intros B [] | constructor].
  - simpl; lia.
  - apply no_k_sunflower_short_family; simpl; lia.
Qed.

Theorem lower_bound_power :
  forall a k p t, 2 <= k -> LowerBound a k p -> LowerBound (t * a) k (p ^ t).
Proof.
  intros a k p t Hk HL; induction t as [|t IH]; simpl.
  - apply lower_bound_zero; exact Hk.
  - apply lower_bound_sum; [exact Hk | exact HL | exact IH].
Qed.

(** ** Consequences

    First, a second proof of the exponential lower bound: the product
    family of [ProductLowerBound.v] is the [t]-fold direct sum of the
    trivial [(k-1)]-point family, and none of that file's reasoning about
    [prod_family] is reused here. *)

Corollary lower_bound_exponential_via_direct_sum :
  forall n k, 1 <= n -> 2 <= k -> LowerBound n k ((k - 1) ^ n).
Proof.
  intros n k Hn Hk.
  replace n with (n * 1) at 1 by lia.
  apply lower_bound_power; [lia|].
  apply lower_bound_trivial; lia.
Qed.

(** Second, and the point of the file: pairing up the uniformity and
    feeding the *exact* value [f(2,3) = 7] gives a rate of [6^(1/2)]
    where the product construction gives [2]. *)

Corollary lower_bound_f_n_3 :
  forall t, LowerBound (t * 2) 3 (6 ^ t).
Proof. intros t; apply lower_bound_power; [lia | exact f_2_3_lower]. Qed.

Corollary lower_bound_f_n_3_odd :
  forall t, LowerBound (t * 2 + 1) 3 (6 ^ t * 2).
Proof.
  intros t.
  apply lower_bound_sum; [lia | apply lower_bound_f_n_3 |].
  replace 2 with (3 - 1) by reflexivity.
  apply lower_bound_trivial; lia.
Qed.

(** At every odd [k], the same with two cliques in place of two triangles. *)

Corollary lower_bound_cliques_power :
  forall k t, 3 <= k -> Nat.Odd k -> LowerBound (t * 2) k ((k * (k - 1)) ^ t).
Proof.
  intros k t Hk Hodd.
  apply lower_bound_power; [lia | apply two_cliques_lower_bound; assumption].
Qed.

Corollary lower_bound_cliques_power_odd :
  forall k t, 3 <= k -> Nat.Odd k ->
    LowerBound (t * 2 + 1) k ((k * (k - 1)) ^ t * (k - 1)).
Proof.
  intros k t Hk Hodd.
  apply lower_bound_sum;
    [lia | apply lower_bound_cliques_power; assumption
         | apply lower_bound_trivial; lia].
Qed.

(** ** These bounds are strictly better than the product construction

    The product family gives [(k-1)^n]; at even [n = 2t] the clique sum
    gives [(k(k-1))^t]. The ratio is [(k/(k-1))^t], so the improvement is
    exponential in the uniformity and not a constant factor. *)

Theorem cliques_beat_product :
  forall k t, 3 <= k -> 1 <= t -> (k - 1) ^ (t * 2) < (k * (k - 1)) ^ t.
Proof.
  intros k t Hk Ht.
  rewrite Nat.mul_comm, Nat.pow_mul_r.
  apply Nat.pow_lt_mono_l; [lia|].
  simpl; nia.
Qed.

Corollary six_beats_four : forall t, 1 <= t -> 2 ^ (t * 2) < 6 ^ t.
Proof.
  intros t Ht.
  pose proof (cliques_beat_product 3 t ltac:(lia) Ht) as H.
  simpl in H; exact H.
Qed.
