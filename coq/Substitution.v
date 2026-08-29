(** * Substitution preserves maximality

    **This is the formalisation of a result the repository already had.**
    `docs/roadmap.md` §13.1 states it, measures it three independent ways
    (`rust/examples/extend_ahs.rs`, `rust/tests/extension.rs`), gives the
    mechanism — *"the covering number is multiplicative … so maximality
    is multiplicative under substitution, and since [iota(2)] and
    [iota(3)] are both maximal the whole 3-adic tower is"* — and names
    exactly what was missing:

    <<
      Formalised: Maximal.iota4_is_maximal_intersecting at b = 4, through
      the general reduction, reflectively, with no ground set. The
      general statement needs `substitute` in Coq, which is §5 item 2's
      session.
    >>

    This file is that session. Nothing here is a new fact about
    sunflowers; what is new is that the general statement is a theorem
    rather than prose plus a measurement, and that [b = 6] and [b = 9]
    now hold in the kernel rather than in a search.

    ** The statement

    [Maximal.MaximalIntersecting b F] says nothing whatsoever can be
    added to [F] — for *every* list, on every ground set, using only the
    intersecting condition. [substitution_is_maximal] says that if both
    seeds are maximal **and** have covering number equal to their
    uniformity, so is the substituted family.

    ** Why the certificate route stops at [b = 4]

    [Maximal.iota4_is_maximal_intersecting] settles [b = 4] by
    [maximal_of_trace_certificate], which enumerates the [2^9] sublists of
    the ground set. At [b = 9] the ground set has 36 points, the same
    certificate is [2^36] sublists, and [vm_compute] does not reach it.
    `rust/tests/extension.rs` gets there by enumerating *minimal* hitting
    sets under a budget — sound because any hitting set of size at most
    [b] contains a minimal one — in about a hundred seconds. This proves
    the same thing at every level of the tower at once, in a second.

    ** Where [b = 9] sits

    [Sharp.iota_nine_at_least_10001_refutes]: at [b = 9] the sharp
    conjecture reads [iota(9) <= 10000], and the substitution family has
    exactly ten thousand members — the bound has **no margin at all**
    there, against five at [b = 4] and seventeen at [b = 6]. That is
    `STATUS.md`'s `the_tower_misses_by_exactly_one` row, and it is why
    the extension question at [b = 9] was worth settling.

    ** What it does not say

    §13.2 already says it and it is repeated here because the two are
    easy to conflate: **maximal is not maximum.**
    [Maximal.maximality_is_not_a_size_bound] is the witness — the Fano
    plane is maximal with seven members. This closes one route to a
    record and is *not* evidence for [Sharp.AHSOptimal]. *)

From Coq Require Import List Arith Lia.
Import ListNotations.

From Sunflower Require Import Sets Sunflower Spread HallCore LowerBound
                             Reflect Intersecting IotaRate SliceRank Counting
                             Product Sharp Maximal.

Set Implicit Arguments.

(** ** The construction, as the proof needs it

    A point of the substituted family is [v * w + u]: block [v], inner
    point [u], with [w] the inner ground size. [place] moves an inner
    member into a block; [assemble] takes an outer member and a choice of
    inner member per block and glues. The choice is a *function*, which
    is what removes every list-length side condition from the argument
    below. *)

Definition place (w v : nat) (M : list nat) : list nat :=
  map (fun u => v * w + u) M.

Definition assemble (w : nat) (T : list nat) (f : nat -> list nat) : list nat :=
  concat (map (fun v => place w v (f v)) T).

(** [slice] is what a candidate set has inside one block; [trace] is the
    same thing read as an inner set. *)

Definition slice (w v : nat) (A : list nat) : list nat :=
  filter (fun x => andb (Nat.leb (v * w) x) (Nat.ltb x (v * w + w))) A.

Definition trace (w v : nat) (A : list nat) : list nat :=
  map (fun x => x - v * w) (slice w v A).

Definition Covers (T : list nat) (F : Family) : Prop :=
  forall B, In B F -> exists x, In x T /\ In x B.

(** ** Elementary facts about the three operations *)

Lemma in_place_iff :
  forall w v M x, In x (place w v M) <-> exists u, In u M /\ x = v * w + u.
Proof.
  intros w v M x; unfold place; split.
  - intro H; apply in_map_iff in H as [u [E Hu]]; exists u; split;
      [exact Hu | symmetry; exact E].
  - intros [u [Hu E]]; apply in_map_iff; exists u; split;
      [symmetry; exact E | exact Hu].
Qed.

Lemma in_slice_iff :
  forall w v A x,
    In x (slice w v A) <-> In x A /\ v * w <= x /\ x < v * w + w.
Proof.
  intros w v A x; unfold slice; rewrite filter_In; split.
  - intros [H1 H2]; apply Bool.andb_true_iff in H2 as [H3 H4].
    split; [exact H1|]; split;
      [apply Nat.leb_le; exact H3 | apply Nat.ltb_lt; exact H4].
  - intros [H1 [H2 H3]]; split; [exact H1|].
    apply Bool.andb_true_iff; split;
      [apply Nat.leb_le; exact H2 | apply Nat.ltb_lt; exact H3].
Qed.

Lemma slice_incl : forall w v A, incl (slice w v A) A.
Proof. intros w v A x H; apply in_slice_iff in H; tauto. Qed.

Lemma slice_NoDup : forall w v A, NoDup A -> NoDup (slice w v A).
Proof. intros; unfold slice; apply NoDup_filter; assumption. Qed.

Lemma slice_is_placed_trace :
  forall w v A, slice w v A = place w v (trace w v A).
Proof.
  intros w v A; unfold place, trace; rewrite map_map.
  rewrite <- (map_id (slice w v A)) at 1.
  apply map_ext_in; intros x Hx.
  apply in_slice_iff in Hx as [_ [Hlo _]]; lia.
Qed.

Lemma in_trace_iff :
  forall w v A u,
    In u (trace w v A) <-> In (v * w + u) A /\ u < w.
Proof.
  intros w v A u; unfold trace; split.
  - intro H; apply in_map_iff in H as [x [E Hx]].
    apply in_slice_iff in Hx as [HxA [Hlo Hhi]]; subst u.
    replace (v * w + (x - v * w)) with x by lia; split; [exact HxA | lia].
  - intros [Hin Hlt]; apply in_map_iff; exists (v * w + u); split; [lia|].
    apply in_slice_iff; split; [exact Hin | lia].
Qed.

Lemma trace_length : forall w v A, length (trace w v A) = length (slice w v A).
Proof. intros; unfold trace; apply map_length. Qed.

Lemma trace_NoDup : forall w v A, NoDup A -> NoDup (trace w v A).
Proof.
  intros w v A HA; unfold trace.
  apply (@NoDup_map_inj nat nat (fun x => x - v * w) (slice w v A)).
  - intros x y Hx Hy E.
    apply in_slice_iff in Hx as [_ [Hx _]]; apply in_slice_iff in Hy as [_ [Hy _]].
    lia.
  - apply slice_NoDup; exact HA.
Qed.

Lemma length_pos_in : forall (l : list nat), 0 < length l -> exists x, In x l.
Proof. intros [|x l] H; simpl in H; [lia | exists x; left; reflexivity]. Qed.

Lemma in_concat_map :
  forall (g : nat -> list nat) (L : list nat) x,
    In x (concat (map g L)) <-> exists v, In v L /\ In x (g v).
Proof.
  intros g L x; split.
  - intro H; apply in_concat in H as [l [Hl Hx]].
    apply in_map_iff in Hl as [v [E Hv]]; subst l; exists v; split; assumption.
  - intros [v [Hv Hx]]; apply in_concat; exists (g v); split;
      [apply in_map_iff; exists v; split; [reflexivity | exact Hv] | exact Hx].
Qed.

(** ** The block decomposition of a candidate set

    The slices of a [NoDup] list over distinct blocks are pairwise
    disjoint, so their concatenation is [NoDup] and sits inside the list.
    That is the whole of the counting step. *)

Lemma NoDup_concat_slices :
  forall w A C,
    1 <= w -> NoDup A -> NoDup C ->
    NoDup (concat (map (fun v => slice w v A) C)).
Proof.
  intros w A C Hw HA; induction C as [|v C IH]; intros HC; simpl; [constructor|].
  inversion HC as [|? ? Hnv HC']; subst.
  apply NoDup_app_disjoint.
  - apply slice_NoDup; exact HA.
  - apply IH; exact HC'.
  - intros x Hx Hy.
    apply in_slice_iff in Hx as [_ [Hlo Hhi]].
    apply in_concat_map in Hy as [v' [Hv' Hx']].
    apply in_slice_iff in Hx' as [_ [Hlo' Hhi']].
    assert (v <> v') by (intro E; subst v'; contradiction).
    nia.
Qed.

Lemma concat_slices_incl :
  forall w A C, incl (concat (map (fun v => slice w v A) C)) A.
Proof.
  intros w A C x H; apply in_concat_map in H as [v [_ Hx]].
  apply (slice_incl w v A); exact Hx.
Qed.

Lemma concat_length_ge :
  forall (C : list nat) (g : nat -> list nat) (c : nat),
    (forall v, In v C -> c <= length (g v)) ->
    length C * c <= length (concat (map g C)).
Proof.
  induction C as [|v C IH]; intros g c H; simpl; [lia|].
  rewrite app_length.
  assert (H1 : c <= length (g v)) by (apply H; left; reflexivity).
  assert (H2 : length C * c <= length (concat (map g C)))
    by (apply IH; intros u Hu; apply H; right; exact Hu).
  lia.
Qed.

Lemma concat_length_tight :
  forall (C : list nat) (g : nat -> list nat) (c : nat),
    (forall v, In v C -> c <= length (g v)) ->
    length (concat (map g C)) <= length C * c ->
    forall v, In v C -> length (g v) = c.
Proof.
  induction C as [|v C IH]; intros g c Hge Hle u Hu; simpl in *; [destruct Hu|].
  rewrite app_length in Hle.
  assert (H1 : c <= length (g v)) by (apply Hge; left; reflexivity).
  assert (H2 : length C * c <= length (concat (map g C)))
    by (apply concat_length_ge; intros z Hz; apply Hge; right; exact Hz).
  destruct Hu as [E | Hu].
  - subst u; lia.
  - apply (IH g c); [intros z Hz; apply Hge; right; exact Hz | lia | exact Hu].
Qed.

(** ** The two seed hypotheses, and the boolean cover test

    [Maximal.blocksb] is "meets every member"; the two directions of its
    correctness are what turn the case analysis below into a choice of
    witness. *)

Lemma blocksb_true_iff :
  forall T F, blocksb T F = true <-> Covers T F.
Proof.
  intros T F; unfold blocksb, Covers; split.
  - intros H B HB.
    pose proof (proj1 (forallb_forall _ _) H B HB) as Hex.
    apply existsb_exists in Hex as [x [Hx Hm]].
    exists x; split; [exact Hx | apply memb_true_iff; exact Hm].
  - intro H; apply forallb_forall; intros B HB.
    destruct (H B HB) as [x [Hx HxB]].
    apply existsb_exists; exists x; split; [exact Hx | apply memb_true_iff; exact HxB].
Qed.

Lemma forallb_false_witness :
  forall {X : Type} (p : X -> bool) (L : list X),
    forallb p L = false -> exists x, In x L /\ p x = false.
Proof.
  intros X p L; induction L as [|x L IH]; simpl; intros H; [discriminate|].
  destruct (p x) eqn:E; simpl in H.
  - destruct (IH H) as [y [Hy Hp]]; exists y; split; [right; exact Hy | exact Hp].
  - exists x; split; [left; reflexivity | exact E].
Qed.

Lemma blocksb_false_witness :
  forall T F, blocksb T F = false -> exists B, In B F /\ Disjoint T B.
Proof.
  intros T F H; unfold blocksb in H.
  destruct (forallb_false_witness _ _ H) as [B [HB Hex]].
  exists B; split; [exact HB|].
  intros x HxT HxB.
  assert (Htrue : existsb (fun y => memb y B) T = true)
    by (apply existsb_exists; exists x; split;
        [exact HxT | apply memb_true_iff; exact HxB]).
  rewrite Htrue in Hex; discriminate.
Qed.

(** ** The theorem

    Both seeds are maximal and have covering number equal to their
    uniformity — for [Product.iota4] the latter is
    [Maximal.iota4_covering_number_is_four], and it is the quantity the
    argument multiplies. [F] need only be *rich*: it contains every
    assembly, up to [SetEq]. Nothing is assumed about what else is in it,
    so the conclusion is about the substitution family and about any
    family containing one. *)

Theorem substitution_is_maximal :
  forall (a c w : nat) (O I F : Family),
    1 <= a -> 1 <= c -> 1 <= w ->
    Uniform a O -> Distinct O -> Intersecting O ->
    (forall T, NoDup T -> Covers T O -> a <= length T) ->
    MaximalIntersecting a O ->
    Uniform c I -> Distinct I -> Intersecting I ->
    (forall U, NoDup U -> Covers U I -> c <= length U) ->
    MaximalIntersecting c I ->
    Grounded I (seq 0 w) ->
    (forall T f, In T O -> (forall v, In v T -> In (f v) I) ->
       exists B, In B F /\ SetEq B (assemble w T f)) ->
    MaximalIntersecting (a * c) F.
Proof.
  intros a c w O I F Ha Hc Hw HUO HDO HIO HtauO HmaxO
         HUI HDI HII HtauI HmaxI HgrI Hrich A HU HD HI.
  (* The shape of the candidate. *)
  assert (HUA : UniformSet (a * c) A)
    by (unfold Uniform in HU; inversion HU as [|X G Hh Ht Heq]; exact Hh).
  destruct HUA as [HAlen HAnd].
  (* [I] is not empty: otherwise any [c]-set extends it. *)
  assert (HIne : I <> []).
  { intro E; subst I.
    apply (HmaxI (seq 0 c)).
    - constructor; [split; [apply seq_length | apply seq_NoDup] | constructor].
    - constructor; [intros B HB; destruct HB | constructor].
    - intros X Y HX HY; destruct HX as [EX | []]; destruct HY as [EY | []];
        subst X Y; intro Hdis.
      apply (Hdis 0); apply in_seq; lia. }
  (* The blocks a point of [A] can lie in. *)
  set (Cand := nodup Nat.eq_dec (map (fun x => x / w) A)).
  set (C := filter (fun v => blocksb (trace w v A) I) Cand).
  assert (HCnd : NoDup C) by (unfold C; apply NoDup_filter, NoDup_nodup).
  assert (HCin : forall v, In v C -> Covers (trace w v A) I).
  { intros v Hv; unfold C in Hv; apply filter_In in Hv as [_ Hb].
    apply blocksb_true_iff; exact Hb. }
  (* A block outside [Cand] has an empty trace. *)
  assert (Hempty : forall v, ~ In v Cand -> trace w v A = []).
  { intros v Hv; unfold trace.
    destruct (slice w v A) as [|x l] eqn:E; [reflexivity | exfalso].
    assert (Hx : In x (slice w v A)) by (rewrite E; left; reflexivity).
    apply in_slice_iff in Hx as [HxA [Hlo Hhi]].
    apply Hv; unfold Cand; apply nodup_In; apply in_map_iff.
    exists x; split; [| exact HxA].
    replace x with (v * w + (x - v * w)) by lia.
    rewrite Nat.div_add_l by lia.
    rewrite (proj2 (Nat.div_small_iff _ _ (Nat.neq_sym _ _ (Nat.lt_neq _ _ Hw))))
      by lia.
    lia. }
  (* ---- Claim 1: [C] meets every member of [O]. ---- *)
  assert (HCcov : Covers C O).
  { intros T HT.
    destruct (existsb (fun v => blocksb (trace w v A) I) T) eqn:Eex.
    - apply existsb_exists in Eex as [v [HvT Hb]].
      exists v; split; [| exact HvT].
      unfold C; apply filter_In; split; [| exact Hb].
      (* [v] has a nonempty trace, so it is a candidate block. *)
      destruct (in_dec Nat.eq_dec v Cand) as [Hin | Hnin]; [exact Hin | exfalso].
      rewrite (Hempty v Hnin) in Hb.
      destruct I as [|M I']; [contradiction | simpl in Hb; discriminate].
    - exfalso.
      (* Every block of [T] misses some inner member; choose one. *)
      set (g := fun v => match find (fun M => disjointb (trace w v A) M) I with
                         | Some M => M
                         | None => hd [] I
                         end).
      assert (Hg : forall v, In v T -> In (g v) I /\ Disjoint (trace w v A) (g v)).
      { intros v HvT.
        assert (Hbf : blocksb (trace w v A) I = false).
        { destruct (blocksb (trace w v A) I) eqn:E; [| reflexivity].
          assert (Htrue : existsb (fun u => blocksb (trace w u A) I) T = true)
            by (apply existsb_exists; exists v; split; [exact HvT | exact E]).
          rewrite Htrue in Eex; discriminate. }
        destruct (blocksb_false_witness _ _ Hbf) as [M [HM Hdis]].
        unfold g; destruct (find (fun N => disjointb (trace w v A) N) I) eqn:Ef.
        - apply find_some in Ef as [Hl Hd]; split;
            [exact Hl | apply disjointb_correct; exact Hd].
        - exfalso.
          pose proof (find_none _ _ Ef M HM) as Hno.
          assert (disjointb (trace w v A) M = true).
          { destruct (disjointb (trace w v A) M) eqn:E2; [reflexivity|].
            apply disjointb_false_iff in E2 as [z [Hz1 Hz2]].
            destruct (Hdis z Hz1 Hz2). }
          congruence. }
      destruct (Hrich T g HT (fun v Hv => proj1 (Hg v Hv))) as [B [HBF Hseq]].
      (* [A] meets [B], and the common point lands in a trace. *)
      assert (Hmeet : exists x, In x A /\ In x B).
      { destruct (disjointb A B) eqn:E.
        - exfalso; apply (HI A B (or_introl eq_refl) (or_intror HBF));
            apply disjointb_correct; exact E.
        - apply disjointb_false_iff; exact E. }
      destruct Hmeet as [x [HxA HxB]].
      destruct Hseq as [Hs1 _]; apply Hs1 in HxB.
      apply in_concat_map in HxB as [v [HvT Hxp]].
      apply in_place_iff in Hxp as [u [Hu Ex]].
      destruct (Hg v HvT) as [HgI Hgd].
      apply (Hgd u); [| exact Hu].
      apply in_trace_iff; split; [rewrite <- Ex; exact HxA|].
      pose proof (HgI) as HgI'.
      pose proof (HgrI (g v) HgI' u Hu) as Hseq2.
      apply in_seq in Hseq2; lia. }
  (* ---- Claims 2-5: the counting. ---- *)
  assert (HCa : a <= length C) by (apply HtauO; assumption).
  assert (Hslice_c : forall v, In v C -> c <= length (slice w v A)).
  { intros v Hv; rewrite <- trace_length; apply HtauI;
      [apply trace_NoDup; exact HAnd | apply HCin; exact Hv]. }
  set (L := concat (map (fun v => slice w v A) C)).
  assert (HLnd : NoDup L) by (unfold L; apply NoDup_concat_slices; assumption).
  assert (HLincl : incl L A) by (unfold L; apply concat_slices_incl).
  assert (HLle : length L <= a * c)
    by (rewrite <- HAlen; apply NoDup_incl_length; assumption).
  assert (HLge : length C * c <= length L)
    by (unfold L; apply concat_length_ge; exact Hslice_c).
  assert (HClen : length C = a) by nia.
  assert (Hexact : forall v, In v C -> length (slice w v A) = c).
  { apply (@concat_length_tight C (fun v => slice w v A) c); [exact Hslice_c|].
    rewrite HClen; exact HLle. }
  assert (HLA : SetEq L A).
  { split; [exact HLincl|].
    apply NoDup_length_incl; [exact HLnd | | exact HLincl].
    rewrite HAlen, <- HClen; exact HLge. }
  (* ---- Claim 6: [C] is a member of [O], and each trace a member of [I]. ---- *)
  assert (HCO : exists T, In T O /\ SetEq C T).
  { destruct (existsb (fun T => seteqb C T) O) eqn:Eex.
    - apply existsb_exists in Eex as [T [HT Hb]]; exists T; split;
        [exact HT | apply seteqb_correct; exact Hb].
    - exfalso; apply (HmaxO C).
      + constructor; [split; [exact HClen | exact HCnd] | exact HUO].
      + constructor; [| exact HDO].
        intros B HB Hseq.
        assert (seteqb C B = true) by (apply seteqb_correct; exact Hseq).
        assert (existsb (fun T => seteqb C T) O = true)
          by (apply existsb_exists; exists B; split; assumption).
        congruence.
      + intros X Y HX HY.
        destruct HX as [EX | HX]; destruct HY as [EY | HY]; subst.
        * intro Hdis.
          destruct (@length_pos_in C ltac:(lia)) as [z Hz].
          exact (Hdis z Hz Hz).
        * intro Hdis; destruct (HCcov Y HY) as [z [Hz1 Hz2]]; apply (Hdis z); assumption.
        * intro Hdis; destruct (HCcov X HX) as [z [Hz1 Hz2]]; apply (Hdis z); assumption.
        * exact (HIO X Y HX HY). }
  destruct HCO as [T [HTO HCT]].
  set (h := fun v => match find (fun M => seteqb (trace w v A) M) I with
                     | Some M => M
                     | None => hd [] I
                     end).
  assert (Hh : forall v, In v C -> In (h v) I /\ SetEq (trace w v A) (h v)).
  { intros v Hv.
    assert (Hmem : exists M, In M I /\ SetEq (trace w v A) M).
    { destruct (existsb (fun M => seteqb (trace w v A) M) I) eqn:Eex.
      - apply existsb_exists in Eex as [M [HM Hb]]; exists M; split;
          [exact HM | apply seteqb_correct; exact Hb].
      - exfalso; apply (HmaxI (trace w v A)).
        + constructor; [split; [rewrite trace_length; apply Hexact; exact Hv
                               | apply trace_NoDup; exact HAnd] | exact HUI].
        + constructor; [| exact HDI].
          intros B HB Hseq.
          assert (seteqb (trace w v A) B = true) by (apply seteqb_correct; exact Hseq).
          assert (existsb (fun M => seteqb (trace w v A) M) I = true)
            by (apply existsb_exists; exists B; split; assumption).
          congruence.
        + intros X Y HX HY.
          destruct HX as [EX | HX]; destruct HY as [EY | HY]; subst.
          * intro Hdis.
            assert (Hlen : length (trace w v A) = c)
              by (rewrite trace_length; apply Hexact; exact Hv).
            destruct (@length_pos_in (trace w v A) ltac:(lia)) as [z Hz].
            exact (Hdis z Hz Hz).
          * intro Hdis; destruct (HCin v Hv Y HY) as [z [Hz1 Hz2]];
              apply (Hdis z); assumption.
          * intro Hdis; destruct (HCin v Hv X HX) as [z [Hz1 Hz2]];
              apply (Hdis z); assumption.
          * exact (HII X Y HX HY). }
    destruct Hmem as [M [HM Hseq]].
    unfold h; destruct (find (fun N => seteqb (trace w v A) N) I) eqn:Ef.
    - apply find_some in Ef as [Hl Hd]; split;
        [exact Hl | apply seteqb_correct; exact Hd].
    - exfalso.
      pose proof (find_none _ _ Ef M HM) as Hno.
      assert (seteqb (trace w v A) M = true) by (apply seteqb_correct; exact Hseq).
      congruence. }
  (* ---- Claim 7: [A] is the assembly, so it was already there. ---- *)
  assert (HTh : forall v, In v T -> In (h v) I).
  { intros v Hv; apply Hh; destruct HCT as [_ H2]; apply H2; exact Hv. }
  destruct (Hrich T h HTO HTh) as [B [HBF Hseq]].
  assert (HAB : SetEq A B).
  { apply (SetEq_trans (A := A) (B := assemble w T h) (C := B));
      [| apply SetEq_sym; exact Hseq].
    destruct HCT as [HCT1 HCT2].
    split; intros x Hx.
    - destruct HLA as [_ HAL]; apply HAL in Hx.
      unfold L in Hx; apply in_concat_map in Hx as [v [Hv Hxs]].
      unfold assemble; apply in_concat_map; exists v; split; [apply HCT1; exact Hv|].
      rewrite slice_is_placed_trace in Hxs.
      apply in_place_iff in Hxs as [u [Hu Ex]].
      apply in_place_iff; exists u; split; [| exact Ex].
      destruct (Hh v Hv) as [_ [Ht _]]; apply Ht; exact Hu.
    - unfold assemble in Hx; apply in_concat_map in Hx as [v [Hv Hxp]].
      assert (HvC : In v C) by (apply HCT2; exact Hv).
      destruct HLA as [HLA1 _]; apply HLA1.
      unfold L; apply in_concat_map; exists v; split; [exact HvC|].
      rewrite slice_is_placed_trace.
      apply in_place_iff in Hxp as [u [Hu Ex]].
      apply in_place_iff; exists u; split; [| exact Ex].
      destruct (Hh v HvC) as [_ [_ Ht]]; apply Ht; exact Hu. }
  inversion HD as [|X G Hni Ht Heq]; subst.
  exact (Hni B HBF HAB).
Qed.

(** ** The construction itself

    [assemble_all] enumerates every choice of inner member per block of a
    single outer member; [substitute] runs it over the outer family. The
    only property needed downstream is that every assembly is in it —
    the *richness* hypothesis of the theorem — so nothing is proved here
    about size, uniformity or distinctness. *)

Fixpoint assemble_all (w : nat) (I : Family) (T : list nat) : Family :=
  match T with
  | [] => [[]]
  | v :: T' =>
      flat_map (fun M => map (fun rest => place w v M ++ rest) (assemble_all w I T')) I
  end.

Definition substitute (w : nat) (O I : Family) : Family :=
  flat_map (assemble_all w I) O.

Lemma in_assemble_all :
  forall w I T f,
    (forall v, In v T -> In (f v) I) ->
    In (assemble w T f) (assemble_all w I T).
Proof.
  intros w I T; induction T as [|v T IH]; intros f Hf; simpl.
  - left; reflexivity.
  - apply in_flat_map; exists (f v); split; [apply Hf; left; reflexivity|].
    apply in_map_iff; exists (assemble w T f); split; [reflexivity|].
    apply IH; intros u Hu; apply Hf; right; exact Hu.
Qed.

Lemma in_substitute :
  forall w O I T f,
    In T O -> (forall v, In v T -> In (f v) I) ->
    In (assemble w T f) (substitute w O I).
Proof.
  intros w O I T f HT Hf; unfold substitute; apply in_flat_map.
  exists T; split; [exact HT | apply in_assemble_all; exact Hf].
Qed.

Lemma substitute_is_rich :
  forall w O I T f,
    In T O -> (forall v, In v T -> In (f v) I) ->
    exists B, In B (substitute w O I) /\ SetEq B (assemble w T f).
Proof.
  intros w O I T f HT Hf; exists (assemble w T f); split;
    [apply in_substitute; assumption | apply SetEq_refl].
Qed.

(** ** Discharging the covering-number hypothesis from a finite check

    [substitution_is_maximal] wants "every [NoDup] cover has at least [b]
    points", quantified over *all* lists. A cover may be intersected with
    the ground set without ceasing to cover, so the sublists of the
    ground set decide it — the same reduction
    [Maximal.maximal_of_trace_certificate] makes, and the same [2^|U|]
    enumeration. *)

Definition tau_certificate (b : nat) (F : Family) (U : list nat) : bool :=
  forallb (fun T => implb (blocksb T F) (Nat.leb b (length T))) (sublists U).

Theorem tau_of_certificate :
  forall b F U,
    NoDup U -> Grounded F U ->
    tau_certificate b F U = true ->
    forall T, NoDup T -> Covers T F -> b <= length T.
Proof.
  intros b F U HndU Hgr Hcert T HndT Hcov.
  set (T' := filter (fun x => memb x T) U).
  assert (HT'sub : In T' (sublists U)) by apply filter_in_sublists.
  assert (HT'nd : NoDup T')
    by (eapply sublists_NoDup_members; [exact HndU | exact HT'sub]).
  assert (HT'T : Subset T' T).
  { intros x Hx; unfold T' in Hx; apply filter_In in Hx as [_ Hm].
    apply memb_true_iff; exact Hm. }
  assert (Hblk : blocksb T' F = true).
  { apply blocksb_true_iff; intros B HB.
    destruct (Hcov B HB) as [x [HxT HxB]].
    exists x; split; [| exact HxB].
    unfold T'; apply filter_In; split;
      [exact (Hgr B HB x HxB) | apply memb_true_iff; exact HxT]. }
  pose proof (proj1 (forallb_forall _ _) Hcert T' HT'sub) as Hcheck.
  cbv beta in Hcheck; rewrite Hblk in Hcheck; simpl in Hcheck.
  apply Nat.leb_le in Hcheck.
  pose proof (NoDup_incl_length HT'nd HT'T) as Hle; lia.
Qed.

(** ** The two seeds

    [Intersecting.iota3] is [iota(3) = 10] on six points; the triangle is
    [iota(2) = 3]. Every hypothesis the theorem needs is decided here by
    reflection over [2^6] and [2^3] sublists. *)

Definition tri : Family := [[0; 1]; [0; 2]; [1; 2]].

Lemma tri_uniform : Uniform 2 tri.
Proof. apply uniformb_correct; vm_compute; reflexivity. Qed.

Lemma tri_distinct : Distinct tri.
Proof. apply distinctb_correct; vm_compute; reflexivity. Qed.

Lemma tri_intersecting : Intersecting tri.
Proof. apply intersectingb_correct; vm_compute; reflexivity. Qed.

Lemma tri_grounded : Grounded tri (seq 0 3).
Proof.
  unfold Grounded; apply (proj1 (groundedb_correct tri (seq 0 3)));
    vm_compute; reflexivity.
Qed.

Lemma tri_is_maximal : MaximalIntersecting 2 tri.
Proof.
  apply (maximal_of_trace_certificate 2 tri (seq 0 3));
    [exact (seq_NoDup 3 0) | exact tri_grounded | vm_compute; reflexivity].
Qed.

Lemma tri_tau :
  forall T, NoDup T -> Covers T tri -> 2 <= length T.
Proof.
  apply (@tau_of_certificate 2 tri (seq 0 3));
    [exact (seq_NoDup 3 0) | exact tri_grounded | vm_compute; reflexivity].
Qed.

Lemma iota3_grounded : Grounded iota3 (seq 0 6).
Proof.
  unfold Grounded; apply (proj1 (groundedb_correct iota3 (seq 0 6)));
    vm_compute; reflexivity.
Qed.

Lemma iota3_is_maximal : MaximalIntersecting 3 iota3.
Proof.
  apply (maximal_of_trace_certificate 3 iota3 (seq 0 6));
    [exact (seq_NoDup 6 0) | exact iota3_grounded | vm_compute; reflexivity].
Qed.

Lemma iota3_tau :
  forall T, NoDup T -> Covers T iota3 -> 3 <= length T.
Proof.
  apply (@tau_of_certificate 3 iota3 (seq 0 6));
    [exact (seq_NoDup 6 0) | exact iota3_grounded | vm_compute; reflexivity].
Qed.

(** ** The three levels of the tower

    [b = 4] is [Maximal.iota4_is_maximal_intersecting] again, reached
    here without enumerating anything; [b = 6] is the family that gives
    [iota(6) >= 300]; and [b = 9] is the one the conjecture is exactly
    tight on. *)

Corollary triangle_squared_is_maximal :
  MaximalIntersecting 4 (substitute 3 tri tri).
Proof.
  apply (@substitution_is_maximal 2 2 3 tri tri (substitute 3 tri tri));
    try lia; try assumption.
  - exact tri_uniform.
  - exact tri_distinct.
  - exact tri_intersecting.
  - exact tri_tau.
  - exact tri_is_maximal.
  - exact tri_uniform.
  - exact tri_distinct.
  - exact tri_intersecting.
  - exact tri_tau.
  - exact tri_is_maximal.
  - exact tri_grounded.
  - intros T f HT Hf; apply substitute_is_rich; assumption.
Qed.

Corollary iota3_into_triangle_is_maximal :
  MaximalIntersecting 6 (substitute 6 tri iota3).
Proof.
  apply (@substitution_is_maximal 2 3 6 tri iota3 (substitute 6 tri iota3));
    try lia.
  - exact tri_uniform.
  - exact tri_distinct.
  - exact tri_intersecting.
  - exact tri_tau.
  - exact tri_is_maximal.
  - exact iota3_uniform.
  - exact iota3_distinct.
  - exact iota3_intersecting.
  - exact iota3_tau.
  - exact iota3_is_maximal.
  - exact iota3_grounded.
  - intros T f HT Hf; apply substitute_is_rich; assumption.
Qed.

Corollary iota3_squared_is_maximal :
  MaximalIntersecting 9 (substitute 6 iota3 iota3).
Proof.
  apply (@substitution_is_maximal 3 3 6 iota3 iota3 (substitute 6 iota3 iota3));
    try lia.
  - exact iota3_uniform.
  - exact iota3_distinct.
  - exact iota3_intersecting.
  - exact iota3_tau.
  - exact iota3_is_maximal.
  - exact iota3_uniform.
  - exact iota3_distinct.
  - exact iota3_intersecting.
  - exact iota3_tau.
  - exact iota3_is_maximal.
  - exact iota3_grounded.
  - intros T f HT Hf; apply substitute_is_rich; assumption.
Qed.

(** ** Why [b = 9] is the one that matters

    [Sharp.AHSOptimal] is [iota(b)^2 <= 10^(b-1)], and
    [Sharp.iota_nine_at_least_10001_refutes] already records the
    threshold: at [b = 9] a family of **10001** members refutes it. The
    substitution family has exactly ten thousand — the conjecture asserts
    it is optimal with no margin whatsoever — and
    [iota3_squared_is_maximal] says the one extra member is not there to
    be found.

    The arithmetic is not recomputed here. [Sharp]'s own note explains
    why: [10 ^ 8] is a hundred million constructors and [vm_compute]
    cannot reach it, so the threshold is derived symbolically there and
    cited here. `rust/tests/substitution.rs` checks the three margins in
    machine integers, where they are free. *)

Theorem the_nine_uniform_boundary_is_closed_to_extension :
  MaximalIntersecting 9 (substitute 6 iota3 iota3)
  /\ (IotaAtLeast 9 10001 -> ~ AHSOptimal).
Proof.
  split;
    [exact iota3_squared_is_maximal | exact iota_nine_at_least_10001_refutes].
Qed.

(** The margin at [b = 4], where the numbers are small enough to compute:
    27 members against a threshold of 32, so five to spare. Contrast the
    zero at [b = 9]. *)

Example the_margin_at_four_is_five :
  27 * 27 <= 10 ^ (4 - 1) /\ 31 * 31 <= 10 ^ (4 - 1) /\ 10 ^ (4 - 1) < 32 * 32.
Proof. repeat split; vm_compute; lia. Qed.

(** ** What this does not say

    Maximality is a statement about *covers* and bounds nothing.
    [Maximal.maximality_is_not_a_size_bound] makes the point with the
    Fano plane: seven members, maximal, and it contains a sunflower. So
    the theorem above closes the extension route and leaves
    [iota(9) <= 10000] — the conjecture itself — entirely open. Kept
    beside the result so the two are not read as one. *)

Theorem maximality_is_not_an_upper_bound :
  MaximalIntersecting 9 (substitute 6 iota3 iota3)
  /\ MaximalIntersecting 3 fano /\ ContainsKSunflower 3 fano
  /\ length fano = 7.
Proof.
  split; [exact iota3_squared_is_maximal|].
  split; [exact fano_is_maximal_intersecting|].
  split; [exact fano_has_a_sunflower | reflexivity].
Qed.
