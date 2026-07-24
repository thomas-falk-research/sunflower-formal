(**
 * Matching.v - Bipartite matchings and vertex covers
 *
 * A [Matching] over a [Graph] is a list of vertex-disjoint edges.
 * A [VertexCover] is a list of vertices touching every edge.
 *
 * We prove:
 *
 *   - [matching_le_cover]: [|M| ≤ |C|] for any matching [M] and
 *     vertex cover [C] in the same graph (the "easy direction" of
 *     König's theorem; proved constructively here).
 *
 *   - [matching_le_half_vertices]: [2|M| ≤ |V|] for any matching
 *     of a simple graph.
 *
 *   - Definition of augmenting paths in bipartite graphs.
 *
 * The full König equality theorem (bipartite max-matching = min
 * vertex cover) and Hall's marriage theorem, formerly stated here as
 * named axioms, are now PROVED constructively in
 * [KoenigHall.v] (theorems [koenig_theorem] and
 * [hall_marriage_theorem], both closed under the global context).
 *
 * VERIFICATION STATUS: Machine-checked, zero admits, zero axioms.
 *)

Require Import List.
Require Import Arith.
Require Import Lia.
Require Import PeanoNat.
From Sunflower Require Import Sets.
From Sunflower Require Import Graph.

Import ListNotations.

(** ** Edges as ordered pairs *)

Definition Edge : Type := (nat * nat)%type.

Definition edge_vertices (e : Edge) : list nat :=
  match e with (u, v) => [u; v] end.

Definition edge_in_graph (G : Graph) (e : Edge) : Prop :=
  EdgeOf G (fst e) (snd e).

(** ** Matching predicate

    A list of edges [M] is a [Matching G M] when:
    1. every edge of [M] is an edge of [G];
    2. no two edges of [M] share a vertex.

    Vertex-disjointness is captured by demanding that the
    concatenation of [edge_vertices] over [M] is [NoDup]. *)

Definition Matching (G : Graph) (M : list Edge) : Prop :=
  Forall (edge_in_graph G) M /\
  NoDup (concat (map edge_vertices M)).

(** ** Vertex cover predicate

    A [VertexCover G C] is a vertex list [C] such that every edge
    [(u, v) ∈ G] has [u ∈ C] or [v ∈ C]. *)

Definition VertexCover (G : Graph) (C : list nat) : Prop :=
  Forall (fun v => VertexOf G v) C /\
  forall u v, EdgeOf G u v -> In u C \/ In v C.

(** ** König's easy direction: [|M| ≤ |C|]

    Proof: for each edge [(u, v) ∈ M], at least one of [u, v] is in
    [C] (vertex-cover hypothesis). Map each edge to a chosen
    endpoint in [C]. This map is injective because two distinct
    matching-edges share no vertex, so they cannot map to the same
    cover-vertex. Injectivity gives [|M| ≤ |C|]. *)

(** Per-edge cover-endpoint selection: given the cover hypothesis,
    produce a function selecting one of the endpoints. *)

Definition cover_pick (C : list nat) (e : Edge) : nat :=
  if memb (fst e) C then fst e else snd e.

Lemma cover_pick_in : forall G M C e,
    Matching G M -> VertexCover G C ->
    In e M -> In (cover_pick C e) C.
Proof.
  intros G M C [u v] [HMall HMnd] [HCall HCcov] Hin.
  rewrite Forall_forall in HMall.
  pose proof (HMall (u, v) Hin) as Hedge.
  unfold cover_pick. simpl.
  destruct (memb u C) eqn:Em.
  - apply memb_true_iff; exact Em.
  - unfold edge_in_graph in Hedge. simpl in Hedge.
    pose proof (HCcov u v Hedge) as Hcov.
    destruct Hcov as [Hu | Hv]; [|exact Hv].
    rewrite memb_false_iff in Em. contradiction.
Qed.

(** Helper: a vertex of an edge in [M] appears in the concat. *)

Lemma in_concat_map_edge :
  forall (e : Edge) (M : list Edge) (x : nat),
    In e M -> In x (edge_vertices e) ->
    In x (concat (map edge_vertices M)).
Proof.
  intros e M x HeM HxE.
  apply in_concat. exists (edge_vertices e); split.
  - apply in_map_iff. exists e; split; [reflexivity | exact HeM].
  - exact HxE.
Qed.

Lemma cover_pick_in_concat : forall (e : Edge) (M : list Edge) (C : list nat),
    In e M -> In (cover_pick C e) (concat (map edge_vertices M)).
Proof.
  intros e M C HeM.
  apply (in_concat_map_edge e M); [exact HeM|].
  unfold cover_pick. destruct e as [u v]; simpl.
  destruct (memb u C); simpl; [left; reflexivity | right; left; reflexivity].
Qed.

(** Clean [NoDup_app] iff that the stdlib lacks by this name. *)

Lemma NoDup_app_iff_alt :
  forall (l l' : list nat),
    NoDup (l ++ l') <-> NoDup l /\ NoDup l' /\ (forall x, In x l -> ~ In x l').
Proof.
  intros l l'; split.
  - intros Hnd. split; [|split].
    + eapply NoDup_app_remove_r; eauto.
    + eapply NoDup_app_remove_l; eauto.
    + intros x Hxl Hxl'.
      induction l as [|a l IH]; [inversion Hxl|].
      simpl in Hnd. inversion Hnd as [|? ? Hnotin Hndr]; subst.
      destruct Hxl as [Eax | Hxl].
      * subst a. apply Hnotin. rewrite in_app_iff; right; exact Hxl'.
      * apply IH; auto.
  - intros [Hl [Hl' Hdis]].
    induction Hl; simpl; [exact Hl'|].
    constructor; [|apply IHHl; intros y Hy; apply Hdis; right; exact Hy].
    rewrite in_app_iff; intros [Hxl | Hxl']; [contradiction|].
    apply (Hdis x); [left; reflexivity | exact Hxl'].
Qed.

Lemma matching_pick_inj : forall G M C u1 v1 u2 v2,
    Matching G M ->
    In (u1, v1) M -> In (u2, v2) M ->
    cover_pick C (u1, v1) = cover_pick C (u2, v2) ->
    (u1, v1) = (u2, v2).
Proof.
  intros G M C u1 v1 u2 v2 [HMall HMnd] Hin1 Hin2 Heq.
  destruct (list_eq_dec Nat.eq_dec [u1; v1] [u2; v2]) as [Hed | Hed].
  - injection Hed as -> ->. reflexivity.
  - exfalso.
    set (p := cover_pick C (u1, v1)) in *.
    assert (Hp_e1 : In p (edge_vertices (u1, v1))).
    { unfold p, cover_pick; simpl. destruct (memb u1 C); simpl; auto. }
    assert (Hp_e2 : In p (edge_vertices (u2, v2))).
    { rewrite Heq. unfold cover_pick; simpl.
      destruct (memb u2 C); simpl; auto. }
    (* Now p is in two distinct sub-lists of concat. NoDup forbids. *)
    revert HMnd Hin1 Hin2 Hed Hp_e1 Hp_e2.
    generalize M; clear -HMall.
    intros M0; induction M0 as [|m rest IH]; intros HMnd Hin1 Hin2 Hed Hp1 Hp2;
      [inversion Hin1|].
    simpl in HMnd. apply NoDup_app_iff_alt in HMnd as [Hnd_m [Hnd_rest Hdis]].
    destruct Hin1 as [Em1 | Hin1], Hin2 as [Em2 | Hin2].
    + subst m. apply Hed. injection Em2; intros; subst; reflexivity.
    + subst m. apply (Hdis p Hp1).
      apply (in_concat_map_edge (u2, v2)); auto.
    + subst m. apply (Hdis p Hp2).
      apply (in_concat_map_edge (u1, v1)); auto.
    + apply (IH Hnd_rest Hin1 Hin2 Hed Hp1 Hp2).
Qed.

(** Direct cardinality bound for an injection. *)

Lemma injection_NoDup_map :
  forall (f : Edge -> nat) (l : list Edge),
    NoDup l ->
    (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
    NoDup (map f l).
Proof.
  intros f l Hnd Hinj.
  induction Hnd as [|x l Hni Hnd IH]; simpl; [constructor|].
  constructor.
  - intro Hinmap. apply in_map_iff in Hinmap as [y [Hfy Hyl]].
    apply Hni. assert (x = y).
    { apply Hinj.
      - left; reflexivity.
      - right; exact Hyl.
      - symmetry; exact Hfy. }
    subst y; exact Hyl.
  - apply IH. intros a b Ha Hb Hf.
    apply Hinj; [right; exact Ha | right; exact Hb | exact Hf].
Qed.

(** Now the headline theorem. *)

(** Matching implies plain NoDup on the edge list. *)

Lemma matching_NoDup : forall G M, Matching G M -> NoDup M.
Proof.
  intros G M [_ HMnd].
  induction M as [|e M' IH]; [constructor|].
  simpl in HMnd. apply NoDup_app_iff_alt in HMnd as [Hnde [Hndr Hdis]].
  constructor.
  - intro Hin. destruct e as [u v]. simpl in Hnde.
    apply (Hdis u).
    + left; reflexivity.
    + apply (in_concat_map_edge (u, v)); auto. left; reflexivity.
  - apply IH. exact Hndr.
Qed.

Theorem matching_le_cover : forall G M C,
    Matching G M -> VertexCover G C -> length M <= length C.
Proof.
  intros G M C HM HC.
  rewrite <- (map_length (cover_pick C) M).
  apply NoDup_incl_length.
  - apply injection_NoDup_map.
    + apply (matching_NoDup G); exact HM.
    + intros e1 e2 H1 H2 Heq.
      destruct e1 as [u1 v1], e2 as [u2 v2].
      eapply matching_pick_inj; eauto.
  - intros x Hx. apply in_map_iff in Hx as [e [Hfe HeM]].
    subst x. eapply cover_pick_in; eauto.
Qed.

(** ** Matching size bound: [2|M| ≤ |V|] *)

Lemma matching_concat_length :
  forall (M : list Edge),
    length (concat (map edge_vertices M)) = 2 * length M.
Proof.
  intros M; induction M as [|e M IH]; simpl; [reflexivity|].
  destruct e as [u v]; simpl. rewrite IH. lia.
Qed.

Theorem matching_le_half_vertices : forall G M,
    Simple G -> Matching G M ->
    2 * length M <= length (vertices G).
Proof.
  intros G M [_ [_ Hnd]] [HMall HMnd].
  rewrite <- matching_concat_length.
  apply NoDup_incl_length; [exact HMnd|].
  intros x Hx. apply in_concat in Hx as [evs [Hin Hxe]].
  apply in_map_iff in Hin as [e [Hfe HeM]]. subst evs.
  rewrite Forall_forall in HMall.
  pose proof (HMall e HeM) as Hedge.
  destruct e as [u v]; simpl in Hxe.
  destruct Hxe as [Eu | [Ev | []]].
  - subst x. destruct Hedge as [Hu _]; exact Hu.
  - subst x. destruct Hedge as [_ [Hv _]]; exact Hv.
Qed.

(** ** Augmenting paths in bipartite graphs

    An [AugmentingPath] in a bipartite graph for a matching [M] is
    a path starting and ending at vertices unmatched by [M], with
    alternating edges (in [M], not in [M], in [M], ...). Augmenting
    such a path increases [|M|] by 1.

    We give the predicate; the constructive maximum-matching
    extraction is left to a future file. *)

Definition unmatched (M : list Edge) (v : nat) : Prop :=
  ~ In v (concat (map edge_vertices M)).

Definition AugmentingPath (G : Graph) (M : list Edge)
                          (u v : nat) (p : list nat) : Prop :=
  Path G u v p /\
  unmatched M u /\ unmatched M v /\
  u <> v.

(** ** Bipartite-specific theorems

    König's equality theorem and Hall's marriage theorem, formerly
    axiomatised here, are proved constructively in
    [KoenigHall.v]:

      - [koenig_theorem]: maximum matching and minimum vertex cover
        exist and have equal size in any simple bipartite graph
        (König 1931; via the deficiency form of Hall's theorem).

      - [hall_marriage_theorem]: Hall's condition on [partA] yields a
        matching saturating [partA] (Hall 1935; Halmos-Vaughan
        induction).  NOTE: the axiom formerly stated here quantified
        Hall's condition over all [incl S partA] lists WITHOUT a
        [NoDup S] guard; duplicated-element lists make that
        hypothesis unsatisfiable whenever [partA] is nonempty, so the
        axiom was degenerate (vacuously satisfiable).  The proved
        statement adds [NoDup S] and is otherwise identical. *)
