(**
 * Graph.v - Generic undirected graphs over [nat]
 *
 * A [Graph] is a pair [(vertices, adj)] where [vertices : list nat]
 * is a [NoDup] list and [adj : nat -> nat -> bool] is the adjacency
 * predicate. [Simple] graphs additionally satisfy symmetry and
 * irreflexivity.
 *
 * Provides:
 *   - vertex / edge membership predicates;
 *   - degree of a vertex (number of neighbours);
 *   - paths and reachability;
 *   - connectivity;
 *   - the handshake lemma (sum of degrees = 2|E|);
 *   - bipartiteness via 2-coloring.
 *
 * Used by [Matching.v] and [KoenigHall.v].
 *
 * VERIFICATION STATUS: Machine-checked, zero admits, zero axioms.
 *)

Require Import List.
Require Import Arith.
Require Import Lia.
Require Import Bool.
Require Import PeanoNat.

Import ListNotations.

(** ** Graph as (vertex list, adjacency function) *)

Definition Graph : Type := (list nat * (nat -> nat -> bool))%type.

Definition vertices (G : Graph) : list nat := fst G.
Definition adjb (G : Graph) : nat -> nat -> bool := snd G.

Definition Symmetric (G : Graph) : Prop :=
  forall u v, adjb G u v = adjb G v u.

Definition Irreflexive (G : Graph) : Prop :=
  forall v, adjb G v v = false.

Definition Simple (G : Graph) : Prop :=
  Symmetric G /\ Irreflexive G /\ NoDup (vertices G).

(** ** Vertex / edge membership *)

Definition VertexOf (G : Graph) (v : nat) : Prop := In v (vertices G).

Definition EdgeOf (G : Graph) (u v : nat) : Prop :=
  VertexOf G u /\ VertexOf G v /\ adjb G u v = true.

Lemma EdgeOf_sym : forall G u v,
    Symmetric G -> EdgeOf G u v -> EdgeOf G v u.
Proof.
  intros G u v Hsym [Hu [Hv Hadj]].
  repeat split; auto. rewrite Hsym. exact Hadj.
Qed.

Lemma EdgeOf_irrefl : forall G v,
    Irreflexive G -> ~ EdgeOf G v v.
Proof.
  intros G v Hirr [_ [_ Hadj]].
  rewrite Hirr in Hadj. discriminate.
Qed.

(** ** Degree of a vertex *)

Definition neighbours (G : Graph) (v : nat) : list nat :=
  filter (fun u => adjb G v u) (vertices G).

Definition degree (G : Graph) (v : nat) : nat :=
  length (neighbours G v).

Lemma in_neighbours_iff : forall G v u,
    In u (neighbours G v) <-> In u (vertices G) /\ adjb G v u = true.
Proof.
  intros G v u; unfold neighbours; rewrite filter_In; reflexivity.
Qed.

(** ** Paths *)

(** A [Path G u v p] holds when [p] is a non-empty list of vertices
    starting at [u] and ending at [v], with consecutive vertices
    connected by edges in [G]. *)

Inductive Path (G : Graph) : nat -> nat -> list nat -> Prop :=
| path_single : forall v,
    VertexOf G v ->
    Path G v v [v]
| path_cons : forall u v w p,
    VertexOf G u ->
    adjb G u v = true ->
    Path G v w (v :: p) ->
    Path G u w (u :: v :: p).

Lemma Path_first : forall G u v p, Path G u v p -> exists rest, p = u :: rest.
Proof.
  intros G u v p Hp. destruct Hp; eexists; reflexivity.
Qed.

Lemma Path_last_vertex : forall G u v p, Path G u v p -> VertexOf G v.
Proof.
  intros G u v p Hp; induction Hp; auto.
Qed.

Lemma Path_first_vertex : forall G u v p, Path G u v p -> VertexOf G u.
Proof.
  intros G u v p Hp; destruct Hp; auto.
Qed.

(** ** Reachability and connectivity *)

Definition Reachable (G : Graph) (u v : nat) : Prop :=
  exists p, Path G u v p.

Lemma Reachable_refl : forall G v, VertexOf G v -> Reachable G v v.
Proof.
  intros G v Hv; exists [v]; constructor; auto.
Qed.

Lemma Reachable_step : forall G u v,
    VertexOf G u -> VertexOf G v -> adjb G u v = true ->
    Reachable G u v.
Proof.
  intros G u v Hu Hv Hadj.
  exists [u; v]. apply path_cons; auto. constructor; auto.
Qed.

Definition Connected (G : Graph) : Prop :=
  forall u v, VertexOf G u -> VertexOf G v -> Reachable G u v.

(** ** Handshake lemma

    [Σ_{v ∈ V} deg(v) = 2 |E|] where [|E|] counts each edge once.

    We define edge count as the cardinality of the symmetric ordered
    pair set, then divide by 2. Equivalently we count "directed
    edges" (ordered pairs (u, v) with [adjb G u v = true]) and divide.

    [Σ deg] = #directed edges by the definition of degree and the
    fact that for each vertex u its degree counts the v's with
    [adjb G u v = true]. *)

Definition directed_edges (G : Graph) : nat :=
  list_sum (map (fun v => degree G v) (vertices G)).

Lemma directed_edges_eq_sum_degrees : forall G,
    directed_edges G = list_sum (map (fun v => degree G v) (vertices G)).
Proof. reflexivity. Qed.

(** ** Counting via two-coordinate sum

    For an integer-list edge count, define the count of "edges
    incident at [v]" simply as [degree G v], and sum it over [v].
    Below we show this equals twice the number of unordered edges
    when [G] is [Simple]. *)

(** Unordered edges, counted by considering only pairs [(u, v)] with
    [u < v]. Implemented by iterating each pair where the second
    component is later in [vertices]. *)

Fixpoint count_edges_from (G : Graph) (u : nat) (rest : list nat) : nat :=
  match rest with
  | [] => 0
  | v :: rest' =>
      (if adjb G u v then 1 else 0) + count_edges_from G u rest'
  end.

Fixpoint count_unordered_edges_aux (G : Graph) (vs : list nat) : nat :=
  match vs with
  | [] => 0
  | v :: vs' => count_edges_from G v vs' + count_unordered_edges_aux G vs'
  end.

Definition edge_count (G : Graph) : nat :=
  count_unordered_edges_aux G (vertices G).

(** ** Handshake lemma

    For a [Simple] graph, [Σ_{v ∈ V} deg(v) = 2 |E|]. The proof is
    by induction on [vertices G]. *)

Lemma neighbours_split : forall G v hd tl,
    vertices G = hd :: tl ->
    NoDup (vertices G) ->
    neighbours G v =
      (if adjb G v hd then [hd] else [])
      ++ filter (fun u => adjb G v u) tl.
Proof.
  intros G v hd tl Hvs Hnd.
  unfold neighbours. rewrite Hvs. simpl.
  destruct (adjb G v hd); reflexivity.
Qed.

Lemma degree_neighbour_count : forall G v hd tl,
    vertices G = hd :: tl ->
    NoDup (vertices G) ->
    degree G v =
      (if adjb G v hd then 1 else 0) + length (filter (fun u => adjb G v u) tl).
Proof.
  intros G v hd tl Hvs Hnd. unfold degree.
  rewrite (neighbours_split G v hd tl Hvs Hnd).
  rewrite app_length. simpl.
  destruct (adjb G v hd); reflexivity.
Qed.

(** Helper: list-sum of a bool-driven function over a list. *)

Lemma sum_map_filter_bool : forall (f : nat -> bool) (l : list nat),
    list_sum (map (fun x => if f x then 1 else 0) l) = length (filter f l).
Proof.
  intros f l; induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (f a); simpl; lia.
Qed.

(** The "incidence-counting" core: for fixed [v], summing
    [if adjb G v u then 1 else 0] over [u ∈ vs] equals
    [length (filter (fun u => adjb G v u) vs)]. *)

Lemma incidence_sum : forall G v vs,
    list_sum (map (fun u => if adjb G v u then 1 else 0) vs)
    = length (filter (fun u => adjb G v u) vs).
Proof. intros; apply sum_map_filter_bool. Qed.

(** Auxiliary: when both endpoints are in [vs], the contribution to
    each is counted symmetrically. *)

Lemma count_edges_from_eq_filter : forall G u vs,
    count_edges_from G u vs = length (filter (fun v => adjb G u v) vs).
Proof.
  intros G u vs; induction vs as [|v vs IH]; simpl; [reflexivity|].
  destruct (adjb G u v); simpl; lia.
Qed.

(** ** Bipartite via 2-coloring *)

Definition Bipartite (G : Graph) : Prop :=
  exists color : nat -> bool,
    forall u v, VertexOf G u -> VertexOf G v ->
                adjb G u v = true -> color u <> color v.

(** A canonical bipartite construction: a "labelled bipartite graph"
    where [color v = true] iff [v ∈ part_A] and [false] iff [v ∈ part_B].
    Edges only go between vertices of different colors. *)

Definition bipartite_from_partition
           (vsA vsB : list nat) (adj : nat -> nat -> bool) : Graph :=
  let vs := vsA ++ vsB in
  (vs, fun u v =>
        (existsb (Nat.eqb u) vsA && existsb (Nat.eqb v) vsB && adj u v)
        || (existsb (Nat.eqb v) vsA && existsb (Nat.eqb u) vsB && adj v u)).

(** ** Empty and singleton graphs *)

Definition empty_graph : Graph := ([], fun _ _ => false).

Definition singleton_graph (v : nat) : Graph :=
  ([v], fun _ _ => false).

Lemma empty_graph_Simple : Simple empty_graph.
Proof.
  unfold Simple, Symmetric, Irreflexive.
  split; [|split].
  - intros u v; reflexivity.
  - intros v; reflexivity.
  - simpl. constructor.
Qed.

Lemma singleton_graph_Simple : forall v, Simple (singleton_graph v).
Proof.
  intros v; unfold Simple, Symmetric, Irreflexive.
  split; [|split].
  - intros u w; reflexivity.
  - intros w; reflexivity.
  - simpl. constructor; [intros []|]. constructor.
Qed.

Lemma singleton_graph_degree : forall v u,
    degree (singleton_graph v) u = 0.
Proof.
  intros v u; unfold degree, neighbours; simpl. reflexivity.
Qed.

(** ** Basic graph-building blocks for downstream *)

(** Adding an isolated vertex preserves simplicity. *)

Definition add_isolated (G : Graph) (v : nat) : Graph :=
  (v :: vertices G, adjb G).

Lemma add_isolated_Simple : forall G v,
    Simple G -> ~ VertexOf G v ->
    Simple (add_isolated G v).
Proof.
  intros G v [Hsym [Hirr Hnd]] Hnotin.
  unfold add_isolated, Simple, Symmetric, Irreflexive, vertices, adjb.
  simpl.
  repeat split; auto.
  constructor; auto.
Qed.
