(** * CliqueLowerBound.v -- An infinite family of exact sunflower lower bounds.

    [F23.two_triangles] is two disjoint copies of [K_3], and it
    witnesses [f(2,3) >= 7]. It is not an isolated construction: for
    every odd [k], two disjoint copies of [K_k] witness

    >  f(2,k) >= k(k-1) + 1.

    Why that shape and no other is the Chvátal–Hanson theorem
    ([ChHa76], cited but *not* formalised here):
    [CH(D, nu) = nu*D + floor(D/2) * floor(nu / ceil(D/2))] is the
    largest number of edges in a graph of maximum degree at most [D]
    and matching number at most [nu], and at [D = nu = k-1] with [k]
    odd the maximiser is exactly two copies of [K_k]. By
    [TwoUniform.two_uniform_sunflower_free_iff] those two parameters
    are precisely what a 2-uniform family must keep below [k] to avoid
    a [k]-sunflower.

    Nothing in this file depends on [ChHa76]: what is proved below is
    the lower bound, from the construction directly. The citation is
    what says the construction is *optimal* -- that
    [f(2,k) = k(k-1) + 1] rather than merely [>=] -- and that half is
    open here.

    The two constraints are checked separately and for different
    reasons. The *degree* bound is local: a vertex of [K_k] has [k-1]
    neighbours, so no vertex lies in [k] edges
    ([two_cliques_degree]). The *matching* bound is a parity argument
    ([two_cliques_matching_split]): [k] pairwise disjoint edges would
    need [2k] vertices, there are exactly [2k], so every vertex would
    be matched — but each component has an odd number of them, and an
    odd set has no perfect matching. Oddness of [k] is doing real work
    here, which is why the even case has a different extremal graph and
    is not proved here.

    At [k = 3] this reproduces [F23.f_2_3_lower] through a completely
    different argument: [F23.v] evaluates a reflective 3-sunflower
    detector on a literal six-edge family, this file counts degrees and
    matchings in a symbolic one ([lower_bound_2_3_from_cliques]).

    The upper half — that [CH(k-1,k-1)] edges is the *most* a
    sunflower-free graph can have — is a separate campaign. The naive
    counting that closes it at [k = 3] in [F23.v] does not generalise.

    Zero axioms, zero admits. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower LowerBound Spread Reflect TwoUniform.
Import ListNotations.

(** ** The complete graph on a vertex list

    [clique_edges l] is every 2-subset of [l], each written with its
    earlier vertex first, so distinct positions give distinct edges. *)

Fixpoint clique_edges (l : list nat) : Family :=
  match l with
  | [] => []
  | v :: rest => map (fun w => [v; w]) rest ++ clique_edges rest
  end.

Lemma clique_edges_subset :
  forall l A, In A (clique_edges l) -> Subset A l.
Proof.
  induction l as [|v rest IH]; simpl; intros A HA; [contradiction|].
  apply in_app_or in HA as [HA | HA].
  - apply in_map_iff in HA as [w [E Hw]]; subst A.
    intros z [E | [E | []]]; subst z; [left; reflexivity | right; exact Hw].
  - intros z Hz; right; exact (IH A HA z Hz).
Qed.

Lemma clique_edges_shape :
  forall l A,
    NoDup l -> In A (clique_edges l) ->
    exists a b, a <> b /\ A = [a; b] /\ In a l /\ In b l.
Proof.
  induction l as [|v rest IH]; simpl; intros A Hnd HA; [contradiction|].
  inversion Hnd as [|? ? Hni Hnd']; subst.
  apply in_app_or in HA as [HA | HA].
  - apply in_map_iff in HA as [w [E Hw]]; subst A.
    exists v, w. split; [|split; [|split]].
    + intro E; subst w; contradiction.
    + reflexivity.
    + left; reflexivity.
    + right; exact Hw.
  - destruct (IH A Hnd' HA) as [a [b [Hab [E [Ha Hb]]]]].
    exists a, b. split; [|split; [|split]];
      [exact Hab | exact E | right; exact Ha | right; exact Hb].
Qed.

Lemma clique_edges_uniform :
  forall l, NoDup l -> Uniform 2 (clique_edges l).
Proof.
  intros l Hnd; apply Forall_forall; intros A HA.
  destruct (clique_edges_shape l A Hnd HA) as [a [b [Hab [E _]]]]; subst A.
  split; [reflexivity|].
  constructor; [intros [E | []]; congruence |].
  constructor; [intros [] | constructor].
Qed.

(** Two edges of a clique are never set-equal: an edge from the [v]
    block contains [v], and an edge from the rest does not. *)

Lemma SetNoDup_app :
  forall F G : list (list nat),
    SetNoDup F -> SetNoDup G ->
    (forall A B, In A F -> In B G -> ~ SetEq A B) ->
    SetNoDup (F ++ G).
Proof.
  intros F G HF; induction HF as [|A F HniA HF IH]; simpl;
    intros HG Hcross; [exact HG|].
  constructor.
  - intros B HB. apply in_app_or in HB as [HB | HB].
    + apply HniA; exact HB.
    + apply Hcross; [left; reflexivity | exact HB].
  - apply IH; [exact HG|].
    intros X Y HX HY; apply Hcross; [right; exact HX | exact HY].
Qed.

Lemma SetNoDup_star_map :
  forall v rest,
    NoDup rest -> ~ In v rest ->
    SetNoDup (map (fun w => [v; w]) rest).
Proof.
  intros v rest; induction rest as [|w rest IH]; simpl; intros Hnd Hni;
    [constructor|].
  inversion Hnd as [|? ? Hniw Hnd']; subst.
  constructor.
  - intros B HB Hseq. apply in_map_iff in HB as [w' [E Hw']]; subst B.
    assert (Hw : In w [v; w']) by (apply (proj1 Hseq); right; left; reflexivity).
    destruct Hw as [E | [E | []]].
    + apply Hni; left; symmetry; exact E.
    + apply Hniw; rewrite E in Hw'; exact Hw'.
  - apply IH; [exact Hnd' | intro H; apply Hni; right; exact H].
Qed.

Lemma clique_edges_distinct :
  forall l, NoDup l -> Distinct (clique_edges l).
Proof.
  unfold Distinct; induction l as [|v rest IH]; simpl; intros Hnd;
    [constructor|].
  inversion Hnd as [|? ? Hni Hnd']; subst.
  apply SetNoDup_app.
  - apply SetNoDup_star_map; [exact Hnd' | exact Hni].
  - apply IH; exact Hnd'.
  - intros A B HA HB Hseq.
    apply in_map_iff in HA as [w [E Hw]]; subst A.
    apply Hni.
    apply (clique_edges_subset rest B HB).
    apply (proj1 Hseq); left; reflexivity.
Qed.

(** [2|E| + |V| = |V|^2] for the complete graph — the edge count
    without a division. *)

Lemma clique_edges_length :
  forall l, 2 * length (clique_edges l) + length l = length l * length l.
Proof.
  induction l as [|v rest IH]; [reflexivity|].
  simpl (clique_edges (v :: rest)).
  rewrite app_length, map_length.
  simpl (length (v :: rest)).
  nia.
Qed.

(** ** The trivial degree bound

    In a distinct 2-uniform family over a ground set [U], a vertex of
    [U] lies in fewer than [|U|] members: its partner in each such
    member is a different point of [U], and two members with the same
    partner would be the same edge. *)

Lemma singleton_pairwise_disjoint :
  forall S : list (list nat), Uniform 1 S -> NoDup S -> PairwiseDisjoint S.
Proof.
  intros S HU Hnd A B HA HB Hne z HzA HzB.
  apply Hne.
  unfold Uniform in HU; rewrite Forall_forall in HU.
  destruct (HU A HA) as [HlA _]. destruct (HU B HB) as [HlB _].
  destruct A as [|a [|? ?]]; simpl in HlA; try discriminate.
  destruct B as [|b [|? ?]]; simpl in HlB; try discriminate.
  destruct HzA as [E | []]; destruct HzB as [E' | []]; congruence.
Qed.

Lemma deg_zero_of_not_in :
  forall F v, (forall A, In A F -> ~ In v A) -> deg [v] F = 0.
Proof.
  intros F v H; unfold deg.
  destruct (filter (containsb [v]) F) as [|A L] eqn:E; [reflexivity|].
  exfalso.
  assert (HA : In A (filter (containsb [v]) F)) by (rewrite E; left; reflexivity).
  apply filter_In in HA as [HAF Hc].
  apply containsb_true_iff in Hc.
  apply (H A HAF), Hc; left; reflexivity.
Qed.

Lemma deg_app :
  forall T F G, deg T (F ++ G) = deg T F + deg T G.
Proof.
  intros T F G; unfold deg; rewrite filter_app, app_length; reflexivity.
Qed.

Lemma deg_lt_ground :
  forall (F : Family) (U : list nat) (v : nat),
    Uniform 2 F -> Distinct F -> NoDup U ->
    (forall A, In A F -> Subset A U) ->
    In v U ->
    deg [v] F < length U.
Proof.
  intros F U v HU HD HndU Hsub HvU.
  assert (HLF : forall A, In A (filter (containsb [v]) F) -> In A F)
    by (intros A HA; apply filter_In in HA; tauto).
  assert (HLv : Forall (fun A => In v A) (filter (containsb [v]) F)).
  { apply Forall_forall; intros A HA. apply filter_In in HA as [_ Hc].
    apply containsb_true_iff in Hc; apply Hc; left; reflexivity. }
  assert (HLsnd : SetNoDup (filter (containsb [v]) F))
    by (apply SetNoDup_filter; exact HD).
  (* Replace each member by its other endpoint: distinct singletons. *)
  assert (HMsnd : SetNoDup (map (rem_elt v) (filter (containsb [v]) F)))
    by (apply SetNoDup_map_rem_preserves; assumption).
  assert (HMu : Uniform 1 (map (rem_elt v) (filter (containsb [v]) F))).
  { apply Forall_forall; intros X HX.
    apply in_map_iff in HX as [A [E HA]]; subst X.
    assert (HAF : In A F) by (apply HLF; exact HA).
    unfold Uniform in HU; rewrite Forall_forall in HU, HLv.
    destruct (HU A HAF) as [HlA HndA].
    split.
    - rewrite (@length_rem_elt_in v A HndA (HLv A HA)), HlA; reflexivity.
    - apply rem_NoDup; exact HndA. }
  assert (HMsub : forall X, In X (map (rem_elt v) (filter (containsb [v]) F)) ->
                            Subset X (rem_elt v U)).
  { intros X HX. apply in_map_iff in HX as [A [E HA]]; subst X.
    intros z Hz. apply in_rem_iff in Hz as [HzA Hzv].
    apply in_rem_iff; split; [apply (Hsub A (HLF A HA)); exact HzA | exact Hzv]. }
  pose proof (@pairwise_disjoint_ground_bound
                (map (rem_elt v) (filter (containsb [v]) F)) (rem_elt v U) 1
                (SetNoDup_NoDup HMsnd) (rem_NoDup v HndU) HMu HMsub
                (singleton_pairwise_disjoint _ HMu (SetNoDup_NoDup HMsnd))) as Hb.
  rewrite map_length, Nat.mul_1_r in Hb.
  rewrite (@length_rem_elt_in v U HndU HvU) in Hb.
  unfold deg.
  destruct U as [|u U']; [contradiction | simpl in Hb |- *; lia].
Qed.

(** ** Two disjoint cliques *)

Definition two_cliques (U0 U1 : list nat) : Family :=
  clique_edges U0 ++ clique_edges U1.

Lemma two_cliques_uniform :
  forall U0 U1, NoDup U0 -> NoDup U1 -> Uniform 2 (two_cliques U0 U1).
Proof.
  intros U0 U1 H0 H1; unfold two_cliques, Uniform.
  apply Forall_app; split; apply clique_edges_uniform; assumption.
Qed.

Lemma two_cliques_distinct :
  forall U0 U1,
    NoDup U0 -> NoDup U1 -> Disjoint U0 U1 ->
    Distinct (two_cliques U0 U1).
Proof.
  intros U0 U1 H0 H1 Hdis; unfold two_cliques, Distinct.
  apply SetNoDup_app;
    [apply clique_edges_distinct; exact H0
    | apply clique_edges_distinct; exact H1 |].
  intros A B HA HB Hseq.
  destruct (clique_edges_shape U0 A H0 HA) as [a [b [_ [E [Ha _]]]]].
  apply (Hdis a Ha).
  apply (clique_edges_subset U1 B HB).
  apply (proj1 Hseq); subst A; left; reflexivity.
Qed.

Lemma two_cliques_length :
  forall U0 U1 k,
    length U0 = k -> length U1 = k ->
    length (two_cliques U0 U1) = k * (k - 1).
Proof.
  intros U0 U1 k H0 H1; unfold two_cliques.
  pose proof (clique_edges_length U0) as E0.
  pose proof (clique_edges_length U1) as E1.
  rewrite H0 in E0; rewrite H1 in E1.
  rewrite app_length.
  destruct k as [|n]; [simpl in *; lia|].
  rewrite Nat.sub_succ, Nat.sub_0_r.
  nia.
Qed.

(** The degree bound: a vertex of one clique has [k-1] neighbours
    there and none in the other. *)

Lemma two_cliques_degree :
  forall U0 U1 k v,
    length U0 = k -> length U1 = k ->
    NoDup U0 -> NoDup U1 -> Disjoint U0 U1 -> 1 <= k ->
    deg [v] (two_cliques U0 U1) < k.
Proof.
  intros U0 U1 k v H0 H1 Hnd0 Hnd1 Hdis Hk.
  unfold two_cliques; rewrite deg_app.
  assert (Hout : forall U, NoDup U -> ~ In v U -> deg [v] (clique_edges U) = 0).
  { intros U HndU HvU. apply deg_zero_of_not_in.
    intros A HA HvA. apply HvU. exact (clique_edges_subset U A HA v HvA). }
  assert (Hin : forall U, NoDup U -> In v U ->
                          deg [v] (clique_edges U) < length U).
  { intros U HndU HvU.
    apply (deg_lt_ground (clique_edges U) U v);
      [apply clique_edges_uniform; exact HndU
      | apply clique_edges_distinct; exact HndU
      | exact HndU
      | intros A HA; exact (clique_edges_subset U A HA)
      | exact HvU]. }
  destruct (in_dec_nat v U0) as [Hv0 | Hv0].
  - rewrite (Hout U1 Hnd1 (fun H => Hdis v Hv0 H)).
    pose proof (Hin U0 Hnd0 Hv0); lia.
  - rewrite (Hout U0 Hnd0 Hv0).
    destruct (in_dec_nat v U1) as [Hv1 | Hv1].
    + pose proof (Hin U1 Hnd1 Hv1); lia.
    + rewrite (Hout U1 Hnd1 Hv1); lia.
Qed.

(** ** The matching bound

    Every edge lies in one clique or the other, so a pairwise disjoint
    subfamily splits in two, and each half is bounded by the vertices
    available to it. *)

Lemma filter_partition_length :
  forall (X : Type) (f : X -> bool) (l : list X),
    length (filter f l) + length (filter (fun x => negb (f x)) l) = length l.
Proof.
  intros X f l; induction l as [|x l IH]; simpl; [reflexivity|].
  destruct (f x); simpl; lia.
Qed.

Lemma two_cliques_matching_split :
  forall (U0 U1 : list nat) (S : list (list nat)),
    NoDup U0 -> NoDup U1 ->
    incl S (two_cliques U0 U1) -> NoDup S -> PairwiseDisjoint S ->
    exists s0 s1,
      length S = s0 + s1 /\ 2 * s0 <= length U0 /\ 2 * s1 <= length U1.
Proof.
  intros U0 U1 S Hnd0 Hnd1 Hincl HndS Hpd.
  exists (length (filter (fun A => subsetb A U0) S)),
         (length (filter (fun A => negb (subsetb A U0)) S)).
  split; [symmetry; apply filter_partition_length|].
  assert (HU2 : Uniform 2 (two_cliques U0 U1))
    by (apply two_cliques_uniform; assumption).
  (* Both halves inherit everything but the ground set. *)
  assert (Hhalf : forall (p : list nat -> bool) (U : list nat),
             NoDup U ->
             (forall A, In A S -> p A = true -> Subset A U) ->
             2 * length (filter p S) <= length U).
  { intros p U HndU Hin.
    assert (Hb := @pairwise_disjoint_ground_bound (filter p S) U 2).
    rewrite Nat.mul_comm in Hb.
    apply Hb.
    - apply NoDup_filter; exact HndS.
    - exact HndU.
    - apply Forall_forall; intros A HA. apply filter_In in HA as [HA _].
      unfold Uniform in HU2; rewrite Forall_forall in HU2.
      apply HU2, Hincl, HA.
    - intros A HA. apply filter_In in HA as [HA Hp]. exact (Hin A HA Hp).
    - intros A B HA HB HAB.
      apply filter_In in HA as [HA _]; apply filter_In in HB as [HB _].
      exact (Hpd A B HA HB HAB). }
  split.
  - apply (Hhalf _ U0 Hnd0).
    intros A _ Hp; apply subsetb_correct; exact Hp.
  - apply (Hhalf _ U1 Hnd1).
    intros A HA Hp.
    (* Not inside [U0], so not an edge of the first clique. *)
    apply Bool.negb_true_iff in Hp.
    pose proof (Hincl A HA) as HAin; unfold two_cliques in HAin.
    apply in_app_or in HAin as [HA0 | HA1].
    + exfalso.
      assert (subsetb A U0 = true)
        by (apply subsetb_correct; exact (clique_edges_subset U0 A HA0)).
      congruence.
    + exact (clique_edges_subset U1 A HA1).
Qed.

(** ** The lower bound

    An odd number of vertices in each component is what kills the
    perfect matching, and hence what makes [k] odd a hypothesis rather
    than a convenience. *)

Theorem two_cliques_no_sunflower :
  forall U0 U1 k,
    length U0 = k -> length U1 = k ->
    NoDup U0 -> NoDup U1 -> Disjoint U0 U1 ->
    3 <= k -> Nat.Odd k ->
    ~ ContainsKSunflower k (two_cliques U0 U1).
Proof.
  intros U0 U1 k H0 H1 Hnd0 Hnd1 Hdis Hk Hodd.
  apply (two_uniform_sunflower_free_iff k (two_cliques U0 U1) ltac:(lia)
           (two_cliques_uniform U0 U1 Hnd0 Hnd1)
           (two_cliques_distinct U0 U1 Hnd0 Hnd1 Hdis)).
  split.
  - intros [S [Hincl [Hnd [Hlen Hpd]]]].
    destruct (two_cliques_matching_split U0 U1 S Hnd0 Hnd1 Hincl Hnd Hpd)
      as [s0 [s1 [Hs [Hb0 Hb1]]]].
    rewrite H0 in Hb0; rewrite H1 in Hb1.
    destruct Hodd as [t Ht].
    (* [s0 + s1 = k] with [2 s0 <= k] and [2 s1 <= k] forces [2 s0 = k]. *)
    lia.
  - intros v.
    apply (two_cliques_degree U0 U1 k v H0 H1 Hnd0 Hnd1 Hdis); lia.
Qed.

Theorem two_cliques_lower_bound :
  forall k, 3 <= k -> Nat.Odd k -> LowerBound 2 k (k * (k - 1)).
Proof.
  intros k Hk Hodd.
  assert (Hdis : Disjoint (seq 0 k) (seq k k)).
  { intros x Hx0 Hx1.
    apply in_seq in Hx0; apply in_seq in Hx1; lia. }
  exists (two_cliques (seq 0 k) (seq k k)).
  split; [|split; [|split]].
  - apply two_cliques_uniform; apply seq_NoDup.
  - apply two_cliques_distinct; try apply seq_NoDup; exact Hdis.
  - pose proof (two_cliques_length (seq 0 k) (seq k k) k
                  (seq_length k 0) (seq_length k k)) as Hlen; lia.
  - apply (two_cliques_no_sunflower _ _ k);
      try apply seq_length; try apply seq_NoDup; assumption.
Qed.

(** So [f(2,k) >= k(k-1) + 1] for every odd [k]: no family of
    [k(k-1)] distinct pairs is forced to contain a [k]-sunflower. *)

Corollary no_upper_bound_at_ch :
  forall k, 3 <= k -> Nat.Odd k -> ~ UpperBound 2 k (k * (k - 1)).
Proof.
  intros k Hk Hodd Hub.
  destruct (two_cliques_lower_bound k Hk Hodd) as [F [HU [HD [Hlen Hns]]]].
  apply Hns, Hub; [exact HU | exact HD | lia].
Qed.

(** ** Coherence with the one exact value already proved

    At [k = 3] the construction is two triangles and the bound is 6 —
    which is [F23.f_2_3_lower], reached here without evaluating a
    sunflower detector on anything. The two proofs share no step: that
    one runs [sunflower3b] on a literal family by [vm_compute], this
    one counts degrees and matchings in a symbolic one. *)

Example clique_construction_at_k_3 :
  two_cliques [0; 1; 2] [3; 4; 5]
  = [[0; 1]; [0; 2]; [1; 2]; [3; 4]; [3; 5]; [4; 5]].
Proof. vm_compute; reflexivity. Qed.

Corollary lower_bound_2_3_from_cliques : LowerBound 2 3 6.
Proof.
  replace 6 with (3 * (3 - 1)) by reflexivity.
  apply two_cliques_lower_bound; [lia | exists 1; reflexivity].
Qed.
