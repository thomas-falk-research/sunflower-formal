(** * Maximal.v — the 1972 construction cannot be extended

    [docs/roadmap.md] §12 gives the threshold at every uniformity: the
    Abbott–Hanson–Sauer record falls the moment some family beats
    [10^((b-1)/2)]. At [b = 9] the substitution
    [substitute(iota(3), iota(3))] builds 10,000 members and the
    threshold is 10,001, so **one** further 9-set would beat 1972
    outright. This file records the answer to the cheapest form of that
    question, which nobody had asked.

    ** The question, and why it is finite

    "Can a set be added?" looks like a question about a ground set: add a
    member on ten points, on eleven, on twelve. It is not. A candidate
    [C] interacts with the family only through its **trace**
    [S = C ∩ U] on the ground set the family already uses — a point in no
    member contributes to no intersection — so [C] meets [A] iff [S]
    does, and [A ∩ C = A ∩ S]. Enumerating traces answers the question
    for every ground set at once, and [maximal_of_trace_certificate] is
    that reduction: a `forallb` over [HallCore.sublists U] implies a
    statement quantified over **every list [A] whatsoever**, with no
    ground-set hypothesis anywhere in it.

    ** What was measured, before any of it was proved

    [rust/examples/extend_ahs.rs], with two independent methods that
    agree — a minimal-hitting-set enumeration, and a SAT encoding whose
    UNSAT verdicts are accepted only when two solvers agree — plus brute
    force over every trace wherever that is affordable:

    >  family                                  b    members   tau   addable
    >  substitute(iota(2), iota(2))            4         27     4   none
    >  substitute(iota(2), iota(3))            6        300     6   none
    >  substitute(iota(3), iota(3))            9      10000     9   none
    >  cone(substitute(g(2), iota(2)))         5         54     -   none
    >  cone(substitute(g(2), iota(3)))         7        600     -   none

    Every row is maximal, on every ground set. For the three pure
    substitutions the verdict does not even use sunflower-freeness: no
    [b]-set meets every member except the members themselves.

    ** The mechanism, in one line

    The covering number is **multiplicative** under the substitution. A
    set [C] meets every member of [substitute(G,H)] exactly when
    [{v : C_v is a transversal of H}] is a transversal of [G], so
    [tau(substitute(G,H)) >= tau(G) tau(H)]; and an intersecting family
    is met by each of its own members, so [tau <= ab]. When
    [tau(G) = a] and [tau(H) = b] — which is what "no transversal smaller
    than a member" means — the two meet, and the minimum transversals are
    exactly the members. **Maximality is multiplicative under
    substitution**, and [iota(2)] and [iota(3)] are both maximal, so the
    whole 3-adic tower is.

    That general statement needs [substitute] formalised, which
    [docs/roadmap.md] §5 item 2 costs a session on its own. What is
    proved here is the reduction in general and the [b = 4] instance
    reflectively.

    ** What it does *not* say, and this is the important half

    **Maximal is not maximum**, and [maximality_is_not_a_size_bound] is
    the witness: the Fano plane is a maximal intersecting 3-uniform
    family with **seven** members, while [Intersecting.iota3] is an
    intersecting 3-uniform family with **ten**. So a family nothing can
    be added to may be strictly smaller than one that exists, and the
    negative result closes one route to the record while saying nothing
    about whether the record is reachable by another.

    Zero axioms, zero admits. *)

From Coq Require Import List Arith Lia Bool.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower HallCore LowerBound Reflect
     Pigeonhole Conjecture F23 Intersecting IotaRate SliceRank IotaGround
     Product.
Import ListNotations.

(** ** Maximality, with no ground set in the statement

    "Nothing can be added" in the strongest available sense: for *every*
    list [A] whatsoever, [A :: F] fails to be a [b]-uniform distinct
    intersecting family. Nothing here bounds where [A] lives, and
    nothing here mentions sunflowers — for the substitution families the
    intersecting condition alone already decides, which is the stronger
    negative. *)

Definition MaximalIntersecting (b : nat) (F : Family) : Prop :=
  forall A : list nat,
    Uniform b (A :: F) -> Distinct (A :: F) -> Intersecting (A :: F) -> False.

(** The sunflower-free reading is weaker and follows: a family admitting
    no intersecting extension admits no sunflower-free intersecting one
    either. Stated so the two are not confused. *)

Theorem maximal_intersecting_is_maximal_iota :
  forall b F,
    MaximalIntersecting b F ->
    forall A,
      Uniform b (A :: F) -> Distinct (A :: F) -> Intersecting (A :: F) ->
      ~ ContainsKSunflower 3 (A :: F) -> False.
Proof. intros b F Hmax A HU HD HI _; exact (Hmax A HU HD HI). Qed.

(** ** The trace reduction, as a reusable certificate

    [blocksb T F] is "T meets every member". The certificate asks: over
    the sublists of the ground set — which is what [HallCore.sublists]
    enumerates, [2^|U|] of them — every trace of size at most [b] that
    meets every member has size exactly [b] and is set-equal to a member.

    That finite check implies maximality over every ground set. The proof
    is the trace argument written out: the common point of [A] and a
    member lies in the member, hence in [U], hence in the trace; the
    trace is [NoDup] and inside [A], so it has at most [b] points; the
    certificate then makes it a member; and a point of [A] outside the
    trace would give [A] a [(b+1)]-st point. *)

Definition blocksb (T : list nat) (F : Family) : bool :=
  forallb (fun B => existsb (fun x => memb x B) T) F.

Definition trace_certificate (b : nat) (F : Family) (U : list nat) : bool :=
  forallb
    (fun T =>
       implb (Nat.leb (length T) b && blocksb T F)
             (Nat.eqb (length T) b && existsb (fun B => seteqb T B) F))
    (sublists U).

Theorem maximal_of_trace_certificate :
  forall b F U,
    NoDup U -> Grounded F U ->
    trace_certificate b F U = true ->
    MaximalIntersecting b F.
Proof.
  intros b F U HndU Hgr Hcert A HU HD HI.
  assert (HUA : UniformSet b A).
  { unfold Uniform in HU; inversion HU as [|X G Hh Ht Heq]; exact Hh. }
  destruct HUA as [HlenA HndA].
  set (T := filter (fun x => memb x A) U).
  assert (HTsub : In T (sublists U)) by apply filter_in_sublists.
  assert (HTnd : NoDup T)
    by (eapply sublists_NoDup_members; [exact HndU | exact HTsub]).
  assert (HTA : Subset T A).
  { intros x Hx; unfold T in Hx; apply filter_In in Hx as [_ Hm].
    apply memb_true_iff; exact Hm. }
  assert (HTlen : length T <= b).
  { rewrite <- HlenA; apply NoDup_incl_length; [exact HTnd | exact HTA]. }
  assert (Hblocks : blocksb T F = true).
  { apply forallb_forall; intros B HB.
    destruct (disjointb A B) eqn:E.
    - exfalso.
      apply (HI A B (or_introl eq_refl) (or_intror HB)).
      apply disjointb_correct; exact E.
    - apply disjointb_false_iff in E as [x [HxA HxB]].
      apply existsb_exists; exists x; split; [| apply memb_true_iff; exact HxB].
      unfold T; apply filter_In; split.
      + exact (Hgr B HB x HxB).
      + apply memb_true_iff; exact HxA. }
  pose proof (proj1 (forallb_forall _ _) Hcert T HTsub) as Hcheck.
  cbv beta in Hcheck.
  assert (Hle : Nat.leb (length T) b = true) by (apply Nat.leb_le; exact HTlen).
  rewrite Hblocks, Hle in Hcheck; simpl in Hcheck.
  apply Bool.andb_true_iff in Hcheck as [Hlenb Hex].
  apply Nat.eqb_eq in Hlenb.
  apply existsb_exists in Hex as [B [HB Hseq]].
  apply seteqb_correct in Hseq.
  assert (HAT : Subset A T).
  { intros x HxA.
    destruct (in_dec_nat x T) as [Hin | Hnin]; [exact Hin | exfalso].
    assert (Hnd2 : NoDup (x :: T)) by (constructor; assumption).
    assert (Hincl : incl (x :: T) A).
    { intros y Hy; destruct Hy as [Ey | Hy];
        [subst y; exact HxA | apply HTA; exact Hy]. }
    pose proof (NoDup_incl_length Hnd2 Hincl) as Hlen'.
    simpl in Hlen'; lia. }
  assert (HAB : SetEq A B).
  { apply (SetEq_trans (A := A) (B := T) (C := B));
      [split; [exact HAT | exact HTA] | exact Hseq]. }
  inversion HD as [|X G Hni Ht Heq]; subst.
  exact (Hni B HB HAB).
Qed.

(** ** The Abbott–Hanson–Sauer family at [b = 4] is maximal

    [Product.iota4] is the substitution of the triangle into itself and
    is the exhaustive maximum [iota(4,9) = 27] (`docs/roadmap.md` §11.5,
    with [|Aut| = 1296] cross-checked against nauty). Nothing can be
    added to it — on any ground set, and without using
    sunflower-freeness at all. *)

Lemma iota4_trace_certificate : trace_certificate 4 iota4 (seq 0 9) = true.
Proof. vm_compute; reflexivity. Qed.

Theorem iota4_is_maximal_intersecting : MaximalIntersecting 4 iota4.
Proof.
  apply (maximal_of_trace_certificate 4 iota4 (seq 0 9)).
  - exact (seq_NoDup 9 0).
  - exact iota4_grounded.
  - exact iota4_trace_certificate.
Qed.

(** The covering number is what the certificate really computes, and it
    is the quantity the general argument multiplies: every trace meeting
    every member has at least [b] points, and one of exactly [b] exists —
    so [tau(iota4) = 4], the uniformity itself. *)

Theorem iota4_covering_number_is_four :
  (forall T, In T (sublists (seq 0 9)) -> blocksb T iota4 = true -> 4 <= length T)
  /\ blocksb [0; 1; 2; 3] iota4 = true.
Proof.
  split.
  - intros T HT Hblk.
    destruct (le_lt_dec 4 (length T)) as [Hge | Hlt]; [exact Hge | exfalso].
    pose proof (proj1 (forallb_forall _ _) iota4_trace_certificate T HT) as Hcheck.
    cbv beta in Hcheck.
    assert (Hle : Nat.leb (length T) 4 = true) by (apply Nat.leb_le; lia).
    rewrite Hblk, Hle in Hcheck; simpl in Hcheck.
    apply Bool.andb_true_iff in Hcheck as [Hlen4 _].
    apply Nat.eqb_eq in Hlen4; lia.
  - vm_compute; reflexivity.
Qed.

(** ** Maximal is not maximum

    The theorem above closes one route to the record. It must not be read
    as saying that route was the only one, and the way to stop that
    reading is a witness rather than a caveat.

    The **Fano plane** — seven lines on seven points, the cyclic
    difference set [{0,1,3}] and its translates — is intersecting, and
    every 3-set meeting all seven lines *is* one of them, so it is
    maximal in exactly the sense proved above. It has seven members.
    [Intersecting.iota3] is an intersecting 3-uniform family with ten.
    So maximality bounds nothing.

    (The Fano plane is not an [iota] witness: three concurrent lines have
    all three pairwise intersections equal to the common point, so it
    contains seven 3-sunflowers. That is recorded below, because a reader
    who missed it would take this for a claim about [iota(3)].) *)

Definition fano : Family :=
  [[0; 1; 3]; [1; 2; 4]; [2; 3; 5]; [3; 4; 6]; [0; 4; 5]; [1; 5; 6]; [0; 2; 6]].

Lemma fano_uniform : Uniform 3 fano.
Proof. apply uniformb_correct; vm_compute; reflexivity. Qed.

Lemma fano_distinct : Distinct fano.
Proof. apply distinctb_correct; vm_compute; reflexivity. Qed.

Lemma fano_intersecting : Intersecting fano.
Proof. apply intersectingb_correct; vm_compute; reflexivity. Qed.

Lemma fano_grounded : Grounded fano (seq 0 7).
Proof.
  unfold Grounded.
  apply (proj1 (groundedb_correct fano (seq 0 7))).
  vm_compute; reflexivity.
Qed.

Lemma fano_trace_certificate : trace_certificate 3 fano (seq 0 7) = true.
Proof. vm_compute; reflexivity. Qed.

Theorem fano_is_maximal_intersecting : MaximalIntersecting 3 fano.
Proof.
  apply (maximal_of_trace_certificate 3 fano (seq 0 7)).
  - exact (seq_NoDup 7 0).
  - exact fano_grounded.
  - exact fano_trace_certificate.
Qed.

(** And it does contain a sunflower, so it is not an [iota] witness. *)

Lemma fano_has_a_sunflower : ContainsKSunflower 3 fano.
Proof. apply sunflower3b_complete; vm_compute; reflexivity. Qed.

Theorem maximality_is_not_a_size_bound :
  MaximalIntersecting 3 fano /\ length fano = 7
  /\ Uniform 3 iota3 /\ Distinct iota3 /\ Intersecting iota3
  /\ length iota3 = 10
  /\ 7 < 10.
Proof.
  split; [exact fano_is_maximal_intersecting|].
  split; [vm_compute; lia|].
  split; [exact iota3_uniform|].
  split; [exact iota3_distinct|].
  split; [exact iota3_intersecting|].
  split; [vm_compute; lia | lia].
Qed.

(** ** Why prescribed symmetry does not transfer

    The campaign's second half was Kramer–Mesner: prescribe a group [G]
    on the ground set and search the [G]-orbits, which is how record
    designs are found. It returns nothing, and not because the search is
    weak — because **no orbit is usable**. Over more than a hundred
    (ground, group) pairs at [b = 3, 4, 5] and grounds 11 to 22,
    [rust/examples/kramer_mesner.rs] finds *zero* orbits that are
    internally consistent.

    The reason is structural and is worth a theorem rather than a
    remark. A [G]-invariant family is a union of [G]-orbits, so every
    orbit must itself be sunflower-free — and if [G] is transitive on the
    ground set then an orbit is **point-regular**, every point lying in
    the same number of members. Regularity plus intersecting-ness forces
    the ground set to be small:

    >  a regular intersecting [b]-uniform family lives on at most [b^2]
    >  points.

    Two consequences. It is why the prescribed-group search finds nothing
    above [g = b^2] — at [b = 3] that is nine points, and the search
    starts at sixteen. And it is a sharpening of
    [Product.the_universal_iota_ground_reading_is_false]: the cone of the
    tree-path family needs [2^b - 1] points, which is far past [b^2], so
    it *must* be irregular — and it is, the apex having degree [|F|]
    while every other point has less. The universal ground reading fails
    only on irregular families.

    Compare [docs/roadmap.md] §7, which measured that the extremal [iota]
    families **are** regular wherever the link bound is tight. Those live
    at [(b,g) = (2,3), (3,6), (4,8), (4,9)] — all comfortably inside
    [b^2]. *)

Lemma degsum_regular :
  forall U F d,
    (forall x, In x U -> length (filter (fun A => memb x A) F) = d) ->
    degsum U F = length U * d.
Proof.
  induction U as [|x U' IH]; intros F d Hreg; [reflexivity|].
  rewrite degsum_cons_point, (Hreg x (or_introl eq_refl)).
  rewrite (IH F d (fun y Hy => Hreg y (or_intror Hy))).
  simpl; lia.
Qed.

Theorem regular_intersecting_ground_bound :
  forall b (F : Family) (U : list nat) (d : nat),
    1 <= b -> F <> [] ->
    NoDup U -> Uniform b F -> Intersecting F -> Grounded F U ->
    (forall x, In x U -> length (filter (fun A => memb x A) F) = d) ->
    length U <= b * b.
Proof.
  intros b F U d Hb Hne HndU HU HI Hgr Hreg.
  assert (HexA : exists A0, In A0 F).
  { destruct F as [|A0 F']; [contradiction | exists A0; left; reflexivity]. }
  destruct HexA as [A0 HA0].
  assert (HlenA0 : length A0 = b) by (eapply Uniform_length; [exact HU | exact HA0]).
  (* [A0] has [b >= 1] points, and any one of them gives [1 <= d]. *)
  assert (Hx0 : exists x0, In x0 A0).
  { destruct A0 as [|x0 A0']; [simpl in HlenA0; lia | exists x0; left; reflexivity]. }
  destruct Hx0 as [x0 Hx0A0].
  assert (Hx0U : In x0 U) by exact (Hgr A0 HA0 x0 Hx0A0).
  assert (Hd1 : 1 <= d).
  { rewrite <- (Hreg x0 Hx0U).
    assert (Hin : In A0 (filter (fun A => memb x0 A) F)).
    { apply filter_In; split; [exact HA0 | apply memb_true_iff; exact Hx0A0]. }
    destruct (filter (fun A => memb x0 A) F); [inversion Hin | simpl; lia]. }
  (* Every member meets [A0], so pigeonhole over the [b] points of [A0]. *)
  assert (Hmeet : forall A, In A F -> exists x, In x A /\ In x A0).
  { intros A HA.
    destruct (disjointb A A0) eqn:E.
    - exfalso; apply (HI A A0 HA HA0), disjointb_correct; exact E.
    - apply disjointb_false_iff in E as [x [HxA HxA0]]; exists x; tauto. }
  assert (Hsize : length F <= b * d).
  { destruct (le_lt_dec (length F) (b * d)) as [Hle | Hlt]; [exact Hle | exfalso].
    destruct (pigeonhole_family F A0 d Hmeet ltac:(rewrite HlenA0; lia))
      as [x [HxA0 Hdeg]].
    assert (HxU : In x U) by exact (Hgr A0 HA0 x HxA0).
    rewrite (Hreg x HxU) in Hdeg; lia. }
  (* Count incidences both ways. *)
  pose proof (degsum_eq_sizesum U F) as Hcount.
  rewrite (degsum_regular U F d Hreg) in Hcount.
  rewrite (sizesum_uniform b U F HndU HU Hgr) in Hcount.
  nia.
Qed.
