(** * SpreadRestrictions.v -- Which restrictions of the spread lemma have
    content, and which are illusions.

    The spread lemma is the one axiom here, and its threshold carries a
    [log n] that is the whole barrier. A natural hope is that the
    families the sunflower recursion actually feeds it are special, so
    that a spread lemma *restricted to that class* could beat [log n]
    without any improvement to the general lemma. This file settles two
    such hopes in opposite directions.

    ** The link restriction is vacuous

    [SpreadReduction.spread_reduction] walks down a chain of links:
    when [F] is not [r]-spread it recurses into [link T F]. So the
    families reaching the spread lemma are iterated links of the
    original. If that class were narrow, a spread lemma for it would be
    a weaker statement and possibly an easier one.

    It is not narrow. It is everything:
    [every_uniform_family_is_a_link] builds, for any uniform distinct
    [G] and any [d], a uniform distinct [F] of uniformity [d + j] with
    [link Y F = G] *on the nose* — take [Y] to be [d] points above [G]'s
    ground set and glue. Iterating gives every depth. So restricting the
    spread hypothesis to links restricts nothing at all, which is
    [link_restriction_is_vacuous]: the restricted hypothesis implies the
    unrestricted one.

    ** The sunflower-free restriction has content, and is enough

    The other reading of "the recursion's families are special" does
    survive, and it is the useful one. Run the reduction contrapositively
    — bound sunflower-free families rather than force sunflowers into
    large ones — and every family reaching the spread lemma is
    *sunflower-free*, because [Spread.link_sunflower_lift] says links of
    sunflower-free families are sunflower-free.

    So [spread_reduction] can be run from a strictly weaker hypothesis:

    >  a sunflower-free [r]-spread [m]-uniform family has at most
    >  [r ^ m] members

    ([SpreadBoundsSunflowerFree]) rather than

    >  every [r]-spread [m]-uniform family with more than [r ^ m]
    >  members has [k] pairwise disjoint members

    ([SpreadReduction.SpreadYieldsDisjoint]). The first is implied by the
    second ([syd_implies_sunflower_free_bound]) and yields the same
    bound on the extremal function ([sunflower_free_bounded]), so it is
    the weaker interface for any future proof of Rao's Lemma 2 — the
    development assumes less by asking for it.

    The two are not obviously equivalent, and no claim is made that they
    are. [SpreadYieldsDisjoint] asserts something about every spread
    family; the restricted form asserts something only about the
    sunflower-free ones, which is all the reduction ever looks at.

    ** A constructivity note

    [sunflower_free_bounded] is the contrapositive of
    [UpperBound m k (S (r ^ m))], and the two are *not* interchangeable
    here: recovering the [UpperBound] form needs [ContainsKSunflower] to
    be decidable, and this development does not prove that. What is
    proved instead is the [LowerBound]-complement form
    ([no_lower_bound_above]), which is the same extremal statement and
    is constructive. [SpreadReduction.spread_reduction] delivers the
    [UpperBound] form because it *constructs* the sunflower; the price
    of the weaker hypothesis is that the conclusion is the bound rather
    than the witness.

    Zero axioms, zero admits. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower LowerBound ProductLowerBound
     Spread SpreadReduction DirectSum.
Import ListNotations.

(** ** Fresh points above a family's ground set *)

Definition ground_max (G : Family) : nat := fold_right max 0 (concat G).

Lemma le_ground_max :
  forall G A x, In A G -> In x A -> x <= ground_max G.
Proof.
  intros G A x HA Hx; unfold ground_max.
  assert (Hc : In x (concat G))
    by (apply in_concat; exists A; split; assumption).
  clear HA Hx.
  induction (concat G) as [|y l IH]; simpl in Hc |- *; [contradiction|].
  destruct Hc as [E | Hc]; [subst y; lia|].
  specialize (IH Hc); lia.
Qed.

(** [d] consecutive points starting one above everything [G] uses. *)

Definition fresh_block (G : Family) (d : nat) : list nat :=
  block (S (ground_max G)) d.

Lemma fresh_block_length : forall G d, length (fresh_block G d) = d.
Proof. intros G d; apply block_length. Qed.

Lemma fresh_block_NoDup : forall G d, NoDup (fresh_block G d).
Proof. intros G d; apply block_NoDup. Qed.

Lemma fresh_block_disjoint :
  forall G d A, In A G -> Disjoint (fresh_block G d) A.
Proof.
  intros G d A HA x Hy Hx.
  unfold fresh_block in Hy; apply in_block_iff in Hy.
  pose proof (le_ground_max G A x HA Hx). lia.
Qed.

(** ** Every uniform family is a link

    The witness is one application of the direct sum: glue a single
    fresh [d]-set onto every member. Taking that [d]-set as the core
    recovers [G] exactly — not up to set-equality, literally. *)

Definition lift_to_link (G : Family) (d : nat) : Family :=
  sum_family [fresh_block G d] G.

Lemma filter_none :
  forall (p : nat -> bool) (l : list nat),
    (forall x, In x l -> p x = false) -> filter p l = [].
Proof.
  intros p l; induction l as [|y l IH]; simpl; intros H; [reflexivity|].
  rewrite (H y (or_introl eq_refl)).
  apply IH; intros x Hx; apply H; right; exact Hx.
Qed.

Lemma filter_all :
  forall (X : Type) (p : X -> bool) (l : list X),
    (forall x, In x l -> p x = true) -> filter p l = l.
Proof.
  intros X p l; induction l as [|y l IH]; simpl; intros H; [reflexivity|].
  rewrite (H y (or_introl eq_refl)); f_equal.
  apply IH; intros x Hx; apply H; right; exact Hx.
Qed.

Lemma filter_id_of_none :
  forall (p : nat -> bool) (l : list nat),
    (forall x, In x l -> p x = true) -> filter p l = l.
Proof. intros p l; apply (filter_all nat p l). Qed.

Lemma setminus_app_fresh :
  forall Y B, Disjoint Y B -> setminus (Y ++ B) Y = B.
Proof.
  intros Y B Hdis; unfold setminus; rewrite filter_app.
  rewrite (filter_none (fun x => negb (memb x Y)) Y).
  - simpl. apply filter_id_of_none; intros x Hx.
    apply Bool.negb_true_iff, memb_false_iff.
    intro HxY; exact (Hdis x HxY Hx).
  - intros x Hx. apply Bool.negb_false_iff, memb_true_iff; exact Hx.
Qed.

Lemma lift_to_link_shape :
  forall G d, lift_to_link G d = map (fun B => fresh_block G d ++ B) G.
Proof.
  intros G d; unfold lift_to_link, sum_family; simpl.
  rewrite app_nil_r; reflexivity.
Qed.

Theorem every_uniform_family_is_a_link :
  forall j d (G : Family),
    Uniform j G -> Distinct G ->
    link (fresh_block G d) (lift_to_link G d) = G
    /\ Uniform (d + j) (lift_to_link G d)
    /\ Distinct (lift_to_link G d)
    /\ length (fresh_block G d) = d
    /\ NoDup (fresh_block G d).
Proof.
  intros j d G HU HD.
  assert (HYnd : NoDup (fresh_block G d)) by apply fresh_block_NoDup.
  assert (HYlen : length (fresh_block G d) = d) by apply fresh_block_length.
  assert (Hcross : CrossDisjoint [fresh_block G d] G).
  { intros A B HA HB.
    destruct HA as [E | []]; subst A.
    apply fresh_block_disjoint; exact HB. }
  assert (HUY : Uniform d [fresh_block G d]).
  { apply Forall_forall; intros A HA.
    destruct HA as [E | []]; subst A; split; assumption. }
  assert (HDY : Distinct [fresh_block G d])
    by (constructor; [intros B [] | constructor]).
  split; [| split; [| split; [| split]]].
  - (* the link recovers [G] on the nose, not merely up to set-equality *)
    unfold link; rewrite lift_to_link_shape.
    rewrite (filter_all (list nat) (containsb (fresh_block G d))
               (map (fun B => fresh_block G d ++ B) G)).
    + rewrite map_map.
      transitivity (map (fun x : list nat => x) G); [| apply map_id].
      apply map_ext_in; intros B HB.
      apply setminus_app_fresh, fresh_block_disjoint; exact HB.
    + intros A HA; apply in_map_iff in HA as [B [E _]]; subst A.
      apply containsb_true_iff; intros x Hx; apply in_or_app; left; exact Hx.
  - exact (sum_family_Uniform d j [fresh_block G d] G HUY HU Hcross).
  - exact (sum_family_Distinct d j [fresh_block G d] G HUY HU HDY HD Hcross).
  - exact HYlen.
  - exact HYnd.
Qed.

(** Sunflower-freeness transfers, so the lift is not a family the
    recursion could never produce: *every sunflower-free uniform family
    is the link of a sunflower-free uniform family*, at every larger
    uniformity. Stated as preservation rather than as an equivalence
    because the equivalence is what needs classical logic and this does
    not — see the constructivity note at the head of the file. *)

Theorem every_sunflower_free_family_is_a_link :
  forall k j d (G : Family),
    2 <= k -> Uniform j G -> Distinct G -> ~ ContainsKSunflower k G ->
    Uniform (d + j) (lift_to_link G d)
    /\ Distinct (lift_to_link G d)
    /\ ~ ContainsKSunflower k (lift_to_link G d)
    /\ link (fresh_block G d) (lift_to_link G d) = G.
Proof.
  intros k j d G Hk HU HD Hno.
  destruct (every_uniform_family_is_a_link j d G HU HD)
    as [Hlink [HUF [HDF [HYlen HYnd]]]].
  assert (HUY : Uniform d [fresh_block G d]).
  { apply Forall_forall; intros A HA.
    destruct HA as [E | []]; subst A; split; assumption. }
  assert (Hcross : CrossDisjoint [fresh_block G d] G).
  { intros A B HA HB.
    destruct HA as [E | []]; subst A.
    apply fresh_block_disjoint; exact HB. }
  split; [exact HUF | split; [exact HDF | split; [| exact Hlink]]].
  unfold lift_to_link.
  apply (sum_family_no_sunflower d k [fresh_block G d] G Hk HUY);
    [ apply no_k_sunflower_short_family; simpl; lia
    | exact Hno
    | exact Hcross ].
Qed.

(** The converse direction, which is the one [spread_reduction] uses:
    a sunflower in the link is a sunflower upstairs. Free, from
    [Spread.link_sunflower_lift] and the fact that [G] literally *is*
    the link. *)

Corollary lift_reflects_sunflowers :
  forall k j d (G : Family),
    Uniform j G -> Distinct G ->
    ContainsKSunflower k G -> ContainsKSunflower k (lift_to_link G d).
Proof.
  intros k j d G HU HD Hc.
  destruct (every_uniform_family_is_a_link j d G HU HD) as [Hlink _].
  rewrite <- Hlink in Hc.
  exact (@link_sunflower_lift (fresh_block G d) (lift_to_link G d) k Hc).
Qed.

(** ** The link restriction is vacuous

    The spread hypothesis, weakened to apply only to families that arise
    as links. Every uniform distinct family does
    ([every_uniform_family_is_a_link] at [d = 1]), so the weakening is
    not a weakening. *)

Definition IsLink (m : nat) (F : Family) : Prop :=
  exists d Y F0,
    1 <= d /\ NoDup Y /\ length Y = d /\
    Uniform (d + m) F0 /\ Distinct F0 /\ link Y F0 = F.

Definition SpreadYieldsDisjointOnLinks (n k r : nat) : Prop :=
  forall (m : nat) (F : Family),
    1 <= m -> m <= n ->
    Uniform m F -> Distinct F ->
    IsLink m F ->
    r ^ m < length F ->
    RaoSpread m F r ->
    exists S : list (list nat),
      incl S F /\ NoDup S /\ length S = k /\ PairwiseDisjoint S.

Theorem every_uniform_family_IsLink :
  forall m F, Uniform m F -> Distinct F -> IsLink m F.
Proof.
  intros m F HU HD.
  destruct (every_uniform_family_is_a_link m 1 F HU HD)
    as [Hlink [HUF [HDF [HYlen HYnd]]]].
  exists 1, (fresh_block F 1), (lift_to_link F 1).
  repeat split; try assumption; lia.
Qed.

Theorem link_restriction_is_vacuous :
  forall n k r,
    SpreadYieldsDisjointOnLinks n k r -> SpreadYieldsDisjoint n k r.
Proof.
  intros n k r H m F H1 H2 HU HD Hsize Hsp.
  apply (H m F H1 H2 HU HD (every_uniform_family_IsLink m F HU HD) Hsize Hsp).
Qed.

(** ** The sunflower-free restriction

    What the reduction actually needs. *)

Definition SpreadBoundsSunflowerFree (n k r : nat) : Prop :=
  forall (m : nat) (F : Family),
    1 <= m -> m <= n ->
    Uniform m F -> Distinct F ->
    ~ ContainsKSunflower k F ->
    RaoSpread m F r ->
    length F <= r ^ m.

Theorem syd_implies_sunflower_free_bound :
  forall n k r,
    2 <= k -> SpreadYieldsDisjoint n k r -> SpreadBoundsSunflowerFree n k r.
Proof.
  intros n k r Hk Hsyd m F H1 H2 HU HD Hno Hsp.
  destruct (le_lt_dec (length F) (r ^ m)) as [Hle | Hlt]; [exact Hle|].
  exfalso.
  destruct (Hsyd m F H1 H2 HU HD Hlt Hsp) as [S [Hincl [Hnd [Hlen Hpd]]]].
  apply Hno.
  exact (ContainsKSunflower_of_incl Hincl Hlen
           (pairwise_disjoint_sunflower Hnd Hpd)).
Qed.

(** The reduction, run from the weaker hypothesis. Every family the
    induction reaches is a link of a sunflower-free family, hence
    sunflower-free, which is exactly the extra hypothesis
    [SpreadBoundsSunflowerFree] carries. *)

Theorem sunflower_free_bounded :
  forall n k r,
    2 <= k -> 1 <= r ->
    SpreadBoundsSunflowerFree n k r ->
    forall m F, m <= n ->
      Uniform m F -> Distinct F -> ~ ContainsKSunflower k F ->
      length F <= r ^ m.
Proof.
  intros n k r Hk Hr Hbound m.
  induction m as [m IH] using lt_wf_ind.
  intros F Hmn HU HD Hno.
  destruct m as [|m'].
  - (* 0-uniform: every member is empty, so a distinct family has at
       most one member. *)
    simpl.
    destruct F as [|A [|B F'']]; simpl; [lia | lia |].
    exfalso.
    unfold Uniform in HU.
    inversion HU as [|? ? HUA HU']; subst.
    inversion HU' as [|? ? HUB HU'']; subst.
    destruct HUA as [HAlen _]; destruct HUB as [HBlen _].
    destruct A as [|a A0]; [|simpl in HAlen; lia].
    destruct B as [|b B0]; [|simpl in HBlen; lia].
    inversion HD as [|? ? Hni _]; subst.
    apply (Hni [] (or_introl eq_refl)); apply SetEq_refl.
  - destruct (rao_witness (S m') F r) as [T|] eqn:Ewit.
    + (* Not spread: the link is a smaller sunflower-free family that the
         induction hypothesis bounds, contradicting the violation. *)
      exfalso.
      apply rao_witness_some in Ewit as [Hcand [Hne Hviol]].
      destruct (@in_cands_inv F T Hcand) as [A [HAF HTsub]].
      assert (HAnd : NoDup A).
      { unfold Uniform in HU; rewrite Forall_forall in HU.
        destruct (HU A HAF) as [_ Hnd]; exact Hnd. }
      assert (HAlen : length A = S m').
      { unfold Uniform in HU; rewrite Forall_forall in HU.
        destruct (HU A HAF) as [Hl _]; exact Hl. }
      assert (HTnd : NoDup T) by (apply (@subsets_NoDup A T HAnd HTsub)).
      assert (HTA : Subset T A) by (apply (@subsets_incl A T HTsub)).
      assert (HTlen : length T <= S m').
      { rewrite <- HAlen. apply NoDup_incl_length; assumption. }
      assert (HTpos : 1 <= length T).
      { destruct T as [|t T0]; [contradiction | simpl; lia]. }
      assert (Hlt : S m' - length T < S m') by lia.
      assert (Hle : S m' - length T <= n) by lia.
      assert (Hnolink : ~ ContainsKSunflower k (link T F))
        by (intro Hc; apply Hno; exact (@link_sunflower_lift T F k Hc)).
      pose proof (IH (S m' - length T) Hlt (link T F) Hle
                    (@link_uniform (S m') T F HU HTnd) (@link_distinct T F HD) Hnolink) as Hb.
      rewrite length_link in Hb. lia.
    + (* Spread: the restricted hypothesis applies, because [F] is
         sunflower-free by assumption. *)
      assert (HFnd : Forall (fun A : list nat => NoDup A) F).
      { unfold Uniform in HU. apply Forall_forall; intros A HA.
        rewrite Forall_forall in HU; destruct (HU A HA) as [_ Hnd]; exact Hnd. }
      assert (Hsp : RaoSpread (S m') F r)
        by (apply (@rao_witness_none (S m') F r HFnd Ewit)).
      exact (Hbound (S m') F (le_n_S _ _ (Nat.le_0_l _)) Hmn HU HD Hno Hsp).
Qed.

(** The same statement as a bound on the extremal function, in the
    [LowerBound]-complement form that needs no decidability. *)

Corollary no_lower_bound_above :
  forall n k r,
    2 <= k -> 1 <= r ->
    SpreadBoundsSunflowerFree n k r ->
    forall m j, m <= n -> r ^ m < j -> ~ LowerBound m k j.
Proof.
  intros n k r Hk Hr Hbound m j Hmn Hj [F [HU [HD [Hlen Hno]]]].
  pose proof (sunflower_free_bounded n k r Hk Hr Hbound m F Hmn HU HD Hno).
  lia.
Qed.
