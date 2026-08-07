(** * CrossIntersecting.v -- the two-point-cover case at every uniformity.

    `docs/roadmap.md` §24.10 proves the star extremal among 3-uniform
    intersecting Rao-spread families of covering number at most 2, once
    [r >= 4 = m + 1], and §25.4 gives the same statement for every [m] at
    the same threshold — in prose, naming two Coq pieces as missing. This
    file supplies both and proves it.

<<
      G  m-uniform, intersecting, RaoSpread r, tau(G) <= 2, r >= m+1
        =>  |G| <= r^(m-1),  the size of a star.
>>

    ** The shape of the argument

    Against a two-point cover [{p,q}] the family splits into the members
    through [p] but not [q], the mirror, and the members through both.
    The last is capped by the pair degree at [r^(m-2)] at once. The tails
    of the other two — the [m-1] points other than the cover point — are
    families [A] and [B] at uniformity [u = m-1] that

      - satisfy Rao's condition at uniformity [u] with the *same* [r],
        because [deg_A(T) = deg_G({p} u T) <= r^(m-1-|T|)];
      - are **cross-intersecting**: a member of one meets a member of the
        other, and not at [p] or [q].

    So everything reduces to a statement about a cross-intersecting pair,
    and the threshold [m+1] is where that statement turns over:

<<
      |A| + |B| <= (r-1)·r^(u-1)      whenever r >= u + 2.
>>

    ** The two bounds, and the covering number that chooses between them

    Write [a] for the covering number of [A] — the least size of a set
    meeting every member. Any member of [B] meets every member of [A], so
    it *is* a cover, and [a <= u]. Two bounds are then available:

      - the **cover bound** [|A| <= a·r^(u-1)]: sum the point degrees over
        a minimum cover;
      - the **greedy bound** [|B| <= u^a·r^(u-a)]: build a decision tree.
        Pick [C1] in [A]; every member of [B] holds one of its [u] points.
        A set of size [j < a] is not a cover of [A], so some member of [A]
        misses it and the tree extends. After [a] steps every member of
        [B] contains one of at most [u^a] specific [a]-sets, each of degree
        at most [r^(u-a)].

    and the same with the roles swapped. That is [greedy_keys] and
    [extend_keys] below — the first of the two pieces §25.4 named.

    Taking [a <= b] and writing [s = a-1], either of

<<
      (O1)  a·r^(u-1) + u^a·r^(u-a)  <= (r-1)·r^(u-1)   iff  u^(s+1) <= (r-2-s)·r^s
      (O2)         2·u^a·r^(u-a)     <= (r-1)·r^(u-1)   iff 2·u^(s+1) <= (r-1)·r^s
>>

    finishes, and every [s] satisfies one: (O1) when [2s <= u], (O2) when
    [u <= 2s], both from one integer Bernoulli inequality. At [s = 0] —
    [A] a star — (O1) reads [u <= r-2], which is [r >= m+1] exactly, so
    the threshold is not an artefact of the argument. It is where the
    star case turns over.

    ** The second missing piece

    Choosing [a] needs "either some [j]-set covers [A], or every set of
    size at most [j] misses a member", constructively. [covers_at_most]
    makes it a finite search: a cover point lying in no member is useless,
    so the candidates can be taken from [concat A], which is exactly the
    device [TwoCover.covers_dec_search] uses at [j = 2]. [least_true] then
    picks the least [j] that works. *)

From Coq Require Import List Arith Lia.
From Coq Require Import PeanoNat.
From Sunflower Require Import Sets Sunflower Pigeonhole Spread SpreadReduction
     DirectSum Reflect SpreadThreshold TwoCover TauThree.
Import ListNotations.

Set Implicit Arguments.

(** ** Bernoulli, in the integer form both options need

    [(u+2)^(t+1) >= u^t · (u + 2(t+1))]. Everything numeric below is this
    one inequality read twice. *)

Lemma bernoulli_shift :
  forall u t, u ^ t * (u + 2 * S t) <= (u + 2) ^ (S t).
Proof.
  intros u t; induction t as [|t IH].
  - simpl; lia.
  - assert (Hp : (u + 2) ^ (S (S t)) = (u + 2) ^ (S t) * (u + 2))
      by (simpl; ring).
    assert (Hq : u ^ (S t) = u ^ t * u) by (simpl; ring).
    rewrite Hp, Hq.
    apply Nat.le_trans with (u ^ t * (u + 2 * S t) * (u + 2)).
    + generalize (u ^ t); intros X; nia.
    + apply Nat.mul_le_mono_r; exact IH.
Qed.

(** *** (O1): the cover bound plus the greedy bound, when [2s <= u] *)

Lemma option_one :
  forall u s, 2 * s <= u -> u ^ (S s) <= (u - s) * (u + 2) ^ s.
Proof.
  intros u s H; destruct s as [|s'].
  - simpl; lia.
  - pose proof (bernoulli_shift u s') as B.
    assert (Hkey : u * u <= (u - S s') * (u + 2 * S s')) by nia.
    assert (Hpow : u ^ (S (S s')) = u ^ s' * (u * u)) by (simpl; ring).
    rewrite Hpow.
    eapply Nat.le_trans.
    + apply Nat.mul_le_mono_l with (p := u ^ s'); exact Hkey.
    + rewrite Nat.mul_assoc, (Nat.mul_comm (u ^ s')).
      rewrite <- Nat.mul_assoc.
      apply Nat.mul_le_mono_l; exact B.
Qed.

(** *** (O2): the greedy bound on both, when [u <= 2s] *)

Lemma option_two :
  forall u s, u <= 2 * s -> 2 * u ^ (S s) <= (u + 1) * (u + 2) ^ s.
Proof.
  intros u s H; destruct s as [|s'].
  - assert (u = 0) by lia; subst; simpl; lia.
  - pose proof (bernoulli_shift u s') as B.
    assert (Hge : 2 * u ^ (S s') <= (u + 2) ^ (S s')).
    { eapply Nat.le_trans; [| exact B].
      assert (Hp : u ^ (S s') = u ^ s' * u) by (simpl; ring).
      rewrite Hp; generalize (u ^ s'); intros X; nia. }
    assert (Hp2 : u ^ (S (S s')) = u ^ (S s') * u) by (simpl; ring).
    rewrite Hp2.
    eapply Nat.le_trans with ((u + 1) * (2 * u ^ (S s'))).
    + generalize (u ^ (S s')); intros X; nia.
    + apply Nat.mul_le_mono_l; exact Hge.
Qed.

(** *** Both, at any [r] above the threshold *)

Lemma option_one_r :
  forall u r s, 2 * s <= u -> u + 2 <= r ->
    u ^ (S s) <= (r - 2 - s) * r ^ s.
Proof.
  intros u r s H1 H2.
  eapply Nat.le_trans; [apply option_one; exact H1|].
  apply Nat.mul_le_mono; [lia | apply Nat.pow_le_mono_l; lia].
Qed.

Lemma option_two_r :
  forall u r s, u <= 2 * s -> u + 2 <= r ->
    2 * u ^ (S s) <= (r - 1) * r ^ s.
Proof.
  intros u r s H1 H2.
  eapply Nat.le_trans; [apply option_two; exact H1|].
  apply Nat.mul_le_mono; [lia | apply Nat.pow_le_mono_l; lia].
Qed.

(** ** The budget: one of the two routes always fits

    This is the whole numeric content, stated in the form the
    combinatorics will hand it: with [a] the covering number of the
    smaller side, either the cover-plus-greedy sum fits, or twice the
    greedy bound does. *)

Theorem budget_split :
  forall u r a,
    1 <= a -> a <= u -> u + 2 <= r ->
    a * r ^ (u - 1) + u ^ a * r ^ (u - a) <= (r - 1) * r ^ (u - 1)
    \/ 2 * (u ^ a * r ^ (u - a)) <= (r - 1) * r ^ (u - 1).
Proof.
  intros u r a Ha1 Hau Hr.
  assert (Hs : a = S (a - 1)) by lia.
  assert (Hsplit : r ^ (u - 1) = r ^ (a - 1) * r ^ (u - a)).
  { rewrite <- Nat.pow_add_r; f_equal; lia. }
  destruct (le_lt_dec (2 * (a - 1)) u) as [Hle|Hgt].
  - left.
    pose proof (@option_one_r u r (a - 1) Hle Hr) as O1.
    rewrite <- Hs in O1.
    assert (Hc : r - 2 - (a - 1) = r - 1 - a) by lia.
    rewrite Hc in O1.
    assert (Har : a <= r - 1) by lia.
    rewrite Hsplit.
    set (X := r ^ (a - 1)) in *; set (Y := r ^ (u - a)) in *.
    generalize dependent (u ^ a); intros Z HZ.
    nia.
  - right.
    pose proof (@option_two_r u r (a - 1) ltac:(lia) Hr) as O2.
    rewrite <- Hs in O2.
    rewrite Hsplit.
    set (X := r ^ (a - 1)) in *; set (Y := r ^ (u - a)) in *.
    generalize dependent (u ^ a); intros Z HZ.
    nia.
Qed.

(** ** The covering-number decision, as a finite search

    A cover point lying in no member is useless, so the candidates can be
    taken from [concat A] — the device [TwoCover.covers_dec_search] uses
    at [j = 2], here for every [j]. *)

Definition coversb (S : list nat) (A : Family) : bool :=
  forallb (fun C => existsb (fun w => memb w C) S) A.

Definition covers_at_most (A : Family) (j : nat) : bool :=
  existsb (fun S => andb (Nat.leb (length S) j) (coversb S A))
          (subsets (nodup Nat.eq_dec (concat A))).

Lemma forallb_false_exists :
  forall {X : Type} (f : X -> bool) (l : list X),
    forallb f l = false -> exists a, In a l /\ f a = false.
Proof.
  intros X f l; induction l as [|a l IH]; simpl; [discriminate|].
  destruct (f a) eqn:E; simpl; intros H.
  - destruct (IH H) as [b [Hb Hf]]; exists b; split; [right|]; assumption.
  - exists a; split; [left; reflexivity | exact E].
Qed.

Lemma coversb_true_spec :
  forall S A, coversb S A = true ->
    forall C, In C A -> exists w, In w S /\ In w C.
Proof.
  intros S A H C HC; unfold coversb in H.
  rewrite forallb_forall in H; specialize (H C HC).
  apply existsb_exists in H as [w [HwS Hm]].
  exists w; split; [exact HwS | apply memb_true_iff; exact Hm].
Qed.

Lemma coversb_false_spec :
  forall S A, coversb S A = false ->
    exists C, In C A /\ (forall w, In w S -> ~ In w C).
Proof.
  intros S A H; unfold coversb in H.
  apply forallb_false_exists in H as [C [HC Hf]].
  exists C; split; [exact HC|].
  intros w HwS Hin.
  assert (Hex : existsb (fun w => memb w C) S = true)
    by (apply existsb_exists; exists w; split;
        [exact HwS | apply memb_true_iff; exact Hin]).
  congruence.
Qed.

(** If the search fails at [j], then *no* set of size at most [j] covers
    [A] — not merely no sublist of the candidate list. *)

Lemma no_small_cover :
  forall (A : Family) j,
    covers_at_most A j = false ->
    forall S, length S <= j -> exists C, In C A /\ (forall w, In w S -> ~ In w C).
Proof.
  intros A j Hfalse S Hlen.
  set (U := nodup Nat.eq_dec (concat A)).
  set (T := filter (fun x => memb x S) U).
  assert (HTsub : In T (subsets U)) by apply filter_in_subsets.
  assert (HTnd : NoDup T)
    by (apply NoDup_filter; apply NoDup_nodup).
  assert (HTincl : incl T S).
  { intros x Hx; apply filter_In in Hx as [_ Hm]; apply memb_true_iff; exact Hm. }
  assert (HTlen : length T <= j)
    by (eapply Nat.le_trans; [apply (NoDup_incl_length HTnd HTincl) | exact Hlen]).
  pose proof (existsb_false_forall _ _ _ Hfalse T HTsub) as E.
  apply Bool.andb_false_iff in E as [E|E].
  { exfalso; apply Nat.leb_nle in E; lia. }
  destruct (coversb_false_spec _ _ E) as [C [HC Hmiss]].
  exists C; split; [exact HC|].
  intros w HwS Hin.
  apply (Hmiss w); [| exact Hin].
  apply filter_In; split.
  - unfold U; apply nodup_In, (proj2 (in_concat A w)); exists C; tauto.
  - apply memb_true_iff; exact HwS.
Qed.

Lemma small_cover_of :
  forall (A : Family) j,
    covers_at_most A j = true ->
    exists S, length S <= j /\ (forall C, In C A -> exists w, In w S /\ In w C).
Proof.
  intros A j H; apply existsb_exists in H as [S [_ Hb]].
  apply Bool.andb_true_iff in Hb as [Hl Hc].
  exists S; split; [apply Nat.leb_le; exact Hl | apply coversb_true_spec; exact Hc].
Qed.

(** A member of a cross-intersecting partner is itself a cover, so the
    search succeeds at [u]; and it fails at 0 as soon as [A] is nonempty. *)

Lemma covers_at_most_top :
  forall (A B : Family) (u : nat),
    Uniform u B -> B <> [] ->
    (forall e f, In e A -> In f B -> exists w, In w e /\ In w f) ->
    covers_at_most A u = true.
Proof.
  intros A B u HUB Hne Hcross.
  destruct (covers_at_most A u) eqn:E; [reflexivity | exfalso].
  assert (Hex : exists f, In f B)
    by (destruct B as [|f B0]; [contradiction | exists f; left; reflexivity]).
  destruct Hex as [f HfB].
  destruct (@uniform_mem u B f HUB HfB) as [Hlf _].
  destruct (@no_small_cover A u E f ltac:(lia)) as [C [HC Hmiss]].
  destruct (Hcross C f HC HfB) as [w [HwC Hwf]].
  apply (Hmiss w Hwf HwC).
Qed.

Lemma covers_at_most_zero :
  forall (A : Family), A <> [] -> covers_at_most A 0 = false.
Proof.
  intros A Hne.
  destruct (covers_at_most A 0) eqn:E; [exfalso | reflexivity].
  destruct (small_cover_of _ _ E) as [S [Hlen Hcov]].
  destruct A as [|C A0]; [contradiction|].
  destruct (Hcov C (or_introl eq_refl)) as [w [HwS _]].
  destruct S; [contradiction | simpl in Hlen; lia].
Qed.

(** The least [j] at which a decidable predicate turns on. *)

Lemma least_true :
  forall (f : nat -> bool) n,
    f n = true -> f 0 = false ->
    exists a, 1 <= a /\ a <= n /\ f a = true /\ f (a - 1) = false.
Proof.
  intros f n; induction n as [|n IH]; intros Hn H0; [congruence|].
  destruct (f n) eqn:En.
  - destruct (IH eq_refl H0) as [a [H1 [H2 [H3 H4]]]].
    exists a; repeat split; try assumption; lia.
  - exists (S n); repeat split; try assumption; [lia | lia |].
    replace (S n - 1) with n by lia; exact En.
Qed.

(** ** The greedy decision tree

    [extend_keys] is the step: for each key [S], name a member of [A]
    missing it and branch on that member's [u] points. Every member of [B]
    that contained [S] now contains one of the extensions, because it
    meets that member of [A] and the meeting point is outside [S]. *)

Lemma extend_keys :
  forall (A B : Family) (u : nat) (Ks : list (list nat)),
    Uniform u A ->
    (forall e f, In e A -> In f B -> exists w, In w e /\ In w f) ->
    (forall S, In S Ks -> exists C, In C A /\ (forall w, In w S -> ~ In w C)) ->
    exists Ks',
      length Ks' <= u * length Ks
      /\ (forall S', In S' Ks' -> exists w S, In S Ks /\ ~ In w S /\ S' = w :: S)
      /\ (forall f, In f B -> forall S, In S Ks -> Subset S f ->
            exists S', In S' Ks' /\ Subset S' f).
Proof.
  intros A B u Ks HUA Hcross; induction Ks as [|S0 Ks IH]; intros Hwit.
  - exists []; split; [simpl; lia | split].
    + intros S' [].
    + intros f _ S [].
  - destruct (Hwit S0 (or_introl eq_refl)) as [C [HCA HCmiss]].
    destruct (IH ltac:(intros S HS; apply Hwit; right; exact HS))
      as [Ks0' [Hlen [Hshape Hcov]]].
    destruct (@uniform_mem u A C HUA HCA) as [HlC _].
    exists (map (fun w => w :: S0) C ++ Ks0'); split; [| split].
    + rewrite app_length, map_length, HlC; simpl; lia.
    + intros S' HS'; apply in_app_or in HS' as [HS'|HS'].
      * apply in_map_iff in HS' as [w [Ew HwC]].
        exists w, S0; split; [left; reflexivity | split].
        -- intros Hin; exact (HCmiss w Hin HwC).
        -- symmetry; exact Ew.
      * destruct (Hshape S' HS') as [w [S [HS [Hnw Ew]]]].
        exists w, S; split; [right; exact HS | split; assumption].
    + intros f HfB S HS Hsub; destruct HS as [ES|HS].
      * subst S.
        destruct (Hcross C f HCA HfB) as [w [HwC Hwf]].
        exists (w :: S0); split.
        -- apply in_or_app; left; apply in_map_iff; exists w; split;
             [reflexivity | exact HwC].
        -- intros y [Ey|Hy]; [subst y; exact Hwf | apply Hsub; exact Hy].
      * destruct (Hcov f HfB S HS Hsub) as [S' [HS' Hsub']].
        exists S'; split; [apply in_or_app; right; exact HS' | exact Hsub'].
Qed.

Lemma greedy_keys :
  forall j (A B : Family) (u : nat),
    Uniform u A ->
    (forall e f, In e A -> In f B -> exists w, In w e /\ In w f) ->
    (forall S, length S < j -> exists C, In C A /\ (forall w, In w S -> ~ In w C)) ->
    exists Ks,
      length Ks <= u ^ j
      /\ (forall S, In S Ks -> length S = j /\ NoDup S)
      /\ (forall f, In f B -> exists S, In S Ks /\ Subset S f).
Proof.
  induction j as [|j IH]; intros A B u HUA Hcross Hwit.
  - exists [[]]; split; [simpl; lia | split].
    + intros S [ES|[]]; subst S; split; [reflexivity | constructor].
    + intros f HfB; exists []; split; [left; reflexivity | intros y []].
  - destruct (IH A B u HUA Hcross ltac:(intros S HS; apply Hwit; lia))
      as [Ks [HlenK [HshapeK HcovK]]].
    destruct (@extend_keys A B u Ks HUA Hcross
                ltac:(intros S HS; destruct (HshapeK S HS) as [Hl _];
                      apply Hwit; lia))
      as [Ks' [Hlen' [Hshape' Hcov']]].
    exists Ks'; split; [| split].
    + eapply Nat.le_trans; [exact Hlen'|].
      simpl; apply Nat.mul_le_mono_l; exact HlenK.
    + intros S' HS'; destruct (Hshape' S' HS') as [w [S [HS [Hnw Ew]]]].
      destruct (HshapeK S HS) as [Hl Hnd]; subst S'.
      split; [simpl; lia | constructor; assumption].
    + intros f HfB; destruct (HcovK f HfB) as [S [HS Hsub]].
      destruct (Hcov' f HfB S HS Hsub) as [S' [HS' Hsub']].
      exists S'; split; assumption.
Qed.

(** ** The two bounds *)

Lemma greedy_bound :
  forall j (A B : Family) (u r : nat),
    1 <= j ->
    Uniform u A -> RaoSpread u B r ->
    (forall e f, In e A -> In f B -> exists w, In w e /\ In w f) ->
    (forall S, length S < j -> exists C, In C A /\ (forall w, In w S -> ~ In w C)) ->
    length B <= u ^ j * r ^ (u - j).
Proof.
  intros j A B u r Hj HUA HRB Hcross Hwit.
  destruct (@greedy_keys j A B u HUA Hcross Hwit) as [Ks [Hlen [Hshape Hcov]]].
  assert (Hb : length B <= length Ks * r ^ (u - j)).
  { apply cover_by_sets.
    - intros f HfB; destruct (Hcov f HfB) as [S [HS Hsub]]; exists S; split; assumption.
    - intros S HS; destruct (Hshape S HS) as [Hl Hnd].
      specialize (HRB S Hnd
        ltac:(destruct S; [simpl in Hl; lia | discriminate])).
      rewrite Hl in HRB; exact HRB. }
  eapply Nat.le_trans; [exact Hb | apply Nat.mul_le_mono_r; exact Hlen].
Qed.

Lemma cover_size_bound :
  forall (A : Family) (u r a : nat) (S : list nat),
    RaoSpread u A r ->
    (forall C, In C A -> exists w, In w S /\ In w C) ->
    length S <= a ->
    length A <= a * r ^ (u - 1).
Proof.
  intros A u r a S HR Hcov Hlen.
  assert (Hb : length A <= length S * r ^ (u - 1)).
  { apply cover_by_points;
      [exact Hcov | intros x _; eapply rao_point; exact HR]. }
  eapply Nat.le_trans; [exact Hb | apply Nat.mul_le_mono_r; exact Hlen].
Qed.

Lemma greedy_mono :
  forall u r a b, a <= b -> b <= u -> u <= r ->
    u ^ b * r ^ (u - b) <= u ^ a * r ^ (u - a).
Proof.
  intros u r a b Hab Hbu Hur.
  assert (Eb : u ^ b = u ^ a * u ^ (b - a))
    by (rewrite <- Nat.pow_add_r; f_equal; lia).
  assert (Er : r ^ (u - a) = r ^ (b - a) * r ^ (u - b))
    by (rewrite <- Nat.pow_add_r; f_equal; lia).
  rewrite Eb, Er, <- Nat.mul_assoc.
  apply Nat.mul_le_mono_l, Nat.mul_le_mono_r, Nat.pow_le_mono_l; exact Hur.
Qed.

(** ** The cross-intersecting pair, with the covering numbers ordered *)

Lemma cross_pair_ordered :
  forall u r (A B : Family) a b,
    1 <= u -> u + 2 <= r ->
    Uniform u A -> Uniform u B ->
    RaoSpread u A r -> RaoSpread u B r ->
    (forall e f, In e A -> In f B -> exists w, In w e /\ In w f) ->
    1 <= a -> a <= u -> 1 <= b -> b <= u -> a <= b ->
    covers_at_most A a = true ->
    covers_at_most A (a - 1) = false ->
    covers_at_most B (b - 1) = false ->
    length A + length B <= (r - 1) * r ^ (u - 1).
Proof.
  intros u r A B a b Hu Hr HUA HUB HRA HRB Hcross Ha1 Hau Hb1 Hbu Hab HcA HcA' HcB'.
  assert (Hflip : forall e f, In e B -> In f A -> exists w, In w e /\ In w f).
  { intros e f He Hf; destruct (Hcross f e Hf He) as [w [H1 H2]];
      exists w; split; assumption. }
  destruct (small_cover_of _ _ HcA) as [S [HSlen HScov]].
  assert (HA1 : length A <= a * r ^ (u - 1))
    by (apply (@cover_size_bound A u r a S HRA HScov HSlen)).
  assert (HB1 : length B <= u ^ a * r ^ (u - a)).
  { apply (@greedy_bound a A B u r Ha1 HUA HRB Hcross).
    intros T HT; apply (@no_small_cover A (a - 1) HcA'); lia. }
  assert (HA2 : length A <= u ^ b * r ^ (u - b)).
  { apply (@greedy_bound b B A u r Hb1 HUB HRA Hflip).
    intros T HT; apply (@no_small_cover B (b - 1) HcB'); lia. }
  assert (HA3 : length A <= u ^ a * r ^ (u - a))
    by (eapply Nat.le_trans; [exact HA2 | apply greedy_mono; lia]).
  destruct (@budget_split u r a Ha1 Hau Hr) as [O1|O2]; lia.
Qed.

(** > **The cross-intersecting bound.** Two nonempty cross-intersecting
    > families at uniformity [u], each satisfying Rao's condition with the
    > same [r >= u + 2], have at most [(r-1)·r^(u-1)] members between them. *)

Theorem cross_pair_bound :
  forall u r (A B : Family),
    1 <= u -> u + 2 <= r ->
    Uniform u A -> Uniform u B ->
    RaoSpread u A r -> RaoSpread u B r ->
    (forall e f, In e A -> In f B -> exists w, In w e /\ In w f) ->
    A <> [] -> B <> [] ->
    length A + length B <= (r - 1) * r ^ (u - 1).
Proof.
  intros u r A B Hu Hr HUA HUB HRA HRB Hcross HAne HBne.
  assert (Hflip : forall e f, In e B -> In f A -> exists w, In w e /\ In w f).
  { intros e f He Hf; destruct (Hcross f e Hf He) as [w [H1 H2]];
      exists w; split; assumption. }
  assert (HtopA : covers_at_most A u = true)
    by (apply (@covers_at_most_top A B u HUB HBne Hcross)).
  assert (HtopB : covers_at_most B u = true)
    by (apply (@covers_at_most_top B A u HUA HAne Hflip)).
  destruct (@least_true (covers_at_most A) u HtopA (covers_at_most_zero HAne))
    as [a [Ha1 [Hau [HcA HcA']]]].
  destruct (@least_true (covers_at_most B) u HtopB (covers_at_most_zero HBne))
    as [b [Hb1 [Hbu [HcB HcB']]]].
  destruct (le_lt_dec a b) as [Hab|Hba].
  - exact (@cross_pair_ordered u r A B a b Hu Hr HUA HUB HRA HRB Hcross
             Ha1 Hau Hb1 Hbu Hab HcA HcA' HcB').
  - pose proof (@cross_pair_ordered u r B A b a Hu Hr HUB HUA HRB HRA Hflip
                  Hb1 Hbu Ha1 Hau ltac:(lia) HcB HcB' HcA') as H; lia.
Qed.

(** ** The tails of a piece are a Rao-spread family one uniformity down *)

Lemma tail_uniform_rao :
  forall m r (G H : Family) (x : nat),
    1 <= m ->
    Uniform m G -> RaoSpread m G r ->
    (forall T, deg T H <= deg T G) ->
    (forall C, In C H -> In C G /\ In x C) ->
    Uniform (m - 1) (map (rem x) H) /\ RaoSpread (m - 1) (map (rem x) H) r.
Proof.
  intros m r G H x Hm HU HR Hsub Hmem; split.
  - apply Forall_forall; intros e He.
    apply in_map_iff in He as [C [Ec HC]].
    destruct (Hmem C HC) as [HCG HxC].
    destruct (@uniform_mem m G C HU HCG) as [Hl Hnd].
    subst e; unfold UniformSet; split;
      [pose proof (@rem_length x C Hnd HxC); lia | apply rem_nodup; exact Hnd].
  - intros T Hnd Hne; unfold deg; rewrite length_filter_map.
    destruct (in_dec Nat.eq_dec x T) as [HxT|HxT].
    + assert (Hz : forall C, containsb T (rem x C) = false).
      { intros C; destruct (containsb T (rem x C)) eqn:E; [|reflexivity].
        exfalso; apply containsb_true_iff in E.
        assert (Hin : In x (rem x C)) by (apply E; exact HxT).
        apply in_rem in Hin as [_ Hne']; apply Hne'; reflexivity. }
      rewrite (filter_ext_eq _ (fun _ => false) H (fun C => Hz C)).
      assert (Hnil : forall (l : Family), filter (fun _ => false) l = [])
        by (induction l; simpl; [reflexivity | assumption]).
      rewrite Hnil; simpl; lia.
    + eapply Nat.le_trans.
      * apply (@filter_length_mono _ _ (containsb (x :: T))).
        intros C HC Hc; apply containsb_true_iff in Hc.
        destruct (Hmem C HC) as [_ HxC].
        apply containsb_true_iff; intros y [Ey|Hy].
        -- subst y; exact HxC.
        -- assert (Hin : In y (rem x C)) by (apply Hc; exact Hy).
           apply in_rem in Hin; tauto.
      * eapply Nat.le_trans; [apply (Hsub (x :: T))|].
        specialize (HR (x :: T) ltac:(constructor; assumption) ltac:(discriminate)).
        simpl in HR |- *.
        replace (m - 1 - length T) with (m - S (length T)) by lia.
        exact HR.
Qed.

(** ** The theorem

    §24.10 at [m = 3] is the [m = 3] instance of this. *)

Theorem two_cover_star_extremal :
  forall m r (G : Family) p q,
    1 <= m -> m + 1 <= r ->
    Uniform m G -> RaoSpread m G r ->
    (forall C D, In C G -> In D G -> exists x, In x C /\ In x D) ->
    (forall C, In C G -> In p C \/ In q C) ->
    length G <= r ^ (m - 1).
Proof.
  intros m r G p q Hm Hr HU HR Hint Hcov.
  (* a single point covering the family is immediate from the point cap *)
  assert (Hstar : forall w, (forall C, In C G -> In w C) -> length G <= r ^ (m - 1)).
  { intros w Hw.
    assert (Hb : length G <= length [w] * r ^ (m - 1)).
    { apply cover_by_points;
        [intros C HC; exists w; split; [left; reflexivity | apply Hw; exact HC]
        | intros y _; eapply rao_point; exact HR]. }
    simpl in Hb; lia. }
  destruct (Nat.eq_dec m 1) as [E1|Hm2].
  { subst m; simpl.
    destruct G as [|C G0] eqn:EG; [simpl; lia | rewrite <- EG in *].
    assert (HC : In C G) by (rewrite EG; left; reflexivity).
    destruct (@uniform_mem 1 G C HU HC) as [Hl _].
    destruct C as [|x [|? ?]]; simpl in Hl; try discriminate.
    apply Hstar with (w := x); intros D HD.
    destruct (Hint D [x] HD HC) as [z [HzD [Ez|[]]]]; subst z; exact HzD. }
  assert (Hm2' : 2 <= m) by lia.
  destruct (Nat.eq_dec p q) as [Epq|Hpq].
  { subst q; apply Hstar with (w := p); intros C HC;
      destruct (Hcov C HC); assumption. }
  pose (Gq' := filter (fun C => memb q C) G).
  pose (Gp := filter (fun C => negb (memb q C)) G).
  pose (Gpq := filter (fun C => memb p C) Gq').
  pose (Gq := filter (fun C => negb (memb p C)) Gq').
  assert (EGq' : Gq' = filter (fun C => memb q C) G) by reflexivity.
  assert (EGp : Gp = filter (fun C => negb (memb q C)) G) by reflexivity.
  assert (EGpq : Gpq = filter (fun C => memb p C) Gq') by reflexivity.
  assert (EGq : Gq = filter (fun C => negb (memb p C)) Gq') by reflexivity.
  assert (E1 : length G = length Gq' + length Gp)
    by (rewrite EGq', EGp; apply length_filter_partition).
  assert (E2 : length Gq' = length Gpq + length Gq)
    by (rewrite EGpq, EGq; apply length_filter_partition).
  (* memberships *)
  assert (HmemP : forall C, In C Gp -> In C G /\ In p C /\ ~ In q C).
  { intros C HC; rewrite EGp in HC; apply filter_In in HC as [HCG Hnq].
    apply Bool.negb_true_iff in Hnq.
    assert (Hq : ~ In q C) by (intros Hin; apply memb_true_iff in Hin; congruence).
    repeat split; try assumption.
    destruct (Hcov C HCG); [assumption | contradiction]. }
  assert (HmemQ : forall C, In C Gq -> In C G /\ In q C /\ ~ In p C).
  { intros C HC; rewrite EGq in HC; apply filter_In in HC as [HC' Hnp].
    rewrite EGq' in HC'; apply filter_In in HC' as [HCG Hq].
    apply Bool.negb_true_iff in Hnp.
    repeat split;
      [exact HCG | apply memb_true_iff; exact Hq
       | intros Hin; apply memb_true_iff in Hin; congruence]. }
  (* the both-points piece is capped by the pair degree *)
  assert (Hpair : length Gpq <= r ^ (m - 2)).
  { eapply Nat.le_trans.
    - rewrite EGpq, EGq'.
      apply (@filter_length_mono _ (fun C => memb p C)
               (fun C => containsb [p; q] C) (filter (fun C => memb q C) G)).
      intros C HC Hp; apply filter_In in HC as [_ Hq].
      apply containsb_true_iff; intros y [Ey|[Ey|[]]]; subst y;
        apply memb_true_iff; assumption.
    - eapply Nat.le_trans; [apply deg_filter_le|].
      specialize (HR [p; q] (pair_nodup Hpq) ltac:(discriminate)); simpl in HR.
      exact HR. }
  (* if either side is empty the family is a star *)
  destruct (list_eq_dec (list_eq_dec Nat.eq_dec) Gp []) as [HpE|HpNE].
  { apply Hstar with (w := q); intros C HC.
    destruct (in_dec Nat.eq_dec q C) as [Hq|Hq]; [exact Hq | exfalso].
    assert (HCp : In C Gp)
      by (rewrite EGp; apply filter_In; split;
          [exact HC | apply Bool.negb_true_iff;
                      destruct (memb q C) eqn:Em;
                      [exfalso; apply Hq, memb_true_iff; exact Em | reflexivity]]).
    rewrite HpE in HCp; exact HCp. }
  destruct (list_eq_dec (list_eq_dec Nat.eq_dec) Gq []) as [HqE|HqNE].
  { apply Hstar with (w := p); intros C HC.
    destruct (in_dec Nat.eq_dec p C) as [Hp|Hp]; [exact Hp | exfalso].
    assert (Hq : In q C) by (destruct (Hcov C HC); [contradiction | assumption]).
    assert (HCq' : In C Gq')
      by (rewrite EGq'; apply filter_In; split;
          [exact HC | apply memb_true_iff; exact Hq]).
    assert (HCq : In C Gq)
      by (rewrite EGq; apply filter_In; split;
          [exact HCq' | apply Bool.negb_true_iff;
                        destruct (memb p C) eqn:Em;
                        [exfalso; apply Hp, memb_true_iff; exact Em | reflexivity]]).
    rewrite HqE in HCq; exact HCq. }
  (* degrees only drop under filtering *)
  assert (HdP : forall T, deg T Gp <= deg T G)
    by (intros T; rewrite EGp; apply deg_filter_le).
  assert (HdQ : forall T, deg T Gq <= deg T G).
  { intros T; rewrite EGq, EGq'.
    eapply Nat.le_trans; [apply deg_filter_le | apply deg_filter_le]. }
  (* the tails *)
  destruct (@tail_uniform_rao m r G Gp p ltac:(lia) HU HR HdP
              ltac:(intros C HC; destruct (HmemP C HC) as [? [? ?]]; split; assumption))
    as [HUA HRA].
  destruct (@tail_uniform_rao m r G Gq q ltac:(lia) HU HR HdQ
              ltac:(intros C HC; destruct (HmemQ C HC) as [? [? ?]]; split; assumption))
    as [HUB HRB].
  assert (Hcross : forall e f, In e (map (rem p) Gp) -> In f (map (rem q) Gq) ->
                     exists w, In w e /\ In w f).
  { intros e f He Hf.
    apply in_map_iff in He as [C [Ec HC]].
    apply in_map_iff in Hf as [D [Ed HD]].
    destruct (HmemP C HC) as [HCG [HpC HqC]].
    destruct (HmemQ D HD) as [HDG [HqD HpD]].
    destruct (Hint C D HCG HDG) as [w [HwC HwD]].
    exists w; subst e f; split; apply in_rem; split; try assumption.
    - intros Ew; subst w; contradiction.
    - intros Ew; subst w; contradiction. }
  assert (Hne : forall (x : nat) (H : Family), H <> [] -> map (rem x) H <> [])
    by (intros x H HH; destruct H; [contradiction | simpl; discriminate]).
  pose proof (@cross_pair_bound (m - 1) r (map (rem p) Gp) (map (rem q) Gq)
                ltac:(lia) ltac:(lia) HUA HUB HRA HRB Hcross
                (Hne p Gp HpNE) (Hne q Gq HqNE)) as Hsum.
  rewrite !map_length in Hsum.
  assert (Esplit : r ^ (m - 1) = (r - 1) * r ^ (m - 1 - 1) + r ^ (m - 2)).
  { replace (m - 1 - 1) with (m - 2) by lia.
    assert (Hp1 : r ^ (m - 1) = r * r ^ (m - 2)).
    { rewrite <- (Nat.pow_succ_r' r (m - 2)); f_equal; lia. }
    rewrite Hp1; assert (1 <= r) by lia; nia. }
  lia.
Qed.

(** ** What is left, at every uniformity

    [StarExtremalAt m r] — [I(m,r) <= r^(m-1)], the star extremal — splits
    by covering number. [tau = 1] is a star and immediate; [tau = 2] is
    the theorem above, for every [m], at [r >= m+1]. What remains is
    [tau >= 3], and this is that statement with the constant left open,
    exactly as [TwoCover.TauThreeAtMost] does at [m = 3].

    Note the [Distinct] hypothesis. §25.1 records what its absence cost
    once already; here it is free, because [rao_uniform_distinct] supplies
    it from the Rao condition the consumer carries. *)

Definition TauThreePieceAtMost (m r K : nat) : Prop :=
  forall (G : Family),
    Uniform m G -> RaoSpread m G r -> Distinct G ->
    (forall C D, In C G -> In D G -> exists x, In x C /\ In x D) ->
    (forall p q, exists C, In C G /\ ~ In p C /\ ~ In q C) ->
    length G <= K.

Theorem star_extremal_from_tau_three :
  forall m r K,
    1 <= m -> m + 1 <= r -> K <= r ^ (m - 1) ->
    TauThreePieceAtMost m r K -> StarExtremalAt m r.
Proof.
  intros m r K Hm Hr HK Htau G HU HR Hint.
  destruct (covers_at_most G 2) eqn:E.
  - destruct (small_cover_of _ _ E) as [S [Hlen Hcov]].
    destruct S as [|x [|y S']]; simpl in Hlen; try lia.
    + destruct G as [|C G0]; [simpl; apply Nat.le_0_l|].
      destruct (Hcov C (or_introl eq_refl)) as [w [[] _]].
    + apply (@two_cover_star_extremal m r G x x Hm Hr HU HR Hint).
      intros C HC; destruct (Hcov C HC) as [w [[Ew|[]] HwC]]; subst w; left; exact HwC.
    + assert (ES : S' = [])
        by (destruct S'; [reflexivity | simpl in Hlen; lia]).
      subst S'.
      apply (@two_cover_star_extremal m r G x y Hm Hr HU HR Hint).
      intros C HC; destruct (Hcov C HC) as [w [[Ew|[Ew|[]]] HwC]];
        [subst w; left; exact HwC | subst w; right; exact HwC].
  - eapply Nat.le_trans; [| exact HK].
    apply Htau; try assumption.
    + apply (@rao_uniform_distinct m r G Hm HU HR).
    + intros p q.
      destruct (@no_small_cover G 2 E [p; q] ltac:(simpl; lia)) as [C [HC Hmiss]].
      exists C; repeat split;
        [exact HC | apply Hmiss; left; reflexivity
         | apply Hmiss; right; left; reflexivity].
Qed.

(** At [m = 3] with [K = 16] this is [TauThree.three_uniform_star_extremal],
    so the general form subsumes the row §25.3 closed. *)

Corollary three_uniform_star_extremal_again :
  forall r, 4 <= r -> StarExtremalAt 3 r.
Proof.
  intros r Hr.
  apply (@star_extremal_from_tau_three 3 r 16); [lia | lia | simpl; nia |].
  intros G HU HR HD Hint Htau; exact (@tau_three_bound G HU HD Hint Htau).
Qed.

(** And the next open row, stated so the remaining gap is one number:
    at [m = 4] the star is extremal from [r = 5] on as soon as a 4-uniform
    intersecting family of covering number at least 3 has at most 125
    members. The elementary greedy bound [m^t * r^(m-t)] is [4^3 * 5 = 320]
    at covering number 3, so the interval to close is [[125, 320]]. *)

Corollary four_uniform_star_extremal_from_tau_three :
  forall r, 5 <= r -> TauThreePieceAtMost 4 r (r ^ 3) -> StarExtremalAt 4 r.
Proof.
  intros r Hr Htau.
  apply (@star_extremal_from_tau_three 4 r (r ^ 3)); [lia | lia | simpl; lia | exact Htau].
Qed.

(** ** The first general answer: the star is extremal once [r >= m^(3/2)]

    §24.13 asks whether the star is extremal for intersecting families
    under Rao's condition once [r >= m+1]. §26.1 settles the [tau <= 2]
    part of it at every uniformity. For [tau >= 3] the greedy tree gives
    [|G| <= m^t·r^(m-t)] with [t = tau(G)], and that beats the star
    [r^(m-1)] exactly when [m^t <= r^(t-1)]. Over [t] in [3..m] the binding
    case is [t = 3], so **[m^3 <= r^2] closes every covering number at
    once** -- and with [r >= m+1] for the two smaller ones, the whole
    question is settled for [r] above [m^(3/2)].

    This is weaker than [r >= m+1] as a threshold, and it does not improve
    any bound on [r*]: feeding it into [star_extremal_gives_m_plus_one]
    would need [(n+1)^2 >= n^3]. What it is, is the first statement of the
    form "[I(m,r) = r^(m-1)]" that holds at *every* uniformity. *)

Lemma covers_at_most_of_cover :
  forall (A : Family) j S,
    length S <= j -> (forall C, In C A -> exists w, In w S /\ In w C) ->
    covers_at_most A j = true.
Proof.
  intros A j S Hlen Hcov.
  destruct (covers_at_most A j) eqn:E; [reflexivity | exfalso].
  destruct (@no_small_cover A j E S Hlen) as [C [HC Hmiss]].
  destruct (Hcov C HC) as [w [HwS HwC]].
  exact (Hmiss w HwS HwC).
Qed.

Lemma pow_cube_step :
  forall m r t, 1 <= m -> 3 <= t -> m ^ 3 <= r ^ 2 -> m ^ t <= r ^ (t - 1).
Proof.
  intros m r t Hm Ht Hc.
  assert (Hr : 1 <= r).
  { destruct r as [|r']; [| lia]; exfalso.
    assert (H1 : 1 <= m ^ 3)
      by (replace 1 with (1 ^ 3) by reflexivity; apply Nat.pow_le_mono_l; lia).
    simpl in Hc; lia. }
  assert (Hsq : m ^ t * m ^ t <= r ^ (t - 1) * r ^ (t - 1)).
  { rewrite <- !Nat.pow_add_r.
    eapply Nat.le_trans with (m ^ (3 * (t - 1))).
    - apply Nat.pow_le_mono_r; lia.
    - rewrite Nat.pow_mul_r.
      eapply Nat.le_trans; [apply Nat.pow_le_mono_l; exact Hc|].
      rewrite <- Nat.pow_mul_r; apply Nat.pow_le_mono_r; lia. }
  generalize dependent (r ^ (t - 1)); generalize dependent (m ^ t).
  intros x y H; nia.
Qed.

Theorem star_extremal_for_large_r :
  forall m r, 1 <= m -> m + 1 <= r -> m ^ 3 <= r ^ 2 -> StarExtremalAt m r.
Proof.
  intros m r Hm Hr Hc G HU HR Hint.
  destruct (covers_at_most G 2) eqn:E2.
  - destruct (small_cover_of _ _ E2) as [S [Hlen Hcov]].
    destruct S as [|x [|y S']]; simpl in Hlen; try lia.
    + destruct G as [|C G0]; [simpl; apply Nat.le_0_l|].
      destruct (Hcov C (or_introl eq_refl)) as [w [[] _]].
    + apply (@two_cover_star_extremal m r G x x Hm Hr HU HR Hint).
      intros C HC; destruct (Hcov C HC) as [w [[Ew|[]] HwC]];
        subst w; left; exact HwC.
    + assert (ES : S' = [])
        by (destruct S'; [reflexivity | simpl in Hlen; lia]).
      subst S'.
      apply (@two_cover_star_extremal m r G x y Hm Hr HU HR Hint).
      intros C HC; destruct (Hcov C HC) as [w [[Ew|[Ew|[]]] HwC]];
        [subst w; left; exact HwC | subst w; right; exact HwC].
  - destruct (list_eq_dec (list_eq_dec Nat.eq_dec) G []) as [HGE|Hne];
      [rewrite HGE; simpl; apply Nat.le_0_l |].
    assert (Htop : covers_at_most G m = true)
      by (apply (@covers_at_most_top G G m HU Hne Hint)).
    destruct (@least_true (covers_at_most G) m Htop (covers_at_most_zero Hne))
      as [t [Ht1 [Htm [Hct Hct']]]].
    assert (Ht3 : 3 <= t).
    { destruct (le_lt_dec t 2) as [Hle|Hgt]; [exfalso | lia].
      destruct (small_cover_of _ _ Hct) as [S [Hlen Hcov]].
      assert (E : covers_at_most G 2 = true)
        by (apply (@covers_at_most_of_cover G 2 S ltac:(lia) Hcov)).
      congruence. }
    assert (Hgb : length G <= m ^ t * r ^ (m - t)).
    { apply (@greedy_bound t G G m r ltac:(lia) HU HR Hint).
      intros T HT; apply (@no_small_cover G (t - 1) Hct'); lia. }
    assert (Hpow : m ^ t <= r ^ (t - 1))
      by (apply pow_cube_step; [lia | exact Ht3 | exact Hc]).
    assert (Hfin : r ^ (t - 1) * r ^ (m - t) = r ^ (m - 1))
      by (rewrite <- Nat.pow_add_r; f_equal; lia).
    eapply Nat.le_trans; [exact Hgb|].
    rewrite <- Hfin; apply Nat.mul_le_mono_r; exact Hpow.
Qed.

(** ** What one bound at [m = 4] would buy

    [SpreadThreshold]'s split leaves [r*(4,3)] at 7. Feeding the four rows
    [m = 1, 2, 3, 4] into [star_extremal_gives_m_plus_one] at [n = 4] would
    put it at 5, and three of those rows are theorems already. The fourth
    is the corollary above, so the whole gap between 7 and 5 is one
    constant: *a 4-uniform intersecting Rao(5)-spread family of covering
    number at least 3 has at most 125 members*. The elementary greedy
    bound [m^t * r^(m-t)] is [4^3 * 5 = 320] at covering number 3 and
    [4^4 = 256] at covering number 4, so the interval to close is
    [[125, 320]]. *)

Theorem r_star_four_at_most_five_from_tau_three :
  TauThreePieceAtMost 4 5 125 -> SpreadYieldsDisjoint 4 3 5.
Proof.
  intros Htau.
  replace 5 with (4 + 1) at 2 by reflexivity.
  apply star_extremal_gives_m_plus_one; [lia|].
  intros m Hm1 Hm4.
  destruct m as [|[|[|[|m']]]]; try lia.
  - apply one_uniform_star_extremal.
  - apply two_uniform_star_extremal; lia.
  - apply three_uniform_star_extremal; lia.
  - assert (m' = 0) by lia; subst m'.
    apply four_uniform_star_extremal_from_tau_three; [lia|].
    replace (5 ^ 3) with 125 by reflexivity; exact Htau.
Qed.

(** ** Why the covering-number-3 piece must carry the Rao condition

    At [m = 3], [TauThree.tau_three_bound] bounds it at 16 with no degree
    cap at all, and the truth is Frankl's 10. At [m = 4] there is no bound
    whatever without one, so the [RaoSpread] hypothesis in
    [TauThreePieceAtMost] is not bookkeeping — it is the difference between
    a finite quantity and an infinite one, and it is why the [m = 3]
    argument does not lift as it stands.

    The witness is [C([5],3)] with one free coordinate attached:

<<
      G_n = { C u {w} : C a 3-subset of {0..4},  w in {5, ..., 7+n} }
>>

    4-uniform, distinct, intersecting because two 3-subsets of a 5-set
    meet, and of covering number at least 3 because two points can neither
    exhaust the 5-set nor the three-or-more values of [w]. Its size is
    [10(n+3)]. Rao's condition would cap [deg({C})] — which is exactly the
    number of values of [w] — at [r^(4-3) = r]. *)

Definition c53 : Family :=
  [[0;1;2];[0;1;3];[0;1;4];[0;2;3];[0;2;4];[0;3;4];
   [1;2;3];[1;2;4];[1;3;4];[2;3;4]].

Definition lift (n : nat) : Family :=
  flat_map (fun w => map (fun C => w :: C) c53) (seq 5 (3 + n)).

Lemma SetNoDup_app :
  forall X Y : Family,
    SetNoDup X -> SetNoDup Y ->
    (forall A B, In A X -> In B Y -> ~ SetEq A B) ->
    SetNoDup (X ++ Y).
Proof.
  induction X as [|A X IH]; simpl; intros Y HX HY Hcross; [exact HY|].
  inversion HX as [|? ? Hni HX']; subst.
  constructor.
  - intros B HB; apply in_app_or in HB as [HB|HB];
      [apply Hni; exact HB | apply Hcross; [left; reflexivity | exact HB]].
  - apply IH; [exact HX' | exact HY |].
    intros A' B' HA' HB'; apply Hcross; [right; exact HA' | exact HB'].
Qed.

Lemma SetNoDup_map :
  forall (f : list nat -> list nat) (l : Family),
    SetNoDup l ->
    (forall A B, In A l -> In B l -> SetEq (f A) (f B) -> SetEq A B) ->
    SetNoDup (map f l).
Proof.
  induction l as [|A l IH]; simpl; intros H Hinj; [constructor|].
  inversion H as [|? ? Hni H']; subst.
  constructor.
  - intros B HB Hseq; apply in_map_iff in HB as [B0 [EB HB0]].
    apply (Hni B0 HB0); apply Hinj;
      [left; reflexivity | right; exact HB0 | rewrite EB; exact Hseq].
  - apply IH; [exact H'|].
    intros A' B' HA' HB'; apply Hinj; right; assumption.
Qed.

Lemma c53_bounded : forall C, In C c53 -> forall x, In x C -> x < 5.
Proof.
  intros C HC x Hx; unfold c53 in HC; simpl in HC.
  repeat (destruct HC as [EC|HC];
          [subst C; destruct Hx as [Ex|[Ex|[Ex|[]]]]; lia |]); contradiction.
Qed.

Lemma c53_setnodup : Distinct c53.
Proof. apply distinctb_correct; vm_compute; reflexivity. Qed.

Lemma c53_uniform : Uniform 3 c53.
Proof. apply uniformb_correct; vm_compute; reflexivity. Qed.

Lemma c53_int :
  forall C D, In C c53 -> In D c53 -> exists x, In x C /\ In x D.
Proof. apply int_b_correct; vm_compute; reflexivity. Qed.

Lemma c53_exists_missing :
  forall a b, a < 6 -> b < 6 ->
    existsb (fun C => andb (negb (memb a C)) (negb (memb b C))) c53 = true.
Proof.
  intros a b Ha Hb.
  do 6 (destruct a as [|a];
        [ do 6 (destruct b as [|b]; [vm_compute; reflexivity|]); exfalso; lia |]);
    exfalso; lia.
Qed.

Lemma c53_memb_min :
  forall p C, In C c53 -> memb p C = memb (Nat.min p 5) C.
Proof.
  intros p C HC; destruct (le_lt_dec 5 p) as [Hle|Hlt].
  - rewrite Nat.min_r by lia.
    assert (E1 : memb p C = false).
    { destruct (memb p C) eqn:E; [|reflexivity].
      exfalso; apply memb_true_iff in E; pose proof (@c53_bounded C HC p E); lia. }
    assert (E2 : memb 5 C = false).
    { destruct (memb 5 C) eqn:E; [|reflexivity].
      exfalso; apply memb_true_iff in E; pose proof (@c53_bounded C HC 5 E); lia. }
    rewrite E1, E2; reflexivity.
  - rewrite Nat.min_l by lia; reflexivity.
Qed.

Lemma c53_tau : forall p q, exists C, In C c53 /\ ~ In p C /\ ~ In q C.
Proof.
  intros p q.
  pose proof (c53_exists_missing (a := Nat.min p 5) (b := Nat.min q 5)
                ltac:(pose proof (Nat.le_min_r p 5); lia)
                ltac:(pose proof (Nat.le_min_r q 5); lia)) as Hex.
  apply existsb_exists in Hex as [C [HC Hcond]].
  apply Bool.andb_true_iff in Hcond as [H1 H2].
  apply Bool.negb_true_iff in H1; apply Bool.negb_true_iff in H2.
  exists C; repeat split; [exact HC | |];
    intros Hin; apply memb_true_iff in Hin;
    rewrite (c53_memb_min _ HC) in Hin; congruence.
Qed.

Lemma in_lift :
  forall n X, In X (lift n) ->
    exists w C, In w (seq 5 (3 + n)) /\ In C c53 /\ X = w :: C.
Proof.
  intros n X HX; unfold lift in HX.
  apply in_flat_map in HX as [w [Hw HX]].
  apply in_map_iff in HX as [C [EC HC]].
  exists w, C; repeat split; [exact Hw | exact HC | symmetry; exact EC].
Qed.

Lemma lift_length : forall n, length (lift n) = 10 * (3 + n).
Proof.
  intros n; unfold lift.
  assert (Hgen : forall W, length (flat_map (fun w => map (fun C => w :: C) c53) W)
                           = 10 * length W).
  { induction W as [|w W IH]; [reflexivity|].
    cbn [flat_map]; rewrite app_length, map_length, IH; cbn [length c53]; lia. }
  rewrite Hgen, seq_length; reflexivity.
Qed.

Lemma lift_uniform : forall n, Uniform 4 (lift n).
Proof.
  intros n; apply Forall_forall; intros X HX.
  destruct (@in_lift n X HX) as [w [C [Hw [HC EX]]]].
  assert (Hw5 : 5 <= w) by (apply in_seq in Hw; lia).
  destruct (@uniform_mem 3 c53 C c53_uniform HC) as [Hl Hnd].
  subst X; unfold UniformSet; split; [simpl; lia|].
  constructor; [| exact Hnd].
  intros Hin; pose proof (@c53_bounded C HC w Hin); lia.
Qed.

Lemma lift_distinct : forall n, Distinct (lift n).
Proof.
  intros n; unfold lift.
  assert (Hgen : forall W, (forall w, In w W -> 5 <= w) -> NoDup W ->
            SetNoDup (flat_map (fun w => map (fun C => w :: C) c53) W)).
  { induction W as [|w W IH]; intros Hge Hnd; [constructor|].
    cbn [flat_map].
    inversion Hnd as [|? ? Hni Hnd']; subst.
    assert (Hw5 : 5 <= w) by (apply Hge; left; reflexivity).
    apply SetNoDup_app.
    - apply SetNoDup_map; [exact c53_setnodup|].
      intros A B HA HB [Hab Hba]; split.
      + intros x Hx.
        assert (Hin : In x (w :: B)) by (apply Hab; right; exact Hx).
        destruct Hin as [Ex|Hx']; [| exact Hx'].
        exfalso; pose proof (@c53_bounded A HA x Hx); lia.
      + intros x Hx.
        assert (Hin : In x (w :: A)) by (apply Hba; right; exact Hx).
        destruct Hin as [Ex|Hx']; [| exact Hx'].
        exfalso; pose proof (@c53_bounded B HB x Hx); lia.
    - apply IH; [intros v Hv; apply Hge; right; exact Hv | exact Hnd'].
    - intros A B HA HB [Hab _].
      apply in_map_iff in HA as [CA [EA HCA]].
      apply in_flat_map in HB as [v [Hv HB]].
      apply in_map_iff in HB as [CB [EB HCB]].
      assert (Hv5 : 5 <= v) by (apply Hge; right; exact Hv).
      assert (Hwv : w <> v) by (intros E; subst v; contradiction).
      assert (Hin : In w B) by (apply Hab; rewrite <- EA; left; reflexivity).
      rewrite <- EB in Hin; destruct Hin as [Ew|Hw'];
        [congruence | pose proof (@c53_bounded CB HCB w Hw'); lia]. }
  apply Hgen.
  - intros w Hw; apply in_seq in Hw; lia.
  - apply seq_NoDup.
Qed.

Lemma lift_int :
  forall n C D, In C (lift n) -> In D (lift n) -> exists x, In x C /\ In x D.
Proof.
  intros n X Y HX HY.
  destruct (@in_lift n X HX) as [w [C [_ [HC EX]]]].
  destruct (@in_lift n Y HY) as [v [D [_ [HD EY]]]].
  destruct (@c53_int C D HC HD) as [x [HxC HxD]].
  exists x; subst X Y; split; right; assumption.
Qed.

Lemma lift_tau :
  forall n p q, exists X, In X (lift n) /\ ~ In p X /\ ~ In q X.
Proof.
  intros n p q.
  destruct (@c53_tau p q) as [C [HC [HpC HqC]]].
  (* three of the values of w are available, and p, q kill at most two *)
  assert (Hw : exists w, In w (seq 5 (3 + n)) /\ w <> p /\ w <> q).
  { assert (H5 : In 5 (seq 5 (3 + n))) by (apply in_seq; lia).
    assert (H6 : In 6 (seq 5 (3 + n))) by (apply in_seq; lia).
    assert (H7 : In 7 (seq 5 (3 + n))) by (apply in_seq; lia).
    destruct (Nat.eq_dec p 5) as [E5|N5]; destruct (Nat.eq_dec q 5) as [F5|G5].
    - exists 6; repeat split; [exact H6 | lia | lia].
    - destruct (Nat.eq_dec q 6) as [F6|G6].
      + exists 7; repeat split; [exact H7 | lia | lia].
      + exists 6; repeat split; [exact H6 | lia | lia].
    - destruct (Nat.eq_dec p 6) as [E6|N6].
      + exists 7; repeat split; [exact H7 | lia | lia].
      + exists 6; repeat split; [exact H6 | lia | lia].
    - exists 5; repeat split; [exact H5 | lia | lia]. }
  destruct Hw as [w [Hw [Hwp Hwq]]].
  exists (w :: C); repeat split.
  - unfold lift; apply in_flat_map; exists w; split;
      [exact Hw | apply in_map_iff; exists C; split; [reflexivity | exact HC]].
  - intros [Ep|Hp]; [congruence | contradiction].
  - intros [Eq|Hq]; [congruence | contradiction].
Qed.

(** > **The negative.** No constant bounds the covering-number-3 piece at
    > uniformity 4 once the Rao condition is dropped — where at uniformity
    > 3 the same quantity is 10. *)

Theorem tau_three_piece_unbounded_at_four :
  forall K, exists G : Family,
    Uniform 4 G /\ Distinct G /\
    (forall C D, In C G -> In D G -> exists x, In x C /\ In x D) /\
    (forall p q, exists C, In C G /\ ~ In p C /\ ~ In q C) /\
    K < length G.
Proof.
  intros K; exists (lift K); repeat split.
  - apply lift_uniform.
  - apply lift_distinct.
  - apply lift_int.
  - apply lift_tau.
  - rewrite lift_length; lia.
Qed.
