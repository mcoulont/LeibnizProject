
From mathcomp Require Import all_ssreflect.
From mathcomp.classical Require Import boolp.
Require Import Relations.Relation_Definitions.
Require Import Classical.
Require Import Logic.IndefiniteDescription.
Require Import Logic.FunctionalExtensionality.
Require Import Logic.PropExtensionality.
Require Import Logic.ProofIrrelevance.
Require Import Logic.ClassicalFacts.
Require Import Sets.Image.
Require Import Arith.Compare_dec.
Require Import FinFun.

Require Import basics.
Require Import relation_facts.
Require Import eqType_facts.
Require Import finType_facts.
Require Import ssrnat_facts.
Require Import preference.
Require Import arrow_theorem.

Section gibbard_theorem.

Context {Outcome: finType}.
Context {Individual : finType}.
Context {Strategies : Individual -> Type}.

Definition StrategyProfile : Type := forall (i : Individual), Strategies i.

Definition GameForm : Type := StrategyProfile -> Outcome.

Definition dominant {k : Individual} (strategy : Strategies k)
(po : PreferenceOrder Outcome) (gf : GameForm) : Prop :=
  forall (sp : StrategyProfile), non_strict po (
    gf (replace sp k strategy)
  ) (gf sp).

Definition straightforward (gf : GameForm) : Prop :=
  forall (po : PreferenceOrder Outcome) (k : Individual),
  exists (strategy : Strategies k),
    dominant strategy po gf.

Definition omnipotent (k : Individual) (gf : GameForm) : Prop :=
  forall (x : Outcome),
  exists (strategy : Strategies k),
  forall (sp : StrategyProfile),
    sp k = strategy -> gf sp = x.

Definition admits_omnipotent (gf : GameForm) : Prop :=
  exists (k : Individual), omnipotent k gf.

Lemma exists_dominant_strategy {gf : GameForm}
(straightforward_gf : straightforward gf) (i : Individual) :
  forall (po : PreferenceOrder Outcome), exists (strategy : Strategies i),
    dominant strategy po gf.
Proof.
  unfold straightforward in straightforward_gf.
  intro.
  apply straightforward_gf.
Qed.

Definition dominant_strategy {gf : GameForm}
(straightforward_gf : straightforward gf) (i : Individual) :
  PreferenceOrder Outcome -> Strategies i.
Proof.
  intro po.
  destruct (constructive_indefinite_description _ (
    exists_dominant_strategy straightforward_gf i po
  )) as [strategy dom].
  exact strategy.
Defined.

Lemma dominant_strategies_well_named
{gf : GameForm} (straightforward_gf : straightforward gf) :
  forall (i : Individual) (po : PreferenceOrder Outcome),
    dominant (
      dominant_strategy straightforward_gf i po
    ) po gf.
Proof.
  intros i. intros po.
  unfold dominant_strategy.
  now destruct constructive_indefinite_description.
Qed.

Definition dominant_strategies_profile
{gf : GameForm} (straightforward_gf : straightforward gf)
(pp : @PreferenceProfile Outcome Individual) : StrategyProfile :=
  fun (i : Individual) => dominant_strategy straightforward_gf i (pp i).

Definition outcome_when_dominant_strategies
{gf : GameForm} (straightforward_gf : straightforward gf)
(pp : @PreferenceProfile Outcome Individual) : Outcome :=
  gf (dominant_strategies_profile straightforward_gf pp).

Definition remove_indifference (po : PreferenceOrder Outcome)
(Z : pred Outcome) : relation Outcome :=
  fun (x : Outcome) => fun (y : Outcome) =>
    if Z x then (
      if Z y then (
        if `[< indifferent po x y >] then (
          enum_rank x >= enum_rank y = true
        ) else non_strict po x y
      ) else True
    ) else (
      if Z y then False else (
        enum_rank x >= enum_rank y
      )
    ).

Definition remove_indifference_profile (pp : @PreferenceProfile Outcome Individual)
(Z : pred Outcome) : Individual -> relation Outcome :=
  fun (i : Individual) => remove_indifference (pp i) Z.

Lemma remove_indifference_is_total_order (po : PreferenceOrder Outcome)
(Z : pred Outcome) :
  total_order (remove_indifference po Z).
Proof.
  unfold remove_indifference. unfold total_order. unfold total.
  split.
  {
    intros.
    destruct (Z x) eqn:Zx.
    {
      destruct (Z y) eqn:Zy.
      {
        destruct (`[< indifferent po x y >]) eqn:Ixy.
        {
          assert (`[< indifferent po y x >]).
          {
            apply asboolT.
            apply indifferent_symmetric.
            apply asboolW. auto.
          }
          rewrite H.
          assert ((enum_rank y <= enum_rank x) || (enum_rank x <= enum_rank y)).
          { apply leq_total. }
          unfold orb in H0.
          destruct (enum_rank y <= enum_rank x) eqn:Exy.
          { tauto. }
          { right. intuition. }
        }
        {
          assert (`[< indifferent po y x >] = false).
          {
            apply asboolF. intro.
            assert (indifferent po x y).
            { apply indifferent_symmetric. exact H. }
            assert (`[< indifferent po x y >]).
            { apply asboolT. exact H0. }
            inversion H1. rewrite Ixy in H3. inversion H3.
          }
          rewrite H.
          destruct po as [R]. destruct p.
          simpl. apply t0.
        }
      }
      { tauto. }
    }
    {
      destruct (Z y) eqn:Zy.
      { tauto. }
      {
        assert ((enum_rank y <= enum_rank x) || (enum_rank x <= enum_rank y)).
        { apply leq_total. }
        unfold orb in H.
        destruct (enum_rank y <= enum_rank x) eqn:Exy.
        { tauto. }
        { right. intuition. }
      }
    }
  }
  {
    split.
    {
      unfold reflexive. intro.
      destruct (Z x) eqn:Zx.
      {
        destruct (`[< indifferent po x x >]).
        {
          assert (enum_rank x <= enum_rank x).
          { auto. }
          auto.
        }
        apply preference_order_reflexive.
        destruct po as [R]. simpl.
        exact p.
      }
      { auto. }
    }
    {
      unfold transitive. intros.
      destruct (Z x) eqn:Zx.
      {
        destruct (Z z) eqn:Zz.
        {
          destruct (`[< indifferent po x z >]) eqn:Ixz.
          {
            destruct (Z y) eqn:Zy.
            {
              destruct (`[< indifferent po x y >]) eqn:Ixy.
              {
                assert (`[< indifferent po y z >]).
                {
                  apply asboolT.
                  apply indifferent_transitive with (y:=x).
                  {
                    apply indifferent_symmetric.
                    apply asboolW. intuition.
                  }
                  { apply asboolW. intuition. }
                }
                rewrite H1 in H0.
                apply leq_trans with (n:=enum_rank y) ; auto.
              }
              {
                assert (~ indifferent po x y).
                { intro. apply asboolT in H1. rewrite Ixy in H1. inversion H1. }
                assert (indifferent po x z).
                { apply asboolW. rewrite Ixz. intuition. }
                assert (~ indifferent po y z).
                {
                  intro. apply H1.
                  assert (indifferent po x y).
                  apply indifferent_transitive with (y:=z).
                  { exact H2. }
                  { apply indifferent_symmetric. exact H3. }
                  { exact H4. }
                }
                assert (`[< indifferent po y z >] = false).
                { apply asboolF. exact H3. }
                rewrite H4 in H0.
                unfold indifferent in H1.
                apply not_and_or in H1. destruct H1.
                {
                  apply NNPP in H1.
                  unfold indifferent in H3.
                  apply not_and_or in H3. destruct H3.
                  {
                    apply NNPP in H3.
                    assert (strict po x z).
                    { apply strict_transitive with (b:=y); try tauto. }
                    unfold indifferent in H2. tauto.
                  }
                  { apply NNPP in H3. unfold strict in H3. tauto. }
                }
                { apply NNPP in H1. unfold strict in H1. tauto. }
              }
            }
            { inversion H0. }
          }
          {
            assert (~ indifferent po x z).
            { intro. apply asboolT in H1. rewrite Ixz in H1. inversion H1. }
            destruct (Z y) eqn:Zy.
            {
              destruct (`[< indifferent po x y >]) eqn:Ixy.
              {
                assert (indifferent po x y).
                { apply asboolW. rewrite Ixy. intuition. }
                assert (`[< indifferent po y z >] = false).
                {
                  apply asboolF.
                  intro.
                  apply H1. apply indifferent_transitive with (y:=y); try tauto.
                }
                rewrite H3 in H0.
                apply non_strict_stable_by_indifferent' with (a:=y) (b:=x) (c:=z).
                { exact H0. }
                { apply indifferent_symmetric. exact H2. }
              }
              assert (~ indifferent po x y).
              { intro. apply asboolT in H2. rewrite Ixy in H2. inversion H2. }
              destruct (`[< indifferent po y z >]) eqn:Iyz.
              {
                assert (indifferent po y z).
                { apply asboolW. rewrite Iyz. intuition. }
                apply non_strict_stable_by_indifferent with (a:=x) (b:=y) (c:=z);
                try tauto.
              }
              { apply non_strict_transitive with (b:=y); try tauto. }
            }
            { inversion H0. }
          }
        }
        { tauto. }
      }
      {
        destruct (Z z) eqn:Zz.
        {
          destruct (Z y) eqn:Zy.
          { inversion H. }
          { inversion H0. }
        }
        {
          destruct (Z y) eqn:Zy.
          { inversion H. }
          { apply leq_trans with (n:=enum_rank y) ; auto. }
        }
      }
    }
    {
      unfold antisymmetric. intros.
      destruct (Z x) eqn:Zx.
      {
        destruct (Z y) eqn:Zy.
        {
          destruct (`[< indifferent po x y >]) eqn:Ixy.
          {
            assert (indifferent po x y).
            { apply asboolW. rewrite Ixy. intuition. }
            assert (`[< indifferent po y x >] = true).
            {
              apply asboolT.
              apply indifferent_symmetric. exact H1.
            }
            rewrite H2 in H0.
            apply enum_rank_inj. apply ord_inj.
            apply anti_leq.
            unfold andb.
            rewrite H0. auto.
          }
          {
            assert (~ indifferent po x y).
            { intro. apply asboolT in H1. rewrite Ixy in H1. inversion H1. }
            assert (`[< indifferent po y x >] = false).
            {
              apply asboolF.
              intro. apply H1. apply indifferent_symmetric. exact H2.
            }
            rewrite H2 in H0.
            unfold indifferent in H1. unfold strict in H1.
            tauto.
          }
        }
        { inversion H0. }
      }
      {
        destruct (Z y) eqn:Zy.
        { inversion H. }
        {
          apply enum_rank_inj. apply ord_inj.
          apply anti_leq.
          unfold andb.
          rewrite H0. auto.
        }
      }
    }
  }
Qed.

Corollary remove_indifference_is_preference_order (po : PreferenceOrder Outcome)
(Z : pred Outcome) :
  preference_order (remove_indifference po Z).
Proof.
  specialize (total_order_is_antisymmetric_preference (remove_indifference po Z)).
  specialize (remove_indifference_is_total_order po Z).
  tauto.
Qed.

Definition remove_indifference_PreferenceOrder (po : PreferenceOrder Outcome)
(Z : pred Outcome) : PreferenceOrder Outcome :=
  exist preference_order (
    remove_indifference po Z
  ) (remove_indifference_is_preference_order po Z).

Lemma remove_indifference_strict_unchanged_on_Z {Z : pred Outcome} {z1 z2 : Outcome}
(po : PreferenceOrder Outcome) (Z1 : Z z1) (Z2 : Z z2) :
  strict po z1 z2 -> strict (remove_indifference_PreferenceOrder po Z) z1 z2.
Proof.
  unfold strict. unfold non_strict.
  simpl.
  unfold remove_indifference.
  rewrite Z1. rewrite Z2.
  apply contra_not. intro.
  destruct (`[< indifferent po z2 z1 >]) eqn:Iz2z1.
  {
    apply asboolW in Iz2z1.
    unfold indifferent in Iz2z1. unfold strict in Iz2z1. unfold non_strict in Iz2z1.
    tauto.
  }
  { unfold non_strict in H. exact H. }
Qed.

Lemma remove_indifference_in_Z_out_Z {Z : pred Outcome} {z1 z2 : Outcome}
(po : PreferenceOrder Outcome) (Z1 : Z z1) (Z2 : ~~ (Z z2)) :
  strict (remove_indifference_PreferenceOrder po Z) z1 z2.
Proof.
  unfold strict. unfold non_strict.
  simpl.
  unfold remove_indifference.
  rewrite Z1. unfold negb in Z2.
  destruct (Z z2).
  { inversion Z2. }
  { tauto. }
Qed.

Definition remove_indifference_PreferenceProfile
(pp : @PreferenceProfile Outcome Individual)
(Z : pred Outcome) : @PreferenceProfile Outcome Individual :=
  fun (i : Individual) => remove_indifference_PreferenceOrder (pp i) Z.

Lemma remove_indifference_well_named (po : PreferenceOrder Outcome)
(Z : pred Outcome) :
  forall (x y : Outcome),
    indifferent (remove_indifference_PreferenceOrder po Z) x y ->
    x = y.
Proof.
  intros.
  unfold remove_indifference_PreferenceOrder in H.
  unfold indifferent in H. unfold strict in H. unfold non_strict in H.
  simpl in H. rewrite notP in H. rewrite notP in H.
  unfold remove_indifference in H. destruct H.
  pose proof (indifferent_symmetric po). unfold symmetric in H1.
  pose proof (H1 y x). specialize (H1 x y).
  assert (indifferent po x y = indifferent po y x).
  { apply propositional_extensionality. tauto. }
  rewrite <- H3 in H.
  destruct (Z x) eqn:Zx.
  {
    destruct (Z y) eqn:Zy.
    {
      destruct (`[< indifferent po x y >]) eqn:indif.
      {
        assert ((enum_rank x <= enum_rank y)%coq_nat).
        { apply le_mathcomp_equivalent. intuition. }
        assert ((enum_rank y <= enum_rank x)%coq_nat).
        { apply le_mathcomp_equivalent. intuition. }
        assert (nat_of_ord (enum_rank x) = nat_of_ord(enum_rank y)).
        { apply Nat.le_antisymm; tauto. }
        apply ord_inj in H6. apply enum_rank_inj. exact H6.
      }
      {
        pose proof (indifferent_if_non_strict_both_ways po x y H0 H).
        exfalso.
        assert (`[< indifferent po x y >] = true).
        { apply asboolT. exact H4. }
        rewrite indif in H5. inversion H5.
      }
    }
    { inversion H. }
  }
  {
    destruct (Z y) eqn:Zy.
    { inversion H0. }
    {
      assert ((enum_rank x <= enum_rank y)%coq_nat).
      { apply le_mathcomp_equivalent. intuition. }
      assert ((enum_rank y <= enum_rank x)%coq_nat).
      { apply le_mathcomp_equivalent. intuition. }
      assert (nat_of_ord (enum_rank x) = nat_of_ord(enum_rank y)).
      { apply Nat.le_antisymm; tauto. }
      apply ord_inj in H6. apply enum_rank_inj. exact H6.
    }
  }
Qed.

Lemma remove_indifference_down_to_littlest_subset {Y Z : pred Outcome}
(po : PreferenceOrder Outcome) (YsubsZ : subpred Y Z) :
  remove_indifference_PreferenceOrder (
    remove_indifference_PreferenceOrder po Z
  ) Y = remove_indifference_PreferenceOrder po Y.
Proof.
  unfold remove_indifference_PreferenceOrder.
  apply subset_eq_compat.
  {
    unfold remove_indifference at 1 3.
    apply functional_extensionality. intro.
    apply functional_extensionality. intro.
    simpl.
    destruct (Y x) eqn:Yx.
    {
      destruct (Y x0) eqn:Yx0.
      {
        destruct (`[< indifferent po x x0 >]) eqn:Ixx0.
        {
          destruct (
            `[< indifferent (
              exist preference_order (
                remove_indifference po Z
              ) (
                remove_indifference_is_preference_order po Z
              )
            ) x x0 >]
          ) eqn:indif.
          { reflexivity. }
          {
            unfold remove_indifference.
            assert (Z x = true).
            { apply YsubsZ. exact Yx. }
            rewrite H.
            assert (Z x0 = true).
            { apply YsubsZ. exact Yx0. }
            rewrite H0.
            rewrite Ixx0.
            reflexivity.
          }
        }
        {
          unfold remove_indifference at 2.
          assert (Z x = true).
          { apply YsubsZ. exact Yx. }
          rewrite H.
          assert (Z x0 = true).
          { apply YsubsZ. exact Yx0. }
          rewrite H0. rewrite Ixx0.
          destruct (
            `[< indifferent (
              exist preference_order (
                remove_indifference po Z
              ) (
                remove_indifference_is_preference_order po Z
              )
            ) x x0 >]
          ) eqn:indif.
          {
            assert (
              indifferent (
                exist preference_order (
                  remove_indifference po Z
                ) (
                  remove_indifference_is_preference_order po Z
                )
              ) x x0
            ).
            { apply asboolW. rewrite indif. intuition. }
            unfold indifferent in H1. unfold strict in H1. unfold non_strict in H1.
            simpl in H1.
            destruct H1. apply NNPP in H1. apply NNPP in H2.
            pose proof (remove_indifference_is_total_order po Z).
            unfold total_order in H3. destruct H3.
            destruct H4.
            assert (x0 = x).
            { apply ord_antisym; try tauto. }
            rewrite H4.
            apply propositional_extensionality.
            assert (non_strict po x x).
            {
              apply preference_order_reflexive.
              destruct po as [R]. simpl. exact p.
            }
            assert (enum_rank x <= enum_rank x).
            { auto. }
            tauto.
          }
          { reflexivity. }
        }
      }
      { reflexivity. }
    }
    { destruct (Y x0) eqn:Yx0; reflexivity. }
  }
Qed.

Lemma remove_indifference_profile_down_to_littlest_subset {Y Z : pred Outcome}
(pp : @PreferenceProfile Outcome Individual) (YsubsZ : subpred Y Z) :
  remove_indifference_PreferenceProfile (
    remove_indifference_PreferenceProfile pp Z
  ) Y = remove_indifference_PreferenceProfile pp Y.
Proof.
  unfold remove_indifference_PreferenceProfile.
  apply functional_extensionality.
  intro.
  apply remove_indifference_down_to_littlest_subset. exact YsubsZ.
Qed.

Definition agree_on (po1 po2 : PreferenceOrder Outcome) (Z : pred Outcome) :
Prop :=
  forall (x y : Outcome),
    (Z x && Z y) ->
    same_order po1 po2 x y.

Definition agree_on_profile (pp1 pp2 : @PreferenceProfile Outcome Individual)
(Z : pred Outcome) : Prop :=
  forall (i : Individual), agree_on (pp1 i) (pp2 i) Z.

Lemma agree_on_implies_remove_indifference_equal
{po1 po2 : PreferenceOrder Outcome} {Z : pred Outcome}
(ago : agree_on po1 po2 Z) :
  remove_indifference_PreferenceOrder po1 Z =
  remove_indifference_PreferenceOrder po2 Z.
Proof.
  apply subset_eq_compat.
  unfold remove_indifference.
  apply functional_extensionality. intro.
  apply functional_extensionality. intro.
  unfold agree_on in ago.
  destruct (Z x) eqn:Zx.
  {
    destruct (Z x0) eqn:Zx0.
    {
      pose proof (ago x x0). rewrite Zx in H. rewrite Zx0 in H.
      simpl in ago.
      assert (true).
      { auto. }
      specialize (H H0).
      unfold same_order in ago. destruct H. destruct H1.
      destruct (`[< indifferent po1 x x0 >]) eqn:Ixx0.
      {
        assert (indifferent po1 x x0).
        { apply asboolW. rewrite Ixx0. intuition. }
        assert (indifferent po2 x x0).
        { rewrite <- H2. exact H3. }
        assert (`[< indifferent po2 x x0 >] = true).
        { apply asboolT. exact H4. }
        rewrite H5. reflexivity.
      }
      {
        assert (~ indifferent po1 x x0).
        { intro. apply asboolT in H3. rewrite Ixx0 in H3. inversion H3. }
        assert (~ indifferent po2 x x0).
        { rewrite <- H2. exact H3. }
        assert (`[< indifferent po2 x x0 >] = false).
        { apply asboolF. exact H4. }
        rewrite H5.
        apply propositional_extensionality.
        apply same_order_non_strict. unfold same_order. tauto.
      }
    }
    { reflexivity. }
  }
  { destruct (Z x0) eqn:Zx0; reflexivity. }
Qed.

Lemma agree_on_implies_remove_indifference_equal_profile
{pp1 pp2 : @PreferenceProfile Outcome Individual} {Z : pred Outcome}
(ago : agree_on_profile pp1 pp2 Z) :
  remove_indifference_PreferenceProfile pp1 Z =
  remove_indifference_PreferenceProfile pp2 Z.
Proof.
  unfold remove_indifference_PreferenceProfile. unfold agree_on_profile in ago.
  apply functional_extensionality. intro.
  apply agree_on_implies_remove_indifference_equal. apply ago.
Qed.

Definition strictly_preferred_when_dominant_strategies {gf : GameForm}
(straightforward_gf : straightforward gf)
(pp : @PreferenceProfile Outcome Individual) : relation Outcome :=
  fun (x : Outcome) => fun (y : Outcome) =>
  x <> y /\ x = outcome_when_dominant_strategies straightforward_gf (
    remove_indifference_PreferenceProfile pp (pair x y)
  ).

Definition preferred_when_dominant_strategies {gf : GameForm}
(straightforward_gf : straightforward gf) (pp : @PreferenceProfile Outcome Individual) :
relation Outcome :=
  fun (x : Outcome) => fun (y : Outcome) =>
  x = y \/ y <> outcome_when_dominant_strategies straightforward_gf (
    remove_indifference_PreferenceProfile pp (pair x y)
  ).

Lemma switch_strictness_preferred_when_dominant_strategies {gf : GameForm}
(straightforward_gf : straightforward gf) (pp : @PreferenceProfile Outcome Individual) :
  switch_strictness (
    preferred_when_dominant_strategies straightforward_gf pp
  ) = strictly_preferred_when_dominant_strategies straightforward_gf pp.
Proof.
  unfold switch_strictness. unfold RelationClasses.complement.
  unfold Basics.flip.
  apply functional_extensionality. intro.
  apply functional_extensionality. intro.
  unfold preferred_when_dominant_strategies.
  unfold strictly_preferred_when_dominant_strategies.
  apply propositional_extensionality.
  rewrite -> eq_symmetric at 1.
  rewrite -> pair_symmetric at 1.
  tauto.
Qed.

Lemma switch_strictness_preferred_when_dominant_strategies' {gf : GameForm}
(straightforward_gf : straightforward gf) (pp : @PreferenceProfile Outcome Individual) :
  switch_strictness (
    strictly_preferred_when_dominant_strategies straightforward_gf pp
  ) = preferred_when_dominant_strategies straightforward_gf pp.
Proof.
  pose proof (switch_strictness_involutive Outcome).
  unfold involutive in H. unfold cancel in H.
  pose proof (
    switch_strictness_preferred_when_dominant_strategies straightforward_gf pp
  ).
  apply (f_equal switch_strictness) in H0.
  rewrite H in H0.
  rewrite H0. reflexivity.
Qed.

Lemma preferred_when_dominant_strategies_strict_implies_nonstrict {gf : GameForm}
(straightforward_gf : straightforward gf) (pp : @PreferenceProfile Outcome Individual)
(x y : Outcome) :
  strictly_preferred_when_dominant_strategies straightforward_gf pp x y ->
  preferred_when_dominant_strategies straightforward_gf pp x y.
Proof.
  unfold preferred_when_dominant_strategies.
  unfold strictly_preferred_when_dominant_strategies.
  intros.
  destruct H.
  rewrite <- H0.
  right. apply not_eq_sym. exact H.
Qed.

Lemma pairwise_determination {gf : GameForm}
(straightforward_gf : straightforward gf)
(pp1 pp2 : @PreferenceProfile Outcome Individual)
(x y : Outcome) :
  @unanimously_same_order Outcome Individual pp1 pp2 x y ->
  (
    strictly_preferred_when_dominant_strategies straightforward_gf pp1 x y <->
    strictly_preferred_when_dominant_strategies straightforward_gf pp2 x y
  ).
Proof.
  unfold unanimously_same_order. unfold strictly_preferred_when_dominant_strategies.
  intros.
  assert (
    remove_indifference_PreferenceProfile pp1 (pair x y) =
    remove_indifference_PreferenceProfile pp2 (pair x y)
  ).
  {
    apply agree_on_implies_remove_indifference_equal_profile.
    unfold agree_on_profile. unfold agree_on.
    intros. specialize (H i).
    unfold pair in H0.
    rewrite Bool.andb_lazy_alt in H0.
    destruct ((x0 == x) || (x0 == y)) eqn:Pxyx0.
    {
      destruct (x0 == x) eqn:Ex0x.
      {
        assert (x0 = x).
        { by apply/eqP. }
        rewrite H1.
        destruct (y0 == x) eqn:Ey0x.
        {
          assert (y0 = x).
          { by apply/eqP. }
          rewrite H2.
          apply same_order_reflexive.
        }
        {
          rewrite Bool.orb_false_l in H0.
          assert (y0 = y).
          { by apply/eqP. }
          rewrite H2.
          exact H.
        }
      }
      {
        rewrite Bool.orb_false_l in Pxyx0.
        assert (x0 = y).
        { by apply/eqP. }
        rewrite H1.
        destruct (y0 == x) eqn:Ey0x.
        {
          assert (y0 = x).
          { by apply/eqP. }
          rewrite H2.
          apply same_order_symmetric. exact H.
        }
        {
          rewrite Bool.orb_false_l in H0.
          assert (y0 = y).
          { by apply/eqP. }
          rewrite H2.
          apply same_order_reflexive.
        }
      }
    }
    { inversion H0. }
  }
  rewrite H0. tauto.
Qed.

Definition IndividualRank : finType :=
  fintype_ordinal__canonical__eqtype_SubType #|[eta Individual]|.

Lemma assertion_1 {gf : GameForm} (straightforward_gf : straightforward gf)
(inh : 0 < #|Individual|) (pp : @PreferenceProfile Outcome Individual)
(sp : StrategyProfile) (x y : Outcome) (Exy : x <> y) :
  (
    forall (i : Individual),
    strict (pp i) y x -> sp i = dominant_strategies_profile straightforward_gf pp i
  ) ->
  (forall (i : Individual), ~ indifferent (pp i) x y) ->
  (preferred_when_dominant_strategies straightforward_gf pp y x) ->
  x <> gf sp.
Proof.
  unfold not. intros.
  unfold preferred_when_dominant_strategies in H1.
  destruct H1.
  { apply Exy. rewrite H1. reflexivity. }
  unfold outcome_when_dominant_strategies in H1.
  pose proof (instance_makes_card_nonnull (enum_val (Ordinal inh) : Individual)).
  pose proof (lt_mathcomp_equivalent 0 #|Individual|).
  assert ((0 < #|Individual|)%coq_nat).
  { tauto. }
  clear H4.
  assert (
    x = gf (
      replace_until 0 sp (
        dominant_strategies_profile straightforward_gf (
          remove_indifference_PreferenceProfile pp (pair y x)
        )
      )
    )
  ).
  { rewrite replace_none. exact H2. }
  assert (
    x <> gf (
      replace_until #|Individual| sp (
        dominant_strategies_profile straightforward_gf (
          remove_indifference_PreferenceProfile pp (pair y x)
        )
      )
    )
  ).
  { rewrite replace_all. exact H1. }
  assert (Minimization_Property (
    fun (k : nat) => x <> gf (
      replace_until k sp (
        dominant_strategies_profile straightforward_gf (
          remove_indifference_PreferenceProfile pp (pair y x)
        )
      )
    )
  )).
  {
    apply excluded_middle_entails_unrestricted_minimization.
    intro. tauto.
  }
  specialize (H7 #|Individual|). simpl in H7. specialize (H7 H6).
  destruct H7 as [k].
  unfold Minimal in H7. destruct H7.
  assert ((k <= #|Individual|)%coq_nat).
  {
    specialize (H8 #|Individual|).
    apply H8. exact H6.
  }
  assert ((0 < k)%coq_nat).
  {
    destruct k eqn:valk.
    {
      rewrite <- H4 in H7.
      exfalso. apply H7. reflexivity.
    }
    { intuition. }
  }
  assert ((Nat.pred k < #|Individual|)%coq_nat).
  {
    assert ((k.-1 < k)%coq_nat).
    {
      apply PeanoNat.Nat.lt_pred_l.
      intuition.
      rewrite H11 in H10. inversion H10.
    }
    apply PeanoNat.Nat.lt_le_trans with (m:=k); tauto.
  }
  assert (Nat.pred k < #|Individual|).
  { apply lt_mathcomp_equivalent. exact H11. }
  assert (
    strict (pp (enum_val (Ordinal H12))) y x <->
    ~ strict (pp (enum_val (Ordinal H12))) x y
  ).
  {
    specialize (H0 (enum_val (Ordinal H12))).
    unfold indifferent in H0.
    pose proof (strict_asymmetric (pp (enum_val (Ordinal H12))) x y).
    tauto.
  }
  assert (
    (
      gf (replace_until k sp (
        dominant_strategies_profile straightforward_gf (
          remove_indifference_PreferenceProfile pp (pair y x)
        )
      )) = y /\
      strict (pp (enum_val (Ordinal H12))) y x
    ) \/ (
      gf (replace_until k sp (
        dominant_strategies_profile straightforward_gf (
          remove_indifference_PreferenceProfile pp (pair y x)
        )
      )) <> y \/
      strict (pp (enum_val (Ordinal H12))) x y
    )
  ).
  { tauto. }
  assert (
    gf (
      replace_until k.-1 sp (
        dominant_strategies_profile straightforward_gf (
          remove_indifference_PreferenceProfile pp (pair y x)
        )
      )
    ) = x
  ).
  {
    specialize (H8 k.-1).
    assert (~ (k <= k.-1)%coq_nat).
    {
      destruct k.
      { inversion H10. }
      {
        rewrite PeanoNat.Nat.pred_succ.
        intro.
        assert ((k < k)%coq_nat).
        { unfold lt. exact H15. }
        { apply (Nat.lt_irrefl k) in H16. inversion H16. }
      }
    }
    unfold not in H8. symmetry. tauto.
  }
  destruct H14.
  {
    destruct H14.
    {
      pose proof H16 as H16'.
      rewrite <- H14 in H16.
      rewrite <- H15 in H16 at 2.
      assert (
        replace_until k.-1 sp (
          dominant_strategies_profile straightforward_gf (
            remove_indifference_PreferenceProfile pp (pair y x)
          )
        ) = replace (
          replace_until k sp (
            dominant_strategies_profile straightforward_gf (
              remove_indifference_PreferenceProfile pp (pair y x)
            )
          )
        ) (
          enum_val (Ordinal H12)
        ) (
          sp (enum_val (Ordinal H12))
        )
      ).
      {
        unfold replace_until.
        apply functional_extensionality_dep. intro.
        destruct (enum_rank x0 < k.-1) eqn:Hx0k.
        {
          rewrite lt_mathcomp_equivalent in Hx0k.
          assert (enum_val (Ordinal H12) <> x0).
          {
            intro.
            rewrite <- H17 in Hx0k.
            rewrite (enum_valK (Ordinal H12)) in Hx0k.
            simpl in Hx0k.
            apply Nat.lt_irrefl with (x:=k.-1). exact Hx0k.
          }
          rewrite replace_unchanges.
          2: { exact H17. }
          assert (enum_rank x0 < k = true).
          {
            rewrite lt_mathcomp_equivalent.
            assert ((k.-1 < k)%coq_nat).
            { apply Arith_base.lt_pred_n_n_stt. exact H10. }
            apply Nat.lt_trans with (m:=k.-1); tauto.
          }
          rewrite H18.
          reflexivity.
        }
        {
          rewrite lt_mathcomp_equivalent_not in Hx0k.
          destruct (enum_rank x0 < k) eqn:Ix0k.
          {
            rewrite lt_mathcomp_equivalent in Ix0k.
            pose proof (lt_eq_lt_dec (enum_rank x0) k.-1).
            destruct H17. destruct s.
            { tauto. }
            {
              assert (enum_val (Ordinal H12) = x0).
              {
                apply enum_rank_inj.
                pose proof (enum_valK (Ordinal H12)).
                rewrite H17. apply ord_inj. rewrite e.
                reflexivity.
              }
              rewrite H17.
              rewrite replace_changes.
              reflexivity.
            }
            {
              apply Nat.lt_pred_le in l.
              pose proof(Nat.lt_le_trans (enum_rank x0) k (enum_rank x0) Ix0k l).
              apply (Nat.lt_irrefl (enum_rank x0)) in H17. inversion H17.
            }
          }
          {
            rewrite lt_mathcomp_equivalent_not in Ix0k.
            assert (nat_of_ord (enum_rank x0) <> k.-1).
            {
              intro.
              rewrite H17 in Ix0k.
              apply Ix0k.
              apply Arith_base.lt_pred_n_n_stt.
              exact H10.
            }
            assert (enum_val (Ordinal H12) <> x0).
            {
              intro.
              rewrite <- H18 in H17.
              pose proof (enum_valK (Ordinal H12)).
              rewrite H18 in H19.
              rewrite H19 in Ix0k.
              simpl in Ix0k.
              apply Ix0k.
              apply Arith_base.lt_pred_n_n_stt.
              exact H10.
            }
            assert (enum_val (Ordinal H12) <> x0).
            { intuition. }
            rewrite replace_unchanges.
            2: { exact H18. }
            destruct (enum_rank x0 < k) eqn:Ex0k.
            {
              rewrite <- lt_mathcomp_equivalent_not in Ix0k.
              rewrite Ex0k in Ix0k.
              inversion Ix0k.
            }
            { reflexivity. }
          }
        }
      }
      rewrite H17 in H16.
      assert (
        ~ dominant (sp (
          enum_val (Ordinal H12)
        )) (pp (
          enum_val (Ordinal H12)
        )) gf
      ).
      {
        unfold dominant. intro.
        specialize (H18 (replace_until k sp (
          dominant_strategies_profile straightforward_gf (
            remove_indifference_PreferenceProfile pp (pair y x)
          )
        ))).
        unfold strict in H16. tauto.
      }
      assert (
        sp (enum_val (Ordinal H12)) =
        dominant_strategies_profile straightforward_gf pp (enum_val (Ordinal H12))
      ).
      { apply H. exact H16'. }
      rewrite H19 in H18. unfold dominant_strategies_profile in H18.
      pose proof (
        dominant_strategies_well_named
        straightforward_gf
        (enum_val (Ordinal H12))
        (pp (enum_val (Ordinal H12)))
      ).
      tauto.
    }
  }
  assert (
    strict (
      remove_indifference_PreferenceProfile pp (pair y x) (enum_val (Ordinal H12))
    ) x (gf (
      replace_until k sp (
        dominant_strategies_profile straightforward_gf (
          remove_indifference_PreferenceProfile pp (pair y x)
        )
      )
    ))
  ).
  {
    assert (
      gf (replace_until k sp (
        dominant_strategies_profile straightforward_gf (
          remove_indifference_PreferenceProfile pp (pair y x)
        )
      )) = y \/
      gf (replace_until k sp (
        dominant_strategies_profile straightforward_gf (
          remove_indifference_PreferenceProfile pp (pair y x)
        )
      )) <> y
    ).
    { tauto. }
    destruct H16.
    {
      destruct H14.
      { tauto. }
      assert (
        strict (
          remove_indifference_PreferenceProfile pp (pair y x) (
            enum_val (Ordinal H12)
          )
        ) x y
      ).
      {
        apply remove_indifference_strict_unchanged_on_Z.
        { apply pair_snd. }
        { apply pair_fst. }
        { exact H14. }
      }
      rewrite H16. exact H17.
    }
    {
      clear H14.
      apply remove_indifference_in_Z_out_Z.
      { apply pair_snd. }
      unfold negb.
      destruct (pair y x (gf (
        replace_until k sp (
          dominant_strategies_profile straightforward_gf (
            remove_indifference_PreferenceProfile pp (pair y x)
          )
        )
      ))) eqn:pair.
      {
        apply nesym in H7.
        pose proof (pair_closure H16 H7).
        exfalso. apply H14.
        intuition.
      }
      { intuition. }
    }
  }
  rewrite <- H15 in H16 at 2.
  assert (
    replace_until k sp (
      dominant_strategies_profile straightforward_gf (
        remove_indifference_PreferenceProfile pp (pair y x)
      )
    ) = replace (
      replace_until k.-1 sp (
        dominant_strategies_profile straightforward_gf (
          remove_indifference_PreferenceProfile pp (pair y x)
        )
      )
    ) (
      enum_val (Ordinal H12)
    ) (
      dominant_strategies_profile straightforward_gf (
        remove_indifference_PreferenceProfile pp (pair y x)
      ) (enum_val (Ordinal H12))
    )
  ).
  {
    unfold replace_until.
    apply functional_extensionality_dep. intro.
    destruct (enum_rank x0 < k.-1) eqn:Hx0k.
    {
      rewrite lt_mathcomp_equivalent in Hx0k.
      assert (enum_val (Ordinal H12) <> x0).
      {
        intro.
        rewrite <- H17 in Hx0k.
        rewrite (enum_valK (Ordinal H12)) in Hx0k.
        simpl in Hx0k.
        apply Nat.lt_irrefl with (x:=k.-1). exact Hx0k.
      }
      rewrite replace_unchanges.
      2: { exact H17. }
      assert (enum_rank x0 < k = true).
      {
        rewrite lt_mathcomp_equivalent.
        assert ((k.-1 < k)%coq_nat).
        { apply Arith_base.lt_pred_n_n_stt. exact H10. }
        apply Nat.lt_trans with (m:=k.-1); tauto.
      }
      rewrite H18.
      rewrite <- lt_mathcomp_equivalent in Hx0k. rewrite Hx0k.
      reflexivity.
    }
    {
      rewrite lt_mathcomp_equivalent_not in Hx0k.
      destruct (enum_rank x0 < k) eqn:Ix0k.
      {
        rewrite lt_mathcomp_equivalent in Ix0k.
        pose proof (lt_eq_lt_dec (enum_rank x0) k.-1).
        destruct H17. destruct s.
        { tauto. }
        {
          assert (enum_val (Ordinal H12) = x0).
          {
            apply enum_rank_inj.
            pose proof (enum_valK (Ordinal H12)).
            rewrite H17. apply ord_inj. rewrite e.
            reflexivity.
          }
          rewrite H17.
          rewrite replace_changes.
          reflexivity.
        }
        {
          apply Nat.lt_pred_le in l.
          pose proof(Nat.lt_le_trans (enum_rank x0) k (enum_rank x0) Ix0k l).
          apply (Nat.lt_irrefl (enum_rank x0)) in H17. inversion H17.
        }
      }
      {
        rewrite lt_mathcomp_equivalent_not in Ix0k.
        assert (nat_of_ord (enum_rank x0) <> k.-1).
        {
          intro.
          rewrite H17 in Ix0k.
          apply Ix0k.
          apply Arith_base.lt_pred_n_n_stt.
          exact H10.
        }
        assert (enum_val (Ordinal H12) <> x0).
        {
          intro.
          rewrite <- H18 in H17.
          pose proof (enum_valK (Ordinal H12)).
          rewrite H18 in H19.
          rewrite H19 in Ix0k.
          simpl in Ix0k.
          apply Ix0k.
          apply Arith_base.lt_pred_n_n_stt.
          exact H10.
        }
        rewrite replace_unchanges.
        2: { exact H18. }
        rewrite <- lt_mathcomp_equivalent_not in Hx0k. rewrite Hx0k.
        reflexivity.
      }
    }
  }
  rewrite H17 in H16.
  assert (
    ~ dominant (
      dominant_strategies_profile straightforward_gf (
        remove_indifference_PreferenceProfile pp (pair y x)
      ) (enum_val (Ordinal H12))
    ) (
      remove_indifference_PreferenceProfile pp (pair y x) (
        enum_val (Ordinal H12)
      )
    ) gf
  ).
  {
    unfold dominant. intro.
    specialize (H18 (replace_until k.-1 sp (
      dominant_strategies_profile straightforward_gf (
        remove_indifference_PreferenceProfile pp (pair y x)
      )
    ))).
    unfold strict in H16. tauto.
  }
  unfold dominant_strategies_profile in H18.
  pose proof (
    dominant_strategies_well_named
    straightforward_gf
    (enum_val (Ordinal H12))
    (
      remove_indifference_PreferenceProfile pp (pair y x) (
        enum_val (Ordinal H12)
      )
    )
  ).
  tauto.
Qed.

Corollary strictly_preferred_when_dominant_strategies_respects_unanimity
{gf : GameForm} (straightforward_gf : straightforward gf) (inh : 0 < #|Individual|)
(pp : @PreferenceProfile Outcome Individual) (x y : Outcome)
(gf_surj : Surjective gf) :
  (forall (i : Individual), strict (pp i) x y) ->
  strictly_preferred_when_dominant_strategies straightforward_gf pp x y.
Proof.
  unfold Surjective in gf_surj. specialize (gf_surj x).
  destruct gf_surj as [sp].
  pose proof(assertion_1 straightforward_gf inh pp sp x y).
  intro.
  assert (x <> y).
  {
    pose proof (H1 (enum_val (Ordinal inh))).
    pose proof (strict_implies_unequal (pp (enum_val (Ordinal inh))) x y H2).
    exact H3.
  }
  specialize (H0 H2).
  assert (
    forall (i : Individual),
      strict (pp i) y x ->
      sp i =
      dominant_strategies_profile straightforward_gf pp i
  ).
  {
    intros. specialize (H1 i).
    exfalso. apply strict_asymmetric with (po:= pp i) (a:=x) (b:=y); tauto.
  }
  specialize (H0 H3).
  assert (forall i : Individual, ~ indifferent (pp i) x y).
  {
    unfold indifferent.
    intro. specialize (H1 i).
    tauto.
  }
  specialize (H0 H4).
  rewrite H in H0.
  assert (~ preferred_when_dominant_strategies straightforward_gf pp y x).
  { tauto. }
  pose proof (
    switch_strictness_preferred_when_dominant_strategies straightforward_gf pp
  ).
  unfold switch_strictness in H6. unfold RelationClasses.complement in H6.
  unfold Basics.flip in H6.
  assert (
    (preferred_when_dominant_strategies straightforward_gf pp y x -> False) =
    strictly_preferred_when_dominant_strategies straightforward_gf pp x y
  ).
  { rewrite <- H6. reflexivity. }
  rewrite <- H7. exact H5.
Qed.

Corollary corollary_2 {gf : GameForm} (straightforward_gf : straightforward gf)
(inh : 0 < #|Individual|) (pp : @PreferenceProfile Outcome Individual)
(x y : Outcome) :
  (forall (i : Individual), ~ indifferent (pp i) x y) ->
  preferred_when_dominant_strategies straightforward_gf pp y x ->
  outcome_when_dominant_strategies straightforward_gf pp <> x.
Proof.
  intros.
  pose proof(assertion_1 straightforward_gf inh pp (
    dominant_strategies_profile straightforward_gf pp
  ) x y).
  assert (x <> y).
  {
    pose proof (H (enum_val (Ordinal inh))).
    intro. apply H2. rewrite H3.
    pose proof (indifferent_reflexive (pp (enum_val (Ordinal inh)))).
    unfold reflexive in H4. apply (H4 y).
  }
  specialize (H1 H2).
  assert (
    forall i : Individual,
    strict (pp i) y x ->
    dominant_strategies_profile straightforward_gf pp i =
    dominant_strategies_profile straightforward_gf pp i
  ).
  { intros. reflexivity. }
  specialize (H1 H3). specialize (H1 H). specialize (H1 H0).
  unfold outcome_when_dominant_strategies. intro. apply H1.
  rewrite H4. reflexivity.
Qed.

Corollary corollary_3 {gf : GameForm} (straightforward_gf : straightforward gf)
(inh : 0 < #|Individual|) (pp : @PreferenceProfile Outcome Individual)
(x y : Outcome) :
  (forall (i : Individual), ~ indifferent (pp i) x y) ->
  outcome_when_dominant_strategies straightforward_gf pp = x ->
  strictly_preferred_when_dominant_strategies straightforward_gf pp x y.
Proof.
  intros.
  pose proof (
    switch_strictness_preferred_when_dominant_strategies straightforward_gf pp
  ).
  rewrite <- H1. unfold switch_strictness.
  unfold RelationClasses.complement. unfold Basics.flip.
  pose proof (corollary_2 straightforward_gf inh pp x y).
  tauto.
Qed.

Lemma assertion_2 {gf : GameForm} (straightforward_gf : straightforward gf)
(inh : 0 < #|Individual|) (pp : @PreferenceProfile Outcome Individual)
(gf_surj : Surjective gf) :
  preference_order (
    preferred_when_dominant_strategies straightforward_gf pp
  ).
Proof.
  rewrite <- switch_strictness_preferred_when_dominant_strategies'.
  apply switch_strict_preference_is_preference.
  unfold strict_preference.
  split.
  {
    unfold strictly_preferred_when_dominant_strategies.
    unfold not. intros.
    rewrite pair_symmetric in H.
    destruct H. destruct H. destruct H0.
    rewrite <- H1 in H2.
    tauto.
  }
  {
    intro. intro. intro.
    assert (
      remove_indifference_PreferenceProfile (
        remove_indifference_PreferenceProfile pp (triple x y z)
      ) (pair x z) = remove_indifference_PreferenceProfile pp (pair x z)
    ).
    {
      apply remove_indifference_profile_down_to_littlest_subset.
      apply pair_subpred_triple'.
    }
    assert (
      strictly_preferred_when_dominant_strategies straightforward_gf pp x z <-> (
        x <> z /\
        x = outcome_when_dominant_strategies straightforward_gf (
          remove_indifference_PreferenceProfile pp (pair x z)
        )
      )
    ).
    { unfold strictly_preferred_when_dominant_strategies. tauto. }
    assert (
      strictly_preferred_when_dominant_strategies straightforward_gf (
        remove_indifference_PreferenceProfile pp (triple x y z)
      ) x z <-> (
        x <> z /\
        x = outcome_when_dominant_strategies straightforward_gf (
          remove_indifference_PreferenceProfile (
            remove_indifference_PreferenceProfile pp (triple x y z)
          ) (pair x z)
        )
      )
    ).
    { unfold strictly_preferred_when_dominant_strategies. tauto. }
    assert (
      strictly_preferred_when_dominant_strategies straightforward_gf (
        remove_indifference_PreferenceProfile pp (triple x y z)
      ) x z <->
      strictly_preferred_when_dominant_strategies straightforward_gf pp x z
    ).
    {
      rewrite H0. rewrite H1. rewrite H.
      reflexivity.
    }
    assert (
      remove_indifference_PreferenceProfile (
        remove_indifference_PreferenceProfile pp (triple x y z)
      ) (pair x y) = remove_indifference_PreferenceProfile pp (pair x y)
    ).
    {
      apply remove_indifference_profile_down_to_littlest_subset.
      apply pair_subpred_triple.
    }
    assert (
      strictly_preferred_when_dominant_strategies straightforward_gf pp x y <-> (
        x <> y /\
        x = outcome_when_dominant_strategies straightforward_gf (
          remove_indifference_PreferenceProfile pp (pair x y)
        )
      )
    ).
    { unfold strictly_preferred_when_dominant_strategies. tauto. }
    assert (
      strictly_preferred_when_dominant_strategies straightforward_gf (
        remove_indifference_PreferenceProfile pp (triple x y z)
      ) x y <-> (
        x <> y /\
        x = outcome_when_dominant_strategies straightforward_gf (
          remove_indifference_PreferenceProfile (
            remove_indifference_PreferenceProfile pp (triple x y z)
          ) (pair x y)
        )
      )
    ).
    { unfold strictly_preferred_when_dominant_strategies. tauto. }
    assert (
      strictly_preferred_when_dominant_strategies straightforward_gf (
        remove_indifference_PreferenceProfile pp (triple x y z)
      ) x y <->
      strictly_preferred_when_dominant_strategies straightforward_gf pp x y
    ).
    {
      rewrite H4. rewrite H5. rewrite H3.
      reflexivity.
    }
    assert (
      remove_indifference_PreferenceProfile (
        remove_indifference_PreferenceProfile pp (triple x y z)
      ) (pair y z) = remove_indifference_PreferenceProfile pp (pair y z)
    ).
    {
      apply remove_indifference_profile_down_to_littlest_subset.
      apply pair_subpred_triple''.
    }
    assert (
      strictly_preferred_when_dominant_strategies straightforward_gf pp y z <-> (
        y <> z /\
        y = outcome_when_dominant_strategies straightforward_gf (
          remove_indifference_PreferenceProfile pp (pair y z)
        )
      )
    ).
    { unfold strictly_preferred_when_dominant_strategies. tauto. }
    assert (
      strictly_preferred_when_dominant_strategies straightforward_gf (
        remove_indifference_PreferenceProfile pp (triple x y z)
      ) y z <-> (
        y <> z /\
        y = outcome_when_dominant_strategies straightforward_gf (
          remove_indifference_PreferenceProfile (
            remove_indifference_PreferenceProfile pp (triple x y z)
          ) (pair y z)
        )
      )
    ).
    { unfold strictly_preferred_when_dominant_strategies. tauto. }
    assert (
      strictly_preferred_when_dominant_strategies straightforward_gf (
        remove_indifference_PreferenceProfile pp (triple x y z)
      ) y z <->
      strictly_preferred_when_dominant_strategies straightforward_gf pp y z
    ).
    {
      rewrite H8. rewrite H9. rewrite H7.
      reflexivity.
    }
    assert (
      strictly_preferred_when_dominant_strategies straightforward_gf (
        remove_indifference_PreferenceProfile pp (triple x y z)
      ) x z -> (
        strictly_preferred_when_dominant_strategies straightforward_gf (
          remove_indifference_PreferenceProfile pp (triple x y z)
        ) x y \/
        strictly_preferred_when_dominant_strategies straightforward_gf (
          remove_indifference_PreferenceProfile pp (triple x y z)
        ) y z
      )
    ).
    2: { rewrite <- H2. rewrite <- H6. rewrite <- H10. exact H11. }
    intro.
    assert (x <> z).
    {
      unfold strictly_preferred_when_dominant_strategies in H11.
      tauto.
    }
    assert (y = x \/ y <> x). { apply classic. }
    destruct H13.
    { rewrite H13. rewrite H13 in H11. right. exact H11. }
    assert (y = z \/ y <> z). { apply classic. }
    destruct H14.
    { rewrite -> H14 at 2. left. exact H11. }
    assert (
      forall (i : Individual), ~ indifferent (
        remove_indifference_PreferenceProfile pp (triple x y z) i
      ) x y
    ).
    {
      intro.
      pose proof (
        remove_indifference_well_named (pp i) (triple x y z) x y
      ).
      intro.
      specialize (H15 H16).
      apply H13. rewrite H15. reflexivity.
    }
    assert (
      forall (i : Individual), ~ indifferent (
        remove_indifference_PreferenceProfile pp (triple x y z) i
      ) x z
    ).
    {
      intro.
      pose proof (
        remove_indifference_well_named (pp i) (triple x y z) x z
      ).
      intro.
      specialize (H16 H17).
      apply H12. rewrite H16. reflexivity.
    }
    assert (
      forall (i : Individual), ~ indifferent (
        remove_indifference_PreferenceProfile pp (triple x y z) i
      ) y z
    ).
    {
      intro.
      pose proof (
        remove_indifference_well_named (pp i) (triple x y z) y z
      ).
      intro.
      specialize (H17 H18).
      apply H14. rewrite H17. reflexivity.
    }
    assert (
      x = outcome_when_dominant_strategies straightforward_gf (
        remove_indifference_PreferenceProfile pp (triple x y z)
      ) \/
      x <> outcome_when_dominant_strategies straightforward_gf (
        remove_indifference_PreferenceProfile pp (triple x y z)
      )
    ). { apply classic. }
    destruct H18.
    {
      left.
      apply (
        corollary_3 straightforward_gf inh (
          remove_indifference_PreferenceProfile pp (triple x y z)
        ) x y
      ).
      { exact H15. }
      { rewrite <- H18. reflexivity. }
    }
    {
      pose proof (
        corollary_2 straightforward_gf inh (
          remove_indifference_PreferenceProfile pp (triple x y z)
        ) z x
      ).
      assert (
        forall i : Individual, ~ indifferent (
          remove_indifference_PreferenceProfile pp (triple x y z) i
        ) z x
      ).
      {
        intro.
        specialize (H16 i).
        pose proof (indifferent_symmetric (
          remove_indifference_PreferenceProfile pp (triple x y z) i
        )).
        unfold symmetric in H20. specialize (H20 z x).
        intro. apply H16. apply H20. exact H21.
      }
      specialize (H19 H20).
      assert (
        preferred_when_dominant_strategies straightforward_gf (
          remove_indifference_PreferenceProfile pp (triple x y z)
        ) x z
      ).
      {
        apply preferred_when_dominant_strategies_strict_implies_nonstrict.
        exact H11.
      }
      specialize (H19 H21).
      assert (
        forall (w : Outcome),
          ~~ (triple x y z) w ->
          w <> outcome_when_dominant_strategies straightforward_gf (
            remove_indifference_PreferenceProfile pp (triple x y z)
          )
      ).
      {
        intros.
        assert (
          forall (i : Individual),
            strict (
              remove_indifference_PreferenceProfile pp (triple x y z) i
            ) x w
        ).
        {
          intro.
          apply remove_indifference_in_Z_out_Z.
          { apply triple_fst. }
          { exact H22. }
        }
        pose proof (
          strictly_preferred_when_dominant_strategies_respects_unanimity
          straightforward_gf
          inh
          (* pp *)
          (remove_indifference_PreferenceProfile pp (triple x y z))
          x
          w
          gf_surj
        ).
        specialize (H24 H23).
        pose proof (
          corollary_2 straightforward_gf inh (
            remove_indifference_PreferenceProfile pp (triple x y z)
          ) w x
        ).
        assert (
          forall i : Individual, ~ indifferent (
            remove_indifference_PreferenceProfile pp (triple x y z) i
          ) w x
        ).
        {
          intro. unfold indifferent.
          specialize (H23 i).
          tauto.
        }
        specialize (H25 H26).
        apply preferred_when_dominant_strategies_strict_implies_nonstrict in H24.
        specialize (H25 H24).
        intro. apply H25. rewrite <- H27. reflexivity.
      }
      assert (
        outcome_when_dominant_strategies straightforward_gf (
          remove_indifference_PreferenceProfile pp (triple x y z)
        ) = y
      ).
      {
        destruct (triple x y z (
          outcome_when_dominant_strategies straightforward_gf (
            remove_indifference_PreferenceProfile pp (triple x y z)
          )
        )) eqn:in_tri.
        {
          pose proof(triple_closure in_tri).
          destruct H23.
          { rewrite H23 in H18. exfalso. apply H18. reflexivity. }
          destruct H23.
          { exact H23. }
          { rewrite H23 in H19. exfalso. apply H19. reflexivity. }
        }
        {
          specialize (H22 (
            outcome_when_dominant_strategies straightforward_gf (
              remove_indifference_PreferenceProfile pp (triple x y z)
            )
          )).
          apply negbT in in_tri. specialize (H22 in_tri).
          exfalso. apply H22. reflexivity.
        }
      }
      right.
      apply (
        corollary_3 straightforward_gf inh (
          remove_indifference_PreferenceProfile pp (triple x y z)
        ) y z H17 H23
      ).
    }
  }
Qed.

Definition aggregation_preferences {gf : GameForm}
(straightforward_gf : straightforward gf) (inh : 0 < #|Individual|)
(pp : @PreferenceProfile Outcome Individual) (gf_surj : Surjective gf) :
PreferenceOrder Outcome :=
  exist preference_order (
    preferred_when_dominant_strategies straightforward_gf pp
  ) (assertion_2 straightforward_gf inh pp gf_surj).

Lemma assertion_3 {gf : GameForm} (straightforward_gf : straightforward gf)
(inh : 0 < #|Individual|) (out3 : #|Outcome| >= 3)
(sp : StrategyProfile) (gf_surj : Surjective gf) :
  exists (k : Individual), @dictator Outcome Individual (
    fun (pp : @PreferenceProfile Outcome Individual) =>
      aggregation_preferences straightforward_gf inh pp gf_surj
  ) k.
Proof.
  apply Arrow.
  { exact out3. }
  {
    unfold respects_unanimity. unfold unanimously_prefers.
    intros.
    pose proof (
      strictly_preferred_when_dominant_strategies_respects_unanimity
      straightforward_gf
      inh
      pp
      a
      b
      gf_surj
      H
    ).
    unfold aggregation_preferences.
    unfold strict. unfold non_strict. simpl.
    rewrite <- switch_strictness_preferred_when_dominant_strategies in H0.
    unfold switch_strictness in H0. unfold RelationClasses.complement in H0.
    unfold Basics.flip in H0.
    tauto.
  }
  {
    unfold independence_irrelevant_alternatives.
    intros.
    pose proof (
      pairwise_determination straightforward_gf pp1 pp2 a b
    ).
    pose proof (
      pairwise_determination straightforward_gf pp1 pp2 b a
    ).
    rewrite unanimously_same_order_symmetric in H1.
    specialize (H0 H). specialize (H1 H).
    rewrite <- switch_strictness_preferred_when_dominant_strategies in H0.
    rewrite <- switch_strictness_preferred_when_dominant_strategies in H0.
    rewrite <- switch_strictness_preferred_when_dominant_strategies in H1.
    rewrite <- switch_strictness_preferred_when_dominant_strategies in H1.
    rewrite same_order_characterization.
    unfold aggregation_preferences. unfold strict. unfold non_strict.
    simpl.
    unfold switch_strictness in H0. unfold switch_strictness in H1.
    unfold RelationClasses.complement in H0. unfold RelationClasses.complement in H1.
    unfold Basics.flip in H0. unfold Basics.flip in H1.
    tauto.
  }
Qed.

Lemma assertion_4 {gf : GameForm} (straightforward_gf : straightforward gf)
(inh : 0 < #|Individual|) (out3 : #|Outcome| >= 3) (gf_surj : Surjective gf) :
  forall (k : Individual),
    @dictator Outcome Individual (
      fun (pp : @PreferenceProfile Outcome Individual) =>
      aggregation_preferences straightforward_gf inh pp gf_surj
    ) k -> omnipotent k gf.
Proof.
  unfold omnipotent.
  intro. intro. intro y.
  remember (single_top_others_indifferent y) as P_y.
  remember (dominant_strategy straightforward_gf k P_y) as s_y.
  exists s_y.
  intro sp0. intro.
  assert (forall (x : Outcome), x <> y -> x <> gf sp0).
  {
    intros.
    pose proof (single_top_very_top y). unfold very_top_choice in H2.
    specialize (H2 x). specialize (H2 H1).
    remember (
      fun (i : Individual) => if i == k then P_y else single_top_others_indifferent x
    ) as P_.
    remember (
      dominant_strategies_profile straightforward_gf P_
    ) as s_.
    assert (s_ k = sp0 k).
    {
      rewrite Heqs_. rewrite HeqP_.
      unfold dominant_strategies_profile.
      rewrite eq_refl.
      rewrite H0. rewrite <- Heqs_y.
      reflexivity.
    }
    pose proof (assertion_1 straightforward_gf inh P_ sp0 x y).
    specialize (H4 H1).
    rewrite <- Heqs_ in H4.
    assert (forall i : Individual, strict (P_ i) y x -> sp0 i = s_ i).
    {
      intros.
      destruct (i == k) eqn:Eik.
      {
        assert (i = k). { by apply/eqP. }
        rewrite H6. rewrite H3. reflexivity.
      }
      {
        assert (P_ i = single_top_others_indifferent x).
        { rewrite HeqP_. rewrite Eik. reflexivity. }
        pose proof (single_top_very_top x).
        unfold very_top_choice in H7.
        apply nesym in H1.
        specialize (H7 y H1).
        rewrite <- H6 in H7.
        exfalso. apply strict_asymmetric with (po:= P_ i) (a:=y) (b:=x); tauto.
      }
    }
    specialize (H4 H5).
    assert (forall i : Individual, ~ indifferent (P_ i) x y).
    {
      intro.
      unfold indifferent.
      destruct (i == k) eqn:Eik.
      {
        rewrite HeqP_. rewrite Eik.
        pose proof (single_top_very_top y).
        unfold very_top_choice in H6.
        specialize (H6 x H1). rewrite <- HeqP_y in H6.
        tauto.
      }
      {
        rewrite HeqP_. rewrite Eik.
        pose proof (single_top_very_top x).
        unfold very_top_choice in H6.
        apply nesym in H1.
        specialize (H6 y H1).
        tauto.
      }
    }
    specialize (H4 H6).
    unfold dictator in H. specialize  (H P_ y x).
    assert (strict (P_ k) y x).
    {
      rewrite HeqP_. rewrite eq_refl. rewrite HeqP_y.
      pose proof (single_top_very_top y).
      unfold very_top_choice in H7.
      specialize (H7 x H1).
      exact H7.
    }
    specialize (H H7).
    assert (preferred_when_dominant_strategies straightforward_gf P_ y x).
    {
      apply preferred_when_dominant_strategies_strict_implies_nonstrict.
      unfold aggregation_preferences in H. unfold strict in H.
      unfold non_strict in H. simpl in H.
      rewrite <- switch_strictness_preferred_when_dominant_strategies.
      unfold switch_strictness. unfold RelationClasses.complement.
      unfold Basics.flip.
      exact H.
    }
    apply H4. exact H8.
  }
  specialize (H1 (gf sp0)). tauto.
Qed.

Theorem Gibbard (_ : StrategyProfile) : forall (gf : GameForm),
  0 < #|Individual| ->
  #|Outcome| >= 3 ->
  Surjective gf ->
  straightforward gf ->
  admits_omnipotent gf.
Proof.
  intros.
  unfold admits_omnipotent.
  assert (
    exists k : Individual, @dictator Outcome Individual (
      fun (pp : @PreferenceProfile Outcome Individual) =>
      aggregation_preferences H2 H pp H1
    ) k
  ).
  2: {
    destruct H3 as [k]. exists k. apply assertion_4 with (
      straightforward_gf := H2
    ) (inh:=H) (gf_surj:=H1); tauto.
  }
  apply assertion_3.
  { exact H0. }
  { unfold StrategyProfile. intro. unfold StrategyProfile in X. apply X. }
Qed.

End gibbard_theorem.

Section gibbard_satterthwaite_theorem.

Context {Alternative: finType}.
Context {Individual : finType}.

Definition Strategy_VotingScheme : Type := PreferenceOrder Alternative.

Definition StrategyProfile_VotingScheme (_ : Individual) : Type :=
  PreferenceOrder Alternative.

Definition VotingScheme : Type :=
  @GameForm Alternative Individual StrategyProfile_VotingScheme.

Definition manipulable (vs : VotingScheme) : Prop :=
  exists (k : Individual) (pp : @PreferenceProfile Alternative Individual)
  (true_po : PreferenceOrder Alternative),
    strict true_po (vs pp) (vs (
      replace pp k true_po
    )).

Corollary GibbardSatterthwaite : forall (vs : VotingScheme),
  0 < #|Individual| ->
  #|Alternative| >= 3 ->
  Surjective vs ->
  (
    @admits_omnipotent Alternative Individual StrategyProfile_VotingScheme vs \/
    manipulable vs
  ).
Proof.
  intros.
  pose proof (lem (
    @admits_omnipotent Alternative Individual StrategyProfile_VotingScheme vs
  )).
  destruct H2. { tauto. }
  right.
  pose proof (
    @Gibbard
    Alternative
    Individual
    StrategyProfile_VotingScheme
  ).
  specialize (H3 (
    fun _ : Individual => single_top_others_indifferent (enum_val (Ordinal H0))
  ) vs H H0 H1).
  assert (~ straightforward vs). { tauto. } clear H3.
  unfold straightforward in H4.
  apply not_all_ex_not in H4.
  destruct H4 as [po].
  apply not_all_ex_not in H3.
  destruct H3 as [k].
  pose proof (not_ex_all_not Strategy_VotingScheme (
    fun (strategy : Strategy_VotingScheme) =>
    dominant strategy po vs
  ) H3 po).
  simpl in H4.
  unfold dominant in H4.
  apply not_all_ex_not in H4.
  destruct H4 as [sp].
  unfold manipulable. exists k. exists sp. exists po.
  unfold strict. exact H4.
Qed.

End gibbard_satterthwaite_theorem.
