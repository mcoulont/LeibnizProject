
Require Import Classical.
Require Import Relations.Relation_Definitions.
Require Import Logic.FunctionalExtensionality.
Require Import Logic.PropExtensionality.
Require Import Logic.IndefiniteDescription.
Require Import Arith.PeanoNat.
Require Import Bool.Bool.
Require Import Program.Basics.
From mathcomp Require Import all_ssreflect.
From mathcomp.classical Require Import boolp.

Require Import relation_facts.
Require Import preference.
Require Import finType_facts.

Section arrow_theorem.

Context {Alternative : finType}.
Context {Individual : finType}.

Definition PreferenceProfile : Type := Individual -> PreferenceOrder Alternative.

Definition Constitution : Type := PreferenceProfile -> PreferenceOrder Alternative.

Definition unanimously_prefers (pp : PreferenceProfile) (a b : Alternative) : Prop :=
  forall (i : Individual), strict (pp i) a b.

Definition respects_unanimity (constitution : Constitution) : Prop :=
  forall (pp : PreferenceProfile) (a b : Alternative),
    unanimously_prefers pp a b ->
    strict (constitution pp) a b.

Definition dictator (constitution : Constitution) (i : Individual) : Prop :=
  forall (pp : PreferenceProfile) (a b : Alternative),
    strict (pp i) a b ->
    strict (constitution pp) a b.

Definition dictator_except (constitution : Constitution) (i : Individual)
(b : Alternative) : Prop := 
  forall (a c : Alternative),
    a <> b ->
    c <> b ->
    forall (pp : PreferenceProfile), strict (pp i) c a -> strict (constitution pp) c a .

Definition unanimously_same_order (pp1 pp2 : PreferenceProfile)
(a b : Alternative) : Prop :=
  forall (i : Individual), same_order (pp1 i) (pp2 i) a b.

Definition independence_irrelevant_alternatives (constitution : Constitution) : Prop :=
  forall (pp1 pp2 : PreferenceProfile) (a b : Alternative),
    unanimously_same_order pp1 pp2 a b ->
    same_order (constitution pp1) (constitution pp2) a b.

Lemma not_very_top_or_not_very_bottom (alt2 : #|Alternative| >= 2)
(po : PreferenceOrder Alternative) (b : Alternative) :
  ~ (very_bottom_choice po b /\ very_top_choice po b).
Proof.
  assert (exists (a : Alternative), a <> b).
  { apply exists_2nd_distinct. exact alt2. }
  destruct H as [a].
  unfold not. rewrite Decidable.not_and_iff.
  unfold very_bottom_choice. unfold very_top_choice.
  intros.
  pose proof (H0 a). pose proof (H1 a).
  pose proof (H2 H). pose proof (H3 H).
  apply strict_asymmetric with (po:=po) (a:=a) (b:=b) ; tauto.
Qed.

Definition unanimous_very_top_choice (pp : PreferenceProfile) (b : Alternative) : Prop :=
  forall (i : Individual), very_top_choice (pp i) b.

Definition unanimous_very_bottom_choice (pp : PreferenceProfile) (b : Alternative) :
Prop :=
  forall (i : Individual), very_bottom_choice (pp i) b.

Definition unanimous_very_extremal_choice (pp : PreferenceProfile) (b : Alternative) :
Prop :=
  forall (i : Individual), very_extremal_choice (pp i) b.

Lemma unanimous_very_top (constitution : Constitution) (una : respects_unanimity constitution)
(pp : PreferenceProfile) (b : Alternative) :
  unanimous_very_top_choice pp b -> very_top_choice (constitution pp) b.
Proof.
  unfold unanimous_very_top_choice. unfold very_top_choice.
  intros.
  unfold respects_unanimity in una. apply una.
  unfold unanimously_prefers. intro.
  apply H. exact H0.
Qed.

Lemma unanimous_very_bottom (constitution : Constitution)
(una : respects_unanimity constitution) (pp : PreferenceProfile) (b : Alternative) :
  unanimous_very_bottom_choice pp b -> very_bottom_choice (constitution pp) b.
Proof.
  unfold unanimous_very_bottom_choice. unfold very_bottom_choice.
  intros.
  unfold respects_unanimity in una. apply una.
  unfold unanimously_prefers. intro.
  apply H. exact H0.
Qed.

Definition make_very_top (po : PreferenceOrder Alternative) (b : Alternative) :
relation Alternative :=
  fun (x : Alternative) => fun (y : Alternative) =>
  if x == b then True else (
    if y == b then False else non_strict po x y
  ).

Definition make_very_bottom (po : PreferenceOrder Alternative) (b : Alternative) :
relation Alternative :=
  fun (x : Alternative) => fun (y : Alternative) =>
  if y == b then True else (
    if x == b then False else non_strict po x y
  ).

Definition make_above (po : PreferenceOrder Alternative) (a b : Alternative) :
relation Alternative :=
  fun (x : Alternative) => fun (y : Alternative) =>
  if x == b then (
    if y == b then true else (
      if asbool (non_strict po a y) then true else false
    )
  ) else (
    if y == b then (
      if asbool (non_strict po a x) then false else true
    ) else asbool (non_strict po x y)
  ).

Lemma make_very_top_transitive (po : PreferenceOrder Alternative)
(b : Alternative) :
  Relation_Definitions.transitive Alternative (make_very_top po b).
Proof.
  unfold Relation_Definitions.transitive. unfold make_very_top.
  intros.
  destruct (x == b) eqn:Hxb.
  { tauto. }
  {
    destruct (y == b) eqn:Hyb.
    { tauto. }
    {
      destruct (z == b) eqn:Hzb.
      { tauto. }
      apply non_strict_transitive with (b:=y) ; tauto.
    }
  }
Qed.

Lemma make_very_bottom_transitive (po : PreferenceOrder Alternative)
(b : Alternative) :
  Relation_Definitions.transitive Alternative (make_very_bottom po b).
Proof.
  unfold Relation_Definitions.transitive. unfold make_very_bottom.
  intros.
  destruct (z == b) eqn:Hxb.
  { tauto. }
  {
    destruct (y == b) eqn:Hyb.
    { tauto. }
    {
      destruct (x == b) eqn:Hzb.
      { tauto. }
      apply non_strict_transitive with (b:=y) ; tauto.
    }
  }
Qed.

Lemma make_above_transitive (po : PreferenceOrder Alternative) (a b : Alternative) :
  Relation_Definitions.transitive Alternative (make_above po a b).
Proof.
  unfold Relation_Definitions.transitive. unfold make_above.
  intros.
  destruct (x == b) eqn:Hxb.
  {
    destruct (z == b) eqn:Hzb.
    { intuition. }
    {
      destruct (y == b) eqn:Hyb.
      { exact H0. }
      destruct (`[< non_strict po a y >]) eqn:Hay.
      {
        assert (non_strict po a y).
        { apply asboolW. intuition. }
        assert (non_strict po y z).
        { apply asboolW. exact H0. }
        assert (non_strict po a z).
        {
          apply non_strict_transitive with (b:=y) ; tauto.
        }
        assert (`[< non_strict po a z >]).
        { apply asboolT. exact H3. }
        unfold is_true in H4. rewrite H4.
        intuition.
      }
      { inversion H. }
    }
  }
  {
    destruct (z == b) eqn:Hzb.
    {
      destruct (y == b) eqn:Hyb.
      { exact H. }
      {
        destruct (`[< non_strict po a y >]) eqn:Hay.
        { inversion H0. }
        {
          assert (non_strict po x y).
          { apply asboolW. exact H. }
          assert (~ non_strict po a y).
          {
            intro. apply asboolT in H2.
            rewrite Hay in H2. inversion H2.
          }
          assert (strict po y a).
          { unfold strict. exact H2. }
          assert (strict po x a).
          { apply non_strict_strict_transitive with (b:=y) ; tauto. }
          unfold strict in H4.
          destruct (`[< non_strict po a x >]) eqn:Hax.
          {
            exfalso. apply H4.
            apply asboolW.
            rewrite Hax. intuition.
          }
          { intuition. }
        }
      }
    }
    {
      destruct (y == b) eqn:Hyb.
      {
        destruct (`[< non_strict po a x >]) eqn:Hax.
        { inversion H. }
        {
          destruct (`[< non_strict po a z >]) eqn:Haz.
          {
            apply asboolT.
            apply strict_implies_non_strict.
            apply strict_non_strict_transitive with (b:=a).
            {
              unfold strict. intro. intuition.
              assert (`[< non_strict po a x >]).
              { apply asboolT. exact H1. }
              rewrite Hax in H2. inversion H2.
            }
            {
              apply asboolW. rewrite Haz. intuition.
            }
          }
          { inversion H0. }
        }
      }
      {
        apply asboolT.
        assert (non_strict po x y).
        { apply asboolW. exact H. }
        assert (non_strict po y z).
        { apply asboolW. exact H0. }
        apply non_strict_transitive with (b:=y) ; tauto.
      }
    }
  }
Qed.

Lemma make_very_top_total (po : PreferenceOrder Alternative) (b: Alternative) :
  total (make_very_top po b).
Proof.
  unfold total. unfold make_very_top.
  intros.
  destruct po. simpl. unfold preference_order in p. destruct p.
  unfold total in H0. pose proof (H0 x y).
  destruct (x == b).
  { tauto. }
  destruct (y == b).
  { tauto. }
  tauto.
Qed.

Lemma make_very_bottom_total (po : PreferenceOrder Alternative) (b: Alternative) :
  total (make_very_bottom po b).
Proof.
  unfold total. unfold make_very_bottom.
  intros.
  destruct po. simpl. unfold preference_order in p. destruct p.
  unfold total in H0. pose proof (H0 x y).
  destruct (x == b).
  { tauto. }
  destruct (y == b).
  { tauto. }
  tauto.
Qed.

Lemma make_above_total (po : PreferenceOrder Alternative) (a b: Alternative) :
  total (make_above po a b).
Proof.
  unfold total. unfold make_above.
  intros.
  destruct po. simpl. unfold preference_order in p. destruct p.
  unfold total in H0. pose proof (H0 x y).
  destruct (x == b).
  {
    destruct (y == b).
    { intuition. }
    destruct (`[< x0 a y >]) ; intuition.
  }
  {
    destruct (y == b).
    { destruct (`[< x0 a x >]) ; intuition. }
    {
      destruct H1.
      { left. apply asboolT. exact H1. }
      { right. apply asboolT. exact H1. }
    }
  }
Qed.

Lemma make_very_top_preference_order (po : PreferenceOrder Alternative)
(b : Alternative) :
  preference_order (make_very_top po b).
Proof.
  unfold preference_order.
  split.
  - apply make_very_top_transitive.
  - apply make_very_top_total.
Qed.

Lemma make_very_bottom_preference_order (po : PreferenceOrder Alternative)
(b : Alternative) :
  preference_order (make_very_bottom po b).
Proof.
  unfold preference_order.
  split.
  - apply make_very_bottom_transitive.
  - apply make_very_bottom_total.
Qed.

Lemma make_above_preference_order (po : PreferenceOrder Alternative)
(a b : Alternative) :
  preference_order (make_above po a b).
Proof.
  unfold preference_order.
  split.
  - apply make_above_transitive.
  - apply make_above_total.
Qed.

Definition make_very_top_preference (po : PreferenceOrder Alternative)
(b : Alternative) : PreferenceOrder Alternative :=
  exist preference_order (make_very_top po b) (
    make_very_top_preference_order po b
  ).

Definition make_very_bottom_preference (po : PreferenceOrder Alternative)
(b : Alternative) : PreferenceOrder Alternative :=
  exist preference_order (make_very_bottom po b) (
    make_very_bottom_preference_order po b
  ).

Definition make_above_preference (po : PreferenceOrder Alternative)
(a b : Alternative) : PreferenceOrder Alternative :=
  exist preference_order (make_above po a b) (
    make_above_preference_order po a b
  ).

Definition make_very_top_at (pp : PreferenceProfile) (b : Alternative)
(n : Individual) : PreferenceProfile :=
  fun (i : Individual) => if i == n then (
    make_very_top_preference (pp i) b
  ) else (pp i).

Lemma make_very_top_well_named (po : PreferenceOrder Alternative)
(b : Alternative) :
  very_top_choice (make_very_top_preference po b) b.
Proof.
  intro.
  unfold make_very_top_preference. unfold make_very_top.
  unfold strict. simpl.
  intro.
  assert ((u == b) = false).
  { by apply/eqP. }
  rewrite H0.
  rewrite eq_refl.
  intuition.
Qed.

Definition make_above_profile (pp : PreferenceProfile)
(a c : Alternative) : PreferenceProfile :=
  fun (i : Individual) => make_above_preference (pp i) a c.

Lemma make_above_well_named (po : PreferenceOrder Alternative) (a b : Alternative) :
  a <> b ->
  strict (make_above_preference po a b) b a.
Proof.
  unfold make_above_preference. unfold make_above.
  unfold strict. unfold non_strict. simpl.
  assert (b == b).
  { intuition. }
  rewrite H.
  intros.
  assert ((a == b) = false).
  { by apply/eqP. }
  rewrite H1.
  intro.
  assert (non_strict po a a).
  {
    destruct po.
    specialize (preference_order_reflexive x p).
    intro. simpl in H2.
    unfold Relation_Definitions.reflexive in H3.
    specialize (H3 a).
    assert (`[< x a a >]).
    { apply asboolT. exact H3. }
    rewrite H4 in H2. inversion H2.
  }
  unfold non_strict in H3.
  assert (`[< sval po a a >]).
  { apply asboolT. exact H3. }
  rewrite H4 in H2. inversion H2.
Qed.

Lemma exists_of_not_extremal (po : PreferenceOrder Alternative) (b : Alternative)
(alt3 : #|Alternative| >= 3) (nextr : ~ very_extremal_choice po b) :
  exists (a c : Alternative),
    a <> b /\ c <> b /\ a <> c /\ non_strict po a b /\ non_strict po b c.
Proof.
  assert (exists (a c : Alternative), a <> b /\ c <> b /\ non_strict po a b /\ non_strict po b c).
  { apply not_extremal. exact nextr. }
  destruct H as [a]. destruct H as [c]. destruct H. destruct H0. destruct H1.
  assert (a <> c \/ a = c).
  { tauto. }
  destruct H3.
  { exists a. exists c. tauto. }
  {
    assert (exists (d : Alternative), d <> a /\ d <> b).
    { apply (exists_3rd_distinct a b alt3). }
    destruct H4 as [d]. destruct H4.
    assert (non_strict po b d \/ non_strict po d b).
    { 
      destruct po. destruct p. simpl. unfold total in t0.
      apply t0.
    }
    rewrite H3 in H1. rewrite H3 in H4.
    destruct H6.
    {
      specialize (not_eq_sym H4). intro. 
      exists c. exists d. tauto.
    }
    { exists d. exists c. tauto. }
  }
Qed.

Lemma extremal_lemma (constitution : Constitution) (alt3 : #|Alternative| >= 3)
(una : respects_unanimity constitution) (iia : independence_irrelevant_alternatives constitution) :
  forall (pp : PreferenceProfile) (b : Alternative),
    unanimous_very_extremal_choice pp b ->
    very_extremal_choice (constitution pp) b.
Proof.
  intros.
  apply NNPP. intro.
  specialize (exists_of_not_extremal (constitution pp) b alt3 H0). intro.
  destruct H1 as [a]. destruct H1 as [c].
  destruct H1. destruct H2. destruct H3. destruct H4.
  unfold unanimous_very_extremal_choice in H. unfold very_extremal_choice in H.
  assert (same_order (constitution pp) (constitution (make_above_profile pp a c)) a b).
  {
    apply iia.
    intro. unfold make_above_profile.
    apply same_order_characterization.
    split.
    {
      split.
      {
        intro.
        unfold make_above_preference. unfold make_above.
        unfold strict. unfold non_strict. simpl.
        assert ((b == c) = false).
        { specialize (not_eq_sym H2). intro. by apply/eqP. }
        rewrite H7.
        assert ((a == c) = false).
        { by apply/eqP. }
        rewrite H8.
        intro.
        specialize (asboolW H9). intro.
        unfold strict in H6. unfold non_strict in H6.
        apply H6. exact H10.
      }
      {
        intro.
        unfold make_above_preference in H6. unfold make_above in H6.
        unfold strict in H6. unfold non_strict in H6. simpl in H6.
        assert ((b == c) = false).
        { specialize (not_eq_sym H2). intro. by apply/eqP. }
        rewrite H7 in H6.
        assert ((a == c) = false).
        { by apply/eqP. }
        rewrite H8 in H6.
        unfold strict. intro.
        apply H6.
        unfold non_strict in H9. apply asboolT. exact H9.
      }
    }
    {
      split.
      {
        intro.
        unfold make_above_preference. unfold make_above.
        unfold strict. unfold non_strict. simpl.
        assert ((a == c) = false).
        { by apply/eqP. }
        rewrite H7.
        assert ((b == c) = false).
        { specialize (not_eq_sym H2). intro. by apply/eqP. }
        rewrite H8.
        intro.
        specialize (asboolW H9). intro.
        unfold strict in H6. unfold non_strict in H6.
        apply H6. exact H10.
      }
      {
        intro.
        unfold make_above_preference in H6. unfold make_above in H6.
        unfold strict in H6. unfold non_strict in H6. simpl in H6.
        assert ((a == c) = false).
        { by apply/eqP. }
        rewrite H7 in H6.
        assert ((b == c) = false).
        { specialize (not_eq_sym H2). intro. by apply/eqP. }
        rewrite H8 in H6.
        unfold strict. intro.
        apply H6.
        unfold non_strict in H9. apply asboolT. exact H9.
      }
    }
  }
  assert (same_order (constitution pp) (constitution (make_above_profile pp a c)) b c).
  {
    apply iia.
    intro. unfold make_above_profile.
    apply same_order_characterization.
    split.
    {
      split.
      {
        intro.
        unfold make_above_preference. unfold make_above.
        unfold strict. unfold non_strict. simpl.
        assert ((c == c) = true).
        { by apply/eqP. }
        rewrite H8.
        assert ((b == c) = false).
        { specialize (not_eq_sym H2). intro. by apply/eqP. }
        rewrite H9.
        intro.
        assert (~ sval (pp i) a b \/ sval (pp i) a b).
        { tauto. }
        destruct H11.
        {
          destruct (`[< sval (pp i) a b >]) eqn:Hab.
          { apply H11. apply asboolW. intuition. }
          { inversion H10. }
        }
        {
          destruct (H i).
          {
            unfold very_top_choice in H12.
            specialize (H12 a H1). unfold strict in H12. unfold non_strict in H12.
            apply H12. exact H11.
          }
          {
            unfold very_bottom_choice in H12.
            specialize (H12 c H2).
            apply strict_asymmetric with (a:=c) (b:=b) (po:= pp i) ; tauto.
          }
        }
      }
      {
        intro.
        unfold make_above_preference in H7. unfold make_above in H7.
        unfold strict in H7. unfold non_strict in H7. simpl in H7.
        assert ((c == c) = true).
        { by apply/eqP. }
        rewrite H8 in H7.
        assert ((b == c) = false).
        { specialize (not_eq_sym H2). intro. by apply/eqP. }
        rewrite H9 in H7.
        destruct (`[< sval (pp i) a b >]) eqn:Hab.
        {
          assert (false). { intuition. }
          inversion H10.
        }
        {
          assert (strict (pp i) b a).
          {
            unfold strict. unfold non_strict.
            intro.
            assert (`[< sval (pp i) a b >]).
            { apply asboolT. exact H10. }
            rewrite Hab in H11. inversion H11.
          }
          destruct (H i).
          { unfold very_top_choice in H11. apply (H11 c H2). }
          {
            unfold very_bottom_choice in H11. specialize (H11 a H1).
            exfalso. apply strict_asymmetric with (a:=a) (b:=b) (po:= pp i) ; tauto.
          }
        }
      }
    }
    {
      split.
      {
        intro.
        unfold make_above_preference. unfold make_above.
        unfold strict. unfold non_strict. simpl.
        assert ((c == c) = true).
        { by apply/eqP. }
        rewrite H8.
        assert ((b == c) = false).
        { specialize (not_eq_sym H2). intro. by apply/eqP. }
        rewrite H9.
        intro.
        destruct (`[< sval (pp i) a b >]) eqn:Hab.
        { inversion H10. }
        {
          assert (strict (pp i) b a).
          {
            unfold strict. unfold non_strict.
            intro.
            assert (`[< sval (pp i) a b >]).
            { apply asboolT. exact H11. }
            rewrite Hab in H12. inversion H12.
          }
          destruct (H i).
          {
            unfold very_top_choice in H12. specialize (H12 c H2).
            exfalso. apply strict_asymmetric with (a:=c) (b:=b) (po:= pp i) ; tauto.
          }
          {
            unfold very_bottom_choice in H12. specialize (H12 a H1).
            exfalso. apply strict_asymmetric with (a:=a) (b:=b) (po:= pp i) ; tauto.
          }
        }
      }
      {
        intro.
        unfold make_above_preference in H7. unfold make_above in H7.
        unfold strict in H7. unfold non_strict in H7. simpl in H7.
        assert ((c == c) = true).
        { by apply/eqP. }
        rewrite H8 in H7.
        assert ((b == c) = false).
        { specialize (not_eq_sym H2). intro. by apply/eqP. }
        rewrite H9 in H7.
        destruct (`[< sval (pp i) a b >]) eqn:Hab.
        {
          destruct (H i).
          {
            unfold very_top_choice in H10. specialize (H10 a H1).
            assert (non_strict (pp i) a b).
            {
              unfold non_strict. unfold strict.
              apply asboolW. intuition.
            }
            exfalso. unfold strict in H10.
            apply H10. exact H11.
          }
          { unfold very_bottom_choice in H10. apply (H10 c H2). }
        }
        {
          assert (false). { intuition. }
          inversion H10.
        }
      }
    }
  }
  assert (non_strict (constitution (make_above_profile pp a c)) a b).
  { apply same_order_non_strict with (po1:= constitution pp) ; tauto. }
  assert (non_strict (constitution (make_above_profile pp a c)) b c).
  { apply same_order_non_strict with (po1:= constitution pp) ; tauto. }
  specialize (non_strict_transitive (constitution (make_above_profile pp a c)) a b c H8 H9).
  intro.
  assert (strict (constitution (make_above_profile pp a c)) c a).
  {
    apply una.
    unfold unanimously_prefers. intro.
    unfold make_above_profile.
    apply make_above_well_named. exact H3.
  }
  unfold strict in H11.
  apply H11. exact H10.
Qed.

Definition is_pivotal (constitution : Constitution) (i : Individual)
(b : Alternative) : Prop :=
  exists (pp pp' : PreferenceProfile),
    (forall (j : Individual), j != i -> pp j = pp' j) /\
    (forall (j : Individual), very_extremal_choice (pp j) b) /\
    (forall (j : Individual), very_extremal_choice (pp' j) b) /\
    very_bottom_choice (pp i) b /\
    very_top_choice (pp' i) b /\
    very_bottom_choice (constitution pp) b /\
    very_top_choice (constitution pp') b.

Definition has_pivot (constitution : Constitution) (b : Alternative): Prop := 
  exists (i : Individual), is_pivotal constitution i b.

Lemma exists_pivot_when_hater (constitution : Constitution)
(una : respects_unanimity constitution)
(iia : independence_irrelevant_alternatives constitution)
(alt3 : #|Alternative| >= 3) (b : Alternative) :
  forall (bHater : finType) (pp : PreferenceProfile),
    bHater = ({i : Individual | asbool (very_bottom_choice (pp i) b)} : finType) ->
    (forall (i : Individual), very_extremal_choice (pp i) b) ->
    very_bottom_choice (constitution pp) b ->
    has_pivot constitution b.
Proof.
  apply (induction_cardinal (fun (bHater : finType) =>
    forall (pp : PreferenceProfile),
      bHater = ({i : Individual | asbool (very_bottom_choice (pp i) b)} : finType) ->
      (forall (i : Individual), very_extremal_choice (pp i) b) ->
      very_bottom_choice (constitution pp) b ->
      has_pivot constitution b
  )).
  {
    intros.
    assert (T =i pred0).
    { apply card0_eq. exact H. }
    unfold pred0 in H3. unfold mem in H3. simpl in H3. unfold eq_mem in H3.
    unfold in_mem in H3. simpl in H3.
    rewrite H0 in H3.
    assert (forall (i : Individual), ~ very_bottom_choice (pp i) b).
    {
      unfold not. intros.
      assert (asbool (very_bottom_choice (pp i) b)).
      { apply asboolT. exact H4. }
      assert ({i : Individual | `[< very_bottom_choice (pp i) b >]}).
      { apply exist with (x:=i). exact H5. }
      apply H3 in X. inversion X.
    }
    unfold very_extremal_choice in H1.
    assert (forall i : Individual, very_top_choice (pp i) b).
    {
      intro.
      pose proof (H1 i). destruct H5.
      { exact H5. }
      pose proof (H4 i).
      exfalso. apply H6 in H5. inversion H5.
    }
    apply unanimous_very_top with (constitution:=constitution) in H5.
    2: { apply una. }
    unfold very_bottom_choice in H2. unfold very_top_choice in H5.
    assert (exists (x y : Alternative), x <> y).
    { apply exists_two_distinct. intuition. }
    destruct H6. destruct H6 as [y].
    assert (x <> b \/ y <> b).
    {
      rewrite <- implyNp. intro.
      unfold not in H7. apply NNPP in H7. rewrite H7 in H6.
      intuition.
    }
    destruct H7.
    {
      pose proof (H5 x). pose proof (H2 x).
      pose proof (H8 H7). pose proof (H9 H7).
      exfalso.
      apply strict_asymmetric with (po := constitution pp) (a:=b) (b:=x) ; tauto.
    }
    {
      pose proof (H5 y). pose proof (H2 y).
      pose proof (H8 H7). pose proof (H9 H7).
      exfalso.
      apply strict_asymmetric with (po := constitution pp) (a:=b) (b:=y) ; tauto.
    }
  }
  {
    intros.
    assert (0 < #|T|).
    { rewrite H0. intuition. }
    assert (exists (t : T), True).
    { exists (enum_val (Ordinal H4)). tauto. }
    destruct H5 as [t]. clear H5.
    rewrite H1 in t.
    assert (exists (i : Individual), `[< very_bottom_choice (pp i) b >]).
    { exists (proj1_sig t). apply (proj2_sig t). }
    destruct H5 as [i0].
    assert (
      very_bottom_choice (constitution (make_very_top_at pp b i0)) b \/
      ~ very_bottom_choice (constitution (make_very_top_at pp b i0)) b
    ).
    { tauto. }
    destruct H6.
    {
      pose proof (
        H
        {i : Individual | `[< very_bottom_choice (make_very_top_at pp b i0 i) b >]}
      ).
      rewrite H1 in H0. unfold is_true in H5.
      assert (forall (i : Individual),
        very_bottom_choice (make_very_top_at pp b i0 i) b <->
        (very_bottom_choice (pp i) b /\ i != i0)
      ).
      {
        intro. split ; intro.
        {
          split.
          {
            assert (i = i0 \/ i <> i0).
            { tauto. }
            destruct H9.
            {
              rewrite H9 in H8. unfold make_very_top_at in H8.
              assert ((i0 == i0) = true).
              { rewrite eq_refl. reflexivity. }
              rewrite H10 in H8.
              assert (very_top_choice (make_very_top_preference (pp i0) b) b).
              { apply make_very_top_well_named. }
              assert (~ (
                very_bottom_choice (make_very_top_preference (pp i0) b) b /\
                very_top_choice (make_very_top_preference (pp i0) b) b
              )).
              {
                apply not_very_top_or_not_very_bottom.
                apply leq_ltn_trans with (n:= 2).
                - easy.
                - exact alt3.
              }
              tauto.
            }
            {
              unfold make_very_top_at in H8.
              destruct (i == i0) eqn:Eii0.
              {
                unfold not in H9. exfalso.
                apply H9. rewrite <- eq_opE. rewrite Eii0.
                intuition.
              }
              { exact H8. }
            }
          }
          {
            unfold negb.
            unfold make_very_top_at in H8.
            destruct (i == i0) eqn:Eii0.
            {
              assert (very_top_choice (make_very_top_preference (pp i0) b) b).
              { apply make_very_top_well_named. }
              assert (i = i0).
              { rewrite <- eq_opE. rewrite Eii0. intuition. }
              rewrite H10 in H8.
              assert (~ (
                very_bottom_choice (make_very_top_preference (pp i0) b) b /\
                very_top_choice (make_very_top_preference (pp i0) b) b
              )).
              {
                apply not_very_top_or_not_very_bottom.
                apply leq_ltn_trans with (n:= 2).
                - easy.
                - exact alt3.
              }
              tauto.
            }
            intuition.
          }
        }
        {
          destruct H8.
          unfold make_very_top_at.
          unfold negb in H9.
          destruct (i == i0) eqn:Eii0.
          { inversion H9. }
          { exact H8. }
        }
      }
      assert (
        (
          fun  (i : Individual) =>
          `[< very_bottom_choice (make_very_top_at pp b i0 i) b >]
        ) = (
          fun  (i : Individual) =>
          `[< very_bottom_choice (pp i) b /\ i != i0 >]
        )
      ).
      {
        apply functional_extensionality.
        intro.
        apply asbool_equiv_eq.
        apply H8.
      }
      assert (
        (
          fun (x : Individual) =>
          `[< very_bottom_choice (pp x) b /\ x != i0 >]
        ) = (
          fun (x : Individual) =>
          `[< very_bottom_choice (pp x) b >] && `[< x != i0 >]
        )
      ).
      {
        apply functional_extensionality. intro.
        rewrite asbool_and.
        reflexivity.
      }
      rewrite H10 in H9.
      assert (
        #|[predI (
          fun i => `[< very_bottom_choice (pp i) b >]) & (fun i => i == i0
        )]| +
        #|[predD (
          fun i => `[< very_bottom_choice (pp i) b >]) & (fun i => i == i0
        )]| =
        #|fun i : Individual => `[< very_bottom_choice (pp i) b >]| 
      ).
      { apply cardID. }
      unfold predI in H11. unfold predD in H11. unfold SimplPred in H11.
      rewrite card_sig in H0. unfold SimplPred in H0. rewrite H0 in H11.
      assert (
        (
          fun x => (x  \notin eq_op^~ i0) && (x  \in (
            fun i : Individual => `[< very_bottom_choice (pp i) b >]
          ))
        ) =
        fun x : Individual => `[< very_bottom_choice (pp x) b >] && `[< x != i0 >]
      ).
      {
        apply functional_extensionality. intro.
        unfold in_mem. unfold mem. simpl.
        rewrite andb_comm.
        assert ((x != i0) = `[< (x != i0) >]).
        { rewrite  asboolb. reflexivity. }
        rewrite <- H12.
        reflexivity.
      }
      rewrite H12 in H11. rewrite <- H9 in H11.
      assert (
        (
          fun x => if x  \in (
            fun i : Individual => `[< very_bottom_choice (pp i) b >]
          ) then x \in eq_op^~ i0 else false
        ) = (fun x => x == i0)
      ).
      {
        apply functional_extensionality. intro.
        destruct (
          x  \in (fun i : Individual => `[< very_bottom_choice (pp i) b >])
        ) eqn:H13.
        { intuition. }
        destruct (x == i0) eqn:Exi0.
        {
          assert (x = i0).
          { by apply/eqP. }
          unfold in_mem in H13. unfold mem in H13. simpl in H13.
          rewrite H14 in H13. rewrite H5 in H13.
          inversion H13.
        }
        { reflexivity. }
      }
      rewrite H13 in H11.
      assert (#|pred1 i0| = 1).
      { apply card1. }
      unfold pred1 in H14. rewrite H14 in H11.
      rewrite add1n in H11. apply Nat.succ_inj in H11.
      assert (#|{i : Individual | `[< very_bottom_choice (
        make_very_top_at pp b i0 i
      ) b >]}: finType| = n).
      {
        rewrite card_sig. unfold SimplPred.
        exact H11.
      }
      specialize (H7 H15 (make_very_top_at pp b i0)).
      assert (
        (
          forall i : Individual, very_extremal_choice (
            make_very_top_at pp b i0 i
          ) b) ->
          very_bottom_choice (constitution (make_very_top_at pp b i0)) b ->
          has_pivot constitution b
      ).
      { apply H7. reflexivity. }
      assert ((forall i : Individual, very_extremal_choice (
        make_very_top_at pp b i0 i
      ) b)).
      {
        intro. pose proof (H2 i).
        unfold make_very_top_at.
        destruct (i == i0) eqn:Eii0.
        {
          assert (i = i0).
          { by apply/eqP. }
          rewrite H18.
          unfold very_extremal_choice. left.
          apply make_very_top_well_named.
        }
        { exact H17. }
      }
      specialize (H16 H17). specialize (H16 H6). exact H16.
    }
    {
      specialize (
        extremal_lemma
        constitution alt3 una iia (make_very_top_at pp b i0) b
      ).
      intros.
      unfold unanimous_very_extremal_choice in H7.
      assert (forall i : Individual, very_extremal_choice (
        make_very_top_at pp b i0 i
      ) b).
      {
        intro.
        destruct (i == i0) eqn:Eii0.
        {
          assert (i = i0).
          { by apply/eqP. }
          rewrite H8.
          unfold very_extremal_choice. left.
          unfold make_very_top_at.
          assert ((i0 == i0) = true).
          { rewrite eq_refl. reflexivity. }
          rewrite H9.
          apply make_very_top_well_named.
        }
        {
          unfold make_very_top_at.
          rewrite Eii0.
          apply H2.
        }
      }
      specialize (H7 H8).
      unfold has_pivot. exists i0.
      unfold is_pivotal. exists pp. exists (make_very_top_at pp b i0).
      repeat split.
      {
        intros.
        unfold make_very_top_at.
        destruct (j == i0) eqn:Eji0.
        { inversion H9. }
        { reflexivity. }
      }
      { exact H2. }
      { exact H8. }
      { rewrite asboolE in H5. exact H5. }
      {
        unfold make_very_top_at.
        assert ((i0 == i0) = true).
        { rewrite eq_refl. reflexivity. }
        rewrite H9.
        apply make_very_top_well_named.
      }
      { exact H3. }
      { unfold very_extremal_choice in H7. tauto. }
    }
  }
Qed.

Definition single_min_all_others_indifferent_preference_profile
(b : Alternative) : PreferenceProfile :=
  fun (i : Individual) => single_bottom_others_indifferent b.

Lemma exists_pivot (constitution : Constitution)
(una : respects_unanimity constitution)
(iia : independence_irrelevant_alternatives constitution)
(alt3 : #|Alternative| >= 3) (b : Alternative) :
  has_pivot constitution b.
Proof.
  apply exists_pivot_when_hater with
  (bHater := {
    i : Individual |
    `[< very_bottom_choice (
      single_min_all_others_indifferent_preference_profile b i
    ) b >]})
  (pp := (single_min_all_others_indifferent_preference_profile b)) ; try tauto.
  assert (forall i : Individual, very_bottom_choice (
    single_min_all_others_indifferent_preference_profile b i
  ) b).
  {
    intro.
    unfold single_min_all_others_indifferent_preference_profile.
    apply single_bottom_very_bottom.
  }
  {
    intro.
    unfold very_extremal_choice. right.
    apply H.
  }
  {
    apply unanimous_very_bottom.
    { exact una. }
    {
      unfold unanimous_very_bottom_choice.
      intro.
      apply single_bottom_very_bottom.
    }
  }
Qed.

Definition pp' (i : Individual) (pp pp1 : PreferenceProfile)
(a b : Alternative) : PreferenceProfile :=
  fun (j : Individual) => (
    if j == i then make_above_preference (pp j) a b else (
        if `[< very_bottom_choice (pp1 j) b >]
        then make_very_bottom_preference (pp j) b
        else make_very_top_preference (pp j) b
      )
    ).

Lemma pivot_implies_dictator_except (constitution : Constitution)
(iia : independence_irrelevant_alternatives constitution) (b : Alternative)
(i : Individual) (i_piv : is_pivotal constitution i b) :
  dictator_except constitution i b.
Proof.
  unfold dictator_except. intros.
  unfold is_pivotal in i_piv. destruct i_piv as [pp1]. destruct H2 as [pp2].
  destruct H2. destruct H3. destruct H4. destruct H5. destruct H6. destruct H7.
  assert (
    forall j, j <> i ->
    very_bottom_choice (pp1 j) b ->
    pp' i pp pp1 a b j = make_very_bottom_preference (pp j) b
  ).
  {
    unfold pp'. intros.
    destruct (j == i) eqn:Eji.
    {
      exfalso. apply H9.
      { by apply/eqP. }
    }
    assert (`[< very_bottom_choice (pp1 j) b >]).
    { apply asboolT. exact H10. }
    rewrite H11.
    reflexivity.
  }
  assert (
    forall j, j <> i ->
    ~ very_bottom_choice (pp1 j) b ->
    pp' i pp pp1 a b j = make_very_top_preference (pp j) b
  ).
  {
    unfold pp'. intros.
    destruct (j == i) eqn:Eji.
    {
      exfalso. apply H10.
      { by apply/eqP. }
    }
    destruct (`[< very_bottom_choice (pp1 j) b >]) eqn:Hb.
    {
      exfalso. apply H11.
      apply asboolW. intuition.
    }
    reflexivity.
  }
  assert (
    pp' i pp pp1 a b i = make_above_preference (pp i) a b
  ).
  {
    unfold pp'.
    assert ((i == i) = true).
    { by apply/eqP. }
    rewrite H11. reflexivity.
  }
  assert ( forall (j : Individual),
    same_order (pp j) (pp' i pp pp1 a b j ) c a
  ).
  {
    unfold pp'. intros.
    rewrite same_order_characterization.
    unfold make_above_preference. unfold make_above.
    unfold strict. unfold non_strict.
    destruct (j == i) eqn:Eji.
    {
      split.
      {
        split.
        {
          intros.
          simpl. intro.
          destruct (a == b) eqn:Eab.
          { apply H. by apply/eqP. }
          destruct (c == b) eqn:Ecb.
          { apply H0. by apply/eqP. }
          assert (non_strict (pp j) a c).
          {
            apply asboolW.
            unfold non_strict.
            exact H13.
          }
          apply H12. apply asboolW. exact H13.
        }
        {
          simpl.
          intros. intro.
          destruct (a == b) eqn:Eab.
          { apply H. by apply/eqP. }
          destruct (c == b) eqn:Ecb.
          { apply H0. by apply/eqP. }
          apply H12. apply asboolT. exact H13.
        }
      }
      {
        split.
        {
          intros.
          simpl. intro.
          destruct (a == b) eqn:Eab.
          { apply H. by apply/eqP. }
          destruct (c == b) eqn:Ecb.
          { apply H0. by apply/eqP. }
          apply H12. apply asboolW. exact H13.
        }
        {
          simpl.
          intros. intro.
          destruct (a == b) eqn:Eab.
          { apply H. by apply/eqP. }
          destruct (c == b) eqn:Ecb.
          { apply H0. by apply/eqP. }
          apply H12. apply asboolT. exact H13.
        }
      }
    }
    {
      split.
      {
        split.
        {
          intros.
          destruct (`[< very_bottom_choice (pp1 j) b >]) eqn:Hb.
          {
            intro.
            unfold make_very_bottom_preference in H13.
            unfold make_very_bottom in H13.
            simpl in H13.
            destruct (c == b) eqn:Ecb.
            { apply H0. by apply/eqP. }
            destruct (a == b) eqn:Eab.
            { apply H. by apply/eqP. }
            unfold non_strict in H13.
            apply H12. exact H13.
          }
          {
            intro.
            unfold make_very_top_preference in H13. unfold make_very_top in H13.
            simpl in H13.
            destruct (c == b) eqn:Ecb.
            { apply H0. by apply/eqP. }
            destruct (a == b) eqn:Eab.
            { apply H. by apply/eqP. }
            unfold non_strict in H13.
            apply H12. exact H13.
          }
        }
        {
          intros.
          destruct (`[< very_bottom_choice (pp1 j) b >]) eqn:Hb.
          {
            intro.
            unfold make_very_bottom_preference in H12.
            unfold make_very_bottom in H12.
            simpl in H12.
            destruct (c == b) eqn:Ecb.
            { apply H0. by apply/eqP. }
            destruct (a == b) eqn:Eab.
            { apply H. by apply/eqP. }
            unfold non_strict in H12.
            apply H12. exact H13.
          }
          {
            intro.
            unfold make_very_top_preference in H12. unfold make_very_top in H12.
            simpl in H12.
            destruct (c == b) eqn:Ecb.
            { apply H0. by apply/eqP. }
            destruct (a == b) eqn:Eab.
            { apply H. by apply/eqP. }
            unfold non_strict in H12.
            apply H12. exact H13.
          }
        }
      }
      {
        split.
        {
          intros.
          destruct (`[< very_bottom_choice (pp1 j) b >]) eqn:Hb.
          {
            intro.
            unfold make_very_bottom_preference in H13.
            unfold make_very_bottom in H13.
            simpl in H13.
            destruct (c == b) eqn:Ecb.
            { apply H0. by apply/eqP. }
            destruct (a == b) eqn:Eab.
            { apply H. by apply/eqP. }
            unfold non_strict in H13.
            apply H12. exact H13.
          }
          {
            intro.
            unfold make_very_top_preference in H13. unfold make_very_top in H13.
            simpl in H13.
            destruct (c == b) eqn:Ecb.
            { apply H0. by apply/eqP. }
            destruct (a == b) eqn:Eab.
            { apply H. by apply/eqP. }
            unfold non_strict in H13.
            apply H12. exact H13.
          }
        }
        {
          intros.
          destruct (`[< very_bottom_choice (pp1 j) b >]) eqn:Hb.
          {
            intro.
            unfold make_very_bottom_preference in H12.
            unfold make_very_bottom in H12.
            simpl in H12.
            destruct (c == b) eqn:Ecb.
            { apply H0. by apply/eqP. }
            destruct (a == b) eqn:Eab.
            { apply H. by apply/eqP. }
            unfold non_strict in H12.
            apply H12. exact H13.
          }
          {
            intro.
            unfold make_very_top_preference in H12. unfold make_very_top in H12.
            simpl in H12.
            destruct (c == b) eqn:Ecb.
            { apply H0. by apply/eqP. }
            destruct (a == b) eqn:Eab.
            { apply H. by apply/eqP. }
            unfold non_strict in H12.
            apply H12. exact H13.
          }
        }
      }
    }
  }
  assert (same_order (constitution pp) (constitution (pp' i pp pp1 a b)) c a).
  {
    apply iia.
    unfold unanimously_same_order. exact H12.
  }
  unfold same_order in H13. destruct H13. destruct H14. rewrite H13.
  apply strict_transitive with (b:=b).
  {
    assert (strict (constitution pp1) c b).
    { unfold very_bottom_choice in H7. apply H7. exact H0. }
    assert (same_order (constitution pp1) (constitution (pp' i pp pp1 a b)) c b).
    {
      apply iia.
      unfold unanimously_same_order. intro j.
      assert (j = i \/ j <> i).
      { tauto. }
      destruct H17.
      {
        rewrite H17.
        assert (strict (pp1 i) c b).
        { unfold very_bottom_choice in H5. apply H5. exact H0. }
        assert (strict (pp' i pp pp1 a b i) c b).
        {
          unfold pp'.
          assert ((i == i) = true).
          { by apply/eqP. }
          rewrite H19.
          unfold make_above_preference. unfold make_above.
          unfold strict. unfold non_strict. simpl.
          assert ((b == b) = true).
          { by apply/eqP. }
          rewrite H20.
          assert ((c == b) = false).
          { by apply/eqP. }
          rewrite H21.
          unfold strict in H1. unfold non_strict in H1.
          destruct `[< sval (pp i) a c >] eqn:Hac.
          {
            exfalso. apply H1.
            apply asboolW. intuition.
          }
          { intuition. }
        }
        apply same_order_strict_case ; tauto.
      }
      {
        assert (very_bottom_choice (pp1 j) b \/ ~ very_bottom_choice (pp1 j) b).
        { tauto. }
        destruct H18.
        {
          specialize (H9 j H17 H18).
          unfold very_bottom_choice in H18.
          specialize (H18 c H0).
          assert (strict (pp' i pp pp1 a b j) c b).
          {
            rewrite H9.
            unfold make_very_bottom_preference. unfold make_very_bottom.
            unfold strict. unfold non_strict. simpl.
            intro.
            assert ((c == b) = false).
            { by apply/eqP. }
            rewrite H20 in H19.
            assert ((b == b) = true).
            { by apply/eqP. }
            rewrite H21 in H19. inversion H19.
          }
          apply same_order_strict_case ; tauto.
        }
        {
          specialize (H3 j). unfold very_extremal_choice in H3.
          assert (very_top_choice (pp1 j) b).
          { tauto. }
          specialize (H10 j H17 H18).
          unfold very_top_choice in H19.
          specialize (H19 c H0).
          assert (strict (pp' i pp pp1 a b j) b c).
          {
            rewrite H10.
            unfold make_very_top_preference. unfold make_very_top.
            unfold strict. unfold non_strict. simpl.
            intro.
            assert ((c == b) = false).
            { by apply/eqP. }
            rewrite H21 in H20.
            assert ((b == b) = true).
            { by apply/eqP. }
            rewrite H22 in H20. inversion H20.
          }
          apply same_order_symmetric. apply same_order_strict_case ; tauto.
        }
      }
    }
    { unfold same_order in H17. tauto. }
  }
  {
    assert (strict (constitution pp2) b a).
    { unfold very_top_choice in H8. apply H8. exact H. }
    assert (same_order (constitution pp2) (constitution (pp' i pp pp1 a b)) b a).
    {
      apply iia.
      unfold unanimously_same_order. intro j.
      assert (j = i \/ j <> i).
      { tauto. }
      destruct H17.
      {
        rewrite H17.
        assert (strict (pp2 i) b a).
        { unfold very_top_choice in H6. apply H6. exact H. }
        assert (strict (pp' i pp pp1 a b i) b a).
        {
          unfold pp'.
          assert ((i == i) = true).
          { by apply/eqP. }
          rewrite H19.
          unfold make_above_preference. unfold make_above.
          unfold strict. unfold non_strict. simpl.
          assert ((b == b) = true).
          { by apply/eqP. }
          rewrite H20.
          assert ((a == b) = false).
          { by apply/eqP. }
          rewrite H21.
          intro.
          destruct (pp i) as [po]. simpl in H22.
          assert (Relation_Definitions.reflexive Alternative po).
          { apply preference_order_reflexive. exact p. }
          unfold Relation_Definitions.reflexive in H23.
          specialize (H23 a).
          assert (`[< po a a >] = true).
          { apply asboolT. exact H23. }
          rewrite H24 in H22. inversion H22.
        }
        apply same_order_strict_case ; tauto.
      }
      {
        assert (very_bottom_choice (pp1 j) b \/ ~ very_bottom_choice (pp1 j) b).
        { tauto. }
        destruct H18.
        {
          specialize (H9 j H17 H18).
          unfold very_bottom_choice in H18.
          specialize (H18 a H).
          assert (strict (pp' i pp pp1 a b j) a b).
          {
            rewrite H9.
            unfold make_very_bottom_preference. unfold make_very_bottom.
            unfold strict. unfold non_strict. simpl.
            intro.
            assert ((a == b) = false).
            { by apply/eqP. }
            rewrite H20 in H19.
            assert ((b == b) = true).
            { by apply/eqP. }
            rewrite H21 in H19. inversion H19.
          }
          assert (j != i).
          { by apply/eqP. }
          specialize (H2 j H20). rewrite H2 in H18.
          apply same_order_symmetric. apply same_order_strict_case ; tauto.
        }
        {
          specialize (H3 j). unfold very_extremal_choice in H3.
          assert (very_top_choice (pp1 j) b).
          { tauto. }
          specialize (H10 j H17 H18).
          unfold very_top_choice in H19.
          specialize (H19 a H).
          assert (strict (pp' i pp pp1 a b j) b a).
          {
            rewrite H10.
            unfold make_very_top_preference. unfold make_very_top.
            unfold strict. unfold non_strict. simpl.
            intro.
            assert ((b == b) = true).
            { by apply/eqP. }
            rewrite H21 in H20.
            assert ((a == b) = false).
            { by apply/eqP. }
            rewrite H22 in H20. inversion H20.
          }
          assert (j != i).
          { by apply/eqP. }
          specialize (H2 j H21). rewrite H2 in H19.
          apply same_order_strict_case ; tauto.
        }
      }
    }
    { unfold same_order in H17. tauto. }
  }
Qed.

Definition third_alt (alt3 : #|Alternative| >= 3) : Alternative :=
  enum_val (Ordinal (n:=#|Alternative|) (m:=2) alt3).

Lemma pivot_implies_dictator (constitution : Constitution)
(iia : independence_irrelevant_alternatives constitution)
(alt3 : #|Alternative| >= 3)
(h_piv : forall (b : Alternative), has_pivot constitution b) :
  exists (i : Individual), dictator constitution i.
Proof.
  pose proof (h_piv (third_alt alt3)).
  unfold has_pivot in H. destruct H as [i].
  assert (forall(a : Alternative), a <> third_alt alt3 ->
    forall (pp : PreferenceProfile),
      (strict (pp i) a (third_alt alt3) -> strict (constitution pp) a (third_alt alt3)) /\
      (strict (pp i) (third_alt alt3) a -> strict (constitution pp) (third_alt alt3) a)
  ).
  {
    intros.
    specialize (exists_3rd_distinct a (third_alt alt3) alt3). intro.
    destruct H1 as [c]. destruct H1.
    pose proof (h_piv c).
    unfold has_pivot in H3. destruct H3 as [j].
    specialize (pivot_implies_dictator_except constitution iia c j H3). intro.
    assert (j <> i \/ j = i).
    { tauto. }
    destruct H5.
    {
      unfold is_pivotal in H.
      destruct H as [pp1]. destruct H as [pp2].
      destruct H. destruct H6. destruct H7. destruct H8. destruct H9. destruct H10.
      specialize (not_eq_sym H2). intro.
      specialize (not_eq_sym H1). intro.
      unfold dictator_except in H4.
      pose proof (H4 (third_alt alt3) a H12 H13 pp2).
      pose proof (H4 a (third_alt alt3) H13 H12 pp1).
      unfold very_top_choice in H11. pose proof (H11 a H0).
      assert (~ strict (constitution pp2) a (third_alt alt3)).
      {
        intro.
        apply strict_asymmetric with (po:= constitution pp2) (a:=a) (b:= third_alt alt3) ;
        tauto.
      }
      assert (~ strict (pp2 j) a (third_alt alt3)).
      { tauto. }
      unfold very_bottom_choice in H10. pose proof (H10 a H0).
      assert (~ strict (constitution pp1) (third_alt alt3) a).
      {
        intro.
        apply strict_asymmetric with (po:= constitution pp1) (a:=a) (b:= third_alt alt3) ;
        tauto.
      }
      assert (~ strict (pp1 j) (third_alt alt3) a).
      { tauto. }
      assert (j != i).
      { by apply/eqP. }
      specialize (H j H22). rewrite H in H21.
      specialize (H7 j). unfold very_extremal_choice in H7. destruct H7.
      {
        unfold very_top_choice in H7. specialize (H7 a H0).
        exfalso. apply H21. exact H7.
      }
      {
        unfold very_bottom_choice in H7. specialize (H7 a H0).
        exfalso. apply H18. exact H7.
      }
    }
    {
      split.
      - unfold dictator_except in H4.
        specialize (not_eq_sym H1). intro.
        specialize (not_eq_sym H2). intro.
        specialize (H4 (third_alt alt3) a H7 H6).
        rewrite H5 in H4. apply H4.
      - unfold dictator_except in H4.
        specialize (not_eq_sym H1). intro.
        specialize (not_eq_sym H2). intro.
        specialize (H4 a (third_alt alt3) H6 H7).
        rewrite H5 in H4. apply H4.
    }
  }
  exists i. unfold dictator. intros.
  assert (third_alt alt3 = a \/ third_alt alt3 <> a).
  { tauto. }
  assert (third_alt alt3 = b \/ third_alt alt3 <> b).
  { tauto. }
  destruct H2.
  {
    destruct H3.
    {
      rewrite H2 in H3. rewrite H3 in H1.
      assert (~ strict (pp i) b b).
      { apply strict_never_reflexive. }
      exfalso. apply H4. exact H1.
    }
    {
      rewrite H2 in H0. rewrite H2 in H3.
      specialize (not_eq_sym H3). intro. specialize (H0 b H4 pp).
      tauto.
    }
  }
  {
    destruct H3.
    {
      rewrite H3 in H0. rewrite H3 in H2.
      specialize (not_eq_sym H2). intro. specialize (H0 a H4 pp).
      tauto.
    }
    {
      specialize (pivot_implies_dictator_except constitution iia (third_alt alt3) i H).
      intro.
      unfold dictator_except in H4.
      specialize (not_eq_sym H3). intro.
      specialize (not_eq_sym H2). intro.
      specialize (H4 b a H5 H6).
      apply H4. exact H1.
    }
  }
Qed.

Theorem Arrow : forall (constitution : Constitution),
  #|Alternative| >= 3 ->
  respects_unanimity constitution ->
  independence_irrelevant_alternatives constitution ->
  exists (n : Individual), dictator constitution n.
Proof.
  intros.
  apply pivot_implies_dictator ; try tauto.
  intro.
  apply exists_pivot ; try tauto.
Qed.

End arrow_theorem.
