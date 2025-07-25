
Require Import Classical_Pred_Type.
From mathcomp Require Import all_ssreflect.

Require Import ethics_first_steps.
Require Import every_ethic_without_dead_end_is_utilitarian.
Require Import ethics_in_society.

Section more_restrictive_ethics_diminish_conflicts.

Context {State : Type}.
Context {Action : Type}.
Context {Individual : finType}.
Context {feasible : State -> @ActionProfile Action Individual -> bool}.

Definition compatible (ap : @ActionProfile Action Individual) (state : State) : Prop :=
  feasible state ap = true.

Definition incompatible (ap : @ActionProfile Action Individual) (state : State) :
Prop :=
  feasible state ap = false.

Definition with_constraints
(feasible : State -> @ActionProfile Action Individual -> bool)
(state : State) : Prop :=
  exists (ap : @ActionProfile Action Individual), incompatible ap state.

Definition everyone_follows_its_ethic (ep : EthicalProfile)
(ap : @ActionProfile Action Individual) (state : State) : Prop :=
  forall (i : Individual), ep i (get_SubjectiveState state i) (ap i) = true.

Lemma no_dead_end_if_everyone_follows_its_ethic (ep : EthicalProfile)
(ap : @ActionProfile Action Individual) (state : State) :
  everyone_follows_its_ethic ep ap state ->
  forall (i : Individual), ~ dead_end (ep i) (get_SubjectiveState state i).
Proof.
  unfold everyone_follows_its_ethic. intros. unfold dead_end.
  specialize (H i).
  apply ex_not_not_all.
  exists (ap i). rewrite H. intuition.
Qed.

Definition conflict (ep : EthicalProfile) (ap : @ActionProfile Action Individual)
(state : State) : Prop :=
  feasible state ap = false /\
  everyone_follows_its_ethic ep ap state.

Definition no_conflict (ep : EthicalProfile) (ap : @ActionProfile Action Individual)
(state : State) : Prop :=
  feasible state ap = true /\
  everyone_follows_its_ethic ep ap state.

Definition no_dead_end_if_conflict (ep : EthicalProfile)
(ap : @ActionProfile Action Individual) (state : State) :
  conflict ep ap state ->
  forall (i : Individual), ~ dead_end (ep i) (get_SubjectiveState state i).
Proof.
  unfold conflict. intro.
  destruct H.
  apply no_dead_end_if_everyone_follows_its_ethic with (ap:=ap). exact H0.
Qed.

Definition no_dead_end_if_no_conflict (ep : EthicalProfile)
(ap : @ActionProfile Action Individual) (state : State) :
  no_conflict ep ap state ->
  forall (i : Individual), ~ dead_end (ep i) (get_SubjectiveState state i).
Proof.
  unfold no_conflict. intro.
  destruct H.
  apply no_dead_end_if_everyone_follows_its_ethic with (ap:=ap). exact H0.
Qed.

Proposition more_restrictive_ethic_diminishes_conflicts (ep : EthicalProfile)
(ap : @ActionProfile Action Individual) (i : Individual)
(ethic : @IndividualEthic State Action Individual) (state : State) :
  more_restrictive (ep i) ethic (get_SubjectiveState state i) ->
  conflict ep ap state ->
  conflict (replace_individual_ethic ep i ethic) ap state.
Proof.
  intros. unfold conflict in *.
  destruct H0. split.
  { apply H0. }
  intro. unfold replace_individual_ethic.
  destruct (i0 == i) eqn:H2.
  2: { apply H1. }
  assert (i0 = i).
  { by apply/eqP. }
  rewrite H3.
  unfold more_restrictive in H. pose proof (H (ap i)).
  apply H4.
  apply H1.
Qed.

Proposition more_restrictive_ethic_strictly_diminishes_conflicts (state : State)
(i : Individual) :
  with_constraints feasible state ->
  exists (ap : @ActionProfile Action Individual) (ep : EthicalProfile)
  (ethic : @IndividualEthic State Action Individual),
    strictly_more_restrictive (ep i) ethic (get_SubjectiveState state i) /\
    ~ conflict ep ap state /\
    conflict (replace_individual_ethic ep i ethic) ap state.
Proof.
  intro. unfold with_constraints in H. destruct H as [ap].
  exists (ap).
  exists (
    fun (j : Individual) =>
    fun (subj_state : SubjectiveState) =>
    fun (action : Action) =>
    if j == i then false else true
  ).
  exists (
    fun (subj_state : SubjectiveState) =>
    fun (action : Action) =>
    true
  ).
  split.
  {
    unfold strictly_more_restrictive.
    split.
    {
      unfold more_restrictive.
      intro.
      reflexivity.
    }
    {
      exists (ap i).
      split.
      {
        rewrite eq_refl.
        reflexivity.
      }
      { reflexivity. }
    }
  }
  unfold conflict.
  split.
  {
    intro. destruct H0. pose proof (H1 i).
    rewrite eq_refl in H2. inversion H2.
  }
  split.
  { tauto. }
  {
    intro.
    unfold replace_individual_ethic.
    destruct (i0 == i) ; reflexivity.
  }
Qed.

End more_restrictive_ethics_diminish_conflicts.
