
Require Import Bool.Bool.
Import BoolNotations.
From mathcomp Require Import all_ssreflect.

Require Import objective_ethics_no_disapproval_iff_same_ethic.

Definition Individual : finType :=
  objective_ethics_no_disapproval_iff_same_ethic.Individual.

Definition more_restrictive (e1 e2 : IndividualEthic)
(subj_state : SubjectiveState) : Prop :=
  forall (action : Action),
    e1 subj_state action = true -> e2 subj_state action = true.

Definition strictly_more_restrictive (e1 e2 : IndividualEthic)
(subj_state : SubjectiveState) : Prop :=
  more_restrictive e1 e2 subj_state /\
  exists (action : Action),
    e1 subj_state action = false /\ e2 subj_state action = true.

Definition ActionProfile : Type := Individual -> Action.

Context {feasible : State -> ActionProfile -> bool}.

Definition with_constraints (feasible : State -> ActionProfile -> bool) : Prop :=
  exists (state : State) (ap : ActionProfile), feasible state ap = false.

Definition conflict (ep : EthicalProfile) (ap : ActionProfile)
(state : State) : Prop :=
  (feasible state ap) = false /\
  forall (i : Individual), ep i (get_SubjectiveState state i) (ap i) = true.

Definition replace_individual_ethic (ep : EthicalProfile) (i : Individual)
(ethic : IndividualEthic) : EthicalProfile :=
  fun (j : Individual) => if j == i then ethic else ep j.

Proposition more_restrictive_ethic_diminishes_conflicts (ep : EthicalProfile)
(ap : ActionProfile) (i : Individual) (ethic : IndividualEthic) (state : State) :
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

Proposition more_restrictive_ethic_strictly_diminishes_conflicts (i : Individual) :
  with_constraints feasible ->
  exists (state : State) (ap : ActionProfile) (ep : EthicalProfile)
  (ethic : IndividualEthic),
    more_restrictive (ep i) ethic (get_SubjectiveState state i) /\
    ~ conflict ep ap state /\
    conflict (replace_individual_ethic ep i ethic) ap state.
Proof.
  intro. unfold with_constraints in H. destruct H as [state]. destruct H as [ap].
  exists (state).
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
  repeat split.
  {
    unfold conflict.
    intro. destruct H0. pose proof (H1 i).
    rewrite eq_refl in H2. inversion H2.
  }
  {
    tauto. 
  }
  {
    intro.
    unfold replace_individual_ethic.
    destruct (i0 == i) ; reflexivity.
  }
Qed.
