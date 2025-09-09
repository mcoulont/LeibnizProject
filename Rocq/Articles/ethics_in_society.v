
From mathcomp Require Import all_ssreflect.
From mathcomp.classical Require Import boolp.

Require Import ethics_first_steps.

Section ethics_in_society.

Context {State : Type}.
Context {Action : Type}.
Context {Individual : finType}.

Definition ActionProfile : Type := Individual -> Action.

Structure SubjectiveState : Type := {
    state : State ;
    individual : Individual
  }.

Definition get_SubjectiveState (state : State) (i : Individual) :
SubjectiveState := {|
    state := state ;
    individual := i
  |}.

Lemma proj_individual_SubjectiveState (state : State) (i : Individual) :
  individual (get_SubjectiveState state i) = i.
Proof.
  auto.
Qed.

Lemma proj_state_SubjectiveState (s : State) (i : Individual) :
  state (get_SubjectiveState s i) = s.
Proof.
  auto.
Qed.

Definition IndividualEthic : Type := @Ethic SubjectiveState Action.

Definition EthicalProfile : Type := Individual -> IndividualEthic.

Definition everyone_same_ethic
(ethical_profile : EthicalProfile) (subjective_state : SubjectiveState) : Prop :=
  forall (i j : Individual),
    ethical_profile i subjective_state =
    ethical_profile j subjective_state.

Definition everyone_always_same_ethic (ethical_profile : EthicalProfile) : Prop :=
  forall (subjective_state : SubjectiveState),
    everyone_same_ethic ethical_profile subjective_state.

End ethics_in_society.
