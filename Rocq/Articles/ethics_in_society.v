
From mathcomp Require Import fintype fingroup perm.

Require Import ethics_first_steps.

Section ethics_in_society.

Context {State : Type}.
Context {Action : Type}.
Context {Individual : finType}.

Definition Profile (T  : Type) : Type := Individual -> T.

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

Open Scope group_scope.

Notation " σ ∘ τ " := (σ * τ) (at level 40, no associativity).
Definition identity : {perm Individual} := 1.

Definition IndividualsPermutationsActingOnStates : Type := {
  permutation : State -> {perm Individual} -> State |
  forall (state : State),
    permutation state identity = state /\
    forall (σ τ : {perm Individual}),
      permutation (permutation state σ) τ = permutation state (σ ∘ τ)
}.

Definition permutation_State (ipos : IndividualsPermutationsActingOnStates) :
State -> {perm Individual} -> State :=
  fun state => fun σ => proj1_sig ipos state σ.

Definition permutation_SubjectiveState (ipos : IndividualsPermutationsActingOnStates) :
SubjectiveState -> {perm Individual} -> SubjectiveState :=
  fun subjective_state => fun σ => get_SubjectiveState (
    proj1_sig ipos subjective_state.(state) σ
  ) (σ subjective_state.(individual)).

Definition IndividualEthic : Type := @Ethic SubjectiveState Action.

Definition everyone_same_ethic
(ethical_profile : Profile IndividualEthic) (subjective_state : SubjectiveState) :
Prop :=
  forall (i j : Individual),
    ethical_profile i subjective_state =
    ethical_profile j subjective_state.

Definition everyone_always_same_ethic (ethical_profile : Profile IndividualEthic) :
Prop :=
  forall (subjective_state : SubjectiveState),
    everyone_same_ethic ethical_profile subjective_state.

End ethics_in_society.
