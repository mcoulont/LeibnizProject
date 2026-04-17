
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.GroupTheory.Perm.Finite

import Articles.ethics_first_steps

namespace ethics_in_society

variable {State : Type}
variable {Action : Type}
variable {Individual : Type}

open Equiv
open ethics_first_steps

def Profile (T  : Type) : Type := Individual -> T

structure SubjectiveState : Type where
  state : State
  individual : Individual

def get_SubjectiveState (state : State) (i : Individual) :
@SubjectiveState State Individual :=
  {state := state, individual := i}

lemma proj_individual_SubjectiveState (state : State) (i : Individual) :
(get_SubjectiveState state i).individual = i := by
  tauto

lemma proj_state_SubjectiveState (s : State) (i : Individual) :
(get_SubjectiveState s i).state = s := by
  tauto

variable [DecidableEq Individual] [Fintype Individual]

def identity : Perm Individual := 1

def IndividualsPermutationsActingOnStates :
Type :=
  {
    permutation : State -> Perm Individual -> State //
    ∀ (state : State), (
      permutation state identity = state ∧
      ∀ (σ τ : Perm Individual),
        permutation (permutation state σ) τ = permutation state (σ • τ)
    )
  }

def permutation_State
(ipos : @IndividualsPermutationsActingOnStates State Individual) :
State -> Perm Individual -> State :=
  fun state => fun σ => ipos.val state σ

def permutation_SubjectiveState
(ipos : @IndividualsPermutationsActingOnStates State Individual) :
@SubjectiveState State Individual -> Perm Individual ->
@SubjectiveState State Individual :=
  fun subjective_state => fun σ => get_SubjectiveState (
    ipos.val subjective_state.state σ
  ) (σ subjective_state.individual)

def IndividualEthic : Type :=
  @Ethic (@SubjectiveState State Individual) Action

def everyone_same_ethic (ethical_profile : @Profile Individual (
  @IndividualEthic State Action Individual)
) (subjective_state : @SubjectiveState State Individual) :
Prop :=
  ∀ (i j : Individual),
    ethical_profile i subjective_state =
    ethical_profile j subjective_state

def everyone_always_same_ethic (ethical_profile : @Profile Individual (
  @IndividualEthic State Action Individual)
) : Prop :=
  ∀ (subjective_state : SubjectiveState),
    everyone_same_ethic ethical_profile subjective_state

end ethics_in_society
