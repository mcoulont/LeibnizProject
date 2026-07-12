
import Articles.ethics_in_society

namespace objective_ethics_no_disapproval_iff_same_ethic

variable {State : Type}
variable {Action : Type}
variable {Individual : Type}
variable {eqInd : DecidableEq Individual}

open Equiv
open ethics_in_society

def objective (ethic : @IndividualEthic State Action Individual)
(ipos : @IndividualsPermutationsActingOnStates State Individual) :
Prop :=
  ∀ (state : State) (individual : Individual) (σ : Perm Individual),
    ethic (
      @permutation_SubjectiveState State Individual ipos (
        @get_SubjectiveState State Individual state individual
      ) σ
    ) =
    ethic ( @get_SubjectiveState State Individual state individual)

def everyone_is_objective
(ethical_profile : Individual -> (@IndividualEthic State Action Individual))
(ipos : @IndividualsPermutationsActingOnStates State Individual) :=
  ∀ (i : Individual), objective (ethical_profile i) ipos

def may_disapprove
(ethical_profile : Individual -> (@IndividualEthic State Action Individual))
(i j : Individual) (state : State) :
Prop :=
  ∃ (action : Action),
    ethical_profile j (
      @get_SubjectiveState State Individual state j
    ) action = true /\
    ethical_profile i (
      @get_SubjectiveState State Individual state j
    ) action = false

def may_never_disapprove
(ethical_profile : Individual -> (@IndividualEthic State Action Individual))
(i j : Individual) :
Prop :=
  ∀ (state : State), ¬ may_disapprove ethical_profile i j state

def nobody_may_disapprove
(ethical_profile : Individual -> (@IndividualEthic State Action Individual))
(state : State) :
Prop :=
  ∀ (i j : Individual), ¬ may_disapprove ethical_profile i j state

def nobody_may_ever_disapprove
(ethical_profile : Individual -> (@IndividualEthic State Action Individual)) :
Prop :=
  ∀ (state : State), nobody_may_disapprove ethical_profile state

lemma same_ethic_implies_may_not_disapprove
(ethical_profile : Individual -> (@IndividualEthic State Action Individual))
(i j : Individual) (state : State) :
ethical_profile i ( @get_SubjectiveState State Individual state j) =
ethical_profile j ( @get_SubjectiveState State Individual state j) ->
¬ may_disapprove ethical_profile i j state := by
  intro eqet mdep
  unfold may_disapprove at mdep
  obtain ⟨action, mde⟩ := mdep
  rcases mde with ⟨etht, ethf⟩
  have eqeta :
  ethical_profile i (get_SubjectiveState state j) action =
  ethical_profile j (get_SubjectiveState state j) action := by
    exact Bool.not_inj_iff.mp (congrArg not (congrFun eqet action))
  rewrite [etht] at eqeta
  rewrite [ethf] at eqeta
  simp at eqeta

theorem objective_ethics_may_never_disapprove_implies_same_ethic
-- in my mind, should have worked without the line below thanks to eqInd
[DecidableEq Individual]
(ipos : @IndividualsPermutationsActingOnStates State Individual)
(ethical_profile : Individual -> (@IndividualEthic State Action Individual))
(i j : Individual) :
objective (ethical_profile i) ipos ->
objective (ethical_profile j) ipos ->
may_never_disapprove ethical_profile i j ->
may_never_disapprove ethical_profile j i ->
ethical_profile i = ethical_profile j := by
  intro obji objj mndij mndji
  apply funext
  intro subjs
  apply funext
  intro action
  cases ethi : ethical_profile i subjs action
  · cases ethj : ethical_profile j subjs action
    · simp
    · specialize (obji subjs.state subjs.individual (swap j subjs.individual))
      unfold get_SubjectiveState at obji
      have eqeti : ∀ (a : Action), (
        ethical_profile i (
          @permutation_SubjectiveState State Individual ipos
          {state := subjs.state, individual := subjs.individual}
          (swap j subjs.individual)
        ) a =
        ethical_profile i {state := subjs.state, individual := subjs.individual} a
      ) := by
        rw [obji]
        simp
      specialize (eqeti action)
      rw [ethi] at eqeti
      unfold permutation_SubjectiveState at eqeti
      simp at eqeti
      specialize (objj subjs.state subjs.individual (swap j subjs.individual))
      unfold get_SubjectiveState at objj
      have eqetj : ∀ (a : Action), (
        ethical_profile j (
          @permutation_SubjectiveState State Individual ipos
          {state := subjs.state, individual := subjs.individual}
          (swap j subjs.individual)
        ) a =
        ethical_profile j {state := subjs.state, individual := subjs.individual} a
      ) := by
        rw [objj]
        simp
      specialize (eqetj action)
      rw [ethj] at eqetj
      unfold permutation_SubjectiveState at eqetj
      simp at eqetj
      specialize (mndij (ipos.val subjs.state (swap j subjs.individual)))
      exfalso
      apply mndij
      unfold may_disapprove
      exists action
  · cases ethj : ethical_profile j subjs action
    · specialize (obji subjs.state subjs.individual (swap i subjs.individual))
      unfold get_SubjectiveState at obji
      have eqeti : ∀ (a : Action), (
        ethical_profile i (
          @permutation_SubjectiveState State Individual ipos
          {state := subjs.state, individual := subjs.individual}
          (swap i subjs.individual)
        ) a =
        ethical_profile i {state := subjs.state, individual := subjs.individual} a
      ) := by
        rw [obji]
        simp
      specialize (eqeti action)
      rw [ethi] at eqeti
      unfold permutation_SubjectiveState at eqeti
      simp at eqeti
      specialize (objj subjs.state subjs.individual (swap i subjs.individual))
      unfold get_SubjectiveState at objj
      have eqetj : ∀ (a : Action), (
        ethical_profile j (
          @permutation_SubjectiveState State Individual ipos
          {state := subjs.state, individual := subjs.individual}
          (swap i subjs.individual)
        ) a =
        ethical_profile j {state := subjs.state, individual := subjs.individual} a
      ) := by
        rw [objj]
        simp
      specialize (eqetj action)
      rw [ethj] at eqetj
      unfold permutation_SubjectiveState at eqetj
      simp at eqetj
      specialize (mndji (ipos.val subjs.state (swap i subjs.individual)))
      exfalso
      apply mndji
      unfold may_disapprove
      exists action
    · simp

lemma objective_ethics_no_disapproval_iff_same
-- in my mind, should have worked without the line below thanks to eqInd
[DecidableEq Individual]
(ipos : @IndividualsPermutationsActingOnStates State Individual)
(ethical_profile : Individual -> (@IndividualEthic State Action Individual)) :
everyone_is_objective ethical_profile ipos ->
(
  nobody_may_ever_disapprove ethical_profile <->
  everyone_always_same_ethic ethical_profile
) := by
  intro evob
  apply Iff.intro
  · intro nob
    unfold everyone_always_same_ethic
    intro subjs
    unfold everyone_same_ethic
    intro i j
    have eqij : ethical_profile i = ethical_profile j := by
      unfold everyone_is_objective at evob
      unfold nobody_may_ever_disapprove nobody_may_disapprove at nob
      apply objective_ethics_may_never_disapprove_implies_same_ethic
      · apply evob
      · apply evob
      · unfold may_never_disapprove
        intro state
        apply nob
      · unfold may_never_disapprove
        intro state
        apply nob
    rewrite [eqij]
    simp
  · intro evsa
    unfold nobody_may_ever_disapprove
    intro state
    unfold nobody_may_disapprove
    intro i j
    apply same_ethic_implies_may_not_disapprove
    unfold everyone_always_same_ethic everyone_same_ethic at evsa
    rw [get_SubjectiveState]
    apply evsa

end objective_ethics_no_disapproval_iff_same_ethic
