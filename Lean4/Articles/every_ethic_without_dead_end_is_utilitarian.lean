
import Mathlib.Data.Nat.Basic
import Mathlib.Order.RelClasses

import Tools.preference
import Articles.ethics_first_steps

namespace every_ethic_without_dead_end_is_utilitarian

variable {State : Type}
variable {Action : Type}

open ethics_first_steps

def dead_end (ethic : @Ethic State Action) (state : State) : Prop :=
  ∀ (action : Action), ethic state action = false

def without_dead_end (ethic : @Ethic State Action) : Prop :=
  forall (state : State), ¬ dead_end ethic state

def UtilityFunction (ps : PreferenceSpace) : Type := State → Action → ps.carrier

def can_be_obtained {ps : PreferenceSpace} (uf : @UtilityFunction State Action ps)
(state : State) (utility : get_carrier ps) : Prop :=
  ∃ (action : Action), utility = uf state action

def is_maximum {ps : PreferenceSpace} (uf : @UtilityFunction State Action ps)
(state : State) (utility : get_carrier ps) : Prop :=
  can_be_obtained uf state utility ∧
  ∀ (action : Action), get_preference_order ps utility (uf state action)

def maximizes {ps : PreferenceSpace}
(ethic : @Ethic State Action) (uf : @UtilityFunction State Action ps) : Prop :=
  forall (state : State) (action : Action),
    ethic state action ↔
    is_maximum uf state (uf state action)

def is_utilitarian (ethic : @Ethic State Action) : Prop :=
  ∃ (ps : PreferenceSpace) (uf : @UtilityFunction State Action ps),
    @maximizes State Action ps ethic uf

def associated_utility (ethic : @Ethic State Action) : State → Action → ℕ :=
  fun state => (fun action => if ethic state action then 0 else 1)

lemma le_preference_order : preference_order Nat.le := by
  unfold preference_order
  constructor
  · apply transitive_le
  · apply le_total

def associatedPreferenceSpace :
  PreferenceSpace := @PreferenceSpace.mk ℕ Nat.le le_preference_order

lemma every_ethic_without_dead_end_is_utilitarian2 :
∀ (ethic : @Ethic State Action), without_dead_end ethic → is_utilitarian ethic := by
  intro ethic
  intro h
  unfold is_utilitarian
  exists associatedPreferenceSpace
  exists (associated_utility ethic)
  unfold maximizes
  intro state action
  unfold is_maximum
  constructor
  · intro h0
    constructor
    · unfold can_be_obtained
      exists action
    · unfold associated_utility
      rw [h0]
      simp
      intro action'
      match (ethic state action') with
      | true =>
        simp
        unfold associatedPreferenceSpace
        unfold get_preference_order
        simp
      | false =>
        simp
        unfold associatedPreferenceSpace
        unfold get_preference_order
        simp
  · intro h0
    rcases h0 with ⟨h1, h2⟩
    match h4 :(ethic state action) with
    | true => rfl
    | false => unfold associated_utility at h1 ; unfold without_dead_end at h ;
               specialize h state ; unfold dead_end at h ;
               exfalso ; apply h ;
               intro action' ; specialize h2 action' ;
               unfold associated_utility at h2
               cases h3 : (ethic state action')
               · case false => rfl
               · case true => rw [h3] at h2 ; simp at h2 ;
                              rw [h4] at h2 ; simp at h2 ;
                              unfold associatedPreferenceSpace at h2 ;
                              unfold get_preference_order at h2 ; simp at h2

end every_ethic_without_dead_end_is_utilitarian
