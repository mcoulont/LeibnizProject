
import Mathlib.Tactic.Tauto

import Articles.every_ethic_without_dead_end_is_utilitarian

namespace utilitarian_ethic_no_freedom_iff_maximum_for_unique_action

variable {State : Type}
variable {Action : Type}

open ethics_first_steps
open every_ethic_without_dead_end_is_utilitarian

def leaves_no_freedom (ethic: @Ethic State Action) (state: State) : Prop :=
  ∃! (action: Action), ethic state action = true

def never_leaves_freedom (ethic: @Ethic State Action) : Prop :=
  ∀ (state: State), leaves_no_freedom ethic state

lemma no_freedom_implies_no_dead_end (ethic: @Ethic State Action) (state: State) :
leaves_no_freedom ethic state -> ¬ dead_end ethic state := by
  intro h
  unfold leaves_no_freedom at h
  unfold ExistsUnique at h
  rcases h with ⟨action, h⟩
  rcases h with ⟨x1, h2⟩
  unfold dead_end
  intro h
  specialize h action
  rw [h] at x1
  contradiction

lemma never_leaves_freedom_implies_never_has_dead_end (ethic: @Ethic State Action) :
never_leaves_freedom ethic → without_dead_end ethic := by
  unfold without_dead_end
  unfold never_leaves_freedom
  intro h
  intro state
  apply no_freedom_implies_no_dead_end
  apply h

def utilitarian_ethic_unique_maximum {ps : PreferenceSpace}
(uf : @UtilityFunction State Action ps) (state : State) : Prop :=
  ∃! (action : Action), is_maximum uf state (uf state action)

def utilitarian_ethic_always_unique_maximum {ps : PreferenceSpace}
(uf : @UtilityFunction State Action ps) : Prop :=
  ∀ (state: State), utilitarian_ethic_unique_maximum uf state

theorem utilitarian_ethic_no_freedom_iff_max_for_unique_action
{ps : PreferenceSpace} :
∀ (ethic: @Ethic State Action) (uf : @UtilityFunction State Action ps)
(_ethic_maximizes_uf : maximizes ethic uf) (state: State),
utilitarian_ethic_unique_maximum uf state ↔
leaves_no_freedom ethic state := by
  intro ethic
  intro uf
  intro ethic_maximizes_uf
  intro state
  unfold maximizes at ethic_maximizes_uf
  constructor
  · intro h0
    unfold leaves_no_freedom
    unfold ExistsUnique
    unfold utilitarian_ethic_unique_maximum at h0
    unfold ExistsUnique at h0
    rcases h0 with ⟨x, h0⟩
    rcases h0 with ⟨h1, h2⟩
    simp at h2
    exists x
    constructor
    · simp
      specialize ethic_maximizes_uf state
      specialize ethic_maximizes_uf x
      rw [← ethic_maximizes_uf] at h1
      exact h1
    · simp
      intro y
      intro h3
      specialize h2 y
      apply h2
      specialize ethic_maximizes_uf state
      specialize ethic_maximizes_uf y
      rw [← ethic_maximizes_uf]
      exact h3
  · intro h
    unfold leaves_no_freedom at h
    unfold ExistsUnique at h
    unfold utilitarian_ethic_unique_maximum
    unfold ExistsUnique
    rcases h with ⟨action, h⟩
    rcases h with ⟨h1, h2⟩
    specialize ethic_maximizes_uf state
    exists action
    simp
    constructor
    · specialize ethic_maximizes_uf action
      rw [← ethic_maximizes_uf]
      exact h1
    · intro y
      simp at h2
      specialize h2 y
      intro h3
      rw [← ethic_maximizes_uf] at h3
      apply h2
      exact h3

lemma utilitarian_ethic_never_freedom_iff_always_maximum_for_unique_action
{ps : PreferenceSpace} :
∀ (ethic: @Ethic State Action) (uf : @UtilityFunction State Action ps)
(_ethic_maximizes_uf : maximizes ethic uf),
utilitarian_ethic_always_unique_maximum uf ↔
never_leaves_freedom ethic := by
  intro ethic
  intro uf
  intro ethic_maximizes_uf
  unfold utilitarian_ethic_always_unique_maximum
  unfold never_leaves_freedom
  constructor
  · intro h
    intro state
    specialize h state
    rw [← utilitarian_ethic_no_freedom_iff_max_for_unique_action ethic uf] <;> tauto
  · intro h
    intro state
    specialize h state
    rw [utilitarian_ethic_no_freedom_iff_max_for_unique_action ethic uf] <;> tauto

end utilitarian_ethic_no_freedom_iff_maximum_for_unique_action
