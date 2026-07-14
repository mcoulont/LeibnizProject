
import Tools.preference

namespace definition_corruption

variable {Individual : Type}
variable {SocietyState : Type}
variable {ChoosablePolicies : Set (SocietyState -> SocietyState)}
variable {best_for_society_according_to : Set Individual -> SocietyState -> ChoosablePolicies}
variable {actual_choice : Set Individual -> SocietyState -> ChoosablePolicies}
variable {individual_preferences : Individual -> PreferenceOrder SocietyState}

def upstanding_choice (deciders : Set Individual) (state : SocietyState) :
ChoosablePolicies :=
  best_for_society_according_to deciders state

def upstanding (deciders : Set Individual) : Prop :=
  ∀ state,
    @upstanding_choice Individual SocietyState ChoosablePolicies best_for_society_according_to deciders state =
    actual_choice deciders state

def can_decide_unilaterally {deciders decisive_ones : Set Individual}
(_ : decisive_ones ⊆ deciders) (state : SocietyState) (choice : ChoosablePolicies) :
Prop :=
  actual_choice decisive_ones state = choice ->
  actual_choice deciders state = choice

def decide_unilaterally {deciders decisive_ones : Set Individual}
(incl : decisive_ones ⊆ deciders) (state : SocietyState) (choice : ChoosablePolicies):
Prop :=
  @can_decide_unilaterally Individual SocietyState ChoosablePolicies actual_choice deciders decisive_ones incl state choice ∧
  actual_choice decisive_ones state = choice

def self_interest_can_prevail {deciders decisive_ones : Set Individual}
(incl : decisive_ones ⊆ deciders) (state : SocietyState) (choice : ChoosablePolicies) :
Prop :=
  @can_decide_unilaterally Individual SocietyState ChoosablePolicies actual_choice deciders decisive_ones incl state choice ∧
  ∀ i ∈ decisive_ones,
    prefers (individual_preferences i) (choice.val state) (
      (@upstanding_choice Individual SocietyState ChoosablePolicies best_for_society_according_to decisive_ones state).val state
    )

def self_interest_prevails {deciders decisive_ones : Set Individual}
(incl : decisive_ones ⊆ deciders) (state : SocietyState) (choice : ChoosablePolicies) :
Prop :=
  @decide_unilaterally Individual SocietyState ChoosablePolicies actual_choice deciders decisive_ones incl state choice ∧
  ∀ i ∈ decisive_ones,
    prefers (individual_preferences i) (choice.val state) (
      (@upstanding_choice Individual SocietyState ChoosablePolicies best_for_society_according_to decisive_ones state).val state
    )

def corruption_opportunity (deciders corrupters : Set Individual) (state : SocietyState)
(influencing_action : Set Individual -> SocietyState -> SocietyState) :
Prop :=
  corrupters.Nonempty ∧
  ∀ corrupter ∈ corrupters, prefers (individual_preferences corrupter) (
    (actual_choice deciders (influencing_action corrupters state)).val state
  ) (
    (actual_choice deciders state).val state
  )

def corruption_prone (deciders : Set Individual) (state : SocietyState) : Prop :=
  ∃ (corrupters : Set Individual) (influencing_action : Set Individual -> SocietyState -> SocietyState),
    @corruption_opportunity Individual SocietyState ChoosablePolicies best_for_society_according_to individual_preferences deciders corrupters state influencing_action

end definition_corruption
