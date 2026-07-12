
import Articles.definition_capitalism_communism

namespace only_capitalism_makes_independent

variable {Individual : Type}
variable {eqInd : DecidableEq Individual}
variable {Individuals : Fintype Individual}

open Fintype
open definition_capitalism_communism

def retribution_depends_only_on_own_contribution {government_spending : MonetaryValue}
(redi : @Redistribution Individual Individuals government_spending) :
Prop :=
  ∃ (f : MonetaryValue -> MonetaryValue),
  ∀ (cont : Individual -> MonetaryValue) (i : Individual),
    redi.val cont i = f (cont i)

lemma retribution_depends_only_on_own_contribution_capitalism
(inh : Fintype.card Individual ≠ 0) (government_spending : MonetaryValue) :
retribution_depends_only_on_own_contribution (
  pure_capitalism_costs_equally_divided_Redistribution inh government_spending
) := by
  exists (fun mv => mv - government_spending / Fintype.card Individual)
  intro cont i
  unfold pure_capitalism_costs_equally_divided_Redistribution
  unfold pure_capitalism_costs_equally_divided
  simp

theorem only_pure_capitalism_makes_independent {government_spending : MonetaryValue}
(inh : Fintype.card Individual ≠ 0)
(redi : @Redistribution Individual Individuals government_spending) :
retribution_depends_only_on_own_contribution redi <->
redi = pure_capitalism_costs_equally_divided_Redistribution inh government_spending := by
  apply Iff.intro
  rotate_left
  · intro eqca
    rw [eqca]
    apply retribution_depends_only_on_own_contribution_capitalism
  · intro rdoc
    have sumc := redi.property
    ext cont i
    unfold retribution_depends_only_on_own_contribution at rdoc
    obtain ⟨retr, rdo⟩ := rdoc
    unfold pure_capitalism_costs_equally_divided_Redistribution
    simp
    unfold pure_capitalism_costs_equally_divided
    have defretr : retr = (fun mv => mv - government_spending / Fintype.card Individual) := by
      apply funext
      intro mv
      specialize (rdo (fun _ => mv))
      unfold accounts_at_equilibirum at sumc
      specialize (sumc (fun _ => mv))
      unfold total_value at sumc
      apply sum_congr at rdo
      rewrite [rdo] at sumc
      simp at sumc
      have defgs : (
        government_spending = ↑(card Individual) * mv - ↑(card Individual) * retr mv
      ) := by
        exact eq_sub_of_add_eq' sumc
      rw [defgs]
      have muld : (
        (↑(card Individual) * mv - ↑(card Individual) * retr mv) / ↑(card Individual) =
        (↑(card Individual) * mv) / ↑(card Individual) -
        ↑(card Individual) * retr mv / ↑(card Individual)
      ) := by
        exact sub_div (↑(card Individual) * mv) (
          ↑(card Individual) * retr mv
        ) ↑(card Individual)
      rw [muld]
      rw [mul_div_cancel_left₀]
      · rw [mul_div_cancel_left₀]
        · simp
        · exact Nat.cast_ne_zero.mpr inh
      · exact Nat.cast_ne_zero.mpr inh
    specialize (rdo cont)
    specialize (rdo i)
    rewrite [defretr] at rdo
    tauto

end only_capitalism_makes_independent
