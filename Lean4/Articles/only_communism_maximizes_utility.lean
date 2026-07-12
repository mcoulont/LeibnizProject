
import Tools.real
import Articles.definition_capitalism_communism

namespace only_communism_maximizes_utility

variable {Individual : Type}
variable {eqInd : DecidableEq Individual}
variable {Individuals : Fintype Individual}

open Set Filter Topology Real Metric
open definition_capitalism_communism

def increases_with_money (utility : MonetaryValue -> ℝ) : Prop :=
  Monotone utility

def law_diminishing_marginal_utility (utility : MonetaryValue -> ℝ) : Prop :=
  ConcaveOn ℝ (Set.Ici (0 : ℝ)) utility

def law_diminishing_marginal_utility_strict (utility : MonetaryValue -> ℝ) : Prop :=
  StrictConcaveOn ℝ (Set.Ici (0 : ℝ)) utility

def social_utility (utility : MonetaryValue -> ℝ) (retr : Individual -> ℝ) : ℝ :=
  ∑ i, utility (retr i)

theorem communism_maximizes_social_utility {government_spending : MonetaryValue}
{utility : MonetaryValue -> ℝ}
{cont : Individual -> MonetaryValue}
{redi : @Redistribution Individual Individuals government_spending}
(inh : Fintype.card Individual ≠ 0) (ldmu : law_diminishing_marginal_utility utility)
(rpos : ∀ i, 0 ≤ redi.val cont i) :
@social_utility Individual Individuals utility (redi.val cont) ≤
@social_utility Individual Individuals utility (
  @pure_communism Individual Individuals government_spending cont
) := by
  unfold social_utility pure_communism total_value
  rw [Finset.sum_const]
  unfold law_diminishing_marginal_utility at ldmu
  let weight := fun _ : Individual => (1 : ℝ) / ↑(Fintype.card Individual)
  have h0 : ∀ i, 0 ≤ weight i := by
    unfold weight
    intro i
    exact Nat.one_div_cast_nonneg (Fintype.card Individual)
  have inh' : (Fintype.card Individual : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr inh
  have h1 : ∑ i, weight i = 1 := by
    unfold weight
    rw [Finset.sum_const]
    simp
    rw [Lean.Grind.Field.mul_inv_cancel]
    exact inh'
  have jens : (
    ∑ i, weight i * utility (redi.val cont i) ≤
    utility (∑ i, weight i * (redi.val cont i))
  ) := by
    apply ldmu.le_map_sum
    · intro i iin
      unfold weight
      simp
    · unfold weight
      rw [Finset.sum_const]
      simp
      rw [Lean.Grind.Field.mul_inv_cancel]
      exact inh'
    · intro i iin
      specialize (rpos i)
      simp
      exact rpos
  unfold weight at jens
  rw [sum_reals_mult_constant] at jens
  have equi := redi.property cont
  unfold accounts_at_equilibirum total_value at equi
  have equl : ∑ i, cont i - government_spending = ∑ i, redi.val cont i := by
    exact sub_eq_iff_eq_add.mpr (id (Eq.symm equi))
  rw [equl]
  have mulc : (
    ∑ i, redi.val cont i / ↑(Fintype.card Individual) =
    ∑ i, 1 / ↑(Fintype.card Individual) * redi.val cont i
  ) := by
    apply Fintype.sum_congr
    intro i
    field
  rw [<- mulc] at jens
  have nneg : 0 ≤ (Fintype.card Individual : ℝ) := by
    exact Nat.cast_nonneg' (Fintype.card Individual)
  apply Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left at jens
  specialize (jens nneg)
  rw [<- mul_assoc] at jens
  simp at jens
  rw [Lean.Grind.Field.mul_inv_cancel] at jens
  · rw [one_mul] at jens
    simp
    rw [sum_reals_div_constant] at jens
    · exact jens
    · exact Nat.cast_ne_zero.mpr inh
  · exact Nat.cast_ne_zero.mpr inh

theorem only_communism_maximizes_social_utility {government_spending : MonetaryValue}
{utility : MonetaryValue -> ℝ} {cont : Individual -> MonetaryValue}
{redi : @Redistribution Individual Individuals government_spending}
(inh : Fintype.card Individual ≠ 0) (ldmu : law_diminishing_marginal_utility_strict utility)
(rpos : ∀ i, 0 ≤ redi.val cont i) :
@social_utility Individual Individuals utility (redi.val cont) =
@social_utility Individual Individuals utility (
  @pure_communism Individual Individuals government_spending cont
) →
redi.val cont = @pure_communism Individual Individuals government_spending cont := by
  intro eqsu
  unfold social_utility pure_communism total_value at eqsu
  rw [Finset.sum_const] at eqsu
  let weight := fun _ : Individual => (1 : ℝ) / ↑(Fintype.card Individual)
  have equi := redi.property cont
  unfold total_value at equi
  have h0 : ∀ i, 0 < weight i := by
    unfold weight
    intro i
    exact Nat.one_div_cast_pos inh
  have inh' : (Fintype.card Individual : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr inh
  have h1 : ∑ i, weight i = 1 := by
    unfold weight
    rw [Finset.sum_const]
    simp
    rw [Lean.Grind.Field.mul_inv_cancel]
    exact inh'
  by_contra nerd
  have jens : (
    ∑ i, weight i * utility (redi.val cont i) <
    utility (∑ i, weight i * (redi.val cont i))
  ) := by
    apply ldmu.lt_map_sum
    · intro i iin
      unfold weight
      simp
      exact Nat.zero_lt_of_ne_zero inh
    · unfold weight
      rw [Finset.sum_const]
      simp
      rw [Lean.Grind.Field.mul_inv_cancel]
      exact inh'
    · intro i iin
      specialize (rpos i)
      simp
      exact rpos
    · contrapose nerd
      rw [not_exists] at nerd
      simp at nerd
      unfold pure_communism total_value
      apply funext
      intro i
      specialize (nerd i)
      have sumc : (
        ∑ j, redi.val cont j =
        ↑(Fintype.card Individual) * redi.val cont i
       ) := by
        rw [Fintype.sum_congr (fun j => redi.val cont j) (fun _ => redi.val cont i)]
        · rw [Finset.sum_const]
          simp
        · intro k
          rw [nerd]
      rw [<- equi]
      simp
      rw [sumc]
      rw [mul_comm]
      rw [mul_div_assoc]
      rw [div_self]
      · simp
      · exact inh'
  unfold weight at jens
  rw [sum_reals_mult_constant] at jens
  rw [sum_reals_mult_constant] at jens
  rw [eqsu] at jens
  simp at jens
  rw [<- mul_assoc] at jens
  rw [Lean.Grind.Field.inv_mul_cancel] at jens
  · rw [<- equi] at jens
    simp at jens
    rw [mul_comm] at jens
    rw [div_eq_mul_inv] at jens
    simp at jens
  · exact inh'

end only_communism_maximizes_utility
