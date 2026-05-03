
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

import Tools.real
import Tools.continuous
import Tools.calculus
import Articles.definition_capitalism_communism

namespace maximizing_work_incentive

variable {Individual : Type}
variable {eqInd : DecidableEq Individual}
variable {Individuals : Fintype Individual}

open Set Filter Topology Real Metric
open definition_capitalism_communism ethics_in_society

noncomputable def average_work_incentive {government_spending : MonetaryValue}
(i : Individual) (a b : MonetaryValue)
(redi : @Redistribution Individual Individuals government_spending)
(cont : @Profile Individual MonetaryValue) :
ℝ := (
  ∫ c in a..b,
  @instantaneous_work_incentive Individual eqInd Individuals government_spending
  i c redi cont
) / (b - a)

lemma average_work_incentive_as_retribution_slope
{government_spending : MonetaryValue} {i : Individual} {a b : MonetaryValue}
{redi : @Redistribution Individual Individuals government_spending}
{cont : @Profile Individual MonetaryValue}
(dif : ∀ x ∈ uIcc a b, DifferentiableAt ℝ (
  @retribution_function Individual eqInd Individuals government_spending redi i cont
) x)
(derc : ContinuousOn (deriv (
  @retribution_function Individual eqInd Individuals government_spending redi i cont
)) (uIcc a b)) :
@average_work_incentive Individual eqInd Individuals government_spending
i a b redi cont = (
  @retribution_function Individual eqInd Individuals government_spending redi i cont b -
  @retribution_function Individual eqInd Individuals government_spending redi i cont a
) / (b - a) := by
  unfold average_work_incentive instantaneous_work_incentive
  have ftc : (
    ∫ (c : ℝ) in a..b, deriv (
      @retribution_function Individual eqInd Individuals government_spending redi i cont
    ) c = (
      @retribution_function Individual eqInd Individuals government_spending redi i cont b
    ) - (
      @retribution_function Individual eqInd Individuals government_spending redi i cont a
    )
  ) := by
    refine intervalIntegral.integral_deriv_eq_sub' (retribution_function redi i cont) rfl ?_ ?_
    · exact dif
    · exact derc
  rw [ftc]

noncomputable def average_work_incentive_until {government_spending : MonetaryValue}
(i : Individual) (redi : @Redistribution Individual Individuals government_spending)
(cont : @Profile Individual MonetaryValue) :
MonetaryValue -> MonetaryValue :=
  fun M => (
    @average_work_incentive Individual eqInd Individuals government_spending
    i 0 M redi cont
  )

def global_average_work_incentive_is {government_spending : MonetaryValue}
(i : Individual) (redi : @Redistribution Individual Individuals government_spending)
(cont : @Profile Individual MonetaryValue) (L : MonetaryValue) :
Prop :=
  Tendsto (
    @average_work_incentive_until Individual eqInd Individuals government_spending
    i redi cont
  ) atTop (𝓝 L)

theorem average_work_incentive_le_1 {government_spending : MonetaryValue}
{i : Individual} {redi : @Redistribution Individual Individuals government_spending}
{cont : @Profile Individual MonetaryValue} {L : MonetaryValue}
(dif : ∀ x ∈ Ici 0, DifferentiableAt ℝ (
  @retribution_function Individual eqInd Individuals government_spending redi i cont
) x)
(derc : ContinuousOn (deriv (
  @retribution_function Individual eqInd Individuals government_spending redi i cont
)) (Ici 0))
(exst :
  @global_average_work_incentive_is Individual eqInd Individuals government_spending
  i redi cont L
)
(orgp : ∃M0, ∀M, M0 ≤ M → 0 ≤ ∑ j ∈ {i}ᶜ, redi.val (replace cont i M) j) :
L <= 1 := by
  unfold global_average_work_incentive_is at exst
  unfold average_work_incentive_until at exst
  have aext : (∀ M : MonetaryValue, 0 ≤ M →
    @average_work_incentive Individual eqInd Individuals government_spending i (0 : ℝ) M redi cont =
    (
      @retribution_function Individual eqInd Individuals government_spending redi i cont M -
      @retribution_function Individual eqInd Individuals government_spending redi i cont (0 : ℝ)
    ) / (M : ℝ)
   ) := by
    intro M posM
    rw [average_work_incentive_as_retribution_slope]
    · simp
    · apply differentiableAt_on_uIcc_of_Ici
      · exact posM
      · exact dif
    · apply continuousOn_Ici_to_uIcc_v1
      · exact derc
      · exact posM
  have eqtd : (
    Tendsto (fun M ↦
      @average_work_incentive Individual eqInd Individuals government_spending
      i 0 M redi cont
    ) atTop (𝓝 L) ↔
    Tendsto (fun M ↦
      (
        @retribution_function Individual eqInd Individuals government_spending redi i cont M -
        @retribution_function Individual eqInd Individuals government_spending redi i cont 0) / M
    ) atTop (𝓝 L)
  ) := by
    apply tendsto_congr'
    unfold EventuallyEq
    unfold Filter.Eventually
    simp
    exists 0
  rw [eqtd] at exst
  unfold retribution_function at exst
  have rdpty := redi.property
  unfold accounts_at_equilibirum total_value at rdpty
  have dvlp : (∀ M, 1 ≤ M →
    (redi.val (replace cont i M) i - redi.val (replace cont i 0) i) / M =
    (
      ∑ j, (replace cont i M) j - government_spending -
      ∑ j ∈ {i}ᶜ, redi.val (replace cont i M) j -
      redi.val (replace cont i 0) i
    ) / M
  ) := by
    intro M posM
    rw [div_left_inj']
    · apply congr_arg (· - (redi.val (replace cont i 0) i))
      rw [<- rdpty]
      simp
      have sumri := Fintype.sum_eq_add_sum_compl i (redi.val (replace cont i M))
      rw [sumri]
      simp
    · intro eqM0
      rw [eqM0] at posM
      linarith
  have eqtd2 : (
    Tendsto (
      fun M ↦ (redi.val (replace cont i M) i - redi.val (replace cont i 0) i) / M
    ) atTop (𝓝 L) ↔
    Tendsto (
      fun M ↦ (
        ∑ j, (replace cont i M) j - government_spending -
        ∑ j ∈ {i}ᶜ, redi.val (replace cont i M) j -
        redi.val (replace cont i 0) i
      ) / M
    ) atTop (𝓝 L)
  ) := by
    apply tendsto_congr'
    unfold EventuallyEq
    unfold Filter.Eventually
    simp
    exists 1
  rw [eqtd2] at exst
  have dvlp2 : (∀ M, 1 ≤ M →
    (
      ∑ j, (replace cont i M) j - government_spending -
      ∑ j ∈ {i}ᶜ, redi.val (replace cont i M) j -
      redi.val (replace cont i 0) i
    ) / M =
    1 + (
      (∑ j ∈ {i}ᶜ, (replace cont i M) j) - government_spending -
      ∑ j ∈ {i}ᶜ, redi.val (replace cont i M) j -
      redi.val (replace cont i 0) i
    ) / M
  ) := by
    intro M posM
    have sumci := Fintype.sum_eq_add_sum_compl i (replace cont i M)
    rw [sumci]
    rw [replace_changes]
    field
  have eqtd3 : (
    Tendsto (
      fun M ↦ (
        ∑ j, (replace cont i M) j - government_spending -
        ∑ j ∈ {i}ᶜ, redi.val (replace cont i M) j -
        redi.val (replace cont i 0) i
      ) / M
    ) atTop (𝓝 L) ↔
    Tendsto (
      fun M ↦ 1 + (
        (∑ j ∈ {i}ᶜ, (replace cont i M) j) - government_spending -
        ∑ j ∈ {i}ᶜ, redi.val (replace cont i M) j -
        redi.val (replace cont i 0) i
      ) / M
    ) atTop (𝓝 L)
  ) := by
    apply tendsto_congr'
    unfold EventuallyEq
    unfold Filter.Eventually
    simp
    exists 1
  rw [eqtd3] at exst
  have rplun : (
    (fun M ↦ 1 + (
      (∑ j ∈ {i}ᶜ, (replace cont i M) j) - government_spending -
      ∑ j ∈ {i}ᶜ, redi.val (replace cont i M) j -
      redi.val (replace cont i 0) i
    ) / M) =
    (fun M ↦ 1 + (
      (∑ j ∈ {i}ᶜ, cont j) - government_spending -
      ∑ j ∈ {i}ᶜ, redi.val (replace cont i M) j -
      redi.val (replace cont i 0) i
    ) / M)
  ) := by
    apply funext
    intro M
    have eqsum : ∑ j ∈ {i}ᶜ, replace cont i M j = ∑ j ∈ {i}ᶜ, cont j := by
      apply Finset.sum_congr
      · simp
      · intro j neij
        rw [replace_unchanges]
        intro eqij
        rw [eqij] at neij
        simp at neij
    rw [eqsum]
  rw [rplun] at exst
  obtain ⟨M0, orgp'⟩ := orgp
  have rdmaj : (∀ M, max 1 M0 ≤ M →
    1 + (
      (∑ j ∈ {i}ᶜ, cont j) - government_spending -
      ∑ j ∈ {i}ᶜ, redi.val (replace cont i M) j -
      redi.val (replace cont i 0) i
    ) / M ≤
    1 + (
      (∑ j ∈ {i}ᶜ, cont j) - government_spending -
      redi.val (replace cont i 0) i
    ) / M
  ) := by
    intro M leM
    specialize (orgp' M)
    have leM0 : M0 ≤ max 1 M0 := by
      exact Std.right_le_max
    have leM1 : M0 ≤ M := by
      exact Std.IsPreorder.le_trans M0 (max 1 M0) M leM0 leM
    specialize (orgp' leM1)
    have le1M : 1 ≤ M := by
      exact le_of_max_le_left leM
    apply add_le_add_right
    apply div_le_div_of_pos
    · rw [gt_iff_lt]
      have lt01 : 0 < (1 : ℝ) := by
        exact Real.zero_lt_one
      apply (lt_of_lt_of_le lt01 le1M)
    · apply sub_le_sub_right
      apply sub_le_self
      exact orgp'
  have rdmaj' : (
    (
      fun M ↦ 1 + (
        (∑ j ∈ {i}ᶜ, cont j) - government_spending -
        ∑ j ∈ {i}ᶜ, redi.val (replace cont i M) j -
        redi.val (replace cont i 0) i
      ) / M
    ) ≤ᶠ[atTop] (
      fun M ↦ 1 + (
        (∑ j ∈ {i}ᶜ, cont j) - government_spending -
        redi.val (replace cont i 0) i
      ) / M
    )
  ) := by
    unfold EventuallyLE
    unfold Filter.Eventually
    simp
    exists (max 1 M0)
    intro M leMx
    specialize (rdmaj M leMx)
    simp at rdmaj
    exact RCLike.ofReal_le_ofReal.mp rdmaj
  have lim0 : (
    Tendsto (
      fun M ↦ (
        (∑ j ∈ {i}ᶜ, cont j) - government_spending -
        redi.val (replace cont i 0) i
      ) / M
    ) atTop (𝓝 0)
  ) := by
    exact Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
  have lim1 : (
    Tendsto (
      fun M ↦ 1 + (
        (∑ j ∈ {i}ᶜ, cont j) - government_spending -
        redi.val (replace cont i 0) i
      ) / M
    ) atTop (𝓝 (1 + 0))
  ) := by
    apply Filter.Tendsto.add
    · apply tendsto_const_nhds
    · apply lim0
  simp at lim1
  apply (le_of_tendsto_of_tendsto exst lim1 rdmaj')

def maximizes_average_work_incentive {government_spending : MonetaryValue}
(i : Individual) (redi : @Redistribution Individual Individuals government_spending)
(cont : @Profile Individual MonetaryValue) : Prop :=
  @global_average_work_incentive_is Individual eqInd Individuals government_spending
  i redi cont 1

lemma global_average_work_incentive_capitalism (government_spending : MonetaryValue)
{i : Individual} {cont : @Profile Individual MonetaryValue}
(dif : ∀ x ∈ Ici 0, DifferentiableAt ℝ (
  @retribution_function Individual eqInd Individuals government_spending (
    pure_capitalism_costs_equally_divided_Redistribution (
      inhabited_implies_nonnull_card i
    ) government_spending
  ) i cont
) x)
(derc : ContinuousOn (deriv (
  @retribution_function Individual eqInd Individuals government_spending (
    pure_capitalism_costs_equally_divided_Redistribution (
      inhabited_implies_nonnull_card i
    ) government_spending
  ) i cont
)) (Ici 0)) :
@maximizes_average_work_incentive Individual eqInd Individuals government_spending
i (pure_capitalism_costs_equally_divided_Redistribution (
  inhabited_implies_nonnull_card i
) government_spending) cont := by
  unfold maximizes_average_work_incentive
  unfold global_average_work_incentive_is
  unfold average_work_incentive_until
  have aext : (∀ M, 0 ≤ M →
    @average_work_incentive Individual eqInd Individuals government_spending
    i 0 M ⟨fun cont i ↦ cont i - government_spending / ↑(Fintype.card Individual), (
      pure_capitalism_costs_equally_divided_at_equilibirum
      (inhabited_implies_nonnull_card i) government_spending
    )⟩ cont =
    (
      @retribution_function Individual eqInd Individuals government_spending (
        pure_capitalism_costs_equally_divided_Redistribution (
          inhabited_implies_nonnull_card i
        ) government_spending
      ) i cont M -
      @retribution_function Individual eqInd Individuals government_spending (
        pure_capitalism_costs_equally_divided_Redistribution (
          inhabited_implies_nonnull_card i
        ) government_spending
      ) i cont 0
    ) / M
  ) := by
    intro M posM
    unfold pure_capitalism_costs_equally_divided_Redistribution
    unfold pure_capitalism_costs_equally_divided
    rw [average_work_incentive_as_retribution_slope]
    · simp
    · unfold pure_capitalism_costs_equally_divided_Redistribution at dif
      unfold pure_capitalism_costs_equally_divided at dif
      apply differentiableAt_on_uIcc_of_Ici
      · exact posM
      · exact dif
    · unfold pure_capitalism_costs_equally_divided_Redistribution at derc
      unfold pure_capitalism_costs_equally_divided at derc
      apply continuousOn_Ici_to_uIcc_v1
      · exact derc
      · exact posM
  unfold pure_capitalism_costs_equally_divided_Redistribution
  unfold pure_capitalism_costs_equally_divided
  have eqtd : (
    Tendsto (fun M ↦
      @average_work_incentive Individual eqInd Individuals government_spending i 0 M ⟨
        fun cont i ↦ cont i - government_spending / ↑(Fintype.card Individual),
        pure_capitalism_costs_equally_divided_at_equilibirum (
          inhabited_implies_nonnull_card i
        ) government_spending
      ⟩ cont
    ) atTop (𝓝 1) ↔
    Tendsto (fun M ↦
      (
        @retribution_function Individual eqInd Individuals government_spending ⟨
          fun cont i ↦ cont i - government_spending / ↑(Fintype.card Individual),
          pure_capitalism_costs_equally_divided_at_equilibirum (
            inhabited_implies_nonnull_card i
          ) government_spending
        ⟩ i cont M -
        @retribution_function Individual eqInd Individuals government_spending ⟨
          fun cont i ↦ cont i - government_spending / ↑(Fintype.card Individual),
          pure_capitalism_costs_equally_divided_at_equilibirum (
            inhabited_implies_nonnull_card i
          ) government_spending
        ⟩ i cont 0) / M
    ) atTop (𝓝 1)
  ) := by
    apply tendsto_congr'
    unfold EventuallyEq
    unfold Filter.Eventually
    simp
    exists 0
  rw [eqtd]
  unfold retribution_function
  simp
  rw [replace_changes]
  have apxt : (fun M ↦ (replace cont i M i - 0) / M) = (fun M ↦ M / M) := by
    apply funext
    intro mv
    rw [replace_changes]
    simp
  rw [apxt]
  have eqtd2 : (
    Tendsto (fun M : ℝ ↦ ((M / M) : ℝ)) atTop (𝓝 1) ↔
    Tendsto (fun M : ℝ ↦ (1 : ℝ)) atTop (𝓝 1)
   ) := by
    apply tendsto_congr'
    unfold EventuallyEq
    unfold Filter.Eventually
    simp
    exists 1
    intro x le1x eq0x
    rw [eq0x] at le1x
    linarith
  rw [eqtd2]
  exact tendsto_const_nhds

end maximizing_work_incentive
