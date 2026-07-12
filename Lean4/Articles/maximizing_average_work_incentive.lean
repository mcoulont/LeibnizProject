
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

import Tools.real
import Tools.finset
import Tools.fintype
import Tools.limits
import Tools.continuous
import Tools.calculus
import Articles.definition_capitalism_communism

namespace maximizing_average_work_incentive

variable {Individual : Type}
variable {eqInd : DecidableEq Individual}
variable {Individuals : Fintype Individual}

open Classical Set Filter Topology Real Metric Finset Fintype
open definition_capitalism_communism

noncomputable def average_work_incentive {government_spending : MonetaryValue}
(i : Individual) (a b : MonetaryValue)
(redi : @Redistribution Individual Individuals government_spending)
(cont : Individual -> MonetaryValue) :
ℝ := (
  @retribution_function Individual eqInd Individuals government_spending redi i cont b -
  @retribution_function Individual eqInd Individuals government_spending redi i cont a
) / (b - a)

lemma average_work_incentive_as_integral {government_spending : MonetaryValue}
{i : Individual} {a b : MonetaryValue}
{redi : @Redistribution Individual Individuals government_spending}
{cont : Individual -> MonetaryValue}
(dif : ∀ x ∈ uIcc a b, DifferentiableAt ℝ (
  @retribution_function Individual eqInd Individuals government_spending redi i cont
) x)
(derc : ContinuousOn (deriv (
  @retribution_function Individual eqInd Individuals government_spending redi i cont
)) (uIcc a b)) :
@average_work_incentive Individual eqInd Individuals government_spending i a b redi cont = (
  ∫ c in a..b,
  @instantaneous_work_incentive Individual eqInd Individuals government_spending
  i c redi cont
) / (b - a) := by
  unfold average_work_incentive
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
  rw [<- ftc]

noncomputable def average_work_incentive_until_pos {government_spending : MonetaryValue}
(i : Individual) (redi : @Redistribution Individual Individuals government_spending)
(cont : Individual -> MonetaryValue) :
MonetaryValue -> MonetaryValue :=
  fun M => (
    @average_work_incentive Individual eqInd Individuals government_spending
    i 0 M redi cont
  )

noncomputable def average_work_incentive_until_neg {government_spending : MonetaryValue}
(i : Individual) (redi : @Redistribution Individual Individuals government_spending)
(cont : Individual -> MonetaryValue) :
MonetaryValue -> MonetaryValue :=
  fun m => (
    @average_work_incentive Individual eqInd Individuals government_spending
    i m 0 redi cont
  )

def average_work_incentive_pos_is {government_spending : MonetaryValue}
(i : Individual) (redi : @Redistribution Individual Individuals government_spending)
(cont : Individual -> MonetaryValue) (awip : MonetaryValue) :
Prop :=
  Tendsto (
    @average_work_incentive_until_pos Individual eqInd Individuals government_spending
    i redi cont
  ) atTop (𝓝 awip)

def average_work_incentive_neg_is {government_spending : MonetaryValue}
(i : Individual) (redi : @Redistribution Individual Individuals government_spending)
(cont : Individual -> MonetaryValue) (awin : MonetaryValue) :
Prop :=
  Tendsto (
    @average_work_incentive_until_neg Individual eqInd Individuals government_spending
    i redi cont
  ) atBot (𝓝 awin)

def global_average_work_incentive_is {government_spending : MonetaryValue}
(i : Individual) (redi : @Redistribution Individual Individuals government_spending)
(cont : Individual -> MonetaryValue) (awi : MonetaryValue) :
Prop :=
  ∃ awin awip, (
    @average_work_incentive_pos_is Individual eqInd Individuals government_spending i redi cont awin ∧
    @average_work_incentive_neg_is Individual eqInd Individuals government_spending i redi cont awip ∧
    (awin + awip) / 2 = awi
  )

def sum_other_retributions_positive_if_individual_contribution_big_enough
{government_spending : MonetaryValue}
(i : Individual) (redi : @Redistribution Individual Individuals government_spending)
(cont : Individual -> MonetaryValue) :
Prop :=
  ∃M0, ∀M, M0 ≤ M → 0 ≤ ∑ j ∈ {i}ᶜ, redi.val (replace cont i M) j

theorem average_work_incentive_pos_le_1 {government_spending : MonetaryValue}
{i : Individual} {redi : @Redistribution Individual Individuals government_spending}
{cont : Individual -> MonetaryValue} {awip : MonetaryValue}
(exst :
  @average_work_incentive_pos_is Individual eqInd Individuals government_spending
  i redi cont awip
)
(sorp :
  @sum_other_retributions_positive_if_individual_contribution_big_enough
  Individual eqInd Individuals government_spending i redi cont
) :
awip <= 1 := by
  unfold average_work_incentive_pos_is at exst
  unfold average_work_incentive_until_pos average_work_incentive at exst; simp at exst
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
  have eqtd2p : (
    Tendsto (
      fun M ↦ (redi.val (replace cont i M) i - redi.val (replace cont i 0) i) / M
    ) atTop (𝓝 awip) ↔
    Tendsto (
      fun M ↦ (
        ∑ j, (replace cont i M) j - government_spending -
        ∑ j ∈ {i}ᶜ, redi.val (replace cont i M) j -
        redi.val (replace cont i 0) i
      ) / M
    ) atTop (𝓝 awip)
  ) := by
    apply tendsto_congr'
    unfold EventuallyEq
    unfold Filter.Eventually
    simp
    exists 1
  rw [eqtd2p] at exst
  have dvlp2p : (∀ M, 1 ≤ M →
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
  have eqtd3p : (
    Tendsto (
      fun M ↦ (
        ∑ j, (replace cont i M) j - government_spending -
        ∑ j ∈ {i}ᶜ, redi.val (replace cont i M) j -
        redi.val (replace cont i 0) i
      ) / M
    ) atTop (𝓝 awip) ↔
    Tendsto (
      fun M ↦ 1 + (
        (∑ j ∈ {i}ᶜ, (replace cont i M) j) - government_spending -
        ∑ j ∈ {i}ᶜ, redi.val (replace cont i M) j -
        redi.val (replace cont i 0) i
      ) / M
    ) atTop (𝓝 awip)
  ) := by
    apply tendsto_congr'
    unfold EventuallyEq
    unfold Filter.Eventually
    simp
    exists 1
  rw [eqtd3p] at exst
  have rplup : (
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
  rw [rplup] at exst
  obtain ⟨M0, sorp'⟩ := sorp
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
    specialize (sorp' M)
    have leM0 : M0 ≤ max 1 M0 := by
      exact Std.right_le_max
    have leM1 : M0 ≤ M := by
      exact Std.IsPreorder.le_trans M0 (max 1 M0) M leM0 leM
    specialize (sorp' leM1)
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
      exact sorp'
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
    exact le_of_eq_of_le rfl rdmaj
  have lim0p : (
    Tendsto (
      fun M ↦ (
        (∑ j ∈ {i}ᶜ, cont j) - government_spending -
        redi.val (replace cont i 0) i
      ) / M
    ) atTop (𝓝 0)
  ) := by
    exact Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
  have lim1p : (
    Tendsto (
      fun M ↦ 1 + (
        (∑ j ∈ {i}ᶜ, cont j) - government_spending -
        redi.val (replace cont i 0) i
      ) / M
    ) atTop (𝓝 (1 + 0))
  ) := by
    apply Filter.Tendsto.add
    · apply tendsto_const_nhds
    · apply lim0p
  simp at lim1p
  apply (le_of_tendsto_of_tendsto exst lim1p rdmaj')

def individual_contribution_atBot_dominates_sum_other_retributions
{government_spending : MonetaryValue}
(i : Individual) (redi : @Redistribution Individual Individuals government_spending)
(cont : Individual -> MonetaryValue) :
Prop :=
  Tendsto (
    fun m ↦ (∑ j ∈ {i}ᶜ, redi.val (replace cont i m) j) / m
  ) atBot (𝓝 0)

theorem average_work_incentive_neg_eq_1 {government_spending : MonetaryValue}
{i : Individual} {redi : @Redistribution Individual Individuals government_spending}
{cont : Individual -> MonetaryValue}
(icd :
  @individual_contribution_atBot_dominates_sum_other_retributions
  Individual eqInd Individuals government_spending i redi cont
) : (
  @average_work_incentive_neg_is Individual eqInd Individuals government_spending
  i redi cont 1
) := by
  unfold average_work_incentive_neg_is
  unfold average_work_incentive_until_neg average_work_incentive; simp
  unfold retribution_function
  have rdpty := redi.property
  unfold accounts_at_equilibirum total_value at rdpty
  have dvln : (∀ m, m ≤ -1 →
    (redi.val (replace cont i 0) i - redi.val (replace cont i m) i) / -m =
    (
      redi.val (replace cont i 0) i -
      ∑ j, (replace cont i m) j + government_spending +
      ∑ j ∈ {i}ᶜ, redi.val (replace cont i m) j
    ) / -m
  ) := by
    intro m negm
    rw [div_left_inj']
    · have coarg : (
        - redi.val (replace cont i m) i =
        - ∑ j, replace cont i m j + government_spending +
        ∑ j ∈ {i}ᶜ, redi.val (replace cont i m) j
      ) := by
        rw [<- rdpty]
        simp
        have sumri := Fintype.sum_eq_add_sum_compl i (redi.val (replace cont i m))
        rw [sumri]
        simp
      rw [sub_eq_add_neg]
      rw [coarg]
      linarith
    · intro nem0
      have eqm0 : m = 0 := by
        exact neg_eq_zero.mp nem0
      rw [eqm0] at negm
      linarith
  have eqtd2n : (
    Tendsto (
      fun m ↦ (redi.val (replace cont i 0) i - redi.val (replace cont i m) i) / -m
    ) atBot (𝓝 1) ↔
    Tendsto (
      fun m ↦ (
        redi.val (replace cont i 0) i -
        ∑ j, (replace cont i m) j + government_spending +
        ∑ j ∈ {i}ᶜ, redi.val (replace cont i m) j
      ) / -m
    ) atBot (𝓝 1)
  ) := by
    apply tendsto_congr'
    unfold EventuallyEq
    unfold Filter.Eventually
    simp
    exists -1
  rw [eqtd2n]
  have dvlp2n : (∀ m, m ≤ -1 →
    (
      redi.val (replace cont i 0) i -
      ∑ j, (replace cont i m) j + government_spending +
      ∑ j ∈ {i}ᶜ, redi.val (replace cont i m) j
    ) / -m =
    1 + (
      redi.val (replace cont i 0) i -
      (∑ j ∈ {i}ᶜ, (replace cont i m) j) + government_spending +
      ∑ j ∈ {i}ᶜ, redi.val (replace cont i m) j
    ) / -m
  ) := by
    intro m negm
    have sumci := Fintype.sum_eq_add_sum_compl i (replace cont i m)
    rw [sumci]
    rw [replace_changes]
    rw [div_neg, div_neg]
    field_simp
    ring_nf
    have nem0 : m ≠ 0 := by
      intro eqm0
      rw [eqm0] at negm
      linarith
    rw [mul_inv_cancel₀ nem0]
    simp
    field_simp
    ring_nf
  have eqtd3n : (
    Tendsto (
      fun m ↦ (
        redi.val (replace cont i 0) i -
        ∑ j, (replace cont i m) j + government_spending +
        ∑ j ∈ {i}ᶜ, redi.val (replace cont i m) j
      ) / -m
    ) atBot (𝓝 1) ↔
    Tendsto (
      fun m ↦ 1 + (
        redi.val (replace cont i 0) i -
        (∑ j ∈ {i}ᶜ, (replace cont i m) j) + government_spending +
        ∑ j ∈ {i}ᶜ, redi.val (replace cont i m) j
      ) / -m
    ) atBot (𝓝 (1 + 0 + -0))
  ) := by
    simp; apply tendsto_congr'
    unfold EventuallyEq
    unfold Filter.Eventually
    simp
    exists -1
  rw [eqtd3n]
  have rplun : (
    (fun m ↦ 1 + (
      redi.val (replace cont i 0) i -
      (∑ j ∈ {i}ᶜ, (replace cont i m) j) + government_spending +
      ∑ j ∈ {i}ᶜ, redi.val (replace cont i m) j
    ) / -m) =
    (fun m ↦ 1 + (
      redi.val (replace cont i 0) i -
      (∑ j ∈ {i}ᶜ, cont j) + government_spending +
      ∑ j ∈ {i}ᶜ, redi.val (replace cont i m) j
    ) / -m)
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
  rw [rplun]
  have smdv : (
    (fun m ↦ 1 + (
      redi.val (replace cont i 0) i -
      (∑ j ∈ {i}ᶜ, cont j) + government_spending +
      ∑ j ∈ {i}ᶜ, redi.val (replace cont i m) j
    ) / -m) =
    (fun m ↦ 1 + (- (
      redi.val (replace cont i 0) i -
      (∑ j ∈ {i}ᶜ, cont j) + government_spending
    )) / m - (∑ j ∈ {i}ᶜ, redi.val (replace cont i m) j) / m)
  ) := by
    funext
    field_simp
    ring
  rw [smdv]
  apply Filter.Tendsto.add
  · apply Filter.Tendsto.add
    · apply tendsto_const_nhds
    · apply lim_inverse_bot
  · rw [<- lim_neg_bot]; apply icd

theorem average_work_incentive_le_1 {government_spending : MonetaryValue}
{i : Individual} {redi : @Redistribution Individual Individuals government_spending}
{cont : Individual -> MonetaryValue} {A : MonetaryValue}
(exst :
  @global_average_work_incentive_is Individual eqInd Individuals government_spending
  i redi cont A
)
(sorp :
  @sum_other_retributions_positive_if_individual_contribution_big_enough
  Individual eqInd Individuals government_spending i redi cont
)
(icd :
  @individual_contribution_atBot_dominates_sum_other_retributions
  Individual eqInd Individuals government_spending i redi cont
) :
A <= 1 := by
  unfold global_average_work_incentive_is at exst
  obtain ⟨l, exst2⟩ := exst
  obtain ⟨L, exst⟩ := exst2
  rcases exst with ⟨exstp, exstn, suml⟩
  unfold average_work_incentive_pos_is at exstp
  have limp := average_work_incentive_pos_le_1 exstp sorp
  rw [tendsto_nhds_unique exstn (average_work_incentive_neg_eq_1 icd)] at suml
  rw [← suml]
  linarith

def maximizes_average_work_incentive {government_spending : MonetaryValue}
(i : Individual) (redi : @Redistribution Individual Individuals government_spending)
(cont : Individual -> MonetaryValue) : Prop :=
  @global_average_work_incentive_is Individual eqInd Individuals government_spending
  i redi cont 1

lemma capitalism_maximizes_average_work_incentive (government_spending : MonetaryValue)
(i : Individual) (cont : Individual -> MonetaryValue) :
@maximizes_average_work_incentive Individual eqInd Individuals government_spending i (
  pure_capitalism_costs_equally_divided_Redistribution (
    inhabited_implies_nonnull_card i
  ) government_spending
) cont := by
  unfold maximizes_average_work_incentive global_average_work_incentive_is
  unfold average_work_incentive_pos_is average_work_incentive_neg_is
  unfold average_work_incentive_until_pos average_work_incentive_until_neg
  exists 1
  exists 1
  apply And.intro
  · unfold pure_capitalism_costs_equally_divided_Redistribution
    unfold pure_capitalism_costs_equally_divided
    unfold average_work_incentive
    unfold retribution_function
    simp
    rw [replace_changes]
    have apxt : (fun M ↦ (replace cont i M i - 0) / M) = (fun M ↦ (M - 0) / M) := by
      funext; rw [replace_changes]
    rw [apxt]
    apply lim_frac_deg_1_0_top
  · apply And.intro
    · have eqtdn : (
        Tendsto (fun m ↦
          @average_work_incentive Individual eqInd Individuals government_spending i m 0 ⟨
            fun cont i ↦ cont i - government_spending / ↑(Fintype.card Individual),
            pure_capitalism_costs_equally_divided_at_equilibirum (
              inhabited_implies_nonnull_card i
            ) government_spending
          ⟩ cont
        ) atBot (𝓝 1) ↔
        Tendsto (fun m ↦
          (
            @retribution_function Individual eqInd Individuals government_spending ⟨
              fun cont i ↦ cont i - government_spending / ↑(Fintype.card Individual),
              pure_capitalism_costs_equally_divided_at_equilibirum (
                inhabited_implies_nonnull_card i
              ) government_spending
            ⟩ i cont 0 -
            @retribution_function Individual eqInd Individuals government_spending ⟨
              fun cont i ↦ cont i - government_spending / ↑(Fintype.card Individual),
              pure_capitalism_costs_equally_divided_at_equilibirum (
                inhabited_implies_nonnull_card i
              ) government_spending
            ⟩ i cont m
          ) / -m
        ) atBot (𝓝 1)
      ) := by
        apply tendsto_congr'
        unfold EventuallyEq Filter.Eventually
        unfold average_work_incentive
        simp
      unfold pure_capitalism_costs_equally_divided_Redistribution
      unfold pure_capitalism_costs_equally_divided
      rw [eqtdn]
      unfold retribution_function
      simp
      rw [replace_changes]
      have apxt : (fun m ↦ (0 - replace cont i m i) / -m) = (fun m ↦ (0 - m) / -m) := by
        apply funext
        intro mv
        rw [replace_changes]
      rw [apxt]
      apply lim_frac_deg_1_0_bot
    · simp

def greatest_contributor (cont : Individual -> MonetaryValue) (i : Individual) :
Prop :=
  ∀ j, cont j ≤ cont i

def least_contributor (cont : Individual -> MonetaryValue) (i : Individual) :
Prop :=
  ∀ j, cont i ≤ cont j

def single_greatest_contributor (cont : Individual -> MonetaryValue)
(i : Individual) :
Prop :=
  greatest_contributor cont i ∧ ∀ j, cont j = cont i → j = i

def single_least_contributor (cont : Individual -> MonetaryValue)
(i : Individual) :
Prop :=
  least_contributor cont i ∧ ∀ j, cont j = cont i → j = i

lemma ne_least_greatest_contributor {i j : Individual}
(al2 : 2 ≤Fintype.card Individual) (cont : Individual -> MonetaryValue)
(sgci : single_greatest_contributor cont i)
(slcj : single_least_contributor cont j) :
i ≠ j := by
  intro eqij
  rw [eqij] at sgci
  unfold single_greatest_contributor at sgci
  unfold single_least_contributor at slcj
  have gci := sgci.left; have lcj := slcj.left
  unfold greatest_contributor at gci; unfold least_contributor at lcj
  have eqct : ∀ k, cont k = cont j := by
    intro k; apply le_antisymm (gci k) (lcj k)
  have eqjk : ∀ k, k = j := by
    intro k; apply sgci.right; apply eqct
  have h_sub : Subsingleton Individual := by
    refine' Subsingleton.intro _
    intro a b
    rw [eqjk a, eqjk b]
  have h_unique : ∃ x : Individual, ∀ y, y = x := by
    refine' ⟨j, _⟩
    intro y
    exact eqjk y
  have h_card_one : Fintype.card Individual = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    exact h_unique
  rw [h_card_one] at al2
  norm_num at al2

lemma single_greatest_contributor_unique {i j : Individual}
{cont : Individual -> MonetaryValue} (sgci : single_greatest_contributor cont i)
(sgcj : single_greatest_contributor cont j) :
i = j := by
  apply sgcj.right i
  unfold single_greatest_contributor greatest_contributor at sgci sgcj
  have leji := sgci.left j; have leij := sgcj.left i
  apply le_antisymm
  · exact leij
  · exact leji

lemma single_least_contributor_unique {i j : Individual}
{cont : Individual -> MonetaryValue} (slci : single_least_contributor cont i)
(slcj : single_least_contributor cont j) :
i = j := by
  apply slcj.right i
  unfold single_least_contributor least_contributor at slci slcj
  have leij := slci.left j; have leji := slcj.left i
  apply le_antisymm
  · exact leij
  · exact leji

noncomputable def communism_except_extremal_contributors
(government_spending : MonetaryValue)
(cont : Individual -> MonetaryValue) :
Individual -> MonetaryValue :=
  fun i => (
    if single_greatest_contributor cont i then cont i
    else if single_least_contributor cont i then cont i
    else (
      (∑ i ∈ Finset.univ.filter (
        fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
      ), cont i - government_spending) /
      ((Finset.univ.filter (
        fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
      )).card : MonetaryValue)
    )
  )

lemma communism_except_extremal_contributors_at_equilibirum
(al3 : 3 ≤ Fintype.card Individual) (government_spending : MonetaryValue) :
@accounts_at_equilibirum Individual Individuals government_spending (
  @communism_except_extremal_contributors Individual Individuals government_spending
) := by
  have al2 : 2 ≤ Fintype.card Individual := by
    exact Nat.le_of_add_left_le al3
  have inh : Fintype.card Individual ≠ 0 := by
    exact Nat.ne_zero_of_lt al2
  intro cont
  have coerd : (
    @Nat.cast MonetaryValue semiring.toNonAssocSemiring.toAddCommMonoidWithOne.toNatCast (Fintype.card Individual) =
    @Nat.cast ℝ instNatCast (Fintype.card Individual)
  ) := by
    exact Nat.cast_inj.mpr rfl
  by_cases sgcn : ∀ i, ¬ single_greatest_contributor cont i
  · by_cases slcn : ∀ i, ¬ single_least_contributor cont i
    · have rwsum : (
        @communism_except_extremal_contributors Individual Individuals
        government_spending cont = (
          fun i ↦ if single_least_contributor cont i then cont i else (
            (∑ i ∈ Finset.univ.filter (
              fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
            ), cont i - government_spending) /
            ((Finset.univ.filter (
              fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
            )).card : MonetaryValue)
          )
        )
      ) := by
        unfold communism_except_extremal_contributors
        apply funext
        intro i
        specialize (sgcn i)
        simp
        intro sgc
        exfalso
        apply sgcn
        exact sgc
      rw [rwsum]
      have rwsm2 : (
        (fun i ↦ if single_least_contributor cont i then cont i else (
          (∑ i ∈ Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          ), cont i - government_spending) /
          ((Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          )).card : MonetaryValue)
        )) = (fun i ↦ (
          ∑ i ∈ Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          ), cont i - government_spending) /
          ((Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          )).card : MonetaryValue
        ))
      ) := by
        apply funext
        intro i
        specialize (slcn i)
        simp
        intro slc
        exfalso
        apply slcn
        exact slc
      rw [rwsm2]
      unfold total_value; rw [Finset.sum_const]
      have eqcrd : (
        ((Finset.univ.filter (
          fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
        )).card : ℝ) =
        (Fintype.card Individual : ℝ)
      ) := by
        apply Nat.cast_inj.mpr
        refine (Finset.card_eq_iff_eq_univ {
          i | ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
        }).mpr ?_
        refine Finset.filter_true_of_mem ?_
        intro i iin
        apply And.intro
        · apply sgcn
        · apply slcn
      rw [eqcrd]; simp
      have coerc : (
        @Nat.cast MonetaryValue semiring.toNonAssocSemiring.toAddCommMonoidWithOne.toNatCast (Fintype.card Individual) =
        @Nat.cast ℝ instNatCast (Fintype.card Individual)
      ) := by
        exact Nat.cast_inj.mpr rfl
      rw [coerc]
      rw [div_eq_mul_inv]; rw [mul_comm]; rw [mul_assoc]
      rw [Lean.Grind.Field.inv_mul_cancel]
      · simp; exact Finset.sum_filter_of_ne fun x a a_1 ↦ And.intro (sgcn x) (slcn x)
      · exact Nat.cast_ne_zero.mpr inh
    · simp at slcn
      obtain ⟨i, slci⟩ := slcn
      unfold total_value
      have rwsum : (
        @communism_except_extremal_contributors Individual Individuals
        government_spending cont = (
          fun i ↦ if single_least_contributor cont i then cont i else (
            (∑ i ∈ Finset.univ.filter (
              fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
            ), cont i - government_spending) /
            ((Finset.univ.filter (
              fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
            )).card : MonetaryValue)
          )
        )
      ) := by
        unfold communism_except_extremal_contributors
        apply funext
        intro i
        specialize (sgcn i)
        simp
        intro sgc
        exfalso
        apply sgcn
        exact sgc
      rw [rwsum]; simp
      have disj : (
        ∑ x, if single_least_contributor cont x then cont x else (
          (∑ i ∈ Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          ), cont i - government_spending) /
          ((Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          )).card : MonetaryValue)
        )
      ) = (
        ∑ x ∈ {i}, if single_least_contributor cont x then cont x else (
          (∑ i ∈ Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          ), cont i - government_spending) /
          ((Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          )).card : MonetaryValue)
        )
      ) + (
        ∑ x ∈ {i}ᶜ, if single_least_contributor cont x then cont x else (
          (∑ i ∈ Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          ), cont i - government_spending) /
          ((Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          )).card : MonetaryValue)
        )
      ) := by
        rw [← Finset.sum_union]
        · simp
        · rw [Finset.disjoint_singleton_left]
          simp
      rw [disj]; simp; simp [slci]
      have sglcn : (
        ∀ j, j ∈ ({i} : Finset Individual)ᶜ →
          ¬ single_greatest_contributor cont j ∧ ¬ single_least_contributor cont j
      ) := by
        intro j neji
        apply And.intro
        · apply sgcn
        · intro slcj; simp at neji; apply neji
          apply slci.right
          unfold single_least_contributor least_contributor at slcj slci
          have leij := slci.left j
          have leji := slcj.left i
          apply le_antisymm
          · exact leji
          · exact leij
      have rwsm2 : (
        ∑ x ∈ {i}ᶜ, if single_least_contributor cont x then cont x else (
          (∑ i ∈ Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          ), cont i - government_spending) /
          ((Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          )).card : MonetaryValue)
        )
      ) = (
        ∑ x ∈ {i}ᶜ,
        (∑ i ∈ Finset.univ.filter (
          fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
        ), cont i - government_spending) /
        ((Finset.univ.filter (
          fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
        )).card : MonetaryValue)
      ) := by
        apply Finset.sum_congr
        · rfl
        · intro j neji
          simp
          intro sgc
          specialize sglcn j neji
          tauto
      rw [rwsm2]
      rw [Finset.sum_const]
      have eqset : (
        ({i}ᶜ : Finset Individual) =
        (Finset.univ.filter (fun i =>
          ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
        ))
      ) := by
        refine Finset.ext_iff.mpr ?_
        intro j
        apply Iff.intro
        · simp; intro neji
          apply And.intro
          · apply sgcn
          · intro slcj
            apply neji
            apply single_least_contributor_unique slcj slci
        · simp; intro nsgcj nslcj eqji; apply nslcj
          rw [eqji]; exact slci
      have eqcrd : (
        ({i}ᶜ : Finset Individual).card = (Finset.univ.filter (
          fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
        )).card
      ) := by
        exact Nat.cast_inj.mpr (congrArg Finset.card eqset)
      rw [<- eqcrd]
      ring_nf; rw [mul_assoc]; rw [mul_assoc]
      rw [Lean.Grind.Field.mul_inv_cancel]
      · rw [mul_one]; rw [mul_one]
        ring_nf
        have sumd : (
          (∑ i ∈ Finset.univ.filter (
            fun i => single_greatest_contributor cont i ∨ single_least_contributor cont i
          ), cont i) +
          (∑ i ∈ Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          ), cont i) =
          ∑ i, cont i
        ) := by
          simp_rw [← not_or]
          exact Finset.sum_filter_add_sum_filter_not Finset.univ _ cont
        rw [<- sumd]
        have sing : (
          Finset.univ.filter (
            fun i => single_greatest_contributor cont i ∨ single_least_contributor cont i
          ) = {i}
        ) := by
          refine Finset.eq_singleton_iff_unique_mem.mpr ?_
          apply And.intro
          · simp; right; exact slci
          · simp; intro j sglcj
            simp [sgcn] at sglcj
            apply single_least_contributor_unique sglcj slci
        have sumi : (
          (∑ i ∈ Finset.univ.filter (
            fun i => single_greatest_contributor cont i ∨ single_least_contributor cont i
          ), cont i) = cont i
        ) := by
          rw [sing]
          rw [Finset.sum_singleton]
        rw [sumi]
      · intro inh'; simp at inh'
        have card1 : Fintype.card Individual = 1 := by
          rw [← Finset.card_univ, ← inh']
          simp
        rw [card1] at al2
        simp at al2
  · by_cases slcn : ∀ i, ¬ single_least_contributor cont i
    · simp at sgcn
      obtain ⟨i, sgci⟩ := sgcn
      unfold total_value
      have rwsum : (
        @communism_except_extremal_contributors Individual Individuals
        government_spending cont = (
          fun i ↦ if single_greatest_contributor cont i then cont i else (
            (∑ i ∈ Finset.univ.filter (
              fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
            ), cont i - government_spending) /
            ((Finset.univ.filter (
              fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
            )).card : MonetaryValue)
          )
        )
      ) := by
        unfold communism_except_extremal_contributors
        apply funext
        intro j
        specialize (slcn j)
        by_cases sgcj : single_greatest_contributor cont j
        · simp [sgcj]
        · simp [sgcj]
          tauto
      rw [rwsum]; simp
      have disj : (
        ∑ x, if single_greatest_contributor cont x then cont x else (
          (∑ i ∈ Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          ), cont i - government_spending) /
          ((Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          )).card : MonetaryValue)
        )
      ) = (
        ∑ x ∈ {i}, if single_greatest_contributor cont x then cont x else (
          (∑ i ∈ Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          ), cont i - government_spending) /
          ((Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          )).card : MonetaryValue)
        )
      ) + (
        ∑ x ∈ {i}ᶜ, if single_greatest_contributor cont x then cont x else (
          (∑ i ∈ Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          ), cont i - government_spending) /
          ((Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          )).card : MonetaryValue)
        )
      ) := by
        rw [← Finset.sum_union]
        · simp
        · rw [Finset.disjoint_singleton_left]; simp
      rw [disj]; simp; simp [sgci]
      have sglcn : (
        ∀ j, j ∈ ({i} : Finset Individual)ᶜ →
          ¬ single_greatest_contributor cont j ∧ ¬ single_least_contributor cont j
      ) := by
        intro j neji
        apply And.intro
        · intro sgcj; simp at neji; apply neji
          apply sgci.right
          unfold single_greatest_contributor greatest_contributor at sgcj sgci
          have leij := sgci.left j
          have leji := sgcj.left i
          apply le_antisymm
          · exact leij
          · exact leji
        · apply slcn
      have rwsm2 : (
        ∑ x ∈ {i}ᶜ, if single_greatest_contributor cont x then cont x else (
          (∑ i ∈ Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          ), cont i - government_spending) /
          ((Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          )).card : MonetaryValue)
        )
      ) = (
        ∑ x ∈ {i}ᶜ,
        (∑ i ∈ Finset.univ.filter (
          fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
        ), cont i - government_spending) /
        ((Finset.univ.filter (
          fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
        )).card : MonetaryValue)
      ) := by
        apply Finset.sum_congr
        · rfl
        · intro j neji
          simp
          intro sgc
          specialize sglcn j neji
          tauto
      rw [rwsm2]
      rw [Finset.sum_const]
      have eqset : (
        ({i}ᶜ : Finset Individual) =
        (Finset.univ.filter (fun i =>
          ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
        ))
      ) := by
        refine Finset.ext_iff.mpr ?_
        intro j
        apply Iff.intro
        · simp; intro neji
          apply And.intro
          · intro sgcj
            apply neji
            apply single_greatest_contributor_unique sgcj sgci
          · apply slcn
        · simp; intro nsgcj nslcj eqji; apply nsgcj
          rw [eqji]; exact sgci
      have eqcrd : (
        ({i}ᶜ : Finset Individual).card = (Finset.univ.filter (
          fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
        )).card
      ) := by
        exact Nat.cast_inj.mpr (congrArg Finset.card eqset)
      rw [<- eqcrd]
      ring_nf; rw [mul_assoc]; rw [mul_assoc]
      rw [Lean.Grind.Field.mul_inv_cancel]
      · rw [mul_one]; rw [mul_one]
        ring_nf
        have sumd : (
          (∑ i ∈ Finset.univ.filter (
            fun i => single_greatest_contributor cont i ∨ single_least_contributor cont i
          ), cont i) +
          (∑ i ∈ Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          ), cont i) =
          ∑ i, cont i
        ) := by
          simp_rw [← not_or]
          exact Finset.sum_filter_add_sum_filter_not Finset.univ _ cont
        rw [<- sumd]
        have sing : (
          Finset.univ.filter (
            fun i => single_greatest_contributor cont i ∨ single_least_contributor cont i
          ) = {i}
        ) := by
          refine Finset.eq_singleton_iff_unique_mem.mpr ?_
          apply And.intro
          · simp; left; exact sgci
          · simp; intro j sglcj
            simp [slcn] at sglcj
            apply single_greatest_contributor_unique sglcj sgci
        have sumi : (
          (∑ i ∈ Finset.univ.filter (
            fun i => single_greatest_contributor cont i ∨ single_least_contributor cont i
          ), cont i) = cont i
        ) := by
          rw [sing]
          rw [Finset.sum_singleton]
        rw [sumi]
      · intro inh'; simp at inh'
        have card1 : Fintype.card Individual = 1 := by
          rw [← Finset.card_univ, ← inh']
          simp
        rw [card1] at al2
        simp at al2
    · simp at sgcn
      obtain ⟨i, sgci⟩ := sgcn
      simp at slcn
      obtain ⟨j, slcj⟩ := slcn
      unfold total_value communism_except_extremal_contributors
      have disj : (
        (
          ∑ x,
          if single_greatest_contributor cont x then cont x
          else if single_least_contributor cont x then cont x
          else (
            (∑ i ∈ Finset.univ.filter (
              fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
            ), cont i - government_spending) /
            ((Finset.univ.filter (
              fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
            )).card : MonetaryValue)
          )
        ) = (
          ∑ x ∈ {i},
          if single_greatest_contributor cont x then cont x
          else if single_least_contributor cont x then cont x
          else (
            (∑ i ∈ Finset.univ.filter (
              fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
            ), cont i - government_spending) /
            ((Finset.univ.filter (
              fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
            )).card : MonetaryValue)
          )
        ) + (
          ∑ x ∈ {j},
          if single_greatest_contributor cont x then cont x
          else if single_least_contributor cont x then cont x
          else (
            (∑ i ∈ Finset.univ.filter (
              fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
            ), cont i - government_spending) /
            ((Finset.univ.filter (
              fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
            )).card : MonetaryValue)
          )
        ) + (
          ∑ x ∈ {i, j}ᶜ,
          if single_greatest_contributor cont x then cont x
          else if single_least_contributor cont x then cont x
          else (
            (∑ i ∈ Finset.univ.filter (
              fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
            ), cont i - government_spending) /
            ((Finset.univ.filter (
              fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
            )).card : MonetaryValue)
          )
        )
      ) := by
        rw [← Finset.sum_union]
        · rw [union_of_singletons_finset i j]
          apply sum_split_two
        · rw [Finset.disjoint_singleton_left]
          refine Finset.notMem_singleton.mpr ?_
          apply ne_least_greatest_contributor al2 cont sgci slcj
      rw [disj]; simp; simp [sgci]; simp [slcj]
      have sglcn : (
        ∀ k, k ∈ ({j} : Finset Individual)ᶜ.erase i →
          ¬ single_greatest_contributor cont k ∧ ¬ single_least_contributor cont k
      ) := by
        intro k neijk
        apply And.intro
        · intro sgcj; simp at neijk; apply neijk.left
          apply single_greatest_contributor_unique sgcj sgci
        · intro slck
          have eqkj := single_least_contributor_unique slck slcj; rw [eqkj] at neijk
          simp at neijk
      have rwsm2 : (
        ∑ x ∈ ({j} : Finset Individual)ᶜ.erase i,
        if single_greatest_contributor cont x then cont x
        else if single_least_contributor cont x then cont x
        else (
          (∑ i ∈ Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          ), cont i - government_spending) /
          ((Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          )).card : MonetaryValue)
        )
      ) = (
        ∑ x ∈ ({j} : Finset Individual)ᶜ.erase i,
        (∑ i ∈ Finset.univ.filter (
          fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
        ), cont i - government_spending) /
        ((Finset.univ.filter (
          fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
        )).card : MonetaryValue)
      ) := by
        apply Finset.sum_congr
        · rfl
        · intro k nekij
          specialize sglcn k nekij
          simp [sglcn.left]; simp [sglcn.right]
      rw [rwsm2]
      rw [Finset.sum_const]
      have eqset : (
        ({j} : Finset Individual)ᶜ.erase i =
        (Finset.univ.filter (fun k =>
          ¬ single_greatest_contributor cont k ∧ ¬ single_least_contributor cont k
        ))
      ) := by
        refine Finset.ext_iff.mpr ?_
        intro k
        apply Iff.intro
        · simp; intro neki nekj
          apply And.intro
          · intro sgck
            apply neki
            apply single_greatest_contributor_unique sgck sgci
          · intro slck
            apply nekj
            apply single_least_contributor_unique slck slcj
        · simp; intro nsgck nslck
          apply And.intro
          · intro eqki; apply nsgck
            rw [eqki]; exact sgci
          · intro eqkj; apply nslck
            rw [eqkj]; exact slcj
      have eqcrd : (
        (({j} : Finset Individual)ᶜ.erase i).card = (Finset.univ.filter (
          fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
        )).card
      ) := by
        exact Nat.cast_inj.mpr (congrArg Finset.card eqset)
      rw [<- eqcrd]
      ring_nf; rw [mul_assoc]; rw [mul_assoc]
      have neij := ne_least_greatest_contributor al2 cont sgci slcj
      rw [Lean.Grind.Field.mul_inv_cancel]
      · rw [mul_one]; rw [mul_one]
        ring_nf
        have sumd : (
          (∑ i ∈ Finset.univ.filter (
            fun i => single_greatest_contributor cont i ∨ single_least_contributor cont i
          ), cont i) +
          (∑ i ∈ Finset.univ.filter (
            fun i => ¬ single_greatest_contributor cont i ∧ ¬ single_least_contributor cont i
          ), cont i) =
          ∑ i, cont i
        ) := by
          simp_rw [← not_or]
          exact Finset.sum_filter_add_sum_filter_not Finset.univ _ cont
        rw [<- sumd]
        have sing : (
          Finset.univ.filter (
            fun k => single_greatest_contributor cont k ∨ single_least_contributor cont k
          ) = {i, j}
        ) := by
          ext k
          constructor
          · intro hk
            simp at hk
            rcases hk with hkg | hkl
            · have : k = i :=
                single_greatest_contributor_unique hkg sgci
              simp [this]
            · have : k = j :=
                single_least_contributor_unique hkl slcj
              simp [this]
          · intro hk
            simp at hk
            rcases hk with rfl | rfl
            · simp [sgci]
            · simp [slcj]
        have sumi : (
          (∑ k ∈ Finset.univ.filter (
            fun k => single_greatest_contributor cont k ∨ single_least_contributor cont k
          ), cont k) = cont i + cont j
        ) := by
          rw [sing]
          rw [Finset.sum_pair neij]
        rw [sumi]
      · refine Nat.cast_ne_zero.mpr ?_
        have h_card : #(({j} : Finset Individual)ᶜ.erase i) = Fintype.card Individual - 2 := by
          calc
            #(({j} : Finset Individual)ᶜ.erase i) = #({j}ᶜ) - 1 := by
              have h_mem : i ∈ ({j}ᶜ : Finset Individual) := by
                simp [neij]
              rw [Finset.card_erase_of_mem h_mem]
            _ = (Fintype.card Individual - 1) - 1 := by
              rw [Finset.card_compl]
              simp
            _ = Fintype.card Individual - 2 := by
              omega
        rw [h_card]
        have h_pos : Fintype.card Individual - 2 > 0 := by
          have h : Fintype.card Individual ≥ 3 := al3
          omega
        exact Nat.pos_iff_ne_zero.mp h_pos

noncomputable def communism_except_extremal_contributors_Redistribution
(al3 : 3 ≤Fintype.card Individual) (government_spending : MonetaryValue) :
@Redistribution Individual Individuals government_spending :=
  ⟨ communism_except_extremal_contributors government_spending,
    communism_except_extremal_contributors_at_equilibirum al3 government_spending ⟩

lemma communism_except_extremal_contributors_maximizes_average_work_incentive
(al3 : 3 ≤Fintype.card Individual) (government_spending : MonetaryValue)
(i : Individual) (cont : Individual -> MonetaryValue) :
@maximizes_average_work_incentive Individual eqInd Individuals government_spending i (
  communism_except_extremal_contributors_Redistribution al3 government_spending
) cont := by
  unfold maximizes_average_work_incentive global_average_work_incentive_is
  unfold average_work_incentive_pos_is average_work_incentive_neg_is
  unfold average_work_incentive_until_pos average_work_incentive_until_neg
  exists 1
  exists 1
  have inh : Nonempty Individual := by
    exact Nonempty.intro i
  apply And.intro
  · have ttgc : Tendsto (fun M ↦
      @average_work_incentive Individual eqInd Individuals government_spending i 0 M (
        communism_except_extremal_contributors_Redistribution al3 government_spending
      ) cont
    ) atTop (𝓝 1) ↔ Tendsto (
      fun M  : ℝ ↦
      (M - (
        if single_greatest_contributor (replace cont i 0) i then replace cont i 0 i
        else if single_least_contributor (replace cont i 0) i then replace cont i 0 i
        else (∑ i_1 with (
          ¬single_greatest_contributor (replace cont i 0) i_1 ∧ ¬single_least_contributor (replace cont i 0) i_1
        ), replace cont i 0 i_1 - government_spending) /
        ↑(#{i_1 | ¬single_greatest_contributor (replace cont i 0) i_1 ∧ ¬single_least_contributor (replace cont i 0) i_1})
      )) / M
    ) atTop (𝓝 (1 + 0)) := by
      unfold communism_except_extremal_contributors_Redistribution
      unfold communism_except_extremal_contributors
      unfold average_work_incentive retribution_function; simp
      apply tendsto_congr'
      unfold EventuallyEq
      unfold Filter.Eventually
      simp
      exists (Finset.univ.image cont).max' (by simp) + 1
      intro M leb
      rw [replace_changes]
      have sgcM : single_greatest_contributor (replace cont i M) i := by
        unfold single_greatest_contributor greatest_contributor
        have incr : (
          (Finset.univ.image cont).max' (by simp) <
          (Finset.univ.image cont).max' (by simp) + 1
        ) := by
          linarith
        apply And.intro
        · intro j; rw [replace_changes]
          by_cases eqij : i = j
          · rw [eqij]; rw [replace_changes]
          · rw [replace_unchanges]
            · have leM := Finset.le_max' (Finset.univ.image cont) (cont j) (by simp)
              apply le_of_lt
              apply lt_of_le_of_lt leM (lt_of_le_of_lt' leb incr)
            · tauto
        · intro j; rw [replace_changes]
          contrapose; intro neji
          rw [replace_unchanges]
          · intro eqcjM
            have leM := Finset.le_max' (Finset.univ.image cont) (cont j) (by simp)
            rw [<- eqcjM] at leb
            have contr := le_trans leb leM
            simp at contr; linarith
          · tauto
      simp [sgcM]
    rw [ttgc]
    have dstr : (
      fun M  : ℝ ↦
      (M - (
        if single_greatest_contributor (replace cont i 0) i then replace cont i 0 i
        else if single_least_contributor (replace cont i 0) i then replace cont i 0 i
        else (∑ i_1 with (
          ¬single_greatest_contributor (replace cont i 0) i_1 ∧ ¬single_least_contributor (replace cont i 0) i_1
        ), replace cont i 0 i_1 - government_spending) /
        ↑(#{i_1 | ¬single_greatest_contributor (replace cont i 0) i_1 ∧ ¬single_least_contributor (replace cont i 0) i_1})
      )) / M
    ) = (
      fun M  : ℝ ↦
      M / M - (
        if single_greatest_contributor (replace cont i 0) i then replace cont i 0 i
        else if single_least_contributor (replace cont i 0) i then replace cont i 0 i
        else (∑ i_1 with (
          ¬single_greatest_contributor (replace cont i 0) i_1 ∧ ¬single_least_contributor (replace cont i 0) i_1
        ), replace cont i 0 i_1 - government_spending) /
        ↑(#{i_1 | ¬single_greatest_contributor (replace cont i 0) i_1 ∧ ¬single_least_contributor (replace cont i 0) i_1})
      ) / M
    ) := by
      apply funext; intro x
      exact
        sub_div x
          (if single_greatest_contributor (replace cont i 0) i then replace cont i 0 i
          else
            if single_least_contributor (replace cont i 0) i then replace cont i 0 i
            else
              (∑ i_1 with
                    ¬single_greatest_contributor (replace cont i 0) i_1 ∧
                      ¬single_least_contributor (replace cont i 0) i_1,
                    replace cont i 0 i_1 -
                  government_spending) /
                ↑(#{i_1 |
                      ¬single_greatest_contributor (replace cont i 0) i_1 ∧
                        ¬single_least_contributor (replace cont i 0) i_1})) x
    rw [dstr]
    apply Filter.Tendsto.add
    · have lfd := lim_frac_deg_1_0_top 0
      simp at lfd; exact lfd
    · rw [lim_neg_top]; simp; apply lim_inverse_top (if single_greatest_contributor (replace cont i 0) i then replace cont i 0 i
      else
        if single_least_contributor (replace cont i 0) i then replace cont i 0 i
        else
          (∑ i_1 with
                ¬single_greatest_contributor (replace cont i 0) i_1 ∧ ¬single_least_contributor (replace cont i 0) i_1,
                replace cont i 0 i_1 -
              government_spending) /
            ↑(#{i_1 |
                  ¬single_greatest_contributor (replace cont i 0) i_1 ∧
                    ¬single_least_contributor (replace cont i 0) i_1}))
  · have ttlc : Tendsto (fun m ↦
      @average_work_incentive Individual eqInd Individuals government_spending i m 0 (
        communism_except_extremal_contributors_Redistribution al3 government_spending
      ) cont
    ) atBot (𝓝 1) ↔ Tendsto (
      fun m  : ℝ ↦
      ((
        if single_greatest_contributor (replace cont i 0) i then replace cont i 0 i
        else if single_least_contributor (replace cont i 0) i then replace cont i 0 i
        else (∑ i_1 with (
          ¬single_greatest_contributor (replace cont i 0) i_1 ∧ ¬single_least_contributor (replace cont i 0) i_1
        ), replace cont i 0 i_1 - government_spending) /
        ↑(#{i_1 | ¬single_greatest_contributor (replace cont i 0) i_1 ∧ ¬single_least_contributor (replace cont i 0) i_1})
      ) - m) / -m
    ) atBot (𝓝 (0 + 1)) := by
      unfold communism_except_extremal_contributors_Redistribution
      unfold communism_except_extremal_contributors
      unfold average_work_incentive retribution_function; simp
      apply tendsto_congr'
      unfold EventuallyEq
      unfold Filter.Eventually
      simp
      exists (Finset.univ.image cont).min' (by simp) - 1
      intro m leb
      rw [replace_changes]
      have slcm : single_least_contributor (replace cont i m) i := by
        unfold single_least_contributor least_contributor
        have incr : (
          (Finset.univ.image cont).min' (by simp) - 1 <
          (Finset.univ.image cont).min' (by simp)
        ) := by
          linarith
        apply And.intro
        · intro j; rw [replace_changes]
          by_cases eqij : i = j
          · rw [eqij]; rw [replace_changes]
          · rw [replace_unchanges]
            · have lem := Finset.min'_le (Finset.univ.image cont) (cont j) (by simp)
              apply le_of_lt
              apply lt_of_le_of_lt' lem (lt_of_le_of_lt leb incr)
            · tauto
        · intro j; rw [replace_changes]
          contrapose; intro neji
          rw [replace_unchanges]
          · intro eqcjm
            have lem := Finset.min'_le (Finset.univ.image cont) (cont j) (by simp)
            rw [<- eqcjm] at leb
            have contr := le_trans lem leb
            simp at contr; linarith
          · tauto
      simp [slcm]; rw [replace_changes]
    rw [ttlc]
    have dstr : (
      fun m  : ℝ ↦
      ((
        if single_greatest_contributor (replace cont i 0) i then replace cont i 0 i
        else if single_least_contributor (replace cont i 0) i then replace cont i 0 i
        else (∑ i_1 with (
          ¬single_greatest_contributor (replace cont i 0) i_1 ∧ ¬single_least_contributor (replace cont i 0) i_1
        ), replace cont i 0 i_1 - government_spending) /
        ↑(#{i_1 | ¬single_greatest_contributor (replace cont i 0) i_1 ∧ ¬single_least_contributor (replace cont i 0) i_1})
      ) - m) / -m
    ) = (
      fun m  : ℝ ↦
      (-(
        if single_greatest_contributor (replace cont i 0) i then replace cont i 0 i
        else if single_least_contributor (replace cont i 0) i then replace cont i 0 i
        else (∑ i_1 with (
          ¬single_greatest_contributor (replace cont i 0) i_1 ∧ ¬single_least_contributor (replace cont i 0) i_1
        ), replace cont i 0 i_1 - government_spending) /
        ↑(#{i_1 | ¬single_greatest_contributor (replace cont i 0) i_1 ∧ ¬single_least_contributor (replace cont i 0) i_1})
      )) / m + m / m
    ) := by
      apply funext; intro x
      field_simp [sub_eq_add_neg, add_comm]
      ring
    rw [dstr]
    apply And.intro
    · apply Filter.Tendsto.add
      · exact
        lim_inverse_bot
          (-if single_greatest_contributor (replace cont i 0) i then replace cont i 0 i
            else
              if single_least_contributor (replace cont i 0) i then replace cont i 0 i
              else
                (∑ i_1 with
                      ¬single_greatest_contributor (replace cont i 0) i_1 ∧
                        ¬single_least_contributor (replace cont i 0) i_1,
                      replace cont i 0 i_1 -
                    government_spending) /
                  ↑(#{i_1 |
                        ¬single_greatest_contributor (replace cont i 0) i_1 ∧
                          ¬single_least_contributor (replace cont i 0) i_1}))
      · have lfd := lim_frac_deg_1_0_bot 0
        simp at lfd; exact lfd
    · simp

end maximizing_average_work_incentive
