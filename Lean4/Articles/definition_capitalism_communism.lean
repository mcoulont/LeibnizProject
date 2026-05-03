
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

import Tools.eqtype
import Tools.function
import Tools.permutations
import Tools.fintype
import Articles.ethics_in_society

namespace definition_capitalism_communism

variable {Individual : Type}
variable {eqInd : DecidableEq Individual}
variable {Individuals : Fintype Individual}

open Finset BigOperators Equiv
open ethics_in_society

@[reducible]
def MonetaryValue : Type := ℝ

def total_value (dist : @Profile Individual MonetaryValue) : MonetaryValue :=
  ∑ i : Individual, dist i

def accounts_at_equilibirum (government_spending : MonetaryValue)
(redi : @Profile Individual MonetaryValue -> @Profile Individual MonetaryValue) :
Prop :=
  ∀ (dist : @Profile Individual MonetaryValue),
    @total_value Individual Individuals (redi dist) + government_spending =
    @total_value Individual Individuals dist

@[reducible]
def Redistribution (government_spending : MonetaryValue) : Type :=
  {
    redi : @Profile Individual MonetaryValue -> @Profile Individual MonetaryValue //
    @accounts_at_equilibirum Individual Individuals government_spending redi
  }

def pure_capitalism :
@Profile Individual MonetaryValue -> @Profile Individual MonetaryValue :=
  id

noncomputable def pure_capitalism_costs_equally_divided
(government_spending : MonetaryValue) :
@Profile Individual MonetaryValue -> @Profile Individual MonetaryValue :=
  fun (cont : @Profile Individual MonetaryValue) => fun i =>
  cont i - government_spending / Fintype.card Individual

lemma pure_capitalism_costs_equally_divided_0 :
@pure_capitalism_costs_equally_divided Individual Individuals 0 =
@pure_capitalism Individual := by
  unfold pure_capitalism_costs_equally_divided pure_capitalism
  apply funext
  simp

lemma pure_capitalism_costs_equally_divided_at_equilibirum
(inh : Fintype.card Individual ≠ 0) (government_spending : MonetaryValue) :
@accounts_at_equilibirum Individual Individuals government_spending (
  @pure_capitalism_costs_equally_divided Individual Individuals government_spending
) := by
  unfold pure_capitalism_costs_equally_divided accounts_at_equilibirum
  intro dist
  unfold total_value
  simp
  rw [mul_comm]
  rw [division_def]
  rw [mul_assoc]
  rw [inv_mul_cancel₀]
  · simp
  · exact Nat.cast_ne_zero.mpr inh

noncomputable def pure_capitalism_costs_equally_divided_Redistribution
(inh : Fintype.card Individual ≠ 0) (government_spending : MonetaryValue) :
@Redistribution Individual Individuals government_spending :=
  ⟨ pure_capitalism_costs_equally_divided government_spending,
    pure_capitalism_costs_equally_divided_at_equilibirum inh government_spending ⟩

def pure_capitalism_Redistribution (inh : Fintype.card Individual ≠ 0) :
@Redistribution Individual Individuals 0 :=
  ⟨
    pure_capitalism,
    pure_capitalism_costs_equally_divided_0 ▸
    pure_capitalism_costs_equally_divided_at_equilibirum inh 0
  ⟩

noncomputable def pure_communism (government_spending : MonetaryValue) :
@Profile Individual MonetaryValue -> @Profile Individual MonetaryValue :=
  fun (cont : @Profile Individual MonetaryValue) => fun _ =>
  (@total_value Individual Individuals cont - government_spending) /
  (Fintype.card Individual : MonetaryValue)

lemma pure_communism_at_equilibirum (inh : Fintype.card Individual ≠ 0)
(government_spending : MonetaryValue) :
@accounts_at_equilibirum Individual Individuals government_spending
(@pure_communism Individual Individuals government_spending) := by
  unfold pure_communism accounts_at_equilibirum total_value
  intro dist
  simp
  rw [mul_div_cancel_of_imp']
  · simp
  · intro emp
    exfalso
    apply inh
    exact Nat.cast_eq_zero.mp emp

noncomputable def pure_communism_Redistribution (inh : Fintype.card Individual ≠ 0)
(government_spending : MonetaryValue) :
@Redistribution Individual Individuals government_spending :=
  ⟨ pure_communism government_spending,
    pure_communism_at_equilibirum inh government_spending ⟩

def is_egalitarian (government_spending : MonetaryValue)
(redi : @Redistribution Individual Individuals government_spending) :
Prop :=
  ∀ (σ : Perm Individual) (cont : @Profile Individual MonetaryValue),
    PermutationsActingOnFunctions (redi.val cont) σ =
    redi.val (PermutationsActingOnFunctions cont σ)

lemma capitalism_is_egalitarian (inh : Fintype.card Individual ≠ 0)
(government_spending : MonetaryValue) :
@is_egalitarian Individual Individuals government_spending (
  pure_capitalism_costs_equally_divided_Redistribution inh government_spending
 ) := by
  tauto

lemma communism_is_egalitarian (inh : Fintype.card Individual ≠ 0)
(government_spending : MonetaryValue) :
@is_egalitarian Individual Individuals government_spending (
  pure_communism_Redistribution inh government_spending
) := by
  unfold is_egalitarian pure_communism_Redistribution
  simp
  unfold pure_communism PermutationsActingOnFunctions total_value
  intro σ cont
  apply funext
  intro ind
  refine (div_eq_div_iff ?_ ?_).mpr ?_
  · exact Nat.cast_ne_zero.mpr inh
  · exact Nat.cast_ne_zero.mpr inh
  · refine (mul_left_inj' ?_).mpr ?_
    · exact Nat.cast_ne_zero.mpr inh
    · simp
      rw [<- sum_reals_perm]
      tauto

def encourages_work {government_spending : MonetaryValue}
(redi : @Redistribution Individual Individuals government_spending) :
Prop :=
  ∀ (cont : @Profile Individual MonetaryValue) (m : MonetaryValue)
  (i : Individual),
    cont i < m →
    redi.val cont i < redi.val (replace cont i m) i

lemma capitalism_encourages_work (inh : Fintype.card Individual ≠ 0)
(government_spending : MonetaryValue) :
@encourages_work Individual eqInd Individuals government_spending (
  pure_capitalism_costs_equally_divided_Redistribution inh government_spending
 ) := by
  unfold encourages_work pure_capitalism_costs_equally_divided_Redistribution
  unfold pure_capitalism_costs_equally_divided
  intro cont m i ltim
  simp
  rewrite [replace_changes]
  exact ltim

lemma communism_encourages_work (inh : Fintype.card Individual ≠ 0)
(government_spending : MonetaryValue) :
@encourages_work Individual eqInd Individuals government_spending (
  pure_communism_Redistribution inh government_spending
) := by
  unfold encourages_work pure_communism_Redistribution
  intro cont m j ltjm
  simp
  unfold pure_communism total_value
  have inh' : 0 < ↑(Fintype.card Individual) := by
    exact Nat.zero_lt_of_ne_zero inh
  have smp :
      (∑ i, replace cont j m i) / ↑(Fintype.card Individual) * ↑(Fintype.card Individual) =
      ∑ i, replace cont j m i := by
    refine div_mul_cancel₀ (∑ i, replace cont j m i) ?_
    refine Ne.symm (ne_of_lt ?_)
    exact Nat.cast_pos'.mpr inh'
  refine (div_lt_div_iff_of_pos_right ?_).mpr ?_
  · exact Nat.cast_pos'.mpr inh'
  · simp
    rw [<- sub_pos]
    rw [<- sum_reals_sub]
    refine (sum_pos_iff_of_nonneg ?_).mpr ?_
    · intro i iu
      rcases eq : decide (i = j) with true|false
      · rw [replace_unchanges]
        · simp
        · exact Ne.symm (not_eq_of_beq_eq_false eq)
      · have eqij : i = j := by
          exact of_decide_eq_true eq
        rw [eqij]
        rw [replace_changes]
        have lejm : cont j <= m := by
          exact Std.le_of_lt ltjm
        exact sub_nonneg_of_le lejm
    · exists j
      simp
      rw [replace_changes]
      exact ltjm

def work_incentive_between {c1 c2 : MonetaryValue} {government_spending : MonetaryValue}
(redi : @Redistribution Individual Individuals government_spending) (i : Individual)
(cont : @Profile Individual MonetaryValue) :
MonetaryValue :=
  redi.val (replace cont i c2) i - redi.val (replace cont i c1) i

def retribution_function {government_spending : MonetaryValue}
(redi : @Redistribution Individual Individuals government_spending)
(i : Individual) (cont : @Profile Individual MonetaryValue) :
MonetaryValue -> MonetaryValue :=
  fun c => redi.val (replace cont i c) i

@[reducible]
noncomputable def instantaneous_work_incentive {government_spending : MonetaryValue}
(i : Individual) (c0 : MonetaryValue)
(redi : @Redistribution Individual Individuals government_spending)
(cont : @Profile Individual MonetaryValue) :
MonetaryValue :=
  deriv (
    @retribution_function Individual eqInd Individuals government_spending redi i cont
  ) c0

lemma work_incentive_capitalism_between (government_spending : MonetaryValue)
(i : Individual) (c c' : MonetaryValue) (cont : @Profile Individual MonetaryValue) :
(
  @work_incentive_between Individual eqInd Individuals c c' government_spending
  (pure_capitalism_costs_equally_divided_Redistribution (
    inhabited_implies_nonnull_card i
  ) government_spending) i cont
) = c' - c := by
  unfold pure_capitalism_costs_equally_divided_Redistribution
  unfold work_incentive_between pure_capitalism_costs_equally_divided
  simp
  rw [replace_changes]
  rw [replace_changes]

lemma instantaneous_work_incentive_capitalism {government_spending : MonetaryValue}
(i : Individual) (c0 : MonetaryValue) (cont : @Profile Individual MonetaryValue) :
@instantaneous_work_incentive Individual eqInd Individuals government_spending i c0
(pure_capitalism_costs_equally_divided_Redistribution (
  inhabited_implies_nonnull_card i
) government_spending) cont = 1 := by
  unfold pure_capitalism_costs_equally_divided_Redistribution
  unfold instantaneous_work_incentive pure_capitalism_costs_equally_divided
  unfold retribution_function replace
  simp

lemma work_incentive_communism_between (government_spending : MonetaryValue)
(i : Individual) (c c' : MonetaryValue) (cont : @Profile Individual MonetaryValue) :
(
  @work_incentive_between Individual eqInd Individuals c c' government_spending
  (pure_communism_Redistribution (
    inhabited_implies_nonnull_card i
  ) government_spending) i cont
) = (c' - c) / Fintype.card Individual := by
  unfold pure_communism_Redistribution work_incentive_between
  simp
  unfold pure_communism total_value
  have inh : Fintype.card Individual ≠ 0 := by
    apply inhabited_implies_nonnull_card
    exact i
  have divdist :
      (∑ i_1, replace cont i c' i_1 - government_spending) / ↑(Fintype.card Individual) -
      (∑ i_1, replace cont i c i_1 - government_spending) / ↑(Fintype.card Individual) =
      (∑ i_1, replace cont i c' i_1 - ∑ i_1, replace cont i c i_1) /
      ↑(Fintype.card Individual) := by
    rw [sub_div]
    rw [sub_div]
    simp
    exact
      div_sub_div_same (∑ i_1, replace cont i c' i_1) (∑ i_1, replace cont i c i_1)
      ↑(Fintype.card Individual)
  rw [divdist]
  refine (div_left_inj' ?_).mpr ?_
  · exact Nat.cast_ne_zero.mpr inh
  · rw [<- sum_reals_sub]
    have smc :
        (fun j => replace cont i c' j - replace cont i c j) =
        (fun j => if j = i then c' - c else 0) := by
      apply funext
      intro j
      rcases eq : decide (j = i) with true|false
      · rw [replace_unchanges]
        · rw [replace_unchanges]
          · simp
            intro eqij
            rw [eqij] at eq
            simp at eq
          · exact Ne.symm (not_eq_of_beq_eq_false eq)
        · exact Ne.symm (not_eq_of_beq_eq_false eq)
      · have eqij : j = i := by
          exact of_decide_eq_true eq
        rw [eqij]
        rw [replace_changes]
        rw [replace_changes]
        simp
    have eqsum :
        ∑ i_1, (replace cont i c' i_1 - replace cont i c i_1) =
        ∑ i_1, if i_1 = i then c' - c else 0 := by
      exact
        Fintype.sum_congr (fun a ↦ replace cont i c' a - replace cont i c a)
          (fun a ↦ if a = i then c' - c else 0) (congrFun smc)
    rw [eqsum]
    exact Fintype.sum_ite_eq' i fun j ↦ c' - c

lemma instantaneous_work_incentive_communism {government_spending : MonetaryValue}
{i : Individual} {c0 : MonetaryValue} {cont : @Profile Individual MonetaryValue}
(_ : DifferentiableAt ℝ (
  @retribution_function Individual eqInd Individuals government_spending (
    pure_communism_Redistribution (
      inhabited_implies_nonnull_card i
    ) government_spending
  ) i cont
) c0) :
@instantaneous_work_incentive Individual eqInd Individuals government_spending i c0
(pure_communism_Redistribution (
  inhabited_implies_nonnull_card i
) government_spending) cont = 1  / Fintype.card Individual := by
  unfold pure_communism_Redistribution instantaneous_work_incentive pure_communism
  unfold retribution_function replace total_value
  simp
  have distr : (
    deriv (fun c ↦ (∑ x, if x = i then c else cont x) / ↑(Fintype.card Individual)) c0 =
    deriv (fun c ↦ (∑ x, if x = i then c else cont x)) c0 / ↑(Fintype.card Individual)
  ) := by
    simpa [div_eq_mul_inv] using (
      deriv_const_mul
      ((Fintype.card Individual : ℝ)⁻¹)
      (fun c ↦ ∑ x, if x = i then c else cont x)
      c0
    ).symm
  rw [<- distr]
  have derd : (
    deriv (fun c ↦ (∑ x, if x = i then c else cont x) / ↑(Fintype.card Individual)) c0 =
    deriv (fun c ↦ (∑ x, if x = i then c else cont x)) c0  / ↑(Fintype.card Individual)
  ) := by
    simpa using (
      deriv_const_div
      (fun c ↦ ∑ x, if x = i then c else cont x)
      (↑(Fintype.card Individual))
      c0
    )
  rw [derd]
  have sumf : (
    (fun c ↦ ∑ x, if x = i then c else cont x) =
    ∑ x, (fun c ↦ if x = i then c else cont x)
  ) := by
    exact Eq.symm (sum_fn univ fun c c_1 ↦ if c = i then c_1 else cont c)
  rw [sumf]
  rw [deriv_sum]
  rotate_left
  · intro j ju
    rcases eq : decide (j = i) with true|false
    · have casne : (fun c ↦ if j = i then c else cont j) = fun c => cont j := by
        apply funext
        intro mv
        refine ite_cond_eq_false mv (cont j) ?_
        exact eq_false_of_decide eq
      rw [casne]
      simp
    · have eqij : j = i := by
        exact of_decide_eq_true eq
      rw [eqij]
      simp
  · rw [div_eq_mul_inv]
    have inh : Fintype.card Individual ≠ 0 := by
      exact inhabited_implies_nonnull_card i
    refine (mul_inv_eq_iff_eq_mul₀ ?_).mpr ?_
    · exact Nat.cast_ne_zero.mpr inh
    · have mul1 : (
        (@Nat.cast MonetaryValue Real.instNatCast (Fintype.card Individual))⁻¹ *
        @Nat.cast MonetaryValue Real.instNatCast (Fintype.card Individual) = 1
      ) := by
        refine inv_mul_cancel₀ ?_
        exact Nat.cast_ne_zero.mpr inh
      rw [mul1]
      have all0 : (
        ∀ (j : Individual), j ≠ i →
        deriv (fun c ↦ if j = i then c else cont j) c0 = 0
      ) := by
        intro j neij
        have casne : (fun c ↦ if j = i then c else cont j) = fun c => cont j := by
          apply funext
          intro mv
          refine ite_cond_eq_false mv (cont j) ?_
          exact eq_false neij
        rw [casne]
        simp
      rw [Fintype.sum_eq_single i all0]
      simp

def currency_change {k : MonetaryValue} (_ : 0 < k)  (mv : MonetaryValue) :
MonetaryValue :=
  mv * k

noncomputable def currency_change_inverse {k : MonetaryValue} (_ : 0 < k)
(mv : MonetaryValue) :
MonetaryValue :=
  mv / k

lemma inverse_currency_change {k : MonetaryValue} (pos : 0 < k) :
Inverse (@currency_change k pos) (@currency_change_inverse k pos) := by
  unfold currency_change currency_change_inverse Inverse
  apply And.intro
  · intro x
    simp
    field_simp
  · intro x
    simp
    field_simp

def currency_change_distribution {k : MonetaryValue} (pos : 0 < k)
(dist : @Profile Individual MonetaryValue) :
@Profile Individual MonetaryValue :=
  fun i => currency_change pos (dist i)

noncomputable def currency_change_distribution_inverse {k : MonetaryValue}
(pos : 0 < k) (dist : @Profile Individual MonetaryValue) :
@Profile Individual MonetaryValue :=
  fun i => currency_change_inverse pos (dist i)

lemma inverse_currency_change_distribution {k : MonetaryValue} (pos : 0 < k) :
Inverse (@currency_change_distribution Individual k pos)
(currency_change_distribution_inverse pos) := by
  unfold currency_change_distribution currency_change_distribution_inverse Inverse
  apply And.intro
  · intro dist
    simp
    apply funext
    intro i
    rw [(inverse_currency_change pos).left]
  · intro dist
    simp
    apply funext
    intro i
    rw [(inverse_currency_change pos).right]

noncomputable def currency_change_redistribution {k : MonetaryValue} (pos : 0 < k)
(redi : @Profile Individual MonetaryValue -> @Profile Individual MonetaryValue) :
@Profile Individual MonetaryValue -> @Profile Individual MonetaryValue :=
  fun cont => currency_change_distribution pos (redi (
    currency_change_distribution_inverse pos cont
  ))

lemma currency_change_at_equilibrium {k : MonetaryValue}
{government_spending : MonetaryValue}
{redi : @Profile Individual MonetaryValue -> @Profile Individual MonetaryValue}
(pos : 0 < k)
(equi : @accounts_at_equilibirum Individual Individuals government_spending redi) :
@accounts_at_equilibirum Individual Individuals (government_spending * k) (
  currency_change_redistribution pos redi
) := by
  unfold accounts_at_equilibirum currency_change_redistribution
  intro dist
  unfold total_value currency_change_distribution
  unfold currency_change currency_change_distribution_inverse
  have distr : (
    ∑ i, (redi (fun i ↦ currency_change_inverse pos (dist i)) i * k) =
    (∑ i, redi (fun i ↦ currency_change_inverse pos (dist i)) i) * k
  ) := by
    exact Eq.symm (sum_mul univ (redi fun i ↦ currency_change_inverse pos (dist i)) k)
  rw [distr]
  unfold currency_change_inverse
  unfold accounts_at_equilibirum at equi
  specialize (equi (currency_change_distribution_inverse pos dist))
  unfold total_value currency_change_distribution_inverse at equi
  unfold currency_change_inverse at equi
  have mulk :(
    (∑ i, redi (fun i ↦ dist i / k) i + government_spending) * k =
    (∑ i, dist i / k) * k
  ) := by
    exact (mul_right_cancel_iff_of_pos pos).mpr equi
  rw [add_mul] at mulk
  rw [mulk]
  rw [mul_comm]
  rw [Finset.mul_sum]
  refine Eq.symm (Fintype.sum_congr dist (fun a ↦ k * (dist a / k)) ?_)
  intro i
  simp
  rw [mul_comm]
  rw [division_def]
  rw [mul_assoc]
  have invk : k⁻¹ * k = 1 := by
    refine inv_mul_cancel₀ ?_
    exact Ne.symm (Std.ne_of_lt pos)
  rw [invk]
  simp

noncomputable def change_currency_Redistribution {k : MonetaryValue}
{government_spending : MonetaryValue}
(redi : @Redistribution Individual Individuals government_spending)
(pos : 0 < k) :
@Redistribution Individual Individuals (government_spending * k) :=
  ⟨ currency_change_redistribution pos redi,
    currency_change_at_equilibrium pos redi.property ⟩

def is_fair {government_spending : MonetaryValue}
(redi : @Redistribution Individual Individuals government_spending) :
Prop :=
  ∀ (cont : @Profile Individual MonetaryValue) (i j : Individual),
    cont i <= cont j ->
    redi.val cont i <= redi.val cont j

def is_strictly_fair {government_spending : MonetaryValue}
(redi : @Redistribution Individual Individuals government_spending) :
Prop :=
  ∀ (cont : @Profile Individual MonetaryValue) (i j : Individual),
    cont i < cont j ->
    redi.val cont i < redi.val cont j

lemma capitalism_is_fair (inh : Fintype.card Individual ≠ 0)
(government_spending : MonetaryValue) :
@is_fair Individual Individuals government_spending (
  pure_capitalism_costs_equally_divided_Redistribution inh government_spending
) := by
  unfold is_fair pure_capitalism_costs_equally_divided_Redistribution
  intro cont i j
  simp
  unfold pure_capitalism_costs_equally_divided
  intro conc
  exact tsub_le_tsub_right conc (government_spending / ↑(Fintype.card Individual))

lemma capitalism_is_strictly_fair (inh : Fintype.card Individual ≠ 0)
(government_spending : MonetaryValue) :
@is_strictly_fair Individual Individuals government_spending (
  pure_capitalism_costs_equally_divided_Redistribution inh government_spending
) := by
  unfold is_strictly_fair pure_capitalism_costs_equally_divided_Redistribution
  intro cont i j
  simp
  unfold pure_capitalism_costs_equally_divided
  intro conc
  exact sub_lt_sub_right conc (government_spending / ↑(Fintype.card Individual))

lemma communism_is_fair (inh : Fintype.card Individual ≠ 0)
(government_spending : MonetaryValue) :
is_fair (pure_communism_Redistribution inh government_spending) := by
  unfold is_fair pure_communism_Redistribution
  intro cont i j
  simp
  unfold pure_communism
  intro leij
  simp

lemma communism_not_strictly_fair {i j : Individual} [DecidableEq Individual]
(government_spending : MonetaryValue) (neij : j ≠ i) :
¬ @is_strictly_fair Individual Individuals government_spending (
  pure_communism_Redistribution (inhabited_implies_nonnull_card i) government_spending
) := by
  unfold is_strictly_fair pure_communism_Redistribution
  intro sf
  specialize (sf (fun i_1 : Individual => if i_1 = i then (1 : ℝ) else (0 : ℝ)) j i)
  have eqii : (if i = i then (1 : ℝ) else 0) = 1 := by
    exact if_pos rfl
  rw [eqii] at sf
  have ji10 : (if j = i then (1 : ℝ) else 0) = 0 := by
    exact if_neg neij
  rw [ji10] at sf
  simp at sf
  unfold pure_communism at sf
  simp at sf

end definition_capitalism_communism
