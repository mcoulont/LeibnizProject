
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

import Tools.eqtype_facts
import Tools.permutations
import Tools.fintype_facts
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

def preserves_total
(redi : @Profile Individual MonetaryValue -> @Profile Individual MonetaryValue) :
Prop :=
  ∀ (dist : @Profile Individual MonetaryValue),
    @total_value Individual Individuals (redi dist) =
    @total_value Individual Individuals dist

@[reducible]
def Redistribution : Type :=
  {
    redi : @Profile Individual MonetaryValue -> @Profile Individual MonetaryValue //
    @preserves_total Individual Individuals redi
  }

def pure_capitalism :
@Profile Individual MonetaryValue -> @Profile Individual MonetaryValue :=
  id

lemma pure_capitalism_preserves_total :
@preserves_total Individual Individuals (@pure_capitalism Individual) := by
  unfold pure_capitalism
  unfold preserves_total
  intro dist
  tauto

def pure_capitalism_Redistribution : @Redistribution Individual Individuals :=
  ⟨ pure_capitalism, pure_capitalism_preserves_total ⟩

noncomputable def pure_communism :
@Profile Individual MonetaryValue -> @Profile Individual MonetaryValue :=
  fun (dist : @Profile Individual MonetaryValue) => fun _ =>
    @total_value Individual Individuals dist / (Fintype.card Individual : MonetaryValue)

lemma pure_communism_preserves_total (inh : Fintype.card Individual ≠ 0) :
@preserves_total Individual Individuals (@pure_communism Individual Individuals) := by
  unfold pure_communism preserves_total total_value
  intro dist
  simp
  refine mul_div_cancel_of_imp' ?_
  intro emp
  exfalso
  apply inh
  exact Nat.cast_eq_zero.mp emp

noncomputable def pure_communism_Redistribution (inh : Fintype.card Individual ≠ 0) :
@Redistribution Individual Individuals :=
  ⟨ pure_communism, pure_communism_preserves_total inh ⟩

def is_egalitarian (redi : @Redistribution Individual Individuals) : Prop :=
  ∀ (σ : Perm Individual) (cont : @Profile Individual MonetaryValue),
    PermutationsActingOnFunctions (redi.val cont) σ =
    redi.val (PermutationsActingOnFunctions cont σ)

lemma capitalism_is_egalitarian :
@is_egalitarian Individual Individuals pure_capitalism_Redistribution := by
  tauto

lemma communism_is_egalitarian (inh : Fintype.card Individual ≠ 0) :
@is_egalitarian Individual Individuals (pure_communism_Redistribution inh) := by
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

def encourages_work (redi : @Redistribution Individual Individuals) : Prop :=
  ∀ (cont : @Profile Individual MonetaryValue) (m : MonetaryValue)
  (i : Individual),
    cont i < m →
    redi.val cont i < redi.val (replace cont i m) i

lemma capitalism_encourages_work :
@encourages_work Individual eqInd Individuals pure_capitalism_Redistribution := by
  unfold encourages_work pure_capitalism_Redistribution pure_capitalism
  intro cont m i ltim
  simp
  rewrite [replace_changes]
  exact ltim

lemma communism_encourages_work (inh : Fintype.card Individual ≠ 0) :
@encourages_work Individual eqInd Individuals (pure_communism_Redistribution inh) := by
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
  · rw [<- sub_pos]
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

def work_incentive_between {c1 c2 : MonetaryValue}
(redi : @Redistribution Individual Individuals) (i : Individual)
(cont : @Profile Individual MonetaryValue) :
MonetaryValue :=
  redi.val (replace cont i c2) i - redi.val (replace cont i c1) i

def retribution_function (redi : @Redistribution Individual Individuals)
(i : Individual) (cont : @Profile Individual MonetaryValue) :
MonetaryValue -> MonetaryValue :=
  fun c => redi.val (replace cont i c) i

@[reducible]
noncomputable def instantaneous_work_incentive {c0 : MonetaryValue}
{redi : @Redistribution Individual Individuals} {i : Individual}
{cont : @Profile Individual MonetaryValue}
(_ : DifferentiableAt ℝ (
  @retribution_function Individual eqInd Individuals redi i cont
) c0) :
MonetaryValue :=
  deriv (@retribution_function Individual eqInd Individuals redi i cont) c0

lemma work_incentive_capitalism_between {c c' : MonetaryValue} (i : Individual)
(cont : @Profile Individual MonetaryValue) :
(
  @work_incentive_between Individual eqInd Individuals c c'
  pure_capitalism_Redistribution i cont
) = c' - c := by
  unfold pure_capitalism_Redistribution work_incentive_between pure_capitalism
  simp
  rw [replace_changes]
  rw [replace_changes]

lemma instantaneous_work_incentive_capitalism {c0 : MonetaryValue} (i : Individual)
{cont : @Profile Individual MonetaryValue}
(diff : DifferentiableAt ℝ (
  @retribution_function Individual eqInd Individuals pure_capitalism_Redistribution
  i cont
) c0) :
@instantaneous_work_incentive Individual eqInd Individuals c0
pure_capitalism_Redistribution i cont diff = 1 := by
  unfold pure_capitalism_Redistribution instantaneous_work_incentive pure_capitalism
  unfold retribution_function replace
  simp

lemma work_incentive_communism_between {c c' : MonetaryValue} (i : Individual)
(cont : @Profile Individual MonetaryValue) :
@work_incentive_between Individual eqInd Individuals c c' (
  pure_communism_Redistribution (inhabited_implies_nonnull_card i)
) i cont =
(c' - c) / Fintype.card Individual := by
  unfold pure_communism_Redistribution work_incentive_between
  simp
  unfold pure_communism total_value
  have inh : Fintype.card Individual ≠ 0 := by
    apply inhabited_implies_nonnull_card
    exact i
  have divdist :
      (∑ i_1, replace cont i c' i_1) / ↑(Fintype.card Individual) -
      (∑ i_1, replace cont i c i_1) / ↑(Fintype.card Individual) =
      (∑ i_1, replace cont i c' i_1 - ∑ i_1, replace cont i c i_1) /
      ↑(Fintype.card Individual) := by
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

lemma instantaneous_work_incentive_communism {c0 : MonetaryValue} (i : Individual)
{cont : @Profile Individual MonetaryValue}
(diff : DifferentiableAt ℝ (fun c =>
  (pure_communism_Redistribution (inhabited_implies_nonnull_card i)).val (replace cont i c) i
) c0) :
@instantaneous_work_incentive Individual eqInd Individuals c0 (
  pure_communism_Redistribution (inhabited_implies_nonnull_card i)
) i cont diff = 1 / Fintype.card Individual := by
  unfold pure_communism_Redistribution instantaneous_work_incentive pure_communism
  unfold retribution_function replace total_value
  simp
  have dist : (
    deriv (fun c ↦ (∑ x, if x = i then c else cont x) / ↑(Fintype.card Individual)) c0 =
    deriv (fun c ↦ (∑ x, if x = i then c else cont x)) c0 / ↑(Fintype.card Individual)
  ) := by
    simpa [div_eq_mul_inv] using (
      deriv_const_mul
      ((Fintype.card Individual : ℝ)⁻¹)
      (fun c ↦ ∑ x, if x = i then c else cont x)
      c0
    ).symm
  rw [<- dist]
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

def currency_change (dist : @Profile Individual MonetaryValue)
(k : MonetaryValue) :
@Profile Individual MonetaryValue :=
  fun i => k * dist i

def stable_by_currency_change (redi : @Redistribution Individual Individuals) :
Prop :=
  ∀ (cont : @Profile Individual MonetaryValue) (k : MonetaryValue),
    redi.val (currency_change cont k) = currency_change (redi.val cont) k

lemma capitalism_stable_by_currency_change :
@stable_by_currency_change Individual Individuals pure_capitalism_Redistribution := by
  unfold stable_by_currency_change pure_capitalism_Redistribution
  intro cont k
  simp
  unfold pure_capitalism
  tauto

lemma communism_stable_by_currency_change (inh : Fintype.card Individual ≠ 0) :
stable_by_currency_change (pure_communism_Redistribution inh) := by
  unfold stable_by_currency_change pure_communism_Redistribution
  intro cont k
  simp
  unfold pure_communism currency_change total_value
  simp
  apply funext
  intro i
  have muldi : ∑ x, k * cont x = k * ∑ i, cont i := by
      exact sum_reals_mult_constant cont k
  rw [muldi]
  exact Eq.symm (mul_div_assoc' k (∑ i, cont i) ↑(Fintype.card Individual))

def is_fair (redi : @Redistribution Individual Individuals) : Prop :=
  ∀ (cont : @Profile Individual MonetaryValue) (i j : Individual),
    cont i <= cont j ->
    redi.val cont i <= redi.val cont j

def is_strictly_fair (redi : @Redistribution Individual Individuals) : Prop :=
  ∀ (cont : @Profile Individual MonetaryValue) (i j : Individual),
    cont i < cont j ->
    redi.val cont i < redi.val cont j

lemma capitalism_is_fair :
@is_fair Individual Individuals pure_capitalism_Redistribution := by
  unfold is_fair pure_capitalism_Redistribution
  intro cont i j
  simp
  unfold pure_capitalism
  intro conc
  exact conc

lemma capitalism_is_strictly_fair :
@is_strictly_fair Individual Individuals pure_capitalism_Redistribution := by
  unfold is_strictly_fair pure_capitalism_Redistribution
  intro cont i j
  simp
  unfold pure_capitalism
  intro conc
  exact conc

lemma communism_is_fair (inh : Fintype.card Individual ≠ 0) :
is_fair (pure_communism_Redistribution inh) := by
  unfold is_fair pure_communism_Redistribution
  intro cont i j
  simp
  unfold pure_communism
  intro leij
  simp

-- I don't get why it doesn't compile without [DecidableEq Individual]
-- (eqInd is there)
lemma communism_not_strictly_fair {i j : Individual} [DecidableEq Individual]
(neij : j ≠ i) :
¬ @is_strictly_fair Individual Individuals (
  pure_communism_Redistribution (inhabited_implies_nonnull_card i)
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
