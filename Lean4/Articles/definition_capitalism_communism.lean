
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
def MonetaryValue : Type := Rat

def total_value (dist : @Profile Individual MonetaryValue) : MonetaryValue :=
  ∑ i : Individual, dist i

def preserves_total
(redi : @Profile Individual MonetaryValue -> @Profile Individual MonetaryValue) :
Prop :=
  ∀ (dist : @Profile Individual MonetaryValue),
    @total_value Individual Individuals (redi dist) =
    @total_value Individual Individuals dist

def Redistribution : Type :=
  {
    redi : @Profile Individual MonetaryValue -> @Profile Individual MonetaryValue //
    -- preserves_total redi
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
  exact Rat.natCast_eq_zero_iff.mp emp

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
      rw [<- sum_rationals_perm]
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
    refine Rat.div_mul_cancel ?_
    refine Ne.symm (Rat.ne_of_lt ?_)
    exact Rat.natCast_pos.mpr inh'
  refine (Rat.div_lt_iff ?_).mpr ?_
  · exact Rat.natCast_pos.mpr inh'
  · rw [smp]
    refine (Rat.lt_iff_sub_pos (∑ i, cont i) (∑ i, replace cont j m i)).mpr ?_
    rw [<- sum_rationals_sub]
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
          exact Rat.le_of_lt ltjm
        exact (Rat.le_iff_sub_nonneg (cont j) m).mp lejm
    · exists j
      simp
      rw [replace_changes]
      exact ltjm

def work_incentive {c c' : MonetaryValue}
(redi : @Redistribution Individual Individuals) (i : Individual)
(cont : @Profile Individual MonetaryValue) :
MonetaryValue :=
  redi.val (replace cont i c') i - redi.val (replace cont i c) i

lemma work_incentive_capitalism {c c' : MonetaryValue} (i : Individual)
(cont : @Profile Individual MonetaryValue) :
@work_incentive Individual eqInd Individuals c c' pure_capitalism_Redistribution
i cont = c' - c := by
  unfold pure_capitalism_Redistribution work_incentive pure_capitalism
  simp
  rw [replace_changes]
  rw [replace_changes]

lemma work_incentive_communism {c c' : MonetaryValue} (i : Individual)
(cont : @Profile Individual MonetaryValue) :
@work_incentive Individual eqInd Individuals c c' (
  pure_communism_Redistribution (inhabited_implies_nonnull_card i)
) i cont =
(c' - c) / Fintype.card Individual := by
  unfold pure_communism_Redistribution work_incentive
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
  · rw [<- sum_rationals_sub]
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

def currency_change (dist : @Profile Individual MonetaryValue)
(k : MonetaryValue) :
@Profile Individual MonetaryValue :=
  fun i => k * dist i

def is_linear (redi : @Redistribution Individual Individuals) : Prop :=
  forall (cont : @Profile Individual MonetaryValue) (k : MonetaryValue),
    redi.val (currency_change cont k) = currency_change (redi.val cont) k

lemma capitalism_is_linear :
@is_linear Individual Individuals pure_capitalism_Redistribution := by
  unfold is_linear pure_capitalism_Redistribution
  intro cont k
  simp
  unfold pure_capitalism
  tauto

lemma communism_is_linear (inh : Fintype.card Individual ≠ 0) :
is_linear (pure_communism_Redistribution inh) := by
  unfold is_linear pure_communism_Redistribution
  intro cont k
  simp
  unfold pure_communism currency_change total_value
  simp
  apply funext
  intro i
  have muldi : ∑ x, k * cont x = k * ∑ i, cont i := by
      exact sum_rationals_mult_constant cont k
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
  exact Rat.le_refl

-- I don't get why it doesn't compile with the line immediately below:
-- lemma communism_not_strictly_fair {i j : Individual} (neij : j ≠ i) :
lemma communism_not_strictly_fair {i j : Individual} [DecidableEq Individual] (neij : j ≠ i) :
¬ @is_strictly_fair Individual Individuals (
  pure_communism_Redistribution (inhabited_implies_nonnull_card i)
) := by
  unfold is_strictly_fair pure_communism_Redistribution
  intro sf
  specialize (sf (fun i_1 : Individual => if i_1 = i then (1 : Rat) else (0 : Rat)) j i)
  have eqii : (if i = i then (1 : Rat) else 0) = 1 := by
    exact if_pos rfl
  rw [eqii] at sf
  have ji10 : (if j = i then (1 : Rat) else 0) = 0 := by
    exact if_neg neij
  rw [ji10] at sf
  simp at sf
  unfold pure_communism at sf
  simp at sf

end definition_capitalism_communism
