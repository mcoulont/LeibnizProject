
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Real.Basic

open Real Set

theorem div_le_div_of_pos (a b c : ℝ) (h : c > 0) (hab : a ≤ b) : a / c ≤ b / c := by
  rw [div_eq_mul_inv]
  refine (mul_inv_le_iff₀ h).mpr ?_
  have dimu : b / c * c = b := by
    refine div_mul_cancel_of_imp ?_
    intro nec0
    rewrite [nec0] at h
    simp at h
  rw [dimu]
  exact hab

lemma uIcc_nonneg_subset_Ici {M : ℝ} (hM : 0 ≤ M) :
Set.uIcc 0 M ⊆ Set.Ici 0 := by
  intro x hx
  simp [Set.uIcc_of_le hM] at hx
  exact hx.1
