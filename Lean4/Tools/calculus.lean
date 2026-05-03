
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

import Tools.real

open Real Set

theorem differentiableAt_Ici_to_uIcc {f : ℝ → ℝ}
(hf : ∀ x ∈ Set.Ici (0 : ℝ), DifferentiableAt ℝ f x) (M : ℝ) (hM : 0 ≤ M) :
∀ x ∈ Set.uIcc 0 M, DifferentiableAt ℝ f x := by
  intro x hx
  exact hf x (uIcc_nonneg_subset_Ici hM hx)

theorem differentiableAt_Ici_to_uIcc_all {f : ℝ → ℝ}
(hf : ∀ x ∈ Set.Ici (0 : ℝ), DifferentiableAt ℝ f x) :
∀ M : ℝ, 0 ≤ M → ∀ x ∈ Set.uIcc 0 M, DifferentiableAt ℝ f x :=
  fun M hM => differentiableAt_Ici_to_uIcc hf M hM

theorem differentiable_to_uIcc {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
∀ M : ℝ, ∀ x ∈ Set.uIcc 0 M, DifferentiableAt ℝ f x :=
  fun _ x _ => hf x

lemma differentiableAt_on_uIcc_of_Ici {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
(hf : ∀ x ∈ Set.Ici (0 : ℝ), DifferentiableAt ℝ f x) :
∀ x ∈ Set.uIcc 0 M, DifferentiableAt ℝ f x :=
  fun x hx => hf x (uIcc_nonneg_subset_Ici hM hx)
