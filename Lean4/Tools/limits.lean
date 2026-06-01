
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology

lemma lim_neg_top (f : ℝ -> ℝ) (l : ℝ) :
Tendsto f atTop (𝓝 l) ↔ Tendsto (fun x => - f x) atTop (𝓝 (-l)) := by
  constructor
  · intro h
    have h_neg : Continuous (fun x : ℝ => -x) := continuous_neg
    exact h_neg.continuousAt.tendsto.comp h
  · intro h
    have h_double_neg : (fun x => -(-f x)) = f := by
      funext x
      ring
    have h_neg : Continuous (fun x : ℝ => -x) := continuous_neg
    have h_comp : Tendsto (fun x => -(-f x)) atTop (𝓝 (-(-l))) := h_neg.continuousAt.tendsto.comp h
    simpa [h_double_neg] using h_comp

lemma lim_neg_bot (f : ℝ -> ℝ) (l : ℝ) :
Tendsto f atBot (𝓝 l) ↔ Tendsto (fun x => - f x) atBot (𝓝 (-l)) := by
  constructor
  · intro h
    have h_neg : Continuous (fun x : ℝ => -x) := continuous_neg
    exact h_neg.continuousAt.tendsto.comp h
  · intro h
    have h_double_neg : (fun x => -(-f x)) = f := by
      funext x
      ring
    have h_neg : Continuous (fun x : ℝ => -x) := continuous_neg
    have h_comp : Tendsto (fun x => -(-f x)) atBot (𝓝 (-(-l))) := h_neg.continuousAt.tendsto.comp h
    simpa [h_double_neg] using h_comp

lemma lim_inverse_top (c : ℝ) : Tendsto (fun x : ℝ => c / x) atTop (𝓝 0) := by
  rw [show (fun x : ℝ => c / x) = (fun x : ℝ => c * x⁻¹) by
    funext x
    rw [div_eq_mul_inv]]
  have h : Tendsto (fun x : ℝ => c * x⁻¹) atTop (𝓝 (c * 0)) :=
    tendsto_const_nhds.mul tendsto_inv_atTop_zero
  convert h using 1
  ring_nf

lemma lim_inverse_bot (c : ℝ) : Tendsto (fun x : ℝ => c / x) atBot (𝓝 0) := by
  rw [show (fun x : ℝ => c / x) = (fun x : ℝ => c * x⁻¹) by
    funext x
    rw [div_eq_mul_inv]]
  have h : Tendsto (fun x : ℝ => c * x⁻¹) atBot (𝓝 (c * 0)) :=
    tendsto_const_nhds.mul tendsto_inv_atBot_zero
  convert h using 1
  ring_nf

lemma lim_frac_deg_1_0_top (c : ℝ) : Tendsto (fun x : ℝ => (x + c) / x) atTop (𝓝 1) := by
  have dist : (fun x ↦ (x + c) / x) = (fun x ↦ x / x + c / x) := by
    funext; (expose_names; exact add_div x c x)
  rw [dist]
  have lim1 : Tendsto (fun x : ℝ ↦ x / x) atTop (𝓝 1) := by
    have eqtd2 : (
      Tendsto (fun x : ℝ ↦ ((x / x) : ℝ)) atTop (𝓝 1) ↔
      Tendsto (fun x : ℝ ↦ (1 : ℝ)) atTop (𝓝 1)
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
  have lim0 : Tendsto (fun x : ℝ ↦ c / x) atTop (𝓝 0) := by
    exact lim_inverse_top c
  have concl := Filter.Tendsto.add lim1 lim0
  simp at concl; exact concl

lemma lim_frac_deg_1_0_bot (c : ℝ) : Tendsto (fun x : ℝ => (c - x) / -x) atBot (𝓝 1) := by
  have dist : (fun x ↦ (c - x) / -x) = (fun x ↦ c / -x - x / -x) := by
    funext; (expose_names; exact sub_div c x (-x))
  rw [dist]
  have lim1 : Tendsto (fun x : ℝ ↦ - x / -x) atBot (𝓝 1) := by
    have eqtd2 : (
      Tendsto (fun x : ℝ ↦ ((- x / -x) : ℝ)) atBot (𝓝 1) ↔
      Tendsto (fun x : ℝ ↦ (1 : ℝ)) atBot (𝓝 1)
    ) := by
      apply tendsto_congr'
      unfold EventuallyEq
      unfold Filter.Eventually
      simp
      exists -1
      intro x le1x eq0x
      rw [eq0x] at le1x
      linarith
    rw [eqtd2]
    exact tendsto_const_nhds
  have dnend : (fun x : ℝ ↦ c / -x) = (fun x : ℝ ↦ (-c) / x) := by
    funext; rw [div_neg_eq_neg_div']
  have lim0 : Tendsto (fun x : ℝ ↦ c / -x) atBot (𝓝 0) := by
    rw [dnend]; exact lim_inverse_bot (-c)
  have concl := Filter.Tendsto.add lim0 lim1
  convert concl using 1
  · funext x
    field_simp
    ring_nf
  · norm_num
