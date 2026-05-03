
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

import Tools.real

open Real Set

theorem continuousOn_Ici_to_uIcc_v1 {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ici 0))
{M : ℝ} (hM : 0 ≤ M) :
ContinuousOn f (Set.uIcc 0 M) :=
  ContinuousOn.mono hf (by
    intro x hx
    simp [Set.uIcc_of_le hM] at hx
    exact hx.1
  )
