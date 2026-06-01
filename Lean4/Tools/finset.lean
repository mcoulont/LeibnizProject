
import Mathlib.Data.Finset.Basic

theorem union_of_singletons_finset {α : Type*} [DecidableEq α] (i j : α) :
    ({i} : Finset α) ∪ {j} = {i, j} := by
  ext x
  simp
