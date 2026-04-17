
import Mathlib.Algebra.Module.BigOperators

import Tools.permutations

open Equiv

lemma inhabited_implies_nonnull_card {A : Type} {As : Fintype A} (a : A) :
Fintype.card A ≠ 0 := by
  refine Nat.ne_zero_iff_zero_lt.mpr ?_
  refine Fintype.card_pos_iff.mpr ?_
  exact Nonempty.intro a

lemma sum_rationals_perm {A : Type} {As : Fintype A} (f : A -> Rat) (σ : Perm A) :
∑ a : A, @PermutationsActingOnFunctions Rat A As f σ a = ∑ a : A, f a := by
  exact sum_comp σ f

lemma sum_rationals_sub {A : Type} {As : Fintype A} (f g : A → Rat) :
∑ i, (f i - g i) = (∑ i, f i) - (∑ i, g i) := by
  classical
  simpa using sum_sub_distrib

lemma sum_rationals_mult_constant {A : Type} {As : Fintype A} (f : A → Rat) (k : Rat) :
∑ i, k * f i = k * (∑ i, f i) := by
  exact Eq.symm (Finset.mul_sum Finset.univ f k)
