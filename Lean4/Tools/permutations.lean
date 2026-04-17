
import Mathlib.GroupTheory.Perm.Finite

open Equiv

def PermutationsActingOnFunctions {A B : Type} [Fintype B]
(f : B -> A) (σ : Perm B) :
B -> A :=
  fun (t : B) => f (σ t)
