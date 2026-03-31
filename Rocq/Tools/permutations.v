
From mathcomp Require Import fintype fingroup perm.

Definition PermutationsActingOnFunctions {A : Type} {T : finType}
(f : T -> A) (σ : {perm T}) :
T -> A :=
  fun (t : T) => f (σ t).
