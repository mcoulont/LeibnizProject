
def replace {A: Type} {B : A -> Type} [DecidableEq A]
(before_replace : ∀ a : A, B a) (a0 : A) (b0 : B a0) :
∀ a : A, B a :=
  fun a => (if e : a = a0 then e ▸ b0 else before_replace a)

theorem replace_changes {A: Type} {B : A -> Type} [DecidableEq A]
(before_replace : ∀ a : A, B a) (a0 : A) (b0 : B a0) :
replace before_replace a0 b0 a0 = b0 := by
  unfold replace
  simp

theorem replace_unchanges {A: Type} {B : A -> Type} [DecidableEq A] {a a' : A}
(before_replace : ∀ a : A, B a) (b : B a) (ne_aa' : a ≠ a') :
replace before_replace a b a' = before_replace a' := by
  unfold replace
  exact dif_neg (id (Ne.symm ne_aa'))
