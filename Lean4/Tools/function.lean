
@[reducible]
def Inverse{α : Type} {β : Type} (g : β → α) (f : α → β) :
Prop :=
  (∀ a : α, g (f a) = a) ∧ (∀ b : β, f (g b) = b)
