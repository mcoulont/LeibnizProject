
namespace ethics_first_steps

variable {State : Type}
variable {Action : Type}

def Ethic : Type := State -> Action -> Bool

def more_restrictive (e1 e2 : @Ethic State Action) (state : State) : Prop :=
  ∀ (action : Action), e1 state action = true -> e2 state action = true

def strictly_more_restrictive (e1 e2 : @Ethic State Action) (state : State) : Prop :=
  more_restrictive e1 e2 state ∧
  ∃ (action : Action), e1 state action = false ∧ e2 state action = true

theorem every_ethic_more_restrictive_than_itself (e : @Ethic State Action) (state : State) :
more_restrictive e e state := by
  unfold more_restrictive
  intros a h
  exact h

theorem no_ethic_strictly_more_restrictive_than_itself (state : State) :
∀ (e : @Ethic State Action), ¬ strictly_more_restrictive e e state := by
  unfold strictly_more_restrictive
  intro e
  intro cont
  rcases cont with ⟨rstr, eth⟩
  rcases eth with ⟨action, ethf, etht⟩
  rw [ethf] at etht
  contradiction

def ethicless : @Ethic State Action :=
  fun _ => (fun _ => true)

theorem ethicless_least_restrictive (e : @Ethic State Action) (state : State) :
more_restrictive e ethicless state := by
  unfold more_restrictive
  unfold ethicless
  intros a h
  trivial

end ethics_first_steps
