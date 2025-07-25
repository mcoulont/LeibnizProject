
namespace ethics_first_steps

variable {State : Type}
variable {Action : Type}

def Ethic : Type := State -> Action -> Bool

def more_restrictive (e1 e2 : @Ethic State Action) (state : State) : Prop :=
  ∀ (action : Action), e1 state action = true -> e2 state action = true

def strictly_more_restrictive (e1 e2 : @Ethic State Action) (state : State) : Prop :=
  more_restrictive e1 e2 state ∧
  ∃ (action : Action), e1 state action = false ∧ e2 state action = true

-- strange error appearing only when the lemma is there:
-- "function expected at true term has type Bool"
-- lemma every_ethic_more_restrictive_than_itself (e : @Ethic State Action) (state : State) :
-- more_restrictive e e state := by
--   unfold more_restrictive
  -- intro h

def ethicless : @Ethic State Action :=
  fun state => (fun action => true)

-- strange error "unknown identifier 'lemma'":
-- lemma ethicless_least_restrictive (e : @Ethic State Action) (state : State) :
-- more_restrictive e ethicless state := by
--   unfold more_restrictive
--   unfold ethicless
--   intro h
--   simpl

end ethics_first_steps
