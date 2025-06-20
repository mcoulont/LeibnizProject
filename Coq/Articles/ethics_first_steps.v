
Require Import Bool.Bool.

Section ethics_first_steps.

Definition Ethic (State : Type) (Action : Type) : Type :=
    State -> Action -> bool.

End ethics_first_steps.
