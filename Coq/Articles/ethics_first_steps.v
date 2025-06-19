
Require Import Bool.Bool.
From mathcomp Require Import all_ssreflect.

Section ethics_first_steps.

Definition Ethic (State : Type) (Action : eqType) : Type :=
    State -> Action -> bool.

End ethics_first_steps.
