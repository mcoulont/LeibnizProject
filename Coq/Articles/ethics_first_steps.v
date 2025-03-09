
Require Import Bool.Bool.

Context {State : Type}.

Context {Action : Type}.

Definition Ethic : Type := State -> Action -> bool.
