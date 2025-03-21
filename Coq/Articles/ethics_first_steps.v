
Require Import Bool.Bool.
From mathcomp Require Import all_ssreflect.

Context {State : Type}.

Context {Action : eqType}.

Definition Ethic : Type := State -> Action -> bool.
