
Require Import relation_facts.
Require Import total_order.

Section agents_dynamic_environment.

Context {Instant : Type}.
Context {Before : TotalOrder Instant}.
Context {State : Type}.
Context {Action : Type}.
Context {Agent : Type}.

Definition ActionPerAgent : Type := Agent -> Action.

Definition History : Type := Instant -> State * ActionPerAgent.

Definition HistoryUntil (t0 : Instant) : Type :=
  { t : Instant | non_strict Before t t0 } -> State * ActionPerAgent.

Definition extends {t0 : Instant} (h : History) (hu : HistoryUntil t0) : Prop :=
  forall (t : { t : Instant | non_strict Before t t0 }),
    non_strict Before (proj1_sig t) t0 -> h (proj1_sig t) = hu t. 

End agents_dynamic_environment.
