
Require Import relation_facts.
Require Import physical_theories.

Section deterministic_physics_free_will.

Context {Time : Type}.
Context {Before : TotalOrder Time}.
Context {State : Type}.
Context {Action : Type}.

Definition ignore_actions (h : @History Time (State * Action)) :
@History Time State :=
  fun t => fst (h t).

Definition get_action (h : @History Time (State * Action)) (t : Time) :
Action :=
  snd (h t).

Definition is_deterministic_except_for_free_will
(pt : @PhysicalTheory Time State) (a_def : Action) :
Prop :=
  forall (h1 h2 : @History Time (State * Action)),
    satisfies (ignore_actions h1) pt ->
    satisfies (ignore_actions h2) pt ->
    forall (t0 : Time), (
      h1 t0 = h2 t0 ->
      forall (t2 : Time), strict Before t0 t2 -> (
        forall (t1 : Time),
          strict Before t0 t1 ->
          non_strict Before t1 t2 ->
          get_action h1 t1 = get_action h2 t1
      ) -> h1 t2 = h2 t2
    ).

End deterministic_physics_free_will.
