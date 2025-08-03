
From mathcomp Require Import reals measure probability.

Require Import relation_facts.

Section deterministic_stochastic_physics.

Context {Time : Type}.
Context {Before : TotalOrder Time}.
Context {State : Type}.
Context {R : realType}.
Context d {State_measurable : measurableType d }.
(* Context {P : probability State_measurable R}. *)

Definition History : Type := Time -> State.

Definition HistoryUntil (t0 : Time) : Type :=
  { t : Time | non_strict Before t t0 } -> State.

Definition HistoryBefore (t0 : Time) : Type :=
  { t : Time | strict Before t t0 } -> State.

Definition extends {t0 : Time} (h : History) (hu : HistoryUntil t0) : Prop :=
  forall (t : { t : Time | non_strict Before t t0 }),
    non_strict Before (proj1_sig t) t0 -> h (proj1_sig t) = hu t.

Definition Event : Type := History -> bool.

Definition happens_in (e : Event) (h : History) : Prop :=
  e(h) = true.

Definition PhysicalTheory : Type := History -> Prop.

Definition satisfies (h : History) (pt : PhysicalTheory) : Prop := pt h.

Definition is_possible (event : Event) (pt : PhysicalTheory) : Prop :=
  exists (h : History), satisfies h pt /\ event h = true.

Definition is_deterministic (pt : PhysicalTheory) : Prop :=
  forall (h1 h2 : History),
    satisfies h1 pt ->
    satisfies h2 pt ->
    forall (t0 : Time), (
      h1 t0 = h2 t0 ->
      forall (t : Time), non_strict Before t0 t -> h1 t = h2 t
    ).

(* to be moved in a separate file? *)
(* Definition stochastic_process (P : probability State_measurable R) : Type :=
  Time -> {RV P >-> R}.

Definition is_stochastic (pt : PhysicalTheory) : Prop :=
  exists (P : probability State_measurable R),
    @distribution _ _ _ State_measurable *)

End deterministic_stochastic_physics.
