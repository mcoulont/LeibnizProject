
From mathcomp Require Import all_algebra all_ssreflect classical_sets boolp.

Require Import relation_facts.

Section physical_theories.

Context {Time : Type}.
Context {Before : TotalOrder Time}.
Context {State : Type}.

Definition History : Type := Time -> State.

Definition HistoryUntil (t0 : Time) : Type :=
  { t : Time | non_strict Before t t0 } -> State.

Definition HistoryBefore (t0 : Time) : Type :=
  { t : Time | strict Before t t0 } -> State.

Definition extends {t0 : Time} (h : History) (hu : HistoryUntil t0) : Prop :=
  forall (t : { t : Time | non_strict Before t t0 }),
    non_strict Before (proj1_sig t) t0 -> h (proj1_sig t) = hu t.

Definition Event : Type := pred History.

Definition happens_in (e : Event) (h : History) : Prop :=
  e h = true.

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
      forall (t : Time), strict Before t0 t -> h1 t = h2 t
    ).

Definition instance_indeterminism (pt : PhysicalTheory) (h1 h2 : History)
(t1 t2 : Time) :
Prop :=
  strict Before t1 t2 /\
  satisfies h1 pt /\
  satisfies h2 pt /\
  h1 t1 = h2 t1 /\
  h1 t2 <> h2 t2.

End physical_theories.
