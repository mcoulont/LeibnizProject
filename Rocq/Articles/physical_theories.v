
Require Import relation_facts.
Require Import occam_razor.

Section physical_theories.

Context {Time : Type}.
Context {Before : TotalOrder Time}.
Context {State : Type}.
Context {offset : Time -> Time -> Time}.

Definition PhysicalTheory : Type := @ScientificTheory Time State.

Definition is_deterministic (pt : PhysicalTheory) : Prop :=
  forall (h1 h2 : @History Time State),
    satisfies h1 pt ->
    satisfies h2 pt ->
    forall (t0 : Time), (
      h1 t0 = h2 t0 ->
      forall (t : Time), strict Before t0 t -> h1 t = h2 t
    ).

Definition instance_indeterminism (pt : PhysicalTheory) (h1 h2 : @History Time State)
(t1 t2 : Time) :
Prop :=
  strict Before t1 t2 /\
  satisfies h1 pt /\
  satisfies h2 pt /\
  h1 t1 = h2 t1 /\
  h1 t2 <> h2 t2.

Definition History_offset (h : @History Time State) (delta_t : Time) :
@History Time State :=
  fun t => h (offset delta_t t).

Definition time_translation_symmetry (pt : PhysicalTheory) : Prop :=
  forall (delta_t : Time) (h : @History Time State),
    satisfies h pt <-> satisfies (History_offset h delta_t) pt.

End physical_theories.
