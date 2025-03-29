
Require Import Relations.Relation_Definitions.

Definition total {T : Type} (R : relation T) := forall (x y : T), R x y \/ R y x.

Definition transitive {T : Type} (R : relation T) := forall (x y z : T),
  R x y -> R y z -> R x z.

Definition preference_order {T : Type} (R : relation T) :=
  transitive R /\ total R.

Structure PreferenceSpace : Type := {
    carrier :> Type ;
    order : relation carrier ;
    is_preference_order: preference_order order
}.

Definition get_carrier : PreferenceSpace -> Type:=
  fun (ps : PreferenceSpace) => ps.(carrier).

Definition get_preference_order (ps : PreferenceSpace) : relation (get_carrier ps) :=
  ps.(order).
