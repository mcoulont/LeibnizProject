
import Mathlib.Order.Defs.Unbundled

def preference_order {T : Type} (R : T -> T -> Prop) : Prop :=
  Transitive R ∧ Total R

structure PreferenceSpace where
  carrier : Type
  order : carrier -> carrier -> Prop
  is_preference_order : preference_order order

def get_carrier : PreferenceSpace -> Type:=
  fun (ps : PreferenceSpace) => ps.carrier

def get_preference_order (ps : PreferenceSpace) : (get_carrier ps) -> (get_carrier ps) -> Prop :=
  ps.order
