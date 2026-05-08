
import Mathlib.Order.Defs.Unbundled
import Mathlib.Data.Real.Basic

open Real Function

def preference_order {T : Type} (R : T -> T -> Prop) : Prop :=
  IsTrans T R ∧ Std.Total R

structure PreferenceSpace where
  carrier : Type
  order : carrier -> carrier -> Prop
  is_preference_order : preference_order order

def get_carrier : PreferenceSpace -> Type:=
  fun (ps : PreferenceSpace) => ps.carrier

def prefers_or_indifferent (ps : PreferenceSpace) :
(get_carrier ps) -> (get_carrier ps) -> Prop :=
  ps.order

def indifferent (ps : PreferenceSpace) :
(get_carrier ps) -> (get_carrier ps) -> Prop :=
  fun a => fun b => ps.order a b ∧ ps.order b a

def prefers (ps : PreferenceSpace) :
(get_carrier ps) -> (get_carrier ps) -> Prop :=
  fun a => fun b => ps.order a b ∧ ¬ ps.order b a

def represented_by_ordinal_utility (ps : PreferenceSpace)
(u : get_carrier ps -> get_carrier ps -> ℝ) :
Prop :=
  ∀ (outcome1 outcome2 : get_carrier ps), (
      (prefers ps outcome1 outcome2 ↔ u outcome1 > u outcome1) ∧
      (indifferent ps outcome1 outcome2 ↔ u outcome1 = u outcome1)
  )
