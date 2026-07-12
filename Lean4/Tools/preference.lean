
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic

open Real Function

def preference_order {T : Type} (R : T -> T -> Prop) : Prop :=
  IsTrans T R ∧ Std.Total R

lemma preference_order_reflexive {T : Type} (R : T -> T -> Prop) :
preference_order R -> Std.Refl R := by
  intro po; unfold preference_order at po
  apply (@Std.Total.to_refl T R po.right)

def PreferenceOrder (T : Type) : Type := {
  R : T -> T -> Prop // preference_order R
}

structure PreferenceSpace where
  carrier : Type
  order : carrier -> carrier -> Prop
  is_preference_order : preference_order order

def get_carrier : PreferenceSpace -> Type:=
  fun (ps : PreferenceSpace) => ps.carrier

def prefers_or_indifferent {T : Type} (po : PreferenceOrder T) :
T -> T -> Prop :=
  po.val

lemma indifferent_refl {T : Type} (po : PreferenceOrder T) (t : T) :
po.val t t := by
  have refl := (preference_order_reflexive po.val po.property)
  exact Std.Refl.refl t

def indifferent {T : Type} (po : PreferenceOrder T) :
T -> T -> Prop :=
  fun a => fun b => po.val a b ∧ po.val b a

def prefers {T : Type} (po : PreferenceOrder T) :
T -> T -> Prop :=
  fun a => fun b => po.val a b ∧ ¬ po.val b a

lemma strict_preference_implies_non_strict {T : Type} (po : PreferenceOrder T) (a b: T) :
prefers po a b -> prefers_or_indifferent po a b := by
  intro prf
  have dsj : prefers_or_indifferent po a b \/ prefers_or_indifferent po b a := by
    have popty := po.property; unfold preference_order at popty
    unfold prefers_or_indifferent
    exact (popty.right.total a b)
  rcases dsj with poab|poba
  · exact poab
  · unfold prefers_or_indifferent at poba
    exfalso
    apply prf.right
    exact poba

lemma strict_implies_unequal {T : Type} (po : PreferenceOrder T) (a b : T) :
prefers po a b → a ≠ b := by
  unfold prefers; intro str eqab
  rw [eqab] at str; apply str.right
  have popty := po.property; unfold preference_order at popty
  apply indifferent_refl

lemma non_strict_transitive {T : Type} (po : PreferenceOrder T) (a b c: T) :
prefers_or_indifferent po a b ->
prefers_or_indifferent po b c ->
prefers_or_indifferent po a c := by
  intro poab pobc
  have popty := po.property; unfold preference_order at popty
  unfold prefers_or_indifferent at *
  exact (popty.left.trans a b c poab pobc)

lemma strict_transitive {T : Type} (po : PreferenceOrder T) (a b c: T) :
prefers po a b ->
prefers po b c ->
prefers po a c := by
  unfold prefers; intro poab pobc
  have poac := (non_strict_transitive po a b c poab.left pobc.left)
  apply And.intro
  · exact poac
  · intro poca
    have poba := non_strict_transitive po b c a pobc.left poca
    apply poab.right; exact poba

lemma non_mutual_strict {T : Type} (po : PreferenceOrder T) (a b: T) :
prefers po a b -> ¬ prefers po b a := by
  intro poab poba
  have poaa := strict_transitive po a b a poab poba
  have neaa := strict_implies_unequal po a a poaa
  tauto

lemma non_strict_strict_transitive {T : Type} (po : PreferenceOrder T) (a b c: T) :
prefers_or_indifferent po a b ->
prefers po b c ->
prefers po a c := by
  intro poab pobc
  have popty := po.property; unfold preference_order at popty
  unfold prefers prefers_or_indifferent at *
  apply And.intro
  · exact (popty.left.trans a b c poab pobc.left)
  · intro poca
    have pocb := popty.left.trans c a b poca poab
    tauto

lemma strict_non_strict_transitive_preference {T : Type} (po : PreferenceOrder T)
(a b c: T) :
prefers po a b ->
prefers_or_indifferent po b c ->
prefers po a c := by
  intro poab pobc
  unfold prefers at *
  have popty := po.property; unfold preference_order at popty
  apply And.intro
  · exact (popty.left.trans a b c poab.left pobc)
  · intro poca
    have poba := popty.left.trans b c a pobc poca
    tauto

def represented_by_utility {T : Type} (po : PreferenceOrder T) (u : T -> ℝ) :
Prop :=
  ∀ (outcome1 outcome2 : T), (
      (prefers po outcome1 outcome2 ↔ u outcome1 > u outcome1) ∧
      (indifferent po outcome1 outcome2 ↔ u outcome1 = u outcome1)
  )

def represented_by_continuous_utility {T : Type} [TopologicalSpace T]
(po : PreferenceOrder T) (u : T -> ℝ) :
Prop :=
  represented_by_utility po u ∧ Continuous u
