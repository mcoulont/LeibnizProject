
Require Import Relations.Relation_Definitions.
Require Import Program.Basics.
Require Import Sets.Image.
From mathcomp Require Import all_ssreflect.

Definition total {T : Type} (R : relation T) : Prop :=
  forall (x y : T), R x y \/ R y x.

Lemma total_is_reflexive {T : Type} (R : relation T) :
  total R -> Relation_Definitions.reflexive T R.
Proof.
  intros.
  unfold reflexive. intro.
  unfold total in H. pose proof (H x x).
  tauto.
Qed.

Definition total_order {T : Type} (R : relation T) : Prop :=
  total R /\ Relation_Definitions.order T R.

Definition map_relation {T U : Type} (f : T -> U) (R : relation U) : relation T :=
  fun (x : T) => fun (y : T) => R (f x) (f y).

Definition second_equal_or_1st_unequal {T : eqType} (a : T) : relation T :=
  fun (x : T) => fun (y : T) =>
  if y == a then true else if x == a then false else true.
