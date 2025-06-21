
Require Import Relations.Relation_Definitions.

Require Import relation_facts.
Require Import preference.

Definition total_order {T : Type} (R : relation T) : Prop :=
  Relation_Definitions.reflexive T R /\ Relation_Definitions.transitive T R /\
  Relation_Definitions.antisymmetric T R /\ total R.

Definition TotalOrder (T : Type) : Type :=
  { R : relation T | total_order R }.

Lemma total_order_is_antisymmetric_preference {T : Type} (R : relation T) :
  total_order R <-> (
    preference_order R /\
    Relation_Definitions.antisymmetric T R
  ).
Proof.
  unfold total_order.
  split.
  {
    intro.
    unfold preference_order. tauto.
  }
  {
    intro.
    destruct H.
    repeat split.
    { apply preference_order_reflexive. exact H. }
    { unfold preference_order in H. tauto. }
    { exact H0. }
    { unfold preference_order in H. tauto. }
  }
Qed.
