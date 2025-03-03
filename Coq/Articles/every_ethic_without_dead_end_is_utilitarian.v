
Require Import Bool.Bool.
Require Import Relations.Relation_Definitions.
Require Import Arith.PeanoNat.
Require Import Classical.

Context {State : Type}.

Context {Action : Type}.

Definition Ethic : Type := State -> Action -> bool.

Definition has_no_dead_end (ethic : Ethic) : Prop :=
  forall (state : State), exists (action : Action), ethic state action = true.

Definition total {T : Type} (R : relation T) := forall (x y : T), R x y \/ R y x.

Definition transitive {T : Type} (R : relation T) := forall (x y z : T),
  R x y -> R y z -> R x z.

Definition preference_order {T : Type} (R : relation T) :=
  transitive R /\ total R.

Definition is_preference_space {T : Type} (R : relation T) : Prop := preference_order R.

Definition is_utility_function {Utility : Type}
(utility_function : State -> Action -> Utility) (R : relation Utility) : Prop :=
  is_preference_space R.

Definition can_be_obtained {Utility : Type}
(utility_function : State -> Action -> Utility) (R : relation Utility)
(state : State) (utility : Utility) :=
  exists (action : Action), utility = utility_function state action.

Definition is_maximum {Utility : Type}
(utility_function : State -> Action -> Utility) (R : relation Utility)
(state : State) (utility : Utility) :=
  can_be_obtained utility_function R state utility /\
  forall (action : Action), R utility (utility_function state action).

Definition results_in_ethic {Utility : Type} {R : relation Utility}
{utility_function : State -> Action -> Utility}
(p : is_utility_function utility_function R) (ethic : Ethic) : Prop :=
  forall (state : State) (action : Action),
    Is_true (ethic state action) <->
    is_maximum utility_function R state (utility_function state action).

Definition is_utilitarian (ethic : Ethic) : Prop :=
  exists (Utility : Type) (R : relation Utility)
  (utility_function : State -> Action -> Utility)
  (p : is_utility_function utility_function R),
    results_in_ethic p ethic.

Definition associated_utility (ethic : Ethic) : State -> Action -> nat :=
  fun state => (fun action => if ethic state action then 0 else 1).

Lemma le_transitive : transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  - apply Hnm.
  - apply le_S. apply IHHmo.
Qed.

Lemma le_total : total le.
Proof.
  intros n m.
  assert (n <= m \/ n > m).
  { apply Nat.le_gt_cases. }
  destruct H.
  - left. tauto.
  - right. unfold gt in H. apply Nat.lt_le_incl. tauto.
Qed.

Lemma associated_utility_is_utility (ethic : Ethic) :
  is_utility_function (associated_utility ethic) le.
Proof.
  unfold is_utility_function. unfold is_preference_space. unfold preference_order.
  split.
  - apply le_transitive.
  - apply le_total.
Qed.

Proposition every_ethic_without_dead_end_is_utilitarian :
  forall (ethic : Ethic), has_no_dead_end ethic -> is_utilitarian ethic.
Proof.
  intros. unfold is_utilitarian.
  exists nat. exists le.
  exists (associated_utility ethic).
  exists (associated_utility_is_utility ethic).
  unfold results_in_ethic. intros. unfold is_maximum.
  split.
  - intro. destruct (ethic state action) eqn:H1.
    2: { simpl in H0. inversion H0. }
    split.
    + unfold can_be_obtained.
      exists action. reflexivity.
    + unfold associated_utility. rewrite H1. intro.
      case (ethic state action0). reflexivity. apply le_S. apply le_n.
  - intro. destruct H0.
    destruct (ethic state action) eqn:H2.
    + reflexivity.
    + unfold associated_utility in H1. rewrite H2 in H1.
      unfold has_no_dead_end in H. pose proof (H state).
      destruct H3 as [action'].
      pose proof (H1 action'). rewrite H3 in H4.
      inversion H4. 
Qed.
