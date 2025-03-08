
Require Import Bool.Bool.
Require Import Relations.Relation_Definitions.
Require Import Arith.PeanoNat.

Context {State : Type}.

Context {Action : Type}.

Definition Ethic : Type := State -> Action -> bool.

Definition dead_end (ethic : Ethic) (state : State) : Prop :=
  forall (action : Action), ethic state action = false.

Definition without_dead_end (ethic : Ethic) : Prop :=
  forall (state : State), ~ dead_end ethic state.

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

Definition UtilityFunction {ps : PreferenceSpace} : Type := State -> Action -> ps.

Definition can_be_obtained {ps : PreferenceSpace}
(uf : UtilityFunction) (state : State) (utility : get_carrier ps) : Prop :=
  exists (action : Action), utility = uf state action.

Definition is_maximum {ps : PreferenceSpace}
(uf : UtilityFunction) (state : State) (utility : get_carrier ps) : Prop :=
  can_be_obtained uf state utility /\
  forall (action : Action), get_preference_order ps utility (uf state action).

Definition maximizes {ps : PreferenceSpace}
(ethic : Ethic) (uf : @UtilityFunction ps) : Prop :=
  forall (state : State) (action : Action),
    Is_true (ethic state action) <->
    is_maximum uf state (uf state action).

Definition is_utilitarian (ethic : Ethic) : Prop :=
  exists (ps : PreferenceSpace) (uf : UtilityFunction), @maximizes ps ethic uf.

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

Lemma le_preference_order : preference_order le.
Proof.
  unfold preference_order. split.
  - apply le_transitive.
  - apply le_total.
Qed.

Definition associatedPreferenceSpace (ethic : Ethic) : PreferenceSpace := {|
  carrier := nat ;
  order := le ;
  is_preference_order := le_preference_order
|}.

Proposition every_ethic_without_dead_end_is_utilitarian :
  forall (ethic : Ethic), without_dead_end ethic -> is_utilitarian ethic.
Proof.
  intros. unfold is_utilitarian.
  exists (associatedPreferenceSpace ethic). exists (associated_utility ethic).
  unfold maximizes. intros. unfold is_maximum.
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
      unfold without_dead_end in H. pose proof (H state).
      unfold dead_end in H3. exfalso. apply H3.
      intro. pose proof (H1 action0).
      destruct (ethic state action0).
      { inversion H4. }
      { reflexivity. }
Qed.
