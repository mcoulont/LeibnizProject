
Require Import Bool.Bool.

Section ethics_first_steps.

Context {State : Type}.
Context {Action : Type}.

Definition Ethic : Type :=
  State -> Action -> bool.

Definition more_restrictive (e1 e2 : Ethic) (state : State) : Prop :=
  forall (action : Action),
    e1 state action = true -> e2 state action = true.

Definition strictly_more_restrictive (e1 e2 : Ethic) (state : State) : Prop :=
  more_restrictive e1 e2 state /\
  exists (action : Action),
    e1 state action = false /\ e2 state action = true.

Lemma every_ethic_more_restrictive_than_itself (state : State) :
  forall (e : Ethic), more_restrictive e e state.
Proof.
  unfold more_restrictive.
  intros.
  exact H.
Qed.

Lemma no_ethic_strictly_more_restrictive_than_itself (state : State) :
  forall (e : Ethic), ~ strictly_more_restrictive e e state.
Proof.
  unfold strictly_more_restrictive.
  unfold not. intros.
  destruct H. destruct H0. destruct H0.
  rewrite H1 in H0. inversion H0.
Qed.

Definition ethicless : Ethic := fun (s : State) => fun (a : Action) => true.

Lemma ethicless_least_restrictive (e : Ethic) (state : State) :
  more_restrictive e ethicless state.
Proof.
  unfold more_restrictive. unfold ethicless.
  intro. reflexivity.
Qed.

End ethics_first_steps.
