
From mathcomp Require Import all_ssreflect.

Require Import ethics_first_steps.
Require Import physical_theories.

Section ethics_restrict_goal_achieving.

Context {Time : Type}.
Context {State : Type}.
Context {Action : Type}.
Context {physical_theory : @PhysicalTheory Time (State * Action)}.

Definition State_dynamic : Type := Time * State.

Definition get_time (state : State_dynamic) : Time :=
  fst state.

Definition get_state (state : State_dynamic) : State :=
  snd state.

Definition state_dynamic (t : Time) (state : State) : State_dynamic :=
  (t, state).

Definition can_achieve (goal : @Event Time (State * Action)) : Prop :=
  is_possible goal physical_theory.

Definition follows_its_ethic (history : @History Time (State * Action))
(ethic : @Ethic State_dynamic Action) (t : Time) : Prop :=
  ethic (
    (t, fst (history t))
  ) (
    snd (history t)
  ).

Definition always_follows_its_ethic (history : @History Time (State * Action))
(ethic :@Ethic State_dynamic Action) : Prop :=
  forall (t : Time), follows_its_ethic history ethic t.

Definition can_achieve_ethically (goal : @Event Time (State * Action))
(ethic : @Ethic State_dynamic Action) : Prop :=
  exists (history : @History Time (State * Action)),
    satisfies history physical_theory /\
    goal history = true /\
    always_follows_its_ethic history ethic.

Lemma ethics_cant_help_goal_achieving
(goal : @Event Time (State * Action)) (ethic : @Ethic State_dynamic Action) :
  can_achieve_ethically goal ethic ->
  can_achieve goal.
Proof.
  intros.
  unfold can_achieve_ethically in H. unfold can_achieve.
  destruct H as [history]. exists history.
  tauto.
Qed.

Definition more_restrictive_dynamic (e1 e2 : @Ethic State_dynamic Action) : Prop :=
  forall (t : Time) (state : State), more_restrictive e1 e2 (
    state_dynamic t state
  ).

Definition strictly_more_restrictive_dynamic
(e1 e2 : @Ethic State_dynamic Action) : Prop :=
  more_restrictive_dynamic e1 e2 /\
  exists (t : Time) (state : State) (action : Action),
    e1 (state_dynamic t state) action = false /\
    e2 (state_dynamic t state) action = true.

Lemma ethic_restricts_goal_achieving (goal : @Event Time (State * Action))
(e1 e2 : @Ethic State_dynamic Action) :
  more_restrictive_dynamic e1 e2 ->
  can_achieve_ethically goal e1 ->
  can_achieve_ethically goal e2.
Proof.
  unfold can_achieve_ethically. intros.
  destruct H0 as [history]. exists history.
  destruct H0. destruct H1.
  split.
  { exact H0. }
  split.
  { exact H1. }
  {
    unfold more_restrictive_dynamic in H. unfold more_restrictive in H.
    unfold always_follows_its_ethic in *.
    intro. specialize (H2 t). specialize (H t).
    unfold follows_its_ethic in *.
    specialize (H (history t).1).
    specialize (H (history t).2).
    tauto.
  }
Qed.

Lemma ethic_strictly_restricts_goal_achieving
(goal : @Event Time (State * Action)) :
  can_achieve goal ->
  can_achieve_ethically goal ethicless.
Proof.
  intro.
  destruct H as [history]. destruct H.
  unfold can_achieve_ethically. exists history.
  split.
  { exact H. }
  split.
  { exact H0. }
  {
    unfold always_follows_its_ethic. intro.
    unfold follows_its_ethic.
    reflexivity.
  }
Qed.

End ethics_restrict_goal_achieving.
