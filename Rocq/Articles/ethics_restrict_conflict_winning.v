
From mathcomp Require Import all_ssreflect.
Require Import Classical.

Require Import eqType_facts.
Require Import ethics_first_steps.
Require Import ethics_in_society.
Require Import occam_razor.
Require Import physical_theories.
Require Import ethics_restrict_goal_achieving.

Section ethics_restrict_conflict_winning.

Context {Time : Type}.
Context {State : Type}.
Context {Action : Type}.
Context {Individual : finType}.
Context {
  physical_theory :
  @PhysicalTheory Time (State * @Profile Individual Action)
}.

Definition GoalProfile : Type :=
  @Profile Individual (@Event Time (State * @Profile Individual Action)).

Definition may_achieve_all (goals : GoalProfile) :
Prop :=
  exists (history : @History Time (State * @Profile Individual Action)),
    satisfies history physical_theory /\
    forall (i : Individual), goals i history.

Definition may_win_conflict (i : Individual) (goals : GoalProfile) :
Prop :=
  ~ may_achieve_all goals /\
  @is_possible Time (
    State * @Profile Individual Action
  ) (goals i)  physical_theory.

Definition may_not_win_conflict (i : Individual) (goals : GoalProfile) :
Prop :=
  ~ may_achieve_all goals /\
  @is_possible Time (State * @Profile Individual Action) (goals i) physical_theory.

Definition state_dynamic_to_subjective (state_d : @State_dynamic Time State)
(i : Individual) : @SubjectiveState (Time * State) Individual :=
  get_SubjectiveState (get_time state_d, get_state state_d) i.

Definition ethic_subjective_to_dynamic
(ethic_subj : @Ethic (@SubjectiveState (Time * State) Individual) Action)
(i : Individual) :
@Ethic (@State_dynamic Time State) (@Profile Individual Action) :=
  fun (state_d : @State_dynamic Time State) =>
  fun (action_profile : @Profile Individual Action) =>
  ethic_subj (
    state_dynamic_to_subjective state_d i
  ) (
    action_profile i
  ).

Definition everyone_follows_its_ethic_dynamic
(history : @History Time (State * @Profile Individual Action))
(ethical_profile : @Profile Individual (@IndividualEthic (Time * State) Action Individual))
(t : Time) :
Prop :=
  forall (i : Individual),
    follows_its_ethic history (
      ethic_subjective_to_dynamic (ethical_profile i) i
    ) t.

Definition everyone_always_follows_its_ethic_dynamic
(history : @History Time (State * @Profile Individual Action))
(ethical_profile : @Profile Individual (@IndividualEthic (Time * State) Action Individual)) :
Prop :=
  forall (i : Individual), always_follows_its_ethic history (
    ethic_subjective_to_dynamic (ethical_profile i) i
  ).

Definition may_all_achieve_ethically (goals : GoalProfile)
(ethical_profile : @Profile Individual (@IndividualEthic (Time * State) Action Individual)) :
Prop :=
  exists (history : @History Time (State * @Profile Individual Action)),
    satisfies history physical_theory /\
    forall (i : Individual), happens_in (goals i) history /\
    everyone_always_follows_its_ethic_dynamic history ethical_profile.

Definition may_achieve_with_ethics (i : Individual)
(goal : @Event Time (State * @Profile Individual Action))
(ethical_profile : @Profile Individual (@IndividualEthic (Time * State) Action Individual)) :
Prop :=
  exists (history : @History Time (State * @Profile Individual Action)),
    satisfies history physical_theory /\
    happens_in goal history /\
    everyone_always_follows_its_ethic_dynamic history ethical_profile.

Definition may_win_conflict_with_ethics (i : Individual)
(ethical_profile : @Profile Individual (@IndividualEthic (Time * State) Action Individual))
(goals : GoalProfile) :
Prop :=
  ~ may_all_achieve_ethically goals ethical_profile /\
  may_achieve_with_ethics i (goals i) ethical_profile.

Definition may_not_win_conflict_with_ethics (i : Individual)
(ethical_profile : @Profile Individual (@IndividualEthic (Time * State) Action Individual))
(goals : GoalProfile) :
Prop :=
  ~ may_all_achieve_ethically goals ethical_profile /\
  ~ may_achieve_with_ethics i (goals i) ethical_profile.

Lemma ethic_restricts_goal_achieving_with_ethics (i : Individual)
(ethical_profile : @Profile Individual (@IndividualEthic (Time * State) Action Individual))
(relaxed_ethic : @Ethic (@SubjectiveState (Time * State) Individual) Action)
(goals : GoalProfile) :
  @more_restrictive_dynamic Time State (@Profile Individual Action) (
    ethic_subjective_to_dynamic (ethical_profile i) i
  ) (
    ethic_subjective_to_dynamic relaxed_ethic i
  ) ->
  may_achieve_with_ethics i (goals i) ethical_profile ->
  may_achieve_with_ethics i (goals i) (
    replace ethical_profile i (
      relaxed_ethic
    )
  ).
Proof.
  unfold may_achieve_with_ethics.
  intros.
  destruct H0 as [history]. destruct H0. destruct H1.
  exists history.
  split.
  { exact H0. }
  split.
  { exact H1. }
  {
    unfold everyone_always_follows_its_ethic_dynamic in *.
    intro.
    unfold always_follows_its_ethic in *.
    intro.
    generalize dependent H2. intro.
    unfold follows_its_ethic in *.
    unfold more_restrictive_dynamic in H.
    specialize (H t). specialize (H (history t).1).
    unfold more_restrictive in H.
    specialize (H (history t).2).
    assert (i0 = i \/ i0 <> i). { apply classic. }
    destruct H3.
    {
      rewrite H3.
      rewrite replace_changes.
      apply H.
      specialize (H2 i t).
      exact H2.
    }
    {
      rewrite replace_unchanges.
      2: { intro. rewrite H4 in H3. apply H3. reflexivity. }
      specialize (H2 i0). specialize (H2 t).
      exact H2.
    }
  }
Qed.

Lemma ethic_restricts_conflict_winning (i : Individual)
(ethical_profile : @Profile Individual (@IndividualEthic (Time * State) Action Individual))
(relaxed_ethic : @Ethic (@SubjectiveState (Time * State) Individual) Action)
(goals : GoalProfile) :
  @more_restrictive_dynamic Time State (@Profile Individual Action) (
    ethic_subjective_to_dynamic (ethical_profile i) i
  ) (
    ethic_subjective_to_dynamic relaxed_ethic i
  ) ->
  may_win_conflict_with_ethics i ethical_profile goals ->
  may_achieve_with_ethics i (goals i) (
    replace ethical_profile i (
      relaxed_ethic
    )
  ).
Proof.
  intros.
  unfold may_win_conflict_with_ethics in H0.
  destruct H0.
  apply ethic_restricts_goal_achieving_with_ethics ; try tauto.
Qed.

End ethics_restrict_conflict_winning.
