
From mathcomp Require Import all_ssreflect.
From mathcomp.classical Require Import boolp.

Require Import ethics_first_steps.
Require Import ethics_in_society.
Require Import deterministic_stochastic_physics.
Require Import ethics_restrict_goal_achieving.

Section ethics_restrict_conflict_winning.

Context {Time : Type}.
Context {State : Type}.
Context {Action : Type}.
Context {Individual : finType}.
Context {
  physical_theory :
  @PhysicalTheory Time (State * @ActionProfile Action Individual)
}.

Definition GoalProfile : Type :=
  Individual -> @Event Time (State * @ActionProfile Action Individual).

Definition can_achieve_all (goals : GoalProfile) :
Prop :=
  exists (history : @History Time (State * @ActionProfile Action Individual)),
    satisfies history physical_theory /\
    forall (i : Individual), goals i history.

Definition can_win_conflict (i : Individual) (goals : GoalProfile) :
Prop :=
  ~ can_achieve_all goals /\
  @can_achieve Time State (
    @ActionProfile Action Individual
  ) physical_theory (goals i).

Definition cannot_win_conflict (i : Individual) (goals : GoalProfile) :
Prop :=
  ~ can_achieve_all goals /\
  @can_achieve Time State (
    @ActionProfile Action Individual
  ) physical_theory (goals i).

Definition state_dynamic_to_subjective (state_d : @State_dynamic Time State)
(i : Individual) : @SubjectiveState (Time * State) Individual :=
  get_SubjectiveState (get_time state_d, get_state state_d) i.

Definition ethic_subjective_to_dynamic
(ethic_subj : @Ethic (@SubjectiveState (Time * State) Individual) Action)
(i : Individual) :
@Ethic (@State_dynamic Time State) (@ActionProfile Action Individual) :=
  fun (state_d : @State_dynamic Time State) =>
  fun (action_profile : @ActionProfile Action Individual) =>
  ethic_subj (
    state_dynamic_to_subjective state_d i
  ) (
    action_profile i
  ).

Definition everyone_follows_its_ethic_dynamic
(history : @History Time (State * @ActionProfile Action Individual))
(ethical_profile : @EthicalProfile (Time * State) Action Individual)
(t : Time) : Prop :=
  forall (i : Individual),
    follows_its_ethic history (
      ethic_subjective_to_dynamic (ethical_profile i) i
    ) t.

Definition everyone_always_follows_its_ethic_dynamic
(history : @History Time (State * @ActionProfile Action Individual))
(ethical_profile : @EthicalProfile (Time * State) Action Individual) : Prop :=
  forall (i : Individual), always_follows_its_ethic history (
    ethic_subjective_to_dynamic (ethical_profile i) i
  ).

Definition can_all_achieve_ethically (goals : GoalProfile)
(ethical_profile : @EthicalProfile (Time * State) Action Individual) : Prop :=
  exists (history : @History Time (State * @ActionProfile Action Individual)),
    satisfies history physical_theory /\
    forall (i : Individual), happens_in (goals i) history /\
    everyone_always_follows_its_ethic_dynamic history ethical_profile.

Definition can_achieve_with_ethics (i : Individual)
(goal : @Event Time (State * @ActionProfile Action Individual))
(ethical_profile : @EthicalProfile (Time * State) Action Individual) : Prop :=
  exists (history : @History Time (State * @ActionProfile Action Individual)),
    satisfies history physical_theory /\
    happens_in goal history /\
    everyone_always_follows_its_ethic_dynamic history ethical_profile.

Definition can_win_conflict_with_ethics (i : Individual)
(ethical_profile : @EthicalProfile (Time * State) Action Individual)
(goals : GoalProfile) :
Prop :=
  ~ can_all_achieve_ethically goals ethical_profile /\
  can_achieve_with_ethics i (goals i) ethical_profile.

Definition cannot_win_conflict_with_ethics (i : Individual)
(ethical_profile : @EthicalProfile (Time * State) Action Individual)
(goals : GoalProfile) :
Prop :=
  ~ can_all_achieve_ethically goals ethical_profile /\
  ~ can_achieve_with_ethics i (goals i) ethical_profile.

Lemma ethic_restricts_goal_achieving_with_ethics (i : Individual)
(ethical_profile : @EthicalProfile (Time * State) Action Individual)
(relaxed_ethic : @Ethic (@SubjectiveState (Time * State) Individual) Action)
(goals : GoalProfile) :
  @more_restrictive_dynamic Time State (@ActionProfile Action Individual) (
    ethic_subjective_to_dynamic (ethical_profile i) i
  ) (
    ethic_subjective_to_dynamic relaxed_ethic i
  ) ->
  can_achieve_with_ethics i (goals i) ethical_profile ->
  can_achieve_with_ethics i (goals i) (
    replace_individual_ethic ethical_profile i (
      relaxed_ethic
    )
  ).
Proof.
  unfold can_achieve_with_ethics.
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
    unfold replace_individual_ethic.
    destruct (i0 == i) eqn:Ei0i.
    {
      assert (i0 == i).
      { intuition. }
      rewrite eq_opE in H3.
      rewrite H3. apply H.
      specialize (H2 i t).
      exact H2.
    }
    {
      specialize (H2 i0). specialize (H2 t).
      exact H2.
    }
  }
Qed.

Lemma ethic_restricts_conflict_winning (i : Individual)
(ethical_profile : @EthicalProfile (Time * State) Action Individual)
(relaxed_ethic : @Ethic (@SubjectiveState (Time * State) Individual) Action)
(goals : GoalProfile) :
  @more_restrictive_dynamic Time State (@ActionProfile Action Individual) (
    ethic_subjective_to_dynamic (ethical_profile i) i
  ) (
    ethic_subjective_to_dynamic relaxed_ethic i
  ) ->
  can_win_conflict_with_ethics i ethical_profile goals ->
  can_achieve_with_ethics i (goals i) (
    replace_individual_ethic ethical_profile i (
      relaxed_ethic
    )
  ).
Proof.
  intros.
  unfold can_win_conflict_with_ethics in H0.
  destruct H0.
  apply ethic_restricts_goal_achieving_with_ethics ; try tauto.
Qed.

End ethics_restrict_conflict_winning.
