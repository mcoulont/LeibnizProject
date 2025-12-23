
Require Import relation_facts.
Require Import occam_razor.

Section definition_intelligence.

Context {TimePerception : Type}.
Context {SpacePerception : Type}.
Context {Action : Type}.
Context {Before : TotalOrder TimePerception}.

Definition Policy : Type :=
  forall (t0 : TimePerception),
    @HistoryBefore TimePerception (SpacePerception * Action) Before t0 -> Action.

Definition follows_policy (h : @History TimePerception (SpacePerception * Action))
(policy : Policy) : Prop :=
  forall (t : TimePerception),
    snd (h t) = policy t (
      @History_restriction_Before TimePerception (SpacePerception * Action) Before t h
    ).

Definition follows_policy_before {t0 : TimePerception}
(h0 : @HistoryBefore TimePerception (SpacePerception * Action) Before t0)
(policy : Policy) : Prop :=
  forall (t : {t : TimePerception | strict Before t t0}),
    snd (h0 t) = policy (proj1_sig t) (
      @HistoryBefore_restriction TimePerception (SpacePerception * Action) Before
      (proj1_sig t) t0
      (strict_implies_non_strict Before (proj1_sig t) t0 (proj2_sig t)) h0
    ).

Definition Strategizing : Type :=
  @Event TimePerception (SpacePerception * Action) -> Policy.

Definition fulfills_goal
(h : @History TimePerception (SpacePerception * Action))
(policy : Policy) (goal : @Event TimePerception (SpacePerception * Action)) :
Prop :=
  follows_policy h policy /\
  happens_in goal h.

Definition fulfilled_goal {t0 : TimePerception}
(h0 : @HistoryBefore TimePerception (SpacePerception * Action) Before t0)
(policy : Policy) (goal : @Event TimePerception (SpacePerception * Action)) :
Prop :=
  follows_policy_before h0 policy /\
  happened_before goal h0.

Definition may_achieve (policy : Policy)
(goal : @Event TimePerception (SpacePerception * Action))
(st : @ScientificTheory TimePerception (SpacePerception * Action)) :
Prop :=
  exists (h : @History TimePerception (SpacePerception * Action)),
    fulfills_goal h policy goal /\
    satisfies h st.

Definition more_adequate_in_deterministic_environment (policy1 policy2 : Policy)
(goal : @Event TimePerception (SpacePerception * Action))
(st : @ScientificTheory TimePerception (SpacePerception * Action)) :
Prop :=
  may_achieve policy2 goal st ->
  may_achieve policy1 goal st.

Definition more_intelligent_in_deterministic_environment
(strategizing1 strategizing2 : Strategizing)
(st : @ScientificTheory TimePerception (SpacePerception * Action)) :
Prop :=
  forall (goal : @Event TimePerception (SpacePerception * Action)),
    more_adequate_in_deterministic_environment (
      strategizing1 goal
    ) (
      strategizing2 goal
    ) goal st.

Definition strictly_more_intelligent_in_deterministic_environment
(strategizing1 strategizing2 : Strategizing)
(st : @ScientificTheory TimePerception (SpacePerception * Action)) :
Prop :=
  more_intelligent_in_deterministic_environment strategizing1 strategizing2 st /\
  exists (goal : @Event TimePerception (SpacePerception * Action)),
    may_achieve (strategizing1 goal) goal st /\
    ~ may_achieve (strategizing2 goal) goal st.

End definition_intelligence.
