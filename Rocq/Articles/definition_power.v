
Require Import ssr.ssrfun.
From mathcomp Require Import fintype fingroup perm.

Require Import relation_facts.
Require Import ethics_in_society.
Require Import occam_razor.

Section definition_power.

Context {Time : Type}.
Context {State : Type}.
Context {Action : Type}.
Context {Individual : finType}.
Context {Before : TotalOrder Time}.

Definition permutation_History
(ipos : @IndividualsPermutationsActingOnStates State Individual)
(h : @History Time (State * @Profile Individual Action))
(σ : {perm Individual}) :
@History Time (State * @Profile Individual Action) :=
  fun (t : Time) => (
    @permutation_State State Individual ipos (h t).1 σ,
    fun i : Individual => (h t).2 (σ i)
  ).

Definition permutation_Event
(ipos : @IndividualsPermutationsActingOnStates State Individual)
(event : @Event Time (State * @Profile Individual Action))
(σ : {perm Individual}) :
@Event Time (State * @Profile Individual Action) :=
  fun (h : @History Time (State * @Profile Individual Action)) =>
    event (permutation_History ipos h σ).

Definition IndividualPolicy : Type :=
  forall (t0 : Time),
    @HistoryBefore Time (State * @Profile Individual Action) Before t0 -> Action.

Definition individual_follows_policy (i : Individual)
(h : @History Time (State * @Profile Individual Action)) (policy : IndividualPolicy) :
Prop :=
  forall (t : Time),
    snd (h t) i = policy t (
      @History_restriction_Before Time (
        State * @Profile Individual Action
      ) Before t h
    ).

Definition individual_fulfills_goal (i : Individual)
(h : @History Time (State * @Profile Individual Action))
(policy : IndividualPolicy) (goal : @Event Time (State * @Profile Individual Action)) :
Prop :=
  individual_follows_policy i h policy /\
  @happens_in Time (State * @Profile Individual Action) goal h.

Definition individual_may_achieve (i : Individual)
(goal : @Event Time (State * @Profile Individual Action))
(st : @ScientificTheory Time (State * @Profile Individual Action)) :
Prop :=
  exists (h : @History Time (State * @Profile Individual Action))
  (policy : IndividualPolicy),
    individual_fulfills_goal i h policy goal /\
    @satisfies Time (State * @Profile Individual Action) h st.

Definition more_powerful
(ipos : @IndividualsPermutationsActingOnStates State Individual)
(st : @ScientificTheory Time (State * @Profile Individual Action))
(i j : Individual) (state : State) :
Prop :=
  forall (goal : @Event Time (State * @Profile Individual Action)),
    individual_may_achieve j goal st ->
    individual_may_achieve i (
      permutation_Event ipos goal (tperm i j)
    ) st.

Definition strictly_more_powerful
(ipos : @IndividualsPermutationsActingOnStates State Individual)
(st : @ScientificTheory Time (State * @Profile Individual Action))
(i j : Individual) (state : State) :
Prop :=
  more_powerful ipos st i j state /\
  exists (goal : @Event Time (State * @Profile Individual Action)),
    ~ individual_may_achieve j goal st /\
    individual_may_achieve i (
      permutation_Event ipos goal (tperm i j)
    ) st.

End definition_power.
