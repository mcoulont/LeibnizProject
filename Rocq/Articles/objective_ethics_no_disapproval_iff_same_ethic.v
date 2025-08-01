
Require Import Logic.FunctionalExtensionality.
From mathcomp Require Import fintype fingroup perm.

Require Import ethics_in_society.

Section objective_ethics_no_disapproval_iff_same_ethic.

Context {State : Type}.
Context {Action : Type}.
Context {Individual : finType}.

Definition PermutationOnIndividuals : Type := {perm Individual}.

Definition identity_permutation : {perm Individual} := 1.
Definition identity : PermutationOnIndividuals := identity_permutation.

Definition composition :
PermutationOnIndividuals -> PermutationOnIndividuals -> PermutationOnIndividuals :=
  fun σ => fun τ => mulg σ τ.

Notation " σ ∘ τ " := (composition σ τ) (at level 40, no associativity).

Definition IndividualsPermutationOnStates : Type := {
  permutation : State -> PermutationOnIndividuals -> State |
  forall (state : State),
    permutation state identity = state /\
    forall (σ τ : PermutationOnIndividuals),
      permutation (permutation state σ) τ = permutation state (σ ∘ τ)
}.

Definition permutation_subjective_state (ipos : IndividualsPermutationOnStates) :
SubjectiveState -> PermutationOnIndividuals -> SubjectiveState :=
  fun subjective_state => fun σ => get_SubjectiveState (
    proj1_sig ipos (state subjective_state) σ
  ) (σ (individual subjective_state)).

Notation " ipos , subjective_state ⋅ σ " := (
  permutation_subjective_state ipos subjective_state σ
) (at level 100, no associativity).

Definition objective (ethic : @IndividualEthic State Action Individual)
(ipos : IndividualsPermutationOnStates) : Prop :=
  forall (state : State) (individual : Individual) (σ : PermutationOnIndividuals),
    ethic ( ipos , (
      get_SubjectiveState state individual
    ) ⋅ σ ) = ethic (get_SubjectiveState state individual).

Definition everyone_is_objective (ethical_profile : EthicalProfile)
(ipos : IndividualsPermutationOnStates) :=
  forall (i : Individual), objective (ethical_profile i) ipos.

Definition may_disapprove (ethical_profile : EthicalProfile) (i j : Individual)
(state : State) : Prop :=
  exists (action : Action),
    ethical_profile j (get_SubjectiveState state j) action = true /\
    ethical_profile i (get_SubjectiveState state j) action = false.

Definition may_never_disapprove (ethical_profile : EthicalProfile)
(i j : Individual) : Prop :=
  forall (state : State), ~ may_disapprove ethical_profile i j state.

Definition nobody_may_disapprove (ethical_profile : EthicalProfile)
(state : State) : Prop :=
  forall (i j : Individual), ~ may_disapprove ethical_profile i j state.

Definition nobody_may_ever_disapprove (ethical_profile : EthicalProfile) : Prop :=
  forall (state : State), nobody_may_disapprove ethical_profile state.

Lemma same_ethic_implies_may_not_disapprove (ethical_profile : EthicalProfile)
(i j : Individual) (state : State) :
  ethical_profile i (get_SubjectiveState state j) =
  ethical_profile j (get_SubjectiveState state j) ->
    ~ may_disapprove ethical_profile i j state.
Proof.
  intros. unfold not. intros.
  unfold may_disapprove in H0. destruct H0 as [action]. destruct H0.
  rewrite H in H1.
  rewrite H0 in H1. inversion H1.
Qed.

Proposition objective_ethics_may_never_disapprove_implies_same_ethic
(ipos : IndividualsPermutationOnStates) (ethical_profile : EthicalProfile)
(i j : Individual) :
  objective (ethical_profile i) ipos ->
  objective (ethical_profile j) ipos ->
  may_never_disapprove ethical_profile i j ->
  may_never_disapprove ethical_profile j i ->
  ethical_profile i = ethical_profile j.
Proof.
  intros.
  apply functional_extensionality. intro.
  apply functional_extensionality. intro.
  destruct (ethical_profile i x x0) eqn:H3.
  {
    destruct (ethical_profile j x x0) eqn:H4.
    { reflexivity. }
    destruct x.
    pose proof (H state individual (tperm i individual)).
    unfold get_SubjectiveState in H5.
    assert ( forall (action : Action),
      ethical_profile i (
        ipos, {| state := state; individual := individual |} ⋅ tperm i individual
      ) action =
      ethical_profile i {| state := state; individual := individual |} action
    ).
    { intro. rewrite H5. reflexivity. }
    pose proof (H6 x0).
    rewrite H3 in H7.
    unfold permutation_subjective_state in H7.
    rewrite proj_individual_SubjectiveState in H7.
    rewrite proj_state_SubjectiveState in H7.
    rewrite tpermR in H7.
    pose proof (H0 state individual (tperm i individual)).
    unfold get_SubjectiveState in H8.
    assert ( forall (action : Action),
      ethical_profile j (
        ipos, {| state := state; individual := individual |} ⋅ tperm i individual
      ) action =
      ethical_profile j {| state := state; individual := individual |} action
    ).
    { intro. rewrite H8. reflexivity. }
    pose proof (H9 x0).
    rewrite H4 in H10.
    unfold permutation_subjective_state in H10.
    rewrite proj_individual_SubjectiveState in H10.
    rewrite proj_state_SubjectiveState in H10.
    rewrite tpermR in H10.
    pose proof (H2 (proj1_sig ipos state (tperm i individual))).
    exfalso. apply H11. exists x0. split ; tauto.
  }
  {
    destruct (ethical_profile j x x0) eqn:H4.
    2: { reflexivity. }
    destruct x.
    pose proof (H state individual (tperm j individual)).
    unfold get_SubjectiveState in H5.
    assert ( forall (action : Action),
      ethical_profile i (
        ipos, {| state := state; individual := individual |} ⋅ tperm j individual
      ) action =
      ethical_profile i {| state := state; individual := individual |} action
    ).
    { intro. rewrite H5. reflexivity. }
    pose proof (H6 x0).
    rewrite H3 in H7.
    unfold permutation_subjective_state in H7.
    rewrite proj_individual_SubjectiveState in H7.
    rewrite proj_state_SubjectiveState in H7.
    rewrite tpermR in H7.
    pose proof (H0 state individual (tperm j individual)).
    unfold get_SubjectiveState in H8.
    assert ( forall (action : Action),
      ethical_profile j (
        ipos, {| state := state; individual := individual |} ⋅ tperm j individual
      ) action =
      ethical_profile j {| state := state; individual := individual |} action
    ).
    { intro. rewrite H8. reflexivity. }
    pose proof (H9 x0).
    rewrite H4 in H10.
    unfold permutation_subjective_state in H10.
    rewrite proj_individual_SubjectiveState in H10.
    rewrite proj_state_SubjectiveState in H10.
    rewrite tpermR in H10.
    pose proof (H1 (proj1_sig ipos state (tperm j individual))).
    exfalso. apply H11. exists x0. split ; tauto.
  }
Qed.

Corollary objective_ethics_no_disapproval_iff_same_ethic
(ipos : IndividualsPermutationOnStates) (ethical_profile : EthicalProfile) :
  everyone_is_objective ethical_profile ipos ->
  (
    nobody_may_ever_disapprove ethical_profile <->
    everyone_always_same_ethic ethical_profile
  ).
Proof.
  intro. split.
  - intro.
    unfold everyone_always_same_ethic. intro.
    unfold everyone_same_ethic. intros.
    assert (ethical_profile i = ethical_profile j).
    2 : { rewrite H1. reflexivity. }
    unfold everyone_is_objective in H.
    unfold nobody_may_ever_disapprove in H0. unfold nobody_may_disapprove in H0.
    apply objective_ethics_may_never_disapprove_implies_same_ethic with (ipos:=ipos).
    + apply H.
    + apply H.
    + unfold may_never_disapprove. intro. apply H0.
    + unfold may_never_disapprove. intro. apply H0.
  - intro.
    unfold nobody_may_ever_disapprove. intro.
    unfold nobody_may_disapprove. intros.
    apply same_ethic_implies_may_not_disapprove.
    unfold everyone_always_same_ethic in H0. unfold everyone_same_ethic in H0.
    apply H0 with (subjective_state:=(get_SubjectiveState state j)).
Qed.

End objective_ethics_no_disapproval_iff_same_ethic.
