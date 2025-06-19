
Require Import Logic.Classical_Pred_Type.
Require Import Logic.FunctionalExtensionality.
From mathcomp Require Import all_ssreflect.

Require Import ethics_first_steps.
Require Import every_ethic_without_dead_end_is_utilitarian.
Require Import objective_ethics_no_disapproval_iff_same_ethic.
Require Import more_restrictive_ethics_diminish_conflicts.

Section unanimous_altruism_not_enough_to_avoid_conflicts.

Context {State : Type}.
Context {Action : eqType}.
Context {Individual : finType}.
Context {feasible : State -> @ActionProfile Action Individual -> bool}.

Definition generalized_whole_society
(e : @IndividualEthic State Action Individual) : EthicalProfile :=
  fun (i : Individual) => e.

Definition altruist (e : @IndividualEthic State Action Individual)
(state : State) : Prop :=
  exists (ap : @ActionProfile Action Individual),
    @no_conflict State Action Individual feasible (
      generalized_whole_society e
    ) ap state.

Lemma no_dead_end_if_altruist (e : @IndividualEthic State Action Individual)
(state : State) :
  altruist e state ->
  forall (i : Individual), ~ dead_end e (get_SubjectiveState state i).
Proof.
  intros.
  unfold altruist in H. destruct H as [ap]. unfold generalized_whole_society in H.
  assert (~ dead_end ((fun (i : Individual) => e) i) (get_SubjectiveState state i)).
  {
    apply (@no_dead_end_if_no_conflict State Action Individual feasible (
      fun (i : Individual) => e
    ) ap state).
    exact H.
  }
  simpl in H0. exact H0.
Qed.

Definition bipartite_contest (state : State) (i j : Individual)
(a_i a_j b_i b_j : Action) : Prop :=
  i <> j /\
  (
    forall (ap : @ActionProfile Action Individual),
      ap i = a_i ->
      ap j = a_j ->
      feasible state ap = false
  ) /\ (
    exists (ap : @ActionProfile Action Individual),
      ap i = a_i /\
      ap j = b_j /\
      feasible state ap = true
  ) /\ (
    exists (ap : @ActionProfile Action Individual),
      ap i = b_i /\
      ap j = a_j /\
      feasible state ap = true
  ).

Proposition unanimous_altruism_not_enough_to_avoid_conflicts (state : State) :
  (
    exists (i j : Individual) (a_i a_j b_i b_j : Action),
      bipartite_contest state i j a_i a_j b_i b_j
  ) -> (
    exists (ep : EthicalProfile) (ap : @ActionProfile Action Individual),
      @conflict State Action Individual feasible ep ap state /\
      forall (k : Individual), altruist (ep k) state
  ).
Proof.
  intro.
  destruct H as [i]. destruct H as [j]. destruct H as [a_i]. destruct H as [a_j].
  destruct H as [b_i]. destruct H as [b_j].
  exists (
    fun (k : Individual) =>
    fun (subj_state : SubjectiveState) =>
    fun (action : Action) =>
    if (k == i) then (
      if (subj_state.(individual) == i) then (
        if (action == a_i) then true else
        if (action == b_i) then true else
        false
      ) else if (subj_state.(individual) == j) then (
        if (action == b_j) then true else false
      ) else true
    )
    else (
      if (subj_state.(individual) == j) then (
        if (action == a_j) then true else
        if (action == b_j) then true else
        false
      ) else if (subj_state.(individual) == i) then (
        if (action == b_i) then true else false
      ) else true
    )
  ).
  exists (
    fun (k : Individual) =>
    if (k == i) then a_i else a_j
  ).
  split.
  {
    unfold conflict.
    split.
    {
      unfold bipartite_contest in H.
      destruct H. unfold not in H.
      assert ((i == j) = false).
      { by apply/eqP. }
      destruct H0.
      apply H0.
      { rewrite eq_refl. reflexivity. }
      { rewrite eq_sym. rewrite H1. reflexivity. }
    }
    {
      unfold everyone_follows_its_ethic.
      intro.
      destruct (i0 == i) eqn:Di0i.
      {
        rewrite Di0i.
        rewrite eq_refl.
        reflexivity.
      }
      {
        rewrite Di0i.
        rewrite eq_refl.
        rewrite proj_individual_SubjectiveState.
        destruct (i0 == j) eqn:Di0j ; reflexivity.
      }
    }
  }
  {
    intro.
    unfold altruist.
    unfold bipartite_contest in H.
    destruct H. destruct H0. destruct H1.
    destruct (k == i) eqn:Dki.
    {
      destruct H1 as [ap].
      exists (
        fun (k : Individual) =>
        if (k == i) then a_i else
        if (k == j) then b_j else
        ap k
      ).
      unfold no_conflict.
      destruct H1. destruct H3.
      split.
      {
        rewrite <- H1. rewrite <- H3.
        assert (
          (fun k0 : Individual => if k0 == i then ap i else if k0 == j then ap j else ap k0) = ap
        ).
        {
          apply functional_extensionality. intro.
          destruct (x == i) eqn:Dxi.
          {
            assert (x = i).
            { by apply/eqP. }
            rewrite H5. reflexivity.
          }
          {
            destruct (x == j) eqn:Dxj.
            {
              assert (x = j).
              { by apply/eqP. }
              rewrite H5. reflexivity.
            }
            reflexivity.
          }
        }
        rewrite H5.
        apply H4.
      }
      {
        unfold everyone_follows_its_ethic. intro.
        unfold generalized_whole_society.
        rewrite proj_individual_SubjectiveState.
        destruct (i0 == i) eqn: Di0i.
        {
          rewrite eq_refl.
          reflexivity.
        }
        {
          destruct (i0 == j) eqn: Di0j.
          {
            rewrite eq_refl.
            reflexivity.
          }
          { reflexivity. }
        }
      }
    }
    {
      destruct H2 as [ap].
      exists (
        fun (k : Individual) =>
        if (k == i) then b_i else
        if (k == j) then a_j else
        ap k
      ).
      unfold no_conflict.
      destruct H2. destruct H3.
      split.
      {
        rewrite <- H2. rewrite <- H3.
        assert (
          (fun k0 : Individual => if k0 == i then ap i else if k0 == j then ap j else ap k0) = ap
        ).
        {
          apply functional_extensionality. intro.
          destruct (x == i) eqn:Dxi.
          {
            assert (x = i).
            { by apply/eqP. }
            rewrite H5. reflexivity.
          }
          {
            destruct (x == j) eqn:Dxj.
            {
              assert (x = j).
              { by apply/eqP. }
              rewrite H5. reflexivity.
            }
            reflexivity.
          }
        }
        rewrite H5.
        apply H4.
      }
      {
        unfold everyone_follows_its_ethic. intro.
        unfold generalized_whole_society.
        rewrite proj_individual_SubjectiveState.
        destruct (i0 == i) eqn: Di0i.
        {
          rewrite eq_refl.
          destruct (i0 == j) eqn: Di0j.
          {
            assert (i0 = i).
            { by apply/eqP. }
            assert (i0 = j).
            { by apply/eqP. }
            assert (i = j).
            {
              rewrite <- H5. rewrite <- H6.
              reflexivity.
            }
            exfalso.
            apply H in H7. inversion H7.
          }
          { reflexivity. }
        }
        {
          destruct (i0 == j) eqn: Di0j.
          {
            rewrite eq_refl.
            reflexivity.
          }
          { reflexivity. }
        }
      }
    }
  }
Qed.

End unanimous_altruism_not_enough_to_avoid_conflicts.
