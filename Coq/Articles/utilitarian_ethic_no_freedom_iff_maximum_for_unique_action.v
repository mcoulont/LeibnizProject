
Require Import Bool.Bool.
Require Import Relations.Relation_Definitions.
From mathcomp Require Import all_ssreflect.

Require Import ethics_first_steps.
Require Import every_ethic_without_dead_end_is_utilitarian.

Definition State : Type := ethics_first_steps.State.
Definition Action : eqType := ethics_first_steps.Action.

Definition leaves_no_freedom (ethic: Ethic) (state: State) : Prop :=
  exists! (action: Action), ethic state action = true.

Definition never_leaves_freedom (ethic: Ethic) : Prop :=
  forall (state: State), leaves_no_freedom ethic state.

Lemma no_freedom_implies_no_dead_end (ethic: Ethic) (state: State) :
  leaves_no_freedom ethic state -> ~ dead_end ethic state.
Proof.
  intro. unfold leaves_no_freedom in H.
  destruct H. unfold unique in H.
  destruct H. unfold dead_end.
  intro. pose proof (H1 x).
  rewrite H in H2. inversion H2.
Qed.

Corollary never_leaves_freedom_implies_never_has_dead_end (ethic: Ethic) :
  never_leaves_freedom ethic -> without_dead_end ethic.
Proof.
  unfold without_dead_end. unfold never_leaves_freedom. intro.
  intro. apply no_freedom_implies_no_dead_end. apply H.
Qed.

Definition utilitarian_ethic_unique_maximum {ps : PreferenceSpace}
(ethic : Ethic) (uf : @UtilityFunction ps)
(ethic_maximizes_uf : maximizes ethic uf) (state : State) :=
  exists! (action : Action), is_maximum uf state (uf state action).

Definition utilitarian_ethic_always_unique_maximum {ps : PreferenceSpace}
(ethic : Ethic) (uf : @UtilityFunction ps) (ethic_maximizes_uf : maximizes ethic uf) :=
  forall (state: State),
    utilitarian_ethic_unique_maximum ethic uf ethic_maximizes_uf state.

Proposition utilitarian_ethic_no_freedom_iff_maximum_for_unique_action
{ps : PreferenceSpace} :
  forall (ethic: Ethic) (uf : UtilityFunction)
  (ethic_maximizes_uf : maximizes ethic uf) (state: State),
    @utilitarian_ethic_unique_maximum ps ethic uf ethic_maximizes_uf state <->
    leaves_no_freedom ethic state.
Proof.
  intros.
  unfold maximizes in ethic_maximizes_uf.
  split.
  - intro. unfold leaves_no_freedom. unfold unique.
    unfold utilitarian_ethic_unique_maximum in H.
    destruct H. unfold unique in H. destruct H.
    exists x. split.
    + pose proof (ethic_maximizes_uf state). pose proof (H1 x).
      rewrite <- H2 in H. unfold Is_true in H.
      destruct (ethic state x).
      { reflexivity. }
      { inversion H. }
    + intros.
      pose proof (H0 x'). apply H2.
      pose proof (ethic_maximizes_uf state). pose proof (H3 x').
      rewrite <- H4. unfold Is_true.
      rewrite H1. tauto.
  - intro. unfold leaves_no_freedom in H. unfold unique in H.
    unfold utilitarian_ethic_unique_maximum. unfold unique.
    destruct H. destruct H.
    pose proof (ethic_maximizes_uf state).
    exists x. split.
    + pose proof (H1 x).
      rewrite <- H2. rewrite H. easy.
    + intro. pose proof (H0 x'). intro.
      rewrite <- H1 in H3. unfold Is_true in H3.
      destruct (ethic state x').
      { apply H2. reflexivity. }
      { inversion H3. }
Qed.

Corollary utilitarian_ethic_never_freedom_iff_always_maximum_for_unique_action
{ps : PreferenceSpace} :
  forall (ethic: Ethic) (uf : UtilityFunction)
  (ethic_maximizes_uf : maximizes ethic uf),
    @utilitarian_ethic_always_unique_maximum ps ethic uf ethic_maximizes_uf <->
    never_leaves_freedom ethic.
Proof.
  intros. unfold utilitarian_ethic_always_unique_maximum. unfold never_leaves_freedom.
  split ; intros; pose proof (H state) ; 
  apply @utilitarian_ethic_no_freedom_iff_maximum_for_unique_action with
  (ps:=ps) (ethic:=ethic) (uf:=uf) (ethic_maximizes_uf:=ethic_maximizes_uf) ;
  tauto.
Qed.
