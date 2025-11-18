
From Stdlib Require Import Classical.
Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.Decidable.
From mathcomp Require Import all_algebra all_ssreflect classical_sets boolp.

Require Import relation_facts.
Require Import boolp_facts.
Require Import physical_theories.

Section many_worlds_interpretation.

Context {Time : Type}.
Context {Before : TotalOrder Time}.
Context {State : Type}.
Context {World : Type}.

Definition Indeterminism (pt : @PhysicalTheory Time State) : Type :=
  {
    h1h2t1t2 : ( @History Time State) * ( @History Time State) * Time * Time |
    @instance_indeterminism Time Before State pt (
      fst (fst (fst h1h2t1t2))
    ) (
      snd (fst (fst h1h2t1t2))
    ) (snd (fst h1h2t1t2)) (snd h1h2t1t2)
  }.

Definition get_h1 {pt : @PhysicalTheory Time State} (ind : Indeterminism pt) :
@History Time State :=
  fst (fst (fst (proj1_sig ind))).

Definition get_h2 {pt : @PhysicalTheory Time State} (ind : Indeterminism pt) :
@History Time State :=
  snd (fst (fst (proj1_sig ind))).

Definition get_t1 {pt : @PhysicalTheory Time State} (ind : Indeterminism pt) :
Time :=
  snd (fst (proj1_sig ind)).

Definition get_t2 {pt : @PhysicalTheory Time State} (ind : Indeterminism pt) :
Time :=
  snd (proj1_sig ind).

Definition deterministic_World (pt : @PhysicalTheory Time State) : Type :=
  Indeterminism pt -> bool.

Lemma indeterministic_iff_any_indeterminism (pt : @PhysicalTheory Time State) :
  ~ @is_deterministic Time Before State pt <->
  inhabited (Indeterminism pt).
Proof.
  unfold is_deterministic.
  split.
  {
    intros.
    apply exists_to_inhabited_sig.
    apply not_all_ex_not in H. destruct H as [h1].
    apply not_all_ex_not in H. destruct H as [h2].
    apply imply_to_and in H. destruct H.
    apply imply_to_and in H0. destruct H0.
    apply not_all_ex_not in H1. destruct H1 as [t1].
    apply imply_to_and in H1. destruct H1.
    apply not_all_ex_not in H2. destruct H2 as [t2].
    apply imply_to_and in H2. destruct H2.
    assert ( @instance_indeterminism Time Before State pt h1 h2 t1 t2).
    { unfold instance_indeterminism. tauto. }
    exists ((h1, h2, t1, t2)). simpl. exact H4.
  }
  {
    intros.
    apply inhabited_sig_to_exists in H.
    destruct H as [h1h2t1t2]. unfold instance_indeterminism in H.
    apply ex_not_not_all. exists (h1h2t1t2.1.1.1).
    apply ex_not_not_all. exists (h1h2t1t2.1.1.2).
    intro.
    destruct H. destruct H1. destruct H2. destruct H3.
    specialize (H0 H1 H2 h1h2t1t2.1.2 H3 h1h2t1t2.2 H).
    apply H4. exact H0.
  }
Qed.

Lemma deterministic_iff_no_indeterminism (pt : @PhysicalTheory Time State) :
  @is_deterministic Time Before State pt <->
  ~ inhabited (Indeterminism pt).
Proof.
  pose proof (indeterministic_iff_any_indeterminism pt). tauto.
Qed.

Definition many_worlds_extension
(pt : @PhysicalTheory Time State) :
@PhysicalTheory Time (deterministic_World pt -> State) :=
  fun (h' : @History Time (deterministic_World pt -> State)) =>
    if `[< exists (ind : Indeterminism pt) (w : deterministic_World pt),
      (w ind /\ (fun t => h' t w) = get_h2 ind) \/
      (~ w ind /\ (fun t => h' t w) = get_h1 ind)
    >] then False else (
      forall (w : deterministic_World pt), pt (fun t => h' t w)
    ).

Lemma deterministic_many_worlds_interpretation
(pt : @PhysicalTheory Time State) :
  @is_deterministic Time Before (deterministic_World pt -> State) (
    many_worlds_extension pt
  ).
Proof.
  unfold is_deterministic. unfold many_worlds_extension.
  unfold satisfies. unfold deterministic_World.
  intros.
  destruct (
  `[< exists (ind : Indeterminism pt) (w : Indeterminism pt -> bool),
    w ind /\ h1^~ w = get_h2 ind \/ ~ w ind /\ h1^~ w = get_h1 ind >]
  ) eqn:dstrH1.
  { inversion H. }
  apply false_to_False in dstrH1.
  pose proof (not_ex_all_not (Indeterminism pt) (
    fun (ind : Indeterminism pt) =>
    exists (w : Indeterminism pt -> bool),
      w ind /\ h1^~ w = get_h2 ind \/ ~ w ind /\ h1^~ w = get_h1 ind
  ) dstrH1).
  simpl in H3.
  destruct (
  `[< exists (ind : Indeterminism pt) (w : Indeterminism pt -> bool),
    w ind /\ h2^~ w = get_h2 ind \/ ~ w ind /\ h2^~ w = get_h1 ind >]
  ) eqn:dstrH2.
  { inversion H0. }
  apply false_to_False in dstrH2.
  pose proof (not_ex_all_not (Indeterminism pt) (
    fun (ind : Indeterminism pt) =>
    exists (w : Indeterminism pt -> bool),
      w ind /\ h2^~ w = get_h2 ind \/ ~ w ind /\ h2^~ w = get_h1 ind
  ) dstrH2).
  simpl in H4.
  rewrite <- notP. intro Hndet.
  pose proof (functional_extensionality (h1 t) (h2 t)).
  rewrite <- contrapositive in H5.
  2: { unfold Decidable.decidable. tauto. }
  specialize (H5 Hndet). apply not_all_ex_not in H5.
  destruct H5 as [w Hneq].
  apply equal_f with (x:=w) in H1.
  assert ( @instance_indeterminism Time Before State pt (h1^~ w) (h2^~ w) t0 t).
  {
    unfold instance_indeterminism.
    split.
    { exact H2. }
    split.
    { apply H. }
    split.
    { apply H0. }
    split.
    { rewrite H1. reflexivity. }
    { exact Hneq. }
  }
  set (
    ind := exist ( fun h1h2t1t2 =>
      @instance_indeterminism Time Before State pt (
        fst (fst (fst h1h2t1t2))
      ) (
        snd (fst (fst h1h2t1t2))
      ) (snd (fst h1h2t1t2)) (snd h1h2t1t2)
    ) (((h1^~ w), (h2^~ w), t0, t)) H5
  ).
  specialize (H3 ind). specialize (H4 ind).
  pose proof (not_ex_all_not (Indeterminism pt -> bool) (
    fun (w : Indeterminism pt -> bool) =>
      w ind /\ h1^~ w = get_h2 ind \/ ~ w ind /\ h1^~ w = get_h1 ind
  ) H3).
  simpl in H6. specialize (H6 w).
  pose proof (not_ex_all_not (Indeterminism pt -> bool) (
    fun (w : Indeterminism pt -> bool) =>
      w ind /\ h2^~ w = get_h2 ind \/ ~ w ind /\ h2^~ w = get_h1 ind
  ) H4).
  simpl in H7. specialize (H7 w).
  tauto.
Qed.

End many_worlds_interpretation.
