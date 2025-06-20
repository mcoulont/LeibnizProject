
Require Import Classical.
Require Import Sets.Image.
Require Import Relations.Relation_Definitions.
Require Import Program.Basics.
From mathcomp Require Import all_ssreflect.

Require Import relation_facts.

Definition preference_order {T : Type} (R : relation T) : Prop :=
  Relation_Definitions.transitive T R /\ total R.

Lemma preference_order_reflexive {T : Type} (R : relation T) :
  preference_order R -> Relation_Definitions.reflexive T R.
Proof.
  intros. unfold preference_order in H. destruct H.
  apply total_is_reflexive.
  tauto.
Qed.

Lemma second_equal_or_1st_unequal_preference_order {T : eqType} (min : T) :
  preference_order (second_equal_or_1st_unequal min).
Proof.
  unfold second_equal_or_1st_unequal.
  split.
  {
    unfold Relation_Definitions.transitive.
    intros.
    destruct (z == min).
    { intuition. }
    {
      destruct (x == min).
      {
        destruct (y == min).
        { inversion H0. }
        { inversion H. }
      }
      { intuition. }
    }
  }
  {
    unfold total.
    intros.
    destruct (y == min).
    { left. intuition. }
    { destruct (x == min) ; intuition. }
  }
Qed.

Definition PreferenceOrder (T : Type) : Type :=
  { R : relation T | preference_order R }.

Definition non_strict {T : Type} (po : PreferenceOrder T) : relation T :=
  proj1_sig po.

Definition strict {T : Type} (po : PreferenceOrder T) : relation T :=
  fun (x y : T) => ~ non_strict po y x.

Definition indifferent {T : Type} (po : PreferenceOrder T) (a b : T) : Prop :=
  ~ strict po a b /\ ~ strict po b a.

Definition top_choice {T : Type} (po : PreferenceOrder T) (max : T) : Prop :=
  forall (t : T), non_strict po max t.

Definition bottom_choice {T : Type} (po : PreferenceOrder T) (min : T) : Prop :=
  forall (t : T), non_strict po t min.

Definition very_top_choice {T : Type} (po : PreferenceOrder T) (t : T) :
Prop :=
  forall (u : T), u <> t -> strict po t u.

Definition very_bottom_choice {T : Type} (po : PreferenceOrder T) (t : T) :
Prop :=
  forall (u : T), u <> t -> strict po u t.

Definition very_extremal_choice {T : Type} (po : PreferenceOrder T) (t : T) : Prop :=
  very_top_choice po t \/ very_bottom_choice po t.

Lemma not_extremal {T : Type} (po : PreferenceOrder T) (b : T) :
  ~ very_extremal_choice po b ->
  exists (a c : T), a <> b /\ c <> b /\ non_strict po a b /\ non_strict po b c.
Proof.
  intro.
  unfold very_extremal_choice in H.
  specialize (not_or_and (very_top_choice po b) (very_bottom_choice po b ) H). intro.
  destruct H0.
  unfold very_top_choice in H0. unfold very_bottom_choice in H1.
  specialize (not_all_ex_not T (fun (u : T) => (u <> b -> strict po b u)) H0). intro.
  destruct H2.
  specialize (not_all_ex_not T (fun (u : T) => (u <> b -> strict po u b)) H1). intro.
  destruct H3 as [y].
  unfold strict in H2. unfold strict in H3.
  exists x. exists y.
  tauto.
Qed.

Lemma transitivity_stable_by_flip {T : Type} {R : relation T}
(trans : Relation_Definitions.transitive T R) :
  Relation_Definitions.transitive T (flip R).
Proof.
  unfold Relation_Definitions.transitive in *. intros. unfold flip in *.
  apply trans with (y:=y) ; tauto.
Qed.

Lemma total_stable_by_flip {T : Type} {R : relation T}
(tot : total R) :
  total (flip R).
Proof.
  unfold total in *. intros. unfold flip in *.
  apply tot.
Qed.

Lemma preference_order_stable_by_flip {T : Type} {R : relation T}
(p_o : preference_order R) :
  preference_order (flip R).
Proof.
  unfold preference_order in *. destruct p_o.
  split.
  - apply transitivity_stable_by_flip ; tauto.
  - apply total_stable_by_flip ; tauto.
Qed.

Definition reverse {T : Type} (po : PreferenceOrder T) : PreferenceOrder T :=
  exist preference_order (
    Basics.flip (non_strict po)
  ) (preference_order_stable_by_flip (proj2_sig po)).

Lemma strict_never_reflexive {T : Type} (po : PreferenceOrder T) (a : T) :
  ~ strict po a a.
Proof.
  intro. unfold strict in H. unfold non_strict in H.
  apply H.
  destruct po.
  assert (Relation_Definitions.reflexive T x) .
  { apply preference_order_reflexive. exact p. }
  unfold Relation_Definitions.reflexive in H0.
  simpl. apply H0.
Qed.

Lemma strict_implies_unequal {T : Type} (po : PreferenceOrder T) (a b : T) :
  strict po a b -> a <> b.
Proof.
  unfold strict.
  intro.
  unfold not. intro.
  rewrite H0 in H.
  apply H.
  destruct po. simpl.
  apply preference_order_reflexive. tauto.
Qed.

Lemma strict_implies_non_strict {T : Type} (po : PreferenceOrder T) (a b: T) :
  strict po a b -> non_strict po a b.
Proof.
  intro. unfold strict in H.
  assert (non_strict po a b \/ non_strict po b a).
  {
    destruct po. simpl in *. unfold preference_order in p. destruct p.
    unfold total in H1. pose proof (H1 a b). tauto.
  }
  tauto.
Qed.

Lemma non_strict_transitive {T : Type} (po : PreferenceOrder T) (a b c: T) :
  non_strict po a b ->
  non_strict po b c ->
  non_strict po a c.
Proof.
  intros.
  destruct po. destruct p. simpl in *.
  unfold Relation_Definitions.transitive in t. apply t with (y:=b) ; tauto.
Qed.

Lemma non_strict_strict_transitive {T : Type} (po : PreferenceOrder T) (a b c: T) :
  non_strict po a b ->
  strict po b c ->
  strict po a c.
Proof.
  intros.
  unfold strict in *.
  intro.
  assert (non_strict po c b).
  {
    destruct po. destruct p. unfold Relation_Definitions.transitive in t.
    simpl in *. apply t with (y:=a) ; tauto.
  }
  apply H0. exact H2.
Qed.

Lemma strict_non_strict_transitive {T : Type} (po : PreferenceOrder T) (a b c: T) :
  strict po a b ->
  non_strict po b c ->
  strict po a c.
Proof.
  intros.
  unfold strict in *.
  intro.
  assert (non_strict po b a).
  {
    destruct po. destruct p. unfold Relation_Definitions.transitive in t.
    simpl in *. apply t with (y:=c) ; tauto.
  }
  apply H. exact H2.
Qed.

Lemma strict_transitive {T : Type} (po : PreferenceOrder T) (a b c: T) :
  strict po a b ->
  strict po b c ->
  strict po a c.
Proof.
  intros.
  assert (non_strict po b c).
  { apply strict_implies_non_strict. exact H0. }
  { apply strict_non_strict_transitive with (b:=b) ; tauto. }
Qed.

Lemma strict_asymmetric {T : Type} (po : PreferenceOrder T) (a b: T) :
  strict po a b ->
  strict po b a ->
  False.
Proof.
  unfold strict.
  intros.
  destruct po. unfold preference_order in p. destruct p.
  simpl in *.
  unfold total in t0. pose proof (t0 a b).
  destruct H1 ; tauto.
Qed.

Definition same_order {T : Type} (po1 po2 : PreferenceOrder T) (a b : T) : Prop :=
  (strict po1 a b <-> strict po2 a b) /\
  (strict po1 b a <-> strict po2 b a) /\
  (indifferent po1 b a <-> indifferent po2 b a).

Lemma same_order_strict_case {T : Type} (po1 po2 : PreferenceOrder T) (a b : T) :
  strict po1 a b ->
  strict po2 a b ->
  same_order po1 po2 a b.
Proof.
  intros. unfold same_order.
  split.
  { tauto. }
  split.
  {
    split.
    { intro. exfalso. apply strict_asymmetric with (a:=b) (b:=a) (po:=po1) ; tauto. }
    { intro. exfalso. apply strict_asymmetric with (a:=b) (b:=a) (po:=po2) ; tauto. }
  }
  { unfold indifferent. tauto. }
Qed.

Lemma same_order_symmetric {T : Type} (po1 po2 : PreferenceOrder T) (a b: T) :
  same_order po1 po2 a b <-> same_order po1 po2 b a.
Proof.
  unfold same_order. unfold indifferent.
  tauto.
Qed.

Lemma same_order_non_strict {T : Type} (po1 po2 : PreferenceOrder T) (a b: T) :
  same_order po1 po2 a b ->
  non_strict po1 a b ->
  non_strict po2 a b.
Proof.
  intros.
  unfold same_order in H.
  destruct H. destruct H1.
  unfold strict in H1. tauto.
Qed.

Lemma same_order_characterization {T : Type} (po1 po2 : PreferenceOrder T) (a b : T) :
  same_order po1 po2 a b <->
  (
    (strict po1 a b <-> strict po2 a b) /\
    (strict po1 b a <-> strict po2 b a)
  ).
Proof.
  unfold same_order.
  split.
  { intro. tauto. }
  {
    intro. destruct H.
    split.
    { exact H. }
    split.
    { exact H0. }
    unfold indifferent. tauto.
  }
Qed.

Lemma preference_order_stable_by_map {T U : Type} (f : T -> U)
(R : relation U) (prefo : preference_order R) :
  preference_order (map_relation f R).
Proof.
  unfold preference_order.
  destruct prefo. split.
  {
    unfold Relation_Definitions.transitive in *.
    intros.
    unfold map_relation in *.
    pose proof (H (f x) (f y) (f z)).
    apply H3 ; tauto.
  }
  {
    unfold total in *.
    intros.
    unfold map_relation in *.
    pose proof (H0 (f x) (f y)).
    exact H1.
  }
Qed.

Definition map_PreferenceOrder {T U : Type} (f : T -> U)
(po : PreferenceOrder U) : PreferenceOrder T :=
  exist preference_order (map_relation f (proj1_sig po)) (
    preference_order_stable_by_map f (proj1_sig po) (proj2_sig po)
  ).

Lemma preference_antisym_iff_total_order {T : Type} {R : relation T}
(p_o : preference_order R) :
  Relation_Definitions.antisymmetric T R <-> total_order R.
Proof.
  unfold total_order.
  split.
  {
    intros.
    split.
    {
      destruct p_o.
      exact H1.
    }
    {
      split.
      { apply preference_order_reflexive. exact p_o. }
      { destruct p_o. exact H0. }
      { exact H. }
    }
  }
  {
    intros.
    destruct H. destruct H0.
    exact ord_antisym.
  }
Qed.

Definition single_bottom_others_indifferent {T : eqType} (min : T) :
PreferenceOrder T :=
  exist preference_order (second_equal_or_1st_unequal min) (
    second_equal_or_1st_unequal_preference_order min
  ).

Lemma single_bottom_very_bottom {T : eqType} (min : T) :
  very_bottom_choice (single_bottom_others_indifferent min) min.
Proof.
  unfold single_bottom_others_indifferent. unfold very_bottom_choice.
  intros.
  unfold second_equal_or_1st_unequal. unfold strict. unfold non_strict.
  simpl. intro.
  destruct (u == min) eqn:Eumin.
  {
    assert (u = min).
    { by apply/eqP. }
    apply H. exact H1.
  }
  {
    assert ((min == min) = true).
    { rewrite eq_refl. reflexivity. }
    rewrite H1 in H0. inversion H0.
  }
Qed.

Structure PreferenceSpace : Type := {
    carrier :> Type ;
    order : relation carrier ;
    is_preference_order: preference_order order
}.

Definition get_carrier : PreferenceSpace -> Type:=
  fun (ps : PreferenceSpace) => ps.(carrier).

Definition get_preference_order (ps : PreferenceSpace) : relation (get_carrier ps) :=
  ps.(order).
