
Require Import Corelib.ssr.ssrfun.
Require Import Stdlib.Logic.IndefiniteDescription.
Require Import Stdlib.Logic.ClassicalDescription.
Require Import Classical.

Require Import relation_facts.

Definition equipotent (T U : Type) : Prop :=
  exists f : T -> U, bijective f.

Definition in_image {A B : Type} (f : A -> B) (b : B) : Prop :=
  exists a : A, f a = b.

Definition antecedent {A B : Type} (f : A -> B) (b : B) : option A.
Proof.
  destruct (excluded_middle_informative (in_image f b)) as [b_in | b_out].
  - unfold in_image in b_in.
    destruct (constructive_indefinite_description _ b_in) as [a eq_fa_b].
    exact (Some a).
  - exact None.
Defined.

Lemma antecedent_exists {A B : Type} (f : A -> B) (a : A) (b : B) :
  antecedent f b = Some a -> f a = b.
Proof.
  unfold antecedent.
  intro.
  destruct (excluded_middle_informative (in_image f b)).
  {
    destruct (
      constructive_indefinite_description (fun a : A => f a = b) i
    ) in H.
    injection H.
    intro. rewrite H0 in e. exact e.
  }
  { inversion H. }
Qed.

Lemma antecedent_not_exists {A B : Type} (f : A -> B) (a : A) (b : B) :
  antecedent f b = None -> f a <> b.
Proof.
  unfold antecedent.
  intro.
  destruct (excluded_middle_informative (in_image f b)).
  {
    destruct (
      constructive_indefinite_description (fun a : A => f a = b) i
    ) in H.
    inversion H.
  }
  {
    unfold in_image in n.
    apply not_ex_all_not with (n:=a) in n.
    exact n.
  }
Qed.

Lemma inj_implies_antecedent_unique {A B : Type} {f : A -> B}
(_ : injective f) (a : A) :
  antecedent f (f a) = Some a.
Proof.
  unfold antecedent.
  destruct (excluded_middle_informative (in_image f (f a))).
  {
    destruct (
      constructive_indefinite_description (fun a0 : A => f a0 = f a) i
    ).
    specialize (H x a e).
    rewrite H. reflexivity.
  }
  {
    unfold in_image in n.
    apply not_ex_all_not with (n:=a) in n.
    exfalso. apply n. reflexivity.
  }
Qed.

Definition not_bigger_than (A B : Type) : Prop :=
  exists (f : A -> B), injective f.

Definition get_injection {A B : Type} (H : not_bigger_than A B) : A -> B.
Proof.
  destruct (constructive_indefinite_description _ H) as [f _].
  exact f.
Defined.

Definition not_bigger_than_transitive :
  Relation_Definitions.transitive Type not_bigger_than.
Proof.
  unfold Relation_Definitions.transitive. unfold not_bigger_than.
  intros.
  destruct H as [f inj_f].
  destruct H0 as [g inj_g].
  exists (g \o f).
  apply inj_comp; tauto.
Qed.

Definition smaller_than (A B : Type) : Prop :=
  not_bigger_than A B /\ ~ not_bigger_than B A.

Lemma smaller_than_irreflexive (A : Type) :
  ~ smaller_than A A.
Proof.
  unfold smaller_than. tauto.
Qed.

Lemma smaller_than_assymmetric :
  assymmetric smaller_than.
Proof.
  unfold assymmetric.
  intros.
  unfold smaller_than.
  tauto.
Qed.

Definition smaller_than_transitive :
  Relation_Definitions.transitive Type smaller_than.
Proof.
  unfold Relation_Definitions.transitive. unfold smaller_than.
  intros.
  destruct H. destruct H0.
  split.
  {
    pose proof (not_bigger_than_transitive).
    unfold Relation_Definitions.transitive in H3.
    apply H3 with (y:= y); tauto.
  }
  {
    intro.
    apply H1.
    pose proof (not_bigger_than_transitive).
    unfold Relation_Definitions.transitive in H4.
    apply H4 with (y:=z); tauto.
  }
Qed.

Definition countable (A : Type) : Prop :=
  not_bigger_than A nat.
