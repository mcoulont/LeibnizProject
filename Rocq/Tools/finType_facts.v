
Require Import Classical.
Require Import Relations.Relation_Definitions.
Require Import Arith.PeanoNat.
Require Import Program.Basics.
Require Import Logic.Epsilon.
From mathcomp Require Import all_ssreflect.
From mathcomp.classical Require Import boolp.

Require Import relation_facts.
Require Import preference.

Lemma induction_cardinal (P : finType -> Prop) :
  (forall (T : finType) , #|T| = 0 -> P T) ->
  (forall (n : nat),
    (forall (T : finType), #|T| = n -> P T) ->
    (forall (T : finType), #|T| = S n -> P T)
  ) ->
  forall (T : finType), P T.
Proof.
  intro. intro. intro.
  assert (forall (n : nat) (T : finType), size (enum T) = n -> P T).
  {
    induction n.
    {
      intro. rewrite <- cardE. apply H.
    }
    {
      intro. rewrite <- cardE. apply H0.
      intro. rewrite cardE. apply IHn.
    }
  }
  pose proof (H1 (size (enum T))).
  apply H2.
  reflexivity.
Qed.

Lemma instance_makes_card_nonnull {T : finType} (t : T) :
  0 < #|T|.
Proof.
  specialize (fintype0 t). intro.
  induction #|T|.
  { exfalso. apply H. reflexivity. }
  { auto. }
Qed.

Lemma max_enum_rank {T : finType} (t : T) :
  enum_rank t < #|T| = true.
Proof.
  assert (enum_rank t < #|T|).
  { auto. }
  intuition.
Qed.

Lemma exists_two_distinct (T : finType) :
  #|T| >= 2 -> exists (x y : T), x <> y.
Proof.
  intro.
  assert (0 < #|T|).
  { intuition. }
  exists (enum_val (Ordinal H)).
  exists (enum_val (Ordinal H0)).
  unfold not. intro.
  apply enum_val_inj in H1.
  inversion H1.
Qed.

Lemma exists_2nd_distinct {T : finType} (x : T) :
  #|T| >= 2 -> exists (y : T), y <> x.
Proof.
  intro.
  assert (exists (a b : T), a <> b).
  { apply exists_two_distinct. exact H. }
  destruct H0 as [a]. destruct H0 as [b].
  assert (b = x \/ b <> x).
  { tauto. }
  destruct H1.
  { rewrite <- H1. exists a. exact H0. }
  { exists b. exact H1. }
Qed.

Lemma exists_3rd_distinct {T : finType} (x y : T) :
  #|T| >= 3 -> exists (z : T), z <> x /\ z <> y.
Proof.
  intro.
  assert (1 < #|T|).
  { intuition. }
  assert (0 < #|T|).
  { intuition. }
  assert (enum_val (Ordinal H) <> x \/ enum_val (Ordinal H) = x).
  { tauto. }
  destruct H2.
  {
    assert (enum_val (Ordinal H) <> y \/ enum_val (Ordinal H) = y).
    { tauto. }
    destruct H3.
    {
      exists (enum_val (Ordinal H)).
      tauto.
    }
    {
      assert (enum_val (Ordinal H1) <> x \/ enum_val (Ordinal H1) = x).
      { tauto. }
      destruct H4.
      {
        exists (enum_val (Ordinal H1)).
        split.
        { tauto. }
        {
          intro.
          assert (
            enum_val (Ordinal (n:=#|T|) (m:=2) H) =
            enum_val (Ordinal (n:=#|T|) (m:=0) H1)
          ).
          {
            rewrite H3. rewrite H5.
            reflexivity.
          }
          assert (Ordinal (n:=#|T|) (m:=2) H = Ordinal (n:=#|T|) (m:=0) H1).
          { apply enum_val_inj. tauto. }
          inversion H7.
        }
      }
      {
        exists (enum_val (Ordinal H0)).
        split.
        {
          intro.
          assert (
            enum_val (Ordinal (n:=#|T|) (m:=1) H0) =
            enum_val (Ordinal (n:=#|T|) (m:=0) H1)
          ).
          {
            rewrite H4. rewrite H5.
            reflexivity.
          }
          assert (Ordinal (n:=#|T|) (m:=1) H0 = Ordinal (n:=#|T|) (m:=0) H1).
          { apply enum_val_inj. tauto. }
          inversion H7.
        }
        {
          intro.
          assert (
            enum_val (Ordinal (n:=#|T|) (m:=1) H0) =
            enum_val (Ordinal (n:=#|T|) (m:=2) H)
          ).
          {
            rewrite H3. rewrite H5.
            reflexivity.
          }
          assert (Ordinal (n:=#|T|) (m:=1) H0 = Ordinal (n:=#|T|) (m:=2) H).
          { apply enum_val_inj. tauto. }
          inversion H7.
        }
      }
    }
  }
  {
    assert (enum_val (Ordinal H1) <> y \/ enum_val (Ordinal H1) = y).
    { tauto. }
    destruct H3.
    {
      exists (enum_val (Ordinal H1)).
      split.
      {
        intro.
        assert (
          enum_val (Ordinal (n:=#|T|) (m:=0) H1) =
          enum_val (Ordinal (n:=#|T|) (m:=2) H)
        ).
        {
          rewrite H2. rewrite H4.
          reflexivity.
        }
        assert (Ordinal (n:=#|T|) (m:=0) H1 = Ordinal (n:=#|T|) (m:=2) H).
        { apply enum_val_inj. tauto. }
        inversion H6.
      }
      { tauto. }
    }
    {
      exists (enum_val (Ordinal H0)).
      split.
      {
        intro.
        assert (
          enum_val (Ordinal (n:=#|T|) (m:=1) H0) =
          enum_val (Ordinal (n:=#|T|) (m:=2) H)
        ).
        {
          rewrite H2. rewrite H4.
          reflexivity.
        }
        assert (Ordinal (n:=#|T|) (m:=1) H0 = Ordinal (n:=#|T|) (m:=2) H).
        { apply enum_val_inj. tauto. }
        inversion H6.
      }
      {
        intro.
        assert (
          enum_val (Ordinal (n:=#|T|) (m:=1) H0) =
          enum_val (Ordinal (n:=#|T|) (m:=0) H1)
        ).
        {
          rewrite H3. rewrite H4.
          reflexivity.
        }
        assert (Ordinal (n:=#|T|) (m:=1) H0 = Ordinal (n:=#|T|) (m:=0) H1).
        { apply enum_val_inj. tauto. }
        inversion H6.
      }
    }
  }
Qed.

Definition replace_until {A: finType} {B : A -> Type}
(n : nat) (profile1 profile2 : forall a : A, B a) : forall a : A, B a :=
  fun (a : A) => if (enum_rank a < n) then profile2 a else profile1 a.

Lemma replace_none {A: finType} {B : A -> Type}
(profile1 profile2 : forall a : A, B a) :
  replace_until 0 profile1 profile2 = profile1.
Proof.
  unfold replace_until.
  apply functional_extensionality_dep. intro.
  rewrite ltn0. reflexivity.
Qed.

Lemma replace_all {A: finType} {B : A -> Type}
(profile1 profile2 : forall a : A, B a) :
  replace_until #|A| profile1 profile2 = profile2.
Proof.
  unfold replace_until.
  apply functional_extensionality_dep. intro.
  rewrite max_enum_rank. reflexivity.
Qed.

