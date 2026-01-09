
Require Import Logic.PropExtensionality.
From mathcomp Require Import all_algebra all_ssreflect boolp.

Require Import ssrnat_facts.

Lemma false_to_False {P : Prop} (_ : `[< P >] = false) :
  ~ P.
Proof.
  intro.
  apply asboolT in H0. rewrite H in H0. inversion H0.
Qed.

Lemma bool_eq_equal {E : eqType} (a b : E) :
  (a == b) = `[< a = b >].
Proof.
  destruct (`[< a = b >]) eqn:Eab.
  {
    assert (a = b).
    { apply asboolW. rewrite Eab. intuition. }
    rewrite H.
    rewrite eq_refl.
    reflexivity.
  }
  {
    assert (a <> b).
    {
      assert (`[< b = b >]).
      { apply asboolT. reflexivity. }
      intro.
      rewrite H0 in Eab. rewrite H in Eab.
      inversion Eab.
    }
    destruct (a == b) eqn:Dab.
    2: { reflexivity. }
    {
      exfalso. apply H.
      by apply/eqP.
    }
  }
Qed.
