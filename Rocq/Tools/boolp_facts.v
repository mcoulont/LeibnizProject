
From mathcomp Require Import all_algebra all_ssreflect boolp.

Lemma false_to_False {P : Prop} (_ : `[< P >] = false) :
  ~ P.
Proof.
  intro.
  apply asboolT in H0. rewrite H in H0. inversion H0.
Qed.
