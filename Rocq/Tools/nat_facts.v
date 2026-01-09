
Require Import Setoid.

Lemma add_translation (m n p : nat) :
  p + m = p + n <-> m = n.
Proof.
  induction p.
  { simpl. split; intros; assumption. }
  {
    simpl.
    split.
    {
      rewrite <- IHp.
      intro.
      apply eq_add_S. exact H.
    }
    { intro. rewrite H. reflexivity. }
  }
Qed.


Lemma add_comm (m n : nat) :
  m + n = n + m.
Proof.
  intros.
  induction m.
  - simpl.
    rewrite <- plus_n_O.
    reflexivity.
  - simpl.
    rewrite -> IHm.
    rewrite plus_n_Sm.
    reflexivity.
Qed.