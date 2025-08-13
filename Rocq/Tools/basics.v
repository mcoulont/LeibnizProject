
Lemma eq_symmetric {T : Type} (x y : T) :
  x = y <-> y = x.
Proof.
  split; intro; rewrite H ; reflexivity.
Qed.
