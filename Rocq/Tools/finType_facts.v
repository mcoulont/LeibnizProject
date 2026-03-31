
Require Import ListDef.
Require Import Classical.
Require Import Relations.Relation_Definitions.
Require Import Arith.PeanoNat.
Require Import Program.Basics.
Require Import Logic.Epsilon.
Require Import Logic.FunctionalExtensionality.
Require Import Logic.ClassicalEpsilon.
Require Import Reals.
From mathcomp Require Import all_ssreflect fintype fingroup perm rat.
From mathcomp.classical Require Import boolp.

Require Import relation_facts.
Require Import eqType_facts.
Require Import perm.
Require Import rationals_facts.
Require Import reals_facts.
Require Import preference.

Open Scope nat_scope.

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

Lemma instance_makes_card_positive {T : finType} (t : T) :
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

Open Scope R_scope.

Local Notation "+%R" := Rplus (at level 0, only parsing).

Definition sum_reals {A : finType} (f : A -> R) : R :=
  (\big[+%R/0%R]_a (f a)%R).

Definition sum_reals_in {A : finType} (f : A -> R) : R :=
  (\big[+%R/0%R]_(i in A) (f i)%R).

Lemma iter_Rplus (x y : R) (n : nat) :
  iter n (fun z => x + z) y = x * (INR n) + y.
Proof.
  induction n.
  {
    simpl.
    rewrite Rmult_0_r. rewrite Rplus_0_l.
    reflexivity.
  }
  {
    rewrite iterS. rewrite IHn.
    rewrite S_INR. rewrite Rmult_plus_distr_l. rewrite <- Rplus_assoc.
    rewrite Rmult_1_r. apply Rplus_eq_compat_r. rewrite Rplus_comm.
    reflexivity.
  }
Qed.

Lemma iter_Rplus_0 (x : R) (n : nat) :
  iter n (fun z => x + z) 0 = x * (INR n).
Proof. by rewrite iter_Rplus Rplus_0_r. Qed.

Lemma sum_reals_const (A : finType) (x : R) :
  sum_reals (fun (a : A) => x) = (INR #|A|) * x.
Proof.
  unfold sum_reals.
  by rewrite big_const iter_Rplus_0 Rmult_comm.
Qed.

Lemma sum_reals_in_const (A : finType) (x : R) :
  sum_reals_in (fun (a : A) => x) = (INR #|A|) * x.
Proof.
  unfold sum_reals_in.
  by rewrite big_const iter_Rplus_0 Rmult_comm.
Qed.

Lemma sum_reals_0 (A : finType) :
  sum_reals (fun (_ : A) => 0) = 0.
Proof.
  by rewrite sum_reals_const Rmult_0_r.
Qed.

Lemma sum_reals_eq {A : finType} (E1 E2 : A -> R) :
  (forall a, E1 a = E2 a) ->
  sum_reals E1 = sum_reals E2.
Proof.
  unfold sum_reals.
  intro eqE.
  apply eq_bigr.
  auto.
Qed.

Lemma sum_reals_le {A : finType} (E1 E2 : A -> R) :
  (forall a, E1 a <= E2 a) ->
  sum_reals E1 <= sum_reals E2.
Proof.
  unfold sum_reals.
  intro leE.
  assert (forall a : A, E1 a < E2 a \/ E1 a = E2 a) as taut.
  {
    intro.
    pose proof (Rle_lt_or_eq (E1 a) (E2 a)) as lteq.
    apply (lteq (leE a)).
  }
  assert (0 < 0 \/ 0 = 0) as taut0. { apply Rle_lt_or_eq. reflexivity. }
  elim/big_ind2: _ => // r1 r3 r2 r4.
  apply Rplus_le_compat.
Qed.

Lemma sum_real_constants (A : finType) (c : R) :
  sum_reals (fun _ : A => c) = c * INR #|A|.
Proof.
  unfold sum_reals.
  rewrite big_const.
  rewrite iter_Rplus_0.
  reflexivity.
Qed.

Lemma sum_reals_additive {A : finType} (E1 E2 : A -> R) :
  sum_reals (
    fun a => E1 a + E2 a
  ) = sum_reals E1 + sum_reals E2.
Proof.
  unfold sum_reals.
  assert (0 = 0 + 0) as plus00. { rewrite Rplus_0_r. reflexivity. }
  elim/big_ind3: _ => // r1 r2 r3 r4 r5 r6.
  intros s321 s654.
  rewrite s321. rewrite s654.
  rewrite <- Rplus_assoc. rewrite <- Rplus_assoc.
  apply Rplus_eq_compat_r with (r:=r4).
  rewrite Rplus_assoc. rewrite Rplus_assoc.
  apply Rplus_eq_compat_l with (r:=r2).
  apply Rplus_comm.
Qed.

Lemma sum_reals_inv {A : finType} (E : A -> R) :
  sum_reals (
    fun a => - E a
  ) = - sum_reals E.
Proof.
  apply (Rplus_eq_reg_l (sum_reals E) (sum_reals (fun a : A => - E a)) (- sum_reals E)).
  rewrite Rplus_opp_r.
  rewrite <- sum_reals_additive.
  rewrite <- sum_reals_0 with (A:=A).
  apply sum_reals_eq.
  intro a. rewrite Rplus_opp_r. reflexivity.
Qed.

Lemma sum_reals_mult_constant {A : finType} (E : A -> R) (k : R) :
  sum_reals (
    fun a => k * E a
  ) = k * sum_reals E.
Proof.
  unfold sum_reals.
  assert (0 = k * 0) as mulk0. { rewrite Rmult_0_r. reflexivity. }
  elim/big_ind2: _ => // r1 r3 r2 r4.
  intro k31. intro k42.
  rewrite k31. rewrite k42.
  rewrite Rmult_plus_distr_l. reflexivity.
Qed.

Lemma sum_reals_minus {A : finType} (E1 E2 : A -> R) :
  sum_reals (
    fun a => E1 a - E2 a
  ) = sum_reals E1 - sum_reals E2.
Proof.
  unfold Rminus.
  rewrite sum_reals_additive. rewrite sum_reals_inv.
  reflexivity.
Qed.

Lemma sum_reals_all_null_but_1 {A : finType} (a0 : A) (c : R) :
  sum_reals (fun (a : A) => if a == a0 then c else 0) = c.
Proof.
  unfold sum_reals.
  assert (
    forall a,
      a != a0 ->
      true ->
      (fun (a : A) => if a == a0 then c else 0) a = 0
  ) as null_case.
  {
    intros a ne tru.
    destruct (a == a0).
    { inversion ne. }
    { reflexivity. }
  }
  assert (xpredT a0 = true) as tru. { reflexivity. }
  pose proof (
    @big_only1 R 0 reals_Monoid_Law A a0 xpredT (
      fun (a : A) => if a == a0 then c else 0
    ) tru null_case
  ) as sum_only1.
  simpl in sum_only1. rewrite eq_refl in sum_only1.
  exact sum_only1.
Qed.

Lemma sum_all_null_but_2 {A : finType} {a1 a2 : A} (ne : a1 <> a2) (c d : R) :
  sum_reals (fun (a : A) => if a == a1 then c else (
    if a == a2 then d else 0
  )) = c + d.
Proof.
  assert (
    (fun a : A => if a == a1 then c else if a == a2 then d else 0) =
    (fun a: A =>
      (if a == a1 then c else 0) + (if a == a2 then d else 0)
    )
  ) as dec.
  {
    apply functional_extensionality. intro a.
    destruct (a == a1) eqn:Ea1.
    {
      destruct (a == a2) eqn:Ea2.
      {
        rewrite eq_bool_equivalent in Ea1. rewrite eq_bool_equivalent in Ea2.
        rewrite <- Ea1 in ne. rewrite <- Ea2 in ne.
        exfalso. apply ne.
        reflexivity.
      }
      { rewrite Rplus_0_r. reflexivity. }
    }
    { destruct (a == a2) eqn:Ea2; rewrite Rplus_0_l; reflexivity. }
  }
  rewrite dec.
  rewrite sum_reals_additive.
  rewrite sum_reals_all_null_but_1. rewrite sum_reals_all_null_but_1.
  reflexivity.
Qed.

Lemma sum_reals_add_to_term {A : finType} (E : A -> R) (a0 : A) (c : R) :
  sum_reals (
    fun a => if a == a0 then E a0 + c else E a
  ) = sum_reals E + c.
Proof.
  pose proof (sum_reals_additive E (
    fun a => if a == a0 then c else 0
  )) as sra.
  rewrite sum_reals_all_null_but_1 in sra.
  rewrite <- sra.
  apply sum_reals_eq.
  intro a.
  destruct (a == a0) eqn:Eaa0.
  {
    rewrite eq_bool_equivalent in Eaa0. rewrite Eaa0.
    reflexivity.
  }
  { rewrite Rplus_0_r. reflexivity. }
Qed.

Lemma sum_reals_add_to_2_terms {A : finType} {a1 a2 : A} (E : A -> R)
(ne : a1 <> a2) (c d : R) :
  sum_reals (
    fun a => if a == a1 then E a1 + c else (
      if a == a2 then E a2 + d else E a
    )
  ) = sum_reals E + c + d.
Proof.
  pose proof (sum_reals_additive E (
    fun a => if a == a1 then c else (
      if a == a2 then d else 0
    )
  )) as sra.
  rewrite sum_all_null_but_2 in sra.
  2: { exact ne. }
  rewrite sum_reals_additive in sra.
  rewrite <- Rplus_assoc in sra.
  rewrite <- sra.
  rewrite <- sum_reals_additive.
  apply sum_reals_eq.
  intro a.
  destruct (a == a1) eqn:Eaa1.
  {
    rewrite eq_bool_equivalent in Eaa1. rewrite Eaa1.
    reflexivity.
  }
  {
    destruct (a == a2) eqn:Eaa2.
    {
      rewrite eq_bool_equivalent in Eaa2. rewrite Eaa2.
      reflexivity.
    }
    { rewrite Rplus_0_r. reflexivity. }
  }
Qed.

Lemma sum_reals_perm {A : finType} (f : A -> R) (σ : {perm A}) :
  sum_reals (PermutationsActingOnFunctions f σ) = sum_reals f.
Proof.
  unfold PermutationsActingOnFunctions. unfold sum_reals.
  rewrite (
    reindex_inj ( @perm_inj A σ) (F:=f) (P := fun _ => true) (x:=0%R) (
      op:=reals_SemiGroup_com_law
    )
  ).
  reflexivity.
Qed.

Lemma sum_nonnegative_reals_is_nonnegative {A : finType} {f : A -> R}
(H : forall (a : A), 0 <= f a) :
  0 <= sum_reals f.
Proof.
  pose proof (sum_reals_0 A). rewrite <-H0.
  unfold sum_reals.
  apply sum_reals_le.
  exact H.
Qed.

Lemma sum_reals_distributive {A : finType} (f : A -> R) (k : R) :
  sum_reals (fun a => k * f a) = k * sum_reals f.
Proof.
  unfold sum_reals.
  assert (0 = k * 0).
  { rewrite Rmult_0_r. reflexivity. }
  elim/big_ind2: _ => // r1 r3 r2 r4.
  intros.
  rewrite H0. rewrite H1.
  rewrite Rmult_plus_distr_l.
  reflexivity.
Qed.

Definition sum_nonnegreals {A : finType} (f : A -> nonnegreal) :
nonnegreal :=
  {|
    nonneg := sum_reals (fun a : A => nonneg (f a)) ;
    cond_nonneg := sum_nonnegative_reals_is_nonnegative (fun a => cond_nonneg (f a))
  |}.

Lemma sum_nonnegreals_0 (A : finType) :
  sum_nonnegreals (fun (_ : A) => zero_nonnegreal) = zero_nonnegreal.
Proof.
  apply equal_nonneg_if_equal_reals. apply sum_reals_0.
Qed.

Lemma sum_nonnegreals_eq {A : finType} (E1 E2 : A -> nonnegreal) :
  (forall a, E1 a = E2 a) ->
  sum_nonnegreals E1 = sum_nonnegreals E2.
Proof.
  intro eqE.
  unfold sum_nonnegreals.
  simpl.
  apply equal_nonneg_if_equal_reals.
  apply sum_reals_eq.
  Set Printing Coercions.
  intro a. rewrite eqE.
  reflexivity.
Qed.

Lemma sum_nonnegreals_le {A : finType} (E1 E2 : A -> nonnegreal) :
  (forall a, E1 a <= E2 a) ->
  sum_nonnegreals E1 <= sum_nonnegreals E2.
Proof.
  intros.
  unfold sum_nonnegreals.
  simpl.
  apply sum_reals_le.
  exact H.
Qed.

Lemma sum_nonnegreals_additive {A : finType} (E1 E2 : A -> nonnegreal) :
  sum_nonnegreals (
    fun a => plus_nonneg (E1 a) (E2 a)
  ) = plus_nonneg (sum_nonnegreals E1) (sum_nonnegreals E2).
Proof.
  unfold sum_nonnegreals.
  apply equal_nonneg_if_equal_reals. simpl.
  rewrite <- sum_reals_additive.
  reflexivity.
Qed.

Lemma sum_nonnegreals_add_to_term {A : finType} (E : A -> nonnegreal) (a0 : A)
(c : nonnegreal) :
  sum_nonnegreals (
    fun a => if a == a0 then plus_nonneg (E a0) c else E a
  ) = plus_nonneg (sum_nonnegreals E) c.
Proof.
  unfold sum_nonnegreals.
  apply equal_nonneg_if_equal_reals. simpl.
  rewrite <- sum_reals_add_to_term with (a0:=a0).
  apply sum_reals_eq.
  intro a.
  destruct (a == a0); reflexivity.
Qed.

Close Scope R_scope.

Open Scope rat_scope.

Definition sum_rationals {A : finType} (f : A -> rat) : rat :=
  (\big[addq/0]_a (f a)).

Lemma iter_rat_plus (x y : rat) (n : nat) :
  iter n (fun z => x + z) y = x * (nat_to_rat n) + y.
Proof.
  induction n.
  {
    simpl. rewrite nat_to_rat_0.
    rewrite mulq0r. rewrite addq0l.
    reflexivity.
  }
  {
    rewrite iterS. rewrite IHn.
    rewrite S_nat_to_rat. rewrite mulq_addr. rewrite <- addqA.
    rewrite mulq1r. rewrite addqC. rewrite <- addqA.
    rewrite (addqC x y).
    reflexivity.
  }
Qed.

Lemma iter_rat_plus_0 (x : rat) (n : nat) :
  iter n (fun z => x + z) 0 = x * (nat_to_rat n).
Proof.
  rewrite iter_rat_plus addq0r. reflexivity.
Qed.

Lemma sum_rationals_eq {A : finType} (E1 E2 : A -> rat) :
  (forall a, E1 a = E2 a) ->
  sum_rationals E1 = sum_rationals E2.
Proof.
  unfold sum_rationals.
  intro eqE.
  apply eq_bigr.
  auto.
Qed.

Lemma sum_rational_constants (A: finType) (c : rat) :
  sum_rationals (fun _ : A => c) = c * nat_to_rat #|A|.
Proof.
  unfold sum_rationals.
  rewrite big_const.
  rewrite iter_rat_plus_0.
  reflexivity.
Qed.

Lemma sum_rationals_additive {A : finType} (E1 E2 : A -> rat) :
  sum_rationals (
    fun a => E1 a + E2 a
  ) = sum_rationals E1 + sum_rationals E2.
Proof.
  unfold sum_rationals.
  assert (0 = 0 + 0) as plus00. { rewrite addq0r. reflexivity. }
  elim/big_ind3: _ => // r1 r2 r3 r4 r5 r6.
  intros s321 s654.
  rewrite s321. rewrite s654.
  rewrite <- addqA. rewrite <- addqA.
  assert (r1 + (r5 + r4) = r5 + (r1 + r4)) as eqr.
  2: { rewrite eqr. reflexivity. }
  rewrite addqA. rewrite addqA.
  assert (r1 + r5 = r5 + r1) as eqr'. { apply addqC. }
  rewrite eqr'. reflexivity.
Qed.

Lemma sum_rationals_mult_constant {A : finType} (E : A -> rat) (k : rat) :
  sum_rationals (
    fun a => k * E a
  ) = k * sum_rationals E.
Proof.
  unfold sum_rationals.
  assert (0 = k * 0) as mulk0. { rewrite mulq0r. reflexivity. }
  elim/big_ind2: _ => // r1 r3 r2 r4.
  intro k31. intro k42.
  rewrite k31. rewrite k42.
  rewrite mulq_addr. reflexivity.
Qed.

Lemma sum_rationals_all_null_but_1 {A : finType} (a0 : A) (c : rat) :
  sum_rationals (fun (a : A) => if a == a0 then c else 0) = c.
Proof.
  unfold sum_rationals.
  assert (
    forall a,
      a != a0 ->
      true ->
      (fun (a : A) => if a == a0 then c else 0) a = 0
  ) as null_case.
  {
    intros a ne tru.
    destruct (a == a0).
    { inversion ne. }
    { reflexivity. }
  }
  assert (xpredT a0 = true) as tru. { reflexivity. }
  pose proof (
    @big_only1 rat 0 rationals_Monoid_Law A a0 xpredT (
      fun (a : A) => if a == a0 then c else 0
    ) tru null_case
  ) as sum_only1.
  simpl in sum_only1. rewrite eq_refl in sum_only1.
  exact sum_only1.
Qed.

Lemma sum_rationals_add_to_term {A : finType} (E : A -> rat) (a0 : A) (c : rat) :
  sum_rationals (
    fun a => if a == a0 then E a0 + c else E a
  ) = sum_rationals E + c.
Proof.
  pose proof (sum_rationals_additive E (
    fun a => if a == a0 then c else 0
  )) as sra.
  rewrite sum_rationals_all_null_but_1 in sra.
  rewrite <- sra.
  apply sum_rationals_eq.
  intro a.
  destruct (a == a0) eqn:Eaa0.
  {
    rewrite eq_bool_equivalent in Eaa0. rewrite Eaa0.
    reflexivity.
  }
  { rewrite addq0r. reflexivity. }
Qed.

Lemma sum_rationals_perm {A : finType} (f : A -> rat) (σ : {perm A}) :
  sum_rationals (PermutationsActingOnFunctions f σ) = sum_rationals f.
Proof.
  unfold PermutationsActingOnFunctions. unfold sum_rationals.
  rewrite (
    reindex_inj ( @perm_inj A σ) (F:=f) (P := fun _ => true) (x:=0%Q) (
      op:=rationals_SemiGroup_com_law
    )
  ).
  reflexivity.
Qed.

Close Scope rat_scope.
