
Require Import ssr.ssrbool.

Require Import preference.
Require Import relation_facts.

Section occam_razor.

Context {Time : Type}.
Context {State : Type}.
Context {Before : TotalOrder Time}.

Definition History : Type := Time -> State.

Definition HistoryUntil (t0 : Time) : Type :=
  { t : Time | non_strict Before t t0 } -> State.

Definition HistoryBefore (t0 : Time) : Type :=
  { t : Time | strict Before t t0 } -> State.

Definition extends {t0 : Time} (h : History) (hu : HistoryUntil t0) : Prop :=
  forall (t : { t : Time | non_strict Before t t0 }),
    non_strict Before (proj1_sig t) t0 -> h (proj1_sig t) = hu t.

Definition HistoryUntil_restriction {t1 t2 : Time}
(le : non_strict Before t1 t2) (h2 : HistoryUntil t2) : HistoryUntil t1.
Proof.
  unfold HistoryUntil in *.
  intros [t Ht].
  apply h2.
  apply exist with (x:=t).
  unfold TotalOrder in Before. destruct Before. (*unfold non_strict in *.*)
  unfold total_order in *.
  simpl in le. simpl in Ht. simpl.
  destruct t0. destruct o.
  unfold Relation_Definitions.transitive in ord_trans.
  apply ord_trans with (y:=t1); tauto.
Defined.

Definition Event : Type := pred History.

Definition happens_in (e : Event) (h : History) : Prop :=
  e h = true.

Definition ScientificTheory : Type := History -> Prop.

Definition satisfies (h : History) (st : ScientificTheory) : Prop := st h.

Definition satisfies_until {t0 : Time} (h0 : HistoryUntil t0)
(st : ScientificTheory) : Prop :=
  exists (h : History), st h /\ extends h h0.

Definition more_precise (st1 st2 : ScientificTheory) : Prop :=
  forall (h : History), st2 h -> st1 h.

Context {SimplerThan : TotalOrder ScientificTheory}.

Definition occam_preferred {t0 : Time} (h0 : HistoryUntil t0)
(st : ScientificTheory) : Prop :=
  satisfies_until h0 st /\
  forall (st2 : ScientificTheory),
    satisfies_until h0 st2 ->
    non_strict SimplerThan st st2.

End occam_razor.
