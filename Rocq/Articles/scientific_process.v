
Require Import relation_facts.
Require Import occam_razor.

Section scientific_process.

Context {TimePerception : Type}.
Context {SpacePerception : Type}.
Context {Action : Type}.
Context {Before : TotalOrder TimePerception}.
Context {SimplerThan : TotalOrder (
  @ScientificTheory TimePerception (SpacePerception * Action)
)}.

Definition brought_insight {t1 t2 : TimePerception} (bef : non_strict Before t1 t2)
(h2 : @HistoryUntil TimePerception (SpacePerception * Action) Before t2) : Prop :=
  forall (st1 st2 : @ScientificTheory TimePerception (SpacePerception * Action)),
    @occam_preferred TimePerception (SpacePerception * Action) Before SimplerThan t1 (
      @HistoryUntil_restriction TimePerception (SpacePerception * Action) Before
      t1 t2 bef h2
    ) st1 ->
    @occam_preferred TimePerception (
      SpacePerception * Action
    ) Before SimplerThan t2 h2 st2 ->
    strict SimplerThan st1 st2.

End scientific_process.
