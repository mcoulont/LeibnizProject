
From Stdlib Require Import Classical.
Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.Decidable.
From mathcomp Require Import all_algebra all_ssreflect classical_sets boolp.

Require Import relation_facts.
Require Import boolp_facts.
Require Import physical_theories.

Section many_worlds_interpretation.

Context {Time : Type}.
Context {Before : TotalOrder Time}.
Context {State : Type}.
Context {World : Type}.

Definition Indeterminism (pt : @PhysicalTheory Time State) : Type :=
  {
    h1h2t1t2 : ( @History Time State) * ( @History Time State) * Time * Time |
    @instance_indeterminism Time Before State pt (
      fst (fst (fst h1h2t1t2))
    ) (
      snd (fst (fst h1h2t1t2))
    ) (snd (fst h1h2t1t2)) (snd h1h2t1t2)
  }.

Definition get_h1 {pt : @PhysicalTheory Time State} (ind : Indeterminism pt) :
@History Time State :=
  fst (fst (fst (proj1_sig ind))).

Definition get_h2 {pt : @PhysicalTheory Time State} (ind : Indeterminism pt) :
@History Time State :=
  snd (fst (fst (proj1_sig ind))).

Definition get_t1 {pt : @PhysicalTheory Time State} (ind : Indeterminism pt) :
Time :=
  snd (fst (proj1_sig ind)).

Definition get_t2 {pt : @PhysicalTheory Time State} (ind : Indeterminism pt) :
Time :=
  snd (proj1_sig ind).

Definition deterministic_World (pt : @PhysicalTheory Time State) : Type :=
  Indeterminism pt -> bool.

Lemma indeterministic_iff_any_indeterminism (pt : @PhysicalTheory Time State) :
  ~ @is_deterministic Time Before State pt <->
  inhabited (Indeterminism pt).
Proof.
  unfold is_deterministic.
  split.
  {
    intros.
    apply exists_to_inhabited_sig.
    apply not_all_ex_not in H. destruct H as [h1].
    apply not_all_ex_not in H. destruct H as [h2].
    apply imply_to_and in H. destruct H.
    apply imply_to_and in H0. destruct H0.
    apply not_all_ex_not in H1. destruct H1 as [t1].
    apply imply_to_and in H1. destruct H1.
    apply not_all_ex_not in H2. destruct H2 as [t2].
    apply imply_to_and in H2. destruct H2.
    assert ( @instance_indeterminism Time Before State pt h1 h2 t1 t2).
    { unfold instance_indeterminism. tauto. }
    exists ((h1, h2, t1, t2)). simpl. exact H4.
  }
  {
    intros.
    apply inhabited_sig_to_exists in H.
    destruct H as [h1h2t1t2]. unfold instance_indeterminism in H.
    apply ex_not_not_all. exists (h1h2t1t2.1.1.1).
    apply ex_not_not_all. exists (h1h2t1t2.1.1.2).
    intro.
    destruct H. destruct H1. destruct H2. destruct H3.
    specialize (H0 H1 H2 h1h2t1t2.1.2 H3 h1h2t1t2.2 H).
    apply H4. exact H0.
  }
Qed.

Lemma deterministic_iff_no_indeterminism (pt : @PhysicalTheory Time State) :
  @is_deterministic Time Before State pt <->
  ~ inhabited (Indeterminism pt).
Proof.
  pose proof (indeterministic_iff_any_indeterminism pt). tauto.
Qed.

Lemma deterministic_iff_single_word (pt : @PhysicalTheory Time State) :
  @is_deterministic Time Before State pt <->
  forall (w w' : deterministic_World pt), w = w'.
Proof.
  rewrite deterministic_iff_no_indeterminism.
  unfold deterministic_World.
  split.
  {
    intros.
    assert (
      ~ exists (h1h2t1t2 : ( @History Time State) * ( @History Time State) * Time * Time),
      @instance_indeterminism Time Before State pt (
        fst (fst (fst h1h2t1t2))
      ) (
        snd (fst (fst h1h2t1t2))
      ) (snd (fst h1h2t1t2)) (snd h1h2t1t2)
    ).
    { intro. apply exists_to_inhabited_sig in H0. apply H. exact H0. }
    apply functional_extensionality. intro.
    exfalso. apply H. apply inhabits. exact x.
  }
  {
    intros. intro.
    apply inhabited_witness in H0.
    specialize (H (fun _ => true) (fun _ => false)).
    assert (xpredT H0 <> xpred0 H0).
    { intro. inversion H1. }
    rewrite [X in X H0 <> _]H in H1.
    apply H1. reflexivity.
  }
Qed.

Definition many_worlds_extension_PhysicalTheory
(pt : @PhysicalTheory Time State) :
@PhysicalTheory Time (deterministic_World pt -> State) :=
  fun (h' : @History Time (deterministic_World pt -> State)) =>
    if `[< exists (ind : Indeterminism pt) (w : deterministic_World pt),
      (w ind /\ (fun t => h' t w) = get_h2 ind) \/
      (~ w ind /\ (fun t => h' t w) = get_h1 ind)
    >] then False else (
      forall (w : deterministic_World pt), pt (fun t => h' t w)
    ).

Lemma deterministic_many_worlds_interpretation
(pt : @PhysicalTheory Time State) :
  @is_deterministic Time Before (deterministic_World pt -> State) (
    many_worlds_extension_PhysicalTheory pt
  ).
Proof.
  unfold is_deterministic. unfold many_worlds_extension_PhysicalTheory.
  unfold satisfies. unfold deterministic_World.
  intros.
  destruct (
  `[< exists (ind : Indeterminism pt) (w : Indeterminism pt -> bool),
    w ind /\ h1^~ w = get_h2 ind \/ ~ w ind /\ h1^~ w = get_h1 ind >]
  ) eqn:dstrH1.
  { inversion H. }
  apply false_to_False in dstrH1.
  pose proof (not_ex_all_not (Indeterminism pt) (
    fun (ind : Indeterminism pt) =>
    exists (w : Indeterminism pt -> bool),
      w ind /\ h1^~ w = get_h2 ind \/ ~ w ind /\ h1^~ w = get_h1 ind
  ) dstrH1).
  simpl in H3.
  destruct (
  `[< exists (ind : Indeterminism pt) (w : Indeterminism pt -> bool),
    w ind /\ h2^~ w = get_h2 ind \/ ~ w ind /\ h2^~ w = get_h1 ind >]
  ) eqn:dstrH2.
  { inversion H0. }
  apply false_to_False in dstrH2.
  pose proof (not_ex_all_not (Indeterminism pt) (
    fun (ind : Indeterminism pt) =>
    exists (w : Indeterminism pt -> bool),
      w ind /\ h2^~ w = get_h2 ind \/ ~ w ind /\ h2^~ w = get_h1 ind
  ) dstrH2).
  simpl in H4.
  rewrite <- notP. intro Hndet.
  pose proof (functional_extensionality (h1 t) (h2 t)).
  rewrite <- contrapositive in H5.
  2: { unfold Decidable.decidable. tauto. }
  specialize (H5 Hndet). apply not_all_ex_not in H5.
  destruct H5 as [w Hneq].
  apply equal_f with (x:=w) in H1.
  assert ( @instance_indeterminism Time Before State pt (h1^~ w) (h2^~ w) t0 t).
  {
    unfold instance_indeterminism.
    split.
    { exact H2. }
    split.
    { apply H. }
    split.
    { apply H0. }
    split.
    { rewrite H1. reflexivity. }
    { exact Hneq. }
  }
  set (
    ind := exist ( fun h1h2t1t2 =>
      @instance_indeterminism Time Before State pt (
        fst (fst (fst h1h2t1t2))
      ) (
        snd (fst (fst h1h2t1t2))
      ) (snd (fst h1h2t1t2)) (snd h1h2t1t2)
    ) (((h1^~ w), (h2^~ w), t0, t)) H5
  ).
  specialize (H3 ind). specialize (H4 ind).
  pose proof (not_ex_all_not (Indeterminism pt -> bool) (
    fun (w : Indeterminism pt -> bool) =>
      w ind /\ h1^~ w = get_h2 ind \/ ~ w ind /\ h1^~ w = get_h1 ind
  ) H3).
  simpl in H6. specialize (H6 w).
  pose proof (not_ex_all_not (Indeterminism pt -> bool) (
    fun (w : Indeterminism pt -> bool) =>
      w ind /\ h2^~ w = get_h2 ind \/ ~ w ind /\ h2^~ w = get_h1 ind
  ) H4).
  simpl in H7. specialize (H7 w).
  tauto.
Qed.

(* Definition restriction_State {World : Type} (state' : World * State) : State :=
  snd state'.

Definition extension_State {World : Type} (w_def : World) (state : State) :
World * State :=
  (w_def, state).

Definition restriction_extension_State {World : Type}
(w_def : World) (state : State) :
  restriction_State (extension_State w_def state) = state.
Proof.
  unfold restriction_State. unfold extension_State.
  reflexivity.
Qed.

Definition restriction_History {World : Type} (h' : @History Time (World * State)) :
@History Time State :=
  fun (t : Time) => restriction_State (h' t).

Definition extension_History {World : Type} (w_def : World)
(h : @History Time State) :
@History Time (World * State) :=
  fun (t : Time) => extension_State w_def (h t).

Definition restriction_extension_History {World : Type}
(w_def : World) (h : @History Time State) :
  restriction_History (extension_History w_def h) = h.
Proof.
  unfold restriction_History. unfold extension_History.
  reflexivity.
Qed.

Definition extension_PhysicalTheory (World : Type)
(pt : @PhysicalTheory Time State) :
@PhysicalTheory Time (World * State) :=
  fun (h' : @History Time (World * State)) =>
    pt (restriction_History h').

Lemma satisfiability_stable_by_extension {World : Type}
(pt : @PhysicalTheory Time State) (h' : @History Time (World * State)) :
  satisfies (restriction_History h') pt <->
  satisfies h' (extension_PhysicalTheory World pt).
Proof.
  unfold extension_PhysicalTheory.
  split; intro Hsat; exact Hsat.
Qed.

Proposition State_extension_does_not_bring_determinism {World : Type}
(_: World) (pt : @PhysicalTheory Time State) :
  (* @is_deterministic Time Before (World * State) (extension_PhysicalTheory A pt) <->
  @is_deterministic Time Before State pt. *)
  ~ @is_deterministic Time Before State pt ->
  ~ @is_deterministic Time Before (World * State) (
    extension_PhysicalTheory World pt
  ).
Proof.
  rewrite contrapositive.
  {
    unfold is_deterministic.
    intros.
    specialize (H (extension_History X h1) (extension_History X h2)).
    rewrite <- (satisfiability_stable_by_extension pt) in H.
    rewrite <- (satisfiability_stable_by_extension pt) in H.
    rewrite restriction_extension_History in H.
    rewrite restriction_extension_History in H.
    specialize (H H0 H1 t0).
    unfold extension_History in H. unfold extension_State in H.
    rewrite H2 in H.
    assert ((X, h2 t0) = (X, h2 t0)). { reflexivity. }
    specialize (H H4 t H3).
    injection H. tauto.
  }
  { unfold Decidable.decidable. tauto. }
Qed. *)

(* Definition removes_indeterminism {World : Type}
(pt : @PhysicalTheory Time State)
(h1' h2' : @History Time (World * State)) (t1 t2 : Time) : Prop :=
  @instance_indeterminism Time Before State pt (
    restriction_History h1'
  ) (
    restriction_History h2'
  ) t1 t2 /\
  h1' t1 <> h2' t1.

Lemma indeterminism_removal {pt : @PhysicalTheory Time State}
{h1 h2 : @History Time State} {t1 t2 : Time}
(ci : @instance_indeterminism Time Before State pt h1 h2 t1 t2) :
  removes_indeterminism pt (
    extension_History true h1
  ) (
    extension_History false h2
  ) t1 t2.
Proof.
  unfold removes_indeterminism.
  split.
  {
    unfold instance_indeterminism. unfold instance_indeterminism in ci.
    rewrite restriction_extension_History.
    rewrite restriction_extension_History.
    exact ci.
  }
  {
    unfold extension_History. unfold extension_State.
    intro. inversion H.
  }
Qed.

Definition Indeterminism (pt : @PhysicalTheory Time State) : Type :=
  {
    h1h2t1t2 : ( @History Time State) * ( @History Time State) * Time * Time |
    @instance_indeterminism Time Before State pt (
      fst (fst (fst h1h2t1t2))
    ) (
      snd (fst (fst h1h2t1t2))
    ) (snd (fst h1h2t1t2)) (snd h1h2t1t2)
  }.

Definition deterministic_extension_State (pt : @PhysicalTheory Time State) :
Type :=
  State * forall (i : Indeterminism pt), bool.

Definition deterministic_extension_History
(pt : @PhysicalTheory Time State) (h : @History Time State) :
@History Time (deterministic_extension_State pt) :=
  fun (t : Time) => (h t, fun (i : Indeterminism pt) =>
    if `[< h = fst (fst (fst (proj1_sig i))) >] then true else false
  ).

Definition deterministic_extension_PhysicalTheory
(pt : @PhysicalTheory Time State) :
@PhysicalTheory Time (deterministic_extension_State pt) :=
  fun (h' : @History Time (deterministic_extension_State pt)) =>
    pt (restriction_History h').

Lemma physical_theory_decidable_with_State_extension
(pt : @PhysicalTheory Time State) :
  @is_deterministic Time Before (deterministic_extension_State pt) (
    deterministic_extension_PhysicalTheory pt
  ).
Proof.
  unfold deterministic_extension_PhysicalTheory.
  unfold is_deterministic. unfold restriction_History.
  unfold restriction_State. unfold satisfies.
  intros.
  Set Printing Implicit.
  unfold deterministic_extension_State in h1.
  unfold deterministic_extension_State in h2.

Proposition physical_theory_decidable_with_State_extension
{pt : @PhysicalTheory Time State}
(count : countable {
  h1h2t1t2 : ( @History Time State) * ( @History Time State) * Time * Time |
  @instance_indeterminism Time Before State pt (fst (fst (fst h1h2t1t2))) (
    snd (fst (fst h1h2t1t2))
  ) (snd (fst h1h2t1t2)) (snd h1h2t1t2)
}) :
  exists (World : Type), @is_deterministic Time Before (World * State) (
    extension_PhysicalTheory A pt
  ).
Proof.
  unfold countable in count. unfold not_bigger_than in count.
  destruct count as [enum count]. *)

(* (*
  Below an additional hypothesis is done compared to the mathematical proof:
  the type/set of states is in the form A -> B.

  This is because, if State is just supposed to be any Type/Set,
  the natural expression of an extension from State to some State' is
  via a product State' = World * State for some A
  (one must be able to define the restriction of a history and
  the extension of a physical theory)
  Then, in order to apply Zorn's lemma, one needs an order relation,
  but as one can't prove A*B <> A
  (see https://proofassistants.stackexchange.com/questions/5316/discriminate-the-cartesian-product-in-rocq),
  we don't have antisymmetry of the relation.

  The fact that A*B <> A is trivial in usual mathematics (that is in ZF),
  so it is quite frustrating not to be able to prove it in Rocq.

  Maybe could one deny the univalence axiom and use another axiom to force
  some "ZF vision" of types/sets ?

  If you have a clue how to improve this, please open an issue at
  https://github.com/mcoulont/LeibnizProject/issues/new
*)

Context {Time : Type}.
Context {Before : TotalOrder Time}.
Context {LocalState : Type}.

Definition State_as_function (Location LocalState : Type) : Type :=
  Location -> LocalState.

Definition restriction_State {Location Location' : Type}
{injLL' : Location -> Location'} (_ : injective injLL')
(state' : @State_as_function Location' LocalState) :
@State_as_function Location LocalState :=
  fun (loc : Location) => state' (injLL' loc).

Definition extension_State {Location Location' : Type}
{f : Location -> Location'} (_ : injective f)
(ls_def : LocalState)
(state : @State_as_function Location LocalState) :
@State_as_function Location' LocalState :=
  fun (loc' : Location') => match antecedent f loc' with
  | None => ls_def
  | Some loc => state loc
  end.

Definition restriction_History {Location Location' : Type}
{f : Location -> Location'} (injLL' : injective f)
(h' : @History Time (Location' -> LocalState)) :
@History Time (Location -> LocalState) :=
  fun (t : Time) => restriction_State injLL' (h' t).

Definition extension_History {Location Location' : Type}
{f : Location -> Location'} (_ : injective f)
(ls_def : LocalState)
(h : @History Time (Location -> LocalState)) :
@History Time (Location' -> LocalState) :=
  fun (t : Time) => fun (loc' : Location') =>
    match antecedent f loc' with
    | None => ls_def
    | Some loc => h t loc
    end.

Lemma restriction_extension_History {Location1 Location2 Location3 : Type}
{f12 : Location1 -> Location2} {f23 : Location2 -> Location3}
(inj12 : injective f12) (inj23 : injective f23)
(ls_def : LocalState)
(h2 : @History Time (Location2 -> LocalState)) :
  restriction_History (inj_comp inj23 inj12) (
    extension_History inj23 ls_def h2
  ) = restriction_History inj12 h2.
Proof.
  unfold extension_History. unfold restriction_History.
  unfold restriction_State.
  apply functional_extensionality. intro.
  apply functional_extensionality. intro.
  destruct (antecedent f23 ((f23 \o f12) x0)) eqn:ant.
  {
    apply antecedent_exists in ant. unfold comp in ant.
    apply inj23 in ant.
    rewrite ant. reflexivity.
  }
  {
    apply antecedent_not_exists with (a:= f12 x0) in ant.
    unfold comp in ant.
    exfalso. apply ant. reflexivity.
  }
Qed.

Definition extension_PhysicalTheory {Location Location' : Type}
{f : Location -> Location'} (inj : injective f)
(pt : @PhysicalTheory Time (Location -> LocalState)) :
@PhysicalTheory Time (Location' -> LocalState) :=
  fun (h' : @History Time (Location' -> LocalState)) =>
    pt (restriction_History inj h').

Lemma satisfiability_stable_by_extension {Location Location' : Type}
{f : Location -> Location'} (inj : injective f)
(pt : @PhysicalTheory Time (Location -> LocalState))
(h' : @History Time (Location' -> LocalState)) :
  satisfies (restriction_History inj h') pt <->
  satisfies h' (extension_PhysicalTheory inj pt).
Proof.
  split; intro Hsatisfies.
  - unfold extension_PhysicalTheory.
    exact Hsatisfies.
  - unfold extension_PhysicalTheory in Hsatisfies.
    exact Hsatisfies.
Qed.

Definition removes_indeterminism {Location Location' : Type}
{f : Location -> Location'} (inj : injective f)
(pt : @PhysicalTheory Time (Location -> LocalState))
(h1' h2' : @History Time (Location' -> LocalState)) (t1 t2 : Time) : Prop :=
  @case_indeterminism Time Before (
    Location -> LocalState
  ) pt (restriction_History inj h1') (restriction_History inj h2') t1 t2 /\
  h1' t1 <> h2' t1.

Definition remove_some_indeterminism (Location Location' : Type)
(pt : @PhysicalTheory Time (Location -> LocalState)) :
Prop :=
  exists (f : Location -> Location') (inj : injective f)
  (h1' h2' : @History Time (Location' -> LocalState)) (t1 t2 : Time),
    removes_indeterminism inj pt h1' h2' t1 t2.

Definition ExtensionRemovingIndeterminism {Location : Type}
(pt : @PhysicalTheory Time (Location -> LocalState)) :
Type :=
  {Location' | remove_some_indeterminism Location Location' pt}.

Definition smaller_ExtensionRemovingIndeterminism {Location : Type}
(pt : @PhysicalTheory Time (Location -> LocalState)) :
relation (ExtensionRemovingIndeterminism pt) :=
  fun eri1 eri2 =>
    smaller_than (proj1_sig eri1) (proj1_sig eri2).

Lemma smaller_ExtensionRemovingIndeterminism_transitive
{Location : Type} (pt : @PhysicalTheory Time (Location -> LocalState)) :
  Relation_Definitions.transitive (
    ExtensionRemovingIndeterminism pt
  ) (
    smaller_ExtensionRemovingIndeterminism pt
  ).
Proof.
  unfold smaller_ExtensionRemovingIndeterminism.
  unfold Relation_Definitions.transitive.
  intros.
  apply smaller_than_transitive with (y:= proj1_sig y); tauto.
Qed.

Lemma smaller_ExtensionRemovingIndeterminism_assymmetric
{Location : Type} (pt : @PhysicalTheory Time (Location -> LocalState)) :
  assymmetric (smaller_ExtensionRemovingIndeterminism pt).
Proof.
  unfold smaller_ExtensionRemovingIndeterminism.
  unfold assymmetric.
  intros.
  apply smaller_than_assymmetric; tauto.
Qed.

Lemma smaller_ExtensionRemovingIndeterminism_irreflexive
{Location : Type} (pt : @PhysicalTheory Time (Location -> LocalState)) :
  relation_facts.irreflexive (smaller_ExtensionRemovingIndeterminism pt).
Proof.
  unfold smaller_ExtensionRemovingIndeterminism.
  unfold irreflexive.
  intros.
  apply smaller_than_irreflexive; tauto.
Qed.

Definition not_bigger_ExtensionRemovingIndeterminism
{Location : Type} (pt : @PhysicalTheory Time (Location -> LocalState)) :
relation (ExtensionRemovingIndeterminism pt) :=
  clos_refl (ExtensionRemovingIndeterminism pt)
    (smaller_ExtensionRemovingIndeterminism pt).

Lemma not_bigger_ExtensionRemovingIndeterminism_transitive
{Location : Type} (pt : @PhysicalTheory Time (Location -> LocalState)) :
  Relation_Definitions.transitive (
    ExtensionRemovingIndeterminism pt
  ) (
    not_bigger_ExtensionRemovingIndeterminism pt
  ).
Proof.
  unfold not_bigger_ExtensionRemovingIndeterminism.
  unfold Relation_Definitions.transitive.
  intros.
  induction H.
  induction H0.
  {
    apply r_step.
    pose proof (
      smaller_ExtensionRemovingIndeterminism_transitive pt
    ).
    unfold Relation_Definitions.transitive in H1.
    apply H1 with (y := y); tauto.
  }
  { apply r_step. exact H. }
  { exact H0. }
Qed.

Lemma not_bigger_ExtensionRemovingIndeterminism_antisymmetric
{Location : Type} (pt : @PhysicalTheory Time (Location -> LocalState)) :
  Relation_Definitions.antisymmetric (
    ExtensionRemovingIndeterminism pt
  ) (
    not_bigger_ExtensionRemovingIndeterminism pt
  ).
Proof.
  unfold not_bigger_ExtensionRemovingIndeterminism.
  unfold Relation_Definitions.antisymmetric.
  intros.
  induction H.
  induction H0.
  {
    pose proof (
      smaller_ExtensionRemovingIndeterminism_assymmetric pt
    ).
    unfold assymmetric in H1. specialize (H1 y0 y).
    tauto.
  }
  {
    pose proof (
      smaller_ExtensionRemovingIndeterminism_irreflexive pt
    ).
    unfold irreflexive in H0. specialize (H0 y).
    tauto.
  }
  { reflexivity. }
Qed.

Inductive generalized_sum {Location : Type}
{pt : @PhysicalTheory Time (Location -> LocalState)}
(set_ERI : set (ExtensionRemovingIndeterminism pt)) : Type :=
  | gsum {eri : ExtensionRemovingIndeterminism pt} (_ : set_ERI eri) :
    proj1_sig eri -> generalized_sum set_ERI.

Definition generalized_sum_inclusion {Location : Type}
{pt : @PhysicalTheory Time (Location -> LocalState)}
{set_ERI : set (ExtensionRemovingIndeterminism pt)}
{eri : ExtensionRemovingIndeterminism pt} (eri_type : set_ERI eri) :
proj1_sig eri -> generalized_sum set_ERI :=
  gsum set_ERI eri_type.

Lemma generalized_sum_inclusion_injective {Location : Type}
{pt : @PhysicalTheory Time (Location -> LocalState)}
{set_ERI : set (ExtensionRemovingIndeterminism pt)}
{eri : ExtensionRemovingIndeterminism pt} (eri_type : set_ERI eri) :
  injective (generalized_sum_inclusion eri_type).
Proof.
  unfold injective.
  intros Location1 Location2 Hgsum.
  unfold generalized_sum_inclusion in Hgsum.
  injection Hgsum. intros.
  apply inj_pair2. exact H.
Qed.

Corollary not_bigger_than_generalized_sum_inclusion {Location : Type}
{pt : @PhysicalTheory Time (Location -> LocalState)}
{set_ERI : set (ExtensionRemovingIndeterminism pt)}
{eri : ExtensionRemovingIndeterminism pt} (_ : set_ERI eri) :
  not_bigger_than (proj1_sig eri)
    (generalized_sum set_ERI).
Proof.
  exists (generalized_sum_inclusion H).
  apply generalized_sum_inclusion_injective; tauto.
Qed.

Definition extension_History_generalized_sum {Location : Type}
{pt : @PhysicalTheory Time (Location -> LocalState)}
{set_ERI : set (ExtensionRemovingIndeterminism pt)}
{eri : ExtensionRemovingIndeterminism pt} (eri_type : set_ERI eri)
(ls_def : LocalState)
(h : @History Time (proj1_sig eri -> LocalState)) :
@History Time (generalized_sum set_ERI -> LocalState) :=
  extension_History (
    generalized_sum_inclusion_injective eri_type
  ) ls_def h.

Set Printing Universes.

Lemma generalized_sum_removes_some_indeterminism {Location : Type}
{pt : @PhysicalTheory Time (Location -> LocalState)}
{set_ERI : set (ExtensionRemovingIndeterminism pt)}
{eri : ExtensionRemovingIndeterminism pt} (eri_type : set_ERI eri)
(ls_def : LocalState) :
  remove_some_indeterminism Location (
    generalized_sum set_ERI
  ) pt.
Proof.
  destruct eri as [Location' Heri].
  unfold remove_some_indeterminism. unfold remove_some_indeterminism in Heri.
  destruct Heri as [iLL' Heri]. destruct Heri as [injLL' Heri].
  destruct Heri as [h1' [h2' Heri]]. destruct Heri as [t1 [t2 riLL']].
  pose proof (not_bigger_than_generalized_sum_inclusion eri_type).
  unfold not_bigger_than in H. destruct H as [iL'GS injL'GS].
  exists (iL'GS \o iLL').
  pose proof (inj_comp injL'GS injLL'). exists H.
  exists (extension_History injL'GS ls_def h1').
  exists (extension_History injL'GS ls_def h2').
  exists t1. exists t2.
  unfold removes_indeterminism. unfold removes_indeterminism in riLL'.
  destruct riLL' as [ciLL' h12].
  unfold case_indeterminism. unfold case_indeterminism in ciLL'.
  destruct ciLL' as [bt1t2 ciLL']. destruct ciLL' as [sat1 ciLL'].
  destruct ciLL' as [sat2 ciLL']. destruct ciLL' as [rHt1 rHt2].
  assert (
    forall h',
    restriction_History H (extension_History injL'GS ls_def h') =
    restriction_History injLL' h'
  ).
  {
    intro.
    pose proof (restriction_extension_History injLL' injL'GS ls_def h').
    assert (inj_comp (f:=iL'GS) (h:=iLL') injL'GS injLL' = H).
    { apply proof_irrelevance. }
    rewrite H1 in H0. rewrite H0.
    reflexivity.
  }
  split.
  {
    split.
    { exact bt1t2. }
    split.
    { rewrite (H0 h1'). exact sat1. }
    split.
    { rewrite (H0 h2'). exact sat2. }
    split.
    { rewrite (H0 h1'). rewrite (H0 h2'). exact rHt1. }
    { rewrite (H0 h1'). rewrite (H0 h2'). exact rHt2. }
  }
  {
    intro. apply h12.
    apply functional_extensionality. intro.
    assert (
      extension_History injL'GS ls_def h1' t1 (iL'GS x) =
      extension_History injL'GS ls_def h2' t1 (iL'GS x)
    ).
    { rewrite H1. reflexivity. }
    unfold extension_History in H2.
    rewrite (inj_implies_antecedent_unique injL'GS x) in H2.
    exact H2.
  }
Qed.

Set Universe Polymorphism.

Definition generalized_sum_ExtensionRemovingIndeterminism {Location : Type}
{pt : @PhysicalTheory Time (Location -> LocalState)}
{set_ERI : set (ExtensionRemovingIndeterminism pt)}
{eri : ExtensionRemovingIndeterminism pt} (eri_type : set_ERI eri)
(ls_def : LocalState) :
ExtensionRemovingIndeterminism pt :=
  exist (
    fun (T : Type) => remove_some_indeterminism Location T pt
  ) (generalized_sum set_ERI) (
    generalized_sum_removes_some_indeterminism eri_type ls_def
  ).

Lemma not_bigger_ExtensionRemovingIndeterminism_chain_has_upper_bound
{Location : Type} (pt : @PhysicalTheory Time (Location -> LocalState))
(chain : set (ExtensionRemovingIndeterminism pt)) :
  total_on chain (
    not_bigger_ExtensionRemovingIndeterminism pt
  ) ->
  exists (L_ub : ExtensionRemovingIndeterminism pt),
  forall L, chain L -> 
    not_bigger_ExtensionRemovingIndeterminism pt L L_ub.
Proof.
  intros Htot.
  Search sum.
  unfold total_on in Htot.
Qed. *)

End many_worlds_interpretation.
