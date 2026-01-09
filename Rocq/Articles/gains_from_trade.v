
Require Import Corelib.Init.Nat.
Require Import Logic.FunctionalExtensionality.
Require Import Logic.ClassicalEpsilon.
Require Import Classical.
Require Import PeanoNat.
Require Import Arith.Compare.
Require Import Logic.IndefiniteDescription.
Require Import Logic.Classical_Pred_Type.
Require Import Logic.ProofIrrelevance.
Require Import Reals.RIneq.
Require Import Reals.
From mathcomp Require Import all_ssreflect fintype.
From mathcomp.algebra Require Import vector.
From mathcomp.classical Require Import boolp.

Require Import nat_facts.
Require Import eqType_facts.
Require Import finType_facts.
Require Import reals_facts.
Require Import ssrnat_facts.
Require Import boolp_facts.
Require Import bigop_facts.
Require Import ethics_in_society.

Section gains_from_trade.

Context {Commodity : eqType}.
Context {Entity : finType}.

Open Scope R_scope.

Definition Quantity : Type := nonnegreal.

Definition WorkProduct : Type := Commodity -> Quantity.

Definition unproductive : WorkProduct :=
  fun _ => zero_nonnegreal.

Definition at_least_as_productive (wp wp' : WorkProduct) :
Prop :=
  forall (c : Commodity), (nonneg (wp' c)) <= (nonneg (wp c)).

Definition possible_targeted_production (doable : WorkProduct -> Prop)
(c : Commodity) (q : Quantity) : Prop :=
  exists (wp : WorkProduct), doable wp /\ wp c = q.

Definition finite_production (doable : WorkProduct -> Prop) : Prop :=
  forall (c : Commodity), bound_nonneg (possible_targeted_production doable c).

Definition production_decreasable_at_will (doable : WorkProduct -> Prop) : Prop :=
  forall (wp wp' : WorkProduct),
    at_least_as_productive wp wp' ->
    doable wp ->
    doable wp'.

Definition is_capacity (doable : WorkProduct -> Prop) : Prop :=
  doable unproductive /\
  finite_production doable /\
  production_decreasable_at_will doable.

Definition Capacity : Type :=
  {doable : WorkProduct -> Prop | is_capacity doable}.

Lemma unproductive_in_capacity (cap : Capacity) :
  sval cap unproductive.
Proof.
  destruct cap as [doable is_cap].
  unfold is_capacity in is_cap.
  destruct is_cap as [doa is_cap].
  simpl. exact doa.
Qed.

Lemma capacity_is_finite (cap : Capacity) :
  finite_production (sval cap).
Proof.
  destruct cap as [doable is_cap].
  unfold is_capacity in is_cap.
  destruct is_cap as [doa is_cap]. destruct is_cap as [fin dec].
  simpl. exact fin.
Qed.

Lemma targeted_capacity_is_finite (cap : Capacity) (other_qties : WorkProduct)
(c : Commodity) :
  bound_nonneg (fun q => sval cap (replace other_qties c q)).
Proof.
  pose proof (capacity_is_finite cap) as finp. unfold finite_production in finp.
  specialize (finp c). unfold possible_targeted_production in finp.
  unfold bound_nonneg in *.
  destruct finp as [lub ub]. exists lub.
  unfold is_upper_bound_nonneg in *.
  intros q in_cap.
  apply ub.
  exists (replace other_qties c q).
  split.
  - exact in_cap.
  - rewrite replace_changes. reflexivity.
Qed.

Lemma possible_targeted_production_0 {doable : WorkProduct -> Prop}
(c : Commodity) (do_un : doable unproductive) :
  exists (q : Quantity), possible_targeted_production doable c q.
Proof.
  unfold possible_targeted_production.
  exists zero_nonnegreal. exists unproductive.
  split.
  { exact do_un. }
  { reflexivity. }
Qed.

Lemma who_can_do_more_can_do_less {wp wp' : WorkProduct} {cap : Capacity}
(cap_wp : sval cap wp) (wp_le : at_least_as_productive wp wp') :
  sval cap wp'.
Proof.
  pose proof (proj2_sig cap). simpl in H.
  unfold is_capacity in H. destruct H. destruct H0.
  specialize (H1 wp wp').
  apply H1; tauto.
Qed.

Definition unanimously_unproductive : @Profile Entity WorkProduct :=
  fun _ => unproductive.

Definition in_capacity (work : @Profile Entity WorkProduct)
(pf_cap : @Profile Entity Capacity) :
Prop :=
  forall (e : Entity), sval (pf_cap e) (work e).

Definition total_production (work : @Profile Entity WorkProduct)
(c : Commodity) : Quantity :=
  sum_nonnegreals (fun e => work e c).

Lemma no_one_does_anything_gives_no_production :
  total_production (fun _ => unproductive) = unproductive.
Proof.
  unfold total_production. unfold unproductive.
  simpl.
  apply functional_extensionality. intro.
  assert (sum0 : sum_reals (fun=> 0) = 0) by apply (sum_reals_0 Entity).
  apply (equal_nonneg_if_equal_reals sum0 (
    cond_nonneg (sum_nonnegreals (fun=> {| nonneg:=0 ; cond_nonneg:= Rle_refl 0 |}))
  ) (Rle_refl 0)).
Qed.

Lemma who_can_do_more_can_do_less_global {work work' : @Profile Entity WorkProduct}
{pf_cap : @Profile Entity Capacity} (incap : in_capacity work pf_cap)
(alap : forall (e : Entity), at_least_as_productive (work e) (work' e)) :
  in_capacity work pf_cap ->
  in_capacity work' pf_cap.
Proof.
  unfold in_capacity. intros.
  specialize (H e). specialize (alap e).
  apply (who_can_do_more_can_do_less H alap).
Qed.

Definition in_total_capacity (pf_cap : @Profile Entity Capacity)
(wp : WorkProduct) :
Prop :=
  exists (work : @Profile Entity WorkProduct),
    in_capacity work pf_cap /\
    total_production work = wp.

Definition efficient (cap : Capacity) (wp : WorkProduct) : Prop :=
  sval cap wp /\
  forall (wp' : WorkProduct), (
    sval cap wp' ->
    (exists (c : Commodity), (nonneg (wp c)) < (nonneg (wp' c))) ->
    (exists (c : Commodity), (nonneg (wp' c)) < (nonneg (wp c)))
  ).

Definition least_upper_bound_possible_qty {cap : Capacity} {c : Commodity}
{other_qties : WorkProduct}
(in_cap : exists q : Quantity, sval cap (replace other_qties c q)) :
  Quantity.
Proof.
  pose proof (completeness_nonneg (
    targeted_capacity_is_finite cap other_qties c
  )) as lub_thm.
  simpl in lub_thm.
  specialize (lub_thm in_cap).
  exact (sval lub_thm).
Defined.

Lemma least_upper_bound_possible_qty_is_upper_bound {cap : Capacity}
{c : Commodity} {other_qties : WorkProduct} {q : Quantity}
{in_cap : exists q : Quantity, sval cap (replace other_qties c q)}
(lt_lub : least_upper_bound_possible_qty in_cap < q) :
  ~ sval cap (replace other_qties c q).
Proof.
  intro capq.
  pose proof (proj2_sig (completeness_nonneg (
    targeted_capacity_is_finite cap other_qties c
  ) in_cap)) as lub_pty.
  simpl in lub_pty.
  unfold is_lub_nonneg in lub_pty.
  destruct lub_pty as [ub lub_least].
  unfold is_upper_bound_nonneg in ub. specialize (ub q capq).
  unfold least_upper_bound_possible_qty in lt_lub.
  pose proof (Rle_lt_trans q (
    sval (completeness_nonneg (targeted_capacity_is_finite cap other_qties c) in_cap)
  ) q ub lt_lub) as cont.
  apply (Rlt_irrefl q). exact cont.
Qed.

Definition finite_precision_possible_qty {cap : Capacity} {c : Commodity}
{other_qties : WorkProduct}
(in_cap : exists q : Quantity, sval cap (replace other_qties c q)) :
Prop :=
  sval cap (replace other_qties c (least_upper_bound_possible_qty in_cap)).

Definition barter {i j : Entity} {c1 c2 : Commodity} {q1 q2 : Quantity}
{repartition : @Profile Entity WorkProduct}
(enough_i : q1 <= repartition i c1) (enough_j : q2 <= repartition j c2) :
@Profile Entity WorkProduct :=
  fun e : Entity => fun c : Commodity =>
    if e == i then (
      if c == c1 then {|
        nonneg := repartition i c1 - q1 ;
        cond_nonneg := Rle_implies_minus_nonneg enough_i
      |}
      else if c == c2 then plus_nonneg (repartition i c2) q2
      else repartition i c
    ) else if e == j then (
      if c == c2 then {|
        nonneg := repartition j c2 - q2 ;
        cond_nonneg := Rle_implies_minus_nonneg enough_j
      |}
      else if c == c1 then plus_nonneg (repartition j c1) q1
      else repartition j c
    ) else repartition e c.

Definition barter_tr {i j : Entity} {c1 c2 : Commodity}
(neij : j <> i) (nec : c2 <> c1) (q1 q2 : Quantity)
(repartition : @Profile Entity WorkProduct) :
  @Profile Entity WorkProduct.
Proof.
  assert ({q1 <= repartition i c1} + {~ q1 <= repartition i c1}) as taut1.
  { apply excluded_middle_informative. }
  assert ({q2 <= repartition j c2} + {~ q2 <= repartition j c2}) as taut2.
  { apply excluded_middle_informative. }
  destruct taut1 as [le1|nle1].
  2: { exact repartition. }
  destruct taut2 as [le2|nle2].
  2: { exact repartition. }
  exact (barter le1 le2).
Defined.

Definition preserves_total_production
(tr : @Profile Entity WorkProduct -> @Profile Entity WorkProduct) :
Prop :=
  forall (repartition : @Profile Entity WorkProduct),
    total_production repartition = total_production (tr repartition).

Definition AggregateTransaction : Type :=
  {
    tr : @Profile Entity WorkProduct -> @Profile Entity WorkProduct |
    preserves_total_production tr
  }.

Definition no_transaction : AggregateTransaction.
Proof.
  assert (preserves_total_production id) as ptp.
  { unfold preserves_total_production. reflexivity. }
  exact (exist preserves_total_production id ptp).
Defined.

Lemma barter_preserves_total_production {i j : Entity} {c1 c2 : Commodity}
(neij : j <> i) (nec : c2 <> c1)
(q1 q2 : Quantity) (repartition : @Profile Entity WorkProduct) :
  preserves_total_production (barter_tr neij nec q1 q2).
Proof.
  unfold preserves_total_production. intro work.
  unfold total_production.
  apply functional_extensionality. intro c.
  unfold barter_tr.
  destruct (excluded_middle_informative (q1 <= work i c1)) as [le1|nle1].
  2: { reflexivity. }
  destruct (excluded_middle_informative (q2 <= work j c2)) as [le2|nle2].
  2: { reflexivity. }
  unfold barter.
  unfold sum_nonnegreals.
  apply equal_nonneg_if_equal_reals.
  assert (
    (fun a : Entity => nonneg (
      if a == i then
        if c == c1
        then {| nonneg := work i c1 - q1; cond_nonneg := Rle_implies_minus_nonneg le1 |}
        else if c == c2 then plus_nonneg (work i c2) q2
        else work i c
      else if a == j then
        if c == c2
        then {| nonneg := work j c2 - q2; cond_nonneg := Rle_implies_minus_nonneg le2 |}
        else if c == c1 then plus_nonneg (work j c1) q1
        else work j c
      else work a c
    )) = (fun a : Entity => (
      if a == i then
        if c == c1
        then work i c1 - q1
        else if c == c2 then (work i c2) + q2
        else work i c
      else if a == j then
        if c == c2
        then work j c2 - q2
        else if c == c1 then (work j c1) + q1
        else work j c
      else work a c
    ))
  ) as dist_nonneg.
  {
    apply functional_extensionality. intro e.
    destruct (e == i).
    {
      destruct (c == c1).
      { reflexivity. }
      { destruct (c == c2); reflexivity. }
    }
    {
      destruct (e == j).
      {
        destruct (c == c2).
        { reflexivity. }
        { destruct (c == c1); reflexivity. }
      }
      { reflexivity. }
    }
  }
  rewrite dist_nonneg.
  destruct (c == c1) eqn:eqc1.
  {
    destruct (c == c2) eqn:eqc2.
    {
      rewrite eq_bool_equivalent in eqc1.
      rewrite eq_bool_equivalent in eqc2.
      rewrite <- eqc1 in nec. rewrite <- eqc2 in nec.
      exfalso. apply nec. reflexivity.
    }
    {
      rewrite eq_bool_equivalent in eqc1. rewrite eqc1.
      unfold Rminus.
      rewrite sum_reals_add_to_2_terms.
      {
        rewrite Rplus_assoc. rewrite Rplus_opp_l.
        rewrite Rplus_0_r. reflexivity.
      }
      { apply nesym. exact neij. }
    }
  }
  {
    destruct (c == c2) eqn:eqc2.
    {
      rewrite eq_bool_equivalent in eqc2. rewrite eqc2.
      unfold Rminus.
      rewrite sum_reals_add_to_2_terms.
      {
        rewrite Rplus_assoc. rewrite Rplus_opp_r.
        rewrite Rplus_0_r. reflexivity.
      }
      { apply nesym. exact neij. }
    }
    {
      apply sum_reals_eq. intro a.
      destruct (a == i) eqn:Eai.
      { rewrite eq_bool_equivalent in Eai. rewrite Eai. reflexivity. }
      {
        destruct (a == j) eqn:Eaj.
        { rewrite eq_bool_equivalent in Eaj. rewrite Eaj. reflexivity. }
        { reflexivity. }
      }
    }
  }
Qed.

Definition barter_AggregateTransaction {i j : Entity} {c1 c2 : Commodity}
{q1 q2 : Quantity} {repartition : @Profile Entity WorkProduct}
(neij : j <> i) (nec : c2 <> c1)
(enough_i : q1 <= repartition i c1) (enough_j : q2 <= repartition j c2) :
AggregateTransaction :=
  exist preserves_total_production (
    barter_tr neij nec q1 q2
  ) (
    barter_preserves_total_production neij nec q1 q2 repartition
  ).

Lemma law_opportunity_cost {c1 c2 : Commodity} {wp : WorkProduct}
{cap : Capacity} {q1 q1' q2 q2' : Quantity} (ltq1 : q1 < q1') (ne_c : c2 <> c1)
(eff : efficient cap (replace (replace wp c1 q1) c2 q2))
(in_cap' : sval cap (replace (replace wp c1 q1') c2 q2')) :
  q2' < q2.
Proof.
  unfold efficient in eff. destruct eff as [in_cap opt].
  specialize (opt (replace (replace wp c1 q1') c2 q2') in_cap').
  assert (
    exists c : Commodity,
      replace (replace wp c1 q1) c2 q2 c <
      replace (replace wp c1 q1') c2 q2' c
  ).
  {
    exists c1.
    rewrite (replace_unchanges (replace wp c1 q1) q2 ne_c).
    rewrite (replace_unchanges (replace wp c1 q1') q2' ne_c).
    rewrite (replace_changes wp c1 q1). rewrite (replace_changes wp c1 q1').
    exact ltq1.
  }
  specialize (opt H). destruct opt as [c opt].
  assert (c = c1 \/ c = c2 \/ (c <> c1 /\ c <> c2)). { tauto. }
  destruct H0.
  {
    rewrite H0 in opt.
    rewrite (replace_unchanges (replace wp c1 q1) q2 ne_c) in opt.
    rewrite (replace_unchanges (replace wp c1 q1') q2' ne_c) in opt.
    rewrite (replace_changes wp c1 q1) in opt.
    rewrite (replace_changes wp c1 q1') in opt.
    exfalso. apply (Rlt_asym q1 q1' ltq1 opt).
  }
  destruct H0.
  {
    rewrite H0 in opt.
    rewrite (replace_changes (replace wp c1 q1) c2 q2) in opt.
    rewrite (replace_changes (replace wp c1 q1') c2 q2') in opt.
    exact opt.
  }
  {
    destruct H0.
    rewrite (replace_unchanges (replace wp c1 q1) q2 (not_eq_sym H1)) in opt.
    rewrite (replace_unchanges (replace wp c1 q1') q2' (not_eq_sym H1)) in opt.
    rewrite (replace_unchanges wp q1 (not_eq_sym H0)) in opt.
    rewrite (replace_unchanges wp q1' (not_eq_sym H0)) in opt.
    exfalso. apply (Rlt_irrefl (wp c) opt).
  }
Qed.

Lemma opportunity_cost_nonnegative {c1 c2 : Commodity} {other_qties : WorkProduct}
{cap : Capacity} {q1 q1' q2 : Quantity} (ltq1 : q1 < q1') (ne_c : c2 <> c1)
(eff : efficient cap (replace (replace other_qties c1 q1) c2 q2))
(in_cap' : exists q2' : Quantity, sval cap (replace (replace other_qties c1 q1') c2 q2')) :
  least_upper_bound_possible_qty in_cap' <= q2.
Proof.
  unfold least_upper_bound_possible_qty.
  pose proof (proj2_sig (
    completeness_nonneg (targeted_capacity_is_finite cap (replace other_qties c1 q1') c2)
    in_cap'
  )) as lubnn.
  simpl in lubnn.
  apply (least_upper_bound_le_if_all_lt_nonneg lubnn).
  intros x posbl.
  apply (law_opportunity_cost ltq1 ne_c eff).
  unfold efficient in eff.
  unfold possible_targeted_production in posbl.
  exact posbl.
Qed.

Definition opportunity_cost {c1 c2 : Commodity} {other_qties : WorkProduct}
{cap : Capacity} {q1 q1' q2 : Quantity} (ltq1 : q1 < q1') (ne_c : c2 <> c1)
(eff : efficient cap (replace (replace other_qties c1 q1) c2 q2))
(in_cap' : exists q2' : Quantity, sval cap (replace (replace other_qties c1 q1') c2 q2')) :
Quantity :=
  {|
    nonneg := q2 - least_upper_bound_possible_qty in_cap' ;
    cond_nonneg := Rle_implies_minus_nonneg (
      opportunity_cost_nonnegative ltq1 ne_c eff in_cap'
    )
  |}.

Definition comparative_advantage {i j : Entity} {c1 c2 : Commodity}
{other_qties_i other_qties_j : WorkProduct}
{q1i q1'i q2i q1j q1'j q2j : Quantity}
(pf_cap : @Profile Entity Capacity)
(ltq1i : q1i < q1'i) (ltq1j : q1j < q1'j) (ne_c : c2 <> c1)
(effi : efficient (pf_cap i) (replace (replace other_qties_i c1 q1i) c2 q2i))
(effj : efficient (pf_cap j) (replace (replace other_qties_j c1 q1j) c2 q2j))
(in_cap'i : exists q2'i : Quantity, sval (pf_cap i) (
  replace (replace other_qties_i c1 q1'i) c2 q2'i
))
(in_cap'j : exists q2'j : Quantity, sval (pf_cap j) (
  replace (replace other_qties_j c1 q1'j) c2 q2'j
)) : Prop :=
  opportunity_cost ltq1i ne_c effi in_cap'i <
  opportunity_cost ltq1j ne_c effj in_cap'j.

Lemma Ricardo_ineq_i {i j : Entity} {c1 c2 : Commodity}
{other_qties_i other_qties_j : WorkProduct}
{q1i q2i q1j q2j δ : Quantity}
{pf_cap : @Profile Entity Capacity}
{in_cap'i : exists q2'i : Quantity, sval (pf_cap i) (
  replace (replace other_qties_i c1 (plus_nonneg q1i δ)) c2 q2'i
)}
{in_cap'j : exists q2'j : Quantity, sval (pf_cap j) (
  replace (replace other_qties_j c1 (plus_nonneg q1j δ)) c2 q2'j
)}
(ne_c : c2 <> c1) (δpos : 0 < δ)
(effi : efficient (pf_cap i) (replace (replace other_qties_i c1 q1i) c2 q2i))
(effj : efficient (pf_cap j) (replace (replace other_qties_j c1 q1j) c2 q2j))
(compad : comparative_advantage pf_cap (
    add_positive_increases_nonneg δpos q1i
  ) (
    add_positive_increases_nonneg δpos q1j
  ) ne_c effi effj in_cap'i in_cap'j
) :
  q2i < least_upper_bound_possible_qty in_cap'i + average_nonneg (
    opportunity_cost (
      add_positive_increases_nonneg δpos q1i
    )  ne_c effi in_cap'i
  ) (
    opportunity_cost (
      add_positive_increases_nonneg δpos q1j
    ) ne_c effj in_cap'j
  ).
Proof.
  unfold opportunity_cost.
  rewrite nonneg_proj_real. rewrite nonneg_proj_real. rewrite nonneg_proj_real.
  rewrite nonneg_proj_real. rewrite nonneg_proj_real.
  apply Rmult_lt_reg_r with (r:=2).
  { apply Rlt_0_2. }
  rewrite Rmult_plus_distr_r.
  rewrite <- Rmult_div_swap. rewrite <- Rmult_div_assoc.
  rewrite (Rdiv_diag).
  2: { auto. }
  rewrite Rmult_1_r.
  rewrite <- Rplus_assoc.
  unfold Rminus.
  assert (
    q2i + - (least_upper_bound_possible_qty in_cap'i) =
    - (least_upper_bound_possible_qty in_cap'i) + q2i
  ) as comm.
  { apply Rplus_comm. }
  rewrite comm.
  assert (
    least_upper_bound_possible_qty in_cap'i * 2 +
    (- least_upper_bound_possible_qty in_cap'i + q2i) =
    least_upper_bound_possible_qty in_cap'i * 2 +
    (- least_upper_bound_possible_qty in_cap'i) + q2i
  ) as asso.
  { rewrite Rplus_assoc. reflexivity. }
  rewrite asso.
  assert (
    nonneg (least_upper_bound_possible_qty in_cap'i) =
    least_upper_bound_possible_qty in_cap'i  * 1
  ) as mul1.
  { rewrite Rmult_1_r. reflexivity. }
  rewrite -> mul1 at 2.
  rewrite <- Ropp_mult_distr_r_reverse. rewrite <- Rmult_plus_distr_l.
  rewrite Rminus_2_1. rewrite Rmult_1_r.
  assert (
    least_upper_bound_possible_qty in_cap'i + q2i =
    q2i + least_upper_bound_possible_qty in_cap'i
  ) as comm2.
  { apply Rplus_comm. }
  rewrite comm2.
  assert (
    q2i + least_upper_bound_possible_qty in_cap'i +
    (q2j + - least_upper_bound_possible_qty in_cap'j) =
    q2i + (least_upper_bound_possible_qty in_cap'i +
    (q2j + - least_upper_bound_possible_qty in_cap'j))
  ) as asso2.
  { rewrite Rplus_assoc. reflexivity. }
  rewrite asso2.
  rewrite Rmult_comm. rewrite <- Rplus_diag.
  apply Rplus_lt_compat_l.
  apply Rplus_lt_reg_l with (r := - least_upper_bound_possible_qty in_cap'i).
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l. rewrite Rplus_0_l.
  unfold comparative_advantage in compad. unfold opportunity_cost in compad.
  rewrite nonneg_proj_real in compad. rewrite nonneg_proj_real in compad.
  assert (
    - least_upper_bound_possible_qty in_cap'i + q2i =
    q2i + - least_upper_bound_possible_qty in_cap'i
  ) as comm3.
  { apply Rplus_comm. }
  rewrite comm3.
  exact compad.
Qed.

Lemma Ricardo_ineq_j {i j : Entity} {c1 c2 : Commodity}
{other_qties_i other_qties_j : WorkProduct}
{q1i q2i q1j q2j δ : Quantity}
{pf_cap : @Profile Entity Capacity}
{in_cap'i : exists q2'i : Quantity, sval (pf_cap i) (
  replace (replace other_qties_i c1 (plus_nonneg q1i δ)) c2 q2'i
)}
{in_cap'j : exists q2'j : Quantity, sval (pf_cap j) (
  replace (replace other_qties_j c1 (plus_nonneg q1j δ)) c2 q2'j
)}
(ne_c : c2 <> c1) (δpos : 0 < δ)
(effi : efficient (pf_cap i) (replace (replace other_qties_i c1 q1i) c2 q2i))
(effj : efficient (pf_cap j) (replace (replace other_qties_j c1 q1j) c2 q2j))
(compad : comparative_advantage pf_cap (
    add_positive_increases_nonneg δpos q1i
  ) (
    add_positive_increases_nonneg δpos q1j
  ) ne_c effi effj in_cap'i in_cap'j
) :
  least_upper_bound_possible_qty in_cap'j < q2j - average_nonneg (
    opportunity_cost (
      add_positive_increases_nonneg δpos q1i
    )  ne_c effi in_cap'i
  ) (
    opportunity_cost (
      add_positive_increases_nonneg δpos q1j
    ) ne_c effj in_cap'j
  ).
Proof.
  unfold opportunity_cost.
  rewrite nonneg_proj_real. rewrite nonneg_proj_real. rewrite nonneg_proj_real.
  rewrite nonneg_proj_real. rewrite nonneg_proj_real.
  apply Rmult_lt_reg_r with (r:=2).
  { apply Rlt_0_2. }
  rewrite Rmult_plus_distr_r.
  rewrite <- Rdiv_opp_l. rewrite <- Rmult_div_swap. rewrite <- Rmult_div_assoc.
  rewrite (Rdiv_diag).
  2: { auto. }
  rewrite Rmult_1_r.
  rewrite Ropp_plus_distr. rewrite <- Rplus_assoc.
  unfold Rminus.
  assert (
    q2j + - (least_upper_bound_possible_qty in_cap'j) =
    - (least_upper_bound_possible_qty in_cap'j) + q2j
  ) as comm.
  { apply Rplus_comm. }
  rewrite comm.
  assert (
    q2j * 2 +
    - (q2i + - least_upper_bound_possible_qty in_cap'i) +
    - (- least_upper_bound_possible_qty in_cap'j + q2j) =
    - (- least_upper_bound_possible_qty in_cap'j + q2j) +
    (
      q2j * 2 +
      - (q2i + - least_upper_bound_possible_qty in_cap'i)
    )
  ) as comm2.
  { apply Rplus_comm. }
  rewrite comm2.
  rewrite Ropp_plus_distr. rewrite Ropp_plus_distr.
  rewrite Ropp_involutive. rewrite Ropp_involutive.
  assert (
    least_upper_bound_possible_qty in_cap'j + - q2j +
    (q2j * 2 + (- q2i + least_upper_bound_possible_qty in_cap'i)) =
    least_upper_bound_possible_qty in_cap'j + (- q2j +
    (q2j * 2 + (- q2i + least_upper_bound_possible_qty in_cap'i)))
  ) as asso.
  { rewrite Rplus_assoc. reflexivity. }
  rewrite asso.
  apply Rplus_lt_reg_l with (r := - least_upper_bound_possible_qty in_cap'j).
  rewrite <- Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_l.
  rewrite <- (Rmult_1_r (least_upper_bound_possible_qty in_cap'j)) at 1.
  rewrite Ropp_mult_distr_r. rewrite <- Rmult_plus_distr_l.
  assert (- (1) + 2 = 1) as Rminus_1_2.
  { rewrite Rplus_comm. rewrite Rminus_2_1. reflexivity. }
  rewrite Rminus_1_2. rewrite Rmult_1_r.
  rewrite <- Rplus_assoc.
  rewrite <- (Rmult_1_r q2j) at 1.
  rewrite Ropp_mult_distr_r. rewrite <- Rmult_plus_distr_l.
  rewrite Rminus_1_2. rewrite Rmult_1_r.
  apply Rplus_lt_reg_r with (r := - (- q2i + least_upper_bound_possible_qty in_cap'i)).
  rewrite Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_r.
  apply Rplus_lt_reg_l with (r := - least_upper_bound_possible_qty in_cap'j).
  rewrite <- Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_l.
  rewrite Ropp_plus_distr. rewrite Ropp_involutive.
  unfold comparative_advantage in compad. unfold opportunity_cost in compad.
  rewrite nonneg_proj_real in compad. rewrite nonneg_proj_real in compad.
  assert (
    - least_upper_bound_possible_qty in_cap'j + q2j =
    q2j + - least_upper_bound_possible_qty in_cap'j
  ) as comm3.
  { apply Rplus_comm. }
  rewrite comm3.
  exact compad.
Qed.

Definition repartition_before_Ricardo_barter {i j : Entity} {c1 c2 : Commodity}
{repartition : @Profile Entity WorkProduct} {q1i q2i q1j q2j δ : Quantity}
{δpos : 0 < δ} {pf_cap : @Profile Entity Capacity}
{in_cap'i : exists q2'i : Quantity, sval (pf_cap i) (
  replace (replace (repartition i) c1 (plus_nonneg q1i δ)) c2 q2'i
)}
{in_cap'j : exists q2'j : Quantity, sval (pf_cap j) (
  replace (replace (repartition j) c1 (plus_nonneg q1j δ)) c2 q2'j
)}
{effi : efficient (pf_cap i) (replace (replace (repartition i) c1 q1i) c2 q2i)}
{effj : efficient (pf_cap j) (replace (replace (repartition j) c1 q1j) c2 q2j)}
(ne_c : c2 <> c1)
(compad : comparative_advantage pf_cap (
    add_positive_increases_nonneg δpos q1i
  ) (
    add_positive_increases_nonneg δpos q1j
  ) ne_c effi effj in_cap'i in_cap'j
) :
@Profile Entity WorkProduct :=
  replace (
    replace repartition i (
      replace (
        replace (repartition i) c1 (plus_nonneg q1i δ)
      ) c2 (least_upper_bound_possible_qty in_cap'i)
    )
  ) j (
    replace (
      replace (repartition j) c1 q1j
    ) c2 q2j
  ).

Lemma Ricardo_barter_enough_i {i j : Entity} {c1 c2 : Commodity}
{repartition : @Profile Entity WorkProduct} {q1i q2i q1j q2j δ : Quantity}
{δpos : 0 < δ} {pf_cap : @Profile Entity Capacity}
{in_cap'i : exists q2'i : Quantity, sval (pf_cap i) (
  replace (replace (repartition i) c1 (plus_nonneg q1i δ)) c2 q2'i
)}
{in_cap'j : exists q2'j : Quantity, sval (pf_cap j) (
  replace (replace (repartition j) c1 (plus_nonneg q1j δ)) c2 q2'j
)}
{effi : efficient (pf_cap i) (replace (replace (repartition i) c1 q1i) c2 q2i)}
{effj : efficient (pf_cap j) (replace (replace (repartition j) c1 q1j) c2 q2j)}
(neij : j <> i) (ne_c : c2 <> c1)
(compad : comparative_advantage pf_cap (
    add_positive_increases_nonneg δpos q1i
  ) (
    add_positive_increases_nonneg δpos q1j
  ) ne_c effi effj in_cap'i in_cap'j
) :
  δ <= repartition_before_Ricardo_barter ne_c compad i c1.
Proof.
  pose proof (cond_nonneg q1i) as pos1i.
  apply (Rplus_le_compat_r δ) in pos1i. rewrite Rplus_0_l in pos1i.
  unfold repartition_before_Ricardo_barter.
  rewrite replace_unchanges.
  2: { exact neij. }
  rewrite replace_changes. rewrite replace_unchanges.
  2: { exact ne_c. }
  rewrite replace_changes.
  auto.
Qed.

Lemma Ricardo_barter_enough_j {i j : Entity} {c1 c2 : Commodity}
{repartition : @Profile Entity WorkProduct} {q1i q2i q1j q2j δ : Quantity}
{δpos : 0 < δ} {pf_cap : @Profile Entity Capacity}
{in_cap'i : exists q2'i : Quantity, sval (pf_cap i) (
  replace (replace (repartition i) c1 (plus_nonneg q1i δ)) c2 q2'i
)}
{in_cap'j : exists q2'j : Quantity, sval (pf_cap j) (
  replace (replace (repartition j) c1 (plus_nonneg q1j δ)) c2 q2'j
)}
{effi : efficient (pf_cap i) (replace (replace (repartition i) c1 q1i) c2 q2i)}
{effj : efficient (pf_cap j) (replace (replace (repartition j) c1 q1j) c2 q2j)}
(ne_c : c2 <> c1)
(compad : comparative_advantage pf_cap (
    add_positive_increases_nonneg δpos q1i
  ) (
    add_positive_increases_nonneg δpos q1j
  ) ne_c effi effj in_cap'i in_cap'j
) :
  average_nonneg (
    opportunity_cost (add_positive_increases_nonneg δpos q1i) ne_c effi in_cap'i
  ) (
    opportunity_cost (add_positive_increases_nonneg δpos q1j) ne_c effj in_cap'j
  ) <= repartition_before_Ricardo_barter ne_c compad j c2.
Proof.
  pose proof (Ricardo_ineq_j ne_c δpos effi effj compad) as ineqj.
  pose proof (cond_nonneg (least_upper_bound_possible_qty in_cap'j)) as lubpos.
  pose proof (Rle_lt_trans 0 (least_upper_bound_possible_qty in_cap'j) (
    q2j - average_nonneg (
      opportunity_cost (add_positive_increases_nonneg δpos q1i) ne_c effi in_cap'i
    ) (
      opportunity_cost (add_positive_increases_nonneg δpos q1j) ne_c effj in_cap'j
    )
  ) lubpos ineqj) as δq.
  apply (Rplus_lt_compat_r (
    average_nonneg (
      opportunity_cost (add_positive_increases_nonneg δpos q1i) ne_c effi in_cap'i
    ) (
      opportunity_cost (add_positive_increases_nonneg δpos q1j) ne_c effj in_cap'j
    )
  )) in δq.
  rewrite Rplus_0_l in δq.
  unfold Rminus in δq.
  rewrite Rplus_assoc in δq. rewrite Rplus_opp_l in δq. rewrite Rplus_0_r in δq.
  apply Rlt_le in δq.
  unfold repartition_before_Ricardo_barter.
  rewrite replace_changes. rewrite replace_changes.
  exact δq.
Qed.

Definition Ricardo_barter {i j : Entity} {c1 c2 : Commodity}
{repartition : @Profile Entity WorkProduct} {q1i q2i q1j q2j δ : Quantity}
{δpos : 0 < δ} {pf_cap : @Profile Entity Capacity}
{in_cap'i : exists q2'i : Quantity, sval (pf_cap i) (
  replace (replace (repartition i) c1 (plus_nonneg q1i δ)) c2 q2'i
)}
{in_cap'j : exists q2'j : Quantity, sval (pf_cap j) (
  replace (replace (repartition j) c1 (plus_nonneg q1j δ)) c2 q2'j
)}
{effi : efficient (pf_cap i) (replace (replace (repartition i) c1 q1i) c2 q2i)}
{effj : efficient (pf_cap j) (replace (replace (repartition j) c1 q1j) c2 q2j)}
(neij : j <> i) (ne_c : c2 <> c1)
(compad : comparative_advantage pf_cap (
    add_positive_increases_nonneg δpos q1i
  ) (
    add_positive_increases_nonneg δpos q1j
  ) ne_c effi effj in_cap'i in_cap'j
) : AggregateTransaction :=
  barter_AggregateTransaction neij ne_c (
    Ricardo_barter_enough_i neij ne_c compad
  ) (
    Ricardo_barter_enough_j ne_c compad
  ).

Theorem Ricardo {i j : Entity} {c1 c2 : Commodity}
{repartition : @Profile Entity WorkProduct}
{q1i q2i q1j q2j δ : Quantity} {δpos : 0 < δ}
{pf_cap : @Profile Entity Capacity}
{in_cap'i : exists q2'i : Quantity, sval (pf_cap i) (
  replace (replace (repartition i) c1 (plus_nonneg q1i δ)) c2 q2'i
)}
{in_cap'j : exists q2'j : Quantity, sval (pf_cap j) (
  replace (replace (repartition j) c1 (plus_nonneg q1j δ)) c2 q2'j
)}
{effi : efficient (pf_cap i) (replace (replace (repartition i) c1 q1i) c2 q2i)}
{effj : efficient (pf_cap j) (replace (replace (repartition j) c1 q1j) c2 q2j)}
(in_capk : forall e : Entity, e <> i -> e <> j -> sval (pf_cap e) (repartition e))
(neij : j <> i) (ne_c : c2 <> c1)
(compad : comparative_advantage pf_cap (
    add_positive_increases_nonneg δpos q1i
  ) (
    add_positive_increases_nonneg δpos q1j
  ) ne_c effi effj in_cap'i in_cap'j
)
(fppi : finite_precision_possible_qty in_cap'i) :
  in_capacity (repartition_before_Ricardo_barter ne_c compad) pf_cap /\
  ~ sval (pf_cap i) (
    sval (
      Ricardo_barter neij ne_c compad
    ) (
      repartition_before_Ricardo_barter ne_c compad
    ) i
  ) /\
  ~ sval (pf_cap j) (
    sval (
      Ricardo_barter neij ne_c compad
    ) (
      repartition_before_Ricardo_barter ne_c compad
    ) j
  ).
Proof.
  split.
  {
    unfold in_capacity. intro e. unfold repartition_before_Ricardo_barter.
    specialize (in_capk e).
    assert (e = i \/ e <> i) as tautei. { tauto. }
    destruct tautei as [eqei|neei].
    {
      rewrite eqei.
      rewrite replace_unchanges.
      2: { exact neij. }
      rewrite replace_changes.
      exact fppi.
    }
    assert (e = j \/ e <> j) as tautej. { tauto. }
    destruct tautej as [eqej|neej].
    {
      rewrite eqej.
      rewrite replace_changes.
      unfold efficient in effj.
      destruct effj as [cap eff]. exact cap.
    }
    rewrite replace_unchanges.
    2: { apply nesym. exact neej. }
    rewrite replace_unchanges.
    2: { apply nesym. exact neei. }
    apply in_capk; tauto.
  }
  unfold Ricardo_barter. simpl. unfold barter_tr. simpl.
  unfold barter. simpl.
  destruct (excluded_middle_informative (
    δ <= repartition_before_Ricardo_barter ne_c compad i c1
  )) as [δbef|δbef].
  2: { pose proof (Ricardo_barter_enough_i neij ne_c compad). tauto. }
  destruct (excluded_middle_informative (
    (q2i - least_upper_bound_possible_qty in_cap'i +
    (q2j - least_upper_bound_possible_qty in_cap'j)) / 2 <=
    repartition_before_Ricardo_barter ne_c compad j c2
  )) as [avgbef|avgbef].
  2: { pose proof (Ricardo_barter_enough_j ne_c compad). tauto. }
  split.
  {
    rewrite eq_refl.
    intro raa.
    set (repartition_after_Ricardo_barter :=
      replace (replace (repartition i) c1 q1i) c2 (
        plus_nonneg (
          least_upper_bound_possible_qty in_cap'i
        ) (
          average_nonneg (
            opportunity_cost (
              add_positive_increases_nonneg δpos q1i
            ) ne_c effi in_cap'i
          ) (
            opportunity_cost (
              add_positive_increases_nonneg δpos q1j
            ) ne_c effj in_cap'j
          )
        )
      )
    ).
    pose proof (Ricardo_ineq_i ne_c δpos effi effj compad) as ineq_i.
    pose proof effi as effi_bis.
    unfold efficient in effi_bis. destruct effi_bis as [in_capi effi'].
    pose proof (effi' repartition_after_Ricardo_barter) as effi0.
    assert (
      repartition_after_Ricardo_barter = (fun c : Commodity =>
        if c == c1 then {|
          nonneg := repartition_before_Ricardo_barter ne_c compad i c1 - δ;
          cond_nonneg := Rle_implies_minus_nonneg δbef
        |}
        else if c == c2 then
          plus_nonneg (repartition_before_Ricardo_barter ne_c compad i c2) (
            average_nonneg (
              opportunity_cost (
                add_positive_increases_nonneg δpos q1i
              ) ne_c effi in_cap'i
            ) (
              opportunity_cost (
                add_positive_increases_nonneg δpos q1j
              ) ne_c effj in_cap'j
            )
          )
        else repartition_before_Ricardo_barter ne_c compad i c
      )
    ) as after_Ricardo_barter.
    {
      apply functional_extensionality. intro c.
      unfold repartition_after_Ricardo_barter.
      destruct (c == c1) eqn:eqc1.
      {
        assert (c = c1) as eqc1'.
        { apply eq_bool_equivalent. exact eqc1. }
        rewrite eqc1'.
        rewrite replace_unchanges.
        2: { exact ne_c. }
        rewrite replace_changes.
        unfold repartition_before_Ricardo_barter.
        pose proof (nonneg_involution (cond_nonneg q1i)) as goalR.
        rewrite <- goalR at 1.
        apply equal_nonneg_if_equal_reals.
        rewrite replace_unchanges.
        2: { exact neij. }
        rewrite replace_changes.
        rewrite replace_unchanges.
        2: { exact ne_c. }
        rewrite replace_changes.
        unfold plus_nonneg.
        rewrite <- goalR at 1.
        rewrite nonneg_involution.
        rewrite <- (Rplus_minus_r q1i δ) at 1.
        apply Rminus_eq_compat_r.
        auto.
      }
      destruct (c == c2) eqn:eqc2.
      {
        assert (c = c2) as eqc2'.
        { apply eq_bool_equivalent. exact eqc2. }
        rewrite eqc2'.
        rewrite replace_changes.
        unfold repartition_before_Ricardo_barter.
        rewrite replace_unchanges.
        2: { exact neij. }
        rewrite replace_changes. rewrite replace_changes.
        reflexivity.
      }
      {
        rewrite replace_unchanges.
        2: { apply eq_bool_equivalent_not.  rewrite eq_sym. exact eqc2. }
        rewrite replace_unchanges.
        2: { apply eq_bool_equivalent_not.  rewrite eq_sym. exact eqc1. }
        unfold repartition_before_Ricardo_barter.
        rewrite replace_unchanges.
        2: { exact neij. }
        rewrite replace_changes.
        rewrite replace_unchanges.
        2: { apply eq_bool_equivalent_not.  rewrite eq_sym. exact eqc2. }
        rewrite replace_unchanges.
        2: { apply eq_bool_equivalent_not.  rewrite eq_sym. exact eqc1. }
        reflexivity.
      }
    }
    rewrite <- after_Ricardo_barter in raa.
    specialize (effi0 raa).
    assert (
      replace (replace (repartition i) c1 q1i) c2 q2i c2 <
      repartition_after_Ricardo_barter c2
    ) as lt2.
    {
      rewrite replace_changes.
      unfold repartition_after_Ricardo_barter.
      rewrite replace_changes.
      exact ineq_i.
    }
    specialize (effi0 (
      ex_intro (
        fun c => (
          replace (replace (repartition i) c1 q1i) c2 q2i c <
          repartition_after_Ricardo_barter c
        )
      ) c2 lt2
    )).
    destruct effi0 as [c effi0].
    destruct (c == c1) eqn:eqc1.
    {
      unfold repartition_after_Ricardo_barter in effi0.
      assert (c = c1) as eqc1'.
      { apply eq_bool_equivalent. exact eqc1. }
      rewrite eqc1' in effi0.
      rewrite replace_unchanges in effi0.
      2: { exact ne_c. }
      rewrite replace_changes in effi0.
      rewrite replace_unchanges in effi0.
      2: { exact ne_c. }
      rewrite replace_changes in effi0.
      pose proof (Rlt_irrefl q1i) as neq.
      apply neq. exact effi0.
    }
    destruct (c == c2) eqn:eqc2.
    {
      assert (c = c2) as eqc2'.
      { apply eq_bool_equivalent. exact eqc2. }
      rewrite eqc2' in effi0.
      apply Rlt_asym in lt2. apply lt2. exact effi0.
    }
    {
      unfold repartition_after_Ricardo_barter in effi0.
      rewrite replace_unchanges in effi0.
      2: { rewrite eq_bool_equivalent_not in eqc2. apply nesym. exact eqc2. }
      rewrite replace_unchanges in effi0.
      2: { rewrite eq_bool_equivalent_not in eqc1. apply nesym. exact eqc1. }
      rewrite replace_unchanges in effi0.
      2: { rewrite eq_bool_equivalent_not in eqc2. apply nesym. exact eqc2. }
      rewrite replace_unchanges in effi0.
      2: { rewrite eq_bool_equivalent_not in eqc1. apply nesym. exact eqc1. }
      apply (Rlt_irrefl (repartition i c)). exact effi0.
    }
  }
  {
    assert ((j == i) = false) as neij'.
    { apply eq_bool_equivalent_not. exact neij. }
    assert ((c1 == c2) = false) as ne_c'.
    { apply eq_bool_equivalent_not. apply nesym. exact ne_c. }
    rewrite eq_refl.
    intro raa.
    rewrite neij' in raa.
    pose proof (Ricardo_ineq_j ne_c δpos effi effj compad) as ineq_j.
    pose proof (cond_nonneg (least_upper_bound_possible_qty in_cap'j)) as lubpos.
    pose proof (Rle_lt_trans 0 (least_upper_bound_possible_qty in_cap'j) (
      q2j - average_nonneg (
        opportunity_cost (
          add_positive_increases_nonneg δpos q1i
        ) ne_c effi in_cap'i
      ) (
        opportunity_cost (
          add_positive_increases_nonneg δpos q1j
        ) ne_c effj in_cap'j
      )
    ) lubpos ineq_j) as qc2j.
    apply (Rlt_le 0 (q2j - (
      average_nonneg (
        opportunity_cost (
          add_positive_increases_nonneg δpos q1i
        ) ne_c effi in_cap'i
      ) (
        opportunity_cost (
          add_positive_increases_nonneg δpos q1j
        ) ne_c effj in_cap'j
      )
    ))) in qc2j.
    assert (
      least_upper_bound_possible_qty in_cap'j < {|
        nonneg := q2j - average_nonneg (
          opportunity_cost (add_positive_increases_nonneg δpos q1i) ne_c effi in_cap'i
        ) (
          opportunity_cost (add_positive_increases_nonneg δpos q1j) ne_c effj in_cap'j
        ) ;
        cond_nonneg := qc2j
      |}
    ) as ineq_j'.
    { auto. }
    pose proof (least_upper_bound_possible_qty_is_upper_bound ineq_j') as out_cap.
    apply out_cap.
    assert (
      (
        fun c : Commodity => (
          if c == c2 then {|
            nonneg := (
              repartition_before_Ricardo_barter ne_c compad j c2 -
              (q2i - least_upper_bound_possible_qty in_cap'i + (
                q2j - least_upper_bound_possible_qty in_cap'j
              )) / 2
            ) ;
            cond_nonneg := Rle_implies_minus_nonneg avgbef
          |}
          else if c == c1 then plus_nonneg (
            repartition_before_Ricardo_barter ne_c compad j c1
          ) δ
          else repartition_before_Ricardo_barter ne_c compad j c
        )
      ) = (replace (replace (repartition j) c1 (plus_nonneg q1j δ)) c2 {|
        nonneg := q2j - average_nonneg (
          opportunity_cost (add_positive_increases_nonneg δpos q1i) ne_c effi in_cap'i
        ) (
          opportunity_cost (add_positive_increases_nonneg δpos q1j) ne_c effj in_cap'j
        ) ;
        cond_nonneg := qc2j
      |})
    ) as eq_sval.
    2: { rewrite eq_sval in raa. exact raa. }
    apply functional_extensionality. intro c.
    destruct (c == c2) eqn:eqc2.
    {
      assert (c = c2) as eqc2'.
      { apply eq_bool_equivalent. exact eqc2. }
      rewrite eqc2'.
      rewrite replace_changes.
      apply equal_nonneg_if_equal_reals.
      unfold repartition_before_Ricardo_barter.
      rewrite replace_changes. rewrite replace_changes.
      unfold opportunity_cost.
      auto.
    }
    destruct (c == c1) eqn:eqc1.
    {
      assert (c = c1) as eqc1'.
      { apply eq_bool_equivalent. exact eqc1. }
      rewrite eqc1'.
      rewrite replace_unchanges.
      2: { exact ne_c. }
      rewrite replace_changes.
      unfold repartition_before_Ricardo_barter.
      rewrite replace_changes.
      rewrite replace_unchanges.
      2: { exact ne_c. }
      rewrite replace_changes.
      reflexivity.
    }
    {
      assert (c <> c1) as eqc1'.
      { apply eq_bool_equivalent_not. exact eqc1. }
      assert (c <> c2) as eqc2'.
      { apply eq_bool_equivalent_not. exact eqc2. }
      rewrite replace_unchanges.
      2: { apply nesym. exact eqc2'. }
      unfold repartition_before_Ricardo_barter.
      rewrite replace_changes.
      rewrite replace_unchanges.
      2: { apply nesym. exact eqc2'. }
      rewrite replace_unchanges.
      2: { apply nesym. exact eqc1'. }
      rewrite replace_unchanges.
      2: { apply nesym. exact eqc1'. }
      reflexivity.
    }
  }
Qed.

End gains_from_trade.
