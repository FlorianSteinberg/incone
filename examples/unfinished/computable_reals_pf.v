(* Implementation of soft comparisons using partial functions *)
From Coquelicot Require Import Coquelicot.
From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_rlzrs.
From metric Require Import reals.
Require Import all_cs_base classical_mach.
Require Import Reals Psatz FunctionalExtensionality ClassicalChoice.
Require Import axioms all_cs cs_mtrc metric_names hyper_spaces.
Require Import continuous_machines.
Require Import monotone_machine_composition.
Require Import Q_reals.
From metric Require Import all_metric reals standard Qmetric.
Arguments partial_function {S} {T}.
Definition ltK (xy : R*R) := let (x,y) := xy in
                     match (total_order_T x y) with
                     | (inleft (left _)) => true_K
                     | (inright _) => false_K
                     | _ => bot_K
                     end.

Lemma ltK_spec x y: ((ltK (x,y)) = true_K <-> (x < y)) /\ ((ltK (x,y)) = false_K <-> (y < x)) /\ ((ltK (x,y)) = bot_K <-> (x = y)). 
Proof.
  rewrite /ltK.
  case: (total_order_T x y) => [[xlty | <-] | xgty].
  split; split;[| | split | split]; try lra;try by auto.
  split; split;[| | split | split]; try lra;try by auto.
  split; split;[| | split | split]; try lra;try by auto.
Qed.

Definition Rdiv_mf := make_mf (fun xy z => (xy.2 <> 0 /\ z = (xy.1/xy.2))).

Structure computable_reals:=
  {
    representation: representation_of R;
    approximate: representation \translatable_to Q_reals.Q_representation;
    addition_rlzr: {f : partial_function| let R := Build_continuity_space representation in f \realizes (uncurry (Rplus: R -> R  -> R))};
    multiplication_rlzr: {f : partial_function| let R := Build_continuity_space representation in f \realizes (uncurry (Rmult: R -> R  -> R))};
    division_rlzr: {f : partial_function| let R := Build_continuity_space representation in f \solves (Rdiv_mf : (R*R) ->> R)};
    ltk_rlzr: {f : partial_function| let R := Build_continuity_space representation in  f \realizes (ltK : R * R -> cs_Kleeneans)};
    cleanup: {f | let R := Build_continuity_space representation in  (F2MF f) \solves (mf_id : R ->> R)};
    limit_rlzr: {f : partial_function| let R := Build_continuity_space representation in f \solves (efficient_limit : (R\^w) ->> R)};
    F2R: {f | let R := Build_continuity_space representation in
                           (F2MF f) \realizes (uncurry (fun (m exp : Z) => (m * powerRZ 2 exp)) : (Z * Z -> R))};
  }.
