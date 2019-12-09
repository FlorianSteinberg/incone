(* Implementation of soft comparisons using machine composition *)
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
Arguments monotone_machine {Q} {A} {Q'} {A'}.
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

Structure computable_reals:=
  {
    representation: representation_of R;
    approximate: representation \translatable_to Q_reals.Q_representation;
    addition_machine: {M : monotone_machine| let R := Build_continuity_space representation in
                           implements (uncurry (Rplus: R -> R  -> R)) M};
    multiplication_machine: {M: monotone_machine| let R := Build_continuity_space representation in
                                            implements (uncurry (Rmult: R -> R -> R)) M};
    ltk_machine: {M : monotone_machine| let R := Build_continuity_space representation in
                           implements (ltK : R * R -> Kleeneans) M};
    F2R_machine: {M : monotone_machine| let R := Build_continuity_space representation in
                           implements (uncurry (fun (m exp : Z) => (m * powerRZ 2 exp)) : (Z * Z -> R)) M};
  }.
