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

Definition Rdiv_mf := make_mf (fun xy z => (xy.2 <> 0 /\ z = (xy.1/xy.2))).
Structure computable_reals:=
  {
    representation: representation_of R;
    approximate: representation \translatable_to Q_reals.Q_representation;
    addition_machine: {M : monotone_machine| let R := Build_continuity_space representation in
                           implements (uncurry (Rplus: R -> R  -> R)) M};
    multiplication_machine: {M: monotone_machine| let R := Build_continuity_space representation in
                                            implements (uncurry (Rmult: R -> R -> R)) M};
    division_machine: {M: monotone_machine| let R := Build_continuity_space representation in
                                            \F_M \solves (Rdiv_mf : (R * R) ->> R)};
    ltk_machine: {M : monotone_machine| let R := Build_continuity_space representation in
                           implements (ltK : R * R -> Kleeneans) M};
    F2R: {f | let R := Build_continuity_space representation in
                           (F2MF f) \realizes (uncurry (fun (m exp : Z) => (m * powerRZ 2 exp)) : (Z * Z -> R))};
  }.


(* sometimes we need the machine instead of the function *)
Lemma F2R_machine (cr : computable_reals) : {M : monotone_machine | let R := Build_continuity_space (representation cr) in implements (uncurry (fun (m exp : Z) => (m * powerRZ 2 exp)) : (Z * Z -> R)) M}.
Proof.
  set mu := (fun (phi: B_(cs_Z \*_cs cs_Z)) (q : Q_(name_space (representation cr))) =>  [:: (inr tt); (inl tt)]) .
  case (F2R cr) => f2r f2r_prp.
  have mm : mu \modulus_function_for (f2r).
  - move => phi q psi [[H1 [H2 _]]]. 
    suff -> : (phi = psi) by trivial.
    apply functional_extensionality => [[]]; by case.
  have mu_mod : (mu \modulus_function_for mu) by trivial.
  exists (F2MM mm mu_mod).
  by rewrite /implements F2M_spec.
Defined.
