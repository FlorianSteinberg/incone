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
Structure computable_reals:=
  {
    representation: representation_of R;
    approximate: {f : partial_function| let R := Build_continuity_space representation in f \realizes ((id: R -> RQ))};
    addition_rlzr: {f : partial_function| let R := Build_continuity_space representation in f \realizes (uncurry (Rplus: R -> R  -> R))};
    multiplication_rlzr: {f : partial_function| let R := Build_continuity_space representation in f \realizes (uncurry (Rmult: R -> R  -> R))};
    division_rlzr: {f : partial_function| let R := Build_continuity_space representation in f \solves (Rdiv_mf : (R*R) ->> R)};
    ltk_rlzr: {f : partial_function| let R := Build_continuity_space representation in  f \realizes (ltK : R * R -> cs_Kleeneans)};
    cleanup: {f | let R := Build_continuity_space representation in  (F2MF f) \solves (mf_id : R ->> R)};
    limit_rlzr: {f : partial_function| let R := Build_continuity_space representation in f \solves (efficient_limit : (R\^w) ->> R)};
    F2R: {f | let R := Build_continuity_space representation in
                           (F2MF f) \realizes (uncurry (fun (m exp : Z) => (m * powerRZ 2 exp)) : (Z * Z -> R))};
  }.
