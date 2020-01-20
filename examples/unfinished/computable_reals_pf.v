(* Implementation of soft comparisons using partial functions *)
From Coquelicot Require Import Coquelicot.
From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_rlzrs.
Require Import Reals.
From metric Require Import all_metric reals standard Qmetric.
Require Import axioms all_cs_base cs_mtrc metric_names hyper_spaces all_cs classical_mach Q_reals.
Require Import continuous_machines monotone_machines Q_round division_for_Q_reals.
Structure computable_reals:=
  {
    representation: representation_of R;
    approximate: {f: partial_function | let R := Build_continuity_space representation in
                                         f \realizes (id: R -> RQ)};
    addition_rlzr: {f: partial_function | let R := Build_continuity_space representation in
                                           f \realizes (uncurry Rplus: R * R -> R)};
    multiplication_rlzr: {f: partial_function | let R := Build_continuity_space representation in
                                                 f \realizes (uncurry Rmult: R * R -> R)};
    division_rlzr: {f: partial_function | let R := Build_continuity_space representation in
                                           f \solves (find_fraction: R * R ->> R)};
    ltk_rlzr: {f: partial_function | let R := Build_continuity_space representation in
                                      f \realizes (ltK : R * R -> cs_Kleeneans)};
    cleanup: {f: partial_function | let R := Build_continuity_space representation in
                  f \solves (mf_id : R ->> R)};
    limit_rlzr: {f: partial_function| let R := Build_continuity_space representation in
                                       f \solves (efficient_limit: R\^w ->> R)};
    F2R: {f  | let R := Build_continuity_space representation in
                                (F2MF f) \realizes (uncurry (fun (m exp: Z) => m * powerRZ 2 exp): _ -> R)};
  }.

Require Import QArith BinNums BinIntDef BinInt Qreals ZArith Psatz.
Definition rational_reals: computable_reals.
  exists Q_representation => /=.
  - by exists (F2PF (@id _)); rewrite F2PF_spec; apply/id_rlzr.
  - by exists (F2PF Rplus_rlzrf); rewrite F2PF_spec; apply/Rplus_rlzr_spec.
  - by exists (F2PF Rmult_rlzr); rewrite F2PF_spec; apply/Rmult_rlzr_spec.
  - suff [f prp]: {f: partial_function | f \solves (F2MF (uncurry Rmult) \o (mf_id ** inversion))}.
    + by exists f; rewrite ffr_spec.
    apply/(cmp_pf (Y:= RQ \*_cs RQ)).
    + by exists (F2PF Rmult_rlzr); rewrite F2PF_spec; apply/Rmult_rlzr_spec.
    + apply/pf_fprd; first by exists (F2PF (@id _)); rewrite F2PF_spec; apply/id_rlzr.
      * exists (get_pf RQinv_M); rewrite gtpf_spec; apply/tight_slvs/sfrst_spec/inv_M_spec.
      reflexivity.
    by trivial.
  - by exists (F2PF ltK_rlzrf); rewrite F2PF_spec; apply/ltK_rlzrf_spec.
  - by exists (F2PF round_name_RQ'); rewrite F2PF_spec; apply/round_RQ'_correct.
  - by exists (F2PF lim_eff_rlzrf); rewrite F2PF_spec; apply/lim_eff_rlzr_spec.
  exists ((fun phi _ => inject_Z (lprj phi (tt: Q_(cs_Z))) * ((1 + 1)^(rprj phi (tt: Q_ cs_Z))))%Q).
  rewrite /uncurry /= /lprj /rprj.
  apply/F2MF_rlzr => phi [m e] /prod_name_spec [<- <-] eps eg0 /=.
  rewrite /lprj /rprj /=.
  rewrite Q2R_mult {1}/Q2R /=.
  suff ->: powerRZ 2 (phi (inr tt)).2 = ((1 + 1) ^ (phi (inr tt)).2)%Q.
  - by rewrite Rinv_1 Rmult_1_r Rminus_eq_0; split_Rabs; lra.
  case eq: ((phi (inr tt)).2 ?= 0)%Z; first by move:eq =>/Z.compare_eq_iff ->; rewrite/Q2R/=; lra.
  - move: eq => /Z.compare_lt_iff ineq.
    rewrite -{1}(Zopp_involutive (phi (inr tt)).2) Qpower_minus.
    have /IZN_var [n ->]: (0 <= -(phi (inr tt)).2)%Z by lia.
    rewrite powerRZ_neg; try lra.
    rewrite -pow_powerRZ Qpower_spec => [ | /Qeq_eqR eq]; f_equal; first by rewrite /Q2R /=; lra.
    suff: (1/2 = 0)%R by lra.
    have ->: (0 = Q2R 0)%R by rewrite /Q2R /=; lra.
    by rewrite -eq /Q2R /=; lra.
  move: eq => /Z.compare_gt_iff ineq.
  have /IZN_var [n ->]: (0 <= (phi (inr tt)).2)%Z by lia.
  by rewrite -pow_powerRZ Qpower_spec /=; last lra; f_equal; rewrite /Q2R /=; lra.
Defined.
