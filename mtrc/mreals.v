(* Proofs that the structures introduced on metric spaces coincide with
the corresponding ones from the standard library. *)
From mathcomp Require Import ssreflect ssrnat ssrbool ssrfun.
From rlzrs Require Import all_mf.
Require Import reals mtrc.
Require Import Reals Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope R_scope.

Lemma Uncv_lim: make_mf Un_cv =~= @limit R_met.
Proof.
  move => xn x; split => ass eps epsg0.
  have [N Nprp]:= ass eps epsg0; exists N => n ineq.
  apply Rlt_le; rewrite /=/R_dist Rabs_minus_sym.
    by rewrite /R_dist in Nprp; apply /Nprp/leP.
    have [ | N Nprp]:= ass (eps/2); try lra; exists N => n ineq.
    rewrite /R_dist Rabs_minus_sym; apply /Rle_lt_trans; first by apply /Nprp /leP.
  lra.
Qed.

Lemma cchy_crit: @Cauchy_sequence R_met === make_subset Cauchy_crit.
Proof.
  move => xn; split => cchy eps epsg0.
  - have [ | N prp]:= cchy (eps/2); first by rewrite /Rdiv; lra.
    exists N => n m /leP ineq /leP ineq'.
    by apply/Rle_lt_trans; first apply/prp => //; rewrite /Rdiv; lra.
  have [N prp]:= cchy eps epsg0.
  by exists N; intros; apply/Rlt_le/prp/leP; first apply/leP.
Qed.

Lemma R_cmplt: complete R_met.
Proof.
  move => xn /cchy_crit cchy.
  have [x /Uncv_lim lim]:= R_complete xn cchy.
  by exists x.
Qed.

Lemma cchy_conv:
  @fast_Cauchy_sequence R_met === dom (@efficient_limit R_met).
Proof.
  move => xn; split => [Cauchy |  [x /lim_eff_lim []]]//.
  rewrite lim_eff_lim dom_restr_spec; split => //.
  exact/R_cmplt/cchy_fast_cchy.
Qed.