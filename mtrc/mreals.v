(* Proofs that the structures introduced on metric spaces coincide with
the corresponding ones from the standard library. *)
From mathcomp Require Import ssreflect ssrnat ssrbool ssrfun.
From rlzrs Require Import all_mf.
Require Import reals mtrc cprd.
Require Import Reals Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope R_scope.

Notation limit := (@metric_limit R_met).

Lemma Uncv_lim: make_mf Un_cv =~= limit.
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

Lemma limD xn yn (x y: R_met):
  limit xn x -> limit yn y ->
  limit (ptw_op Rplus xn yn :nat -> R_met) (x + y).
Proof. by rewrite -Uncv_lim => lim lim'; apply/CV_plus. Qed.

Lemma limB xn yn (x y: R_met):
  limit xn x -> limit yn y ->
  limit (ptw_op Rminus xn yn :nat -> R_met) (x - y).
Proof. by rewrite -Uncv_lim => lim lim'; apply/CV_minus. Qed.

Lemma limM xn yn (x y: R_met):
  limit xn x -> limit yn y ->
  limit (ptw_op Rmult xn yn: nat -> R_met) (x * y).
Proof. by rewrite -Uncv_lim => lim lim'; apply/CV_mult. Qed.

Lemma lim_pos xn (x: R_met):
  limit xn x -> (forall n, 0 <= xn n) -> 0 <= x.
Proof.
  move => lim prp.
  suff: -x/2 <= 0 by lra.
  apply Rnot_lt_le => ineq.
  have [N cnd]:= lim _ ineq.
  have := cnd N (leqnn N); rewrite /=/R_dist/=.
  have := prp N; split_Rabs; lra.
Qed.

Lemma lim_inc xn yn x y:
  (forall i, xn i <= yn i) -> limit xn x -> limit yn y -> x <= y.
Proof.
  move => prp lim lim'.
  have ineq: forall i, 0 <= yn i - xn i by move => i; have:= prp i; lra.
  suff: 0 <= y - x by lra.
  exact/lim_pos/ineq/limB.
Qed.

Definition scale (r: R) x (n: nat) := (r * (x n)).

Lemma scale_ptw r: scale r =1 ptw_op Rmult (cnst r).
Proof. done. Qed.

Lemma lim_scale x r r': limit x r -> limit (scale r' x) (r' * r).
Proof.
  move => lim.
  rewrite scale_ptw.
  apply/limM/lim/lim_cnst.
Qed.