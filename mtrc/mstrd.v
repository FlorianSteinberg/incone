(* Proofs that the structures introduced on metric spaces coincide with
the corresponding ones from the standard library. *)
From mathcomp Require Import ssreflect ssrnat ssrbool ssrfun.
From rlzrs Require Import all_mf.
Require Import reals mtrc cprd sub.
Require Import Reals Ranalysis Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope R_scope.

Local Open Scope metric_scope.

Definition M_S2MS_mixin (M: Metric_Space): MetricSpace.mixin_of (Base M).
  apply/(MetricSpace.Mixin _ (dist_sym M) _ _ (dist_tri M)).
  by move => x y; apply/Rge_le/dist_pos.
  by move => x; rewrite dist_refl.
  by move => x y eq; apply/dist_refl.
Defined.

Canonical M_S2MS (M: Metric_Space): MetricSpace := MetricSpace.Pack (M_S2MS_mixin M) (Base M).

Definition MS2M_S (M: MetricSpace): Metric_Space.
  exists M d.
  by move => x y; apply/Rle_ge/dst_pos.
  exact/dst_sym.
  move => x y; split => [eq | ->].
  - exact/dst_eq.
  exact/dstxx.
  move => x y; exact/dst_trngl.
Defined.

Canonical MS2M_Sc M := MS2M_S M.

(* This does not ues the function above to remove the necessity to rewrite /R_dist everytime. *)
Definition R_MetricSpace_mixin: MetricSpace.mixin_of R.
  apply/(@MetricSpace.Mixin _ (fun x y => Rabs (x - y)) _ (dist_sym R_met) _ _ (dist_tri R_met)).
  by intros; apply/Rge_le/(dist_pos R_met).
  by intros; apply/(dist_refl R_met).
  by intros; apply/(dist_refl R_met).
Defined.  

Canonical metric_R:= MetricSpace.Pack R_MetricSpace_mixin (Base R_met).

Lemma Uncv_lim: make_mf Un_cv =~= limit.
Proof.
  move => xn x; split => ass eps epsg0.
  have [N Nprp]:= ass eps epsg0; exists N => n ineq.
  apply/Rlt_le; rewrite /distance /= Rabs_minus_sym.
    by rewrite /R_dist in Nprp; apply /Nprp/leP.
  have [ | N Nprp]:= ass (eps/2); try lra; exists N => n ineq.
  rewrite /R_dist Rabs_minus_sym; apply /Rle_lt_trans; first by apply /Nprp /leP.
  lra.
Qed.

Lemma cchy_crit: Cauchy_sequence === make_subset Cauchy_crit.
Proof.
  move => xn; split => cchy eps epsg0.
  - have [ | N prp]:= cchy (eps/2); first by rewrite /Rdiv; lra.
    exists N => n m /leP ineq /leP ineq'.
    by apply/Rle_lt_trans; first apply/prp => //; rewrite /Rdiv; lra.
  have [N prp]:= cchy eps epsg0.
  by exists N; intros; apply/Rlt_le/prp/leP; first apply/leP.
Qed.

Lemma R_cmplt: complete metric_R.
Proof.
  move => xn /cchy_crit cchy.
  have [x /Uncv_lim lim]:= R_complete xn cchy.
  by exists x.
Qed.

Definition subspace_class (M: MetricSpace) (A: subset M): MetricSpace.mixin_of A.
  exists (fun x y => d (sval x) (sval y)).
  - by move => x y; apply/dst_pos.
  - by move => x y; apply/dst_sym.
  - by move => x; apply/dstxx.
  - by move => x y dst; apply/eq_sub/dst_eq.
  - by move => x y z; apply/dst_trngl.
Defined.

Canonical subspace (M: MetricSpace) (A: subset M):= MetricSpace.Pack (subspace_class A) A.

Lemma cntp_limin (M N: MetricSpace) (f: M -> N) x:
  continuity_point f x <-> limit_in (MS2M_S M) (MS2M_S N) f All x (f x).
Proof.
  split => [cont eps eg0 | lmt eps eg0].
  - have e2g0: 0 < eps/2 by lra.
    have [delta [dg0 prp]]:= cont (eps/2) e2g0.
    exists delta; split => // x' [_ dst].
    apply/Rle_lt_trans.
    + rewrite /dist /= dst_sym; apply/prp/Rlt_le.
      by rewrite dst_sym; apply/dst.
    lra.
  have [delta [dg0 prp]]:= lmt eps eg0.
  exists (delta/2); split; first lra; move => y dst.
  rewrite dst_sym; apply/Rlt_le.
  by apply/prp; split => //; rewrite /dist /= dst_sym; lra.
Qed.

Lemma cont_limin (M N: MetricSpace) (A: subset M) (f: M -> N) (x: A):
  continuity_point (fun (x': A) => f (projT1 x')) x <-> limit_in (MS2M_S M) (MS2M_S N) f A (projT1 x) (f (projT1 x)).
Proof.
  split => [cont eps eg0 | lmt eps eg0].
  - have e2g0: 0 < eps/2 by lra.
    have [delta [dg0 /=prp]]:= cont (eps/2) e2g0.
    exists delta; rewrite /dist/=.
    split => // y [Ay dst]; apply/Rle_lt_trans.
    + rewrite dst_sym; have ->: y = sval (exist _ _ Ay) by trivial.
      by apply/prp; rewrite dst_sym; apply/Rlt_le.
    lra.
  have [delta [dg0 /=prp]]:= lmt eps eg0.
  exists (delta/2); split; first lra; move => [y Ay]; rewrite {1}/d /= => dst.
  apply/Rlt_le; rewrite dst_sym; apply/prp.
  split => //=; rewrite dst_sym.
  by apply/Rle_lt_trans; first exact/dst; lra.
Qed.

Lemma limD xn yn x y:
  limit xn x -> limit yn y ->
  limit (ptw_op Rplus xn yn :nat -> R_met) (x + y).
Proof. by rewrite -Uncv_lim => lim lim'; apply/CV_plus. Qed.

Lemma limB xn yn x y:
  limit xn x -> limit yn y ->
  limit (ptw_op Rminus xn yn :nat -> R_met) (x - y).
Proof. by rewrite -Uncv_lim => lim lim'; apply/CV_minus. Qed.

Lemma limM xn yn x y:
  limit xn x -> limit yn y ->
  limit (ptw_op Rmult xn yn: nat -> R_met) (x * y).
Proof. by rewrite -Uncv_lim => lim lim'; apply/CV_mult. Qed.

Lemma lim_pos xn x:
  limit xn x -> (forall n, 0 <= xn n) -> 0 <= x.
Proof.
  move => lim prp.
  suff: -x/2 <= 0 by lra.
  apply Rnot_lt_le => ineq.
  have [N cnd]:= lim _ ineq.
  have := cnd N (leqnn N); rewrite /distance /=.
  by have := prp N; split_Rabs; lra.
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