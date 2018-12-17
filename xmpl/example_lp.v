Require Import Reals Qreals Psatz Classical FunctionalExtensionality.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import all_cs reals Q_reals mtrc mreals Rstruct.
From Coquelicot Require Import Hierarchy.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope R_scope.
Import GRing.Theory.

Section lp.
  Context (p: R).
  Notation limit := (@limit R_met).

  Definition Rpow x p := if eqr x 0 then 0 else Rpower x p.

  Lemma Rpow_pos x q: 0 <= Rpow x q.
  Proof.
    rewrite /Rpow; case: ifP => [eq | ineq]; first exact/Rle_refl.
    by rewrite/Rpower; apply/Rlt_le/exp_pos.
  Qed.
  
  Definition p_norm_seq x n := \sum_(0 <= i < n) Rpow (Rabs (x i)) p.

  Lemma pnrms_grw x: Un_growing (p_norm_seq x).
  Proof.
    move => n; have := Rpow_pos (Rabs (x n)) p.
    by rewrite /p_norm_seq big_nat_recr/= /GRing.add/= //; lra.
  Qed.

  Lemma pnrms_pos x i: 0 <= p_norm_seq x i.
  Proof.
    elim: i => [ | i ih].
    rewrite /p_norm_seq big_nil; exact/Rle_refl.
    exact/Rle_trans/pnrms_grw.
  Qed.
    
  Definition pow_p_norm := limit \o (F2MF p_norm_seq).
  
  Lemma ppnrm_lim x: pow_p_norm x ===
     limit (fun n => \sum_(0 <= i < n) Rpow (Rabs (x i)) p).
  Proof. by rewrite /pow_p_norm comp_F2MF. Qed.

  Lemma ppnrm_sing : pow_p_norm \is_singlevalued.
  Proof. exact/comp_sing/F2MF_sing/lim_sing. Qed.  

  Lemma ppnrm_pos x r: pow_p_norm x r -> 0 <= r.
  Proof.
    by move => nrm; apply/lim_pos/pnrms_pos/x; rewrite -ppnrm_lim.
  Qed.
  
  Lemma Rpow_inv x q: q <> 0 -> 0 <= x -> Rpow (Rpow x (/q)) q = x.
  Proof.
    move => neg ineq.
    rewrite /Rpow.
    case E: (eqr x 0).
    move: E => /eqP E.
    by case: ifP => /eqP neq.
    move: E => /eqP E.
    case: ifP => /eqP.
    rewrite /Rpower => eq.
    suff : 0 < 0 by lra.
    rewrite -{2}eq.
    apply/exp_pos.
    move => ineq'.
    rewrite /Rpower.
    rewrite ln_exp -Rmult_assoc Rinv_r//.
    rewrite Rmult_1_l exp_ln; lra.
  Qed.

  Definition p_norm:= make_mf (fun x r =>
    (exists s, pow_p_norm x s) /\ forall s, pow_p_norm x s ->
               (s = 0 -> r = 0) /\ (0 < s -> r = Rpow s (/p))).
  
  Lemma pnrm_pos x r: p <> 0 -> p_norm x r -> 0 <= r.
  Proof.
    move => neg [[s val] prp].
    have []:= prp s val.
    have : 0 <= s by apply/ppnrm_pos/val.
    case => [ineq _ imp | ineq imp _]; last by rewrite imp //; apply/Rle_refl.
    by rewrite imp//; apply/Rpow_pos.
  Qed.
  
  Lemma dom_pnrm: p <> 0 -> dom p_norm === dom pow_p_norm.
  Proof.
    move => neq x.
    split => [[r [[s val]]] | [r nrm]]; first by exists s.    
    case: (ppnrm_pos nrm) => [ineq | eq].
    - exists (Rpow r (/p)).
      split => [ | s nrm']; first by exists r.
      split => [eq | ineq']; last by rewrite (ppnrm_sing nrm nrm').
      by rewrite (ppnrm_sing nrm nrm') in ineq; lra.
    exists 0; split => [ | s nrm']; first by exists r.
    by split => //; rewrite (ppnrm_sing nrm' nrm) -eq; lra.
  Qed.
         
  Context (p_norm_f: (nat -> R) -> R).
  Hypothesis p_norm_spec: p_norm_f \is_choice_for p_norm.

  Notation "\| x \|_p" := (p_norm_f x) (format "'\|' x '\|_p'").
  
  Notation "x + y" := (ptwn_op Rplus x y).

  Definition RN_AbelianGroup_mixin: AbelianGroup.mixin_of (nat -> R).
  Proof.
    exists (ptwn_op Rplus) (ptwn Ropp) (cnst 0).
    exact/ptwC/Rplus_comm.
    by apply/ptwA => x y z; rewrite Rplus_assoc.
    move => x; apply/functional_extensionality => n.
    by rewrite /ptw_op/cnst/= Rplus_0_r.
    move => x; apply/functional_extensionality => n.
    by rewrite /ptw/ptw_op/cnst /= Rplus_opp_r.
  Defined.

  Definition RN_AbelianGroup: AbelianGroup :=
    AbelianGroup.Pack (nat -> R) RN_AbelianGroup_mixin (nat -> R).

  Definition scale (r: R) x (n: nat) := (r * (x n)).

  Lemma scale_ptw r: scale r =1 ptw_op Rmult (cnst r).
  Proof. done. Qed.

  Lemma lim_scale x r r': limit x r -> limit (scale r' x) (r' * r).
  Proof.
    move => lim.
    rewrite scale_ptw.
    apply/limM/lim/lim_cnst.
  Qed.

  Definition RN_ModuleSpace_mixin:
    ModuleSpace.mixin_of R_Ring RN_AbelianGroup.
  Proof.
    exists scale.
    move => r r' x; apply/functional_extensionality => n.
    by rewrite /scale/mult/= Rmult_assoc.
    move => x; apply/functional_extensionality => n.
    by rewrite /scale/one/= Rmult_1_l.
    move => r x y; apply/functional_extensionality => n.
    by rewrite /scale/plus/=/ptw_op Rmult_plus_distr_l.
    move => r r' x; apply/functional_extensionality => n.
    by rewrite /scale/plus/= Rmult_plus_distr_r.
  Qed.

  Lemma Rpow_mult x y q: 0 <= x -> 0 <= y -> Rpow (x * y) q = Rpow x q * Rpow y q.
  Proof.
    move => [ineq | <-]; last first.
    - rewrite {2}/Rpow Rmult_0_l; case: ifP => /eqP eq//.
      by rewrite {1}/Rpow; case: ifP => /eqP//; rewrite Rmult_0_l.
    move => [ineq' | <-]; last first.
    - rewrite {3}/Rpow Rmult_0_r; case: ifP => /eqP eq//.
      by rewrite {1}/Rpow; case: ifP => /eqP//; rewrite Rmult_0_r.
    rewrite /Rpow.
    case: ifP => /eqP eq; first by case: (Rmult_integral _ _ eq); lra.
    case: ifP => /eqP; try lra; case: ifP => /eqP; try lra.
    by rewrite Rpower_mult_distr.
  Qed.
    
  Lemma pnrms_scale x r': 
    p_norm_seq (scale r' x) = scale (Rpow (Rabs r') p) (p_norm_seq x).
  Proof.
    apply/functional_extensionality => n.
    elim: n => [ | n].
    - by rewrite /scale /p_norm_seq !big_nil Rmult_0_r.
    rewrite /scale/p_norm_seq !big_nat_recr/= // => ->.
    rewrite Rmult_plus_distr_l.
    by rewrite Rabs_mult Rpow_mult //; apply/Rabs_pos.
  Qed.

  Lemma ppnrm_scale x r r':
    pow_p_norm x r -> pow_p_norm (scale r' x) (Rpow (Rabs r') p * r).
  Proof.
    move => nrm; rewrite ppnrm_lim.
    have := pnrms_scale x r'.
    rewrite {1}/p_norm_seq => ->.
    apply/limM; first exact/lim_cnst.
    by rewrite -ppnrm_lim.
  Qed.

  Lemma Rpow_eq0 r q: Rpow r q = 0 ->  r = 0.
  Proof.
    rewrite /Rpow; case: ifP =>/eqP // _.
    rewrite /Rpower; have := exp_pos (q * ln r); lra.
  Qed.
  
  Lemma pnrm_hom x r r': 
    p <> 0 -> p_norm x r -> p_norm (scale r' x) ((Rabs r') * r).
  Proof.
    move => neq [[s nrm] prp].
    case: (ppnrm_pos nrm) => [ineq | eq].
    - split => [ | s' nrm'].
      + by exists (Rpow (Rabs r') p * s); apply ppnrm_scale.
      have nrm'':= ppnrm_scale r' nrm.
      rewrite (ppnrm_sing nrm' nrm'').
      split => [eq | ineq'].
      + case: (Rmult_integral _ _ eq) => eq'; try lra.
        by have -> := Rpow_eq0 eq'; rewrite Rmult_0_l.
      rewrite Rpow_mult; try lra; last exact/Rpow_pos.
      rewrite -{1}(Rinv_involutive p)//.
      rewrite Rpow_inv; try exact/Rabs_pos; try by apply/Rinv_neq_0_compat.
      by f_equal; have [_ ->]:= prp s nrm.
    split => [ | s' nrm'].
    - by exists (Rpow (Rabs r') p * s); apply/ppnrm_scale.
    split => [eq' | ]; first by have [->]:= prp s nrm; rewrite // Rmult_0_r.
    rewrite {2}(ppnrm_sing nrm' (ppnrm_scale r' nrm)).
    rewrite Rpow_mult; try lra; last exact/Rpow_pos.
    rewrite -{1}(Rinv_involutive p) // Rpow_inv; last exact/Rabs_pos.
    - move => ineq; f_equal; have [-> // _]:= prp s nrm.
      by rewrite -eq /Rpow; case: ifP => /eqP //.
    by apply/Rinv_neq_0_compat.
  Qed.
    
  Lemma grwD x y: Un_growing x -> Un_growing y -> Un_growing (x + y).
  Proof.
    move => grw grw' n; exact/Rplus_le_compat/grw'/grw.
  Qed.
  
  Notation "x - y" := (ptwn_op Rminus x y).

  Lemma lim_inc xn yn x y:
    (forall i, xn i <= yn i) -> limit xn x -> limit yn y -> x <= y.
  Proof.
    move => prp lim lim'.
    have ineq: forall i, 0 <= yn i - xn i by move => i; have:= prp i; lra.
    suff: 0 <= y - x by lra.
    exact/lim_pos/ineq/limB.
  Qed.

  Lemma pnrms_leq x r i:
    pow_p_norm x r -> p_norm_seq x i <= r.
  Proof.
    move => nrm; exact/growing_ineq/Uncv_lim/ppnrm_lim/nrm/pnrms_grw.
  Qed.

  Definition Nrm2Metr (N: NormedModule R_AbsRing): Metric_Space.
  Proof.
    exists N (fun x y => norm (minus x y)).
    by move => x y; apply/Rle_ge/norm_ge_0.
    by move => x y; rewrite -norm_opp opp_minus.
    Search _ NormedModule.
    move => x y; split => [eq | <-].

    have:= norm_eq_zero _ eq.
    
    admit.
    by rewrite minus_eq_zero norm_zero.
    move => x y z.
    suff ->: minus x y = plus (minus x z) (minus z y) by apply/norm_triangle.
    rewrite {2 3}/minus.
    by rewrite plus_assoc -(plus_assoc x) plus_opp_l plus_zero_r.
  Admitted.

    
  Lemma pnrms_bnd x y:
    has_ub (p_norm_seq x) -> has_ub (p_norm_seq y) ->
    has_ub (p_norm_seq (x + y)).
  Proof.
    move => [ub iub] [ub' iub'].    
    
    exists 

    
  Lemma pdomD x y:
    x \from dom p_norm -> y \from dom p_norm -> (x + y) \from dom p_norm.
  Proof.
    move => [r nrm] [r' nrm'].
    have []:= growing_cv (p_norm_seq (x - y)).
    exact/pnrms_grw.
    rewrite pnrm_Uncv.
    apply growing_cv
    apply/R_cmplt => eps eg0.
    have e2g0: 0 < eps/2 by lra.
    have [N prp]:= nrm (eps/2) e2g0.
    have [N' prp']:= nrm (eps/2) e2g0.
    exists (maxn N N') => n m ineq ineq'.
    rewrite /= /R_dist.
    
    
    Search _ Rpower.
  Notation "x - y" := (ptwn_op Rminus x y).    

  Definition lp_met : Metric_Space.
  Proof.
    exists (dom p_norm) (fun (x y: dom p_norm) => \|projT1 x - projT1 y\|_p).
    move => [x [r lmt]] [y [r' lmt']] /=.
    apply/Rle_ge.
    apply/lim_pos.
    apply/p_norm_spec.

    rewrite lim_cs_lim.
    move => eps eg0.
    
    
  Definition e i: RQ\^w:= fun j => if (i == j)%nat then R1 else R0. 

  Definition init_seg x n:= (fun k => if (k < n)%nat then x k else R0).
  
  Definition rep_lp := make_mf (fun phimu (xn: dom p_norm) =>
    (lprj phimu) \is_description_of (projT1 xn)
    /\
    forall n, \|fun k => \sum_(rprj phimu n <= k < n) Rpower (Rabs (projT1 xn k)) p\|_p <= /2^n).
    
  Lemma rep_lp_sur: rep_lp \is_cototal.
  Proof.
    move => [xn [r nrm]] /=.
    have [phi phinxn] := get_description xn.
    have: forall n, exists mun, forall r,
            lim (fun k => \sum_(mun <= i < n) Rpower (Rabs (xn i)) p) r -> r <= /2^n.
    move => n.
    