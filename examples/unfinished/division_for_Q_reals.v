From mathcomp Require Import ssreflect seq ssrfun ssrbool ssrnat eqtype bigop.
From rlzrs Require Import all_rlzrs.
From metric Require Import all_metric reals standard Qmetric.
Require Import axioms all_cs cs_mtrc metric_names hyper_spaces Q_reals.
Require Import Qreals Reals Psatz ClassicalChoice FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import QArith.

Local Open Scope R_scope.
Section inversion.
  Definition inversion := make_mf (fun x y => x * y = 1).

  Lemma dom_inv: dom inversion === make_subset(fun x => x <> 0).
  Proof.
    move => x; split => [[y/= eq eq'] | /= neq]; first by rewrite eq' in eq; lra.
    by exists (Rinv x); rewrite Rinv_r.
  Qed.

  Lemma Rinv_spec: (fun x => Rinv x) \is_choice_for inversion.
  Proof.
    by move => x [y /=]; case: (total_order_T x 0) => [[?|{1 2}->]|?]; try rewrite Rinv_r; lra.
  Qed.

  Lemma Rabs_le_up x: \|x| <= \|up(x)| + 1.
  Proof. by have := archimed x; split_Rabs; lra. Qed.
  
  Lemma Rinv_not_cont: ~ (Rinv: RQ -> RQ) \is_continuous.
  Proof.
    move => /cont_scnt cont.
    have lim : limit (fun n => /2^n) 0.
    - apply/RQ_Rm_lim/lim_mlim/lim_tpmn => n; exists n => m ineq /=.
      by rewrite Rminus_0_l Rabs_Ropp Rabs_pos_eq; [apply/tpmnP | apply/tpmn_pos].
    move: lim => /cont/RQ_Rm_lim/lim_mlim/lim_tpmn lim.
    have [N Nprp]:= lim (0%nat); move: lim => _.
    set M := (Z_size (Z.abs (up (/0))))%nat.
    have := Nprp (maxn N M.+1).+1.
    rewrite /ptw /= Rinv_1 Rinv_involutive => [ineq | ]; last by have:=pow_lt 2 (maxn N M.+1); lra.
    suff: 1 < \| /0 - 2 ^ (maxn N M.+1).+1| by apply/Rle_not_lt/ineq/leqW/leq_maxl.
    rewrite -Rabs_Ropp Ropp_minus_distr.
    apply/Rlt_le_trans/Rabs_triang_inv.
    rewrite Rabs_pos_eq; last by apply/pow_le; lra.
    suff: 1 + \| /0 | < 2^(maxn N M.+1).+1 by have := pow_le 2 (maxn N M).+1; lra.
    rewrite -tech_pow_Rmult double.
    apply/Rplus_le_lt_compat; first by apply/pow_R1_Rle; lra.
    apply/Rle_lt_trans; first exact/Rabs_le_up.
    rewrite Rabs_Zabs.
    apply/Rlt_le_trans.
    apply/Rplus_lt_le_compat/Rle_refl/Z_size_lt.
    apply/Rle_trans/Rle_pow/leP/leq_maxr; try lra.
    rewrite -tech_pow_Rmult double.
    by apply/Rplus_le_compat/pow_R1_Rle; first exact/Rle_refl; lra.
  Qed.

  Definition Qmin r r':=
    match Qlt_le_dec r r' with
    | left _ => r
    | right _ => r'
    end.

  Lemma Rmin_Qmin (r r': Q): Rmin r r' = Qmin r r'.
  Proof.
    rewrite /Rmin /Qmin; symmetry.
    by case: (Qlt_le_dec r r') => [/Qlt_Rlt | /Qle_Rle]; case: (Rle_dec r r'); lra.
  Qed.
  
  Definition RQinv_M phi neps :=
    let n := neps.1 in
    let eps := neps.2 in
    let tpmn := ((/(1 + 1)) ^ (Z.of_nat n))%Q in
    let del := (Qabs (phi tpmn) - tpmn)%Q in
    if Qle_bool eps 0
    then Some 0%Q
    else if Qle_bool (Qabs (phi tpmn)) tpmn
         then None
         else Some (/(phi (Qmin (del/(1+1)) (eps * del^2/(1 + 1)))))%Q.

  Lemma Rabs0_dec x: decidable (0 < \|x|).
  Proof.
    case: (total_order_T x 0) => [[ | ->] | ]; try by left; split_Rabs; lra.
    right; split_Rabs; lra.
  Qed.

  Lemma QleP r q: reflect (Qle r q) (Qle_bool r q).
  Proof. by apply/(iffP idP) => /Qle_bool_iff //. Qed.
    
  Lemma inv_M_spec: \F_(RQinv_M) \solves inversion.
  Proof.
    move => phi x phinx /dom_inv neq; rewrite /= in neq; split => [ | Fphi val].
    - apply/FM_dom => eps.
      case eq: (Qle_bool eps 0).
      + by exists 0%Q; exists 0%nat; rewrite /RQinv_M; case: ifP => //=; rewrite eq //.
      have ineq: (0 < eps)%Q by apply Qnot_le_lt => /Qle_bool_iff; rewrite eq.
      case: (Rabs0_dec x) => xineq; last by split_Rabs; lra.
      have [n nineq]:= dns0_tpmn xineq.
      exists (
          let tpmn := ((/(1 + 1)) ^ (Z.of_nat n.+1))%Q in
          let del := (Qabs (phi tpmn) - tpmn)%Q in
          (/(phi (Qmin (del/(1+1)) (eps * del^2/(1 + 1)))))%Q).
      exists n.+1.
      rewrite /RQinv_M.
      have prp: ~ / (1 + 1) == 0 by move => /Qeq_eqR; rewrite /Q2R /=; lra.
      case: ifP => [ | _]; first by rewrite eq.
      case: ifP => // /QleP/Qle_Rle/Rle_not_lt fls; exfalso; apply/fls.
      rewrite Qabs_Rabs Qpower_spec // {1}/Q2R /= Rmult_1_l -Rinv_pow; try lra.
      apply/Rle_lt_trans.
      + by apply/Rmult_le_compat_l/Rlt_le/nineq/Rlt_le/Rinv_0_lt_compat; lra.
      set del:= Qpower_positive (/(1+1)) (Pos.of_succ_nat n).
      have ->: Q2R (phi del) = x - (x - phi del) by ring.
      apply/Rlt_le_trans/Rabs_triang_inv.
      suff: \|x - phi del| < /2 * \|x| by split_Rabs; lra.
      apply/Rle_lt_trans; first apply/phinx; have /= ->:= @Qpower_spec (/(1 + 1))%Q n.+1 => //.
      + apply/Rmult_lt_0_compat; rewrite /Q2R /=; try lra.
        by rewrite Rmult_1_l -Rinv_pow; try lra; exact/tpmn_lt.
      by rewrite /Q2R /= Rmult_1_l -Rinv_pow; try lra.
    case: (Rabs0_dec x) => [/dns0_tpmn [n ineq] | ]; last by split_Rabs; lra.
    exists (Rinv x); split => [eps eg0 | ]; last by rewrite /= Rinv_r; split_Rabs; lra.
    have [m /=]:= val eps; rewrite /RQinv_M; case: ifP => [/QleP /Qle_Rle /= | _]; try lra.
    set tpmm := ((/(1+1))^Z.of_nat m)%Q.
    set del := (Qabs (phi tpmm) - tpmm)%Q.
    case: ifP => //= /QleP tmp.
    have ineq': tpmm < \|phi tpmm|.
    - by rewrite -Qabs_Rabs; apply/Rnot_le_lt => tmp'; apply/tmp/Rle_Qle.
    move: tmp => _ [<-].    
    set r := (phi(Qmin (del /(1 + 1)) (eps * (del * del) / (1 + 1))))%Q.
    have tpmm_spec: / 2 ^ m = tpmm.
    - rewrite /tpmm Qpower_spec; last by rewrite /Qinv /=; lra.
      rewrite Q2R_inv /Q2R/=; try lra.
      by rewrite Rinv_1 Rmult_1_r -Rinv_pow; lra.
    have : 0 < tpmm by rewrite -tpmm_spec; apply/tpmn_lt.
    have neq' : 0 <> r.
    - rewrite /r.
      suff: \|x - phi (Qmin (del /(1 + 1)) (eps * (del * del)/(1 + 1)))| < \|x| by split_Rabs; nra.
      apply/Rle_lt_trans/ineq/Rle_trans; first apply/phinx.
      rewrite -Rmin_Qmin.
      rewrite /Rmin.
      case: Rle_dec.

  Admitted.
  
  Lemma M_cont: RQinv_M \is_continuous_functional.
  Proof.
    move => phi.
    exists (fun neps =>
              let tpmn := Qpower (/(1 + 1)) (Z.of_nat neps.1) in
              let delta := (Qabs (phi tpmn) - tpmn)%Q in
              [:: tpmn; Qmin (delta/(1+1)) (neps.2 * delta^2/(1 + 1))]%Q).
    by rewrite /RQinv_M => eps psi [-> [->]].
  Qed.

  Lemma inv_cont: inversion \has_continuous_realizer.
  Proof.
    exists (\F_(FMop.use_first RQinv_M)); split; try exact/sfrst_cntf_cont/M_cont.
    exact/tight_slvs/FMop.sfrst_spec/inv_M_spec.
  Qed.
End inversion.
