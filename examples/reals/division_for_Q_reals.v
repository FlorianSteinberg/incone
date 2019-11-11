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

  Lemma inv_sing: inversion \is_singlevalued.
  Proof.
    by move => x x' y /= eq eq'; rewrite -(Rmult_1_r x') -eq' -Rmult_assoc (Rmult_comm x') eq; lra.
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

  Lemma Rmin_leql x y: Rmin x y <= x.
  Proof.  by rewrite /Rmin; case: Rle_dec; lra. Qed.

  Lemma Rmin_leqr x y: Rmin x y <= y.
  Proof. by rewrite /Rmin; case: Rle_dec; lra. Qed.
  
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
    exists (Rinv x); split; try move  => eps eg0; try by rewrite /= Rinv_r.
    have [m /=]:= val eps; rewrite /RQinv_M; case: ifP => [/QleP /Qle_Rle /= | _]; try lra.
    set tpmm := ((/(1+1))^Z.of_nat m)%Q.
    set del := (Qabs (phi tpmm) - tpmm)%Q.
    case: ifP => //= /QleP tmp.
    have ineq': tpmm < \|phi tpmm|.
    - by rewrite -Qabs_Rabs; apply/Rnot_le_lt => tmp'; apply/tmp/Rle_Qle.
    move: tmp => _ [<-].
    set t := (Qmin (del/(1 + 1)) (eps * (del * del)/(1 + 1)))%Q.
    have del_pos: 0 < del by rewrite /del Q2R_minus Qabs_Rabs; lra.
    have tineq: 0 < t.
    - rewrite /t -Rmin_Qmin /Rmin.
      case: Rle_dec => _; first by rewrite Q2R_div; try rewrite {2}/Q2R /=; nra.
      rewrite !Q2R_mult Q2R_inv; try rewrite {4}/Q2R /= Rinv_1 Rmult_1_r; try nra.
      by apply/Rmult_lt_0_compat; try apply/Rmult_lt_0_compat; try nra.
    suff [xb pb]: del <= \|x| /\ del * /2 <= \|phi t|.
    - rewrite Q2R_inv; last move => /Qeq_eqR; try by split_Rabs; nra.
      have -> : /x - /phi t = (phi t - x)/ (phi t * x) by field; split_Rabs; nra.
      rewrite Rabs_mult Rabs_Rinv; try by split_Rabs; nra.
      rewrite Rabs_mult; apply/Rle_trans.
      + apply/Rmult_le_compat_r; first by apply/Rlt_le/Rinv_0_lt_compat; split_Rabs; nra.
      by rewrite Rabs_minus_sym; apply/phinx.
      suff tineq': t <= \| phi t| * \| x| * eps.
      + apply/Rle_trans.
        * by apply/Rmult_le_compat_r/tineq'/Rlt_le/Rinv_0_lt_compat; split_Rabs; nra.
        by rewrite (Rmult_comm _ eps) Rmult_assoc Rinv_r; split_Rabs; nra.
      apply/Rle_trans; first by rewrite/t -Rmin_Qmin; apply/Rmin_leqr.
      rewrite !Q2R_mult {4}/Q2R /=.
      by apply/Rle_trans/Rmult_le_compat_r/Rmult_le_compat/xb/pb; try lra.
    suff xgd: del <= \|x|.
    - split => //.
      have -> : Q2R (phi t) = x - (x - phi t) by lra.
      apply/Rle_trans/Rabs_triang_inv.
      suff: \|x - phi t| <= del * /2 by lra.
      apply/Rle_trans; first exact/phinx.
      rewrite /t -Rmin_Qmin; apply/Rle_trans; first exact/Rmin_leql.
      by rewrite Q2R_div; try rewrite {2}/Q2R /=; try lra.  
    have ->: x = phi tpmm - (phi tpmm - x) by lra.
    apply/Rle_trans/Rabs_triang_inv.
    rewrite /del Q2R_minus Qabs_Rabs Rabs_minus_sym.
    by apply/Rplus_le_compat_l/Ropp_le_contravar/phinx; rewrite -tpmn_Q; apply/tpmn_lt.
  Qed.
  
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

Section division.  
  Definition find_fraction := make_mf (fun xy z => xy.2 <> 0 /\ xy.2 * z = xy.1).

  Lemma ffr_dom x y: (x, y) \from dom find_fraction <-> y <> 0.
  Proof. by split => [[_ []] | neq]//; exists (x/y); split => //=; field. Qed.
    
  Lemma Rdiv_icf_ffr: (uncurry Rdiv) \is_choice_for find_fraction.
  Proof. by rewrite /uncurry; case => [x y] [z /=[neq eq]]; split => //; field. Qed.

  Lemma ffr_spec: find_fraction =~= (F2MF (uncurry Rmult)) \o (mf_id ** inversion).
  Proof.
    rewrite sing_rcmp; last exact/fprd_sing/inv_sing/F2MF_sing.
    move => [x y] z; split => [/= [neq eq] | [[_ yi] /= [[<- inv] <-]]]; last first.
    - split => [eq | ]; first by rewrite eq in inv; lra.
      by rewrite /uncurry/= (Rmult_comm x) -Rmult_assoc inv; lra.
    rewrite /uncurry /=.
    by exists (x, /y); split; first split => //=; last rewrite /= -eq; field.
  Qed.

  Lemma ffr_cont: find_fraction \has_continuous_solution.
  Proof.
    rewrite ffr_spec.
    apply/comp_hcs/Rmult_cont/fprd_hcs/inv_cont.
    by exists mf_id; split; try exact/id_cntop; apply/id_rlzr.
  Qed.
End division.
