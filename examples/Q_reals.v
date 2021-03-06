From mathcomp Require Import ssreflect seq ssrfun ssrbool ssrnat eqtype.
From rlzrs Require Import all_rlzrs.
Require Import all_cs cs_mtrc.
From metric Require Import reals metric standard Qmetric.
Require Import Qreals Reals Psatz ClassicalChoice FunctionalExtensionality.
Require Import sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import QArith.
Local Open Scope R_scope.

Section reals_via_rational_approximations.
  Coercion Q2R: Q >-> R.
  Definition rep_RQ : (Q -> Q) ->> R := make_mf (
    fun phi x => forall eps, 0 < Q2R eps-> Rabs(x - Q2R(phi eps)) <= Q2R eps).

  Lemma rep_RQ_sur: rep_RQ \is_cototal.
  Proof.
    move => x; pose aprx (eps: Q) := (inject_Z (Int_part (x/eps)) * eps)%Q.
    exists aprx => eps eg0.
    have ->: (x - aprx eps) = (x/eps - Int_part (x/eps)) * eps.
    - by rewrite Q2R_mult {1}/Q2R/=; field; lra.
    have []:= base_Int_part (x/eps); intros.
    rewrite Rabs_mult !Rabs_pos_eq; try lra.
    by rewrite -[X in _ <= X]Rmult_1_l; apply/Rmult_le_compat; lra.
  Qed.

  Lemma rep_RQ_sing: rep_RQ \is_singlevalued.
  Proof.
    move => phi x x' phinx phinx'.
    apply/(cond_eq_f accf_Q2R_0) => eps eg0.
    rewrite /R_dist.
    set r := Q2R (phi (eps/(1 + 1))%Q); rewrite /R_dist.
    have ->: (x-x') = ((x-r) + (r-x')) by field.
    apply/Rle_trans/Rle_trans; first exact/Rabs_triang.
    - apply /Rplus_le_compat; last rewrite Rabs_minus_sym; [apply phinx | apply phinx'];
      rewrite Q2R_div; try lra; rewrite {2}/Q2R/=; lra.
    by rewrite Q2R_div; try lra; rewrite {2 4}/Q2R/=; lra.
  Qed.

  Canonical RQ_class:= @continuity_space.Class _ _ _
                         (interview.Mixin rep_RQ_sur) (dictionary.Mixin rep_RQ_sing)
                         (continuity_space.Mixin 0%Q 0%Q count.Q_count count.Q_count).
  Canonical RQ := continuity_space.Pack RQ_class.
  
  Section addition.
    Definition Ropp_rlzrf phi (eps: Q) := Qopp (phi eps).
    
    Definition Ropp_rlzr: questions RQ ->> questions RQ := F2MF Ropp_rlzrf.
    
    Lemma Ropp_rlzr_spec: Ropp_rlzr \realizes (F2MF Ropp: RQ ->> RQ).
    Proof.
      rewrite F2MF_rlzr_F2MF => phi x phinx eps epsg0 /=.
      by rewrite Q2R_opp; move: (phinx eps epsg0); split_Rabs; lra.
    Qed.

    Lemma Ropp_rlzr_cntop: Ropp_rlzr \is_continuous_operator.
    Proof.
        by rewrite cont_F2MF /Ropp_rlzrf => phi; exists (fun eps => [:: eps]) => psi q' [<-].
    Qed.
    
    Lemma Ropp_hcr: (F2MF Ropp: RQ ->> RQ) \has_continuous_realizer.
    Proof. exists Ropp_rlzr; split; [apply/Ropp_rlzr_spec | apply/Ropp_rlzr_cntop]. Qed.

    Lemma Ropp_cont: (Ropp: RQ -> RQ) \is_continuous.
    Proof. exact/Ropp_hcr. Qed.

    Definition Rplus_rlzrf phi (eps: Q) :=
      (lprj phi (eps/(1+1)) + rprj phi (Qdiv eps (1+1)))%Q.

    Definition Rplus_rlzr: questions (RQ \*_cs RQ) ->> questions RQ:= F2MF Rplus_rlzrf.

    Lemma Rplus_rlzr_spec:
      Rplus_rlzr \realizes (F2MF (fun x => Rplus x.1 x.2) : (RQ \*_cs RQ) ->> RQ).
    Proof.
      rewrite F2MF_rlzr_F2MF => phi x phinx eps eg0.
      rewrite /Rplus_rlzr Q2R_plus.
      set r := Q2R (lprj phi (Qdiv eps (1 + 1))).
      set q := Q2R (rprj phi (Qdiv eps (1 + 1))).
      have ->: (x.1 + x.2 - (r + q)) = (x.1 - r + (x.2 - q)) by field.
      apply/Rle_trans; first exact/Rabs_triang; rewrite -(eps2 (Q2R eps)).
      have eq: Q2R eps * / 2 = Q2R (eps / (1 + 1)).
      - by symmetry; rewrite Q2R_div; first rewrite {2}/Q2R/=; lra.
      by rewrite eq; apply: Rplus_le_compat; apply phinx; lra.
    Qed.

    Lemma Rplus_rlzr_cntop: Rplus_rlzr \is_continuous_operator.
    Proof.
      rewrite cont_F2MF => phi.
      exists (fun eps => [:: inl (Qdiv eps (1 + 1)); inr (Qdiv eps (1 + 1))]).
      by rewrite /Rplus_rlzrf/lprj/rprj => psi q' [-> [->]].
    Qed.

    Lemma Rplus_cont: (fun (xy: RQ \*_cs RQ) => xy.1 + xy.2: RQ) \is_continuous.
    Proof.
      exists Rplus_rlzr; split; [exact/Rplus_rlzr_spec | exact/Rplus_rlzr_cntop].
    Qed.
  End addition.

  Section multiplication.
(* Multiplication is more involved as the precision of approximations that have to be used
depends on the size of the inputs *)
    Let trunc eps:Q := if Qlt_le_dec eps 1 then eps else 1%Q.

    Lemma trunc_le eps: Q2R (trunc eps) <= Q2R eps.
    Proof.
        by rewrite /trunc; case: (Qlt_le_dec eps 1) => ass /=; [lra | apply Qle_Rle].
    Qed.

    Lemma truncI eps: 0 < Q2R eps -> 0 < Q2R (trunc eps) <= 1.
    Proof.
      rewrite /trunc; case: (Qlt_le_dec eps 1) => /= ass; last by rewrite /Q2R/=; lra.
      split => //; apply Rlt_le; replace 1 with (Q2R 1) by by rewrite /Q2R/=; lra.
      by apply Qlt_Rlt.
    Qed.

    Let rab := (fun (phi : Q -> Q) => inject_Z (up(Rabs(Q2R(phi (1#2)))+1))).

    Lemma rab_pos phi: 1 <= Q2R (rab phi).
    Proof.
      rewrite /Q2R/rab/=; rewrite Rinv_1 Rmult_1_r.
      apply: Rle_trans; last by apply Rlt_le; apply archimed.
        by rewrite -{1}(Rplus_0_l 1); apply Rplus_le_compat_r; exact: Rabs_pos.
    Qed.

    Lemma up_le r: up r <= r + 1.
    Proof. by have:= archimed r; lra. Qed.
    
    Lemma up_lt r : r < up r.
    Proof. by have:= archimed r; lra. Qed.

    Lemma rab_spec phi (x: RQ): phi \describes x \wrt RQ ->
                      Rabs x <= Q2R (rab phi).
    Proof.
      move => phinx.
      rewrite /rab{1}/Q2R/= Rinv_1 Rmult_1_r.
      apply/Rle_trans/Rlt_le/up_lt.
      suff: Rabs x - Rabs (Q2R (phi (1#2))) <= 1 by lra.
      apply/Rle_trans; first apply/Rabs_triang_inv.
      apply/Rle_trans; first apply/phinx; rewrite /Q2R/=; lra.
    Qed.
    
    Definition Rmult_rlzrf phi (eps: Q) :=
      (lprj phi (trunc eps / (1 + 1)/(rab (rprj phi)))
       *
       (rprj phi (eps / (1 + 1)/(rab (lprj phi)))))%Q.
    
    Definition Rmult_rlzr : questions (RQ \*_cs RQ) ->> questions RQ:= F2MF Rmult_rlzrf.
    
    Lemma Rmult_rlzr_spec:
      Rmult_rlzr \realizes (F2MF (fun x => Rmult x.1 x.2):RQ \*_cs RQ ->> RQ).
    Proof.
      rewrite F2MF_rlzr_F2MF => phi [x y] [phinx psiny] eps eg0 /=.
      rewrite Q2R_mult.
      set r := Q2R (lprj phi (trunc eps / (1 + 1) / rab (rprj phi))%Q).
      set q := Q2R (rprj phi (eps / (1 + 1) / rab (lprj phi))%Q).
      have g0: 0 < Q2R (eps / (1 + 1)) by rewrite Q2R_div; first rewrite {2}/Q2R/=; lra.
      have ->: (x * y - r * q) = ((x - r) * y + r * (y - q)) by field.
      have ->: (Q2R eps) = (Q2R (eps/ (1 + 1)) + Q2R (eps/ (1 + 1))).
      - by rewrite Q2R_div; first rewrite {3 5}/Q2R/=; lra.
      apply/Rle_trans/Rplus_le_compat; first exact/Rabs_triang.
      - rewrite Rabs_mult; have rab_pos:= (rab_pos (rprj phi)).
        case: (classic (y = 0)) => [eq | neq].
        + by apply/ Rle_trans; last apply/ Rlt_le /g0; rewrite eq Rabs_R0; lra.
        rewrite -[X in _ <= X]Rmult_1_r -(Rinv_l (Rabs y)); last by split_Rabs; lra.
        rewrite -Rmult_assoc; apply: Rmult_le_compat; try by split_Rabs; lra.
        have neq': ~ rab (rprj phi) == 0 => [/Qeq_eqR eq | ].
        + by have := rab_pos; rewrite eq /Q2R /=; lra.
        have le:= truncI eg0; apply/Rle_trans.
        + apply/phinx; rewrite Q2R_div; try lra.
          apply Rmult_gt_0_compat; last by apply Rlt_gt; apply Rinv_0_lt_compat; lra.
          by rewrite Q2R_div; first rewrite {2}/Q2R/=; try lra.
        rewrite Q2R_div// Q2R_div//Q2R_div// {2 5}/Q2R/=; try lra.
        have le':= trunc_le eps.
        apply/Rmult_le_compat; try lra.
        + by apply/Rlt_le/Rinv_0_lt_compat/Rlt_le_trans/rab_pos; lra.
        apply Rinv_le_contravar; first by split_Rabs; lra.
        exact /rab_spec.
      rewrite Rabs_mult; case: (classic (r = 0)) => [eq | neq].
      - by apply/ Rle_trans; [rewrite eq Rabs_R0 | apply/ Rlt_le/ g0]; lra.
      rewrite /Qdiv -(Rmult_1_l (Q2R (eps / (1 + 1)))).
      rewrite -(Rinv_r (Rabs r)); last by split_Rabs; lra.
      rewrite Rmult_assoc; apply: Rmult_le_compat; try by split_Rabs; lra.
      have neq': ~ rab (lprj phi) == 0 => [/Qeq_eqR eq | ].
      - by have := rab_pos (lprj phi); rewrite eq /Q2R /=; lra.
      rewrite Rmult_comm; apply/ Rle_trans; first apply psiny.
      - suff lt: 0 < / Q2R (rab (lprj phi)).
        + by rewrite Q2R_div /Rdiv; first apply/Rmult_lt_0_compat; lra.
        by apply/Rinv_0_lt_compat/Rlt_le_trans/rab_pos; lra.
      rewrite Q2R_div; try lra.
      rewrite /Rdiv; apply Rmult_le_compat_l; try lra.
      apply Rle_Rinv; first exact: Rabs_pos_lt; try lra.
      - rewrite /rab {1}/Q2R/= Rinv_1 Rmult_1_r.
        apply/Rle_lt_trans/(archimed (Rabs (Q2R (lprj phi (1 # 2)))+1)).1.
        by have:= Rabs_pos (Q2R (lprj phi (1#2))); lra.
      rewrite /rab{1}/Q2R/= Rinv_1 Rmult_1_r.
      apply/Rle_trans/Rlt_le/(archimed (Rabs (Q2R (lprj phi (1 # 2)))+1)).1.
      suffices: (Rabs r - Rabs (Q2R (lprj phi (1#2))) <= 1) by lra.
      apply/ Rle_trans; first exact/Rabs_triang_inv.
      have ->: (r - Q2R (lprj phi (1#2))) = ((r - x) - (Q2R (lprj phi (1#2)) - x)) by field.  
      apply/Rle_trans/Rle_trans; first exact/Rabs_triang.
      - apply/Rplus_le_compat; last rewrite Rabs_Ropp.
        + rewrite Rabs_minus_sym; apply/phinx.
          rewrite Q2R_div; first rewrite  /Qdiv Q2R_mult; first apply/Rmult_lt_0_compat.
          * by rewrite {2}/Q2R/=; have := truncI eg0; lra.
          * by apply/Rinv_0_lt_compat/Rlt_le_trans/rab_pos; lra.
          by move => /Qeq_eqR eq; have := rab_pos (rprj phi); rewrite eq /Q2R /=; lra.
        by rewrite Rabs_minus_sym; apply/phinx; rewrite /Q2R/=; lra.
      have rps:= rab_pos (rprj phi).
      apply/Rle_trans.
      - apply/Rplus_le_compat_r; rewrite/Rdiv.
        rewrite Q2R_div => [ | /Qeq_eqR eq]; last by rewrite /Q2R /=; lra.
        apply/Rmult_le_compat_l/Rinv_le_contravar/rab_pos; try lra.
        by have:= truncI eg0; rewrite /Qdiv Q2R_mult {4}/Q2R/=; lra.
      by rewrite Rinv_1 Rmult_1_r /Qdiv Q2R_mult {2 3}/Q2R/=; have:= truncI eg0; lra.
    Qed.

    Lemma Rmult_rlzr_cntop: Rmult_rlzr \is_continuous_operator.
    Proof.
      apply/cont_F2MF => phi; rewrite /Rmult_rlzrf /=.
      exists (fun eps => [:: inl (1 # 2); inr (1 # 2);
                          inl (trunc eps / (1 + 1) / rab (rprj phi))%Q;
                          inr (eps / (1 + 1) / rab (lprj phi))%Q]).
      by rewrite /rab/lprj/rprj => eps psi [-> [-> [-> [->]]]].
    Qed.  

    Lemma Rmult_cont: (fun (xy: RQ \*_cs RQ) => xy.1 * xy.2: RQ) \is_continuous.
    Proof.
      by exists Rmult_rlzr; split; [apply/Rmult_rlzr_spec | apply/Rmult_rlzr_cntop].
    Qed.
  End multiplication.

  Section limit.
    Notation lim:= (@limit metric_R: RQ\^w ->> RQ).
    Notation lim_eff:= (@efficient_limit metric_R: RQ\^w ->> RQ).

    Lemma cnst_dscr q: (cnst q) \describes (Q2R q) \wrt RQ.
    Proof. rewrite /cnst => eps; split_Rabs; lra. Qed.

    Lemma cnst_sqnc_dscr q: (cnst q) \describes (cnst (Q2R q)) \wrt (RQ\^w).
    Proof. rewrite /cnst => n eps ineq; split_Rabs; lra. Qed.

    Lemma Q_sqnc_dscr qn:
      (fun neps => qn neps.1) \describes (fun n => Q2R (qn n)) \wrt (RQ\^w).
    Proof. move => n eps ineq /=; split_Rabs; lra. Qed.

    Lemma lim_cnst x: lim (cnst x) x.
    Proof. exists 0%nat; rewrite /cnst/distance/=/R_dist; split_Rabs; lra. Qed.

    Local Open Scope baire_scope.
    Lemma lim_not_cont: ~ lim \has_continuous_realizer.
    Proof.
      move => [/= F [/= rlzr /cont_spec cont]].
      pose xn := cnst (Q2R 0): RQ\^w.
      have limxn0: lim xn (Q2R 0) by exists 0%nat; rewrite /xn/cnst/distance/=/R_dist; split_Rabs; lra.
      have qnfdF: cnst 0%Q \from dom F.
      - by apply /(rlzr_dom rlzr); [exact/cnst_sqnc_dscr | exists (Q2R 0)].
      have [Lf Lmod]:= cont (cnst 0%Q) qnfdF.
      set fold := @List.fold_right nat nat.
      pose L := Lf 1%Q.
      pose m:= fold maxn 0%N (unzip1 L).
      have mprop: forall n eps, List.In (n, eps) L -> (n <= m)%nat.
      - rewrite /m; elim: {1 2}L => // a K ih n eps /=.
	by case =>[-> | ineq]; apply/leq_trans; [ | apply/leq_maxl | apply/ih/ineq | apply/leq_maxr].
      pose yn:= (fun n => Q2R (if (n <= m)%nat then 0%Q else 3#1)): RQ\^w.
      pose rn (p: nat * Q) := if (p.1 <= m)%nat then 0%Q else 3#1.
      have rnyn: rn \describes yn \wrt (RQ\^w) by apply/Q_sqnc_dscr.
      have limyn3: lim yn 3.
      - exists (S m) => n /leP ineq; rewrite /yn.
        by case: ifP => [/leP ineq' | ]; [lia | rewrite /distance/=; split_Rabs; lra].
      have [phi Frnphi]: rn \from dom F by apply /(rlzr_dom rlzr); first exact/rnyn; exists 3.
      have coin: (cnst 0%Q) \and rn \coincide_on L.
      - apply /coin_lstn => [[n eps] listin].
        rewrite /cnst /rn; case: ifP => // /= /leP ineq.
        by exfalso; apply/ineq/leP/mprop/listin.
      have [psi Fqnpsi]:= qnfdF.
      have eq: psi 1%Q == phi 1%Q.
      - have [a' crt]:= Lmod 1%Q; rewrite (crt rn coin phi)// (crt (cnst 0%Q) _ psi) //.
        exact/coin_ref.
      have := Qeq_eqR (psi 1%Q) (phi 1%Q) eq.
      have psin0: psi \describes 0 \wrt ( RQ).
      - apply /(rlzr_val_sing _ rlzr)/Fqnpsi/lim_cnst; first exact/lim_sing.
        by rewrite /cnst/=/Q2R /=; split_Rabs; lra.
      have phin3: phi \describes 3 \wrt RQ.
      - by apply/(rlzr_val_sing _ rlzr)/Frnphi/limyn3; first exact/lim_sing.
      have l01: 0 < Q2R 1 by rewrite /Q2R/=; lra.
      have:= psin0 1%Q l01; have:= phin3 1%Q l01.
      by rewrite {2 4}/Q2R/=; split_Rabs; lra.
    Qed.
    Local Close Scope baire_scope.
    
    Definition lim_eff_rlzrf phin eps :=
      phin ((Pos_size (Qden eps)).+1, (eps * (1#2))%Q): Q.
    
    Definition lim_eff_rlzr : questions (RQ\^w) ->> questions RQ := F2MF lim_eff_rlzrf.
    
    Lemma lim_eff_rlzr_spec:
      lim_eff_rlzr \realizes lim_eff.
    Proof.
      rewrite F2MF_rlzr => psi xn psinxn [x lim].
      exists x; split => // eps epsg0.
      set N:= (Pos_size (Qden eps)).
      have ->: x - Q2R (lim_eff_rlzrf psi eps) = x - (xn N.+1) + (xn N.+1 - Q2R (lim_eff_rlzrf psi eps)) by lra.
      rewrite /lim_eff_rlzrf -/N.
      apply/Rle_trans/Rle_trans; first exact/Rabs_triang.
      - apply/Rplus_le_compat; first exact/lim.
        by apply psinxn; rewrite Q2R_mult {2}/Q2R/=; lra. 
      have lt1:= pow_lt 2 (Pos_size (Qden eps)); have lt2:= size_Qden epsg0.
      by rewrite Q2R_mult {2}/Q2R /= /N Rinv_mult_distr; lra.
    Qed.

    Lemma lim_eff_rlzr_cntop : lim_eff_rlzr \is_continuous_operator.
    Proof.
      apply/cont_F2MF => phi; rewrite /lim_eff_rlzrf.
      by exists (fun eps => [:: ((Pos_size (Qden eps)).+1, (eps * (1#2))%Q)]) => eps psi [].
    Qed.

    Lemma lim_eff_hcr: lim_eff \has_continuous_realizer.
    Proof.
      by exists lim_eff_rlzr; split; [apply/lim_eff_rlzr_spec | apply/lim_eff_rlzr_cntop].
    Qed.
  End limit.
End reals_via_rational_approximations.

Section metric_Qreals.
  Local Open Scope R_scope.
  Notation subset := mf_subset.type.
  Context (r: nat -> Q).
  Hypothesis r_dense: dense_sequence (Q2R \o_f r: nat -> R_met).
  
  Definition Rm := metric_cs r_dense.
  Definition Rm2RQ_rlzrf phi eps := r (phi (Pos_size (Qden eps))).

  Lemma Rm2RQ_rlzr_cntop: (Rm2RQ_rlzrf \is_continuous_function)%baire.
  Proof.
  move => phi; exists (fun eps => [:: Pos_size (Qden eps)]).
  by rewrite /Rm2RQ_rlzrf => eps psi [->].
  Qed.

  Lemma Rm2RQ_rlzrf_spec:
    (F2MF Rm2RQ_rlzrf: questions Rm ->> questions RQ) \realizes mf_id.
  Proof.
    apply/F2MF_rlzr_F2MF => phi x phinx eps eg0.
    rewrite /Rm2RQ_rlzrf.
    apply/Rle_trans; first exact/phinx.
    exact/size_Qden.
  Qed.

  Lemma Rm2RQ_cont:
    (id: Rm -> RQ) \is_continuous.
  Proof.
    exists (F2MF Rm2RQ_rlzrf).
    split; first exact Rm2RQ_rlzrf_spec.
    exact/cont_F2MF/Rm2RQ_rlzr_cntop.
  Qed.  
End metric_Qreals.  