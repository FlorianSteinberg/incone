Require Import Reals Qreals Psatz Classical FunctionalExtensionality.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import all_cs reals Q_reals mtrc mreals Rstruct.
From Coquelicot Require Import Coquelicot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope R_scope.
Import GRing.Theory.

Section RN.
  Notation "x + y" := (ptwn_op Rplus x y).

  Definition RN_AbelianGroup_mixin: AbelianGroup.mixin_of (nat -> R).
  Proof.
    exists (ptwn_op Rplus) (ptwn Ropp) (cnst 0); first exact/ptwC/Rplus_comm.
    - by apply/ptwA => x y z; rewrite Rplus_assoc.
    - move => x; apply/functional_extensionality => n.
      by rewrite /ptw_op/cnst/= Rplus_0_r.
    - move => x; apply/functional_extensionality => n.
      by rewrite /ptw/ptw_op/cnst /= Rplus_opp_r.
  Defined.

  Definition RN_AbelianGroup: AbelianGroup :=
    AbelianGroup.Pack (nat -> R) RN_AbelianGroup_mixin (nat -> R).

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
  Defined.

  Definition RN_ModuleSpace_class:
    ModuleSpace.class_of R_Ring RN_AbelianGroup.
  Proof.
    exists (RN_AbelianGroup_mixin).
    apply/RN_ModuleSpace_mixin.
  Defined.

  Definition RN_ModuleSpace: ModuleSpace R_Ring:= 
    ModuleSpace.Pack R_Ring RN_AbelianGroup RN_ModuleSpace_class (nat -> R).
End RN.

Section p_norm.
  Notation "x '+_pw' y" := (ptwn_op Rplus x y) (at level 40).
  Context (p: R).
  Notation limit := (@metric_limit metric_R).

  Definition Rabs_power r p := if eqr r 0 then 0 else Rpower (Rabs r) p.

  Notation "`| r `|^ p" := (Rabs_power r p) (format "'`|' r '`|^' p", at level 35).

  Lemma Rapw0 q: `|0`|^q = 0.
  Proof. by rewrite /Rabs_power; case: ifP => /eqP //. Qed.

  Lemma Rapw_p1 r: `|r`|^1 = Rabs r.
  Proof.
    rewrite /Rabs_power.
    case: ifP => [/eqP -> | /eqP neq]; first by rewrite Rabs_R0.
    by rewrite Rpower_1//; split_Rabs; lra.
  Qed.
  
  Lemma Rapw_p0 r: `|r`|^0 = INR (~~ eqr r 0).
  Proof.
    rewrite /Rabs_power; case: ifP => // /eqP neq.
      by rewrite Rpower_O //; split_Rabs; lra.
  Qed.
  
  Lemma Rapw_pos r q: 0 <= `|r`|^q.
  Proof.
    rewrite /Rabs_power; case: ifP => [eq | ineq]; first exact/Rle_refl.
    by rewrite/Rpower; apply/Rlt_le/exp_pos.
  Qed.

  Lemma Rapw_lt r q: r <> 0 -> 0 < `|r`|^q.
  Proof.
    rewrite /Rabs_power => ineq.
    have ->: eqr r 0 = false by apply/eqP.
    exact/exp_pos.
  Qed.

  Lemma Rapw_Rabs r: `|Rabs r`|^p = `|r`|^p.
  Proof.
    rewrite /Rabs_power.
    case: ifP => [/eqP eq | /eqP ineq]; first by have:= Rnorm0_eq0 eq; case: ifP => /eqP //.
    case: ifP => [/eqP  eq| /eqP neq]; first by exfalso; apply ineq; rewrite eq Rabs_R0.
    by rewrite Rabs_Rabsolu.
  Qed.

  Lemma RapwN r: `|-r`|^p = `|r`|^p.
  Proof. by rewrite -(Rapw_Rabs r) -Rabs_Ropp Rapw_Rabs. Qed.

  Lemma Rapw_eq0 r q: `|r`|^q = 0 ->  r = 0.
  Proof.
    rewrite /Rabs_power; case: ifP =>/eqP // _.
    by rewrite /Rpower; have := exp_pos (q * ln (Rabs r)); lra.
  Qed.

  Lemma Rapw_inj r r' q: q <> 0 -> `|r`|^q = `|r' `|^q -> Rabs r = Rabs r'.
  Proof.
    rewrite {2}/Rabs_power => ineq.
    case: ifP => [/eqP -> zr | neq]; first by rewrite (@Rapw_eq0 r q).
    rewrite {1}/Rabs_power; case: ifP => [/eqP -> zr| /eqP neq']; last move: neq => /eqP neq.
    - by rewrite (@Rapw_eq0 r' q) // /Rabs_power neq.
    rewrite /Rpower => /exp_inv/Rmult_eq_reg_l [] // /ln_inv -> //; split_Rabs; lra.
  Qed.

    Lemma Rapw_mult x y q: `|x * y`|^q = `|x`|^q * `|y`|^q.
  Proof.
  rewrite /Rabs_power Rabs_mult.
  case: ifP => [/eqP /Rmult_integral [] ->| /eqP /Rmult_neq_0_reg [ineq ineq']].
    + by case: ifP => /eqP //; rewrite Rmult_0_l.
  - case: ifP; first by rewrite Rmult_0_l.
    by case: ifP => /eqP //; rewrite Rmult_0_r.
  case: ifP => /eqP // _; case: ifP => /eqP //_.
  by rewrite -Rpower_mult_distr //; split_Rabs; lra.
  Qed.

  Lemma Rapw_inc x y q: 0 < q -> Rabs x < Rabs y ->  `|x`|^q < `|y`|^q.
  Proof.
    rewrite /Rabs_power => pg0 ineq; case: ifP => /eqP.
    - by case: ifP => [/eqP | /eqP _ _]; [move: ineq; split_Rabs; lra | exact/exp_pos].
    case: ifP => /eqP; first by move: ineq; split_Rabs; lra.
    rewrite /Rpower => neq neq'.
    rewrite !(Rmult_comm q); apply/exp_increasing/Rmult_lt_compat_r => //.
    by apply/ln_increasing; first by split_Rabs; lra.
  Qed.
  
  Lemma Rapw_inc_le x y: 0 <= p -> Rabs x <= Rabs y ->  `|x`|^p <= `|y`|^p.
  Proof.
  case => [pg0 | <-]; last first.
  - rewrite !Rapw_p0; case: (classic (y = 0)) => [eq | neq].
    + rewrite eq => ineq; have ->: x = 0 by move: ineq; split_Rabs; lra.
      by have -> /= : eqr 0 0 = true; [apply/eqP | apply/Rle_refl].
    have ->/=: eqr y 0 = false by apply/eqP.
    by case: (eqr x 0) => /=; lra.
  case => [ineq | eq]; first exact/Rlt_le/Rapw_inc.
  by rewrite -(Rapw_Rabs x) eq Rapw_Rabs; apply /Rle_refl.
  Qed.

  Lemma Rapw_lt_inv x y: 0 < p -> `|x`|^p < `|y`|^p -> Rabs x < Rabs y.
  Proof.
  rewrite /Rabs_power => pg0.
  case: ifP => [/eqP -> | /eqP neq].
  - by case: ifP => [/eqP -> | /eqP]; split_Rabs; lra.
  case: ifP => [ | /eqP neq' /exp_lt_inv ineq].
  - by rewrite /Rpower; first by have := exp_pos (p * ln (Rabs x)); lra.
  apply/ln_lt_inv; try by split_Rabs; lra.
  exact/Rmult_lt_reg_l/ineq.
  Qed.
                                         
  Lemma Rapw_le_inv x y: 0 < p -> `|x`|^p <= `|y`|^p -> Rabs x <= Rabs y.
  Proof.
  move => pg0 [ineq | eq]; first by apply/Rlt_le/Rapw_lt_inv.
  by rewrite (Rapw_inj _ eq); lra.
  Qed.

  Lemma Rapw_inv x q: q <> 0 -> `|`|x`|^(/q)`|^q = Rabs x.
  Proof.
  rewrite/Rabs_power => neg.
  case E: (eqr x 0); move: E => /eqP.
  - by case: ifP => [_ -> | /eqP] //; rewrite Rabs_R0.
  case: ifP => /eqP.
  - rewrite /Rpower => eq; suff : 0 < 0 by lra.
    by rewrite -{2}eq; apply/exp_pos => ineq'.
  rewrite /Rpower [X in q * ln (X)]Rabs_pos_eq; last exact/Rlt_le/exp_pos.
  rewrite ln_exp -Rmult_assoc Rinv_r//Rmult_1_l => ineq ineq'.
  by rewrite exp_ln; split_Rabs; lra.
  Qed.

  Lemma Rpower_cont q x: 0 < x -> continuous (Rpower^~ q) x.
  Proof.
    move => ineq.
    apply/(continuous_comp (fun x => q * ln x) exp).
    - apply/continuous_mult; first exact/continuous_const.
      apply/continuity_pt_filterlim/derivable_continuous_pt.
      exists (/x).
      exact/derivable_pt_lim_ln.
    exact/continuity_pt_filterlim/derivable_continuous_pt/derivable_pt_exp.
  Qed.

  Lemma Rapw_cont q x: 0 < q -> continuous (fun x => Rabs_power x q) x.
  Proof.
    move => gt.
    case: (total_order_T 0 x) => [[ineq | <-] | ineq].
    - + apply/continuity_pt_filterlim.
        apply/(continuity_pt_ext_loc (fun x => Rpower x q)).
        * have pos: 0 < x /2 by lra.
          exists (mkposreal _ pos) => y /=.
          rewrite /ball/=/AbsRing_ball/=/abs/=/minus/=/plus/=/opp/=/Rabs_power => ineq'.
          have ->: eqr y 0 = false by apply/eqP; split_Rabs; lra.
          by rewrite Rabs_pos_eq//; split_Rabs;lra.
        exact/continuity_pt_filterlim/Rpower_cont.
    - move => A [[eps ineq]].
      rewrite Rapw0 => bll.
      rewrite /filtermap /=.
      have pos: 0 < `|eps`|^(/q) by apply/Rapw_lt; lra.
      exists (mkposreal _ pos) => y bll'; apply/bll; move: bll'.
      rewrite /ball /=/AbsRing_ball/abs/=!minus_zero_r => bll'.
      rewrite Rabs_pos_eq; last exact/Rapw_pos.
      apply/Rlt_le_trans.
      - apply/Rapw_inc => //.
        rewrite -(Rabs_pos_eq (`|eps`|^/q)) in bll'; last exact/Rapw_pos.
        exact/bll'.
      rewrite Rapw_inv; try lra.
      by rewrite Rabs_pos_eq; try lra.
    apply/continuity_pt_filterlim.
    apply/(continuity_pt_ext_loc (fun x => Rpower (-x) q)).
    - have pos: 0 < (- x) /2 by lra.
      exists (mkposreal _ pos) => y /=.
      rewrite /ball/=/AbsRing_ball/=/abs/=/minus/=/plus/=/opp/=/Rabs_power => ineq'.
      have ->: eqr y 0 = false by apply/eqP; split_Rabs; lra.
      rewrite -{2}(Ropp_involutive y) Rabs_Ropp.
      by rewrite Rabs_pos_eq//; split_Rabs;lra.
    apply/continuity_pt_filterlim.
    apply/(continuous_comp Ropp (fun x => Rpower x q)).
    - exact/continuous_opp.
    by apply/Rpower_cont; lra.
  Qed.
  
  Definition p_norm_seq x n := \sum_(0 <= i < n) `|x i`|^p.
  
  Lemma pnrmsS x n : p_norm_seq x n.+1 = p_norm_seq x n + `|x n`|^p.
  Proof. by rewrite /p_norm_seq big_nat_recr. Qed.

  Lemma pnrms0: p_norm_seq (cnst 0) = cnst 0.
  Proof.
    apply/functional_extensionality.
    elim => [ | n ih]; first by rewrite /p_norm_seq big_nil.
    by rewrite pnrmsS Rapw0 Rplus_0_r.
  Qed.

  Lemma pnrmsN x: p_norm_seq (ptw Ropp x) = p_norm_seq x.
  Proof.
    apply/functional_extensionality.
    elim => [ | n ih]; first by rewrite /p_norm_seq !big_nil.
    by rewrite !pnrmsS ih RapwN.
  Qed.
    
  Lemma pnrms_grw x: Un_growing (p_norm_seq x).
  Proof.
    move => n; have := Rapw_pos (Rabs (x n)) p.
    by rewrite /p_norm_seq big_nat_recr/= /GRing.add/= // Rapw_Rabs; lra.
  Qed.

  Lemma pnrms_pos x i: 0 <= p_norm_seq x i.
  Proof.
    elim: i => [ | i ih]; last exact/Rle_trans/pnrms_grw.
    by rewrite /p_norm_seq big_nil; apply/Rle_refl.
  Qed.
    
  Definition pow_p_norm := limit \o (F2MF p_norm_seq).
  
  Lemma ppnrm_lim x: pow_p_norm x ===
     limit (fun n => \sum_(0 <= i < n) `|x i`|^p).
  Proof. by rewrite /pow_p_norm comp_F2MF. Qed.

  Lemma ppnrm0: pow_p_norm (cnst 0) 0.
  Proof.
    rewrite ppnrm_lim.
    have:= pnrms0.
    rewrite /p_norm_seq => ->.
    exact/lim_cnst.
  Qed.

  Lemma ppnrmN x: pow_p_norm (ptw Ropp x) === pow_p_norm x.
  Proof.
    rewrite !ppnrm_lim.
    have := pnrmsN x.
    by rewrite /p_norm_seq => ->.
  Qed.

  Lemma ppnrm_sing : pow_p_norm \is_singlevalued.
  Proof. exact/comp_sing/F2MF_sing/lim_sing. Qed.  

  Lemma ppnrm_pos x r: pow_p_norm x r -> 0 <= r.
  Proof.
    by move => nrm; apply/lim_pos/pnrms_pos/x; rewrite -ppnrm_lim.
  Qed.
  
  Definition p_norm:= make_mf (fun x r => 0 <= r /\ pow_p_norm x (`|r`|^p)).

  Lemma ppnrm_pnrm x r : p_norm x r <-> 0 <= r /\ pow_p_norm x (`|r`|^p).
  Proof. done. Qed.

  Lemma pnrm0: p_norm (cnst 0) 0.
  Proof.
    rewrite ppnrm_pnrm; split; first exact/Rle_refl.
    by rewrite Rapw0; apply/ppnrm0.
  Qed.   

  Lemma pnrmN x: p_norm x === p_norm (ptw Ropp x).
  Proof. by move => r; rewrite !ppnrm_pnrm ppnrmN. Qed.    
    
  Lemma pnrm_pos x r: p_norm x r -> 0 <= r.
  Proof. by case. Qed.

  Lemma pnrm_lim x: 0 < p -> p_norm x ===
     limit (fun n => `|p_norm_seq x n`|^(/p)).
  Proof.
    move => pos r; split => [nrm | lmt].
    - have neq: /p <> 0.
      + suff: 0 < /p by lra.
        exact/Rinv_0_lt_compat.
      rewrite -(Rabs_pos_eq r); last exact/pnrm_pos/nrm.
      rewrite -(Rapw_inv r neq) Rinv_involutive; last lra.
      rewrite -Uncv_lim.
      apply/(continuity_seq (fun x => Rabs_power x (/p)) (p_norm_seq x)).
      + exact/continuity_pt_filterlim/Rapw_cont/Rinv_0_lt_compat.
      move: nrm => [_ ].
      by rewrite ppnrm_lim -Uncv_lim.
    split; first by apply/lim_pos => [ | n/=]; [exact/lmt | exact/Rapw_pos].
    rewrite ppnrm_lim.
    have eq: p_norm_seq x =1 fun n => `|`|p_norm_seq x n`|^(/p)`|^p.
    - by move => n/=; rewrite Rapw_inv; try lra; rewrite Rabs_pos_eq //; apply/pnrms_pos.
    apply/lim_prpr; first exact/eq.
    rewrite -(Uncv_lim); move: lmt => /Uncv_lim lmt.
    apply/(continuity_seq (Rabs_power^~ p) ) => //.
    exact/continuity_pt_filterlim/Rapw_cont.
  Qed.

  Lemma dom_pnrm: p <> 0 -> dom p_norm === dom pow_p_norm.
  Proof.
  move => neq x.
  split => [[r [_ val]] | [r val]]; first by exists (`|r`|^p).
  exists (`|r`|^(/p)); rewrite ppnrm_pnrm; split; first exact/Rapw_pos.
  rewrite Rapw_inv // Rabs_pos_eq //.
  exact/ppnrm_pos/val.
  Qed.
      
  Lemma pnrms_scale x r': 
    p_norm_seq (scale r' x) = scale (`|r'`|^p) (p_norm_seq x).
  Proof.
    apply/functional_extensionality => n.
    elim: n => [ | n].
    - by rewrite /scale /p_norm_seq !big_nil Rmult_0_r.
    rewrite /scale/p_norm_seq !big_nat_recr/= // => ->.
    by rewrite Rmult_plus_distr_l Rapw_mult //; apply/Rabs_pos.
  Qed.

  Lemma ppnrm_scale x r r':
    pow_p_norm x r -> pow_p_norm (scale r' x) (`|r'`|^p * r).
  Proof.
    move => nrm; rewrite ppnrm_lim.
    have := pnrms_scale x r'.
    rewrite {1}/p_norm_seq => ->.
    apply/limM; first exact/lim_cnst.
    by rewrite -ppnrm_lim.
  Qed.

  Lemma pnrm_sing: p <> 0 -> p_norm \is_singlevalued.
  Proof.
    move => neq x r r' nrm nrm'.
    rewrite -(Rabs_pos_eq r); last exact/pnrm_pos/nrm.
    rewrite -(Rabs_pos_eq r'); last exact/pnrm_pos/nrm'.
    apply/Rapw_inj; first exact/neq.
    apply/ppnrm_sing/nrm'.2/nrm.2.
  Qed.
    
  Lemma pnrm_hom x r r': 
    p <> 0 -> p_norm x r -> p_norm (scale r' x) ((Rabs r') * r).
  Proof.
  move => neq [ineq nrm].
  split; first by apply/Rmult_le_pos =>//; apply/Rabs_pos.
  by rewrite Rapw_mult Rapw_Rabs; apply/ppnrm_scale.
  Qed.
    
  Lemma grwD x y: Un_growing x -> Un_growing y -> Un_growing (x +_pw y).
  Proof. by move => grw grw' n; apply/Rplus_le_compat/grw'/grw. Qed.
  
  Notation "x - y" := (ptwn_op Rminus x y).

  Lemma pnrms_leq x r i: pow_p_norm x r -> p_norm_seq x i <= r.
  Proof. by move => nrm; apply/growing_ineq/Uncv_lim/ppnrm_lim/nrm/pnrms_grw. Qed.

  Lemma ppnrm_leq x r i: pow_p_norm x r -> `|x i`|^p <= r.
  Proof.
  move => nrm; apply/Rle_trans/pnrms_leq/nrm/i.+1.
  have:= pnrms_pos x i; have:= Rapw_pos (x i) p.
  by rewrite/p_norm_seq big_nat_recr//= /GRing.add/=; lra.
  Qed.

  Lemma ln_leq0 r: 1 <= r -> 0 <= ln r.
  Proof.
  case => [ineq | <-]; rewrite -ln_1; last exact/Rle_refl.
  by apply/Rlt_le/ln_increasing; lra.
  Qed.
  
  Lemma pnrm_leq x r i: 0 < p -> p_norm x r -> Rabs (x i) <= r.
  Proof.
  move => pg0 nrm.
  rewrite -(Rabs_pos_eq r); last exact/pnrm_pos/nrm.
  exact/(Rapw_le_inv pg0)/ppnrm_leq/nrm.2.
  Qed.

  Lemma Rpower_ineq x y q q':
    1 <= p -> 1 <= q' -> 0 < x -> 0 < y -> Rpower x (/q') * Rpower y (/q) <= x/q' + y/q.
  Proof.
  Admitted.
  
  Lemma Rapw_conv x y: 1 < p -> `|(x + y)/2`|^p <= (`|x`|^p + `|y`|^p)/2.
  Proof.
  Admitted.
  
  Lemma RapwD x y: 1 <= p ->  `|x + y`|^p <= Rpower 2 (p-1) * (`|x`|^p + `|y`|^p).
  Proof.
  case => [pg1 | <-]; last first.
  - rewrite !Rapw_p1 /Rminus Rplus_opp_r Rpower_O; try lra.
    rewrite Rmult_1_l; exact/Rabs_triang.
  suff ineq: `|x + y`|^p <= `|2 * x`|^p / 2 + `|2 * y`|^p / 2.
  apply/Rle_trans; first exact/ineq.
  rewrite !Rapw_mult /Rdiv.
  rewrite !Rmult_assoc !(Rmult_comm _ (/2)) -!Rmult_assoc.
  rewrite -Rmult_plus_distr_l.
  apply/Rmult_le_compat_r; first exact/Rplus_le_le_0_compat/Rapw_pos/Rapw_pos.
  rewrite /Rabs_power; case: ifP => /eqP neq; try lra.
  rewrite Rabs_pos_eq; try lra.
  by rewrite /Rminus Rpower_plus Rpower_Ropp Rpower_1; try lra; apply/Rle_refl.
  apply/Rle_trans.
  have ->: x + y = (2 * x + 2 * y) /2 by field.
  apply/Rapw_conv => //.
  lra.
  Qed.

  Lemma pnrms_bnd x y i: 1 <= p ->
    p_norm_seq (x +_pw y) i
    <=
    Rpower 2 (p - 1) * (p_norm_seq x i + p_norm_seq y i).
  Proof.
    move => ineq; elim: i => [ | i ih].
    rewrite /p_norm_seq !big_nil Rplus_0_r Rmult_0_r; apply Rle_refl.
    rewrite !pnrmsS.
    apply/Rle_trans.
    apply/Rplus_le_compat.
    apply/ih.
    rewrite /ptw_op; apply/RapwD => //.
    lra.
  Qed.
End p_norm.

Section lp.
  Context p (p_spec: 1 <= p).        
  Definition lp := dom (p_norm p).
  Definition norm x:= iota (p_norm p x).  
  Notation "\| x \|_p" := (norm x) (format "'\|' x '\|_p'").
  Notation "x +_pw y" := (ptwn_op Rplus x y) (at level 45).

  Lemma norm_spec x: x \from lp -> (p_norm p) x (norm x).
  Proof.
    move => [r nrm].
    have []:= @iota_correct R_AbsRing R_CompleteNormedModule (fun r => (p_norm p) x r).
    - exists r; split => // r' nrm'.
      by rewrite (pnrm_sing _ nrm nrm') //; lra.
    by move => ineq prp; rewrite /norm.
  Qed.

  Lemma pdomD x y:
    x \from lp -> y \from lp -> (x +_pw y) \from lp.
  Proof.
    move => [r nrm] [r' nrm'].
    have []:= growing_cv (p_norm_seq p (x +_pw y)); first exact/pnrms_grw.
    - exists (Rpower 2 (p - 1) * (Rabs_power r p + Rabs_power r' p)) => s [i ->].
      apply/Rle_trans; first by apply/pnrms_bnd.
      apply/Rmult_le_compat_l; first by rewrite /Rpower; apply/Rlt_le/exp_pos.
      exact/Rplus_le_compat/pnrms_leq/nrm'.2/pnrms_leq/nrm.2.
    move => s /Uncv_lim /ppnrm_lim lmt.
    exists (Rabs_power s (/p)).
    split; first exact/Rapw_pos.
    rewrite Rapw_inv; try lra.
    by rewrite Rabs_pos_eq; last exact/ppnrm_pos/lmt.
  Qed.

  Definition lp_plus (x y: lp): lp.
  Proof.
    move: x y => [x nrm] [y nrm'].
    exact/exist/pdomD/nrm'/nrm.
  Defined.
    
  Lemma lpN x:
    x \from lp -> (ptw Ropp x) \from lp.
  Proof.
    move => [r nrm].
    exists r; split; first exact/nrm.1.
    move: nrm.2; rewrite !ppnrm_lim.
    suff : p_norm_seq p x = p_norm_seq p (ptw Ropp x) by rewrite /p_norm_seq => ->.
    apply/functional_extensionality => n.
    rewrite /p_norm_seq /ptwn.
    apply/eq_bigr => i _.
    by rewrite -[RHS]Rapw_Rabs Rabs_Ropp Rapw_Rabs.
  Qed.

  Definition lp_opp (x: lp): lp.
    move: x => [x nrm].
    exact/exist/lpN/nrm.
  Defined.

  Lemma lp0: (fun _ => 0) \from lp.
  Proof.
    exists 0.
    split; first exact/Rle_refl.
    rewrite Rapw0 ppnrm_lim.
    suff : p_norm_seq p (fun _ => 0) = cnst 0.
    - by rewrite /p_norm_seq => ->; apply/lim_cnst. 
    apply/functional_extensionality => n.
    elim: n => [ | n ih]; first by rewrite /p_norm_seq big_nil.
    by rewrite pnrmsS ih Rapw0 /cnst/= Rplus_0_r.
  Qed.
    
  Definition lp_zero: lp.
  Proof.
    by exists (fun _ => 0); apply/lp0.
  Defined.
  
  Definition lp_AbelianGroup_mixin: AbelianGroup.mixin_of lp.
    exists lp_plus lp_opp lp_zero. 
    move => [x nrm] [y nrm'].
    exact/eq_sub/(@plus_comm RN_AbelianGroup).
    move => [x nrm] [y nrm'] [z nrm''].
    exact/eq_sub/(@plus_assoc RN_AbelianGroup).
    move => [x nrm].
    exact/eq_sub/(@plus_zero_r RN_AbelianGroup).
    move => [x nrm].
    exact/eq_sub/(@plus_opp_r RN_AbelianGroup).
  Defined.
  
  Definition lp_AbelianGroup:= AbelianGroup.Pack lp lp_AbelianGroup_mixin lp.

  Lemma lp_scal x r:
    x \from lp -> (scale r x) \from lp.
  Proof.
    move => [r' nrm].
    exists (Rabs r * r').
    by apply/pnrm_hom => //; lra.
  Qed.

  Definition lp_scale (r: R_Ring) (x: lp_AbelianGroup): lp_AbelianGroup.
    move: x => [x nrm].
    exact/exist/lp_scal/nrm/r.
  Defined.

  Definition lp_ModuleSpace_mixin: ModuleSpace.mixin_of R_Ring lp_AbelianGroup.
    exists lp_scale.
    move => r r' [x nrm].
    exact/eq_sub/(@scal_assoc _ RN_ModuleSpace).
    move => [x nrm].
    exact/eq_sub/(@scal_one _ RN_ModuleSpace).
    move => r [x nrm] [y nrm'].
    exact/eq_sub/(@scal_distr_l _ RN_ModuleSpace).
    move => r r' [x nrm].
    exact/eq_sub/(@scal_distr_r _ RN_ModuleSpace).
  Defined.

  Definition lp_ModuleSpace_class: ModuleSpace.class_of R_Ring lp.
    exists lp_AbelianGroup_mixin.
    exact/lp_ModuleSpace_mixin.
  Defined.

  Definition lp_ModuleSpace: ModuleSpace R_Ring :=
    ModuleSpace.Pack R_Ring lp lp_ModuleSpace_class lp.

  Notation "x -_pw y" := (@minus RN_AbelianGroup x y) (at level 34).    

  Definition lp_NormedModuleAux_class: NormedModuleAux.class_of R_AbsRing lp.
  Proof.
    split; first exact/lp_ModuleSpace_class.
    exists (fun (x: lp) r (y: lp) => \|projT1 x -_pw projT1 y\|_p <= r).
    move => [x nrm] [r rg0].
    rewrite minus_eq_zero /=.
    suff: \|(fun _ => 0)\|_p = 0 by rewrite /zero/=/cnst/= => ->; lra.
    apply/pnrm_sing; [ | apply/norm_spec | ]; try lra.
    - exact/lp0.
    exact/pnrm0.
    move => x y e ineq.
    rewrite -opp_minus.
    
    
    have nrm':= pnrm_spec (pnrm0 p).
    rewrite (pnrm_sing _ nrm' (pnrm0 p)); try lra.
    exact/Rlt_le.
    move => [x nrm] [y nrm'] r.
    rewrite /=.
    rewrite -opp_minus => ineq.
    Search _ 
    
  Definition lp_met : MetricSpace.
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
    