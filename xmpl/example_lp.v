Require Import Reals Qreals Psatz Classical FunctionalExtensionality.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import all_cs reals Q_reals mtrc mreals Rstruct.
From Coquelicot Require Import Hierarchy Continuity.

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
  Qed.
End RN.

Section lp.
  Notation "x '+_pw' y" := (ptwn_op Rplus x y) (at level 40).
  Context (p: R).
  Notation limit := (@metric_limit R_met).

  Definition Rabs_power r p := if eqr r 0 then 0 else Rpower (Rabs r) p.

  Notation "`| r `|^ p" := (Rabs_power r p) (format "'`|' r '`|^' p", at level 35).

  Lemma Rapw0 q: `|0`|^q = 0.
  Proof. by rewrite /Rabs_power; case: ifP => /eqP //. Qed.

  Lemma Rapw_p1 r: `|r`|^1 = Rabs r.
  Proof.
  rewrite /Rabs_power.
  case: ifP => [/eqP -> | /eqP neq]; first by rewrite Rabs_R0.
  rewrite Rpower_1//; split_Rabs; lra.
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
  
  Definition p_norm_seq x n := \sum_(0 <= i < n) `|x i`|^p.

  Lemma Rapw_Rabs r: `|Rabs r`|^p = `|r`|^p.
  Proof.
  rewrite /Rabs_power.
  case: ifP => [/eqP eq | /eqP ineq]; first by have:= Rnorm0_eq0 eq; case: ifP => /eqP //.
  case: ifP => [/eqP  eq| /eqP neq]; first by exfalso; apply ineq; rewrite eq Rabs_R0.
  by rewrite Rabs_Rabsolu.
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

  Lemma ppnrm_sing : pow_p_norm \is_singlevalued.
  Proof. exact/comp_sing/F2MF_sing/lim_sing. Qed.  

  Lemma ppnrm_pos x r: pow_p_norm x r -> 0 <= r.
  Proof.
    by move => nrm; apply/lim_pos/pnrms_pos/x; rewrite -ppnrm_lim.
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

  Definition p_norm:= make_mf (fun x r => 0 <= r /\ pow_p_norm x (`|r`|^p)).

  Definition lp := dom p_norm.
    
  Lemma ppnrm_pnrm x r : p_norm x r <-> 0 <= r /\ pow_p_norm x (`|r`|^p).
  Proof. done. Qed.
  
  Lemma pnrm_pos x r: p_norm x r -> 0 <= r.
  Proof. by case. Qed.
  
  Lemma dom_pnrm: p <> 0 -> dom p_norm === dom pow_p_norm.
  Proof.
  move => neq x.
  split => [[r [_ val]] | [r val]]; first by exists (`|r`|^p).
  exists (`|r`|^(/p)); rewrite ppnrm_pnrm; split; first exact/Rapw_pos.
  rewrite Rapw_inv // Rabs_pos_eq //.
  exact/ppnrm_pos/val.
  Qed.
         
  Context (p_norm_f: (nat -> R) -> R).
  Hypothesis p_norm_spec: p_norm_f \is_choice_for p_norm.

  Notation "\| x \|_p" := (p_norm_f x) (format "'\|' x '\|_p'").
  
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

  Lemma Rapw_inc x y: Rabs x < Rabs y ->  `|x`|^p <= `|y`|^p.

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
  
  Lemma pnrm_leq x r i: 0 < p -> p_norm x r -> Rabs (x i) <= r.
  Proof.
  move => pg0 nrm.
  rewrite -(Rabs_pos_eq r); last exact/pnrm_pos/nrm.
  exact/(Rapw_le_inv pg0)/ppnrm_leq/nrm.2.
  Qed.

  Lemma Rpower_ineq x y p q:
    1 <= p -> 1 <= q -> 0 < x -> 0 < y -> Rpower x (/p) * Rpower y (/q) <= x/p + y/q.
  Lemma Rapw_conv x y: 1 < p -> `|x/2 + y/2`|^p <= 1/2 * `|x + y`|^p.
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
  Admitted.

  Lemma pnrms_bnd x y:
    has_ub (p_norm_seq x) -> has_ub (p_norm_seq y) ->
    has_ub (p_norm_seq (x +_pw y)).
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
    