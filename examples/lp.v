Require Import Reals Qreals Psatz Classical FunctionalExtensionality.
From mathcomp Require Import all_ssreflect all_algebra.
From rlzrs Require Import all_mf.
Require Import iseg.
From metric Require Import pointwise reals metric standard coquelicot.
From Coquelicot Require Import Coquelicot.
From Younginequality Require Import Rstruct youngsinequality concave.

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
    - move => r r' x; apply/functional_extensionality => n.
      by rewrite /scale/mult/= Rmult_assoc.
    - move => x; apply/functional_extensionality => n.
      by rewrite /scale/one/= Rmult_1_l.
    - move => r x y; apply/functional_extensionality => n.
      by rewrite /scale/plus/=/ptw_op Rmult_plus_distr_l.
    move => r r' x; apply/functional_extensionality => n.
    by rewrite /scale/plus/= Rmult_plus_distr_r.
  Defined.

  Definition RN_ModuleSpace_class:
    ModuleSpace.class_of R_Ring RN_AbelianGroup.
    exists (RN_AbelianGroup_mixin).
    apply/RN_ModuleSpace_mixin.
  Defined.

  Definition RN_ModuleSpace: ModuleSpace R_Ring:= 
    ModuleSpace.Pack R_Ring RN_AbelianGroup RN_ModuleSpace_class (nat -> R).
End RN.

Section p_norm.
  Notation "x '+_pw' y" := (ptwn_op Rplus x y) (at level 40).
  Context (p: R).
  Notation limit := (@limit metric_R).
  Notation "`| r `|^ p" := (Rabs_power r p) (format "'`|' r '`|^' p", at level 35).
    
  Section p_norm_sequence.
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

    Lemma pnrms_scale x r': 
      p_norm_seq (scale r' x) = scale (`|r'`|^p) (p_norm_seq x).
    Proof.
      apply/functional_extensionality => n.
      elim: n => [ | n].
      - by rewrite /scale /p_norm_seq !big_nil Rmult_0_r.
      rewrite /scale/p_norm_seq !big_nat_recr/= // => ->.
      by rewrite Rmult_plus_distr_l Rapw_mult //; apply/Rabs_pos.
    Qed.

  End p_norm_sequence.

  Section pow_p_norm.
    Definition pow_p_norm := limit \o (F2MF p_norm_seq).
  
    Lemma ppnrm_lim x: pow_p_norm x ===
                                  limit (p_norm_seq x).
    Proof. by rewrite /pow_p_norm comp_F2MF. Qed.

    Lemma ppnrm0: pow_p_norm (cnst 0) 0.
    Proof. by rewrite ppnrm_lim pnrms0; apply/lim_cnst. Qed.

    Lemma ppnrmN x: pow_p_norm (ptw Ropp x) === pow_p_norm x.
    Proof. by rewrite !ppnrm_lim pnrmsN. Qed.

    Lemma ppnrm_sing : pow_p_norm \is_singlevalued.
    Proof. exact/comp_sing/F2MF_sing/lim_sing. Qed.  

    Lemma ppnrm_pos x r: pow_p_norm x r -> 0 <= r.
    Proof. by move => nrm; apply/lim_pos/pnrms_pos/x; rewrite -ppnrm_lim. Qed.

    Lemma ppnrm_scale x r r':
      pow_p_norm x r -> pow_p_norm (scale r' x) (`|r'`|^p * r).
    Proof.
      move => nrm; rewrite ppnrm_lim pnrms_scale.
      apply/limM; first exact/lim_cnst.
      by rewrite -ppnrm_lim.
    Qed.

    Lemma ppnrm_leq x r i: pow_p_norm x r -> p_norm_seq x i <= r.
    Proof. by move => nrm; apply/growing_ineq/Uncv_lim/ppnrm_lim/nrm/pnrms_grw. Qed.

    Lemma ppnrm_coef x r i: pow_p_norm x r -> `|x i`|^p <= r.
    Proof.
      move => nrm; apply/Rle_trans/ppnrm_leq/nrm/i.+1.
      have:= pnrms_pos x i; have:= Rapw_pos (x i) p.
      by rewrite/p_norm_seq big_nat_recr//= /GRing.add/=; lra.
    Qed.

  End pow_p_norm.
    
  Section p_norm_multifunction.
    Definition mf_p_norm_expanded_def:= make_mf (fun x r => 0 <= r /\ pow_p_norm x (`|r`|^p)).
    Fact p_norm_key : unit. Proof. by []. Qed.
    Definition mf_p_norm := locked_with p_norm_key mf_p_norm_expanded_def.
    Canonical p_norm_unlockable := [unlockable of mf_p_norm].
    
    Lemma ppnrm_pnrm x r : mf_p_norm x r <-> 0 <= r /\ pow_p_norm x (`|r`|^p).
    Proof. by rewrite unlock. Qed.

    Lemma pnrm0: mf_p_norm (cnst 0) 0.
    Proof.
      rewrite ppnrm_pnrm; split; first exact/Rle_refl.
      by rewrite Rapw0; apply/ppnrm0.
    Qed.   

    Lemma pnrmN x: mf_p_norm x === mf_p_norm (ptw Ropp x).
    Proof. by move => r; rewrite !ppnrm_pnrm ppnrmN. Qed.    
    
    Lemma pnrm_pos x r: mf_p_norm x r -> 0 <= r.
    Proof. by rewrite unlock; case. Qed.

    Lemma pnrm_lim x: 0 < p -> mf_p_norm x ===
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
        move: nrm; rewrite unlock => [[_]].
        by rewrite ppnrm_lim -Uncv_lim.
      rewrite unlock; split; first by apply/lim_pos => [ | n/=]; [exact/lmt | exact/Rapw_pos].
      rewrite ppnrm_lim.
      have eq: p_norm_seq x =1 fun n => `|`|p_norm_seq x n`|^(/p)`|^p.
      - by move => n/=; rewrite Rapw_inv; try lra; rewrite Rabs_pos_eq //; apply/pnrms_pos.
      apply/lim_prpr; first exact/eq.
      rewrite -(Uncv_lim); move: lmt => /Uncv_lim lmt.
      apply/(continuity_seq (Rabs_power^~ p) ) => //.
      exact/continuity_pt_filterlim/Rapw_cont.
    Qed.

    Lemma dom_pnrm: p <> 0 -> dom mf_p_norm === dom pow_p_norm.
    Proof.
      split => [[r] | [r val]]; first by rewrite unlock => [[_ val]]; exists (`|r`|^p).
      exists (`|r`|^(/p)); rewrite ppnrm_pnrm; split; first exact/Rapw_pos.
      rewrite Rapw_inv // Rabs_pos_eq //.
      exact/ppnrm_pos/val.
    Qed.

    Lemma dom_lp x: p <> 0 -> x \from dom mf_p_norm <-> has_ub (p_norm_seq x).
    Proof.
      move => neq.
      rewrite dom_pnrm //.
      split => [[r nrm] | hub]; first by exists r => _ [i ->]; apply/ppnrm_leq.
      have [r lub]:= ub_to_lub _ hub.
      exists r; rewrite ppnrm_lim -Uncv_lim.
      exact/Un_cv_crit_lub/lub/pnrms_grw.
    Qed.

      Lemma pnrm_sing: p <> 0 -> mf_p_norm \is_singlevalued.
    Proof.
      move => neq x r r' nrm nrm'.
      rewrite -(Rabs_pos_eq r); last exact/pnrm_pos/nrm.
      rewrite -(Rabs_pos_eq r'); last exact/pnrm_pos/nrm'.
      apply/Rapw_inj; first exact/neq.
      move: nrm nrm'; rewrite unlock => [[_ eq]] [_ eq'].
      exact/ppnrm_sing/eq'/eq.
    Qed.
    
    Lemma pnrm_hom x r r': 
      p <> 0 -> mf_p_norm x r -> mf_p_norm (scale r' x) ((Rabs r') * r).
    Proof.
      rewrite unlock => neq [ineq nrm].
      split; first by apply/Rmult_le_pos =>//; apply/Rabs_pos.
      by rewrite Rapw_mult Rapw_Rabs; apply/ppnrm_scale.
    Qed.
    
    Lemma grwD x y: Un_growing x -> Un_growing y -> Un_growing (x +_pw y).
    Proof. by move => grw grw' n; apply/Rplus_le_compat/grw'/grw. Qed.
  
    Notation "x - y" := (ptwn_op Rminus x y).

    Lemma ln_leq0 r: 1 <= r -> 0 <= ln r.
    Proof.
      case => [ineq | <-]; rewrite -ln_1; last exact/Rle_refl.
      by apply/Rlt_le/ln_increasing; lra.
    Qed.
  
    Lemma pnrm_coef x r i: 0 < p -> mf_p_norm x r -> Rabs (x i) <= r.
    Proof.
      move => pg0 nrm.
      rewrite -(Rabs_pos_eq r); last exact/pnrm_pos/nrm.
      move: nrm; rewrite unlock => [[_ eq]].
      exact/(Rapw_le_inv pg0)/ppnrm_coef/eq.
    Qed.
  End p_norm_multifunction.

  Section lp_norm.
    Definition lp := make_subset (fun x => has_ub (p_norm_seq x)).    
    Definition p_norm (x: lp):= iota (mf_p_norm (projT1 x)).
    Notation "\| x \|_p" := (p_norm x) (format "'\|' x '\|_p'").
    Hypothesis pn0: p <> 0.

    Lemma lp_spec: lp === dom mf_p_norm.
    Proof. by move => x; rewrite dom_lp. Qed.
    
    Lemma norm_spec (x: lp): mf_p_norm (projT1 x) (\|x\|_p).
    Proof.
      move: x => [x lp].
      have [r nrm]:= (lp_spec x).1 lp.
      apply/(@iota_correct R_AbsRing R_CompleteNormedModule (fun r => mf_p_norm x r)).
      exists r; split => // r' nrm'.
      by rewrite (pnrm_sing _ nrm nrm') //; lra.
    Qed.
    
    Lemma norm_eq (x: lp) r: mf_p_norm (projT1 x) r -> \|x\|_p = r.
    Proof. by move => nrm; apply/pnrm_sing/nrm/norm_spec. Qed.

    Lemma norm_pos (x: lp): 0 <= \|x\|_p.
    Proof. exact/pnrm_pos/norm_spec. Qed.

    Lemma norm_eq0 (x: lp): 0 < p -> \|x\|_p = 0 -> sval x = cnst 0.
    Proof.
      move => pspec eq.
      apply/functional_extensionality => n.
      have eq': mf_p_norm (sval x) 0 by rewrite -eq; apply/norm_spec.
      have := pnrm_coef n _ eq'.
      by rewrite /cnst; split_Rabs; lra.
    Qed.

    Lemma lp0: (fun _ => 0) \from lp.
    Proof.
      exists 0.
      move => _ [i ->].
      suff ->: p_norm_seq (fun _ => 0) = cnst 0 by rewrite /cnst; apply/Rle_refl.
      apply/functional_extensionality => n.
      elim: n => [ | n ih]; first by rewrite /p_norm_seq big_nil.
      by rewrite pnrmsS ih Rapw0 /cnst/= Rplus_0_r.
    Qed.
    
    Definition lp_zero: lp.
    Proof. by exists (fun _ => 0); apply/lp0. Defined.
    
    Lemma norm0: \|lp_zero\|_p = 0.
    Proof. exact/norm_eq/pnrm0. Qed.

    Lemma lpN x:
      x \from lp -> (ptw Ropp x) \from lp.
    Proof.
      move => [r ub]; exists r => _ [i ->].
      by rewrite pnrmsN; apply/ub; exists i.
    Qed.
    
    Definition lp_opp (x: lp): lp := exist _ _ (lpN (projT2 x)).

    Lemma norm_opp x: \| lp_opp x \|_p = \|x\|_p.
    Proof.
      apply/norm_eq.
      rewrite -(pnrmN (sval x)).
      exact/norm_spec.
    Qed.
  End lp_norm.
End p_norm.
Notation "'l_' p" := (lp p) (at level 2, format "'l_' p").
Notation "\| x |" := (p_norm x) (at level 2, format "'\|' x '|'").

Section lp.
  Section lp_AbelianGroup.
    Context (p: R).        
    Notation "x +_pw y" := (ptwn_op Rplus x y) (at level 45).

    Lemma pnrms_bnd x y i: 1 <= p ->
                           p_norm_seq p (x +_pw y) i
                           <=
                           Rpower 2 (p - 1) * (p_norm_seq p x i + p_norm_seq p y i).
    Proof.
      move => ineq; elim: i => [ | i ih].
      rewrite /p_norm_seq !big_nil Rplus_0_r Rmult_0_r; apply Rle_refl.
      rewrite !pnrmsS; apply/Rle_trans.
      - apply/Rplus_le_compat; first exact/ih.
        by rewrite /ptw_op; apply/RapwD => //.
      lra.
    Qed.

    Lemma lpdomD x y: 1 <= p ->
      x \from (l_ p) -> y \from (l_ p) -> (x +_pw y) \from (l_ p).
    Proof.
      move => pspec [r nrm] [r' nrm'].
      exists (Rpower 2 (p - 1) * (r + r')) => _ [i ->].
      apply/Rle_trans; first exact/pnrms_bnd.
      apply/Rmult_le_compat_l; first exact/Rlt_le/exp_pos.
      by apply/Rplus_le_compat/nrm'; [apply/nrm; exists i | exists i].
    Qed.

    Context (pspec: 1 <= p).
    Definition lp_plus (x y: l_ p): l_ p:= exist _ _ (lpdomD pspec (projT2 x) (projT2 y)).
    
    Definition lp_AbelianGroup_mixin: AbelianGroup.mixin_of l_ p.
      exists lp_plus (@lp_opp p) (@lp_zero p). 
      move => [x nrm] [y nrm'].
      exact/eq_sub/(@plus_comm RN_AbelianGroup).
      move => [x nrm] [y nrm'] [z nrm''].
      exact/eq_sub/(@plus_assoc RN_AbelianGroup).
      move => [x nrm].
      exact/eq_sub/(@plus_zero_r RN_AbelianGroup).
      move => [x nrm].
      exact/eq_sub/(@plus_opp_r RN_AbelianGroup).
    Defined.
  
    Canonical lp_AbelianGroup:= AbelianGroup.Pack l_ p lp_AbelianGroup_mixin l_ p.
  End lp_AbelianGroup.

  Section lp_ModuleSpace.
    Context p (p_spec: 1 <= p).
    Lemma lp_scal x r:
      x \from l_ p -> (scale r x) \from l_ p.
    Proof.
      move => [r' nrm]; exists (`|r`|^p * r') => _ [i ->].
      by rewrite pnrms_scale; apply/Rmult_le_compat_l/nrm; [exact/Rapw_pos | exists i].
    Qed.

    Definition lp_scale (r: R_Ring) (x: l_ p): l_ p :=
      exist _ _ (lp_scal r (projT2 x)).

    Definition lp_ModuleSpace_mixin: ModuleSpace.mixin_of R_Ring (lp_AbelianGroup p_spec).
      exists lp_scale.
      - move => r r' [x nrm].
        exact/eq_sub/(@scal_assoc _ RN_ModuleSpace).
      - move => [x nrm].
        exact/eq_sub/(@scal_one _ RN_ModuleSpace).
      - move => r [x nrm] [y nrm'].
        exact/eq_sub/(@scal_distr_l _ RN_ModuleSpace).
      move => r r' [x nrm].
      exact/eq_sub/(@scal_distr_r _ RN_ModuleSpace).
    Defined.
    
    Definition lp_ModuleSpace_class: ModuleSpace.class_of R_Ring l_ p.
      exists (lp_AbelianGroup_mixin p_spec).
      exact/lp_ModuleSpace_mixin.
    Defined.

    Definition lp_ModuleSpace: ModuleSpace R_Ring :=
      ModuleSpace.Pack R_Ring l_ p lp_ModuleSpace_class l_ p.
  End lp_ModuleSpace.

  Section lp_NormedModule.
    Local Notation "x *_pw y" := (ptw_op Rmult x y) (at level 3).
    Lemma Hoelder's_inequality x y p q: 1 <= p -> 1 <= q -> /p + /q = 1 ->
      x \from l_ p -> y \from l_ q -> (x *_pw y) \from l_ 1.
    Proof.
      move => pspec qspec h lpx lqy.
      pose x':= exist _ _ lpx: lp_ModuleSpace pspec.
      pose y' := exist _ _ lqy: lp_ModuleSpace qspec.
      case: (total_order_T (\|x'|) 0) => [[ineq | eq] | ineq]; first by have := norm_pos _ x'; lra.
      - suff->: ptwn_op Rmult x y = cnst 0 by apply/lp0.
        apply/functional_extensionality => n.
        rewrite /cnst/ptwn_op /=.
        suff -> : x n = 0 by lra.
        suff: Rabs (x n) <= 0 by have:= Rabs_pos (x n); split_Rabs; lra.
        by apply/pnrm_coef; last first; [rewrite -eq; apply/norm_spec; lra | lra].
      pose u := scal (/ \| x'|) x'.
      have nu1: \|u| = 1.
      - rewrite /u/= -(Rinv_l (\|x'|)); try lra.
        apply/norm_eq; try lra.
        rewrite /= -{2}(Rabs_pos_eq (/ \|x'|)); last exact/Rlt_le/Rinv_0_lt_compat.
        apply/pnrm_hom; try lra.
        by apply/norm_spec; lra.
      case: (total_order_T (\|y'|) 0) => [[ineq' | eq] | ineq']; first by have := norm_pos _ y'; lra.
      - suff->: ptwn_op Rmult x y = cnst 0 by apply/lp0.
        apply/functional_extensionality => n.
        rewrite /cnst/ptwn_op /=.
        suff -> : y n = 0 by lra.
        suff: Rabs (y n) <= 0 by have:= Rabs_pos (y n); split_Rabs; lra.
        by apply/pnrm_coef; last first; [rewrite -eq; apply/norm_spec; lra | lra].
      pose v := scal (/ \| y'|) y'.
      have nv1: \|v| = 1.
      - rewrite /v/= -(Rinv_l (\|y'|)); try lra.
        apply/norm_eq; try lra.
        rewrite /= -{2}(Rabs_pos_eq (/ \|y'|)); last exact/Rlt_le/Rinv_0_lt_compat.
        apply/pnrm_hom; try lra.
        by apply/norm_spec; lra.
      suff [r bnd]: l_ 1 (ptwn_op Rmult (sval u) (sval v)).
      - exists (\|y'| * \|x'| * r) => _ [n ->].
        apply/Rle_trans/Rmult_le_compat_l/bnd; last first; first by exists n; apply/eqP/eq_refl.
        + by apply/Rmult_le_pos; lra.
        elim: n => [ | n ih]; first by rewrite /p_norm_seq !big_nil Rmult_0_r; apply/Rle_refl.
        rewrite /p_norm_seq !big_nat_recr /= //.
        + apply/Rle_trans; last first.
          rewrite Rmult_plus_distr_l.
          apply/Rplus_le_compat; first exact/ih.
          rewrite Rmult_assoc Rapw_p1 /ptwn_op/=.
          rewrite /scale !Rabs_mult Rabs_pos_eq ?(Rabs_pos_eq (/ \|y'|)); try by apply/Rlt_le/Rinv_0_lt_compat; lra.
          have ->: \|y'| * (\|x'| * (/ \|x'| * Rabs (x n) * (/ \|y'| * Rabs (y n)))) = Rabs (x n) * Rabs (y n) by field; lra.
          apply/Rle_refl.
        apply/Rplus_le_compat_l.
        by rewrite Rapw_p1 Rabs_mult; exact/Rle_refl.
      suff bnd: forall n, Rabs ((sval u n) * (sval v n)) <= `|sval u n`|^p /p + `|sval v n`|^q /q.
      exists (`|\|u|`|^p / p + `|\|v|`|^q / q).  
      move => _ [n ->].
      apply/Rle_trans; last first.
      - apply/Rplus_le_compat.
        + apply/Rmult_le_compat_r; first by apply/Rlt_le/Rinv_0_lt_compat; lra.
          apply/(ppnrm_leq n).
          have [[ | _ prp _]]:= ppnrm_pnrm p (sval u) (\|u|); first by apply/norm_spec; lra.
          exact/prp.
        apply/Rmult_le_compat_r; first by apply/Rlt_le/Rinv_0_lt_compat; lra.
        apply/(ppnrm_leq n).
        have [[ | _ prp _]]:= ppnrm_pnrm q (sval v) (\|v|); first by apply/norm_spec; lra.
        exact/prp.
      elim: n => [ | n ih]; first by rewrite !/p_norm_seq !big_nil !Rmult_0_l Rplus_0_l; apply/Rle_refl.
      rewrite /p_norm_seq !big_nat_recr /= //.
      apply/Rle_trans.
      - apply/Rplus_le_compat; first exact/ih.
        by rewrite Rapw_p1; apply/bnd.
      by rewrite /p_norm_seq /= /GRing.add /=; lra.
      move => n.
      rewrite Rabs_mult.
      apply/Rle_trans; first exact/Young's_inequality/h.
      rewrite !Rapw_Rabs; exact/Rle_refl.
    Qed.

    Context p (pspec: 1 <= p).
    
    Lemma Minkowski's_inequality (x y: lp_ModuleSpace pspec):
      \|plus x y| <= \|x| + \|y|.
    Proof.
      
    Admitted.

    Lemma norm_scale r (x: lp_ModuleSpace pspec): \|lp_scale r x| = Rabs r * \|x|.
    Proof. by apply/norm_eq/pnrm_hom/norm_spec; lra. Qed.

    Definition lp_NormedModuleAux_class: NormedModuleAux.class_of R_AbsRing l_ p.
    Proof.
      split; first exact/lp_ModuleSpace_class.
      exists (fun (x: lp_ModuleSpace pspec) r (y: lp_ModuleSpace pspec) => \|minus x y| < r).
      - move => [x nrm] [r rg0].
        rewrite minus_eq_zero /=.
        suff: \|@zero (lp_ModuleSpace pspec)| = 0 by rewrite /zero/=/cnst/= => ->; lra.
        by apply/norm_eq/pnrm0; lra.
      - by move => x y e ineq; rewrite -opp_minus norm_opp //; lra.
      move => x y z r r' nrm nrm'.
      apply/Rle_lt_trans/Rplus_lt_compat/nrm'/nrm/Rle_trans/Minkowski's_inequality.
      rewrite plus_assoc -(plus_assoc x) plus_opp_l plus_zero_r.
      exact/Rle_refl.
    Defined.
    Print Assumptions lp_NormedModuleAux_class.
    
    Definition lp_NormedModule_class: NormedModule.class_of R_AbsRing l_ p.
      exists lp_NormedModuleAux_class; exists (@p_norm p) 1.
      - exact/Minkowski's_inequality.
      - by move => r x; rewrite norm_scale; apply/Rle_refl.
      - move => x y eps ineq; rewrite /ball /=.
        by rewrite -opp_minus norm_opp; try lra.
      - move => x y eps; rewrite /ball/= Rmult_1_l => bll.
        by rewrite -opp_minus norm_opp; try lra.
      move => x n0.
      apply/eq_sub/functional_extensionality => i /=.
      apply/Rabs_eq_0/Rle_antisym/Rabs_pos; rewrite -n0.
      by apply/pnrm_coef/norm_spec; lra.
    Defined.

    Canonical lp_NormedModule:= NormedModule.Pack R_AbsRing l_ p lp_NormedModule_class l_ p.
  End lp_NormedModule.

  Section Fundamental_systems.
    Context (K: AbsRing) (V: NormedModule K).
   
    Definition in_span (E: subset V) x :=
      exists (L: seq (K * E)), x = \big[plus/zero]_(av <- L) scal av.1 (sval av.2).
    
    Definition span (E: subset V) := make_subset (in_span E).

    Lemma span0 E: span E zero.
    Proof. by exists [::]; rewrite big_nil. Qed.      

    Definition in_span_over (A: subset K) (E: subset V) x:= 
      exists (L: seq (A * E)), x = \big[plus/zero]_(av <- L) scal (projT1 av.1) (projT1 av.2).
    
    Definition span_over A E := make_subset (in_span_over A E).

    Notation "\span_of E \over A" := (span_over A E) (at level 30).
    
    Lemma spno0 A E: zero \from span_over A E.
    Proof. by exists [::]; rewrite big_nil. Qed.
      
    Lemma spno_subs (A: subset K) (E: subset V):
      one \from A -> E \is_subset_of \span_of E \over A.
    Proof.
      move => Aone v Ev.
      pose one':= exist A one Aone.
      pose v' := exist E v Ev.
      exists [:: (one', v')].
      by rewrite big_cons big_nil plus_zero_r scal_one.
    Qed.

    Lemma spno_all E: span E === span_over All E.
    Proof.
      move => x.
      split => [[L ->] | [L ->]].
      - elim: L => [ | [r v] L [L' eq]]; first by exists [::]; rewrite !big_nil.
        have allr: All r by trivial.
        pose r' := exist All r allr.
        by exists ((r', v) :: L'); rewrite !big_cons eq.
      elim: L => [ | [[r allr] v] L [L' eq]]; first by exists [::]; rewrite !big_nil.
      by exists ((r,v) :: L'); rewrite !big_cons eq.
    Qed.

    Lemma span_subs (E: subset V): E \is_subset_of span E.
    Proof. by move => Ev; rewrite spno_all; apply/spno_subs. Qed.
    
    Definition fundamental_subset E := dense_subset (span E).

    Lemma fsst_dns A E: dense_subset A -> fundamental_subset E -> dense_subset (span_over A E).
    Proof.
      move => dns fsst x eps eg0.
      have e2: 0 < eps/2 by lra.
      have [y [[L eq] ineq]]:= fsst x (eps/2) e2.
      suff [y' [spn lt]]: exists y', y' \from span_over A E /\ d y y' < eps/2.
      - by exists y'; split; last by apply/(dst_le ineq); first exact/Rlt_le/lt; lra.
      elim: L (y) eq => [z | [k v] L ih z /= eq].
      - by rewrite big_nil; exists zero; split; first exact/spno0; rewrite -eq dstxx.
      pose z' := \big[plus/zero]_(j <- L) scal j.1 (sval j.2).              
      have [ | v' [[L' eq'] dst]]//:= ih z'.
      case: (total_order_T (norm (sval v)) 0) => [[ineq' | eq''] | ineq']. 
      - by have := norm_ge_0 (sval v); lra.
      - exists v'; split; first by exists L'.
        by rewrite eq big_cons -/z' /= (norm_eq_zero _ eq'') scal_zero_r plus_zero_l.
      pose delta := (eps/2 - (d z' v'))/(2 * norm (sval v)).
      have [ | k' [Ak' dk']]:= dns k delta; first by apply/Rlt_gt/Rdiv_lt_0_compat; lra.
      exists (plus (scal k' (sval v)) v').
      split; first by exists ((exist A k' Ak', v):: L'); rewrite big_cons eq'.
      rewrite eq big_cons /d /= /minus opp_plus plus_assoc.
      rewrite -(plus_assoc (scal k (sval v))) (plus_comm _ (opp (scal k' (sval v)))).
      rewrite plus_assoc -(plus_assoc _ _ (opp v')).
      apply/Rle_lt_trans; first exact/norm_triangle.
      rewrite -(Rplus_0_r (eps/2)) -(Rminus_diag_eq (- d z' v') (- d z' v')) // -Rplus_assoc.
      apply/Rplus_lt_le_compat; last by rewrite /d /=/minus/z' Ropp_involutive; apply/Rle_refl.
      rewrite -scal_opp_l -scal_distr_r.
      apply/Rle_lt_trans; first exact/norm_scal.
      rewrite -[X in _ < X]Rmult_1_r -(Rinv_l (norm (sval v))); try lra.
      rewrite -Rmult_assoc; apply/Rmult_lt_compat_r => //.
      apply/Rle_lt_trans; first exact/dk'.
      rewrite /delta.
      apply/Rmult_lt_compat_l; try lra.
      apply/Rinv_lt_contravar; try lra.
      by apply/Rmult_lt_0_compat; lra.      
    Qed.

    Definition fundamental_system (F: nat -> V) := fundamental_subset (codom (F2MF F)).
  End Fundamental_systems.
    
  Section standard_basis.
    Context p (pspec: 1 <= p).
    Definition e (i: nat): RN_ModuleSpace:= fun j => if (i == j)%nat then R1 else R0.
    
    Lemma pnrms_e i j: p_norm_seq p (e i) j = if (i < j)%nat then R1 else R0.
    Proof.
      rewrite/p_norm_seq.
      elim: j => [ | j ih]; first by rewrite big_nil.        
      rewrite big_nat_recr //= ih.
      case E: (i < j)%nat.
      - rewrite /e; have ->: i == j = false by apply/ltn_eqF; rewrite E.
        by rewrite Rapw0 leqW // addr0.
      case E': (i == j)%nat.
      - rewrite /e E' Rapw1 /GRing.add/= Rplus_0_l.
        by move: E' => /eqP ->; case: ifP => // /leP//.
      rewrite /e E' Rapw0 addr0.
      case: ifP => // ineq.
      exfalso; move: E' => /eqP neq; apply/neq.
    Admitted.

    Lemma lp_e i: (e i) \from l_ p.
    Proof.
      exists 1.
      move => _ [j ->].
      rewrite pnrms_e.
      by case: (i < j)%nat; lra.
    Qed.

    Notation lp := (lp_NormedModule pspec).
    Definition sbs i: lp:= exist _ _ (lp_e i).

    Canonical Ml (G: AbelianGroup): Monoid.law (@zero G) :=
      Monoid.Law plus_assoc plus_zero_l plus_zero_r.

    Notation "x - y" := (minus x y).
    Notation "\| x |" := (norm x).

    Lemma lim_norm xn (x: lp_NormedModule pspec):
      limit xn x <-> limit (fun n => norm (minus x (xn n))) 0.
    Proof.
      split => lim eps eg0; have [N prp]:= lim eps eg0; exists N => m ineq.
      - rewrite /d/= Rminus_0_l Rabs_Ropp Rabs_pos_eq; last by apply/norm_pos; lra.
        exact/prp.
      have := prp m ineq.
      by rewrite /d/= Rminus_0_l Rabs_Ropp Rabs_pos_eq; last by apply/norm_pos; lra.
    Qed.

    Lemma sbs_lim x:
      limit (fun n => \big[plus/zero]_(0 <= i < n) scal (sval x i) (sbs i)) x.
    Proof.
      apply/lim_norm.
      
      have := pnrm_lim.
      
      rewrite /limit /= => eps eg0.
    rewrite /d /=.
    
    Lemma fsys_sbs: fundamental_system (sbs: nat -> lp).
    Proof.
      move => x eps eg0.
      have neq: p <> 0 by lra.
      have:= @norm_spec p neq x.
      rewrite ppnrm_pnrm ppnrm_lim; case => _ lmt.
      have epg0: 0 < Rabs_power eps p by apply/Rapw_lt; lra.
      have [N prp]:= lmt (`|eps`|^p) epg0.
      exists (\big[plus/zero]_(0 <= i < N) scal (sval x i) (sbs i : lp)).
      split.
      - have eltsbs i: (sbs i) \from codom (F2MF sbs) by exists i.
        exists (map (fun i => (sval x i, exist _ _ (eltsbs i))) (iseg id N)).
        rewrite big_map /=.
        elim: (N) => [ | n ih] ; first by rewrite big_nil.
        by rewrite /= big_cons big_nat_recr //= plus_comm ih.
      rewrite /d /= /norm/=.
      rewrite -[X in X <= _]Rabs_pos_eq; last exact/norm_pos.
      rewrite -(Rabs_pos_eq eps); try lra.
      apply (@Rapw_le_inv p); try lra.
      apply/Rle_trans/prp; last by have: (N <= N)%nat by trivial.
      suff ->: \|minus x (\big[plus/zero]_(0<= i < N) scal (sval x i) (sbs i))|
        =
        `|d (`|\|x|`|^p) (p_norm_seq p (projT1 x) N.+1)`|^/p.
      rewrite Rapw_inv; try lra.
      rewrite Rabs_pos_eq; last exact/dst_pos.
      exact/Rle_refl.
      apply/norm_eq; try lra.
      rewrite /d/=/ptwn_op/ptwn/=.
      apply/ppnrm_pnrm; split; first exact/Rapw_pos.
      rewrite Rapw_inv; try lra.
      rewrite Rabs_pos_eq; last exact/Rabs_pos.
      rewrite /d/=.
      eapply/Req_le.
      
      Search _ (_ = _ -> _ <= _).
      Search _ Rabs_power.
      rewrite /d /= in prp.
      

      apply/Rle_trans/(prp N)=>//.
      Search _ "tri" "inv".