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
  Local Notation "x +_pw y" := (ptwn_op Rplus x y) (at level 35).
  
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

  Definition mult (x y: RN_ModuleSpace): RN_ModuleSpace := (ptw_op Rmult x y).
End RN.
Notation "x *_pw y" := (mult x y) (at level 3).

(*Section lower_reals.
  Inductive lower_real := R2lR: R -> lower_real | infinity.
  Coercion R2lR: R >-> lower_real.
  Local Notation lR := lower_real.

  Definition lR2Rbar (r: lR) : Rbar :=
    match r with
    | R2lR r => Rbar.real r
    | infinity => p_infty
    end.

  Definition lR_plus x y :=
    match x with
    | R2lR x' => match y with
                 | R2lR y' => R2lR (x' + y')
                 | _ => infinity
                 end
    | _ => infinity
    end.

  Lemma lR2Rbar_plus x y: Rbar_plus (lR2Rbar x) (lR2Rbar y) = lR2Rbar (lR_plus x y). 
  Proof. by case: x; case: y. Qed.

  Definition lR_le x y:=
    match y with
    | R2lR y' => match x with
                 | R2lR x' => Rle x' y'
                 | infinity => False
                 end
    | infinity => True
    end.

  Local Notation "x <=_ y" := (lR_le x y) (at level 3).

  Lemma lR2Rbar_le x y: Rbar_le (lR2Rbar x) (lR2Rbar y) <-> lR_le x y.
  Proof. by case: x; case: y. Qed.

  Definition non_negative_reals := {x: R | 0 <= x}.
  Local Notation pos_R := non_negative_reals.

  Inductive non_negative_lower_real:= pR2plR: pos_R -> non_negative_lower_real.
  Notation pos_lR:= non_negative_lower_real.
End lower_reals.*)

Section p_norm.
  Local Notation "x '+_pw' y" := (ptwn_op Rplus x y) (at level 40).
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
  
    Lemma ppnrm_lim x: pow_p_norm x === limit (p_norm_seq x).
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
    
    Lemma pnrm_ppnrm x r : mf_p_norm x r <-> 0 <= r /\ pow_p_norm x (`|r`|^p).
    Proof. by rewrite unlock. Qed.

    Lemma ppnrm_pnrm x r: p <> 0 -> pow_p_norm x r <-> 0 <= r /\ mf_p_norm x (`|r`|^(/p)).
    Proof.
      move => neq; split => [nrm | [pos /pnrm_ppnrm [_ nrm]]]; last first.
      - by rewrite -(Rabs_pos_eq r) //-(Rapw_inv r neq).
      have pos: 0 <= r by apply/ppnrm_pos/nrm.
      split => //; rewrite unlock; split; first exact/Rapw_pos.
      by rewrite Rapw_inv // Rabs_pos_eq.
    Qed.
      
    Lemma pnrm0: mf_p_norm (cnst 0) 0.
    Proof.
      rewrite pnrm_ppnrm; split; first exact/Rle_refl.
      by rewrite Rapw0; apply/ppnrm0.
    Qed.   

    Lemma pnrmN x: mf_p_norm x === mf_p_norm (ptw Ropp x).
    Proof. by move => r; rewrite !pnrm_ppnrm ppnrmN. Qed.    
    
    Lemma pnrm_pos x r: mf_p_norm x r -> 0 <= r.
    Proof. by rewrite unlock; case. Qed.

    Lemma pnrm_lim x: 0 < p -> mf_p_norm x === limit (fun n => `|p_norm_seq x n`|^(/p)).
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

    (*
    Lemma pnrm_lim_neq x: p <> 0 -> (forall n, x n <> 0) ->
                          mf_p_norm x === limit (fun n => `|p_norm_seq x n`|^(/p)).
    Proof.
      move => neq prp r; split => [nrm | lmt].
      - have neq': /p <> 0 by apply/Rinv_neq_0_compat.
        rewrite -(Rabs_pos_eq r); last exact/pnrm_pos/nrm.
        rewrite -(Rapw_inv r neq') Rinv_involutive; last lra.
        rewrite -Uncv_lim.
        apply/(continuity_seq (fun x => Rabs_power x (/p)) (p_norm_seq x)).
        + apply/derivable_continuous_pt.
          exists (/p * `|`|r`|^p`|^(/p -1)).
          apply/Rapw_diff_pos.
          have /ppnrm_pnrm [geq ppnrm]:= nrm.
          exact/Rlt_le_trans/(ppnrm_coef 0)/ppnrm/Rapw_lt.
        move: nrm; rewrite unlock => [[_]].
        by rewrite ppnrm_lim -Uncv_lim.
      rewrite unlock; split; first by apply/lim_pos => [ | n/=]; [exact/lmt | exact/Rapw_pos].
      rewrite ppnrm_lim.
      have eq: p_norm_seq x =1 fun n => `|`|p_norm_seq x n`|^(/p)`|^p.
      - by move => n/=; rewrite Rapw_inv; try lra; rewrite Rabs_pos_eq //; apply/pnrms_pos.
      apply/lim_prpr; first exact/eq.
      rewrite -(Uncv_lim); move: lmt => /Uncv_lim lmt.
      apply/(continuity_seq (Rabs_power^~ p) ) => //.
      apply/derivable_continuous_pt.
      exists (p* `|r`|^(p - 1)).
      apply/Rapw_diff_pos.
      suff ineq: Rabs (x 0%nat) <= r.
      - by apply/Rlt_le_trans/ineq; have := prp 0%nat; split_Rabs; lra.
      apply/lim_inc/Uncv_lim; last first.
    Admitted.
     *)
    
    Lemma dom_pnrm: p <> 0 -> dom mf_p_norm === dom pow_p_norm.
    Proof.
      split => [[r] | [r val]]; first by rewrite unlock => [[_ val]]; exists (`|r`|^p).
      exists (`|r`|^(/p)); rewrite pnrm_ppnrm; split; first exact/Rapw_pos.
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
    
  Section infty_norms.
    Definition infty_p_norm x : Rbar :=
      match (Lim_seq (p_norm_seq x)) with
      | Finite x => `|x`|^(/p)
      | p_infty => p_infty
      | m_infty => p_infty
      end.

    Lemma ipnrm_pos_bar x: Rbar_le 0 (infty_p_norm x).
    Proof.
      by rewrite /infty_p_norm; case: (Lim_seq (p_norm_seq x)) => // r; apply/Rapw_pos.
    Qed.

    Lemma ipnrm_pos x: 0 <= (infty_p_norm x).
    Proof.
      rewrite /infty_p_norm.
      case: (Lim_seq (p_norm_seq x)) => [r | | ]; try apply/Rle_refl.
      exact/Rapw_pos.
    Qed.

    Lemma ipnrm_ex_lim x: ex_lim_seq (p_norm_seq x).
    Proof. exact/ex_lim_seq_incr/pnrms_grw. Qed.

    Lemma ipnrm_is_lim x: 0 < p -> is_lim_seq (fun n => `|p_norm_seq x n`|^(/p)) (infty_p_norm x).
    Proof.
      move => plt.
      rewrite /infty_p_norm.
      have lmt:= Lim_seq_correct (p_norm_seq x) (ipnrm_ex_lim x).
      case E: (Lim_seq (p_norm_seq x)) => [r | | ].
      - apply/(is_lim_seq_continuous (fun x => `|x`|^(/p))); last by rewrite -E.
        exact/continuity_pt_filterlim/Rapw_cont/Rinv_0_lt_compat.
      - move => P [y prp].
        pose Q z:= P (`|z`|^(/p)).
        have loc: Rbar_locally (Lim_seq (p_norm_seq x)) Q.
        - rewrite E; exists (`|y`|^p) => y' ineq.
          apply/prp.
          suff: Rabs y < `|y'`|^(/p) by split_Rabs; lra.
          have lt: 0 < /p by apply/Rinv_0_lt_compat.
          rewrite -(@Rapw_inv y (/p)); try lra.
          apply/Rapw_inc; try lra.
          rewrite Rabs_pos_eq; last exact/Rapw_pos.
          rewrite Rinv_involutive; try lra.
          apply/Rlt_le_trans; first exact/ineq.
          by split_Rabs; lra.
        have [N cnd]:= lmt _ loc.
        exists N => n Nln.
        exact/cnd.
      exfalso; have loc: Rbar_locally m_infty (Rlt^~ 0) by exists 0; move => y'; lra.
      rewrite -E in loc.
      have [n prp]:= lmt (fun x => x < 0) loc.
      apply/Rle_not_lt/(prp n) => //.
      exact/pnrms_pos.      
    Qed.

    Lemma ipnrm_spec x: 0 < p ->
      (exists nrm, infty_p_norm x = Finite nrm /\ mf_p_norm x nrm) \/ infty_p_norm x = p_infty.
    Proof.
      move => plt.         
      have:= @ipnrm_is_lim x plt.
      case: (infty_p_norm x) => [r lmt | | lmt]; try by right.
      - left; exists r; split => //.
        exact/pnrm_lim/Uncv_lim/is_lim_seq_Reals/lmt.
      exfalso; have loc: Rbar_locally m_infty (Rlt^~ 0) by exists 0.
      have [n prp]:= lmt (fun x => x < 0) loc.
      apply/Rle_not_lt/(prp n) => //.
      exact/Rapw_pos.
    Qed.

    Lemma ipnrm_ndom x: 0 < p -> infty_p_norm x = p_infty <-> ~ x \from dom mf_p_norm.
    Proof.
      move => plt.
      have iplt: 0 < /p by apply/Rinv_0_lt_compat.
      split => [eq [r nrm] | ndm]; last first.
      - case : (ipnrm_spec x) => // [[r [nrm eq]]].
        by exfalso; apply/ndm; exists r.
      have prp: Rbar_locally (infty_p_norm x) [eta Rlt r] by rewrite eq; exists r.
      have [N cnd]:= ipnrm_is_lim plt prp.
      apply/Rle_not_lt/(cnd N) => //.
      rewrite -(Rabs_pos_eq r); last exact/pnrm_pos/nrm.
      rewrite -(@Rapw_inv r (/p)); try lra.
      rewrite Rinv_involutive; try lra.
      apply/Rapw_inc_le; try lra.
      rewrite !Rabs_pos_eq; try exact/Rapw_pos; try exact/pnrms_pos.
      apply/ppnrm_leq.
      by have /pnrm_ppnrm []:= nrm.
    Qed.

    Lemma ipnrm_pnrm x r: 0 < p -> mf_p_norm x r <-> infty_p_norm x = r.
    Proof.
      move => plt; split => [nrm | ].
      - case: (ipnrm_spec x plt) => [[r' [eq nrm']] | /ipnrm_ndom ndm].
        + by rewrite (pnrm_sing _ nrm nrm'); try lra.
        by exfalso; apply/ndm => //; exists r.
      rewrite /infty_p_norm //.
      case E: (Lim_seq (p_norm_seq x)) => [r0 | | ]// [<-].
      apply/pnrm_ppnrm; split; first exact/Rapw_pos.
      rewrite Rapw_inv; try lra.
      suff rpos: (0 <= r0).
      rewrite Rabs_pos_eq // ppnrm_lim -Uncv_lim /= -is_lim_seq_Reals -E.
      apply/Lim_seq_correct/ipnrm_ex_lim.
      apply/lim_pos; last by move => n; apply/pnrms_pos.
      apply/Uncv_lim/is_lim_seq_Reals; rewrite -E.
      exact/Lim_seq_correct/ipnrm_ex_lim.      
    Qed.

    Lemma ipnrm_pnrm_eq x r: 0 < p -> mf_p_norm x r -> infty_p_norm x = r.
    Proof. by intros; apply/ipnrm_pnrm. Qed.

    Lemma ipnrm_ppnrm x r: 0 < p -> pow_p_norm x (Rabs r) <-> infty_p_norm x = real (`|r`|^(/p)).
    Proof.
      move => plt.
      split => [/ppnrm_pnrm [ | pos /ipnrm_pnrm ->] | eq]; try lra; first by rewrite Rapw_Rabs.
      apply/ppnrm_pnrm; try lra.
      split; first exact/Rabs_pos.
      apply/ipnrm_pnrm; try lra.
      by rewrite Rapw_Rabs.
    Qed.

    Lemma ipnrm_ppnrm_eq x r: 0 < p -> pow_p_norm x (Rabs r) -> infty_p_norm x = real (`|r`|^(/p)).
    Proof. by intros; apply/ipnrm_ppnrm. Qed.

    Lemma ipnrm0: 0 < p -> infty_p_norm (cnst 0) = 0.
    Proof. by move => plt; apply/ipnrm_pnrm/pnrm0. Qed.

    Lemma Rbar_mult_pinfty_r (x: R): 0 < x -> Rbar_mult x p_infty = p_infty.
    Proof.
      move => ineq.
      rewrite /Rbar_mult /=.
      case: (Rle_dec 0 x) => [le | ]; try lra.
      by case: (Rle_lt_or_eq_dec 0 x le); try lra.
    Qed.

    Lemma Rbar_mult_pinfty_l (x: R): 0 < x -> Rbar_mult p_infty x = p_infty.
    Proof.
      move => ineq.
      rewrite /Rbar_mult /=.
      case: (Rle_dec 0 x) => [le | ]; try lra.
      by case: (Rle_lt_or_eq_dec 0 x le); try lra.
    Qed.
  End infty_norms.    

  Section lp_norm.
    Definition lp := make_subset (fun x => has_ub (p_norm_seq x)).    
    Definition p_norm (x: lp):= iota (mf_p_norm (projT1 x)).
    Notation "\| x \|_p" := (p_norm x) (format "'\|' x '\|_p'").
    Hypothesis pn0: p <> 0.
      
    Lemma lp_spec: lp === dom mf_p_norm.
    Proof. by move => x; rewrite dom_lp. Qed.
    
    Lemma norm_spec (x: lp): mf_p_norm (sval x) (\|x\|_p).
    Proof.
      move: x => [x lp].
      have [r nrm]:= (lp_spec x).1 lp.
      apply/(@iota_correct R_AbsRing R_CompleteNormedModule (fun r => mf_p_norm x r)).
      exists r; split => // r' nrm'.
      by rewrite (pnrm_sing _ nrm nrm') //; lra.
    Qed.
    
    Lemma norm_eq (x: lp) r: mf_p_norm (projT1 x) r -> \|x\|_p = r.
    Proof. by move => nrm; apply/pnrm_sing/nrm/norm_spec. Qed.

    Lemma norm_ipnrm x: 0 < p ->
      \|x\|_p = infty_p_norm (sval x).
    Proof.
      move => plt; apply/norm_eq.
      move: x => [ /=x /lp_spec [r nrm]].
      by have ->:= (ipnrm_pnrm x r plt).1 nrm.
    Qed.
      
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

    Lemma lp0: cnst 0 \from lp.
    Proof.
      exists 0 => _ [i ->].
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
Notation "'\|' x '\|_' p" := (infty_p_norm p x) (format "'\|' x '\|_' p", at level 2).

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
    Local Notation "\| x |" := (p_norm x) (at level 2, format "'\|' x '|'").
    Local Notation "x <=_ y" := (Rbar_le x y) (at level 35).
    Local Notation "x *_ y" := (Rbar_mult x y) (at level 25).
    Lemma scal_mult_l x y a: scal a (x *_pw y) = (scal a x) *_pw y.
    Proof. by rewrite /scal/mult/ptw_op/=/scale; apply/functional_extensionality => n; ring. Qed.
      
    Lemma scal_mult_r x y a: scal a (x *_pw y) = x *_pw (scal a y).
    Proof. by rewrite /scal/mult/ptw_op/=/scale; apply/functional_extensionality => n; ring. Qed.

    Lemma Hoelder's_inequality_mf x y p norm_x norm_y:
      1 < p -> mf_p_norm p x norm_x -> mf_p_norm (p/(p-1)) y norm_y ->
      exists norm_xy, mf_p_norm 1 (x *_pw y) (norm_xy) /\ norm_xy <= norm_x * norm_y.
    Proof.
      move => plt.
      have ->: p/(p-1) = /(1-/p) by field; lra.
      set q := /(1-/p).
      move => nrmx nrmy.
      have p01: 0 < /p < 1.
      - by split; [apply/Rinv_0_lt_compat | rewrite -Rinv_1; apply/Rinv_lt_contravar]; lra.
      have pspec: 1 <= p by lra.
      have qlt: 1 < q by rewrite /q -{1}Rinv_1; apply/Rinv_lt_contravar; lra.
      have qspec: 1 <= q by lra.
      have h: /p + /q = 1 by rewrite /q; field; lra.
      have lpx: x \from l_ p by rewrite lp_spec; try lra; exists norm_x.
      pose x' := exist _ _ lpx: lp_ModuleSpace pspec.
      have lqy: y \from l_ q by rewrite lp_spec; try lra; exists norm_y.
      pose y' := exist _ _ lqy: lp_ModuleSpace qspec.
      case: (total_order_T norm_x 0) => [[ineq | eq] | ineq]; first by have := pnrm_pos nrmx; lra.
      - exists 0; rewrite eq; rewrite eq in nrmx; split; try lra.
        suff->: x *_pw y = cnst 0 by apply/pnrm0.
        apply/functional_extensionality => n.
        rewrite /cnst/mult/ptwn_op /=.
        suff -> : x n = 0 by lra.
        suff: Rabs (x n) <= 0 by have:= Rabs_pos (x n); split_Rabs; lra.
        by apply/pnrm_coef/nrmx; lra.
      pose u := scal (/ norm_x) x'.
      have nu1: \|u| = 1.
      - rewrite /u/= -(Rinv_l (norm_x)); try lra.
        apply/norm_eq; try lra.
        rewrite /= -{2}(Rabs_pos_eq (/ norm_x)); last exact/Rlt_le/Rinv_0_lt_compat.
        by apply/pnrm_hom; try lra.
      case: (total_order_T (norm_y) 0) => [[ineq' | eq] | ineq']; first by have := pnrm_pos nrmy; lra.
      - exists 0; rewrite eq; rewrite eq in nrmy; split; try lra.
        suff->: x *_pw y = cnst 0 by apply/pnrm0.
        apply/functional_extensionality => n.
        rewrite /cnst/mult/ptwn_op /=.
        suff -> : y n = 0 by lra.
        suff: Rabs (y n) <= 0 by have:= Rabs_pos (y n); split_Rabs; lra.
        by apply/pnrm_coef/nrmy; lra.
      pose v := scal (/ norm_y) y'.
      have nv1: \|v| = 1.
      - rewrite /v/= -(Rinv_l norm_y); try lra.
        apply/norm_eq; try lra.
        rewrite /= -{2}(Rabs_pos_eq (/ norm_y)); last exact/Rlt_le/Rinv_0_lt_compat.
        by apply/pnrm_hom; try lra.
      suff [r [nrmuv bnd]]: exists r, mf_p_norm 1 (ptwn_op Rmult (sval u) (sval v)) r /\ r <= 1.
      - exists (norm_y * norm_x * r); split; last first.
        + rewrite (Rmult_comm norm_y) Rmult_assoc -{2}(Rmult_1_r norm_y).
          exact/Rmult_le_compat_l/Rmult_le_compat_l/bnd/pnrm_pos/nrmy/pnrm_pos/nrmx.
          rewrite -(Rabs_pos_eq (norm_y * norm_x)); last exact/Rmult_le_pos/pnrm_pos/nrmx/pnrm_pos/nrmy.
        have ->: x *_pw y = scal (norm_y * norm_x) (scal (/ (norm_x * norm_y)) x *_pw y).  
        + by rewrite /scal/mult/ptw_op/= /scale; apply/functional_extensionality => n; field; lra.
        apply/pnrm_hom; try lra.
        rewrite Rinv_mult_distr; try lra.
        by rewrite -scal_assoc scal_mult_r scal_mult_l.
      suff uvl1: forall n, p_norm_seq 1 ((sval u) *_pw (sval v)) n <= 1.
      - have/lp_spec [ | r nrm]: (sval u) *_pw (sval v) \from l_ 1 by exists 1 => _ [n ->]; apply/uvl1.
        + lra.
        exists r; split => //.
        apply/lim_inc/lim_cnst/pnrm_lim/nrm; try lra.
        by move => i; rewrite /cnst Rinv_1 Rapw_p1 Rabs_pos_eq; [apply/uvl1 | apply/pnrms_pos].
      suff seq : forall n, p_norm_seq 1 (sval u) *_pw (sval v) n <= p_norm_seq p (sval u) n /p + p_norm_seq q (sval v) n /q.
      - move => n.
        apply/Rle_trans; first exact/seq.
        have ->: 1 = `|\|u|`|^p * /p + `|\|v|`|^q * /q by rewrite nu1 nv1 !Rapw1; lra.
        apply/Rplus_le_compat/Rmult_le_compat_r/ppnrm_leq; try by apply/Rlt_le/Rinv_0_lt_compat; lra.
        + apply/Rmult_le_compat_r/ppnrm_leq; first by apply/Rlt_le/Rinv_0_lt_compat; lra.
          by have /pnrm_ppnrm []: mf_p_norm p (sval u) (\|u|) by apply/norm_spec; lra.
        by have /pnrm_ppnrm []: mf_p_norm q (sval v) (\|v|) by apply/norm_spec; lra.
      elim => [ | n ih]; first by rewrite /p_norm_seq !big_nil /Rdiv /GRing.zero /=; lra.
      rewrite !pnrmsS Rapw_p1 {2}/mult/ptw_op.     
      by have := Young's_inequality (sval u n) (sval v n) pspec qspec h; lra.
    Qed.

    Theorem Hoelder's_inequality_infty p x y: 1 < p -> \|x *_pw y\|_1 <=_ \|x\|_p *_ \|y\|_(p/(p-1)).
    Proof.
      set q := p/(p-1) => plt.
      have p01: 0 < /p < 1.
      - by split; [apply/Rinv_0_lt_compat | rewrite -Rinv_1; apply/Rinv_lt_contravar]; lra.
      have pspec: 1 <= p by lra.
      have qlt: 1 < q.
      - rewrite /q /Rdiv -{1}(Rinv_r (p-1)); try lra.
        by apply/Rmult_lt_compat_r; try lra; apply/Rinv_0_lt_compat; lra.
      have qspec: 1 <= q by lra.
      have h: /p + /q = 1 by rewrite /q; field; lra.
      case: (@ipnrm_spec p x) => [ | [norm_x [-> nrm]] | ->]; try lra.
      - case: (@ipnrm_spec q y) => [ | [norm_y [-> nrm']] | eq]; try lra.
        + have [nrm_xy [nrmxy ineq]]:= Hoelder's_inequality_mf plt nrm nrm'.
          have [ | [nrm_xy' [-> nrmxy']] | /ipnrm_ndom ndm]:= @ipnrm_spec 1 (x *_pw y); first lra.
          - by rewrite (pnrm_sing _ nrmxy' nrmxy); try lra.
          exfalso; apply/ndm; try lra.
          by exists nrm_xy.
        case: (pnrm_pos nrm) => [ineq | eq'].
        + by rewrite eq Rbar_mult_pinfty_r // /Rbar_le; case: (infty_p_norm 1 x *_pw y).
        suff ->: x *_pw y = cnst 0.  
        * rewrite ipnrm0; try lra; rewrite eq /=.
          case: (Rle_dec 0 norm_x) => [H | ]; try lra.
          by case: (Rle_lt_or_eq_dec 0 norm_x H); try lra.
        rewrite /mult/ptw_op/cnst; apply/functional_extensionality => n.
        have -> : x n = 0 by have := pnrm_coef n _ nrm; split_Rabs; lra.
        by rewrite Rmult_0_l.
      case: (@ipnrm_spec q y) => [ | [norm_y [-> nrm]] | ->]; try lra; last first.
      - by case: (infty_p_norm 1 x *_pw y).
      case: (pnrm_pos nrm) => [ineq | eq'].
      - by rewrite Rbar_mult_pinfty_l // /Rbar_le; case: (infty_p_norm 1 x *_pw y).
      suff ->: x *_pw y = cnst 0.    
      - rewrite ipnrm0 /=; try lra.
        case: (Rle_dec 0 norm_y) => [H | ]; try lra.
        by case: (Rle_lt_or_eq_dec 0 norm_y H); try lra.
      rewrite /mult/ptw_op/cnst; apply/functional_extensionality => n.
      have -> : y n = 0 by have := pnrm_coef n _ nrm; split_Rabs; lra.
      by rewrite Rmult_0_r.
    Qed.

    Lemma Rapw_m1 x p: 0 <= x -> `|x`|^(p - 1) = `|x`|^p/ x.
    Proof.
      rewrite /Rabs_power => pos.
      case: ifP => [_ |/eqP neq]; first by rewrite /Rdiv Rmult_0_l.
      rewrite !Rabs_pos_eq // /Rdiv -{3}(Rpower_1 x); try lra.
      by rewrite -Rpower_Ropp Rpower_plus.
    Qed.

    Notation "x +_pw y":= (@plus RN_ModuleSpace x y) (at level 35).
    Notation "x +_ y" := (Rbar_plus x y) (at level 25).
    Lemma Minkowski's_inequality_mf x y p norm_x norm_y:
      1 <= p -> 
      mf_p_norm p x norm_x -> mf_p_norm p y norm_y ->
      exists norm_xy, mf_p_norm p (x +_pw y) norm_xy /\ norm_xy <= norm_x + norm_y.
    Proof.
      case => [plt1 | eq]; last first.
      - rewrite -eq => nrm nrm'.
        have lp1: x \from l_ 1 by apply/lp_spec; try lra; exists norm_x.
        have lp1': y \from l_ 1 by apply/lp_spec; try lra; exists norm_y.
        have pspec: 1 <= 1 by lra.
        have lt: 0 < 1 by lra.
        have /lp_spec [ | norm_xy nrm'' ] := lpdomD pspec lp1 lp1'; try lra.
        exists norm_xy; split => //.
        apply/lim_inc/limD/pnrm_lim/nrm'/lt/pnrm_lim/nrm/lt/pnrm_lim/nrm''/lt.
        move => n.
        rewrite /ptwn_op/=/p_norm_seq Rinv_1 !Rapw_p1.
        apply/Rle_trans/Rabs_triang.
        rewrite !Rabs_pos_eq.
        elim: n => [ | n ih]; first by rewrite !big_nil; rewrite Rplus_0_r; apply/Rle_refl.
        rewrite !big_nat_recr //=.
        move: ih; rewrite /GRing.add/=.
        suff : `|x n + y n`|^1 <=`|x n`|^1 + `|y n`|^1 by lra.
        rewrite !Rapw_p1.
        exact/Rabs_triang.
        elim: n => [ | n ih]; first by rewrite !big_nil; rewrite Rplus_0_r; apply/Rle_refl.
        rewrite !big_nat_recr //=.
        move: ih; rewrite /GRing.add/=; rewrite !Rapw_p1; split_Rabs; lra.
        elim: n => [ | n ih]; first by rewrite !big_nil; apply/Rle_refl.
        rewrite !big_nat_recr //=.
        move: ih; rewrite /GRing.add/=; rewrite !Rapw_p1; split_Rabs; lra.
      move => /pnrm_ppnrm [pos nrm] /pnrm_ppnrm [pos' nrm']; have plt: 0 < p by lra.
      have pspec: 1 <= p by lra.
      have lpx: x \from l_ p by apply/lp_spec; try lra; exists norm_x; apply/pnrm_ppnrm.
      have lpy: y \from l_ p by apply/lp_spec; try lra; exists norm_y; apply/pnrm_ppnrm.
      have /lp_spec [ | norm_xy /pnrm_ppnrm [pos'' nrm'']]:= lpdomD pspec lpx lpy; try lra.
      exists norm_xy; split; first exact/pnrm_ppnrm.
      case: pos'' => [nlt | <-]; last exact/Rplus_le_le_0_compat/pos'/pos.
      suff ineq: `|norm_xy`|^p <= (norm_x + norm_y) * `|norm_xy`|^p / norm_xy.
      - have l1: 1 <= (norm_x + norm_y)/norm_xy.
        + apply/Rmult_le_reg_l.
          * have neq: norm_xy <> 0 by lra.
            exact/(Rapw_lt p)/neq.
          lra.
        apply/Rmult_le_reg_r; first exact/Rinv_0_lt_compat/nlt.
        by rewrite Rinv_r; lra.
      apply/lim_inc; [move => n | exact/ppnrm_lim/nrm'' | ]; last exact/lim_cnst.
      rewrite /ptwn_op /cnst /p_norm_seq /=.
      have ineq: \sum_(0 <= i < n) `|x i + y i`|^p
                 <= \sum_(0 <= i < n) (Rabs (x i) + Rabs (y i)) * `|x i + y i`|^(p - 1).
      - elim: n => [ | n ih]; first by rewrite !big_nil; apply/Rle_refl.
        rewrite !big_nat_recr //=; apply/Rplus_le_compat; first exact/ih.
        rewrite /Rabs_power.
        case: ifP => [_ |/eqP neq]; first by rewrite mulr0; apply/Rle_refl.
        apply/Rle_trans/Rmult_le_compat_r/Rabs_triang/Rlt_le/exp_pos.
        rewrite -{2}(Rpower_1 (Rabs (x n + y n))); last exact/Rabs_pos_lt.
        by rewrite -Rpower_plus; apply/Req_le; f_equal; lra.        
      apply/Rle_trans; first exact/ineq.
      have pneq: p <> 0 by lra.
      have pneq': /p <> 0.
      - suff: 0 < /p by lra.
        exact/Rinv_0_lt_compat.
      have ->: \sum_(0 <= i < n) (Rabs (x i) + Rabs (y i)) * `|x i + y i`|^(p - 1)
      = p_norm_seq 1 (x *_pw (fun i => `|x i + y i`|^(p - 1))) n +
        p_norm_seq 1 (y *_pw (fun i => `|x i + y i`|^(p - 1))) n.
      - rewrite /p_norm_seq.
        elim: (n) => [ | k ih]; first by rewrite !big_nil Rplus_0_r.
        rewrite !big_nat_recr //= ih mulrDl /GRing.add/= !Rapw_p1 /GRing.mul/=.
        rewrite !Rabs_mult ![Rabs (`|_`|^(p-1))]Rabs_pos_eq; last exact/Rapw_pos.
        ring.
      suff hnrm: mf_p_norm (p/(p - 1)) (fun n => `|x n + y n`|^(p - 1)) (`|norm_xy`|^p/norm_xy).
      - have [ | r [rnrm]]:= Hoelder's_inequality_mf plt1 ((ppnrm_pnrm _ _ _).1 nrm).2 hnrm; try lra.
        rewrite -{1}(Rinv_involutive p)// Rapw_inv // /Rdiv//.
        rewrite Rabs_pos_eq => [xineq |]; last by apply/pnrm_pos/pnrm_ppnrm; split; last exact/nrm.
        have [ | r' [r'nrm]]:= Hoelder's_inequality_mf plt1 ((ppnrm_pnrm _ _ _).1 nrm').2 hnrm; try lra.
        rewrite -{1}(Rinv_involutive p)// Rapw_inv // /Rdiv.
        rewrite Rabs_pos_eq => [yineq |]; last by apply/pnrm_pos/pnrm_ppnrm; split; last exact/nrm'.
        rewrite Rmult_assoc Rmult_plus_distr_r.
        apply/Rle_trans/Rplus_le_compat/yineq/xineq.
        apply/Rplus_le_compat; apply/ppnrm_leq/ppnrm_pnrm => //; split => //.
        - apply/pnrm_pos/rnrm.
          by rewrite Rinv_1 Rapw_p1 (Rabs_pos_eq r); last exact/pnrm_pos/rnrm.
        apply/pnrm_pos/r'nrm.
        by rewrite Rinv_1 Rapw_p1 (Rabs_pos_eq r'); last exact/pnrm_pos/r'nrm.
      rewrite -Rapw_m1; last by lra.
      apply/pnrm_ppnrm; split; first exact/Rapw_pos.
      rewrite ppnrm_lim.
      rewrite /p_norm_seq.
      have eq: forall z, `|`|z`|^(p-1)`|^(p/(p-1)) = `|z`|^p.
      - move => z.
        rewrite /Rabs_power.
        case: ifP; case: ifP => [_ /eqP | _ /eqP] //.
          rewrite /Rpower; have : 0 < exp ((p-1) * ln (Rabs z)) by apply/exp_pos.
          lra.
        move => _.
        rewrite Rabs_pos_eq; last exact/Rlt_le/exp_pos.
        by rewrite Rpower_mult; f_equal; field; lra.
      rewrite eq.
      have ->: (fun n0 => \sum_(0 <= i < n0) `|`|x i + y i`|^(p - 1)`|^(p/(p-1))) =
      fun n0 => \sum_(0 <= i < n0) `|x i + y i`|^p.
      - apply/functional_extensionality; elim => [ | k ih]; first by rewrite !big_nil.
        by rewrite !big_nat_recr //= ih eq.
      by apply/ppnrm_lim.
    Qed.

    Lemma Minkowski's_inequality_infty (x y: RN_ModuleSpace) p:
      1 <= p -> \|x +_pw y\|_p <=_ \|x\|_p +_ \|y\|_p.
    Proof.
      move => pspec; have plt: 0 < p by lra.
      case: (ipnrm_spec x plt) => [[norm_x [-> nrm]] |  ->]; last first.
      - rewrite /Rbar_plus /Rbar_plus' /=.
        case E: (\|y\|_p) => [norm_y | | ]; try by case : (\|plus x y\|_p).
        by have:=ipnrm_pos_bar p y; rewrite E.
      case: (ipnrm_spec y plt) => [[norm_y [-> nrm']] |  ->]; last by case: (\|plus x y\|_p).
      have [nrm_xy [nrm'' ineq]]:= Minkowski's_inequality_mf pspec nrm nrm'.
      by rewrite (ipnrm_pnrm_eq _ nrm''); try lra.
    Qed.
      
    Context (p: R).
    Hypothesis (pspec: 1 <= p).
    Lemma Minkowski's_inequality (x y: lp_ModuleSpace pspec): \|plus x y| <= \|x| + \|y|.
    Proof.
      have pneq: p <> 0 by lra.
      have nrm := norm_spec pneq x; have nrm':= norm_spec pneq y.
      have [r [nrm'' ineq]]:= Minkowski's_inequality_mf pspec nrm nrm'.
      exact/Rle_trans/ineq/Req_le/norm_eq.
    Qed.
      
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

    Lemma e_mult x i: x *_pw (e i) = scal (x i) (e i).
    Proof.
      rewrite /mult/ptw_op; apply/functional_extensionality => n.
      by rewrite /e/scal /=/scale; case: ifP => [/eqP -> | ]; lra.
    Qed.

    Lemma pnrms_e i j: p_norm_seq p (e i) j = if (i < j)%nat then R1 else R0.
    Proof.
      rewrite/p_norm_seq.
      elim: j => [ | j ih]; first by rewrite big_nil.        
      rewrite big_nat_recr //= ih /e.
      case: ifP => [ilj | /negP jli].
      - rewrite /e; have ->: i == j = false by apply/ltn_eqF.
        by rewrite Rapw0 leqW // addr0.
      case: ifP => [/eqP -> | /eqP neq].
      - have ->: (j < j.+1)%nat by trivial.
        by rewrite Rapw1 add0r.
      case: ifP; last by rewrite Rapw0 addr0.
      by rewrite leq_eqVlt => /orP [/eqP [] | ineq]//; exfalso; apply/jli.
    Qed.
(*
    Lemma pnrms_e' (x: RN_ModuleSpace) j: 0 < p ->
      `|p_norm_seq p x j`|^(/p) = \|\big[plus/zero]_(0 <= i < j) x *_pw (e i) \|_p.
    Proof.                                                                        
      move=> plt.
      elim: j => [ | j ih]; first by rewrite /p_norm_seq !big_nil ipnrm0; try lra; rewrite Rapw0.
      rewrite pnrmsS (ipnrm_ppnrm_eq plt (r := p_norm_seq p x j + `|x j`|^p)) //.

      
      rewrite big_nat_recr.
      apply ipnrm_ppnrm_eq.
      rewrite (ipnrm_ppnrm_eq).
      
      apply/ipnrm_ppnrm.
      
      rewrite big_nat_recr.




      Lemma lp_e i: (e i) \from l_ p.
    Proof.
      exists 1 => _ [j ->].
      rewrite pnrms_e.
      by case: (i < j)%nat; lra.
    Qed.

    Notation lp := (lp_NormedModule pspec).
    Definition sbs i: lp:= exist _ _ (lp_e i).

    Canonical Ml (G: AbelianGroup): Monoid.law (@zero G) :=
      Monoid.Law plus_assoc plus_zero_l plus_zero_r.

    Notation "x - y" := (minus x y).
    Notation "\| x |" := (norm x).

    Lemma lim_norm xn (x: lp):
      limit xn x <-> limit (fun n => norm (minus x (xn n))) 0.
    Proof. by rewrite lim_dst. Qed.

    Lemma sbs_lim (x: lp):
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
      *)