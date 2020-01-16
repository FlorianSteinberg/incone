From mathcomp Require Import ssreflect seq ssrfun ssrbool ssrnat eqtype bigop.
From rlzrs Require Import all_rlzrs.
From metric Require Import all_metric reals standard Qmetric.
Require Import axioms all_cs cs_mtrc metric_names hyper_spaces Q_reals.
Require Import Qreals Qround QOrderedType Reals Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import QArith ZArith.

Set Printing Coercions.

Section rounding.
  Definition Qround_eps (x eps : Q) :=
    let qZpre := Qceiling (1/((1+1)*eps)) in
    let q := Z.to_pos qZpre in
    let qQ := (Zpos q # 1) in
    let p := Qfloor (qQ*x+(1 # 2)) in
    p # q.

  Lemma Qabs_le x a: -a <= x <= a -> Qabs x  <= a.
  Proof.
    intros; apply/Rle_Qle; rewrite Qabs_Rabs.
    by split_Rabs; try rewrite -Q2R_opp; apply/Qle_Rle; lra.
  Qed.

  Lemma Qround_eps_safe x eps: 0 < eps -> Qabs (Qround_eps x eps - x) <= eps.
  Proof.
    move => eg0.
    
    set inveps2 := 1/((1+1)*eps).
    have zero_lt_inveps : 0 < inveps2 by apply/Qlt_shift_div_l; lra.

    set qZpre := Qceiling inveps2.
    have inveps2_le_qZpre: inveps2 <= inject_Z qZpre by apply/Qle_ceiling.

    have zeroZ_lt_qZpre: (0 < qZpre)%Z by rewrite Zlt_Qlt; q_order.

    set q := Z.to_pos qZpre.
    have q_is_qZpre: Z.pos q = qZpre by apply/Z2Pos.id.

    set qQ := Z.pos q # 1.
    have inveps2_lt_q: inveps2 <= qQ by rewrite/qQ q_is_qZpre.

    have zero_lt_invq: 0 <= / qQ by apply/Qinv_le_0_compat.

    have half_le_epsq: 1#2 <= eps * qQ.
    - suff: (1+1)*eps *inveps2 == 1 by nra.
      by apply/Qmult_div_r; lra.

    have round_qx_le: (qQ *x + (1#2) - 1)/qQ <= (Qfloor (qQ * x + (1#2)) # q).
    - rewrite !Qmake_Qdiv/inject_Z.
      suff temp: qQ * x + (1 # 2) - 1 <= Qfloor (qQ * x + (1 # 2)) # 1 by apply/Qmult_le_compat_r.
      rewrite -(Qplus_le_l _ _ 1); have ->: qQ * x + (1 # 2) - 1 + 1 == qQ * x + (1 # 2) by ring.
      suff->:(Qfloor (qQ * x + (1 # 2)) # 1) + 1 == Qfloor (qQ * x + (1 # 2)) + 1 # 1.
      + by apply/Qlt_le_weak;have := Qlt_floor  (qQ * x + (1#2)).
      by rewrite !Qmake_Qdiv inject_Z_plus /inject_Z; field.  

    apply Qabs_le; rewrite /Qround_eps-/inveps2-/qZpre-/q-/Z.mul-/qQ; split.
    - suff: x - eps <= (qQ * x + (1 # 2) - 1) / qQ by nra.
      have H: (x-eps) * qQ <= qQ * x + (1 # 2) - 1 by nra.
      move: (Qmult_le_compat_r _ _ _ H zero_lt_invq).
      have ->: (x - eps) * qQ * / qQ == x - eps by field.
      by have ->: (qQ * x + (1 # 2) - 1) * / qQ == (qQ * x + (1 # 2) - 1) / qQ by field.
    have temp3: qQ * x + (1 # 2) <= (eps + x) * qQ by nra.
    have:= Qmult_le_compat_r _ _ _ temp3 zero_lt_invq.
    have ->: (eps + x) * qQ * / qQ == eps + x by field.
    have ->: (qQ * x + (1 # 2)) * / qQ == (qQ * x + (1 # 2)) / qQ by field.
    suff: Qfloor (qQ * x + (1#2)) # q <= (qQ *x + (1#2))/qQ by lra.
    by rewrite Qmake_Qdiv; apply/Qmult_le_compat_r; first exact/Qfloor_le.      
  Qed.

  Definition rounding_ratio := 1#16.

  Definition round_name_RQ (phi : names_RQ) : names_RQ :=
    fun eps => 
      let eps1 := eps * (1-rounding_ratio) in
      let eps2 := eps * rounding_ratio in
      Qround_eps (phi eps1) eps2.
  
  Lemma round_RQ_correct : F2MF round_name_RQ \realizes (id : RQ -> RQ).
  Proof.
    rewrite F2MF_rlzr => phi x phinx eps eg0.
    have /Qeq_eqR -> : eps == eps*(1-rounding_ratio) + eps*rounding_ratio by ring.
    rewrite Q2R_plus; apply /Rle_trans/Rplus_le_compat; last first.
    - apply/Qle_Rle/(Qround_eps_safe (x:=(phi (eps*(1-rounding_ratio)))))/Rlt_Qlt.
      rewrite Q2R_mult {1}/Q2R /=.
      suff: (0 < Q2R rounding_ratio)%R by nra.
      by rewrite /Q2R /=;lra.
    - apply phinx; rewrite Q2R_mult Q2R_minus {2}/Q2R/=.
      suff: (Q2R rounding_ratio < 1)%R by nra.
      by rewrite /Q2R /=;lra.
    by rewrite/round_name_RQ Qabs_Rabs Q2R_minus /id; split_Rabs;lra.
  Qed.
End rounding.

Require Import Coq.Lists.StreamMemo.
Definition to_int (q : Q) :=  (Pos.to_nat (Qden q)).
Definition from_int (p : nat) := (1 # (Pos.of_nat p)).
Definition memoize_real (phi : nat -> Q) := let p := (memo_list Q phi) in
                                                     fun n => memo_get Q n p.
Definition round_name_RQ' (phi : names_RQ) : names_RQ := (memoize_real ( (round_name_RQ phi) \o_f from_int)) \o_f to_int. 
Lemma round_RQ'_correct : F2MF round_name_RQ' \realizes (id : RQ -> RQ).
Proof.
Admitted.
