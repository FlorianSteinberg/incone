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

  Lemma Qabs_le : forall x a : Q, (-a <= x <= a) -> (Qabs x  <= a).
  Proof.
    move => x a [ax xa].
    apply Qle_Rle in xa.
    apply Qle_Rle in ax.
    rewrite Q2R_opp in ax.
    have temp:= Rabs_le x a.
    have temp2: (\| x | <= a)%R. apply temp; split. apply ax. apply xa.
    apply Rle_Qle.
    by rewrite Qabs_Rabs.
  Qed.


  Lemma Qround_eps_safe x eps : 
    (0 < eps) ->
    Qabs (Qround_eps x eps - x) <= eps.
  Proof.
    move => zero_lt_eps.
    have zero_lt_2eps : 0 < (1+1)*eps by lra.
    (* proved: 0 < (1 + 1)*eps *)

    set inveps2 := 1/((1+1)*eps).
    have zero_lt_inveps : 0 < inveps2 by apply: Qlt_shift_div_l; lra.
    (* proved: 0 < 1/((1 + 1)*eps) *)

    set qZpre := Qceiling inveps2.
    have inveps2_le_qZpre: inveps2 <= inject_Z qZpre by apply: Qle_ceiling.
    (* proved: inveps2 <= inject_Z qZpre *)

    have zeroZ_lt_qZpre: (0 < qZpre)%Z by rewrite Zlt_Qlt; q_order.
    (* proved: 0 < qZpre *)

    set q := Z.to_pos qZpre.
    have q_is_qZpre: Z.pos q = qZpre by apply: Z2Pos.id => //.
    (* proved: Z.pos q = qZpre *)

    set qQ := (Z.pos q # 1).
    have inveps2_lt_q : inveps2 <= qQ.
    unfold qQ.
    rewrite q_is_qZpre => //.
    (* proved: inveps2 <= qQ *)

    have zero_lt_q : 0 < qQ by q_order. 
    have zero_lt_invq : 0 <= / qQ by apply: Qinv_le_0_compat.

    elim: zeroZ_lt_qZpre.

    have half_le_epsq: 1#2 <= eps * qQ.
    1:{

      have temp1 : ((1+1)*eps)*inveps2 == 1 by apply: Qmult_div_r; lra.
      have temp2 : inveps2*((1+1)*eps) <= qQ * ((1+1) * eps) 
        by apply: Qmult_le_compat_r; lra.
      have one_lt_q2eps : 1 <= qQ * ((1+1) * eps) by lra.
      (* proved: 1 <= qQ*2*eps *)

      have z_le_half : 0 <= 1#2 by [].
      have := (Qmult_le_compat_r (1) (qQ*((1+1)*eps)) (1#2) one_lt_q2eps z_le_half).
      rewrite Qmult_1_l.
      have ->: qQ * ((1 + 1) * eps) * (1 # 2) == eps * qQ by field.
      by [].
    }

    (* rewrite the goal: *)
    apply Qabs_le.
    unfold Qround_eps.
    fold inveps2 qZpre q Z.mul qQ.
    split. (* 2 goals *)

    2:{
      have round_qx_le: Qfloor (qQ * x + (1#2)) # q <= (qQ *x + (1#2))/qQ.
      rewrite Qmake_Qdiv.
      unfold inject_Z.
      fold qQ.
      have : (Qfloor (qQ * x + (1 # 2)) # 1) <= (qQ * x + (1 # 2)).
      2:{ move => temp3. apply: Qmult_le_compat_r. apply: temp3. by []. }
      apply: Qfloor_le.
      (* proved: round_qx_le (see above) *)

      have : (qQ * x + (1 # 2)) / qQ <= eps + x.
      2: { 
        move => temp3. 
        move : (QOrder.le_trans round_qx_le temp3). 
        move => temp4.
        by lra.
      } (* reduced goal 1 to the above *)

      have qinvq : qQ * / qQ == 1. by apply: Qmult_inv_r; q_order.

      have : qQ * x + (1 # 2) <= (eps + x) * qQ.
      2: { 
        move => temp3.
        move: (Qmult_le_compat_r _ _ _ temp3 zero_lt_invq).
        have ->: (eps + x) * qQ * / qQ == eps + x by field.
        have ->: (qQ * x + (1 # 2)) * / qQ == (qQ * x + (1 # 2)) / qQ by field.
        by [].
      } (* reduced goal 1 to the above *)

      rewrite Qmult_plus_distr_l.
      rewrite Qplus_comm.
      rewrite Qmult_comm.
      by rewrite Qplus_le_l.
    }

    have round_qx_le: (qQ *x + (1#2) - 1)/qQ <= (Qfloor (qQ * x + (1#2)) # q).
    1: {
      rewrite Qmake_Qdiv.
      rewrite Qmake_Qdiv.
      rewrite Qmake_Qdiv.
      unfold inject_Z.
      fold qQ.
      have : (qQ * x + (1 # 2) - 1) <= (Qfloor (qQ * x + (1 # 2)) # 1).
      2: { move => temp. apply: Qmult_le_compat_r. apply: temp. by []. }
      have := Qlt_floor  (qQ * x + (1#2)).
      unfold inject_Z.
      move => temp.
      rewrite -(Qplus_le_l _ _ 1).
      have temp3: qQ * x + (1 # 2) - 1 + 1 == qQ * x + (1 # 2) by ring.
      rewrite temp3. elim: temp3.
      have ->: (Qfloor (qQ * x + (1 # 2)) # 1) + 1 == Qfloor (qQ * x + (1 # 2)) + 1 # 1.  
      rewrite !Qmake_Qdiv. 
      rewrite inject_Z_plus.
      unfold inject_Z.
      by field.  
      by apply: Qlt_le_weak.
      (* proved: round_qx_le (see above) *)
    }

    have : x - eps <= (qQ * x + (1 # 2) - 1) / qQ.
    2:{
      move => temp3.
      move : (QOrder.le_trans temp3 round_qx_le).
      move => temp4.
      by lra. 
    }

    have : (x-eps)*qQ <= qQ * x + (1 # 2) - 1.
    2:{
      move => temp3.
      move: (Qmult_le_compat_r _ _ _ temp3 zero_lt_invq).
      have ->: (x - eps) * qQ * / qQ == x - eps by field.
      have ->: (qQ * x + (1 # 2) - 1) * / qQ == (qQ * x + (1 # 2) - 1) / qQ by field.
      by [].
    }

    rewrite Qmult_plus_distr_l.
    rewrite Qmult_comm.
    have ->: qQ * x + (1 # 2) - 1 == qQ * x + (- (1 # 2)) by field.
    rewrite Qplus_le_r.
    apply Qopp_le_compat in half_le_epsq.
    have ->: -eps * qQ == -(eps*qQ) by ring.
    by [].

Qed.

End rounding.

Definition rounding_ratio : Q := 1#16.

Definition round_name_RQ (phi : names_RQ) : names_RQ :=
  fun eps => 
    let eps1 := eps * (1-rounding_ratio) in
    let eps2 := eps * rounding_ratio in
    Qround_eps (phi eps1) eps2.

Lemma round_RQ_correct : F2MF round_name_RQ \realizes (id : RQ -> RQ).
Proof.
  rewrite F2MF_rlzr => phi x phinx eps eg0.

  (* rewrite the phinx assumption: *)
  simpl in phinx.

  (* tidy up the goal: *)
  unfold id.
  unfold round_name_RQ.
  set rr := rounding_ratio.
  set rrI := 1 - rr.
  set eps1 := eps * (1-rr).
  set eps2 := eps * rr.

  (* prepare to apply phinx with eps1: *)
  have e1g0: (0 < eps1)%R.
  1:{
    unfold eps1.
    have temp: (0 < rrI)%R.
    2: {
      have temp2 : (0 < eps * rrI)%R by apply: Rmult_lt_0_compat.
      rewrite -Q2R_mult in temp2.
      apply temp2. 
    }
    rewrite -RMicromega.IQR_0.
    by apply: Qlt_Rlt.
  }

  have phinxe1_dist_x := phinx eps1 e1g0.

  (* prepare to apply Qround_eps_safe with eps2: *)
  have e2g0: (0 < eps2).
  1:{
    unfold eps2.
    have temp2 : (0 < eps * rr)%R.
    apply: (Rmult_lt_0_compat) => //. 
    rewrite -RMicromega.IQR_0.
    by apply: Qlt_Rlt.
    rewrite -Q2R_mult in temp2.
    apply: Rlt_Qlt.
    rewrite RMicromega.IQR_0.
    apply temp2. 
  }


  (* apply Qround_eps_safe with eps2 and tidy up: *)
  have qround_dist_e2 := Qround_eps_safe (x := phi eps1) e2g0.
  set roundedx := Qround_eps (phi eps1) eps2.
  fold roundedx in qround_dist_e2.
  apply Qle_Rle in qround_dist_e2.
  rewrite Qabs_Rabs in qround_dist_e2.
  rewrite Q2R_minus in qround_dist_e2.
  rewrite -Rabs_Ropp in qround_dist_e2.

  (* finish the proof using triangle inequality, 
     unifying the arithmetic (Q vs R): *)
  have := Rabs_triang (x - phi eps1) (- (roundedx - phi eps1)%R).
  have ->: ((x - phi eps1) + - (roundedx - phi eps1))%R = (x - roundedx)%R by field.
  move => triang.
  apply: Rle_trans; first exact triang.
  have le_e12 : (\| x - phi eps1 | + \| - (roundedx - phi eps1) | <= eps1 + eps2)%R by apply: Rplus_le_compat.
  apply: Rle_trans; first exact le_e12.
  have e12 : eps1 + eps2 == eps.
  unfold eps1. unfold eps2. by ring.
  apply: Req_le.
  rewrite -Q2R_plus.
  by apply: Qeq_eqR.

Qed.