(* Compatibility with rationals from the standard library *)

From mathcomp Require Import ssreflect seq ssrfun ssrbool ssrnat eqtype.
Require Import all_cs reals mtrc mstrd.
Require Import Qreals Reals Psatz ClassicalChoice FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import QArith.
Local Open Scope R_scope.
Local Open Scope metric_scope.

Section rationals_as_reals.
  Coercion IZR: Z >-> R.
  Fixpoint Pos_size p :=
    match p with
    | xH => 1%nat
    | xI p' => S (Pos_size p')
    | xO p' => S (Pos_size p')
    end.
  
  Lemma Pos_size_gt0 p: (0 < Pos_size p)%nat.
  Proof. by elim p. Qed.
  
  Definition Z_size z:=
    match z with
    | Z0 => 0%nat
    | Z.pos p => Pos_size p
    | Z.neg p => Pos_size p
    end.
  
  Lemma Z_size_eq0 z: Z_size z = 0%nat <-> z = 0%Z.
  Proof.
    split => [ | ->]//.
    case: z => // p/=; have := Pos_size_gt0 p => /leP ineq eq; rewrite eq in ineq; lia.
  Qed.
  
  Lemma Z_size_lt z: IZR z < 2 ^ (Z_size z).
  Proof.
    rewrite pow_IZR; apply IZR_lt; rewrite -two_power_nat_equiv.
    elim: z => // p; elim: p => // p /= ih.
    rewrite !Pos2Z.inj_xI two_power_nat_S.
    have ineq: (Z.pos p + 1 <= two_power_nat (Pos_size p))%Z by lia.
    by apply/ Z.lt_le_trans; last apply Zmult_le_compat_l; [ | apply ineq | ]; lia.
  Qed.

  Lemma Qnum_gt:
	forall eps: Q, (0 < eps)%Q -> (0 < Qnum eps)%Z.
  Proof.
    move => eps epsg0.
    rewrite Zlt_Qlt/inject_Z.
    have eq: eps == Qnum eps # Qden eps by trivial.
    have lt: (0 * (Z.pos (Qden eps)#1) < eps * ((Z.pos (Qden eps))#1))%Q by apply Qmult_lt_compat_r.
    apply Rlt_Qlt.
    have:= (Qlt_Rlt (0 * (Z.pos (Qden eps) # 1)) (eps * (Z.pos (Qden eps) # 1)) (lt)).
    rewrite Q2R_mult /Q2R/= mult_IZR Pos.mul_1_r !Rmult_assoc Rinv_r; last exact: IZR_nz.
    by rewrite Rinv_1.
  Qed.
  
  Lemma size_Qden eps: 0 < Q2R eps -> /2^(Pos_size (Qden eps)) <= Q2R eps.
  Proof.
    move => ineq; rewrite /Q2R/Rdiv /Qdiv -[/_]Rmult_1_l.
    apply Rmult_le_compat; [ | apply Rlt_le; apply Rinv_0_lt_compat; apply pow_lt | | ]; try lra.
    - apply IZR_le; suff: (0 < Qnum eps)%Z by lia.
      by apply Qnum_gt; apply Rlt_Qlt; rewrite {1}/Q2R/=; try lra.
    apply Rinv_le_contravar; first exact /IZR_lt/Pos2Z.is_pos.
    by have /=:= Z_size_lt (Z.pos (Qden eps)); lra.
  Qed.

  Lemma accf_Q2R_0: acc_f_zero_plus Q2R.
  Proof.
    move=> r rPos.
    have ir_Pos : 0 < /r by apply: Rinv_0_lt_compat.
    pose z := up (/ r).
    have irLz : / r < IZR z by rewrite /z; have := archimed (/ r); lra.
    have zPos : 0 < IZR z by lra.
    pose p := Z.to_pos z.
    have pE : (Z.pos p)%Z = z by rewrite Z2Pos.id //; apply: lt_0_IZR.
    exists (1 # p).
    rewrite /Q2R /= pE Rmult_1_l; try lra.
    split; first by apply Rinv_0_lt_compat.
    rewrite -(Rinv_involutive r); try lra.
    by apply: Rinv_lt_contravar; try nra.
  Qed.

  Lemma Z_tech a b : (0 < b -> a / b * b > a  - b)%Z.
  Proof.
    move=> Pb; rewrite {2}(Z_div_mod_eq a b); try lia.
    suffices : (0 <= a mod b < b)%Z by lia.
    by apply: Z_mod_lt; lia.
  Qed.

  Definition Int_partQ eps := ((Qnum eps) / (Z.pos (Qden eps)))%Z.

  Lemma base_Int_partQ eps:
    Int_partQ eps <= Q2R eps /\ Q2R eps < Int_partQ eps + 1.
  Proof.
    have ineq: (Z.pos (Qden eps) > 0)%Z.
    - suffices: (0 < Z.pos (Qden eps))%Z by lia.
      apply lt_IZR; have <-: IPR (Qden eps) = Z.pos (Qden eps) by trivial.
      by rewrite -INR_IPR; apply/pos_INR_nat_of_P.
    split.
    - rewrite -(Rmult_1_r (Qnum eps / Z.pos (Qden eps))%Z).
      rewrite -(Rinv_r (Z.pos (Qden eps))); last exact: IZR_nz.
      rewrite -Rmult_assoc; apply/Rmult_le_compat_r.
      - by apply/Rlt_le/Rinv_0_lt_compat/IZR_lt; lia.
      by rewrite Rmult_comm -mult_IZR; apply/IZR_le/Z_mult_div_ge; lia.
    rewrite /Q2R/Int_partQ.
    have ineq': ((Qnum eps / Z.pos (Qden eps)) * (Z.pos (Qden eps)) > Qnum eps - Z.pos (Qden eps))%Z.
    - by apply/(@Z_tech (Qnum eps) (Z.pos (Qden eps))); lia.
    apply Rlt_gt.
    suffices ineq'': (Qnum eps - Z.pos (Qden eps)) < (Qnum eps / Z.pos (Qden eps))%Z * Z.pos (Qden eps).
    suffices:(Qnum eps * / Z.pos (Qden eps) - 1 < (Qnum eps / Z.pos (Qden eps))%Z) by lra.
    have ->: (Qnum eps * / Z.pos (Qden eps) - 1) = ((Qnum eps  - Z.pos (Qden eps))/ Z.pos (Qden eps)) by field.
    have ->: (IZR(Qnum eps / Z.pos (Qden eps))%Z) =
	((Qnum eps / Z.pos (Qden eps))%Z * Z.pos (Qden eps)/ Z.pos (Qden eps)) by field => //.
    by apply Rmult_lt_compat_r; first by apply/Rinv_0_lt_compat/IZR_lt; lia.
    by rewrite -mult_IZR -minus_IZR; apply IZR_lt; lia.
  Qed.

  Definition upQ eps:= (Int_partQ eps + 1)%Z.
  Lemma archimedQ r:
    IZR (upQ r) > Q2R r /\ IZR (upQ r) - Q2R r <= 1.
  Proof.
    have []:= base_Int_partQ r; rewrite plus_IZR; lra.
  Qed.

  Notation subset := mf_subset.type.

  Lemma Q_dense:
    dense_subset (codom (F2MF Q2R): subset metric_R).
  Proof.
    move => x eps eg0.
    have [q [qg0 qle]]:= accf_Q2R_0 eg0.
    have ieps_pos : 0 < /(Q2R q) by apply: Rinv_0_lt_compat.
    pose aprx:= (inject_Z (Int_part (x / Q2R q)) * q)%Q.
    exists (Q2R aprx); split; first by exists aprx.
    rewrite /distance/=/R_dist/=; have []:= base_Int_part (x / Q2R q); intros.
    have ->: x - Q2R aprx = (x / Q2R q - Int_part (x/Q2R q)) * Q2R q.
    - by rewrite /aprx Q2R_mult {1}/Q2R/=; field; lra.
    rewrite Rabs_mult !Rabs_pos_eq; last rewrite /Rdiv; try lra.
    by rewrite /Rdiv -(Rmult_1_l eps); apply/Rmult_le_compat; lra.
  Qed.

  Lemma Q_sur_dns (r: nat -> Q):
    r \is_surjective -> dense_sequence (Q2R \o_f r: nat -> R_met).
  Proof.
    move => sur; rewrite dseq_dns.
    suff ->: codom (F2MF (Q2R \o_f r)) === codom (F2MF Q2R) by apply/Q_dense.
    rewrite -F2MF_comp_F2MF comp_rcmp; last exact/F2MF_tot.
    move => x; split => [[n [q []]] | [q <-]]; first by exists q.
    by have [n eq]:= sur q; exists n; exists q.
  Qed.
End rationals_as_reals.

Section rationals_and_metric_spaces.
  Context (M: MetricSpace).
  Implicit Types (x y: M).
  Notation subset:= mf_subset.type.
  Lemma dense_Q (A: subset M): dense_subset A <->
    forall x eps, 0 < Q2R eps -> exists y, y \from A /\ d x y <= Q2R eps.
  Proof.
    split => dns x eps eg0; first exact/dns.
    have [q ineq]:= accf_Q2R_0 eg0.
    have [y []]:= dns x q ineq.1.
    exists y; split => //.
    exact/Rlt_le/Rle_lt_trans/ineq.2.
  Qed.

  Lemma cond_eq_Q x y:
    (forall q, d x y <= Q2R q) -> x = y.
  Proof.
    move => prp; apply/dst_eq/cond_eq_f; first exact/accf_Q2R_0.
    intros; rewrite/R_dist Rabs_pos_eq Rminus_0_r; first exact/prp.
    exact/dst_pos.
  Qed.

  Lemma limQ xn x: limit xn x <->
    forall eps, 0 < Q2R eps -> exists N, forall m, (N <= m)%nat -> d x (xn m) <= Q2R eps.
  Proof.
    split => lim eps eg0; first exact/lim.
    have [q ineq]:= accf_Q2R_0 eg0.
    have [N prp]:= lim q ineq.1.
    exists N => m Nlm.
    exact/Rlt_le/Rle_lt_trans/ineq.2/prp.
  Qed.
End rationals_and_metric_spaces.