From mathcomp Require Import ssreflect seq ssrnat ssrbool eqtype ssrfun.
From mf Require Import all_mf.
Require Import Q_reals.
Require Import all_cont FMop.
Require Import iseg.
Require Import Coquelicot.PSeries.
Require Import Setoid.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Coquelicot.Coquelicot.
From metric Require Import reals metric standard Qmetric.
Require Import Qreals Reals Psatz ClassicalChoice FunctionalExtensionality.
Require Import ProofIrrelevance ProofIrrelevanceFacts.
Require Import Interval.Interval_tactic.
Import QArith.

From rlzrs Require Import all_rlzrs.
Require Import all_cs cs_mtrc.

Section names_for_realizers.
  Definition names_RQ := (Q->Q).
  Definition names_RQw := ((nat*Q)->Q).
  Definition ps_names := ((unit+unit)+(nat*Q))->((nat*nat)*Q).
  Definition psx_names := ((unit+unit)+(nat*Q)+Q)->((nat*nat)*Q*Q).
  Definition RQ_pair (a:Q->Q) (b:Q->Q) := (pair 0%Q 0%Q (a,b)).
End names_for_realizers.

Section powerseries_basic_facts.
  Definition single_element_seq (m : nat) x := (fun n => (if (n == m) then x else 0%R)).

  Lemma single_element_seq_zeros m x : forall k, (k != m) -> ((single_element_seq m x) k) = 0%R.
  Proof.
  move => k k_prop.
  rewrite /single_element_seq. 
    by apply ifN_eq.
  Qed.

  Lemma single_element_seq_bound m x : (0 <= x)%R -> forall (n : nat), (0 <= ((single_element_seq m x) n) <= x)%R.
  Proof.
    move => H n.
    case e : (n != m).
      - rewrite single_element_seq_zeros; by [lra | apply e].
    apply negb_true_iff in e.
    rewrite negb_involutive in e.
    rewrite /single_element_seq.
    by rewrite ifT; first by lra.
  Qed.

  Lemma single_element_sum_zero m x n : (n < m)%nat -> (sum_n (single_element_seq m x) n) = 0%R.
  Proof.
    elim: n => [H | n IH H]; first by rewrite sum_O;apply ifN_eqC; apply (lt0n_neq0 H).
    rewrite sum_Sn.
    have H' : (n < m)%nat by auto.
    rewrite (IH H').
    rewrite plus_zero_l.
    have lt := (neq_ltn n.+1 m).
    symmetry in lt.
    have triv : (n.+1 < m)%nat || (m < n.+1)%nat by rewrite H.
    apply ifN_eq.
    by rewrite triv in lt.
  Qed.

  Lemma single_element_sum_val m x : (sum_n (single_element_seq m x) m) = x.
  Proof.
    case m => [| n]; first by rewrite sum_O.
    rewrite sum_Sn.
    rewrite single_element_sum_zero; last by [].
    by rewrite plus_zero_l; apply ifT.
  Qed.

  Lemma single_element_sum_zero2 m x n n' : (m < n)%nat -> (sum_n_m (single_element_seq m x) n n') = 0%R.
  Proof.
    move => H.
    have S := (sum_n_m_ext_loc (single_element_seq m x) (fun _ => 0%R) n n').
    rewrite sum_n_m_const_zero in S.
    apply S.
    move => k [k_prop1 k_prop2].
    have H' : (m < n)%coq_nat by apply /leP.
    have k_prop' : (m < k)%coq_nat by lia.
    have k_prop'' : (m < k)%nat by apply /ltP.
    apply single_element_seq_zeros.
    rewrite neq_ltn.
    rewrite k_prop''.
    by apply orbT.
  Qed.

  Lemma single_element_sum m x : forall n, (m <= n)%nat -> (sum_n (single_element_seq m x) n) = x.
  Proof.
    move => n n_prop.
    have C := (sum_n_m_Chasles (single_element_seq m x) 0 m n).
    rewrite /sum_n.
    rewrite C;last by apply /leP.
    - rewrite (single_element_sum_zero2 x n);last by [].
      by rewrite plus_zero_r;apply single_element_sum_val.
   by lia.
  Qed.

  Lemma single_element_sum_lt m x : (0 <= x)%R ->  forall n, ( 0 <= (sum_n (single_element_seq m x) n) <= x)%R.
  Proof.
    move => H n.
    case prop : (n < m)%nat; first by rewrite single_element_sum_zero; by [lra|].
    rewrite single_element_sum; first by lra.
    apply negb_true_iff in prop.
    have l := (leqNgt m n).
    symmetry in l.
    by rewrite l in prop.
  Qed.

  Lemma single_element_sum_limit m x : (Series.Series (single_element_seq m x)) = x.
  Proof.
    rewrite /Series.Series.
    have le := (Lim_seq_ext_loc (sum_n (single_element_seq m x)) (fun n => x)).
    rewrite Lim_seq_const in le.
    rewrite le;first by [].
    exists m.
    move => n n_prop.
    have n_prop' : (m <= n) % nat by apply /leP.
    by apply single_element_sum.
  Qed.

  Lemma positive_sum_grows (a : nat -> R) m: (Series.ex_series a) -> (forall n, (0 <= (a n))%R) -> ((a m) <= (Series.Series a))%R.
  Proof.
    move => H0 H.
    have le := (Series.Series_le (single_element_seq m (a m)) a).
    rewrite single_element_sum_limit in le.
    apply le; last by [].
    move => n.
    case e : (n != m).
    - by rewrite single_element_seq_zeros; by [split; by [lra | apply H]|].
    apply negb_true_iff in e.
    rewrite negb_involutive in e.
    rewrite /single_element_seq.
    rewrite ifT;last by [].
    split;first by apply H.
    have e' : n = m by apply /eqP.
    by rewrite e';lra.
  Qed.

  Lemma M_exists a : forall r : R, (0 < r)%R -> (Rbar_lt r (CV_radius a)) -> exists M : R , forall n, (Rabs(a n) <= M * (/ r) ^ n)%R.
  Proof.
    move => r r_prop1 r_prop2.
    have r_prop1' := (Rgt_ge r 0 (Rlt_gt 0 r r_prop1)).
    have absreqr := (Rabs_right r r_prop1').
    apply symmetry in absreqr.
    rewrite absreqr in r_prop2.
    have := (CV_disk_inside a r r_prop2).
    case => M M_prop.
    exists M.
    move => n.
    have coeffge0 : forall n, (0 <= (Rabs (a n) * (r ^ n))) %R.
    - move => m.
      have pos := (Rle_ge 0 (Rabs (a m)) (Rabs_pos (a m))).
      have pow_pos := (pow_le r m (Rlt_le 0 r r_prop1)).
      apply Rle_ge in pow_pos.
      have Rm := (Rmult_ge_compat_r (r ^ m) (Rabs (a m)) 0 pow_pos pos).
      rewrite Rmult_0_l in Rm.
      by lra;apply Rm.
    have coeff_eq : forall m, (Rabs ((a m) * (r ^ m))) = ((Rabs (a m))*(r ^ m))%R.
    - move => m.
      rewrite Rabs_mult.
      rewrite (Rabs_pos_eq (r ^ m)); first by [].
      have pow_pos := (pow_le r m (Rlt_le 0 r r_prop1)).
      apply Rle_ge in pow_pos.
      by apply (Rge_le (r ^ m) 0 pow_pos).
    have series2 := (Series.is_series_ext (fun n => (Rabs (a n * r^n))) (fun n => ((Rabs (a n) * r^n)) % R) M coeff_eq M_prop).
    have series_exists : (Series.ex_series (fun n => (Rabs (a n) * (r ^ n))%R)) by exists M.
    have psum := (positive_sum_grows n series_exists coeffge0).
    apply Series.is_series_unique in series2.   
    rewrite series2 in psum.
    have e0 : (0 <= (/ r) ^ n)%R.
    - suff: (0 < (/ r) ^ n)%R by lra.
      by apply pow_lt;apply Rinv_0_lt_compat.
    have ra := (Rmult_le_compat_r ((/ r) ^n) (Rabs (a n)*(r ^ n)) M e0 psum).
   have rin := Rinv_pow.
   symmetry in rin.
   rewrite rin in ra;last by apply Rgt_not_eq;apply r_prop1.
   rewrite Rinv_r_simpl_l in ra; last by apply Rgt_not_eq;apply pow_lt.
   by rewrite rin;last by  apply Rgt_not_eq;apply r_prop1.
  Qed.

  Lemma nat_upper r : exists U : nat, (r < (INR U)) % R.
  Proof.
    exists (Z.to_nat (up r)).
   have [arch _] := (archimed r).
   apply Rgt_lt in arch.
   rewrite /Z.to_nat. 
   case e : (up r) => [|a|a]; first by rewrite e in arch.
   - by rewrite INR_IPR;rewrite e in arch.
   rewrite e in arch.
   have lt := (Zlt_neg_0 a).
   apply /Rlt_trans.
   apply arch.
   by apply IZR_lt.
  Qed.

  Definition series1 a := (Rbar_lt (1%R) (CV_radius a)). 
  Definition series_bound a A k := (0 < k)%coq_nat /\ (0 < A)%coq_nat /\ forall n, ((Rabs (a n)) <= (INR A) * (/ (1+/(INR k))) ^ n)%R.
  Lemma Ak_exists a : (series1 a) -> exists A k : nat, (series_bound a A k).
  Proof.
    move => H.
    have e : exists k : nat, (0 < k )%coq_nat /\ (Rbar_lt (1+(/ INR k))%R (CV_radius a)).
    - have := (open_Rbar_lt' 1%R (CV_radius a) H).
      move => [eps H2].
      have [k [k_prop1 k_prop2]] := (archimed_cor1 eps (cond_pos eps)).
      exists k.
      split;first by apply k_prop2.
      apply H2.
      apply /norm_compat1.
      have eq : (minus (1 + (/ (INR k))) 1)%R = (/ (INR k))%R by rewrite /minus;rewrite /opp;rewrite /plus //=;lra.
      rewrite eq/norm //= /abs //=.
      rewrite Rabs_right; first by apply k_prop1.
      apply Rle_ge.
      have lt := (lt_0_INR k k_prop2).
      suff : (0 < (/ (INR k)))%R by lra. 
      by apply Rinv_0_lt_compat.
    case e => k [k_prop1 k_prop2].
    have r_prop : (0 < (1+(/ (INR k))))%R.
    - apply Rplus_lt_0_compat; by [lra | apply Rinv_0_lt_compat;apply lt_0_INR].
    case (M_exists r_prop k_prop2) => M M_prop.
    case (nat_upper M) => A A_prop.
    exists A.+1.
    exists k.
    split; first by apply k_prop1.
    split; first by apply Nat.lt_0_succ.
    move => n.
    apply /Rle_trans.
    apply M_prop.
    apply Rmult_le_compat_r; first by apply pow_le, Rlt_le, Rinv_0_lt_compat.
    by rewrite S_INR; lra.
  Qed.

  Definition powerseries1 := {a : nat -> R | series1 a }.
End powerseries_basic_facts.
Section ps_representation.
  Definition ps_rep : (questions (cs_nat \*_cs cs_nat \*_cs RQ\^w)) ->> powerseries1 := make_mf (fun phi (a : powerseries1) => (rprj phi) \describes (projT1 a) \wrt (RQ\^w) /\ (series_bound (projT1 a) (lprj (lprj phi) tt) (rprj (lprj phi) tt))).

  Lemma ps_rep_sur: ps_rep \is_cototal.
  Proof.
    move  => a.
    have := (Ak_exists (projT2 a)).
    case => A;case => k H.
    have [phi phina]:= (get_description ((A,k,(projT1 a)) : (cs_nat \*_cs cs_nat \*_cs RQ\^w))).
    exists phi.
    split; first by apply phina.
    have eqA : (lprj (lprj phi) tt) = A by apply phina.
    have eqk : (rprj (lprj phi) tt) = k by apply phina.
    rewrite eqA.
    by rewrite eqk.
  Qed.

  Lemma ps_rep_sing: ps_rep \is_singlevalued.
  Proof.
    move => phi [a ap] [b bp] [//=phina _] [phinb _].
    apply subset_eq_compat.
    suff : forall i, (a i) = (b i) by apply functional_extensionality.
    move => i.
    by apply (rep_RQ_sing (phina i) (phinb i)).
  Qed.

  Definition powerseries1_cs := (make_cs (someq (cs_nat \*_cs cs_nat \*_cs RQ\^w)) (somea (cs_nat \*_cs cs_nat \*_cs RQ\^w)) (queries_countable (cs_nat \*_cs cs_nat \*_cs RQ\^w)) (answers_countable (cs_nat \*_cs cs_nat \*_cs RQ\^w)) ps_rep_sur ps_rep_sing).
End ps_representation.
Section ps_summation.
  Lemma series_exists_helper k : (0 < k)%coq_nat -> ((Rabs (/ (1 + / INR k))) < 1)%R.
  Proof.
    move => k_prop.
    rewrite Rabs_right.
    - have lt := (Rinv_1_lt_contravar 1 (1 + (/ INR k))).
      rewrite Rinv_1 in lt.
      apply lt; first by lra.
      suff : (0 < (/ INR k))%R by lra.
      by apply Rinv_0_lt_compat; apply lt_0_INR.
    apply Rgt_ge.
    apply Rinv_0_lt_compat.
    suff : (0 < (/ INR k))%R by lra.
    by apply Rinv_0_lt_compat; apply lt_0_INR.
  Qed.

  Lemma bseries_exists_Rabs a A k : (series_bound a A k) -> (Series.ex_series (fun n => (Rabs (a n)))).
  Proof.
    move => [H1 [H2 H]].
    have H' : forall n : nat, (0 <= (Rabs (a n)) <= (INR A)*(/ (1 + / INR k))^n)%R by split;[apply Rabs_pos|apply H].
    have le := (Series.ex_series_le (fun n => (Rabs (a n))) (fun n => (INR A *(/ (1 + / INR k))^n))%R).
    apply le; first by move => n;rewrite /norm//=/abs//=; rewrite Rabs_Rabsolu.
    have scal := (Series.ex_series_scal (INR A) (fun n=> ((/ (1 + / INR k)) ^ n))%R).
    rewrite /Hierarchy.scal//=/mult//= in scal.
    apply scal.
    by apply Series.ex_series_geom; apply series_exists_helper.
  Qed.
  Lemma pow_le_1_compat : forall x n, (0 <= x <= 1)%R -> ((x ^ n) <= 1)%R.
  Proof.
    move => x n [xB0 xB].
    case n => [ | n']; first by apply Req_le;apply pow_O.
    case xB => xB'.
    - apply Rlt_le.
      apply pow_lt_1_compat; first by split; by [apply Rabs_pos | ].
      by apply Nat.lt_0_succ.
    rewrite xB'.
    by apply Req_le; apply pow1.
  Qed.

  Lemma pow_le_1_compat_abs : forall x n, ((Rabs x) <= 1)%R -> (((Rabs x) ^ n )<= 1)%R.
  Proof.
    move => x n xa.
    apply pow_le_1_compat.
    by split; [apply Rabs_pos | ].
  Qed.

  Lemma bseries_exists_Rabs2 a A k : forall x, (Rabs x <= 1)%R -> (series_bound a A k) -> (Series.ex_series (fun n => (Rabs ((a n) * (x ^ n))))).
  Proof.
    move => x xB sb.
    apply (ex_series_le (fun n => (Rabs ((a n) * (x ^ n)))) (fun n => (Rabs (a n)))); last by apply (bseries_exists_Rabs sb).
    move => n.
    rewrite /norm //= /abs //=.
    rewrite Rabs_Rabsolu Rabs_mult.
    rewrite <- Rmult_1_r.
    apply Rmult_le_compat_l; first by apply Rabs_pos.
    rewrite <- RPow_abs.
    by apply pow_le_1_compat_abs.
  Qed.
  Lemma invp1gt0 k : (0 < k)%coq_nat -> (0 < 1 + /INR k)%R.
  Proof.
    move => H.
    suff: (0 < / INR k)%R by lra.
    apply Rinv_0_lt_compat.
    by apply lt_0_INR.
  Qed.
  Lemma invge0 k : (0 < k)%coq_nat -> (0 <= /(1 + /INR k))%R.
  Proof.
    move => H.
    apply Rlt_le.
    apply Rinv_0_lt_compat.
    by apply invp1gt0.
  Qed.

  Lemma series_tail_approx a A k: (series_bound a A k) -> forall N,  ((Series.Series (fun k => (Rabs (a (N.+1+k)%coq_nat)))) <= (INR A) * (INR k.+1) * (/ (1 + (/ (INR k)))) ^ (N.+1))%R.

  Proof.
    move => H N.
    have [k_prop _] := H.
    have series_exists :  (Series.ex_series (fun n : nat => Rabs (a (succn N + n)%coq_nat))) by apply  (Series.ex_series_incr_n (fun n => (abs (a n))));apply (bseries_exists_Rabs H).
    have H' : forall n, (0 <= (Rabs (a (succn N +n)%coq_nat)) <= INR A * (/ (1 + / INR k)) ^ (succn N + n))%R by split; [apply Rabs_pos|apply H].
    have le := (Series.Series_le (fun n => (Rabs (a ((N.+1)+n)%coq_nat))) (fun n => (INR A *(/ (1 + / INR k))^(N.+1+n))%R) H').
    apply /Rle_trans.
    apply le.
    - have incr := (Series.ex_series_incr_n (fun n => (INR A *(/ (1 + / INR k))^(n))%R) (N.+1)). 
      apply incr.
      have scal := (Series.ex_series_scal (INR A) (fun n=> ((/ (1 + / INR k)) ^ n))%R).
      apply scal.
      by apply Series.ex_series_geom; apply series_exists_helper.
      have scal := (Series.Series_scal_l (INR A) (fun n=> ((/ (1 + / INR k)) ^ (succn N+n)))%R).
      rewrite scal.
      rewrite Rmult_assoc.
      apply (Rmult_le_compat_l); first by apply pos_INR.
      rewrite (Series.Series_ext (fun n : nat => (/ (1 + / INR k)) ^ (succn N + n))%R (fun n =>  (/ (1 + / INR k)) ^ (succn N) * (/ (1 + / INR k)) ^ n)%R); last by apply pow_add.
      have scal' := (Series.Series_scal_l  ((/ (1 + / INR k)) ^ succn N) (fun n=> ((/ (1 + / INR k)) ^ n))%R).
      rewrite scal'.
      rewrite Series.Series_geom;last by apply series_exists_helper.
      rewrite Rmult_comm.
      have simple : (0 < 1 + /INR k)%R.
       - suff: (0 < / INR k)%R by lra.
          apply Rinv_0_lt_compat.
          by apply lt_0_INR.
      have simple2 : (0 <= /(1 + /INR k))%R.
      - apply Rlt_le.
        by apply Rinv_0_lt_compat.
      apply Rmult_le_compat_r; first by apply pow_le; apply simple2.
      apply Req_le.
      have simple' : ((1+(/ INR k)) <> 0)%R by apply not_eq_sym; apply Rlt_not_eq.
      have t : ((1- /(1 + /INR k)) = (/ INR k / (1 + /INR k)))%R.
      - have min := (Rcomplements.Rdiv_minus 1 1 1 (1+ /INR k) R1_neq_R0 simple').
        rewrite Rcomplements.Rdiv_1 in min.
        rewrite Rmult_1_l in min.
        rewrite Rmult_1_r in min.
        have inv := (Rinv_Rdiv (1+ / INR k) 1 simple' R1_neq_R0).
        symmetry in inv.
        rewrite inv in min.
        rewrite Rcomplements.Rdiv_1 in min.
        suff : ((1 + / INR k - 1) = / INR k)%R by lra.
        by lra.
     rewrite t.
     have inrneq0 : ((INR k) <> 0)%R by apply not_eq_sym;apply Rlt_not_eq;apply lt_0_INR.
     rewrite Rinv_Rdiv; last by apply simple'. 
     - rewrite /Rdiv.
       rewrite Rinv_involutive;last by apply inrneq0.
       rewrite Rmult_plus_distr_r.
       rewrite Rmult_1_l.
       rewrite Rinv_l;last by apply inrneq0.
       symmetry.
       by apply S_INR.
     by apply Rinv_neq_0_compat.   
  Qed.

  Lemma tmpn_series_helper1 : forall x, (0 <= x <= (/ 2))%R -> ((exp ((ln 2)*x)) <= 1+x)%R.
  Proof.
    move => x [H1 H2].
    pose f  := (fun x => (exp ((ln 2)*x))).
    pose df  := (fun x => ((ln 2)*exp ((ln 2)*x)))%R.
    have df_prop : forall x, (is_derive f x (df x)).
    - move => x0.
      rewrite /f/df.
      auto_derive; by [ | lra].
    have MVT := (MVT_gen f 0 x df). 
    simpl in MVT.
    case MVT => [t t_prop | t t_prop | t [[t_prop1 t_prop2] M]]; first by apply df_prop.
    - apply derivable_continuous_pt.
      rewrite /f.
      by auto_derive.
    move : M.
    rewrite /f.
    have simpl1 : ((x-0)=x)%R by lra.
    have simpl2 : ((ln 2 * 0)=0)%R by lra.
    rewrite simpl1 simpl2 exp_0.
    rewrite /df.
    move => M.
    have M' : ((exp (ln 2 * x)) <= 1+(ln 2)*(exp (ln 2 * (/ 2)))*x)%R.
    - suff: ((ln 2)*(exp (ln 2 * t))*x <= (ln 2)*(exp (ln 2 * (/ 2)))*x)%R by lra.
      suff:  ((exp (ln 2 * t)) <= (exp (ln 2 * (/ 2))))%R.
      move => H'.
      do 2! rewrite Rmult_assoc.
      apply (Rmult_le_compat_l (ln 2)); first by apply Rlt_le;apply (Rlt_trans 0 (/ 2)); by [lra | apply ln_lt_2].
      by apply (Rmult_le_compat_r x); first by apply H1.
     have exp_increasing' : forall x y : R, (x <= y)%R -> (exp x <= exp y)%R.
     * move => x0 y0.
       case => H'; by [apply Rlt_le; apply exp_increasing | rewrite H'; apply Req_le].
      apply exp_increasing'.
      suff : (t <= (/ 2))%R by apply (Rmult_le_compat_l (ln 2)); apply (Rle_trans 0 (/ 2)); [lra | apply Rlt_le; apply ln_lt_2].
      apply /Rle_trans.
      apply t_prop2.
      by rewrite Rmax_right; by [apply H1 | ].
    suff: ((ln 2)*(exp (ln 2 * (/ 2))) <= 1)%R.
    - move => H'.
      apply /Rle_trans.
      apply M'.
      apply Rplus_le_compat_l.
      suff:  (ln 2 * exp (ln 2 * / 2) * x <= 1*x)%R by lra.
      by apply Rmult_le_compat_r.
    by interval.
  Qed.

  Lemma tmpn_series_helper2 : forall k,  (2 <= (1+(/ INR (k.+1))) ^ (k.+1))%R.
  Proof.
    case.
    rewrite pow_1.
    suff: (1 = (/ INR 1))%R by lra.
    by rewrite Rinv_1.
    move => k. 
    have helper_cond : (0 <= (/ (INR k.+2)) <= (/ 2))%R.
    - split; first by apply Rlt_le;apply Rinv_0_lt_compat;apply lt_0_INR;lia.
      apply Rinv_le_contravar; first by lra.
      do 2! rewrite S_INR.
      suff: (0 <= INR k)%R by lra.
      by apply pos_INR.
    have helper := (tmpn_series_helper1 helper_cond).
    have Rpwr : (exp (ln 2 * / INR (k.+2))) = (Rpower 2 (/ INR (k.+2))) by rewrite /Rpower Rmult_comm.
    rewrite Rpwr in helper.
    have Rpwr_pos' : (0 < (Rpower 2 (/ INR (k.+2))))%R.
    - apply Rgt_lt.
      apply bertrand.Rpower_pos; first by lra.
      apply Rlt_le.
      apply Rinv_0_lt_compat.
      by apply lt_0_INR; lia.
    have rt : 2 = (Rpower (Rpower 2 (/ INR (k.+2))) (INR (k.+2))).
    - rewrite Rpower_mult.
      rewrite Rinv_l; last by apply not_0_INR.
      by rewrite Rpower_1; lra.
    rewrite rt.
    rewrite Rpower_pow; last by apply Rpwr_pos'.
    apply pow_incr.
    split; by [apply Rlt_le; apply Rpwr_pos' | apply helper].
  Qed.


  Lemma tpmn_series_helper3 : forall k m : nat, (0 < k)%coq_nat -> ((/ (1 + (/ (INR k)))) ^ ((k*m).+1) <= (/ 2 ^ m))%R.
  Proof.
    move => k m k_prop.
    have h : ((/ (1 + / INR k)) <= 1)%R.
    - rewrite <- Rinv_1 at 2.
      apply Rinv_le_contravar; first by lra.
      suff : (0 < (/ INR k))%R by lra. 
      by apply Rinv_0_lt_compat; apply lt_0_INR.
    have h' : (0 < (1 + / (INR k)))%R.
    - suff: (0 < / (INR k))%R by lra.
      apply Rinv_0_lt_compat.
      by apply lt_0_INR.
    have helper' : ((/ (1 + (/ (INR k)))) ^ k <= (/ 2))%R.
    - rewrite <- Rinv_pow; last by apply nesym; apply Rlt_not_eq. 
      have helper := (tmpn_series_helper2 k.-1).
      rewrite <- S_pred_pos in helper; last by [].
      by apply Rle_Rinv; by [lra | apply pow_lt].
    have lt1 :   ((/ (1 + / INR k)) ^ (k * m).+1 <= (/ (1 + / INR k)) ^ (k * m))%R.
    - have t:= tech_pow_Rmult.
      symmetry in t.
      have m1 := (Rmult_1_l ((/ (1 + / INR k)) ^ (k * m))%R).
      symmetry in m1.
      rewrite m1 t.
      apply Rmult_le_compat_r; last by apply h.
      apply pow_le.
      apply Rlt_le.
      apply Rinv_0_lt_compat.
      suff : (0 < / INR k)%R by lra.
      by apply Rinv_0_lt_compat; apply lt_0_INR. 
    apply /Rle_trans.
    apply lt1.
    rewrite pow_mult.
    rewrite Rinv_pow; last by lra.
    apply pow_incr.
    split; by [apply pow_le, Rlt_le, Rinv_0_lt_compat| ].
  Qed.

  Definition coeff_num A k n := (k * (n+(Nat.log2 (A*(k.+1))).+1))%coq_nat.
  Lemma tpmn_series a A k n: (series_bound a A k) ->  ((Series.Series (fun m => (Rabs (a ((coeff_num A k n).+1+m)%coq_nat)))) <= (/ 2 ^ n))%R.
  Proof.
    move => H.
     have [H1 [HA H2]] := H.
    apply /Rle_trans.
    apply series_tail_approx; by apply H.
    have helper := (tpmn_series_helper3 (n + (Nat.log2 (A * (k.+1))).+1)%nat H1).
    have le_0 : (0 <= INR A * (INR k.+1))%R by apply Rmult_le_pos; by apply pos_INR.
    have compat := (Rmult_le_compat_l _  _  _ le_0 helper).
    apply /Rle_trans.
    apply compat.
    rewrite pow_add.
    rewrite Rinv_mult_distr; try by apply pow_nonzero; lra.
    rewrite <- Rmult_assoc.
    apply (Rmult_le_reg_r ( 2 ^ (Nat.log2 (A * (k.+1))).+1)); first by apply pow_lt;lra.
    rewrite Rmult_assoc.
    rewrite Rinv_l; last by apply pow_nonzero; lra.
    rewrite Rmult_1_r.
    rewrite Rmult_comm.
    apply Rmult_le_compat_l.
    - by apply Rlt_le, Rinv_0_lt_compat, pow_lt;lra.
    have Akgt0 : (0 < A*(k.+1))%coq_nat by apply Nat.mul_pos_pos; by [ | apply Nat.lt_0_succ].
    have [_ sp] := (Nat.log2_spec _ Akgt0).
    apply lt_INR in sp.
    rewrite <- mult_INR.
    apply Rlt_le.
    rewrite pow_INR in sp.
    by apply sp.
  Qed. 

  Lemma tpmn_PSeries a A k n : forall x, (Rabs x <= 1) % R -> (series_bound a A k) -> ((Rabs ((PSeries a x) - (sum_n (fun k => ((a k)*(x ^ k)))%R (coeff_num A k n)))) <= (/ 2 ^ n))%R.
  Proof.
    move => x xle1 H.
    rewrite /PSeries.
    set p0 := (fun k => ((a k)*(x ^ k)))%R.
    rewrite (Series_incr_n p0 (coeff_num A k n).+1); try by [apply ex_series_Rabs; apply (bseries_exists_Rabs2 xle1 H) | apply Nat.lt_0_succ].
    rewrite <- pred_Sn. 
    rewrite <- sum_n_Reals.
    rewrite Rplus_comm.
    have rpm_assoc u v w: ((u+v)-w = (u+(v-w)))%R by lra.
    rewrite rpm_assoc Rminus_eq_0 Rplus_0_r //=.
    apply /Rle_trans.
    apply Series.Series_Rabs.
    - have e := (bseries_exists_Rabs2 xle1 H).
      have [ex _] := (ex_series_incr_n (fun n : nat => Rabs (a n * x ^ n)) (coeff_num A k n).+1).
      by apply ex.
    simpl.
    have lt :  ((Series (fun n0 : nat => Rabs (p0 (coeff_num A k n + n0)%coq_nat.+1))) <= (Series (fun n0 : nat => Rabs (a (coeff_num A k n + n0)%coq_nat.+1))))%R.
     - apply Series_le; last by apply (ex_series_incr_n (fun n0 => (abs (a n0))) (coeff_num A k n).+1); apply (bseries_exists_Rabs H).
       move => m.
       split;first by apply Rabs_pos.
       rewrite /p0.
       rewrite Rabs_mult.
       rewrite <- Rmult_1_r.
       apply Rmult_le_compat_l; first by apply Rabs_pos.
       rewrite <- RPow_abs.
       by apply pow_le_1_compat_abs.
    apply /Rle_trans.
    apply lt.
    by apply tpmn_series.
  Qed.

  Fixpoint finite_sum_rlzr_rec (phia : names_RQw) (phix : names_RQ) (N M : nat) : names_RQ :=
    match M with  
    | 0%nat => (fun q => (phia (N,q)))
    | S M'=> (fun q => (Rplus_rlzrf
                      (RQ_pair
                         (fun q' => (phia ((N-M)%nat,q')))
                         (fun q' => (Rmult_rlzrf (RQ_pair
                                                 (finite_sum_rlzr_rec phia phix N M')
                                                 phix)
                                                  q'))
                      ) q))
    end.              
  Definition finite_sum_rlzrf (phi : ps_names) phix N := (finite_sum_rlzr_rec (rprj phi) phix N N).
  Lemma finite_sum_rlzr_rec_spec1 : forall a phia phix N, (phia \describes a \wrt powerseries1_cs) ->(finite_sum_rlzr_rec (rprj phia) phix N 0) \describes (projT1 a N) \wrt RQ. 
  Proof.
    move => a phia phix N [H1 H2].
    rewrite /finite_sum_rlzr_rec => eps eps_prop.
    by apply H1.
  Qed.
  Lemma finite_sum_rlzr_rec_spec2 : forall a phia x phix M N S, (phia \describes a \wrt powerseries1_cs) -> (phix \describes x \wrt RQ) -> (finite_sum_rlzr_rec (rprj phia) phix N M) \describes S \wrt RQ -> (finite_sum_rlzr_rec (rprj phia) phix N M.+1) \describes ((projT1 a (N-M.+1)%nat)+S*x)%R \wrt RQ.
  Proof.
    move => a phia x phix M N S [Ha _] Hx H.
    rewrite /finite_sum_rlzr_rec => eps eps_prop.
    pose prod := (fun q' => Rmult_rlzrf (name_pair (finite_sum_rlzr_rec (rprj phia) phix N M)
                                                 phix) q').
    have inner : prod \describes (S*x)%R \wrt RQ.
    - have := Rmult_rlzr_spec.
      rewrite F2MF_rlzr_F2MF => mspec.
      specialize (mspec (name_pair (finite_sum_rlzr_rec (rprj phia) phix N M) phix) (S,x)).
      simpl in mspec.
      rewrite /lprj/rprj in mspec.
      simpl in mspec.
      specialize (mspec (conj H Hx)).
      rewrite /prod.
      simpl.
      by apply mspec.
    have := Rplus_rlzr_spec.
    rewrite F2MF_rlzr_F2MF => pspec.
    specialize (pspec (name_pair (fun q' : queries RQ => rprj phia ((N - M.+1)%nat, q')) prod) ((projT1 a (N - M.+1)%nat),(S * x)%R)).
    simpl in pspec.
    rewrite /lprj/rprj in pspec.
    simpl in pspec.
    have Ha' := (Ha (N-M.+1)%nat).
    specialize (pspec (conj Ha' inner)).
    by apply pspec.
  Qed.

  Lemma  finite_sum_rlzr_rec_spec3 : forall a phia x phix N M, (M <= N)%coq_nat -> (phia \describes a \wrt powerseries1_cs) -> (phix \describes x \wrt RQ) -> (finite_sum_rlzr_rec (rprj phia) phix N M) \describes (sum_n (fun k => (((projT1 a) (k+(N-M))%coq_nat)*(x ^ k))%R) M) \wrt RQ.
  Proof.
    move => a phia x phix N.
    elim => [ltp phiana phixnx | M IH ltp phiana phixnx].
    - rewrite sum_O.
      rewrite pow_O Rmult_1_r.
      rewrite <- minus_n_O, plus_O_n.
      by apply finite_sum_rlzr_rec_spec1.
    have hs0 : forall b, sum_n b M.+1 = ((b 0%nat)+(sum_n_m b 1 M.+1))%R.
    - move => b.
      rewrite sum_n_m_sum_n;last by apply Nat.le_0_l.
      rewrite sum_O /minus/plus/opp /=.
      by lra.  
    have hs :  (sum_n (fun k : nat => ((projT1 a (k + (N - M.+1))%coq_nat) * x ^ k)%R) M.+1) = ((projT1 a (N-M.+1)%coq_nat)+((sum_n (fun k => (projT1 a (k+(N-M))%coq_nat)*x^k) % R) M)*x)%R.
      - rewrite hs0.
        rewrite pow_O Rmult_1_r plus_O_n.
        apply Rplus_eq_compat_l.
        have S := (sum_n_m_S (fun k : nat => ((projT1 a (k + (N - M.+1))%coq_nat) * x ^ k)%R) 0 M).
        rewrite <- S.
        have t : forall n, ((n.+1 + (N-M.+1))%coq_nat = (n + (N-M)))%coq_nat.
        * move => n.
          rewrite /subn/subn_rec Nat.sub_succ_r //=.
          rewrite Nat.add_pred_r; last by apply Nat.sub_gt.
          rewrite <- S_pred_pos; last by apply Nat.add_pos_r; apply lt_minus_O_lt.
          by lia.
        have help1 : (sum_n_m (fun k : nat => ((projT1 a (k.+1 + (N - M.+1))%coq_nat) * x ^ k.+1)%R) 0 M) =   (sum_n_m (fun k : nat => (((projT1 a (k + (N - M))%coq_nat) * x ^ k)*x)%R) 0 M).
        * apply sum_n_m_ext => n.
          rewrite t.
          rewrite <- tech_pow_Rmult.
          by lra.
        rewrite help1.
        rewrite sum_n_m_mult_r.
        by apply Rmult_eq_compat_r.
    rewrite hs.
    apply finite_sum_rlzr_rec_spec2; try by [].
    apply IH; by [lia | ].
  Qed.

  Lemma finite_sum_rlzr_spec : forall a phia x phix N, (phia \describes a \wrt powerseries1_cs) -> (phix \describes x \wrt RQ) -> (finite_sum_rlzrf phia phix N) \describes (sum_n (fun k => (projT1 a k)*(x ^ k))%R N) \wrt RQ.
  Proof.
    move => a phia x phix N phiana phixnx.
    rewrite /finite_sum_rlzrf.
    have spec := (finite_sum_rlzr_rec_spec3 (le_n N) phiana phixnx).
    have t0 : (sum_n (fun k : nat => (projT1 a (k + (N - N))%coq_nat * x ^ k)%R) N) = (sum_n (fun k : nat => (projT1 a k * x ^ k)%R) N) by apply sum_n_ext => n;  rewrite /subn/subn_rec Nat.sub_diag Nat.add_0_r.
    by rewrite <- t0.
  Qed.

  Definition RQ1 := (cs_sub (make_subset (fun x : RQ => ((Rabs x) <= 1)%R))).

  Definition get_coeff_num (phi : ps_names) eps := (coeff_num (lprj (lprj phi) tt) ((rprj (lprj phi) tt)) (Pos_size (Qden (eps)))).

  Lemma get_coeff_num_cont : (get_coeff_num \is_continuous_function) %baire.
  Proof.
    move => phi.
    rewrite /get_coeff_num.
    exists ((fun q => [:: (inl (inr tt)); (inl (inl tt)) ])).
    move => q psi [H1 [H2 _]].
    by rewrite /lprj/rprj H1 H2.
  Qed.

  Definition sum_rlzrf' (phia : ps_names) phix eps := (finite_sum_rlzrf phia phix (get_coeff_num phia (eps / (1+1))) (eps / (1+1))).

  Lemma sum_rlzrf_spec : forall a phia x phix, (Rabs x <= 1)%R-> (phia \describes a \wrt powerseries1_cs) -> (phix \describes x \wrt RQ) -> (sum_rlzrf' phia phix) \describes (PSeries (projT1 a) x) \wrt RQ.
  Proof.
    move => a phia x phix xB [phiana1 sb] phixnx.
    simpl => eps epsgt0.
    set N := (coeff_num ((lprj (lprj  phia)) tt) ((rprj (lprj phia)) tt) (Pos_size (Qden (eps / (1+1))))).
    set A := ((lprj (lprj  phia)) tt).
    set k := ((rprj (lprj  phia)) tt).
    rewrite /sum_rlzrf' //=.
    have tr : forall x y z, ((Rabs (x-y)) <= ((eps/(1+1))%Q))%R -> (((Rabs (y-z))) <= ((eps/(1+1))%Q))%R -> ((Rabs (x-z)) <= eps)%R.
    - move => x0 y0 z0 H1 H2.
      have arith : ((x0 - z0) = ((x0 - y0) + (y0 - z0)))%R by lra.
      rewrite arith.
      apply /Rle_trans.
      apply Rabs_triang.
      have d : (~ 1 + 1 == 0) by [].
      rewrite Q2R_div in H1; last by [].
      rewrite Q2R_plus in H1.
      rewrite Q2R_div in H2; last by [].
      rewrite Q2R_plus in H2.
      by lra.
    apply (tr _ (sum_n (fun k => (projT1 a k)*(x ^ k))%R N) _).
    - have t := (tpmn_PSeries (Pos_size (Qden (eps / (1+1)%Q))) xB sb).
      apply /Rle_trans.
      apply t.
      apply size_Qden.
      rewrite Q2R_div; last by [].
      rewrite Q2R_plus.
      by lra.
    apply finite_sum_rlzr_spec; try by [].
    rewrite Q2R_div; last by [].
    rewrite Q2R_plus.
    by lra.
  Qed.

  Definition sum_rlzrf (phi : psx_names) eps := (sum_rlzrf' (lprj phi) (rprj phi) eps).
  Definition sum_rlzr: (questions (powerseries1_cs \*_cs RQ1) ->> questions RQ) := F2MF sum_rlzrf.

  Definition pssum :=  (fun ax : (powerseries1_cs \*_cs RQ1) => (PSeries (projT1 ax.1) (projT1 ax.2))).
  Lemma sum_rlzr_spec : sum_rlzr \realizes (F2MF pssum : (powerseries1_cs \*_cs RQ1) ->> RQ).
  Proof.
    rewrite F2MF_rlzr_F2MF => phi ax phinax eps eg0.
    apply sum_rlzrf_spec; by [apply (projT2 ax.2) | apply phinax | ].
  Qed.

  Definition fun_pair (X Y Z : cs) (f : (questions X -> questions Y)) (g: questions X -> questions Z) phi : (questions (Y \*_cs Z)) := (name_pair (f phi) (g phi)).

  Lemma fun_pair_cont (X Y Z : cs) (f : (questions X -> questions Y)) (g : (questions X -> questions Z)) : (f \is_continuous_function)%baire -> (g \is_continuous_function)%baire -> ((fun_pair f g) \is_continuous_function)%baire.
  Proof.
    move => fc gc phi.
    apply choice in fc.
    case fc => fcf fcfp.
    apply choice in gc.
    case gc => gcf gcfp.
    exists (fun q =>
         match q with
         | inl q' => (fcf phi q')
         | inr q' => (gcf phi q')
      end).
    move => q psi.
    case q => q' coin; by apply injective_projections; [try apply fcfp| try apply gcfp].
  Qed.

  Lemma finite_sum_cont : forall N M, ((fun (phi  : (questions ( RQ\^w \*_cs  RQ))) eps => (finite_sum_rlzr_rec (lprj phi) (rprj phi) N M) eps) \is_continuous_function)%baire.
  Proof.
    move => N M.
    elim : M => [|m IH].
    -  set F_c := ((fun (phi' : (questions ( RQ\^w ))) (eps' : Q) => (phi' (N,eps'))) \o_f lprj) : ((questions ( RQ\^w \*_cs  RQ)) -> Q -> (answers RQ)).
      suff : (F_c \is_continuous_function)%baire by []. 
      rewrite <- cont_F2MF.
      rewrite /F_c.
      rewrite <- F2MF_comp_F2MF.
      apply cont.cont_comp; first by rewrite cont_F2MF;apply lprj_cont.
      rewrite cont_F2MF.
      move => phi.
      by exists (fun q => [:: (N,q)]) => q' psi [H1 _].
    simpl.
   set F_cl' := (fun phi : (questions (RQ\^w)) => (fun q' : Q => phi ((N - m.+1)%nat, q')):(questions RQ)).
   pose F_cl :=  (F_cl' \o_f lprj):((questions (RQ\^w \*_cs RQ) -> questions RQ)).
    set F_cr1 :=(fun phi:  (questions (RQ\^w \*_cs RQ)) => (finite_sum_rlzr_rec (lprj phi) (rprj phi) N m)).
    set F_cr := Rmult_rlzrf \o_f (fun_pair F_cr1 rprj).
    set F_ci := (fun_pair F_cl F_cr).
    set F_c := Rplus_rlzrf \o_f
                          F_ci.
    suff: (F_c  \is_continuous_function)%baire by [].
    rewrite <- cont_F2MF.
    rewrite /F_c.
    rewrite <- F2MF_comp_F2MF.
    apply cont.cont_comp; last by apply Rplus_rlzr_cntop.
    rewrite cont_F2MF.
    apply fun_pair_cont; last first.
    - rewrite /F_cr.
      rewrite <- cont_F2MF.
      rewrite <- F2MF_comp_F2MF.
      apply cont.cont_comp; last by apply Rmult_rlzr_cntop.
      rewrite cont_F2MF.
      apply fun_pair_cont; by [apply IH | apply rprj_cont].
    rewrite /F_cl.
    rewrite <- cont_F2MF.
    rewrite <- F2MF_comp_F2MF.
    apply cont.cont_comp; first by rewrite cont_F2MF; apply lprj_cont.
    rewrite cont_F2MF.
    move => phi.
    exists (fun q => [:: ((N-m.+1)%nat, q)]).
    by move => q psi [coin _].
  Qed.

  Definition finite_sum_rlzr_p (phi : (questions (RQ\^w \*_cs RQ \*_cs cs_nat))) := (finite_sum_rlzr_rec (lprj (lprj phi)) (rprj (lprj phi)) ((rprj phi) tt)) ((rprj phi) tt).

  Lemma finite_sum_cont' : (finite_sum_rlzr_p \is_continuous_function)%baire.
  Proof.
    move => phi.
    have fsc := (finite_sum_cont (rprj phi tt) (rprj phi tt) (lprj phi)). 
    case fsc.
    move => fscf fscfp.
    exists (fun q => (inr tt) :: map inl (fscf q)).
    move => q psi [H1 H2].
    have p0 : (rprj psi tt) = (rprj phi tt) by rewrite /rprj H1.
    rewrite /finite_sum_rlzr_p.
    rewrite p0.
    apply fscfp.
    have coin_prop : forall L, (phi \and psi \coincide_on (map inl L))%baire -> ((lprj phi) \and (lprj psi) \coincide_on L)%baire.
    - elim => [| x L IH]; first by [].
      move => [C1 C2].
      split; by [rewrite /lprj C1 | apply (IH C2)].
    apply coin_prop.
    by apply H2.
  Qed.

  Definition emb1 (eps : Q) (phi : (questions (powerseries1_cs \*_cs RQ1)))  : (questions (RQ\^w \*_cs RQ \*_cs cs_nat)) :=  (fun q : (queries (RQ\^w \*_cs RQ \*_cs cs_nat)) =>
                                                                 match q with
                                                                 | (inl (inl q')) => ((rprj (lprj phi ) q'), (somea RQ), (somea cs_nat))
                                                                 | (inl (inr q')) => ((somea (RQ\^w)), rprj phi q', (somea cs_nat))
                                                                 | (inr tt) => ((somea (RQ\^w)), (somea RQ), get_coeff_num (lprj phi) eps)
                                                                 end).
  Lemma emb1_cont eps : ((emb1 eps) \is_continuous_function)%baire.
  Proof.
    move => phi.
    exists (fun q => match q with
               | (inl (inl q')) => [:: (inl (inr q'))]
               | (inl (inr q')) => [:: (inr q')]
               | (inr tt) => [:: (inl (inl (inl tt))); (inl (inl (inr tt)))]
      end).
    move => q psi.
    case  q => q'.
    - case q' => q'' [H1 _]; try by rewrite //=/rprj/lprj H1.
    case q'.
    move => [H1 [H2 _]] //=.
    rewrite /get_coeff_num.
    by rewrite /rprj/lprj H1 H2.
  Qed.

  Lemma sum_rlzr_cntop: sum_rlzr \is_continuous_operator.
  Proof.
    rewrite cont_F2MF /sum_rlzrf/sum_rlzrf'/finite_sum_rlzrf.
    set F' := (fun (phi : (questions (powerseries1_cs \*_cs RQ1))) eps => ((finite_sum_rlzr_p \o_f (emb1 (eps / (1+1)))) phi (eps / (1+1)))).
    have compc eps : ((finite_sum_rlzr_p \o_f (emb1 eps)) \is_continuous_function)%baire.
    - rewrite <- cont_F2MF.
      rewrite <- F2MF_comp_F2MF.
      apply cont.cont_comp; apply cont_F2MF; by [apply emb1_cont | apply finite_sum_cont'].
      suff : (F' \is_continuous_function)%baire by [].
   rewrite /continuous_f in compc.
   move => phi.
   simpl.
   rewrite /F'.
   have compc' eps := (compc eps phi).
   apply choice in compc'.
   case compc'.
   move => L Lp.
   exists (fun eps => (L (eps / (1+1)) (eps / (1+1)))).
   move => eps psi.
   by apply Lp.
  Qed.  
End ps_summation.

Section addition.
  Lemma addition_bound a b : forall A1 k1 A2 k2, (series_bound a A1 k1) -> (series_bound b A2 k2) -> (series_bound (fun n => (a n + b n)%R) (A1+A2) (max k1 k2)). 
  Proof.
    move => A1 k1 A2 k2 [k1_pos [A1_pos B1]] [k2_pos [A2_pos B2]].
    split; [apply Nat.max_lt_iff; auto | split => [ | n]; first by apply Nat.add_pos_r]. 
    apply /Rle_trans.
    apply Rabs_triang.
    have le : ((Rabs (a n) + (Rabs (b n))) <= (INR A1)*(/ (1 + (/ (INR k1))))^n+(INR A2)*(/ (1 + (/ (INR k2))))^n)%R by apply Rplus_le_compat.
    apply /Rle_trans.
    apply le.
    have p0 : forall s t, (0 < s)%coq_nat ->  (0 <= (/ (1 + (/ (INR s)))) <= (/ (1 + / INR (max s t))))%R.
    - move => s t sgt0.
      split; first by apply invge0.
      apply Rinv_le_contravar;first by apply invp1gt0;apply Nat.max_lt_iff;auto.
      apply Rplus_le_compat_l.
      apply Rinv_le_contravar; first by apply lt_0_INR.
      apply le_INR.
      by apply Nat.le_max_l.
    have l1 := (pow_incr (/ (1 + (/ INR k1))) (/ (1 + ( / INR (max k1 k2)))) n (p0 k1 k2 k1_pos)).
    have l2 := (pow_incr (/ (1 + (/ INR k2))) (/ (1 + ( / INR (max k2 k1)))) n (p0 k2 k1 k2_pos)).
    rewrite Nat.max_comm in l2.
    have l1' := (Rmult_le_compat_l (INR A1) ((/ (1 + (/ INR k1)))^n) ((/ (1 + ( / INR (max k1 k2))))^n) (pos_INR A1) l1).
    have l2' := (Rmult_le_compat_l (INR A2) ((/ (1 + (/ INR k2)))^n) ((/ (1 + ( / INR (max k1 k2))))^n) (pos_INR A2) l2).

    have c := (Rplus_le_compat ((INR A1)*((/ (1 + (/ INR k1)))^n)) ((INR A1) * (/ (1 + ( / (INR ((max k1 k2))))))^n) ((INR A2)*(/ (1 + / (INR k2)))^n) (INR A2 * (/ (1 + ( / INR (max k1 k2))))^n) l1' l2').
    apply /Rle_trans.
    apply c.
    rewrite <- Rmult_plus_distr_r.
    rewrite <- plus_INR.
    by rewrite /addn/addn_rec;lra.
  Qed.
  Definition addition_rlzrf (phi1 phi2:ps_names) (q: (unit + unit + nat*Q) ) := match q with
                                           | (inr q') => (0%nat, 0%nat,(Rplus_rlzrf (RQ_pair (fun eps => (rprj phi1 (q'.1,eps))) (fun eps => (rprj phi2 (q'.1,eps)))) q'.2))
                                           | (inl (inl q')) => (((lprj (lprj phi1) q')+(lprj (lprj phi2) q'))%nat, 0%nat, 0%Q)
                                           | (inl (inr q')) => (0%nat,(max (rprj (lprj phi1) q') (rprj (lprj phi2) q')), 0%Q)
                                           end.
  Lemma series1_add a b : (series1 a)->(series1 b)->(series1 (PS_plus a b)).
  Proof.
    move => ap bp.
    have Rbargt : (Rbar_lt 1%Z (Rbar_min (CV_radius a) (CV_radius b))) by apply Rbar_min_case.
    apply /Rbar_lt_le_trans.
    apply Rbargt.
    by apply CV_radius_plus.
  Qed.

  Definition ps1_addition (a b : powerseries1) : powerseries1 := exist series1 (PS_plus  (projT1 a) (projT1 b)) (series1_add (projT2 a) (projT2 b)).

  Definition psadd :=  (fun ab : (powerseries1_cs \*_cs powerseries1_cs) => (ps1_addition ab.1 ab.2)).

  Lemma addition_rlzrf_spec : forall phi1 phi2 (a b : powerseries1), (phi1 \describes a \wrt powerseries1_cs) -> (phi2 \describes b \wrt powerseries1_cs) -> (addition_rlzrf phi1 phi2) \describes (ps1_addition a b)  \wrt powerseries1_cs.
  Proof.
    move => phi1 phi2 a b [//= phi1na1 phi1na2] [//= phi2nb1 phi2nb2].
    split => [n eps epsgt0 | ] //=; last by apply addition_bound.
    rewrite /addition_rlzrf/rprj //=.
    have := Rplus_rlzr_spec.
    rewrite F2MF_rlzr_F2MF => //= pspec.
    have ps := (pspec (RQ_pair (fun eps' => (phi1 (inr (n, eps'))).2) (fun eps' => (phi2 (inr (n,eps'))).2)) ((sval a n), (sval b n))).
    apply ps; last by apply epsgt0.
    by split; [apply phi1na1 |  apply phi2nb1].
Qed.

  Definition addition_rlzrf' (phiab : (questions (powerseries1_cs \*_cs powerseries1_cs)))  := (addition_rlzrf (lprj phiab) (rprj phiab)).

  Definition addition_rlzr: (questions (powerseries1_cs \*_cs powerseries1_cs) ->> (questions (powerseries1_cs))) := F2MF addition_rlzrf'.

  Lemma addition_rlzr_spec : addition_rlzr \realizes (F2MF psadd).
  Proof.
    rewrite F2MF_rlzr_F2MF => ab [phia phib] [phiana phibnb].
    rewrite /addition_rlzrf'.
    by apply addition_rlzrf_spec.
  Qed. 

End addition.
Section multiplication.
  Lemma multiplication_bound_helper1 : forall n r, (0 < r < 1)%R -> (((INR n)*(r ^ n) <= (INR n.+1)*(r ^ (n.+1))))%R <-> ((INR n) <= (r / (1-r)))%R.
  Proof.
    move => n r rlt1.
    have t : ((r ^ (n.+1)) = r*(r^n))%R by simpl; lra.
    split => H.
    - apply Rle_div_r; first by lra.
      rewrite Rmult_minus_distr_l Rmult_1_r.
      suff : (INR n <= ((INR n)+1)*r)%R by lra.
      rewrite <- S_INR.   
      apply (Rmult_le_reg_r (r ^ n)); first by apply pow_lt;lra.
      rewrite Rmult_assoc.
      by rewrite <- t.
    rewrite t; rewrite <- Rmult_assoc.
    apply Rmult_le_compat_r; first by apply pow_le;lra.
    rewrite S_INR.
    suff: ((INR n)*(1-r) <= r)%R by lra.
    apply Rle_div_r; by lra.
  Qed.
  
  Lemma multiplication_bound_helper2 : forall n j r, (0 < r < 1)%R -> (n <= j)%coq_nat ->  ((INR j) <= (r / (1-r)))%R -> ((INR n)*(r ^ n) <= (INR j)*(r ^ j))%R.
  Proof.
    move => n j r rb njb jb.
    have nb : ((INR n) <= (r / (1-r)))%R by apply (Rle_trans _ _ _ (le_INR _ _ njb)).    
    move : jb njb.
    elim j => [jb njb|j' IH jb njb]; first by rewrite Rmult_0_l; rewrite <- (le_n_0_eq n njb);simpl;lra.
    have jb' : (INR (j') <= (r / (1-r)))%R by apply (Rle_trans _ (INR j'.+1)); by [rewrite S_INR;lra|].
    case (Nat.le_gt_cases n j') => njb'.
    - apply /Rle_trans.
      apply IH; try by [].
      apply multiplication_bound_helper1; try by [].
      have t : (n = (j'.+1)) by lia.               
      rewrite t.
      by lra.
  Qed.

  Lemma multiplication_bound_helper3 : forall n j r, (0 < r < 1)%R -> (j <= n)%coq_nat -> ((r / (1-r)) < (INR j))%R ->  ((INR n)*(r ^ n) <= (INR j)*(r ^ j))%R.
  Proof.
    move => n j r rb njb nj.
    move : njb.
    rewrite Nat.le_lteq.
    case => njb; last by rewrite njb;lra.
    move : njb.
    elim n => [njb' |n' IH njb' ]; first by rewrite Rmult_1_r;apply Rmult_le_pos; [apply pos_INR | apply pow_le;lra ].
    have njb'' : (j <= n')%coq_nat by lia.   
    have nb'' : ((r / (1-r)) < (INR n'))%R.
    - apply /Rlt_le_trans.
      apply nj.
      by apply le_INR.
    have h : ((INR n'.+1)*(r^(n'.+1)) <= ((INR n')*r^n'))%R.
     -apply Rlt_le.
      apply Rnot_le_lt.
      apply (not_iff_compat (multiplication_bound_helper1 n' rb)).
      by apply Rlt_not_le.
    apply /Rle_trans.
    apply h.
    move : njb''.
    rewrite Nat.le_lteq.
    case => njb''; last by rewrite njb''; lra.
    by apply IH.
  Qed.

  Lemma multiplication_bound_helper4 : forall n j, ((INR n) * ((/ (1 + (/ (INR j.+1)))) ^ n) <= (INR j.+2)* ((/ (1 + (/ (INR j.+1)))) ^ j.+2))%R.
  Proof.
    move => n j.
    set r := (/ (1 + (/ (INR j.+1))))%R.
    have rlt : (0 < r < 1)%R.
    - rewrite /r.
      split.
      + apply Rinv_0_lt_compat.
        suff: (0 < (/ (INR j.+1)))%R by lra.
        apply Rinv_0_lt_compat.
        by apply lt_0_INR;lia.
      rewrite <- Rinv_1 at 2.
      suff : (0 < (/ (INR j.+1)))%R.
      + move => H.
        by apply Rinv_lt_contravar; lra.
      apply Rinv_0_lt_compat.
      by apply lt_0_INR;lia.
    have h : ((r / (1-r)) = (INR (j.+1)))%R.
    - apply (Rmult_eq_reg_r (1-r)); last by lra.
      field_simplify; last by lra.
      do 2! rewrite Rdiv_1.
      rewrite /r.     
      field.
      split; [apply not_0_INR; lia |].
      suff: (0 <= (INR j.+1))%R by lra.
      by apply pos_INR.
    case (Nat.le_gt_cases n j.+1) => e.
    - symmetry in h.
      have [_ B]:= (multiplication_bound_helper1 j.+1 rlt ).
      specialize (B (Req_le _ _ h)).
      have Rl := (Rle_trans _ _ _ _ B).
      apply Rl.
      apply multiplication_bound_helper2; [apply rlt|apply e | rewrite h;lra].
    apply multiplication_bound_helper3; [apply rlt | lia  |].
    apply /Rle_lt_trans.
    apply (Req_le _ _ h).
    by apply lt_INR; lia.
  Qed.

  Lemma multiplication_bound_helper : forall n j, ((INR n) * ((/ (1 + (/ (INR j.+1)))) ^ n) <= (/ 2)*(INR j.+2)) %R.
  Proof.
    move => n j.
    apply /Rle_trans.
    apply multiplication_bound_helper4.
    have t : (0 < j.+1)%coq_nat by lia.
    have h := (tpmn_series_helper3 1 t).
    rewrite pow_1 in h.
    ring_simplify.
    apply Rmult_le_compat_l; first by apply pos_INR; lia.
    have jf : ((((j.+1)*1)%coq_nat.+1) = (j.+2))%coq_nat by lia.
    by rewrite jf in h.
  Qed.
  Lemma series_bound_larger_k a : forall A k k', (k <= k')%coq_nat -> (series_bound a A k) -> (series_bound a A k').
  Proof.
    move => A k k' klek' [kgt0 [Agt0 b1]].
    split; try split => [ | n];try lia.
    apply /Rle_trans.
    apply b1.
    apply Rmult_le_compat_l; first by apply pos_INR;lia.
    apply pow_incr.
    have k'gt0 : (0 < k')%coq_nat by lia.
    have lt j : (0 < j)%coq_nat -> (0 < 1+(/ INR j))%R.
    - move => jlt.
      suff : (0 < (/ INR j))%R by lra.
      apply Rinv_0_lt_compat.
      by apply lt_0_INR.
    split; first by apply Rlt_le; apply Rinv_0_lt_compat; apply (lt k).
    apply Rinv_le_contravar; first by apply (lt k').
    apply Rplus_le_compat_l.
    apply Rinv_le_contravar; first by apply lt_0_INR.
    by apply le_INR.
  Qed.
  Lemma multiplication_bound a b : forall A1 k1 A2 k2, (series_bound a A1 k1) -> (series_bound b A2 k2) -> (series_bound (PS_mult a b) (A1*A2*((max k1 k2).+2)) (2*(max k1 k2))).  
  Proof.
  move => A1 k1 A2 k2 sb1 sb2.
  set k := (max k1 k2).
  have k1k : (k1 <= k)%coq_nat by lia.
  have k2k : (k2 <= k)%coq_nat by lia.
  have [kgt0 [A1gt0 b1]] := (series_bound_larger_k k1k sb1).
  have [_ [A2gt0 b2]] := (series_bound_larger_k k2k sb2).
  split; try split => [ | n]; try apply Nat.mul_pos_pos;try apply Nat.mul_pos_pos;try lia.
  rewrite /PS_mult.
  apply /Rle_trans.
  apply sum_f_R0_triangle.
  set cn := (fun (m : nat) => ((INR (A1*A2)%coq_nat) * ((/ (1 + (/ INR k)))^n))%R).
  apply /Rle_trans.
  apply (sum_Rle _ cn).
  - move => m mltn.
    rewrite Rabs_mult.
    apply /Rle_trans.
    apply (Rmult_le_compat _ _ _ _ (Rabs_pos _) (Rabs_pos _) (b1 m) (b2 (n-m)%coq_nat)  ).
    have ar : ((((INR A1) * (/ (1 + (/ (INR k))))^m)*((INR A2)*(/ (1 + (/ (INR k))))^(n-m)%coq_nat)) = ((INR A1)*(INR A2)*((/ (1 + (/ (INR k))))^m*(/ (1 + (/ (INR k))))^(n-m)%coq_nat)))%R by lra.
    rewrite ar.
    rewrite <- mult_INR.
    rewrite <- pow_add.
    rewrite le_plus_minus_r;last by [].
    by rewrite /cn;lra.
   rewrite sum_cte.
   have eq1 : ((/ (1 + (/ (INR k)))) = ((/ (1+(/ (INR ((2*k)%coq_nat)))))*(/ (1 + (/ (INR (2*k)%coq_nat.+1))))))%R.
   rewrite !S_INR.
   rewrite !mult_INR.
   simpl.
   field.
   split; try split; (suff: (0 < (INR k))%R by lra);by apply lt_0_INR.
   rewrite eq1.
   rewrite !mult_INR.
   rewrite Rpow_mult_distr.
   rewrite !Rmult_assoc.
   do 2! (apply Rmult_le_compat_l; first by apply Rlt_le;apply lt_0_INR).
   rewrite (Rmult_comm (INR k.+2) _).
   apply Rmult_le_compat_l; last first.
   rewrite Rmult_comm.
   have ineq : ((INR n.+1) * (/ (1 + (/ INR (2 * k)%coq_nat.+1))) ^ n <= ((INR n) * (/ (1 + (/ INR (2 * k)%coq_nat.+1))) ^ n)+1)%R.
   - rewrite S_INR.
     rewrite Rmult_plus_distr_r.
     apply Rplus_le_compat_l.
     rewrite Rmult_1_l.
     apply pow_le_1_compat.
     split; [apply Rlt_le; apply Rinv_0_lt_compat | rewrite <- Rinv_1; apply Rinv_le_contravar ]; try lra; try (suff: (0 < / (INR (2*k)%coq_nat.+1)) % R by lra); apply Rinv_0_lt_compat; apply lt_0_INR; lia.
   apply /Rle_trans.
   apply ineq.
   rewrite (S_INR k.+1).
   apply Rplus_le_compat_r.
   apply /Rle_trans.
   apply multiplication_bound_helper.
   rewrite !S_INR.
   rewrite mult_INR //=.
   lra.
   apply pow_le.
   rewrite <- mult_INR.
   by apply invge0; lia.
  Qed.

  Definition get_pwr (phi : ps_names) := (rprj phi).
  Definition get_coeff_name (phi : ps_names) n := (fun eps => (get_pwr phi (n,eps))).
  Definition get_A (phi : ps_names) := (lprj (lprj  phi) tt).
  Definition get_k (phi : ps_names) := (rprj (lprj  phi) tt).

  Fixpoint convolution_rlzrf_rec (phi1 phi2 : ps_names) (n i : nat) := match i with
                                                                 | 0%nat => (Rmult_rlzrf (RQ_pair (get_coeff_name phi1 0) (get_coeff_name phi2 n)))
                                                                 | (S i') => (Rplus_rlzrf (RQ_pair  (convolution_rlzrf_rec phi1 phi2 n i') (Rmult_rlzrf (RQ_pair (get_coeff_name phi1 i) (get_coeff_name phi2 (n-i)%coq_nat)))))
                                                                 end.
  Lemma convolution_rlzrf_rec_spec (phi1 phi2 : ps_names) n m :  forall a b, (phi1 \describes a \wrt powerseries1_cs) -> (phi2 \describes b \wrt powerseries1_cs) -> (convolution_rlzrf_rec phi1 phi2 n m) \describes (sum_f_R0 (fun k : nat => ((sval a k) * (sval b (n - k)%coq_nat))%R) m) \wrt RQ. 
  Proof.
    move => a b [phia _] [phib _].
    elim : m => [eps epsgt0| m' IH].
    - have := Rmult_rlzr_spec.
      rewrite F2MF_rlzr_F2MF => mspec.
      rewrite /convolution_rlzrf_rec//=.
      specialize (mspec (RQ_pair (get_coeff_name phi1 0) (get_coeff_name phi2 n)) ((sval a 0%nat),(sval b n))).
      rewrite !Nat.sub_0_r.
      apply mspec; last by [].
      by split; [apply phia | apply phib ].
    rewrite sum_N_predN;last by lia.
    have t : forall n', (n'.+1.-1)%coq_nat = n' by auto.
    rewrite t.
    rewrite /convolution_rlzrf_rec.
    have := Rplus_rlzr_spec.
    rewrite F2MF_rlzr_F2MF => pspec.
    move => eps epsgt0 //=.
    have pspec' := (pspec _ ((sum_f_R0 (fun k : nat => ((sval a k) * (sval b (n - k)%coq_nat))%R) m'), ((sval a (m'.+1)%nat)*(sval b (n-m'.+1)%nat))%R)).
    apply pspec'; last by [].
    split; rewrite /lprj/rprj //=.
    move => eps' eps'gt0.
    have := Rmult_rlzr_spec.
    rewrite F2MF_rlzr_F2MF => mspec.
    apply (mspec _ ((sval a m'.+1), (sval b (n-m'.+1)%nat)));last by [].
    split; [apply phia | apply phib ].
  Qed.

  Definition convolution_rlzrf (phi1 phi2 : ps_names) n := (convolution_rlzrf_rec phi1 phi2 n n).
  Lemma convolution_rlzrf_spec (phi1 phi2 : ps_names) n : forall a b, (phi1 \describes a \wrt powerseries1_cs) -> (phi2 \describes b \wrt powerseries1_cs) -> (convolution_rlzrf phi1 phi2 n) \describes (PS_mult (projT1 a) (projT1 b) n) \wrt RQ.
  Proof.
    by apply convolution_rlzrf_rec_spec.
  Qed.

  Definition multiplication_rlzrf (phi1 phi2:ps_names) (q: (unit + unit + nat*Q) ) := match q with
                                           | (inr q') => (0%nat, 0%nat,(convolution_rlzrf phi1 phi2 q'.1 q'.2))
                                           | (inl (inl q')) => (((get_A phi1)*(get_A phi2)*(max (get_k phi1) (get_k phi2)).+2)%nat, 0%nat, 0%Q)
                                           | (inl (inr q')) => (0%nat,(2*(max (get_k phi1) (get_k phi2)))%nat, 0%Q)
                                           end.

  Lemma bseries_series1 a : (exists A k, (series_bound a A k)) -> (series1 a). 
  Proof.
    case => A; case => k [gt0k [gt0A H]].
    rewrite /series1.
    rewrite /CV_radius /Lub_Rbar; case ex_lub_Rbar => x [p1 p2].
    have h : forall n, (0 < n)%coq_nat -> (0 < (1 + / (INR (n))))%R.
    - move => n Hn.
      suff : (0 < (/ (INR n)))%R by lra.
      by apply Rinv_0_lt_compat; apply lt_0_INR.
    have n2gt0 n  : (0 < n)%coq_nat -> (0 < 2 * n)%coq_nat.
      move => Hn.
      by apply /ltP; rewrite muln_gt0;apply /ltP.
    have h' : forall n, (0 <= (1 + / (INR (2*k)))^n)%R.
    - move => n.
      by apply pow_le; apply Rlt_le;apply h; apply n2gt0.
    have s : (CV_disk a (1+(/ (INR (2*k))))).
      - rewrite /CV_disk.
        set b := (fun n => ((INR A)*(((/ (1 + (/ (INR k)))) ^ n)*(1+(/ (INR (2 * k))))^n))%R).
        have e := (ex_series_le _ b).
        apply e.
        + move => n.
          rewrite /norm //= /abs //=.
          rewrite Rabs_Rabsolu.
          rewrite Rabs_mult.
          rewrite (Rabs_right ((1 + (/ (INR (2*k)))) ^ n));last by apply Rle_ge;apply h'.
          rewrite /b;rewrite <- Rmult_assoc; apply Rmult_le_compat_r; by [apply h' | ].
        + have scal := ex_series_scal_l.
          apply scal.
          apply (ex_series_ext (fun n => ((1 + (/ (INR (2 * k)))) / (1 + (/ INR k)))^n)%R).
          move => n.
          rewrite <- Rpow_mult_distr.
          suff : (((1 + (/ (INR (2 * k)))) / (1 + (/ INR k))) = (((/ (1 + (/ (INR k)))))*(1+(/ (INR (2 * k))))))%R by move => H';rewrite H';lra.
          field;split; try split; apply Rgt_not_eq; apply Rlt_gt; try apply lt_0_INR; try apply n2gt0; try lia.
          suff : (0 < (INR k))%R by lra.
          by apply lt_0_INR.
      apply ex_series_geom.
      rewrite Rabs_right.
      + rewrite <- Rdiv_lt_1; last by apply h.
      suff : ((/ (INR (2 * k))) < (/ INR k))%R by lra.
      apply Rinv_lt_contravar; [rewrite <- mult_INR; apply lt_0_INR | try apply lt_INR;try lia].
      + apply /ltP.
        rewrite muln_gt0.
        apply /andP.
        split; by apply /ltP;try apply n2gt0.
      +  by apply /ltP;apply ltn_Pmull; [| apply /ltP].
      apply Rle_ge.
      apply Rdiv_le_0_compat; by try apply Rlt_le; apply h; try apply n2gt0.
    have lt1 : (Rbar_lt 1%Z (1 + (/ INR (2*k)))%R).
    - suff : (0 < (/ (INR (2*k))))%R by simpl; lra.
      by apply Rinv_0_lt_compat; apply lt_0_INR; apply n2gt0.
    apply /Rbar_lt_le_trans.
    apply lt1.
    by apply (p1 _ s).
  Qed.

  Lemma series1_mult a b : (series1 a)->(series1 b)->(series1 (PS_mult a b)).
  Proof.
     move => H1 H2.
     apply bseries_series1.
     Search _ series1.
     case (Ak_exists H1) => A1; case => k1 sb1.
     case (Ak_exists H2) => A2; case => k2 sb2.
     exists (A1*A2*((max k1 k2).+2))%coq_nat; exists (2*(max k1 k2))%coq_nat.
     by apply multiplication_bound.
  Qed.

  Definition ps1_mult (a b : powerseries1) : powerseries1 := exist series1 (PS_mult (projT1 a) (projT1 b)) (series1_mult (projT2 a) (projT2 b)).

  Definition psmult :=  (fun ab : (powerseries1_cs \*_cs powerseries1_cs) => (ps1_mult ab.1 ab.2)).

  Lemma multiplication_rlzrf_spec : forall phi1 phi2 (a b : powerseries1), (phi1 \describes a \wrt powerseries1_cs) -> (phi2 \describes b \wrt powerseries1_cs) -> (multiplication_rlzrf phi1 phi2) \describes (ps1_mult a b)  \wrt powerseries1_cs.
  Proof.
    move => phi1 phi2 a b [//= phi1na1 phi1na2] [//= phi2nb1 phi2nb2].
    split => [n eps epsgt0 | ] //=; by [apply multiplication_bound | apply convolution_rlzrf_spec].
Qed.
   
  Definition multiplication_rlzrf' (phiab : (questions (powerseries1_cs \*_cs powerseries1_cs)))  := (multiplication_rlzrf (lprj phiab) (rprj phiab)).

  Definition multiplication_rlzr: (questions (powerseries1_cs \*_cs powerseries1_cs) ->> (questions (powerseries1_cs))) := F2MF multiplication_rlzrf'.

  Lemma multiplication_rlzr_spec : multiplication_rlzr \realizes (F2MF psmult).
  Proof.
    rewrite F2MF_rlzr_F2MF => ab [phia phib] [phiana phibnb].
    rewrite /multiplication_rlzrf'.
    by apply multiplication_rlzrf_spec.
  Qed. 
End multiplication.

Section examples.
  Notation "x '+rq' y" :=
  (Rplus_rlzrf (name_pair x y)) (at level 35, format "x '+rq' y").    
  Notation "x '*rq' y" :=
  
  Definition Q2RQ (q:Q) := (fun (eps :Q) => q). 

  Definition N2Q n := (Z.of_nat n # 1).
  Fixpoint inv_fact_acc (n:nat) (eps:Q) acc := (if (Qle_bool acc eps) then
                                             0%Q else (match n with
                                           | 0%nat => acc
                                           | n.+1 => (inv_fact_acc n eps (acc / (N2Q n.+1)))
                                           end)).
  Lemma inv_fact_acc_spec1 : forall n (eps acc : Q), (acc <= eps)%R -> (inv_fact_acc n eps acc)=0%Q.
  Proof.
    move => n eps acc H.
    rewrite /inv_fact_acc.
    apply Rle_Qle in H.
    apply (Qle_bool_iff acc eps) in H.
    elim n => [| n' IH]; by apply ifT.
  Qed.

  Lemma  Rlt_not_Qle (a b:Q) : (a < b)%R -> (not (Qle_bool b a)).
    move => H.
    apply Rlt_Qlt in H.
    have q := (Qle_bool_iff b a).
    apply Qlt_not_le in H.
    by rewrite <- q in H.
  Qed.

  Lemma inv_fact_acc_spec2 : forall n (eps acc : Q), (eps < acc)%R  -> (inv_fact_acc n.+1 eps acc) =  (inv_fact_acc n eps (acc / (N2Q (n.+1)))).
  Proof.
    move => n.
    move => eps acc H.
    rewrite /inv_fact_acc.
    rewrite ifN; last by apply /negP; apply Rlt_not_Qle.
    done.
  Qed.
  Lemma fact_helper x n : ((x / N2Q n.+1)%Q / INR (fact n))%R = (x / (INR (fact n.+1)))%R.
  Proof.
    rewrite Q2R_div; last by [].
    apply Interval_missing.Rdiv_eq_reg; try by apply INR_fact_neq_0.
    have t : (Q2R (N2Q n.+1) = (INR (n.+1)))%R.
    - rewrite /N2Q.
      rewrite INR_IZR_INZ.
      rewrite /Q2R.
      simpl.
      by lra.
    rewrite t.
    rewrite /Rdiv.
    rewrite (Rmult_comm _ x).
    rewrite Rmult_assoc.
    apply Rmult_eq_compat_l.
    rewrite <- simpl_fact.
    rewrite Rmult_comm.
    field.
    by split; apply INR_fact_neq_0.
  Qed.

  Lemma inv_fact_acc_spec3 : forall n (eps acc : Q), ((acc / (INR (fact n))) <= eps) % R -> ((inv_fact_acc n eps acc) = 0).
  Proof.
    elim => [eps acc H| n IH eps acc H]; first by apply inv_fact_acc_spec1;rewrite Rdiv_1 in H.
    case e: (Qle_bool acc eps); first by apply ifT.
    simpl.
    rewrite ifF; last by [].
    apply IH.
    suff : ((acc / N2Q n.+1)%Q / INR (fact n))%R = (acc / (INR (fact n.+1)))%R by move => H'; rewrite H'.
    by apply fact_helper.
  Qed.

  Lemma inv_fact_acc_spec4 : forall n (eps acc : Q), (0 < acc)%R -> ((acc / (INR (fact n))) > eps) % R -> (Q2R (inv_fact_acc n eps acc) = (acc / (INR (fact  n)))%R).
  Proof.
    elim => [eps acc accgt0 H | n IH eps acc accgt0 H].
    - rewrite /inv_fact_acc ifF; first by simpl;lra.
      suff : (eps < acc)%R by move=>H';apply /negP; apply (Rlt_not_Qle H').
      apply Rgt_lt.
      simpl in H.
      by lra.
      have H' : (eps < acc)%R.
      - apply Rgt_lt in H.
        apply /Rlt_le_trans.
        apply H.
        apply Rle_div_l; first by apply INR_fact_lt_0.
        rewrite <- (Rmult_1_r acc) at 1.
        apply Rmult_le_compat_l; first by apply Rlt_le.
        have inr1 : (1 = (INR 1))%R by auto.
        rewrite inr1.
        apply le_INR.
        by apply lt_O_fact.
      rewrite inv_fact_acc_spec2; last by apply H'.
      rewrite IH; first by apply fact_helper.
      - rewrite Q2R_div; last by [].
       apply Rdiv_lt_0_compat; first by apply accgt0.
       have t : (Q2R (N2Q n.+1) = (INR (n.+1)))%R.
       + rewrite /N2Q.
         rewrite INR_IZR_INZ.
         rewrite /Q2R.
         simpl.
         by lra.
       rewrite t.
       by apply lt_0_INR; lia.
     by rewrite fact_helper.
  Qed. 

  Definition inv_fact n eps := (inv_fact_acc n eps 1).

  Lemma inv_fact_spec : forall n (eps:Q), (0 < eps)%R -> ((Rabs ((/ (INR (fact n))) - (inv_fact n eps))) <= eps)%R. 
  Proof.
    move => n eps epsgt0.
    rewrite /inv_fact.
    case (Rlt_or_le eps (/ (INR (fact n)))) => H.
    - rewrite inv_fact_acc_spec4; try lra.
      have s : (1%Q / (INR (fact n)))%R = (/ (INR (fact n)))%R by lra.
      rewrite s.
      rewrite Rminus_eq_0 Rabs_R0.
      by apply Rlt_le.
    rewrite inv_fact_acc_spec3; last by lra.
    rewrite RMicromega.IQR_0 Rminus_0_r.
    rewrite Rabs_right; first by apply H.
    apply Rle_ge; apply Rlt_le.
    apply Rinv_0_lt_compat.
    by apply INR_fact_lt_0.
  Qed.

  Lemma inv_fact_is_name : (fun nq => (inv_fact nq.1 nq.2)) \describes (fun n => (/ (INR (fact n)))%R) \wrt (RQ\^w).
  Proof.
    move => n eps.
    by apply inv_fact_spec.
  Qed.
End examples.
  Require Extraction.
  Require ExtrHaskellZInteger.
  Require ExtrHaskellNatInt.
  Extraction Language Haskell.
  Definition exp_ps (nq: (nat*Q)) := (inv_fact nq.1 nq.2).
  Definition N2cs (n : nat) : (questions cs_nat) := (fun (q : unit) => n). 
  Definition make_ps_name (phia : (questions (RQ\^w))) A k := (name_pair (name_pair (N2cs A) (N2cs k)) phia).
  Definition exp_name := (make_ps_name exp_ps 2 1).

  Definition ps_e := (fun n => (/ (INR (fact n)))%R).
  Lemma ps_es1 : series1 ps_e.
  Proof.
    rewrite /series1.
    have s := (is_exp_Reals 2).
    have s' : (CV_disk ps_e 2).
    - rewrite /CV_disk.
      rewrite /is_pseries in s.
      rewrite /ex_series.
      exists (exp 2).
      rewrite /scal in s.
      simpl in s.
      rewrite /mult in s.
      simpl in s.
      have fe : (fun n => ((pow_n 2 n)* (/ (INR (fact n))))%R) = (fun n => (Rabs ((ps_e n) * 2^n))).
      - apply functional_extensionality.
        move => x.
        rewrite pow_n_pow.
        rewrite Rabs_right; rewrite /ps_e; first by lra.
        apply Rle_ge.
        apply Rmult_le_pos; first by apply Rlt_le; apply Rinv_0_lt_compat;apply INR_fact_lt_0.
        apply pow_le;lra.
      by rewrite <- fe.
    rewrite /CV_radius.
    apply (Rbar_lt_le_trans _ 2); first by simpl;lra.
    have t : not (is_ub_Rbar (CV_disk ps_e) 1).
    rewrite /is_ub_Rbar.
    move => H.
    move : (H 2 s').
    by simpl; lra.
    have [c _] := (Lub_Rbar_correct (CV_disk ps_e)).
    by apply c.
  Qed.
  Definition ps_e1 := exist series1 ps_e ps_es1.
  Lemma exp_name_spec : exp_name \describes ps_e1 \wrt powerseries1_cs. 
  Proof.
    split.
    - move => i eps epsgt0 //=.
      rewrite /ps_e /exp_name /make_ps_name /name_pair /rprj /exp_ps //=.
      by apply inv_fact_spec.
    simpl.
    rewrite /series_bound /exp_name /make_ps_name /rprj /lprj /N2cs //=.
    split; [lia | split; first by lia] => n.
    rewrite Rinv_1.
    rewrite /ps_e.
    rewrite <- Rinv_pow; last by lra.
    rewrite Rabs_Rinv;last by apply INR_fact_neq_0.
    rewrite Rabs_right; last by apply Rle_ge; apply Rlt_le; apply INR_fact_lt_0.
    have t : (1+1)%R = 2 by lra.
    rewrite t.
    rewrite Rmult_comm.
    apply Rle_div_l; first by lra.
    rewrite /Rdiv.
    rewrite <- Rinv_mult_distr; [| apply INR_fact_neq_0| lra].
    apply Rle_Rinv; [apply pow_lt;lra|apply Rmult_lt_0_compat;[apply INR_fact_lt_0|lra] |].
    elim n => [| n' IH]; first by simpl;lra.
    rewrite mult_INR //=.
    rewrite Rmult_comm;apply Rmult_le_compat_r; first by lra.
    move : IH; case n' => [| n'' IH]; first by simpl;lra.
    apply /Rle_trans.
    apply IH.
    rewrite Rmult_comm.
    apply Rmult_le_compat_r; last first.
    - rewrite S_INR.
      suff : (0 <= INR n'')%R by lra.
      by apply pos_INR.
    by apply pos_INR.
  Qed.

  Definition comp_exp (phi :names_RQ) :(names_RQ) := (sum_rlzrf' exp_name phi).
  
  Definition exp1 (x : RQ1) : RQ := (exp (projT1 x)).
  Lemma comp_exp_spec : (F2MF comp_exp: (questions RQ1)->>(questions RQ)) \realizes (F2MF exp1).
  Proof.
     apply F2MF_rlzr_F2MF.
     move => phi x phinx.
     rewrite /comp_exp.
     rewrite /exp1.
     rewrite (exp_Reals (projT1 x)).
     by apply (sum_rlzrf_spec (projT2 x) exp_name_spec ).
  Qed.
  Definition ce n := (comp_exp (Q2RQ (1#1)) (1#n)).
  Extraction "inv_fact" ce.
    
  Definition sin_ps (nq: (nat*Q)) := match (nq.1 mod 4) with
                                   | 0%nat => 0
                                   | 1%nat => (inv_fact nq.1 nq.2)
                                   | 2%nat => 0
                                   | _ => -(inv_fact nq.1 nq.2)
                                   end.
  Definition sin_name := (make_ps_name sin_ps 1 1).
  Definition comp_sin (phi : (questions RQ)) := (sum_rlzrf' sin_name phi).
  Definition sin_plus_e := (addition_rlzrf sin_name exp_name).
  Definition comp_spe (phi : (questions RQ)) := (sum_rlzrf' sin_plus_e phi).
  Definition PSeries2 a x y := (PSeries (fun n => (PSeries (fun m => (a (n,m))) y)) x). 
  
