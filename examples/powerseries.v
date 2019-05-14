From mathcomp Require Import ssreflect seq ssrnat ssrbool eqtype ssrfun.
From mf Require Import all_mf.
Require Import Q_reals.
Require Import all_cont FMop.
Require Import iseg.
Require Import Coquelicot.PSeries.
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

Fixpoint finite_sum_rlzr_rec (phia : (questions (RQ\^w))) (phix : (questions RQ)) (N M : nat) : (questions RQ) :=
  match M with  
  | 0%nat => (fun q => (phia (N,q)))
  | S M'=> (fun q => (Rplus_rlzrf
                    (name_pair
                       (fun q' => (phia ((N-M)%nat,q')))
                       (fun q' => (Rmult_rlzrf (name_pair
                                               (finite_sum_rlzr_rec phia phix N M')
                                               phix)
                                                q'))
                    ) q))
  end.              
Definition finite_sum_rlzrf (phi : (questions powerseries1_cs)) phix N := (finite_sum_rlzr_rec (rprj phi) phix N N).

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

Definition get_coeff_num (phi : (questions powerseries1_cs)) eps := (coeff_num (lprj (lprj phi) tt) ((rprj (lprj phi) tt)) (Pos_size (Qden (eps)))).

Lemma get_coeff_num_cont : (get_coeff_num \is_continuous_function) %baire.
Proof.
  move => phi.
  rewrite /get_coeff_num.
  exists ((fun q => [:: (inl (inr tt)); (inl (inl tt)) ])).
  move => q psi [H1 [H2 _]].
  by rewrite /lprj/rprj H1 H2.
Qed.

Definition sum_rlzrf' (phia : (questions powerseries1_cs)) phix eps := (finite_sum_rlzrf phia phix (get_coeff_num phia (eps / (1+1))) (eps / (1+1))).
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

Definition sum_rlzrf (phi : (questions (powerseries1_cs \*_cs RQ1))) eps := (sum_rlzrf' (lprj phi) (rprj phi) eps).
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
