From mathcomp Require Import all_ssreflect all_algebra.
From mf Require Import all_mf.
From metric Require Import pointwise reals standard Qmetric coquelicot.
Require Import Qreals Reals Psatz ClassicalChoice FunctionalExtensionality.
Require Import axioms all_cs cs_mtrc Q_reals Rstruct.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Interval_tactic.
Import QArith GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope R_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section powerseries_basic_facts.
  Definition single_element_seq (m : nat) x n := if n == m then x else 0%R.

  Notation "'e_' i"  := (single_element_seq i 1) (at level 30).

  Lemma single_element_seq_zeros m x k: k != m -> single_element_seq m x k = 0.
  Proof. exact/ifN_eq. Qed.

  Lemma single_element_seq_bound m x n: 0 <= x -> 0 <= single_element_seq m x n <= x.
  Proof. by rewrite /single_element_seq; case: ifP; lra. Qed.

  Lemma sum_big_ord (a: nat -> R) n: sum_n a n = \sum_(i < n.+1) a i.
  Proof.
    rewrite sum_n_Reals.
    by elim: n => [ | n ih]; [rewrite big_ord1; compute; lra |  rewrite big_ord_recr -ih].
  Qed.
  
  Lemma selt_sum0 m x n : (n <= m)%nat -> \sum_(i < n) (single_element_seq m x) i = 0.
  Proof.
    case: n => [ | n]; first rewrite big_ord0 //; rewrite -sum_big_ord.
    elim: n => [ineq | n ih ineq]; first by rewrite sum_O; apply/ifN_eqC/lt0n_neq0.
    rewrite sum_Sn ih; last exact/leq_trans/ineq.
    rewrite single_element_seq_zeros/plus/=; try lra.
    by apply/negP => /eqP eq; move: ineq; rewrite eq ltnn.
  Qed.

  Lemma selt_sum_val m x: \sum_(i < m.+1) single_element_seq m x i = x.
  Proof.
    rewrite -sum_big_ord; case m => [| n]; first by rewrite sum_O.
    by rewrite sum_Sn sum_big_ord selt_sum0 // plus_zero_l; apply/ifT.
  Qed.

  Lemma sum_sub (a: nat -> R) n m:
    (n <= m)%nat -> \sum_(n <= i < m) a i = \sum_(i < m) a i - \sum_(i < n) a i.
  Proof.
    move => /subnK <-; elim: (m - n)%nat => [ | k].
    - by rewrite add0n /index_iota subnn big_nil Rminus_eq_0.
    rewrite addSn big_ord_recr big_nat_recr/=/GRing.add/=/GRing.opp; last exact/leq_addl; lra.
  Qed.

  Lemma big_nat_ord (R: Type) (idx: R) (op: Monoid.law idx) (n: nat) (F: nat -> R):
    \big[op/idx]_(0 <= i < n) F i = \big[op/idx]_(i < n) F i.
  Proof.
    elim: n => [ | n ih]; first by rewrite big_nil big_ord0.
    by rewrite big_ord_recr big_nat_recr // ih.
  Qed.
  
  Lemma sum_big_nat (a: nat -> R) n m: sum_n_m a n m = \sum_(n <= i < m.+1) a i.
  Proof.
    case ineq: (n <= m)%nat; last first.
    - rewrite sum_n_m_zero; last by apply/leP; rewrite ltnNge ineq.
      by rewrite big_geq; last by rewrite ltnNge ineq.
    case: n ineq => [ | n ineq]; first by rewrite big_nat_ord -sum_big_ord.
    rewrite sum_n_m_sum_n; last by apply/leP/leq_trans/ineq.
    by rewrite !sum_big_ord sum_sub //; apply/leq_trans; first exact/ineq.
  Qed.
  
  Lemma selt_sum0_gt m x n n':
    (m < n)%nat -> \sum_(n <= i < n') single_element_seq m x i = 0.
  Proof.
    case ineq: (n < n')%nat; last by rewrite big_geq // leqNgt ineq.    
    case: n' ineq => // n' H' H; rewrite -sum_big_nat.
    rewrite (sum_n_m_ext_loc _ (cnst 0))=>[ | k [? ?]]; first exact/sum_n_m_const_zero.
    by apply/single_element_seq_zeros/negP => /eqP eq; move: H; rewrite -eq =>/leP; lia.
  Qed.
  
  Lemma selt_sum m x n: (m <= n)%nat -> \sum_(i < n.+1) single_element_seq m x i = x.
  Proof.
    move => /leP ineq; rewrite -sum_big_ord /sum_n (sum_n_m_Chasles _ 0 m); try lia.
    rewrite !sum_big_nat [X in plus _ X]selt_sum0_gt // plus_zero_r.
    by rewrite big_nat_ord; apply/selt_sum_val.
  Qed.

  Lemma single_element_sum_lt m x n: 0 <= x ->  0 <= \sum_(i < n) single_element_seq m x i <= x.
  Proof.
    move => pos; case ineq: (n <= m)%nat; first by rewrite selt_sum0 //; lra.
    by case: n ineq => // n ineq; rewrite selt_sum; try lra; rewrite leqNgt ineq.
  Qed.

  Local Notation convergent a := (ex_series a).

  Lemma is_series_lim (a: nat -> R) r:
    is_series a r <-> r \from metric_limit (fun n => \sum_(i < n) a i).
  Proof.
    split => val.
    - apply/Uncv_lim/is_lim_seq_Reals/(is_lim_seq_incr_n _ 1%nat) => eps eg0.
      by have [N Nprp]:= val eps eg0; exists N => n ineq; rewrite Nat.add_1_r -sum_big_ord; apply/Nprp.
    apply/is_lim_seq_Reals/Uncv_lim => eps eg0.
    have [[ | N] Nprp]:= val eps eg0; last by exists N => m ineq; rewrite sum_big_ord; apply/Nprp.
    by exists 1%nat; case => // m ineq; rewrite sum_big_ord; apply/Nprp.
  Qed.

  Lemma cnv_spec (a: nat -> R): convergent a <-> (fun n => \sum_(i < n) a i) \from dom metric_limit.
  Proof. by split => [[r val] | [r val]]; exists r; apply/is_series_lim. Qed.

  Lemma Series_spec (a: nat -> R):
    convergent a -> Series a \from metric_limit (fun n => \sum_(i < n) a i).
  Proof. by move => cnv; apply/is_series_lim/Series_correct. Qed.
  
  Lemma selt_Series m x: Series (single_element_seq m x) = x.
  Proof.
    rewrite /Series (Lim_seq_ext_loc _ (cnst x)); first by rewrite Lim_seq_const.
    by exists m => n /leP ?; rewrite sum_big_ord selt_sum.
  Qed.

  Lemma positive_sum_grows a m: convergent a -> (forall n, 0 <= a n) -> a m <= Series a.
  Proof.
    move => H0 H; rewrite -(selt_Series m (a m)); apply/Series_le =>// n.
    by rewrite/single_element_seq; case: ifP => [/eqP -> | _]; split; try exact/H; lra.
  Qed.

  Notation "a \is_series_with_radius r" := (Rbar_lt r (CV_radius a)) (at level 30).

  Lemma exists_M a r: 0 < r -> a \is_series_with_radius r -> exists M, forall n, Rabs(a n) <= M/(r ^ n).
  Proof.
    move => rg0 rc; exists (Series (fun n => \|a n * r^n|)) => n.
    rewrite -[X in X <= _]Rmult_1_r -(Rinv_r (r^n)); last by have:= pow_lt r n; lra.
    rewrite -Rmult_assoc; apply/Rmult_le_compat_r; first exact/Rlt_le/Rinv_0_lt_compat/pow_lt/rg0.
    rewrite -(Rabs_pos_eq (r ^ n)) //; last by apply/pow_le; lra.
    rewrite -Rabs_mult; apply/positive_sum_grows => [ | m]; last exact/Rabs_pos.
    by apply/CV_disk_inside; case: (CV_radius) rc; rewrite /Rbar_lt; try split_Rabs; lra.
  Qed.

  Lemma nat_upper r: exists U, r < INR U.
  Proof.
    exists (Z.to_nat (up r)); have := archimed r.
    rewrite /Z.to_nat; case: up => [/= | p | p]; try rewrite INR_IPR /IZR; try lra.
    by rewrite/=/IZR -INR_IPR; have := INR_pos p; lra.
  Qed.
  
  Definition is_series_bound a A k := forall n, \|a n| <= IPR A/(1 + /(INR k + 1))^n.

  Notation "a \is_bounded_by A \and k" := (is_series_bound a A k) (at level 30).

  Lemma exists_Ak a: a \is_series_with_radius 1 -> exists A k, a \is_bounded_by A \and k.
  Proof.
    move => H.
    have [k [/leP kg0 ineq]]: exists k, (0 < k )%nat /\ Rbar_lt (1+/INR k)%R (CV_radius a).
    - have [eps prp]:= open_Rbar_lt' 1 (CV_radius a) H.
      have [k [k_prop1 kg0]] := archimed_cor1 eps (cond_pos eps).
      exists k; split; first exact/leP; apply/prp.
      suff: 0 <= /INR k by rewrite/ball/=/AbsRing_ball/abs/minus/plus/opp/=; split_Rabs; lra.
      exact/Rlt_le/Rinv_0_lt_compat/lt_0_INR.
    have ikg0: 0 < /INR k by apply/Rinv_0_lt_compat/lt_0_INR.
    have [|| M M_prp]//:= exists_M (r := 1 + /INR k) (a:= a); try lra.
    case (nat_upper M) => A A_prop.
    exists (Pos.of_nat A.+1); exists k.-1 => n.
    apply/Rle_trans; first exact/M_prp.
    rewrite -!INR_IPR !Nat2Pos.id // -S_INR -(S_pred _ 0); try lia.    
    apply/Rmult_le_compat_r; last by rewrite S_INR; lra.
    by apply/Rlt_le/Rinv_0_lt_compat/pow_lt; lra.
  Qed.
  
  Definition powerseries1 := {a | a \is_series_with_radius 1}.
End powerseries_basic_facts.
Notation "a \is_series_with_radius r" := (Rbar_lt r (CV_radius a)) (at level 30).
Notation "a \is_bounded_by A \and k" := (is_series_bound a A k) (at level 30).

Section ps_representation.
  Definition cs_pos:= discrete_space pos_count.
  Definition names_PS:= B_(cs_pos \*_cs cs_nat \*_cs RQ\^w).
  Definition rep_PS: names_PS ->> powerseries1 :=
    make_mf (fun (phi: names_PS) an =>
               let a := sval an in
               let A := lprj (lprj phi) tt in
               let k := rprj (lprj phi) tt in
               rprj phi \is_name_of a
               /\
               a \is_bounded_by A \and k
            ).
  
  Lemma rep_PS_sur: rep_PS \is_cototal.
  Proof.
    move  => [a rad].
    have [A [k bnd]]:= exists_Ak rad.
    have [phi phina]:= get_name (a: RQ\^w).
    exists (pair (pair (cnst A: B_(cs_pos), cnst k: B_(cs_nat)), phi)).
    by split; try exact/phina; apply/bnd.
  Qed.

  Lemma rep_PS_sing: rep_PS \is_singlevalued.
  Proof. by move => ? ? ? [phina _] [phina' _]; apply/eq_sub/(rep_sing (X:=RQ\^w))/phina'. Qed.

  Definition powerseries1_representation:=
    Build_representation_of (Build_represented_over rep_PS_sur rep_PS_sing).

  Definition PS := Build_continuity_space powerseries1_representation.
End ps_representation.

Notation convergent a := (ex_series a).

Definition absolutely_convergent (K: AbsRing) (V: NormedModule K) (a: nat -> V):=
  convergent (fun n => norm (a n)).

Lemma acnv_cnv (a: nat -> R): absolutely_convergent a -> convergent a.
Proof. exact/ex_series_Rabs. Qed.

Section ps_summation.
  Definition powers a x n := a n * x ^ n.

  Lemma PSeries_Series a x: PSeries a x = Series (powers a x).
  Proof. done. Qed.
  
  Lemma pos_gt0 p: 0 < IPR p.
  Proof.
    by suff: IPR 1 <= IPR p; first rewrite {1}/IPR; try lra; rewrite -!INR_IPR; apply/le_INR; lia.
  Qed.

  Lemma Ipinv_ineq x: 0 <= x -> 0 < /(x + 1) <= 1.
  Proof.
    by intros; split; [apply/Rinv_0_lt_compat | rewrite -{2}Rinv_1; apply/Rinv_le_contravar]; lra.
  Qed.

  Lemma invp1_ineq k: 0 < /(1 + /(INR k + 1)) < 1.
  Proof.
    have: 0 < /(INR k + 1) by apply/Rinv_0_lt_compat; have := pos_INR k; lra.
    have ineq := Ipinv_ineq (pos_INR k); split; first by apply Rinv_0_lt_compat; lra.
    by rewrite -{3}Rinv_1; apply/Rinv_lt_contravar; lra.
  Qed.


  Lemma invp1_Rabs k: \|/(1 + /(INR k + 1))| < 1.
  Proof. by have := invp1_ineq k; split_Rabs; lra. Qed.

  Lemma cnv_scale (a: nat -> R) (r: R): r <> 0 ->
    convergent a <-> convergent (scale r a).
  Proof.
    split => [ | cnv]; first exact/ex_series_scal.
    apply/(ex_series_ext (fun n => (scale (/r) (scale r a) n)))/ex_series_scal/cnv => n.
    by rewrite/scale -Rmult_assoc Rinv_l; lra.
  Qed.

  Lemma pow_le_1_compat x n: 0 <= x <= 1 -> 0 <= x ^ n <= 1.
  Proof. intros; rewrite -(pow1 n); split; [apply/pow_le | apply/pow_incr]; try lra. Qed.

  Lemma pow_0_lt_lt_1_compat x n: 0 < x < 1 -> 0 < x ^ n.+1 < 1.
  Proof.
    by move => ?; split; try apply/pow_lt; try apply pow_lt_1_compat; try lra; apply/leP.
  Qed.
    
  Lemma pow_le_1_compat_abs x n: \|x| <= 1 -> \|x| ^ n <= 1.
  Proof. by intros; split_Rabs; apply pow_le_1_compat; lra. Qed.

  Lemma sbnd_acnv a A k: a \is_bounded_by A \and k -> absolutely_convergent a.
  Proof.
    rewrite/absolutely_convergent => bnd.
    have /cnv_scale->: /IPR A <> 0 by have: 0 < /IPR A; first exact/Rinv_0_lt_compat/pos_gt0; lra.
    apply/ex_series_le/ex_series_geom/invp1_Rabs/k => n.
    rewrite/=-Rinv_pow; last by have:=Ipinv_ineq (pos_INR k); try lra.
    rewrite/Rdiv/norm/=/abs/=/scale/= Rabs_mult [X in _ * X]Rabs_pos_eq; try exact/Rabs_pos.
    apply/Rle_trans; first exact/Rmult_le_compat_l/bnd/Rabs_pos.
    rewrite Rabs_pos_eq; try exact/Rlt_le/Rinv_0_lt_compat/pos_gt0.
    apply/Req_le; field; split; try by have := pos_gt0 A; lra.
    by apply/pow_nonzero; have := Ipinv_ineq (pos_INR k); lra.
  Qed.

  Lemma sbnd_psrs a A k x:
    \|x| <= 1 -> a \is_bounded_by A \and k -> absolutely_convergent (powers a x).
  Proof.
    move => /pow_le_1_compat_abs xl1 bnd.
    apply/sbnd_acnv => n; rewrite Rabs_mult -RPow_abs; apply/Rle_trans/bnd.
    by apply/Rle_trans; first exact/Rmult_le_compat_l/xl1/Rabs_pos; lra.
  Qed.

  Local Notation shift n a := (fun k => a (n + k)%nat).

  Lemma cnv_shft n (a: nat -> R): convergent a -> convergent (shift n a).
  Proof. by move => ?; rewrite -ex_series_incr_n. Qed.

  Lemma shft_cnv n (a: nat -> R): convergent (shift n a) -> convergent a.
  Proof. by move => ?; apply/(ex_series_incr_n _ n). Qed.

  Lemma sbnd_tail a A k N: a \is_bounded_by A \and k ->
    Series (shift N (ptw Rabs a)) <= IPR A * (INR k + 2)/(1 + /(INR k + 1))^N.
  Proof.
    move => bnd; have neq n : 1 + /(INR n + 1) <> 0.
    - by apply/nesym/Rlt_not_eq; have := Ipinv_ineq (pos_INR n); lra.
    apply/Rle_trans.
    - apply/Series_le; first by split; [apply/Rabs_pos | apply/bnd].
      have /ex_series_geom/(cnv_shft N)/cnv_scale prp:= invp1_Rabs k.
      apply/ex_series_ext/(prp (IPR A)) => [n | ]; try by have := pos_gt0 A; lra.
      by rewrite /scale -Rinv_pow.
    rewrite Series_scal_l /Rdiv Rmult_assoc; apply/Rmult_le_compat_l; try exact/Rlt_le/pos_gt0.
    apply/Rle_trans.
    - apply/Req_le/Series_ext => n; rewrite pow_add.
      by rewrite Rinv_mult_distr; try exact/pow_nonzero/neq.
    rewrite Series_scal_l Rmult_comm; apply/Rmult_le_compat_r.
    - apply/Rlt_le/Rinv_0_lt_compat/pow_lt; have := Ipinv_ineq (pos_INR k); lra.
    rewrite (Series_ext _ [eta pow (/(1 + /(INR k + 1)))]) => [ | n]; last apply/Rinv_pow/neq.
    by rewrite Series_geom; try exact/invp1_Rabs; apply/Req_le; field; have := pos_INR k; lra.
  Qed.
  Lemma expl1px x: 0 <= x <= / 2 -> exp (ln 2 * x) <= 1 + x.
  Proof.
    move => [H1 H2].
    pose f x := exp (ln 2 * x); pose df x := ln 2 * exp (ln 2 * x).
    have df_prop y: (is_derive f y (df y)) by rewrite/f/df; auto_derive; try lra.
    case: (MVT_gen f 0 x df) => [? ? | ? ? | t [[mn /Rmax_Rle mx]]]; first by apply df_prop.
    - by apply/derivable_continuous_pt; rewrite /f; auto_derive.
    move: mn; rewrite /Rmin; case: Rle_dec; try lra; move => _ tg0.
    rewrite/f/df Rminus_0_r Rmult_0_r exp_0 => eq.
    suff: exp (ln 2 * x) - 1 <= x by lra.
    rewrite eq -[X in _ <= X]Rmult_1_l; apply/Rmult_le_compat_r => //.    
    have ineq: ln 2 * exp (ln 2/2) <= 1 by interval.
    apply/Rle_trans/ineq/Rmult_le_compat_l/Raux.exp_le/Rmult_le_compat_l; try interval.    
    by case: mx tg0; lra.
  Qed.

  Lemma exp_prod_lbnd k: 2 <= (1 + /(INR k + 1)) ^ k.+1.
  Proof.    
    rewrite -S_INR; case: k => [ | k]; first by rewrite pow_1 /= Rinv_1; lra.
    have /expl1px: 0 <= /INR k.+2 <= / 2.
    - split; first by apply Rlt_le;apply Rinv_0_lt_compat;apply lt_0_INR;lia.
      by apply Rinv_le_contravar; last rewrite !S_INR; have := pos_INR k; lra.
    have ->: exp (ln 2 / INR k.+2) = Rpower 2 (/INR k.+2) by rewrite /Rpower Rmult_comm.
    move => helper.
    have Rpwr_pos' : 0 < Rpower 2 (/INR k.+2).
    - by apply/bertrand.Rpower_pos/Rlt_le/Rinv_0_lt_compat/lt_0_INR; try lra; lia.
    have -> : 2 = Rpower (Rpower 2 (/INR k.+2)) (INR k.+2).
    - rewrite Rpower_mult.
      rewrite Rinv_l; last by apply not_0_INR.
      by rewrite Rpower_1; lra.
    rewrite Rpower_pow; last by apply Rpwr_pos'.
    apply pow_incr.
    by split; first exact/Rlt_le/Rpwr_pos'; apply helper.
  Qed.

  Lemma exp_prod_lbnd_pos k: 2 <= (1 + /IPR k) ^ Pos.to_nat k.
  Proof.
    apply/Rle_trans; first exact/(exp_prod_lbnd (Pos.to_nat k).-1).
    by rewrite -S_INR -INR_IPR -(S_pred _ 0); try lra; lia.
  Qed.

  Lemma pow_pow x n m: (x ^ n) ^ m = x ^ (n * m).
  Proof. by elim: m => [ | m /= ->]; first rewrite muln0 //; rewrite mulnS pow_add. Qed.
    
  Lemma exp_prod_ubnd k m: /(1 + /(INR k + 1)) ^ (k.+1 * m) <= / 2 ^ m.
  Proof.
    rewrite -pow_pow -S_INR.
    apply/Rinv_le_contravar/pow_incr; first by apply/pow_lt; lra.
    by rewrite S_INR; split; try lra; apply/exp_prod_lbnd.
  Qed.

  Fixpoint pow_pos (p: positive) n :=
    match n with
    | 0%nat => 1%positive
    | S n' => (p * pow_pos p n')%positive
    end.

  Lemma pos_pow_pos p n: IPR p ^ n = IPR (pow_pos p n).
  Proof. by elim: n => //= n ->; rewrite -!INR_IPR -mult_INR Pos2Nat.inj_mul. Qed.

(*
  Fixpoint log2 p :=
    match p with
    | xH => 0%nat
    | xO p => (log2 p).+1
    | xI p => (log2 p).+1
    end.

  Lemma poss_gt p: (0 < Pos_size p)%nat.
  Proof. by case: p. Qed.

  Lemma size_log2 p: log2 p = (Pos_size p).-1.
  Proof. by elim: p => //= p ->; rewrite -(S_pred _ 0) //; apply/leP/poss_gt. Qed.

  Lemma log2_pow_pos (n: nat): log2 (pow_pos 2 n) = n.
  Proof. by elim: n => //= n ->. Qed.
*)

  Definition log2 p := Nat.log2 (Pos.to_nat p).

  Lemma log2_spec_ineq (p: positive): (pow_pos 2 (log2 p) <= p < pow_pos 2 (log2 p).+1)%positive.
  Proof.
    have /Nat.log2_spec [ineq ineq']:= Pos2Nat.is_pos p.
    split; first apply/Pos2Nat.inj_le/INR_le; last apply/Pos2Nat.inj_lt/INR_lt.
    - by rewrite INR_IPR -pos_pow_pos; suff <- //: INR 2 = IPR 2; rewrite -pow_INR; apply/le_INR.
    rewrite [X in _ < X]INR_IPR -pos_pow_pos.
    by suff<-//: INR 2 = IPR 2; rewrite -pow_INR; apply/lt_INR.
  Qed.

  Lemma Rlt_log2 (p: positive): IPR p < 2 ^ (log2 p).+1.
  Proof.
    suff ->//: 2 = IPR 2; rewrite pos_pow_pos -!INR_IPR.
    exact/lt_INR/Pos2Nat.inj_lt/(log2_spec_ineq _).2.
  Qed.
  
  Definition coeff_num A k n := (k.+1 * ((log2 (A * Pos.of_nat (k.+2))).+1 + n))%nat.
  
  Lemma sbnd_cnum a A k n:
    a \is_bounded_by A \and k -> Series (shift (coeff_num A k n) (ptw Rabs a)) <= /2 ^ n.
  Proof.
    have ? := Ipinv_ineq (pos_INR k).
    move => /sbnd_tail ineq; apply/Rle_trans; first exact/ineq; rewrite -pow_pow pow_add/Rdiv.
    rewrite Rinv_mult_distr; try by rewrite pow_pow; apply/pow_nonzero; lra.
    rewrite -!Rmult_assoc; apply/Rle_trans/exp_prod_ubnd/k.
    rewrite -[X in _ <= X]Rmult_1_l -pow_pow.
    apply/Rmult_le_compat_r; first by apply/Rlt_le/Rinv_0_lt_compat/pow_lt/pow_lt; lra.
    apply/(Rdiv_le_1 _ _ _).1; first by apply/pow_lt/pow_lt; lra.
    have ->: INR k + 2 = INR k.+2 by rewrite !S_INR; lra.
    apply/Rle_trans/pow_incr; try by split; last apply/exp_prod_lbnd; lra.
    apply/Rle_trans/Rlt_le/Rlt_log2.
    by rewrite -[X in _ <= X]INR_IPR Pos2Nat.inj_mul mult_INR INR_IPR Nat2Pos.id; try lra; lia.
  Qed. 

  Lemma pwrs_le a x n: \|x| <= 1 -> \|powers a x n| <= \|a n|.
  Proof. by move => /(pow_le_1_compat_abs n); rewrite /powers RPow_abs; split_Rabs; nra. Qed.
  
  Lemma acnv_pwrs a x: \|x| <= 1 -> absolutely_convergent a -> absolutely_convergent (powers a x).
  Proof.
    move => /pwrs_le ineq cnv; apply/ex_series_le/cnv => n.
    by rewrite/norm/=/abs/= Rabs_pos_eq; try exact/Rabs_pos.
  Qed.

  Lemma tpmn_psrs a A k n x: \|x| <= 1 -> a \is_bounded_by A \and k ->
    \|Series (powers a x) - \sum_(i< coeff_num A k n) powers a x i| <= / 2 ^ n.
  Proof.
    case eq: (coeff_num A k n) => [ | c] => xle1 bnd.
    - by rewrite big_ord0 Rminus_0_r; apply/Rle_trans/Rle_trans/sbnd_cnum/bnd/Req_le/Series_ext.
    rewrite (Series_incr_n _ c.+1); try exact/leP; last first.
    - exact/acnv_cnv/acnv_pwrs/sbnd_acnv/bnd.
    rewrite -sum_n_Reals sum_big_ord; have -> u v: u + v - u = v by lra.
    apply/Rle_trans.
    - by apply/Series_Rabs; have /(acnv_pwrs xle1)/(cnv_shft c.+1):= sbnd_acnv bnd.
    by rewrite -eq; apply/sbnd_cnum => i; apply/Rle_trans/bnd/pwrs_le.
    Unshelve.
    exact/a.
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
  (Rmult_rlzrf (name_pair x y)) (at level 30, format "x '*rq' y").    
  
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
    
  Definition sin_ps (nq: (nat*Q)) := match (nq.1 mod 4) with
                                   | 0%nat => 0
                                   | 1%nat => (inv_fact nq.1 nq.2)
                                   | 2%nat => 0
                                   | _ => -(inv_fact nq.1 nq.2)
                                   end.
  Definition sin_name := (make_ps_name sin_ps 1 1).
  Definition comp_sin (phi : (questions RQ)) := (sum_rlzrf' sin_name phi).
  Definition sin_plus_e := (addition_rlzrf sin_name exp_name).
  Definition sin_mult_e := (multiplication_rlzrf sin_name exp_name).
  Definition comp_spe (phi : (questions RQ)) := (sum_rlzrf' sin_plus_e phi).
  Definition comp_sme (phi : (questions RQ)) := (sum_rlzrf' sin_mult_e phi).
  Compute (comp_sme (Q2RQ (1#2)) (1#2)).
  Definition PSeries2 a x y := (PSeries (fun n => (PSeries (fun m => (a (n,m))) y)) x). 
  
