(*This file considers Baire space nat -> nat as example for
a space that can be thought about continuity on. *)
From mathcomp Require Import all_ssreflect.
From metric Require Import reals metric standard.
From Coquelicot Require Import Coquelicot.
Require Import all_core classical_cont.
Require Import Reals ClassicalChoice Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope metric_scope.
Local Open Scope baire_scope.

Section baire_distance.
  Context Q (cnt: nat -> Q).
  Hypothesis sur: cnt \is_surjective.
  Context (A: eqType).
  Notation B := (Q -> A).
  Notation init_seg n := (iseg cnt n).

  Definition baire_val_seq phipsi n :=
    search (fun i => (phipsi.1 (cnt i): A) != phipsi.2 (cnt i)) n.

  Lemma bvls_spec phi psi n:
    (forall m, (m < n)%nat -> phi (cnt m) = psi (cnt m)) <->
    baire_val_seq (phi, psi) n = n.
  Proof.
    split => [prp | eq m ineq].
    - rewrite/baire_val_seq /=.
      apply/eqP; rewrite eqn_leq; apply/andP; split; first exact/search_le.
      rewrite leqNgt search_find -{2}(size_iota 0 n) -has_find.
      apply/negP => /hasP [m]; rewrite mem_iota add0n => /andP [_ ineq] /negP prp'.
      exact/prp'/eqP/prp.
    apply/eqP/negP => /negP neq.
    suff: (baire_val_seq (phi, psi) n < n)%nat by rewrite eq => /leP; lia.
    rewrite /baire_val_seq search_find -{2}(size_iota 0 n) -has_find; apply/hasP.
    by exists m => //; rewrite mem_iota add0n; apply/andP.  
  Qed.

  Lemma bvls_coin phi psi n:
    (phi \and psi \coincide_on (init_seg n)) <-> baire_val_seq (phi, psi) n = n.
  Proof.
    rewrite coin_lstn -bvls_spec.
    split => [prp m ineq | prp q /lstn_iseg [m [ineq <-]]]; last exact/prp.
    by apply/prp/lstn_iseg; exists m.
  Qed.
    
  Lemma bvsq_ext phi psi n:
    (forall m, (m < n)%nat -> phi (cnt m) = psi (cnt m)) ->
    baire_val_seq (phi, psi) n = n.
  Proof. by move => /bvls_spec. Qed.

  Lemma bvsq_geq phi psi n: (baire_val_seq (phi, psi) n <= n)%nat.
  Proof. exact/search_le. Qed.

  Lemma bdsq_fchy phi psi: (fun n => /2^(baire_val_seq (phi, psi) n)) \is_fast_Cauchy_sequence.
  Proof.
    pose p i := phi (cnt i) != psi (cnt i).
    apply/cchy_eff_suff => n m ineq.
    have le: 0 <= /2^n by apply/Rlt_le/Rinv_0_lt_compat/pow_lt; lra.
    have le': 0 <= /2^m by apply/Rlt_le/Rinv_0_lt_compat/pow_lt; lra.
    case E:(has p (seq.iota 0%nat n.+1)). 
    - move: E => /hasP => [[k]]; rewrite mem_iota add0n => /andP [_ ineq'] neq.      
      rewrite /p/d/= Rminus_diag_eq /baire_val_seq; first by split_Rabs; lra.
      do 2 f_equal; rewrite -(search_eq neq); last by apply/leq_trans/ineq'.
      by rewrite -[RHS](search_eq neq) //; apply/leq_trans/ineq/leq_trans/ineq'.
    rewrite /d /= bvsq_ext => [ | k ineq']; last first.
    - apply/eqP/negP => neg.
      move: E => /hasP prp; apply/prp; exists k; last exact/negP.
      rewrite mem_iota add0n; apply/andP; split => //.
      by apply/leq_trans; first exact/ineq'.
    case E':(has (fun i => phi (cnt i) != psi (cnt i)) (seq.iota 0%nat m.+1)); last first. 
    - rewrite bvsq_ext => [ | k ineq']; first by split_Rabs; lra.
    - apply/eqP/negP => neg.
      move: E' => /hasP prp; apply/prp; exists k; last exact/negP.
      by rewrite mem_iota add0n; apply/andP; split; last by apply/leq_trans; first exact/ineq'.
    suff: (/2 ^ baire_val_seq (phi, psi) m <= /2 ^ n).  
    - by have := tpmn_pos n; have := tpmn_pos (baire_val_seq (phi, psi) m); split_Rabs; lra.
    apply/tpmnP; rewrite /baire_val_seq /=.
    rewrite -(@search_fail p n); first exact/search_inc.
    move => k pk; rewrite ltnNge; apply/negP => kln.
    move: E => /hasP [].
    by exists k; first by rewrite mem_iota; apply/andP.
  Qed.
  
  Lemma bdsq_sym phi psi n: baire_val_seq (phi, psi) n = baire_val_seq (psi, phi) n.
  Proof.
    apply/search_ext => k ineq /=.
    by apply/eqP; case: ifP => /eqP // neg eq; apply/neg.    
  Qed.
    
  Definition mf_baire_distance := make_mf (fun phipsi =>
    efficient_limit (fun n => /2^(baire_val_seq phipsi n))).
    
  Lemma bdst_sing: mf_baire_distance \is_singlevalued.
  Proof. by move => [phi psi] r r' dst dst'; apply/metric.lim_eff_sing/dst'/dst. Qed.

  Lemma bdst0 phi: mf_baire_distance (phi,phi) 0.
  Proof.
    by move => n; rewrite bvsq_ext; first by have:= tpmn_pos n; rewrite /d/=; split_Rabs; lra.
  Qed.

  Lemma bdst_tot: mf_baire_distance \is_total.
  Proof.
    move => [phi psi].
    have /fchy_lim_eff [ | r lmt]:= bdsq_fchy phi psi; first exact/R_cmplt.
    by exists r.
  Qed.

  Lemma bdst_sym phi psi: mf_baire_distance (phi, psi) === mf_baire_distance (psi, phi).
  Proof. by split => dst n; rewrite bdsq_sym; apply/dst. Qed.

  Definition baire_distance phi psi := iota (mf_baire_distance (phi,psi)).

  Lemma bdst_spec phi psi: mf_baire_distance (phi, psi) (baire_distance phi psi).
  Proof.
    apply/(iota_correct (mf_baire_distance (phi,psi))).
    have [x val]:= bdst_tot (phi, psi).
    by exists x; split => // x' val'; apply/bdst_sing/val'/val.
  Qed.

  Lemma bdst_val phi psi x: mf_baire_distance (phi, psi) x -> baire_distance phi psi = x.
  Proof. move => dst; exact/bdst_sing/dst/bdst_spec. Qed.

  Lemma bdst_lim phi psi:
    metric.limit (fun n => /2 ^ (baire_val_seq (phi, psi) n)) (baire_distance phi psi).
  Proof. exact/lim_eff_lim/bdst_spec. Qed.
    
  Lemma dst_pos phi psi: 0 <= baire_distance phi psi.
  Proof.
    apply/lim_pos => [ | n]; first exact/lim_eff_lim/bdst_spec.
    exact/tpmn_pos.
  Qed.
  
  Lemma dst_sym phi psi: baire_distance phi psi = baire_distance psi phi.
  Proof. exact/bdst_val/bdst_sym/bdst_spec. Qed.

  Lemma dstxx phi: baire_distance phi phi = 0.
  Proof. exact/bdst_val/bdst0. Qed.

  Lemma dst_eq phi psi: baire_distance phi psi = 0 -> phi = psi.
  Proof.
    move => eq.
    apply/functional_extensionality => q.
    have [n <-]:= sur q.
    suff /eqP/bvls_spec prp: baire_val_seq (phi, psi) n.+1 == n.+1 by apply/ prp.
    rewrite eqn_leq; apply/andP; split; first exact/search_le.
    by apply/tpmnP; have := bdst_spec phi psi n.+1; rewrite /d /=; split_Rabs; lra.
  Qed.

  Lemma dst_trngl phi psi psi':
    baire_distance phi psi <= baire_distance phi psi' + baire_distance psi' psi.
  Proof.
    apply/lim_inc/limD/bdst_lim/bdst_lim/bdst_lim => i; rewrite /pointwise.ptw_op /=. 
    rewrite tpmn_half.
    apply/Rplus_le_compat/tpmnP.
  Admitted.

  Definition metric_baire_mixin: MetricSpace.mixin_of B :=
    MetricSpace.Mixin dst_pos dst_sym dstxx dst_eq dst_trngl.

  Canonical metric_baire: MetricSpace := MetricSpace.Pack metric_baire_mixin B.

  Require Import classical_count.
  Lemma lim_lim: (@metric.limit metric_baire) =~= baire.limit.
  Proof.
    have [sec ms]:= exists_minsec sur.
    pose melt:= max_elt sec.
    move => xn x.
    split => [lmt L | lmt eps eg0].
    - have [ | N prp]:= lmt (/2^(melt L)); first by apply/Rinv_0_lt_compat/pow_lt; lra.
      exists N => m ineq.
      apply/coin_subl/coin_iseg/bvls_coin.
      apply/iseg_melt/ms.
      exact/leqnn.
      have : /2^(baire_val_seq (x, xn m) (melt L)) = /2^ (melt L).
  Admitted.
      
  Lemma cont_cont (F: B -> B): F \is_continuous_function <-> (F \is_continuous)%met.