From mathcomp Require Import ssreflect seq ssrfun ssrbool ssrnat.
Require Import all_cs reals.
Require Import Qreals Reals Psatz ClassicalChoice.
Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope R_scope.

Notation subset := mf_subset.type.
Section metric_spaces.
  Context (M: Metric_Space).
  Arguments dist {m}.
  Arguments dist_tri {m} {x} {y}.
  Arguments dist_pos {m}.
  Arguments dist_refl {m}.
  Arguments dist_sym {m}.
  Coercion Base: Metric_Space >-> Sortclass.

  Definition metric_limit := make_mf (fun xn x =>
    forall eps, 0 < eps -> exists N, forall m,
          (N <= m)%nat -> @dist M x (xn m) <= eps).

  Global Instance limit_prpr:
    Proper (@eqfun M nat ==> @set_equiv M) metric_limit.
  Proof.
    move => xn yn eq x.
    split => lim eps eg0; have [N prp]:= lim eps eg0; exists N => m.
    - by rewrite -(eq m); apply/prp.
    by rewrite (eq m); apply/prp.
  Qed.
    
  Lemma lim_sing: metric_limit \is_singlevalued.
  Proof.
    move => xn x x' limxnx limxnx'.
    apply/dist_refl/cond_eq => eps epsg0.
    rewrite Rminus_0_r Rabs_pos_eq; last exact/Rge_le/dist_pos.
    have [ | N Nprp]:= limxnx (eps/3); try lra.
    have [ | N' N'prp]:= limxnx' (eps/3); try lra.
    pose k:= maxn N N'.
    apply/Rle_lt_trans; first exact/(dist_tri (xn k)).
    have ->: eps = eps/2 + eps/2 by lra.
    apply/Rplus_lt_compat; apply/Rle_lt_trans.
    - + * by apply/Nprp; rewrite /k leq_maxl.
        lra.
      by rewrite dist_sym; apply /N'prp; rewrite/k leq_maxr.
    lra.
  Qed.

  Lemma lim_cnst x: metric_limit (cnst x) x.
  Proof.
    by exists 0%nat; rewrite /cnst (dist_refl x x).2// => m ineq; lra.
  Qed.
  
  Definition limit_tpmn := make_mf (fun xn x =>
    forall n, exists N, forall m, (N <= m)%nat -> @dist M x (xn m) <= /2 ^ n).

  Lemma cond_eq_tpmn x y:
    (forall n, @dist M x y <= / 2 ^ n) -> x = y.
  Proof.
    move => prp.
    apply/dist_refl.
    symmetry; apply/cond_eq_f.
    - exact/accf_2pown.
    move => n/= ineq.
    rewrite /R_dist Rminus_0_l Rabs_Ropp Rabs_pos_eq.
    exact/prp.
    exact/Rge_le/dist_pos.
  Qed.

  Lemma lim2_lim: limit_tpmn =~= metric_limit.
  Proof.
    move => xn x; split => [lim eps eg0 | lim n].
    - have [n ineq]:= accf_2pown eg0.
      have [N prp]:= lim n.
      exists N => m Nlm.
      exact/Rlt_le/Rle_lt_trans/ineq.2/prp.
    have [ | N prp]:= lim (/2 ^ n); first by apply/Rinv_0_lt_compat/pow_lt; lra.
    by exists N.
  Qed.
            
  Definition dense_subset (A: subset M):=
    forall x eps, eps > 0 -> exists y, y \from A /\ dist x y <= eps.

  Global Instance dns_prpr: Proper (@set_equiv M ==> iff) dense_subset.
  Proof.
    move => A B eq; split => dns x eps eg0; have [y []]:= dns x eps eg0; exists y.
    - by rewrite -eq.
    by rewrite eq.
  Qed.
    
  Lemma dense_tpmn (A: subset M):
    dense_subset A <-> forall x n, exists y, y \from A /\ dist x y <= /2^n.
  Proof.
    split => [dns x n | dns x eps eg0]; first by apply/dns/Rlt_gt/Rinv_0_lt_compat/pow_lt; lra.
    have [n ineq]:= accf_2pown eg0.
    have [y []]:= dns x n.
    exists y; split => //.
    exact/Rlt_le/Rle_lt_trans/ineq.2.
  Qed.

  Definition dense_sequence (r: nat -> M) :=
    forall x eps, 0 < eps -> exists n, dist x (r n) <= eps.

  Lemma dseq_dns (r: nat -> M):
    dense_sequence r <-> dense_subset (codom (F2MF r)). 
  Proof.
    split => dns x eps eg0; have []:= dns x eps eg0.
    - by move => n ineq; exists (r n); split => //; exists n.
    by move => y [[n <-] ineq]; exists n.
  Qed.

  Lemma dseq_tpmn (r: nat -> M):
    dense_sequence r <-> forall x n, exists m, dist x (r m) <= /2^n.
  Proof.
    split => [dns x n| dns x eps eg0]; first apply/dns.
    - by apply/Rinv_0_lt_compat/pow_lt; lra.
    have [n ineq]:= accf_2pown eg0.
    have [m prp]:= dns x n.
    exists m.
    exact/Rlt_le/Rle_lt_trans/ineq.2/prp.
  Qed.
  
End metric_spaces.
Arguments dist {m}.
Arguments dist_tri {m} {x} {y}.
Arguments dist_pos {m}.
Arguments dist_refl {m}.
Arguments dist_sym {m}.
Arguments metric_limit {M}.

Section efficient_convergence.
  Context (M: Metric_Space).

  Definition Cauchy_sequence := make_subset (fun (xn: nat -> M) =>
    forall eps, 0 < eps -> exists N, forall n m,
          (N <= n)%nat -> (N <= m)%nat -> dist (xn n) (xn m) <= eps).

  Definition complete := Cauchy_sequence \is_subset_of dom metric_limit.
  
  Definition fast_Cauchy_sequence := make_subset (fun (xn: nat -> M) =>
    forall n m, dist (xn n) (xn m) <= /2^n + /2^m).

  Lemma tpmn_half n: / 2 ^ n = / 2 ^ n.+1 + / 2 ^ n.+1.
  Proof.
    by have pos:= pow_lt 2 n; rewrite /= Rinv_mult_distr; lra.
  Qed.
  
  Lemma cchy_fast_cchy xn:
    fast_Cauchy_sequence xn -> Cauchy_sequence xn.
  Proof.
    move => cchy eps epsg0.
    have [N [_ ineq]]:= accf_2pown epsg0.
    exists N.+1 => n m nineq mineq.
    apply/Rlt_le/Rle_lt_trans; last exact/ineq.
    apply /Rle_trans; [exact/cchy | rewrite (tpmn_half N)].
    by apply/Rplus_le_compat; apply/Rinv_le_contravar;
      try apply/pow_lt; try apply/Rle_pow/leP => //; try lra.
  Qed.
    
  Lemma cchy_tpmn xn:
    (forall k, exists N, forall n m,
            (N <= n <= m)%nat -> dist (xn n) (xn m) <= /2^k) <->
    Cauchy_sequence xn.
  Proof.
    split => [ass eps epsg0 | cchy k]; last first.
    - have [ | N prp]:= cchy (/2 ^ k).
      + by apply/Rinv_0_lt_compat/pow_lt; lra.
      exists N => n m /andP [ineq ineq'].
      exact/prp/leq_trans/ineq'.
    have [N [g0 /Rlt_le ineq]]:= accf_2pown epsg0.
    have [N' N'prp]:= ass N.
    exists N' => n m nineq mineq.
    case/orP: (leq_total n m) => ineq'.
    - by apply/Rle_trans; first exact/N'prp/andP.
    by rewrite dist_sym; apply/Rle_trans; first apply/N'prp/andP.
  Qed.

  Lemma cchy_fast_sseq xn:
    Cauchy_sequence xn -> exists mu, fast_Cauchy_sequence (xn \o_f mu).
  Proof.
    move => /cchy_tpmn cchy.    
    have /choice[mu prp]:= cchy.
    exists mu => n m /=.
    case/orP: (leq_total (mu n) (mu m)) => ineq.
    - apply/Rle_trans; first by apply/prp/andP.
      rewrite -[X in X <= _]Rplus_0_r; apply/Rplus_le_compat_l.
      by apply/Rlt_le/Rinv_0_lt_compat/pow_lt; lra.
    rewrite dist_sym; apply/Rle_trans; first by apply/prp/andP.
    rewrite -[X in X <= _]Rplus_0_l; apply/Rplus_le_compat_r.
    by apply/Rlt_le/Rinv_0_lt_compat/pow_lt; lra.
  Qed.

  Definition efficient_limit := make_mf (fun xn (x: M) =>
    forall n, dist x (xn n) <= /2^n).

  Lemma lim_eff_lim: efficient_limit =~= metric_limit|_(fast_Cauchy_sequence).
  Proof.
    move => xn x; split => [lim | [cchy lim] n].
    - split => [n m | eps epsg0].
      + apply /Rle_trans/Rplus_le_compat/lim; first apply/(dist_tri x).
        by rewrite dist_sym; apply/lim.
      have [n ineq]:= accf_2pown epsg0.
      exists n => m nlm.
      apply/Rlt_le/Rle_lt_trans/ineq.2/Rle_trans; first exact/lim.
      apply/Rinv_le_contravar; first by apply/pow_lt; lra.
      by apply/Rle_pow/leP => //; lra.
    suff all: forall m, dist x (xn n) <= / 2 ^ n + / 2 ^ m.
    - suff: dist x (xn n) - / 2 ^ n <= 0 by lra.
      apply/Rnot_lt_le => ineq.
      have [m ineq']:= accf_2pown ineq.
      by have := all m; lra.
    move => m.  
    have [ | N prp]:= lim (/2 ^ m.+1); first by apply/Rinv_0_lt_compat/pow_lt; lra.
    rewrite (tpmn_half m) -Rplus_assoc Rplus_comm.
    apply/Rle_trans/Rplus_le_compat.
    - + by apply/(dist_tri (xn (maxn m.+1 N))).
    - exact/prp/leq_maxr.
    rewrite dist_sym; apply/Rle_trans; first exact/cchy.
    apply/Rplus_le_compat_l/Rinv_le_contravar/Rle_pow/leP/leq_maxl; try lra.
    by apply/pow_lt; lra.
  Qed.
    
   Lemma lim_exte_lim_eff : metric_limit \extends efficient_limit.
   Proof.
    rewrite lim_eff_lim {2}[metric_limit]restr_all.
    exact/exte_restr/subs_all.
  Qed.

  Lemma lim_tight_lim_eff: metric_limit \tightens efficient_limit.
  Proof.
    apply sing_exte_tight; [exact/lim_sing | exact/lim_exte_lim_eff].
  Qed.

  Lemma lim_eff_sing: efficient_limit \is_singlevalued.
  Proof.
    by apply /exte_sing; first apply/ lim_exte_lim_eff; last apply/lim_sing.
  Qed.

  Lemma Cauchy_crit_eff_suff xn:
    (forall n m, (n <= m)%nat -> dist (xn n) (xn m) <= /2^n + /2^m) ->
    fast_Cauchy_sequence xn.
  Proof.
    move => ass n m.
    case /orP: (leq_total n m) => ineq; first by apply ass.
    by rewrite dist_sym Rplus_comm; apply ass.
  Qed.

End efficient_convergence.
  
Section metric_representation.
  Context (M: Metric_Space) (r: nat -> Base M). 
  Hypothesis rdense: dense_sequence r.

  Definition m_rep : (nat -> nat) ->> M := make_mf (fun phi x =>
    forall n, dist x (r (phi n))<= /2^n).

  Lemma m_rep_sur: m_rep \is_cototal.
  Proof.
    move => x; have /dseq_tpmn prp:= rdense.
    by have /choice:= prp x.
  Qed.
  
  Lemma m_rep_sing: m_rep \is_singlevalued.
  Proof.
    move => phi x y phinx phiny.
    apply/dist_refl/cond_eq_f => [ | n _]; first exact/accf_2pown.
    rewrite /R_dist Rminus_0_r.
    apply/Rle_trans.
    - rewrite Rabs_pos_eq; last by have:= dist_pos x y; lra.
      apply/(dist_tri (r (phi n.+1))) .
    rewrite tpmn_half.
    apply/Rplus_le_compat; first exact/phinx.
    by rewrite dist_sym; apply/phiny.
  Qed.

  Definition cs_M := continuity_space.Pack 0%nat 0%nat nat_count nat_count
                                           (make_dict m_rep_sur m_rep_sing).
  
  Lemma cnst_dscr n:
    (cnst n) \is_description_of (r n: cs_M).
  Proof.
    rewrite /cnst => k.
    have /dist_refl -> :=eq_refl (r n).
    by apply/Rlt_le/Rinv_0_lt_compat/pow_lt; lra.
  Qed.

  Lemma cnst_sqnc_dscr n: (cnst n) \is_description_of (cnst (r n): cs_M\^w).
  Proof.
    rewrite /cnst => k m.
    have /dist_refl -> := eq_refl (r n).
    by apply/Rlt_le/Rinv_0_lt_compat/pow_lt; lra.
  Qed.
  
  Lemma Q_sqnc_dscr qn:
    (fun neps => qn neps.1) \is_description_of ((fun n => r (qn n)): cs_M\^w).
  Proof.
    move => k m /=.
    have /dist_refl -> := eq_refl (r (qn k)).
    by apply/Rlt_le/Rinv_0_lt_compat/pow_lt; lra.
  Qed.

  Lemma lim_cs_lim : metric_limit =~= @cs_limit cs_M.
  Proof.
    move => xn x.
    split => [/lim2_lim/choice [mu prp] | [phin [phi [phinxn [phinx lim]]]]].
    - have [phin phinxn]:= get_description (xn: cs_M\^w).
      have [phi phinx]:= get_description (x: cs_M).
      exists (fun mn => if (mu mn.2.+1 <= mn.1)%nat then phi mn.2.+1 else phin mn).
      exists (fun n => phi n.+1).
      split => [m n | ].
      + case: ifP => /= ineq; last exact/phinxn.
        apply/Rle_trans; first apply/(dist_tri x).
        rewrite tpmn_half; apply/Rplus_le_compat; last exact/phinx.
        by rewrite dist_sym; apply/prp.
      split.
      - move => n; apply/Rle_trans; first exact/phinx.
        apply/Rinv_le_contravar/Rle_pow/leP => //; try lra.
        by apply/pow_lt; lra.
      elim => [ | n L [N prp']]; first by exists 0%nat.
      exists (maxn N (mu n.+1)) => m ineq /=.
      split; last exact/prp'/leq_trans/ineq/leq_maxl.
      rewrite/uncurry/=; case: ifP => ineq' //.
      have: (mu n.+1 <= m)%nat by apply/leq_trans/ineq/leq_maxr.
      by rewrite ineq'.
    apply/lim2_lim => n.
    have [N prp]:= lim (iseg (@id nat) n.+2).
    exists N => m ineq.
    have /coin_lstn prp':= prp m ineq.
    apply/Rle_trans; first exact/(dist_tri (r (phi n.+1))).
    apply/Rle_trans; first apply/Rplus_le_compat; first exact/phinx.
    + rewrite dist_sym (prp' n.+1); first exact/phinxn.
      by apply/lstn_iseg; exists n.+1.
    by rewrite -tpmn_half; apply/Rle_refl.
  Qed.

  Lemma ptw_op_scnt (op: cs_M \*_cs cs_M -> cs_M) xn x yn y:
    op \is_continuous -> metric_limit xn x -> metric_limit yn y ->
    metric_limit (cptwn_op op (xn,yn)) (op (x,y)).
  Proof.
    move => /cont_scnt cont lmt lmt'.    
    have ->: cptw_op op = ptw op \o_f (@cs_zip _ _ _ cs_M cs_M) by trivial.
    - by rewrite lim_cs_lim; apply/cont; rewrite lim_prd -!lim_cs_lim.
  Qed.
End metric_representation.