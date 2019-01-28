From mathcomp Require Import ssreflect seq ssrfun ssrbool ssrnat.
From rlzrs Require Import all_rlzrs.
From metric Require Import reals pointwise metric.
Require Import all_cs_base cprd.
Require Import Qreals Reals Psatz ClassicalChoice ChoiceFacts.
Require Import Morphisms.
Local Open Scope cs_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope R_scope.
Local Open Scope cs_scope.
Notation metric_limit:= metric.limit.
Notation "x \is_metric_limit_of xn" := (metric_limit xn x) (at level 2): cs_scope.
Section metric_representation.
  Context (M: MetricSpace) (r: nat -> M). 
  Hypothesis rdense: dense_sequence r.

  Definition metric_representation : (nat -> nat) ->> M := make_mf (fun phi x =>
    forall n, d x (r (phi n))<= /2^n).
  
  Lemma mrep_sur: metric_representation \is_cototal.
  Proof.
    move => x; have /dseq_tpmn prp:= rdense.
    by have /nat_choice:= prp x.
  Qed.

  Lemma mrep_spec phi: metric_representation phi === efficient_limit (r \o_f phi).
  Proof. done. Qed.

  Lemma mrep_sing: metric_representation \is_singlevalued.
  Proof.
    move => phi x y phinx phiny.
    apply/dst_eq/cond_eq_f => [ | n _]; first exact/accf_tpmn.
    rewrite /R_dist Rminus_0_r.
    apply/Rle_trans.
    - rewrite Rabs_pos_eq; last by have:= dst_pos x y; lra.
      apply/(dst_trngl (r (phi n.+1))) .
    rewrite tpmn_half.
    apply/Rplus_le_compat; first exact/phinx.
    by rewrite dst_sym; apply/phiny.
  Qed.

  Definition metric_cs := make_cs 0%nat 0%nat nat_count nat_count mrep_sur mrep_sing.

  Lemma cnst_dscr n:
    (cnst n) \describes (r n) \wrt metric_cs.
  Proof.
    by rewrite /cnst /= dstxx => k; apply/Rlt_le/Rinv_0_lt_compat/pow_lt; lra.
  Qed.

  Lemma cnst_sqnc_dscr n: (cnst n) \describes (cnst (r n)) \wrt (metric_cs\^w).
  Proof.
    rewrite /cnst /= dstxx => k m.
    by apply/Rlt_le/Rinv_0_lt_compat/pow_lt; lra.
  Qed.
  
  Lemma Q_sqnc_dscr qn:
    (fun neps => qn neps.1) \describes (fun n => r (qn n)) \wrt (metric_cs\^w).
  Proof.
    move => k m; rewrite dstxx.
    by apply/Rlt_le/Rinv_0_lt_compat/pow_lt; lra.
  Qed.

  Lemma lim_mlim : @limit metric_cs =~= metric_limit.
  Proof.
    move => xn x.
    split; last first => [/lim_tpmn/choice [mu prp] | [phin [phi [phinxn [phinx lim]]]]].
    - have [phin phinxn]:= get_description (xn: metric_cs\^w).
      have [phi phinx]:= get_description (x: metric_cs).
      exists (fun mn => if (mu mn.2.+1 <= mn.1)%nat then phi mn.2.+1 else phin mn).
      exists (fun n => phi n.+1).
      split => [m n | ].
      + case: ifP => /= ineq; last exact/phinxn.
        apply/Rle_trans; first apply/(dst_trngl x).
        rewrite tpmn_half; apply/Rplus_le_compat; last exact/phinx.
        by rewrite dst_sym; apply/prp.
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
    apply/lim_tpmn => n.
    have [N prp]:= lim (iseg (@id nat) n.+2).
    exists N => m ineq.
    have /coin_lstn prp':= prp m ineq.
    apply/Rle_trans; first exact/(dst_trngl (r (phi n.+1))).
    apply/Rle_trans; first apply/Rplus_le_compat; first exact/phinx.
    + rewrite dst_sym (prp' n.+1); first exact/phinxn.
      by apply/lstn_iseg; exists n.+1.
    by rewrite -tpmn_half; apply/Rle_refl.
  Qed.
End metric_representation.

Section continuity.  
  Context (M N: MetricSpace) (r: nat -> M) (q: nat -> N). 
  Hypothesis rdense: dense_sequence r.
  Hypothesis qdense: dense_sequence q.
  Lemma scnt_mscnt (f: metric_cs rdense -> metric_cs qdense):
    f \is_sequentially_continuous <-> (f \is_sequentially_continuous)%met.
  Proof.
    split => [cont x xn | cont x xn].
    - by rewrite -!lim_mlim; apply/cont.
    by rewrite !lim_mlim; apply/cont.
  Qed.

  Lemma ptw_op_scnt (K: MetricSpace) s (sdense: @dense_sequence K s)
        (op: metric_cs rdense \*_cs metric_cs qdense -> metric_cs sdense) xn x yn y:
    op \is_continuous -> x \is_limit_of xn -> y \is_limit_of yn ->
    (op (x, y)) \is_limit_of (cptwn_op op (xn,yn)).
  Proof.
    move => /cont_scnt cont lmt lmt'.    
    have ->: cptw_op op = ptw op \o_f (@cs_zip _ _ _ (metric_cs rdense) (metric_cs qdense)) by trivial.
    apply/cont; first exact/choice.
    by rewrite lim_prd.
  Qed.

  Lemma rlzr_scnt (f: metric_cs rdense -> metric_cs qdense) F:
    F \realizes (F2MF f) -> F \is_sequentially_continuous_operator -> f \is_sequentially_continuous.
  Proof. by move => rlzr cont x xn; apply/rlzr_scnt/cont/rlzr/choice. Qed.

  Lemma cont_mcont (f: metric_cs rdense -> metric_cs qdense):
    f \is_continuous -> (f \is_continuous)%met.
  Proof.
    move => [F [/rlzr_F2MF rlzr cont]] x eps epsg0.
    have [phi' phinx]:= get_description (x: metric_cs rdense).
    pose phi n:= phi' n.+1.
    have [ | [Fphi val] prp]:= rlzr phi x.
    - move => n; apply/Rle_trans; first exact/phinx.
      apply/Rinv_le_contravar/Rle_pow/leP => //; try lra.
      by apply/pow_lt; lra.
    have [Lf md]:= cont phi Fphi val.
    have [ | n [_ ineq]]:= @accf_tpmn (eps/2); first by lra.
    pose K := foldr maxn 0%nat (Lf n).
    exists (/2^(foldr maxn 0%nat (Lf n)).+1).
    split => [ | y dst]; first by apply/Rinv_0_lt_compat/pow_lt; lra.
    have [psi' psi'ny]:= get_description (y: metric_cs rdense).
    pose psi k := if (k < (foldr maxn 0%nat (Lf n)).+1)%nat then phi k else psi' k.
    have [ | [Fpsi val'] prp']:= rlzr psi y.
    - rewrite /psi => k.
      case E: (k < (foldr maxn 0 (Lf n)).+1)%nat; [ | apply psi'ny].
      apply/dst_le; first by rewrite dst_sym; apply/dst.
      + exact/phinx.
      rewrite [X in _ <= X]tpmn_half.
      by apply/Rplus_le_compat; apply/Rinv_le_contravar/Rle_pow/leP => //; try apply/pow_lt; try lra.
    suff eq: Fpsi n = Fphi n.
    - apply/dst_le; first by apply/prp/n; first exact/val.
      + by rewrite -eq dst_sym; apply/prp'.
      lra.
    apply/md/val'; rewrite /psi.
    apply/coin_lstn => k.
    elim: (Lf n) => // m L ih /= [<- | lstn].
    - suff ->: (m < (maxn m (foldr maxn 0 L)).+1)%nat by trivial.
      by have:= leq_maxl m (foldr maxn 0%nat L).
    rewrite {1}ih //.
    case: ifP => [ineq' |].
    - by have ->: (k < (maxn m (foldr maxn 0 L)).+1)%nat by apply/leq_trans; [apply/ineq' | apply/leq_maxr].
    case: ifP => // ineq' /negP ineq''.
    exfalso; apply/ineq''; move: lstn.
    elim L => // a L' ih' /=[ <- | lstn]; first by have:= leq_maxl a (foldr maxn 0 L')%nat.
    by apply/leq_trans; first exact/ih'; have := leq_maxr a (foldr maxn 0 L')%nat.
  Qed.
End continuity.