From mathcomp Require Import ssreflect seq ssrfun ssrbool ssrnat.
From rlzrs Require Import all_rlzrs.
From metric Require Import reals pointwise metric.
Require Import all_cs_base cprd classical_cont.
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
    split; last first => [/lim_tpmn/countable_choice [mu prp] | [phin [phi [phinxn [phinx lim]]]]].
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
    rewrite /baire.limit in lim.
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
    have ->: cptw_op op = ptw op \o_f (@cs_zip _ _ _ _ (metric_cs rdense) (metric_cs qdense)) by trivial.
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
  
  Lemma exists_minmod_met (f : metric_cs rdense -> metric_cs qdense) x:
    (f \is_continuous_in x)%met ->
    exists mu : nat -> nat, forall n,
      (forall y, (d x y <= /2 ^ (mu n) -> d (f x) (f y) <= /2 ^ n))
      /\
      forall m, (forall y, d x y <= /2 ^ m -> d (f x) (f y) <= (/2 ^ n)) -> (mu n <= m)%nat. 
  Proof.
    move => cont.
    suff /nat_choice [mu muprp]: forall n, exists m,
          (forall y, d x y <= /2 ^ m -> d (f x) (f y) <= /2 ^ n)
          /\
          (forall k : nat,
          (forall y : M, d x y <= / 2 ^ k -> d (f x) (f y) <= / 2 ^ n) -> (m <= k)%nat).
    - by exists mu => n; apply/muprp.
    move => n.
    have [ | delta [/dns0_tpmn [m mld] prp]]:= cont (/2^n); first exact/tpmn_lt.
    apply/well_order_nat; exists m => y dst.
    exact/prp/Rle_trans/Rlt_le/mld.
  Qed.

  Lemma mcont_cont (f: metric_cs rdense -> metric_cs qdense):
    (f \is_continuous)%met -> f \is_continuous.
  Proof.
    move => cont.
    have /countable_choice [mu minmod]:= exists_minmod_met (cont (r _)).
    Print baire.limit.   
    pose F := (make_mf (fun phi Fphi => forall n, exists k,
                              (mu (phi k) n.+1 <= k)%nat
                              /\
                              (forall k', (mu (phi k') n.+1 <= k')%nat ->(k <= k')%nat)
                              /\
                              d (q (Fphi n)) (f (r (phi k))) <= /2 ^ n.+1
                              /\
                              (forall m, d (q m) (f (r (phi k))) <= /2 ^ n.+1 -> (Fphi n <= m)%nat)
              )).
    have Fcont: F \is_continuous_operator.
    - move => /= phi Fphi /nat_choice [nu nu_prop].
      exists (fun n => (init_seg (nu n).+1)) => n psi coin Fphi' prop.
      have [k' [ineq [min [dst md]]]]:= prop n.    
      have keqk' : k' = nu n.
      + have [nu_prop1 [nu_prop2 _]]:= nu_prop n.
        rewrite coin.1 in nu_prop1.
        have /leP lt:= (min (nu n) nu_prop1).
        suff e0 : psi k' = phi k' by rewrite e0 in ineq; have /leP gt := (nu_prop2 k' ineq); lia.
        have [cs _] := coin_lstn phi psi (init_seg (nu n).+1).
        have [_ lst] := (lstn_iseg (@id nat) k' (nu n).+1).
        by symmetry; apply/(cs coin k')/lst; exists k'; split; first apply/leP; lia.
      have e0 : f (r (psi k')) = f (r (phi (nu n))) by rewrite keqk' coin.1.        
      have [_ [_ [nu1 nu4]]] := nu_prop n.
      rewrite -e0 in nu1 nu4.
      have /leP lt := md (Fphi n) nu1.
      have /leP gt := nu4 (Fphi' n) dst.
      lia.
    exists F; split; last exact/Fcont.
    apply/sing_rlzr_F2MF; first exact/cont_sing.
    split => [phi x phinx | phi x Fphi phinx val n].
    - suff /=/nat_choice [h /nat_choice [h']]: forall n, exists k, exists s : nat,
            (mu (phi k) n.+1 <= k)%nat /\
            (forall k' : nat, (mu (phi k') n.+1 <= k')%nat -> (k <= k')%nat) /\
            d (q s) (f (r (phi k))) <= / (2 ^ n.+1) /\
            (forall m : nat, d (q m) (f (r (phi k))) <= / (2 ^ n.+1) -> (s <= m)%nat).
      + by exists h' => n; exists (h n).
      move => n.
      suff /well_order_nat [k []]: exists k, (mu (phi k) n.+1 <= k)%nat.
      - exists k.
        have /well_order_nat [s [c sprp]]:= @qdense (f (r (phi k))) (/2^n.+1) (tpmn_lt _).      
        exists s; split => //; split => //.
        by split => [ | m]; rewrite dst_sym; last apply sprp.
      have [nu nuprp]:= exists_minmod_met (cont x).
      suff modmod: forall l n',
          d x (r l) <= /2 ^ (nu n'.+1).+1 -> (mu l n' <= (nu n'.+1).+1)%nat.
      - by exists (nu n.+2).+1; apply/modmod/phinx.
      move => z k dst; apply minmod => y dst'.
      apply/dst_le; last by rewrite tpmn_half; exact/Rle_refl.
      - rewrite dst_sym; apply nuprp.
        by apply/Rle_trans/tpmnP/leqW/leqnn; first exact/dst.
      by apply nuprp; apply/dst_le; first exact/dst; first exact/dst'; rewrite -tpmn_half; lra.
    rewrite dst_sym; have [k [ineq [min [dst prp]]]]:= val n.
    apply/dst_le; first exact/dst; last by rewrite [X in _ <= X]tpmn_half; apply/Rle_refl.
    apply minmod; apply/Rle_trans/tpmnP/ineq.
    rewrite dst_sym; apply/phinx.
  Qed.
End continuity.
