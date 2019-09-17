From mathcomp Require Import ssreflect seq ssrfun ssrbool ssrnat choice.
From rlzrs Require Import all_rlzrs.
From metric Require Import reals pointwise all_metric.
Require Import all_cs_base cprd classical_cont classical_count.
Require Import Qreals Reals Psatz ClassicalChoice ChoiceFacts.
Require Import Morphisms.
Local Open Scope cs_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope R_scope.
Local Open Scope cs_scope.
Notation metric_limit:= pseudo_metric_spaces.limit.
Notation "x \is_metric_limit_of xn" := (metric_limit xn x) (at level 2): cs_scope.
Section metric_representation.
  Context (M: MetricSpace) (T: Type) (T_count: T \is_countable) (r: T -> M).
  Hypothesis rdense: codom (F2MF r) \is_dense_subset.

  Definition metric_representation : (nat -> T) ->> M := make_mf (fun phi x =>
    forall n, d(x, r (phi n)) <= /2^n).
  
  Lemma mrep_sur: metric_representation \is_cototal.
  Proof.
    move => x; have /dns_tpmn prp:= rdense.
    suff/countable_choice [phi phinx]:
      forall n, exists t, distance (x, r t) <= /2^n
      by exists phi; apply/phinx.
    by move => n; have [_ [[t <-] dst]]:= prp x n; exists t.
  Qed.

  Lemma mrep_spec phi: metric_representation phi === efficient_limit (r \o_f phi).
  Proof. done. Qed.

  Lemma mrep_sing: metric_representation \is_singlevalued.
  Proof.
    move => phi x y phinx phiny.
    apply/dst0_eq/cond_eq_f => [ | n _]; first exact/accf_tpmn.
    rewrite /R_dist Rminus_0_r tpmn_half.
    apply/Rle_trans/Rplus_le_compat/phiny/phinx.
    rewrite [X in _ <= _ + X]dst_sym.
    by rewrite Rabs_pos_eq; [apply/dst_trngl | apply/dst_pos].
  Qed.

  Definition metric_names: naming_space.
    exists nat T.
    - exact/0%nat.
    - exact/nat_count.
    exact/T_count.
  Defined.
  
  Definition metric_cs: cs.
    exists M metric_names metric_representation.
    split; [apply/mrep_sur | apply/mrep_sing].
  Defined.

  Lemma cnst_dscr t:
    (cnst t) \describes (r t) \wrt metric_cs.
  Proof. by move => n; rewrite dstxx; apply/tpmn_pos. Qed.

  Lemma cnst_sqnc_dscr t: (cnst t) \describes (cnst (r t)) \wrt (metric_cs\^w).
  Proof. by apply/Iprd_base => n m; rewrite dstxx; apply/tpmn_pos. Qed.
  
  Lemma Q_sqnc_dscr tn:
    (fun neps => tn neps.1) \describes (fun n => r (tn n)) \wrt (metric_cs\^w).
  Proof. by move => k m; rewrite dstxx; exact/tpmn_pos. Qed.

  Lemma lim_mlim : @limit metric_cs =~= metric_limit.
  Proof.
    move => xn x.
    split; last first => [/lim_tpmn/countable_choice [mu prp] | [phin [phi [phinxn [phinx /lim_coin lim]]]]].
    - have [phin phinxn]:= get_description (xn: metric_cs\^w).
      have [phi phinx]:= get_description (x: metric_cs).
      exists (fun mn => if (mu mn.2.+1 <= mn.1)%nat then phi mn.2.+1 else phin mn).
      exists (fun n => phi n.+1).
      split => [m n | ].
      + case: ifP => /= ineq; last exact/phinxn.
        rewrite tpmn_half.
        apply/Rle_trans/Rplus_le_compat/phinx/prp/ineq.
        rewrite [X in _ <= X + _]dst_sym.
        exact/dst_trngl.
      split => [n | ]; first by apply/Rle_trans/tpmnP; first exact/phinx.
      apply/lim_coin.
      elim => [ | n L [N prp']]; first by exists 0%nat.
      exists (maxn N (mu n.+1)) => m ineq /=.
      split; last exact/prp'/leq_trans/ineq/leq_maxl.
      rewrite/uncurry/=; case: ifP => ineq' //.
      have: (mu n.+1 <= m)%nat by apply/leq_trans/ineq/leq_maxr.
      by rewrite ineq'.
    apply/lim_tpmn => n.
    have [N prp]:= lim (iseg (@id nat) n.+2).
    exists N => m ineq.
    have /coin_agre prp':= prp m ineq.
    rewrite tpmn_half.
    apply/Rle_trans/Rplus_le_compat/phinxn/m/phinx.
    suff ->: phin (m, n.+1) = phi n.+1 by rewrite [X in _ <= _ + X]dst_sym; apply/dst_trngl.
    rewrite prp' //.
    by apply/lstn_iseg; exists n.+1.
  Qed.
End metric_representation.

Section continuity.  
  Context (M: MetricSpace) (r: sequence_in M).
  Hypothesis rdense: r \is_dense_sequence.
  Context (N: MetricSpace) (q: sequence_in N).
  Hypothesis qdense: q \is_dense_sequence.
  Notation cs_M := (metric_cs nat_count ((dseq_dns r).1 rdense)).
  Notation cs_N := (metric_cs nat_count ((dseq_dns q).1 qdense)).
  
  Lemma scnt_mscnt (f: cs_M -> cs_N):
    f \is_sequentially_continuous <-> ((f: M2PM M -> M2PM N) \is_sequentially_continuous)%metric.
  Proof.
    split => [cont x xn | cont x xn].
    - by rewrite -!lim_mlim; apply/cont.
    by rewrite !lim_mlim; apply/cont.
  Qed.

  Lemma rlzr_scnt (f: cs_M -> cs_N) F:
    F \realizes f -> F \is_sequentially_continuous_operator ->
    f \is_sequentially_continuous.
  Proof. by move => rlzr cont x xn; apply/rlzr_scnt/cont/rlzr/choice. Qed.

  Lemma cont_mcont (f: cs_M -> cs_N):
    f \is_continuous -> ((f: M2PM M -> M2PM N) \is_continuous)%metric.
  Proof.
    move => [F [/rlzr_F2MF rlzr cont]] x eps epsg0.
    have [phi' phinx]:= get_description (x: cs_M).
    pose phi n:= phi' n.+1.
    have [n | [Fphi val] prp]:= rlzr phi x; first by apply/Rle_trans/tpmnP; first exact/phinx.
    have [Lf md]:= cont phi Fphi val.
    have [ | n [_ ineq]]:= @accf_tpmn (eps/2); first by lra.
    pose K := foldr maxn 0%nat (Lf n).
    exists (/2^(foldr maxn 0%nat (Lf n)).+1).
    split => [ | y dst]; first by apply/Rinv_0_lt_compat/pow_lt; lra.
    have [psi' psi'ny]:= get_description (y: cs_M).
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
    apply/coin_agre => k.
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
  
  Lemma exists_minmod_met (f : cs_M -> cs_N) x:
    ((f: M2PM M -> M2PM N) \continuous_in x)%metric ->
    exists mu : nat -> nat, forall n,
      (forall y, (d (x, y)<= /2 ^ (mu n) -> d (f x, f y) <= /2 ^ n))
      /\
      forall m, (forall y, d (x, y) <= /2 ^ m -> d (f x, f y) <= (/2 ^ n)) -> (mu n <= m)%nat. 
  Proof.
    move => cont.
    suff /countable_choice [mu muprp]: forall n, exists m,
          (forall y, d (x, y) <= /2 ^ m -> distance (f x, f y) <= /2 ^ n)
          /\
          (forall k : nat,
          (forall y : M, d (x, y) <= / 2 ^ k -> distance (f x, f y) <= / 2 ^ n) -> (m <= k)%nat).
    - by exists mu => n; apply/muprp.
    move => n.
    have [ | delta [/dns0_tpmn [m mld] prp]]:= cont (/2^n); first exact/tpmn_lt.
    apply/well_order_nat; exists m => y dst.
    exact/prp/Rle_trans/Rlt_le/mld.
  Qed.

  Lemma mcont_cont (f: cs_M -> cs_N):
    ((f: M2PM M -> M2PM N) \is_continuous)%metric -> f \is_continuous.
  Proof.
    move => cont.
    have /countable_choice [mu minmod]:= exists_minmod_met (cont (r _)).
    pose F := (make_mf (fun phi Fphi => forall n, exists k,
                              (mu (phi k) n.+1 <= k)%nat
                              /\
                              (forall k', (mu (phi k') n.+1 <= k')%nat ->(k <= k')%nat)
                              /\
                              distance (q (Fphi n), f (r (phi k))) <= /2 ^ n.+1
                              /\
                              (forall m, distance (q m, f (r (phi k))) <= /2 ^ n.+1 -> (Fphi n <= m)%nat)
              )).
    have Fcont: F \is_continuous_operator.
    - move => /= phi Fphi /countable_choice [nu nu_prop].
      exists (fun n => (init_seg (nu n).+1)) => n psi coin Fphi' prop.
      have [k' [ineq [min [dst md]]]]:= prop n.    
      have keqk' : k' = nu n.
      + have [nu_prop1 [nu_prop2 _]]:= nu_prop n.
        rewrite coin.1 in nu_prop1.
        have /leP lt:= (min (nu n) nu_prop1).
        suff e0 : psi k' = phi k' by rewrite e0 in ineq; have /leP gt := (nu_prop2 k' ineq); lia.
        have [cs _] := coin_agre (init_seg (nu n).+1) phi psi.
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
    split => [phi [x phinx] | phi x Fphi phinx val n].
    - suff /=/countable_choice [h /countable_choice [h']]: forall n, exists k, exists s : nat,
            (mu (phi k) n.+1 <= k)%nat /\
            (forall k' : nat, (mu (phi k') n.+1 <= k')%nat -> (k <= k')%nat) /\
            distance (q s, f (r (phi k))) <= / (2 ^ n.+1) /\
            (forall m : nat, distance (q m, f (r (phi k))) <= / (2 ^ n.+1) -> (s <= m)%nat).
      + by exists h' => n; exists (h n).
      move => n.
      suff /well_order_nat [k []]: exists k, (mu (phi k) n.+1 <= k)%nat.
      - exists k.
        have /well_order_nat [s [c sprp]]:= @qdense (f (r (phi k))) (/2^n.+1) (tpmn_lt _).      
        exists s; split => //; split => //.
        by split => [ | m]; rewrite dst_sym; last apply sprp.
      have [nu nuprp]:= exists_minmod_met (cont x).
      suff modmod: forall l n',
          distance (x, r l) <= /2 ^ (nu n'.+1).+1 -> (mu l n' <= (nu n'.+1).+1)%nat.
      - by exists (nu n.+2).+1; apply/modmod/phinx.
      move => z k dst; apply minmod => y dst'.
      apply/dst_le; last by rewrite tpmn_half; exact/Rle_refl.
      - rewrite dst_sym; apply nuprp.
        by apply/Rle_trans/tpmnP/leqW/leqnn; first exact/dst.
      by apply nuprp; apply/dst_le; first exact/dst; first exact/dst'; rewrite -tpmn_half; lra.
    rewrite dst_sym; have [k [ineq [min [dst prp]]]]:= val n.
    apply/dst_le; first exact/dst; last by rewrite [X in _ <= X]tpmn_half; apply/Rle_refl.
    apply minmod; apply/Rle_trans/tpmnP/ineq.
    by rewrite dst_sym.
  Qed.

  (*
  Context (K: MetricSpace) (s: sequence_in K) (somet
    Lemma ptw_op_scnt (K: MetricSpace) s (sdense: @dense_sequence K s)
        (op: cs_M * cs_N -> metric_cs sdense) xn x yn y:
    op \is_continuous -> x \is_limit_of xn -> y \is_limit_of yn ->
    (op (x, y)) \is_limit_of (cptwn_op op (xn,yn)).
  Proof.
    move => /cont_scnt cont lmt lmt'.    
    have ->: cptw_op op = ptw op \o_f (@cs_zip _ _ _ _ (metric_cs rdense) (metric_cs qdense)) by trivial.
    apply/cont; first exact/choice.
    by rewrite lim_prd.
  Qed.
  *)
End continuity.