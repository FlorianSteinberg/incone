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
  
  Lemma exists_minmod_met (f : metric_cs rdense -> metric_cs qdense) :
    (f \is_continuous)%met ->
    exists mu : M -> nat -> nat, forall x n,
      (forall y, (d x y <= /2 ^ (mu x n) -> d (f x) (f y) <= /2 ^ n))
      /\
      forall m, (forall y, d x y <= /2 ^ m -> d (f x) (f y) <= (/2 ^ n)) -> (mu x n <= m)%nat. 
  Proof.
    move => cont.
    suff /choice [mu muprp]: forall xn, exists mu,
          (forall y, d xn.1 y <= /2 ^ mu -> d (f xn.1) (f y) <= /2 ^ xn.2)
          /\
          (forall m : nat,
          (forall y : M, d xn.1 y <= / 2 ^ m -> d (f xn.1) (f y) <= / 2 ^ xn.2) -> (mu <= m)%nat).
    - by exists (fun x n => mu (x, n)) => x n; apply/(muprp (x, n)).
    pose mf_mod := make_mf (fun xn m => 
           (forall y, d xn.1 y <= /2 ^ m ->  d (f xn.1) (f y) <= /2 ^ xn.2)).
    have mod_tot: mf_mod \is_total.
    - move => [x n].
      have [ | delta [/dns0_tpmn [m mld] prp]]:= cont x (/2^n); first exact/tpmn_lt.
      by exists m => y /=dst; apply/prp; lra.
    move => [x n].
    by have := @classical_cont.well_order_nat (mf_mod (x, n)) (mod_tot (x, n)).
  Qed.

  Lemma mcont_cont (f: metric_cs rdense -> metric_cs qdense):
    (f \is_continuous)%met -> f \is_continuous.
    move => /exists_minmod_met [mu minmod].
    
    case : (mu_exists' H) => [ mu [mu_pos [mule1 [mu_modulus mu_cont]]]].
    
    have st : forall x phi n, (phi \describes x \wrt (metric_cs rdense)) -> exists k, (/2 ^ k) <= (mu (r (phi k)) n).
    - move => x phi n phi_prop.
      specialize (st0 x).
      apply ClassicalChoice.choice in st0.
      case st0.
      move => st0f st0fprop.
      simpl in phi_prop.
      have closeness : forall k, ((st0f n.+1) <= k) % nat ->  (mu x n.+1)/4 <= (mu (r (phi k)) n).
      + move => k k_prop.
        have stprop := (st0fprop (n.+1)).
        have xclose1 : (d x (r (phi k))) <= (mu x n.+1)/2.
        * have xclose' := (phi_prop (k)).
          have triv : (/2 ^ k) <= (/2 ^ (st0f n.+1)) by apply /tpmnP.
          apply /Rle_trans.
          by apply xclose'.
        apply /Rle_trans.
        * by apply triv.
        by apply stprop.
      have xclose : (d x (r (phi k))) <= (mu x n.+1).
      * have := (mu_pos x n.+1).
          by lra.
        have fxclose : d (f x) (f (r (phi k))) <= /2^(n.+1).
        * have mod' := (mu_modulus x (r (phi k)) n.+1 (xclose)).
          done.
        have p0 : forall y, (d (r (phi k)) y) <= (mu x n.+1)/2 -> (d x y) <= ((mu x n.+1)).
        * move => y H0.
          have dt := (dst_trngl).
          specialize (dt M x y (r (phi k))).
          apply /Rle_trans.
          apply dt.
          by lra.
       have mod' : forall y, (d (r (phi k)) y) <= (mu x n.+1)/2 -> (d (f (r (phi k))) (f y)) <= (/2 ^ n).
    move => y closeness.
    have dt := dst_trngl.
    specialize (dt N (f (r (phi k))) (f y) (f x)).
    rewrite dst_sym in fxclose.
    apply /Rle_trans.
    apply dt.
    have fxyclose := (mu_modulus x y n.+1).
    have p0' := (fxyclose (p0 y closeness)).
    have rp := (Rplus_le_compat_l (d (f (r (phi k))) (f x)) (d (f x) (f y)) (/2 ^ (n.+1)) p0').
    have rp' := (Rplus_le_compat_r (/2 ^ (n.+1)) (d (f  (r (phi k))) (f x)) (/2 ^ (n.+1)) fxclose).
    apply /Rle_trans.
    apply rp.
    apply /Rle_trans.
    apply rp'.
    have tp := (tpmn_half n).
    by lra.
    have mu_lt : 0 < (mu x n.+1)/2 < 1.
    split.
    suff : 0 < (mu x n.+1) by lra.
    apply (mu_pos x (n.+1)).
    suff :(mu x n.+1)<2 by lra.
    apply /Rle_lt_trans.
    apply (mule1 x n.+1).
    by lra.
    have cont' := (mu_cont (r (phi k)) n ((mu x n.+1)/2) mu_lt mod').
    have triv : (mu x n.+1) / 2 / 2 = (mu x n.+1)/4.
    by field.
     rewrite triv in cont'.
     done.
    exists (st0f n.+1).+2.
    have triv : ((st0f n.+1) <= (st0f n.+1).+2)%nat.
    apply /leq_trans.
    have triv' : ((st0f n.+1) <= (st0f n.+1).+1)%nat.
    done.
    apply triv'.
    done.
    have triv' : forall k, (2 ^ k) <> 0.
    move => k.
    case.
    have very_trivial : (0 < 2).
    by lra.
    have p'' := (pow_lt 2 k very_trivial).
    move => H3.
    rewrite H3 in p''.
    by lra.
    have closeness' := (closeness (st0f n.+1).+2 triv).
    have P := (st0fprop n.+1). 
    have triv2 : (/2 ^ ((st0f n.+1).+2)) = (/2 ^ (st0f n.+1))/4.
    simpl.
    rewrite Rinv_mult_distr.
    rewrite Rinv_mult_distr.
    field.
    apply triv'.
    by lra.
    apply triv'.
    by lra.
    case.
    move => H3.
    have U := (Rmult_integral 2 (2 ^ (st0f n.+1)) H3).
    case U.
    by lra.
    by apply triv'.
    rewrite triv2.
    have P' : (/ 2 ^ st0f n.+1)/4 <= (mu x n.+1)/4.
    apply /Rle_div_l.
    by lra.
    apply /Rle_trans.
    apply P.
    have t : ((mu x n.+1)/4)*4 = (mu x n.+1).
    by field.
    rewrite t.
    have mu_pos' := (mu_pos x n.+1).
    by lra.
    apply /Rle_trans.
    apply P'.
    by apply closeness'.

      have st2 : forall x n, exists i, (d (f x) (q i)) <= (/2 ^ n).
      move => x n.
      have [ds _] := (dseq_tpmn q).
      specialize (ds qdense (f x) n).
      by apply ds.
      exists (make_mf (fun phi Fphi => forall n, exists k, (/2 ^ k) <= (mu (r (phi k)) n.+2) /\ (forall k', (/2 ^ k') <= (mu (r (phi k')) n.+2) ->(k <= k')%nat) /\ (d (q (Fphi n)) (f (r (phi k)))) <= (/2 ^ n.+1) /\ (forall m, (d (q m) (f (r (phi k)))) <= (/2 ^ n.+1) -> ((Fphi n) <= m)%nat))).
      split.
      apply rlzr_F2MF.
      move => phi x.
      split.
      simpl.
      have st' := (st x phi _ H0).
      have st_min : forall n, exists k, (/ 2 ^ k) <= (mu (r (phi k)) n) /\ forall k', (/ 2 ^ k') <= (mu (r (phi k')) n) -> (k <= k')%nat.
      move => n.
      by apply (classical_cont.well_order_nat (st' n)).     
      apply choice in st_min.
      have := st_min.
      case.
      move => stc stc_prop.
      have prop0 : forall n, exists m, (d (f (r (phi (stc n.+2)))) (q m)) <= (/2 ^ (n.+1)) /\ forall t, (d (f (r (phi (stc n.+2)))) (q t)) <= (/ 2 ^ (n.+1)) -> (m <= t)%nat.
      move => n.
      have P_exists : exists m, (d (f (r (phi (stc n.+2)))) (q m)) <= (/2 ^ (n.+1)).
      by apply (qdense (f (r (phi (stc n.+2)))) (tpmn_lt n.+1)).
      have := (classical_cont.well_order_nat P_exists).
      case.
      move => n0 n0_prop.
      exists n0.
      by apply n0_prop.
      apply choice in prop0.
      have := prop0.
      case.
      move => F F_prop.
      exists F.
      move => n.
      exists (stc n.+2).
      split.
      by apply stc_prop.
      have := (F_prop n).
      move => [Fp1 Fp2].
      rewrite dst_sym in Fp1.
      split.
      by apply stc_prop.
      split.
      apply /Rle_trans.
      apply Fp1.
      have triv : / (2 * 2^n) = (/ 2 ^ n.+1).
      done.
      rewrite triv.
      by apply /tpmnP.
      move => m.
      specialize (Fp2 m).
      rewrite dst_sym in Fp2.
      by apply Fp2.
      simpl.
      move => psi psi_prop n.
      specialize (psi_prop n).
      case psi_prop.
      move => k [prop1 [prop2' [prop2 prop2'']]].
      apply /Rle_trans.
      have dt := dst_trngl.
      specialize (dt N (f x) (q (psi n)) (f (r (phi k))) ).
      apply dt.
      rewrite dst_sym in prop2.
      have e0 : (d (f x) (f (r (phi k)))) <= (/2 ^ (n.+1)).
      have mmod := (mu_modulus (r (phi k)) x n.+2).
      specialize (H0 k).
      rewrite dst_sym in H0.
      have e1 : (d (r (phi k)) x) <= (mu (r (phi k)) n.+2).
      apply /Rle_trans.
      apply H0.
      by apply prop1.
      specialize (mmod e1).
      rewrite dst_sym in mmod.
      apply /Rle_trans.
      apply mmod.
      by apply /tpmnP.
      have Rp := (Rplus_le_compat (d (f x) (f (r (phi k)))) (/ 2 ^ n.+1) (d (f (r (phi k))) (q (psi n))) (/2 ^ n.+1) e0 prop2).
       apply /Rle_trans.
       apply Rp.
       have tp := (tpmn_half n).
       apply symmetry in tp.
       rewrite tp.
       by lra.
   rewrite /cont.continuous.
   simpl.
   move => phi Fphi.
   move => prop.
   apply choice in prop.
   have := prop.
   case.
   move => S S_prop.
   exists (fun n=>(init_seg (S n).+1)).
   move => n psi.
   move => coin.
   have := coin.
   simpl.
   move => [L1 L2] Fphi' H2.
   specialize (S_prop n).
   case (H2 n).
   move => k' [k'_prop1 [k'_prop2 [k'_prop3 k'_prop4]]].
   have keqk' : k' = (S n).
   have := S_prop.
   move => [S_prop1 [S_prop2 _]].
   rewrite L1 in S_prop1.
   have lt := (k'_prop2 (S n) S_prop1).
   have e0 : phi(k') = psi(k').
   have := (@coin_lstn nat nat phi psi (init_seg (S n).+1)).
   move => [cs _].
   specialize (cs coin k').
   have := (lstn_iseg (@id nat) k' (S n).+1).
   move => [_ lst].
   have w : (exists n0 : nat, (n0 < (S n).+1)%nat /\ n0 = k').
   by exists k'.
   specialize (lst w).
   specialize (cs lst).
   by apply cs.
   apply symmetry in e0.
   rewrite e0 in k'_prop1.
   have gt := (S_prop2 k' k'_prop1).
   have eq := (eqn_leq k' (S n)).
   rewrite gt in eq.
   rewrite lt in eq.
   simpl in eq.
   apply /eqP.
   by rewrite eq.
   have e0 : (f (r (psi k'))) = (f (r (phi (S n)))).
   rewrite keqk'.
   by rewrite L1.
   have lt := (k'_prop4 (Fphi n)).
   rewrite e0 in lt.
   have := S_prop.
   move => [_ [_ [S1 S4]]].
   specialize (lt S1).
   have gt := (S4 (Fphi' n)).
   apply symmetry in e0.
   rewrite e0 in gt.
   specialize (gt k'_prop3).
   have eq := (eqn_leq (Fphi' n) (Fphi n)).
   rewrite gt in eq.
   rewrite lt in eq.
   simpl in eq.
   apply /eqP.
   by rewrite eq.
Qed.
End continuity.