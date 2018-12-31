From mathcomp Require Import ssreflect seq ssrfun ssrbool ssrnat.
From rlzrs Require Import all_rlzrs.
Require Import all_cs reals.
Require Import Qreals Reals Psatz ClassicalChoice.
Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope R_scope.
Module MetricSpace.
  Record mixin_of (M: Type) :=
    Mixin {
        d : M -> M -> R;
        d_pos: forall x y: M, 0 <= d x y;
        d_sym: forall x y: M, d x y = d y x;
        dxx: forall x: M, d x x = 0;
        d_eq: forall x y: M, d x y = 0 -> x = y;
        d_trngl: forall x y z: M, d x y <= d x z + d z y;
        }.

  Section ClassDef.
    Notation class_of := mixin_of (only parsing).
  
    Structure type := Pack {sort; _ : class_of sort; _: Type}.

    Local Coercion sort: type >-> Sortclass.

    Definition class (cT: type) := let: Pack _ c _ := cT return class_of cT in c.
  End ClassDef.

  Module Exports.
    Coercion sort: type >-> Sortclass.
    Bind Scope metric_scope with sort.
    Notation MetricSpace := MetricSpace.type.
  End Exports.

End MetricSpace.

Export MetricSpace.Exports.

Delimit Scope metric_scope with met.
Local Open Scope metric_scope.

Coercion Base: Metric_Space >-> Sortclass.
Definition distance M := MetricSpace.d (MetricSpace.class M).
Arguments distance {M}.
Notation d := distance.
Notation subset := mf_subset.type.

Section MetricSpaces.
  Definition make_MetricSpace M (d: M -> M -> R)
             (d_pos: forall x y: M, 0 <= d x y)
             (d_sym: forall x y: M, d x y = d y x)
             (dxx: forall x: M, d x x = 0)
             (d_eq: forall x y: M, d x y = 0 -> x = y)
             (d_trngl: forall x y z: M, d x y <= d x z + d z y): MetricSpace.
  Proof.
    apply/MetricSpace.Pack/M.
    exists d.
    exact/d_pos.
    exact/d_sym.
    exact/dxx.
    exact/d_eq.
    exact/d_trngl.
  Defined.
  
  Context (M: MetricSpace).
  Implicit Types (x y z: M) (xn yn: nat -> M).

  Lemma dst_pos x y: 0 <= d x y.
  Proof. exact/MetricSpace.d_pos. Qed.

  Lemma dst_sym x y: d x y = d y x.
  Proof. exact/MetricSpace.d_sym. Qed.

  Lemma dst_eq x y: d x y = 0 -> x = y.
  Proof. exact/MetricSpace.d_eq. Qed.

  Lemma dst_trngl x y z: d x y <= d x z + d z y.
  Proof. exact/MetricSpace.d_trngl. Qed.
  Arguments dst_trngl {x} {y}.
  
  Lemma dstxx x: d x x = 0.
  Proof. exact/MetricSpace.dxx. Qed.
    
  Lemma dst_le x y z r r' q: d x z <= r -> d z y <= r' -> r + r' <= q -> d x y <= q.
  Proof.
    move => ineq ienq' add.
    by apply/Rle_trans/add/Rle_trans/Rplus_le_compat; first exact/dst_trngl.
  Qed.

  Lemma dst_lt x y z r r' q: d x z <= r -> d z y <= r' -> r + r' < q -> d x y < q.
  Proof.
    move => ineq ienq' add.
    by apply/Rle_lt_trans/add/Rle_trans/Rplus_le_compat; first exact/dst_trngl.
  Qed.
 
  Definition metric_limit := make_mf (fun xn x =>
    forall eps, 0 < eps -> exists N, forall m,
          (N <= m)%nat -> d x (xn m) <= eps).

  Notation limit := metric_limit.
  
  Global Instance lim_prpr:
    Proper (@eqfun M nat ==> @set_equiv M) metric_limit.
  Proof.
    move => xn yn eq x.
    split => lim eps eg0; have [N prp]:= lim eps eg0; exists N => m.
    - by rewrite -(eq m); apply/prp.
    by rewrite (eq m); apply/prp.
  Qed.
    
  Lemma lim_sing: limit \is_singlevalued.
  Proof.
    move => xn x x' limxnx limxnx'.
    apply/dst_eq/cond_eq => eps epsg0.
    rewrite Rminus_0_r Rabs_pos_eq; last exact/dst_pos.
    have [ | N Nprp]:= limxnx (eps/3); try lra.
    have [ | N' N'prp]:= limxnx' (eps/3); try lra.
    pose k:= maxn N N'.
    apply/dst_lt; first exact/Nprp/leq_maxl/N'.
    - rewrite dst_sym; apply/N'prp/leq_maxr.
    lra.
  Qed.

  Lemma lim_cnst x: limit (cnst x) x.
  Proof.
    exists 0%nat; rewrite/cnst dstxx; intros.
    lra.
  Qed.
  
  Lemma lim_tpmn xn x: metric_limit xn x <->
    (forall n, exists N, forall m, (N <= m)%nat -> d x (xn m) <= /2 ^ n).
  Proof.
  split => [lim n | lim eps eg0].
  - have [ | N prp]:= lim (/2 ^ n); first by apply/Rinv_0_lt_compat/pow_lt; lra.
    by exists N.
  have [n ineq]:= accf_2pown eg0.
  have [N prp]:= lim n.
  exists N => m Nlm.
  exact/Rlt_le/Rle_lt_trans/ineq.2/prp.
  Qed.
  
  Lemma cond_eq_tpmn x y:
    (forall n, d x y <= / 2 ^ n) -> x = y.
  Proof.
    move => prp; apply/dst_eq; symmetry.
    apply/cond_eq_f => [ | n ineq]; first exact/accf_2pown.
    rewrite /R_dist Rminus_0_l Rabs_Ropp Rabs_pos_eq; first exact/prp.
    exact/dst_pos.
  Qed.
           
  Definition dense_subset (A: subset M):=
    forall x eps, eps > 0 -> exists y, y \from A /\ d x y <= eps.

  Global Instance dns_prpr: Proper (@set_equiv M ==> iff) dense_subset.
  Proof.
    move => A B eq; split => dns x eps eg0; have [y []]:= dns x eps eg0; exists y.
    - by rewrite -eq.
    by rewrite eq.
  Qed.
    
  Lemma dense_tpmn (A: subset M):
    dense_subset A <-> forall x n, exists y, y \from A /\ d x y <= /2^n.
  Proof.
    split => [dns x n | dns x eps eg0]; first by apply/dns/Rlt_gt/Rinv_0_lt_compat/pow_lt; lra.
    have [n ineq]:= accf_2pown eg0.
    have [y []]:= dns x n.
    exists y; split => //.
    exact/Rlt_le/Rle_lt_trans/ineq.2.
  Qed.

  Definition dense_sequence (r: nat -> M) :=
    forall x eps, 0 < eps -> exists n, d x (r n) <= eps.

  Lemma dseq_dns (r: nat -> M):
    dense_sequence r <-> dense_subset (codom (F2MF r)). 
  Proof.
    split => dns x eps eg0; have []:= dns x eps eg0.
    - by move => n ineq; exists (r n); split => //; exists n.
    by move => y [[n <-] ineq]; exists n.
  Qed.

  Lemma dseq_tpmn (r: nat -> M):
    dense_sequence r <-> forall x n, exists m, d x (r m) <= /2^n.
  Proof.
    split => [dns x n| dns x eps eg0]; first apply/dns.
    - by apply/Rinv_0_lt_compat/pow_lt; lra.
    have [n ineq]:= accf_2pown eg0.
    have [m prp]:= dns x n.
    exists m.
    exact/Rlt_le/Rle_lt_trans/ineq.2/prp.
  Qed.  
End MetricSpaces.
Arguments metric_limit {M}.
Arguments dst_trngl {M} {x} {y}.
Notation limit := metric_limit.

Section Cauchy_sequences.
  Context (M: MetricSpace).
  Implicit Types (x y z: M) (xn yn: nat -> M).
  
  Definition Cauchy_sequence := make_subset (fun xn =>
    forall eps, 0 < eps -> exists N, forall n m,
          (N <= n)%nat -> (N <= m)%nat -> d (xn n) (xn m) <= eps).
  
  Lemma lim_cchy: dom metric_limit \is_subset_of Cauchy_sequence.
  Proof.
    move => xn [x lim] eps eg0.
    have [ | N prp]:= lim (eps/2); first by lra.
    exists N => n m ineq ineq'.
    apply/dst_le;first by rewrite dst_sym; apply/prp.
    - exact/prp.
    lra.
  Qed.
  
  Definition complete := Cauchy_sequence \is_subset_of dom metric_limit.
  
  Definition fast_Cauchy_sequence := make_subset (fun (xn: nat -> M) =>
    forall n m, d (xn n) (xn m) <= /2^n + /2^m).

  Lemma tpmn_half n: / 2 ^ n = / 2 ^ n.+1 + / 2 ^ n.+1.
  Proof. by have pos:= pow_lt 2 n; rewrite /= Rinv_mult_distr; lra. Qed.
  
  Lemma fchy_cchy: fast_Cauchy_sequence \is_subset_of Cauchy_sequence.
  Proof.
    move => xn cchy eps epsg0.
    have [N [_ ineq]]:= accf_2pown epsg0.
    exists N.+1 => n m nineq mineq.
    apply/Rlt_le/Rle_lt_trans; last exact/ineq.
    apply /Rle_trans; [exact/cchy | rewrite (tpmn_half N)].
    by apply/Rplus_le_compat; apply/Rinv_le_contravar;
      try apply/pow_lt; try apply/Rle_pow/leP => //; try lra.
  Qed.
    
  Lemma cchy_tpmn xn: Cauchy_sequence xn <->
    (forall k, exists N, forall n m,
            (N <= n <= m)%nat -> d (xn n) (xn m) <= /2^k).
  Proof.
    split => [cchy k | ass eps epsg0].
    - have [ | N prp]:= cchy (/2 ^ k).
      + by apply/Rinv_0_lt_compat/pow_lt; lra.
      exists N => n m /andP [ineq ineq'].
      exact/prp/leq_trans/ineq'.
    have [N [g0 /Rlt_le ineq]]:= accf_2pown epsg0.
    have [N' N'prp]:= ass N.
    exists N' => n m nineq mineq.
    case/orP: (leq_total n m) => ineq'.
    - by apply/Rle_trans; first exact/N'prp/andP.
    by rewrite dst_sym; apply/Rle_trans; first apply/N'prp/andP.
  Qed.

  Definition eventually_big mu:= forall (n: nat), exists N, forall m,
          (N <= m)%nat -> (n <= mu m)%nat.

  Lemma lim_evb xn mu (x: M): limit xn x -> eventually_big mu -> limit (xn \o_f mu) x.
  Proof.
    move => lim evb eps eg0.
    have [N prp]:= lim eps eg0.
    have [N' ineq]:= evb N.
    exists N' => m ineq'.
    exact/prp/ineq/ineq'. 
  Qed.
  
  Lemma cchy_evb xn mu: Cauchy_sequence xn -> eventually_big mu -> Cauchy_sequence (xn \o_f mu).
  Proof.
    move => cchy evb eps eg0.
    have [N prp]:= cchy eps eg0.
    have [N' le]:= evb N.
    exists N' => n m ineq ineq'; apply/prp/le; last exact/ineq'.
    exact/le/ineq.
  Qed.

  Lemma cchy_fchy xn:
    Cauchy_sequence xn -> exists mu, fast_Cauchy_sequence (xn \o_f mu).
  Proof.
    move => /cchy_tpmn cchy.    
    have /choice[mu prp]:= cchy.
    exists mu => n m /=.
    case/orP: (leq_total (mu n) (mu m)) => ineq.
    - apply/Rle_trans; first by apply/prp/andP.
      rewrite -[X in X <= _]Rplus_0_r; apply/Rplus_le_compat_l.
      by apply/Rlt_le/Rinv_0_lt_compat/pow_lt; lra.
    rewrite dst_sym; apply/Rle_trans; first by apply/prp/andP.
    rewrite -[X in X <= _]Rplus_0_l; apply/Rplus_le_compat_r.
    by apply/Rlt_le/Rinv_0_lt_compat/pow_lt; lra.
  Qed.

  Definition efficient_limit := make_mf (fun xn (x: M) =>
    forall n, d x (xn n) <= /2^n).

  Lemma lim_eff_spec: efficient_limit =~= metric_limit|_(fast_Cauchy_sequence).
  Proof.
    move => xn x; split => [lim | [fchy lim] n].
    - split => [n m | eps epsg0].
      apply/dst_le/Rle_refl/lim; first by rewrite dst_sym; apply/lim.
      have [n ineq]:= accf_2pown epsg0.
      exists n => m nlm.
      apply/Rlt_le/Rle_lt_trans/ineq.2/Rle_trans; first exact/lim.
      apply/Rinv_le_contravar; first by apply/pow_lt; lra.
      by apply/Rle_pow/leP => //; lra.
    suff all: forall m, d x (xn n) <= / 2 ^ n + / 2 ^ m.
    - suff: d x (xn n) - / 2 ^ n <= 0 by lra.
      apply/Rnot_lt_le => ineq.
      have [m ineq']:= accf_2pown ineq.
      by have := all m; lra.
    move => m.  
    have [ | N prp]:= lim (/2 ^ m.+1); first by apply/Rinv_0_lt_compat/pow_lt; lra.
    rewrite (tpmn_half m) -Rplus_assoc Rplus_comm.
    apply/Rle_trans/Rplus_le_compat.
    - + by apply/(dst_trngl (xn (maxn m.+1 N))).
    - exact/prp/leq_maxr.
    rewrite dst_sym; apply/Rle_trans; first exact/fchy.
    apply/Rplus_le_compat_l/Rinv_le_contravar/Rle_pow/leP/leq_maxl; try lra.
    by apply/pow_lt; lra.
  Qed.
    
  Lemma lim_eff_lim : metric_limit \extends efficient_limit.
  Proof.
    rewrite lim_eff_spec {2}[metric_limit]restr_all.
    exact/exte_restr/subs_all.
  Qed.

  Lemma fchy_lim_eff: complete ->
    fast_Cauchy_sequence === dom efficient_limit.
  Proof.
    move => cmplt xn; split => [cchy | [x /lim_eff_spec []]]//.
    rewrite lim_eff_spec dom_restr_spec; split => //.
    exact/cmplt/fchy_cchy.
  Qed.  

  Lemma lim_tight_lim_eff: metric_limit \tightens efficient_limit.
  Proof.
    apply sing_exte_tight; [exact/lim_sing | exact/lim_eff_lim].
  Qed.

  Lemma lim_eff_sing: efficient_limit \is_singlevalued.
  Proof.
    by apply /exte_sing; first apply/ lim_eff_lim; last apply/lim_sing.
  Qed.

  Lemma cchy_eff_suff xn:
    (forall n m, (n <= m)%nat -> d (xn n) (xn m) <= /2^n + /2^m) ->
    fast_Cauchy_sequence xn.
  Proof.
    move => ass n m.
    case /orP: (leq_total n m) => ineq; first by apply ass.
    by rewrite dst_sym Rplus_comm; apply ass.
  Qed.
End Cauchy_sequences.
Definition Cauchy_sequences := Cauchy_sequence.
Arguments Cauchy_sequence {M}.
Definition fast_Cauchy_sequences := fast_Cauchy_sequence.
Arguments fast_Cauchy_sequence {M}.
Arguments efficient_limit {M}.

Section continuity.
  Definition continuity_point (M N: MetricSpace) (f: M -> N) x :=
    forall eps, 0 < eps -> exists delta, 0 < delta /\ forall y, d x y <= delta -> d (f x) (f y) <= eps.

  Definition continuity_points (M N: MetricSpace) (f: M -> N) :=
    make_subset (fun x => continuity_point f x).

  Definition continuous (M N: MetricSpace) (f: M -> N):=
    forall x, continuity_point f x.

  Definition sequential_continuity_point (M N: MetricSpace) (f: M -> N) x:=
    forall xn, metric_limit xn x -> metric_limit (ptw f xn) (f x).

  Definition sequentially_continuous (M N: MetricSpace) (f: M -> N):=
    forall x, sequential_continuity_point f x.
  
  Lemma cntp_scntp (M N: MetricSpace) (f: M -> N) x:
    continuity_point f x -> sequential_continuity_point f x.
  Proof.
    move => cont xn lmt eps eg0.
    have [delta [dg0 prp]]:= cont eps eg0.
    have [N' cnd]:= lmt delta dg0.
    exists N' => m ineq.
    exact/prp/cnd.
  Qed.

  Lemma cont_scnt (M N: MetricSpace) (f: M -> N): continuous f -> sequentially_continuous f.
  Proof. by move => cont x; apply/cntp_scntp. Qed.

  Require Import ChoiceFacts.
  Lemma scnt_cont (M N: MetricSpace) (f: M -> N):
    FunctionalCountableChoice_on M -> sequentially_continuous f -> continuous f.
  Proof.
    move => choice scnt x eps eg0.
    apply/not_all_not_ex => prp.
    have /choice [xn xnprp]: forall n, exists y, d x y <= /2^n /\ eps < d (f x) (f y).
    - move => n; have /not_and_or [ | cnd]:= (prp (/2 ^ n)).
      + by have : 0 < /2^n by apply/Rinv_0_lt_compat/pow_lt; lra.
      apply/not_all_not_ex => asd.
      apply/cnd => y dst.
      have /not_and_or [ineq | ineq]:= asd y; last exact/Rnot_lt_le.
      lra.
    have lmt: limit xn x.
    - rewrite lim_tpmn => n.
      exists n => m ineq; have [le _]:= xnprp m.
      apply/Rle_trans; first exact/le.
      apply/Rinv_le_contravar/Rle_pow; try lra; first by apply/pow_lt; lra.
      exact/leP.
    have [K cnd]:= scnt x xn lmt eps eg0.
    have []:= xnprp K.
    suff: d (f x ) (f (xn K)) <= eps by lra.
    exact/cnd.
  Qed.
End continuity.