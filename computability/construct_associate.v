From mathcomp Require Import ssreflect ssrfun seq ssrnat ssrbool eqtype fintype.
From mf Require Import all_mf classical_mf.
From metric Require Import pointwise.
Require Import all_cont search PhiN FMop Umach classical_mach seq_cont graphs.
Require Import axioms Classical ChoiceFacts Psatz Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma subs_unionl T (P P': subset T): P \is_subset_of P \u P'.
Proof. by left. Qed.

Lemma subs_unionr T (P P': subset T): P \is_subset_of P' \u P.
Proof. by right. Qed.

Lemma maxnS n m: maxn n m.+1 = (maxn n.-1 m).+1.
Proof. by case: n => [ | n]; [rewrite !max0n | rewrite maxnSS]. Qed.

Lemma maxSn n m: maxn n.+1 m = (maxn n m.-1).+1.
Proof. by case: m => [ | m]; [rewrite !maxn0 | rewrite maxnSS]. Qed.

Section construct_associate.
  Local Open Scope name_scope.
  Context (Q: eqType) (Q' A A': Type) (somea: A) (someq: Q).
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Context (mu: B -> nat * Q' -> seq Q).
  Hypothesis modmod: mu \modulus_function_for mu.
  Implicit Types (KL: seq (Q * A)).
  
  Notation GL2F KL := (LF2F somea (GL2LF KL)).
  Notation trunc phi K := (trunc somea phi K).
    
  Lemma trunc_spec phi (K: seq Q): trunc phi K = GL2F (F2GL phi K).
  Proof. by apply/fun_ext => q; apply/trunc_val_spec. Qed.
  
  Context (M: B -> nat * Q' -> option A').
  Hypothesis (mod: mu \modulus_function_for M).
  
  Fixpoint psi_FM_rec k l (KLq': seq (Q * A) * Q') :=
    match k with
    | 0 => inr [:: someq]
    | S k' => let (KL, q') := KLq' in
             let K := mu (GL2F KL) (l - k', q') in
             if check_sublist K (unzip1 KL)
             then match M (GL2F KL) (l - k', q') with
                  | Some a' => inl a'
                  | None => psi_FM_rec k' l KLq'
                  end
             else inr (filter (fun q => ~~ (q \in unzip1 KL)) K)
    end.    
    
  Definition psi_FM KLq' := psi_FM_rec (size KLq'.1).+1 (size KLq'.1) KLq'.      

  Lemma psi_FM_dsrch KL q':
    psi_FM (KL, q') =
    if direct_search
         (fun k => (mu (GL2F KL) (k, q'), M (GL2F KL) (k, q')))
         (fun Koa' => ~~ check_sublist Koa'.1 (unzip1 KL) || isSome Koa'.2)
         (size KL)
         is Some (K, oa')
    then if ~~ check_sublist K (unzip1 KL)
         then inr (filter (fun q => ~~ (q \in unzip1 KL)) K)
         else if oa' is Some a' then inl a' else inr [:: someq]
    else inr [:: someq].
  Proof.
    rewrite /psi_FM /direct_search.
    move: {2 3}(size KL) => l; move: l.
    elim: (size KL) => [l | k ih l /=].
    - by rewrite /= subSS subn0; case: ifP => [subl |/= -> /=]//; case eq: M => //=; rewrite subl.
    move: (ih (l)) => /=.
    rewrite !subSS.
    case: ifP => subl /=.
    - case eq: M; last by case: ifP => subl' /=; first case eq'': M => //; rewrite /= subl'.
      rewrite /= subl /=; case: ifP => subl' /=; last by rewrite subl'.
      by case eq': M; [rewrite /= subl' | rewrite /= subl].
    rewrite subl /=; case: ifP => /= subl'; last by rewrite subl'.
    by case eq': M => //=; [rewrite subl' | rewrite subl].
  Qed.

  Lemma psi_FM_osrch_or KL q':
    psi_FM (KL, q') =
    let l := ord_search
               (fun k => ~~ check_sublist (mu (GL2F KL) (k, q')) (unzip1 KL)
                      ||
                      M (GL2F KL) (k, q')) (size KL) in
    if ~~ check_sublist (mu (GL2F KL) (l, q')) (unzip1 KL)
    then inr (filter (fun q => ~~ (q \in unzip1 KL)) (mu (GL2F KL) (l, q')))
    else if M (GL2F KL) (l, q') is Some a'
         then inl a'
         else inr [::someq].
  Proof.
    rewrite psi_FM_dsrch dsrch_osrch //=.
    case: ifP => // or.
    case: ifP => //subl; first by have : false by rewrite -or; apply/orP; left.
    by case Mval: M => [a' | ]//; have: false by rewrite -or; apply/orP; right; rewrite Mval.
  Qed.

  Lemma psi_FM_osrch_min KL q':
    psi_FM (KL, q') =
    let l :=
        minn (ord_search (fun k => M (GL2F KL) (k, q')) (size KL))
             (ord_search (fun k => ~~ check_sublist (mu (GL2F KL) (k, q')) (unzip1 KL)) (size KL))
    in
    if ~~ check_sublist (mu (GL2F KL) (l, q')) (unzip1 KL)
    then inr (filter (fun q => ~~ (q \in unzip1 KL)) (mu (GL2F KL) (l, q')))
    else if M (GL2F KL) (l, q') is Some a'
         then inl a'
         else inr [::someq].
  Proof.                             
    rewrite minnC.
    have <-:= osrch_or (fun k => ~~ check_sublist (mu (GL2F KL) (k, q')) (unzip1 KL))
     (fun k => M (GL2F KL) (k, q')) (size KL).
    exact/psi_FM_osrch_or.
  Qed.

  Lemma psi_FM_osrch KL q':
    let k := ord_search (fun k => ~~ check_sublist (mu (GL2F KL) (k, q')) (unzip1 KL)) (size KL) in
    let m := ord_search (fun m => M (GL2F KL) (m, q')) (size KL) in
    psi_FM (KL, q') =
    if m < k
    then if M (GL2F KL) (m, q') is Some a' then inl a' else inr [:: someq]
    else if ~~ check_sublist (mu (GL2F KL) (k, q')) (unzip1 KL)
         then inr [seq q <- mu (GL2F KL) (k, q') | q \notin unzip1 KL]
         else if M (GL2F KL) (size KL, q') is Some a' then inl a' else inr [::someq].
  Proof.
    move => k m; rewrite psi_FM_osrch_min -/k -/m /minn; case ineq: (m < k).
    - suff /clP ->: (mu (GL2F KL) (m, q')) \is_sublist_of (unzip1 KL) by trivial.
      apply/clP/negP => /negP pm; move: ineq.
      by rewrite ltnNge => /negP fls; apply/fls/osrch_min.
    case: ifP => // cl; suff ->: k = size KL by trivial.
    apply/eqP; rewrite eqn_leq; apply/andP; split; first exact/osrch_le.
    rewrite leqNgt; apply/negP => /osrch_ltP [[/=l lt] pl].
    suff: false  by trivial.
    rewrite -cl.
    apply/(@osrch_correct_le (fun k => ~~ check_sublist (mu (GL2F KL) (k, q')) (unzip1 KL))).
    - exact/pl.
    by apply/leq_trans/lt.
  Qed.

  Lemma psi_FM_nsrch KL q':
    let k := nat_search (fun k => ~~ check_sublist (mu (GL2F KL) (k, q')) (unzip1 KL)) (size KL) in
    let m := nat_search (fun m => M (GL2F KL) (m, q')) (size KL) in
    psi_FM (KL, q') =
    if m < k
    then if M (GL2F KL) (m, q') is Some a' then inl a' else inr [:: someq]
    else if k <= size KL
         then inr [seq q <- mu (GL2F KL) (k, q') | q \notin unzip1 KL]
         else inr [::someq].
  Proof.
    have on: forall p n, nat_search p n = ord_search p n.+1 by trivial.
    rewrite !on !osrchS.
    case: ifP => [ cl k| fls].
    - case: ifP => [mval m|].
      + rewrite psi_FM_osrch -/k -/m; case: ifP => // fls.
        have -> //: k <= size KL by apply/osrch_le.
        by rewrite cl.
      rewrite psi_FM_osrch -/k.
      set m := ord_search (fun m => M (GL2F KL) (m, q')) (size KL).
      rewrite /= => fls.
      have ->: m = size KL.
      + apply/eqP/osrch_eqP; case => [[/=m' lt] pm'].
        suff: false by trivial.
        rewrite -fls; apply/(@osrch_correct_le (fun m => M (GL2F KL) (m, q'))); first exact/pm'.
        by apply/leq_trans/lt.
      have ->: size KL < k = false by rewrite ltnNge; apply /negP/negP/osrch_le.
      rewrite cl.
      have ->: (size KL).+1 < k = false.
      + by rewrite ltnNge; apply/negP/negP/leq_trans; first exact/osrch_le.
      by have ->//: k <= size KL by apply/osrch_le.
    set k := ord_search (fun k => ~~ check_sublist (mu (GL2F KL) (k, q')) (unzip1 KL)) (size KL).
    have eq: k = size KL.
    + apply/eqP/osrch_eqP; case => [[k' lt] pk'].
      suff: false; [done | rewrite -fls].
      apply/(@osrch_correct_le (fun k => ~~ check_sublist (mu (GL2F KL) (k, q')) (unzip1 KL))).
      * exact/pk'.
      by apply/leq_trans/lt.
    case: ifP => [mval sze m | fls'].
    - rewrite /sze psi_FM_osrch -/m fls.
      have ->: m < (size KL) .+1 by have: m <= size KL by apply/osrch_le.
      case: ifP => // ineq; have -> //: m = size KL.
      apply/eqP; rewrite eqn_leq; apply/andP; split; first exact/osrch_le.
      by rewrite leqNgt -eq ineq.
    rewrite /= !ltnn psi_FM_osrch /= -/k fls eq.
    set m := ord_search (fun m => M (GL2F KL) (m, q')) (size KL).
    have:= fls'; rewrite -/m.
    suff ->: m = size KL.
    rewrite !ltnn //; case: M => //.
    apply/eqP; rewrite eqn_leq; apply/andP; split; first exact/osrch_le.
    rewrite leqNgt; apply/negP => /osrch_ltP [[/=m' lt] pm'].
    suff: false by trivial.
    rewrite -fls'.
    apply/(@osrch_correct_le (fun m => M (GL2F KL) (m, q'))); first exact/pm'.
    by apply/leq_trans/lt.
  Qed.
    
  Lemma psi_FM_rec_not_nil k l KL q' K: psi_FM_rec k l (KL,q') = inr K -> K <> nil.
  Proof.
    elim: k => [[<-] | k ih] //=.
    case: ifP => // /clP subl; first by case: M.
    case => <- /= eq; apply/subl; move: eq.
    elim: (mu (GL2F KL) (l - k, q')) => [_ q | ]// q K' ih' /=.
    by case: ifP => // /inP lstn /ih' subl' p /= [<- | ] // lstn'; apply/subl'.
  Qed.

  Lemma psi_FM_not_nil KL q' K: psi_FM (KL, q') = inr K -> K <> nil.
  Proof. exact/psi_FM_rec_not_nil. Qed.

  Lemma psi_FM_size_gs_gq phi n q':
    size (gather_shapes psi_FM phi  q' n) <= size (gather_queries psi_FM phi (n, q')).
  Proof.
    rewrite /gather_queries; elim: n => //= n ih.
    case E: psi_FM => [ | K] //=.
    rewrite size_cat; apply/leq_trans/(@leq_add 1)/ih => //.
    by case: (K) (psi_FM_not_nil E). 
  Qed.

  Lemma psi_FM_gq_size phi q' n m:
    n <= m -> size (gather_queries psi_FM phi (n, q')) <= size (gather_queries psi_FM phi (m, q')).
  Proof.
    move => /subnK <-.
    elim: (m - n) => // k ih.
    rewrite addSn /gather_queries /=.
    case E: psi_FM => [ | K] //=.
    rewrite size_cat.
    apply/leq_trans/(@leq_add 1)/ih => //.
    by case: (K) (psi_FM_not_nil E). 
  Qed.
  
  Lemma psi_FM_inr_M KL q':
    (forall t', t' <= size KL -> M (GL2F KL) (t', q') = None) -> ~~ psi_FM (KL, q').
  Proof.
    move => min; rewrite psi_FM_dsrch.        
    case ds: direct_search => [Koa' | ] //.
    move: Koa' ds; case => [K oa'] ds.
    have [l' [ineq [eq1 eq2]]]:= dsrch_le ds.
    move: eq1 eq2 ds => -> -> ds.
    by case: ifP => // subl; rewrite min.
  Qed.

  Lemma psi_FM_val_spec KL q' a':
    psi_FM (KL, q') = inl a'
    <->
    exists t, t <= size KL /\ use_first M (GL2F KL) (t, q') = Some a' /\
         forall t', t' <= t -> (mu (GL2F KL) (t', q')) \is_sublist_of (unzip1 KL).
  Proof.
    split => [ | [t [ineq [val subl]]]]; rewrite psi_FM_dsrch.
    - case ds: direct_search => [Koa' | ] //.
      move: Koa' ds; case => [K oa'] ds.
      have [l' [ineq [eq1 eq2]]]:= dsrch_le ds.
      move: eq1 eq2 ds => -> ->.    
      rewrite dsrch_osrch [X in X -> _]/=.
      case: ifP => // /orP [/clP subl | _] [<- <-].
      - by case: ifP => // /clP subl'; exfalso; apply/subl.
      case: ifP => // /clP subl.
      case eq: M => [b' | ] //; case => <-.
      exists (ord_search (fun k => ~~ check_sublist (mu (GL2F KL) (k, q')) (unzip1 KL)
                       || M (GL2F KL) (k, q')) (size KL)); split.
      - exact/osrch_le.
      split => [ | t'].
      - rewrite sfrst_osrch -eq; do 2 f_equal.
        apply/eqP/osrch_eqP; case => [[/=m mineq] val].
        move: mineq; rewrite ltnNge => /negP fls; apply/fls.
        by apply/osrch_min/orP; right.
      rewrite leq_eqVlt ltnNge => /orP [/eqP ->| ] // /negP fls.
      by apply/clP /negP => /negP cl; apply/fls/osrch_min/orP; left.
    rewrite (dsrch_val (ord_search (fun k => M (GL2F KL) (k, q')) t)) //=.
    - case: ifP => [/clP fls | _]; first by exfalso; apply/fls/subl/osrch_le.
      by rewrite -sfrst_osrch val.
    - by have := leq_trans (osrch_le (fun k => M (GL2F KL) (k, q')) t) ineq.
    - by apply/orP; right; rewrite -sfrst_osrch val.
    move => k /orP [/clP fls | val']; last exact/osrch_min.
    case lt: (t <= k).
    - have le: t <= k by rewrite lt.
      exact/leq_trans/le/osrch_le.
    exfalso; apply/fls/subl.
    suff klt: k < t by apply/leq_trans/klt.
    by rewrite ltnNge lt.
  Qed.

  Lemma psi_FM_val KL q' a':
    psi_FM (KL, q') = inl a' -> use_first M (GL2F KL) (size KL, q') = Some a'.
  Proof.
    by have/mon_spec mon:=sfrst_mon (M:= M)=> /psi_FM_val_spec [t [? [/mon eq ?]]]; apply/eq.
  Qed.

  Lemma psi_FM_size_gq phi q' k time: time \from cost M phi ->
    k <= time q' -> k <= size (gather_queries psi_FM phi (k, q')). 
  Proof.
    move => /cost_spec prp.
    move: prp (prp q') => _ [_].
    elim: k => // k ih min ineq.
    rewrite /gather_queries /=.
    case eq: psi_FM => [a' | K]; last first.
    - rewrite size_cat -addn1 addnC.
      apply/leq_add/ih/leq_trans/ineq => //.
      by have := psi_FM_not_nil eq; case: (K).
    move: eq => /psi_FM_val_spec [t []].
    rewrite size_F2GL -trunc_spec unzip1_F2GL => sze [val prp].
    apply/leq_trans; first exact/ineq.
    apply/leq_trans/(osrch_le (fun n => M (trunc phi (gather_queries psi_FM phi (k, q'))) (n, q'))).
    apply/min; have:= val; rewrite sfrst_osrch.
    rewrite (@mod _ _ phi); last exact/coin_subl/trunc_coin/prp/osrch_le.
    rewrite (@osrch_eq _ _ (size (gather_queries psi_FM phi (k, q')))) => [-> | |] //.
    by rewrite -sfrst_osrch val//.
  Qed.

  Lemma psi_FM_noval KL K t q':
    M (GL2F KL) (t, q') -> t <= size KL -> psi_FM (KL, q') = inr K ->
    let l := nat_search (fun n => ~~ check_sublist (mu (GL2F KL) (n, q')) (unzip1 KL)) (size KL) in
    K = filter (fun q => ~~ (q \in unzip1 KL)) (mu (GL2F KL) (l, q')).
  Proof.
    move => mval ineq eq l.
    move: eq; rewrite psi_FM_nsrch -/l.
    set m:= nat_search (fun m => M (GL2F KL) (m, q')) (size KL).
    case: ifP => [lt | leq].
    - case eq: M => //.
      suff: @None A' by trivial.
      rewrite -eq.
      apply/(@nsrch_correct_le (fun m => M (GL2F KL) (m, q'))); first exact/mval.
      by apply/leq_trans; first exact/ineq.
    suff -> : l <= size KL by case => <-.
    move: leq; rewrite ltnNge => /negP/negP leq.
    apply/leq_trans; first exact/leq.
    suff: m < (size KL).+1 by trivial.
    by apply/nsrch_leP; exists t.
  Qed.

  Lemma psi_FM_noval_phi KL K t q' phi: phi \coincides_with (GL2F KL) \on (unzip1 KL) ->
    M phi (t, q') -> t <= size KL -> psi_FM (KL, q') = inr K ->
    let l := nat_search (fun n => ~~ check_sublist (mu (GL2F KL) (n, q')) (unzip1 KL)) (size KL) in
    K = filter (fun q => ~~ (q \in unzip1 KL)) (mu (GL2F KL) (l, q')).
  Proof.
    move => coin mval ineq eq l.
    move: eq; rewrite psi_FM_nsrch -/l.
    set m:= nat_search (fun m => M (GL2F KL) (m, q')) (size KL).
    case: ifP => [lt | /negP leq].
    - case eq: M => //.
      have subl: (mu (GL2F KL) (m, q')) \is_sublist_of (unzip1 KL).
      + by apply/clP/negP => /negP cl; move: lt; rewrite ltnNge => /negP fls; apply/fls/nsrch_min.
      suff: @None A' by trivial.
      rewrite -eq.
      have/nsrch_leP [m' [m'sze pm']]:
        m <= size KL by have: m < (size KL).+1 by apply/leq_trans/nsrch_le; first exact/lt.
      exact/(@nsrch_correct_le (fun m => M (GL2F KL) (m, q')))/m'sze.      
    case: ifP => [_ [<-] | /negP le]//.
    exfalso; apply/le/leq_trans/ineq/nsrch_min/clP => subl.
    suff leq': m <= size KL by apply/le/leq_trans/leq'; rewrite leqNgt; apply/negP.
    apply/nsrch_leP; exists t; split => //.
    rewrite (@mod _ _ phi) //.
    exact/coin_sym/coin_subl/coin.
  Qed.


  Lemma psi_FM_noval_phi' KL K t q' phi:
    phi \coincides_with (GL2F KL) \on (unzip1 KL) ->
    M phi (t, q') -> t <= size KL -> psi_FM (KL, q') = inr K ->
    let l := ord_search
               (fun n => ~~ check_sublist (mu (GL2F KL) (n, q')) (unzip1 KL) || M (GL2F KL) (n, q'))
               (size KL) in
    K = filter (fun q => ~~ (q \in unzip1 KL)) (mu (GL2F KL) (l, q'))
                           /\ forall t', t' < l -> mu (GL2F KL) (t', q') \is_subset_of unzip1 KL.
  Proof.
    move => coin Mval ineq.
    rewrite psi_FM_dsrch dsrch_osrch /=.
    case: ifP => [/orP [-> [<-] | mvl] |].
    - split => // t'; rewrite ltnNge => /negP fls; apply/clP/negP => prp.
      by apply/fls/osrch_min/orP; left; apply/negP.
    - case: ifP => [/clP fls [<-] | /clP subl].
      split => // t'; rewrite ltnNge => /negP fls'; apply/clP/negP => prp.
      by apply/fls'/osrch_min/orP; left; apply/negP.
    - by case eq: M mvl.
    move => fls [<-].
    suff: false by trivial.
    rewrite -fls.
    apply/(@osrch_correct_le (fun k => ~~ check_sublist (mu (GL2F KL) (k, q')) (unzip1 KL)
                                    ||
                                    M (GL2F KL) (k, q')) t (size KL)) => //.
    apply/orP.
    case cl: (check_sublist (mu (GL2F KL) (t, q')) (unzip1 KL)); last by left.
    right.
    move: cl => /clP subl.
    rewrite (@mod _ _ phi) //.
    exact/coin_subl/coin_sym/coin.
  Qed.

  Hypothesis choice: forall A, FunctionalChoice_on Q A.
  Lemma psi_FM_exte: \F_(U psi_FM) \extends \F_(use_first M).
  Proof.
    move => phi Fphi val q'.
    have [_ [| time tprp]]:= cost_dom M phi; first by apply/sfrst_dom; exists Fphi.
    have [k val']:= val q'; have := val'.
    rewrite sfrst_osrch -osrch_osrch -(@cost_val _ _ _ _ _ _ _ _ time) // =>[tval|]; last first.
    - by rewrite -sfrst_osrch val'. 
    have/cost_spec tprp':= tprp; move: tprp' (tprp' q') => _ [_ tmin].

    pose K n := gather_queries psi_FM phi (n, q').
    pose phin n:= trunc phi (K n).

    suff [m mprp]:
      exists m, forall t, t <= time q' ->
                (mu (phin m) (t, q'))
                  \is_sublist_of
                  (K m).
    - exists (maxn (time q') m).+1.
      apply/U_val_spec; split; first exact/gs_cns; simpl.  
      apply/psi_FM_val_spec.
      exists (time q'); split.
      + by rewrite size_F2GL; apply/leq_trans/psi_FM_gq_size/leq_maxl/psi_FM_size_gq/leqnn.
      split => //.
      + rewrite -trunc_spec -tval !sfrst_osrch.
        rewrite [RHS](@mod _ _ (trunc phi (gather_queries psi_FM phi (maxn (time q') m, q')))).
        * do 2 f_equal.
          apply/eqP/osrch_eqP; case => [[/=t' ineq] fval].
          move: ineq; rewrite ltnNge => /negP fls; apply/fls.
          have le: t' <= time q' by rewrite leqNgt; apply/negP => lt; apply/fls/leq_trans/lt.   
          apply/tmin; move: fval.     
          rewrite -(@mod (trunc phi (gather_queries psi_FM phi (m, q')))) //.
          - by rewrite (@mod _ _ phi) //; first exact/coin_subl/trunc_coin/mprp.
          apply/coin_trans/coin_sym/coin_subl/trunc_coin/subs_trans/gq_subl/leq_maxr/mprp => //.
          by apply/coin_subl/trunc_coin/mprp.
        apply/coin_sym/coin_subl/trunc_coin.
        rewrite -(@modmod (trunc phi (gather_queries psi_FM phi (m, q')))).
        * exact/subs_trans/gq_subl/leq_maxr/mprp.
        exact/coin_subl/trunc_coin/mprp.
      rewrite -trunc_spec unzip1_F2GL => t' leq.
      rewrite -(@modmod (trunc phi (gather_queries psi_FM phi (m, q')))).
      + exact/subs_trans/gq_subl/leq_maxr/mprp.
      apply/coin_trans/coin_sym/coin_subl/trunc_coin/subs_trans/gq_subl/leq_maxr/mprp => //.
      exact/coin_subl/trunc_coin/mprp.
      
    have coin l m: l <= m -> phin m \coincides_with phi \on K l.
    - by move => ineq; apply/coin_subl/trunc_coin/gq_subl.    

    have coinlm l m: l <= m -> phin l \coincides_with phin m \on K l.
    - by move => ineq; apply/coin_trans/coin_sym/coin/ineq/coin.

    suff: forall t, t <= time q' -> exists m, forall t', t' <= t -> mu (phin m) (t', q') \is_subset_of K m.
    - elim: (time q') => [ass | t ih ass].
      + by have [ | m mprp]//:= ass 0; exists m => t'; rewrite leqn0 => /eqP ->; apply/mprp.
      have [ | m mprp]:= ih; first by move => t' ineq; apply/ass/leq_trans; first exact/ineq.
      have [ | m' m'prp] //:= ass t.+1.
      exists (maxn m m') => l.
      rewrite leq_eqVlt; case/orP => [/eqP -> | ineq].
      + rewrite -(@modmod (phin m')); first exact/subs_trans/gq_subl/leq_maxr/m'prp.
        exact/coin_subl/coinlm/leq_maxr/m'prp.
      rewrite -(@modmod (phin m)); first exact/subs_trans/gq_subl/leq_maxl/mprp.
      exact/coin_subl/coinlm/leq_maxl/mprp.

    have [psi lmt]: exists psi, psi \is_limit_of phin.
    - suff /choice: forall q, exists a, exists n, forall m, n <= m -> a = phin m q by trivial.
      move => q.
      case: (classic (exists k, q \in gather_queries psi_FM phi (k, q'))) => [[m /inP lstn] | ].
      * by exists (phi q); exists m => m' ineq; rewrite /phin/graphs.trunc; have /inP ->:= gq_subl ineq lstn.
      move => /not_ex_all_not prp.
      exists (somea); apply/not_all_not_ex => fls; apply/fls.
      move => m ineq; rewrite /phin/graphs.trunc.
      by have ->: q \in gather_queries psi_FM phi (m, q') = false by apply/negP/prp.

    have lim: mu psi \is_limit_of ptw mu phin.
    - suff scnt: (F2MF mu) \is_sequentially_continuous by apply/scnt; first exact/lmt.
      by apply/cont_scnt/cont_F2MF => phi'; exists (mu phi') => q'1 psi'; apply/modmod.
 
    elim => [_ | t ih ineq].
    - have [m mprp]:= lim (0, q'); exists (maxn (time q') m).+1 => t; rewrite leqn0 => /eqP ->.
      rewrite /ptw in mprp.
      rewrite -mprp //; last by apply/leqW/leq_maxr.
      rewrite (mprp m) // {1}/K /gather_queries /=.
      case psival: psi_FM => [a' | K'].
      + move: psival => /psi_FM_val_spec.
        rewrite -trunc_spec unzip1_F2GL; case => [t' [sze [sfrstval prp]]].
        apply/subs_trans/(prp 0) => //.
        rewrite -!mprp //; apply/leq_maxr.
      have [] //:= @psi_FM_noval_phi' _ _ (time q') _ phi _ _ _ psival.
      rewrite -trunc_spec unzip1_F2GL; apply/coin_sym/trunc_coin.
      - by rewrite tval.
      - rewrite size_F2GL; apply/leq_trans/size_gq/leq_maxl.
        exact/psi_FM_size_gq/leqnn/tprp.
      case eq: ord_search => [ | n] ->; rewrite -trunc_spec unzip1_F2GL filter_ntn => prp.
      - by rewrite -!mprp //; last exact/leq_maxr; left.
      apply/subs_trans/subs_unionr/subs_trans/(prp 0) => //.
      by rewrite -!mprp //; apply/leq_maxr.

    case: ih => [ | n nprp]; first by apply/leq_trans/ineq.
    have [m mprp]:= lim (t.+1, q'). exists (maxn n (maxn m (time q'))).+1 => t'.
    - rewrite leq_eqVlt; case/orP => [/eqP ts | ineq']; last first.
      + apply/subs_trans/gq_subl/leqW/leq_maxl/subs_trans/nprp; last first.
        * have leq: t' <= t by trivial.
          exact/leq.
        rewrite -(@modmod (phin n)) //.
        by apply/coin_subl/coinlm/leqW/leq_maxl; first exact/nprp.
      rewrite /ptw in mprp.
      rewrite ts -mprp //; last exact/leq_trans/leqW/leq_maxr/leq_maxl.
      rewrite (mprp m) // {1}/K /gather_queries /=.
      case psival: psi_FM => [a' | K'].
      + move: psival => /psi_FM_val_spec.
        rewrite -trunc_spec unzip1_F2GL; case => [l [sze [sfrstval prp]]].
        apply/subs_trans/(prp t.+1) => //.
        rewrite -!mprp //; first exact/leq_trans/leq_maxr/leq_maxl.
        apply/leq_trans; first exact/ineq.
        move: sfrstval; rewrite sfrst_osrch (@mod _ _ phi) => [Mval | ].
        apply/leq_trans/(@osrch_le (fun k => M (phin (maxn n (maxn m (time q')))) (k, q'))).
        - by apply/tmin; rewrite Mval.
        exact/coin_subl/trunc_coin/prp/osrch_le.        
      case cl: (check_sublist (mu (phin m) (t.+1, q')) (K (maxn n (maxn m (time q'))))).
      - rewrite /=; apply/subl_cat; right.
        by rewrite -mprp // (mprp m)//; apply/clP.
      have tval': M phi (time q', q') by rewrite tval.
      have -> := psi_FM_noval_phi _ tval' _ psival.
      + rewrite -trunc_spec unzip1_F2GL size_F2GL /= filter_ntn; apply/subs_trans/subs_unionl.
        suff eq: nat_search (fun k => ~~ check_sublist (mu (phin (maxn n (maxn m (time q')))) (k, q')) (K (maxn n (maxn m (time q'))))) (size (K (maxn n (maxn m (time q'))))) = t.+1.
        * by rewrite eq -!mprp //; apply/leq_trans/leq_maxr/leq_trans/leq_maxl.
        apply/eqP; rewrite eqn_leq; apply/andP; split.
        * apply/nsrch_min; rewrite -mprp//; last exact/leq_trans/leq_maxr/leq_trans/leq_maxl.
          by rewrite (mprp m)// cl.            
        have lt: t < size (K (maxn n (maxn m (time q')))).
        * apply/leq_trans/size_gq/leq_trans/leq_maxr/leq_maxr.
          exact/leq_trans/psi_FM_size_gq/leqnn/tprp/ineq.
        pose p k:= ~~ check_sublist (mu (phin (maxn n (maxn m (time q')))) (k, q'))
                                          (K (maxn n (maxn m (time q')))).
        have <-:= @nsrch_eq p _ _ _ lt.
        rewrite nsrchS.
        case: ifP => // /negP pt.
        rewrite ltnNge; apply/negP => le.
        apply/pt/clP.
        apply/subs_trans/gq_subl/leq_maxl.
        rewrite -(@modmod (phin n)); first exact/nprp.
        exact/coin_subl/coinlm/leq_maxl/nprp.
      apply/nsrch_correct/clP => subl.
      suff: false by trivial.
      rewrite -cl; apply/clP/subs_trans/subl; rewrite -!mprp //.
      exact/leq_trans/leq_maxr/leq_maxl.
    rewrite -trunc_spec unzip1_F2GL.
    exact/coin_sym/trunc_coin.
    rewrite size_F2GL.
    apply/leq_trans/size_gq/leq_trans/leq_maxr/leq_maxr.
    exact/psi_FM_size_gq/leqnn.
    Unshelve.
    apply/0.
  Qed.  

  Lemma psi_FM_sfrst: (U psi_FM) \evaluates \F_(use_first M).
  Proof. exact/mon_eval/psi_FM_exte/sfrst_sing/U_mon. Qed.

  Lemma psi_FM_spec: (U psi_FM) \evaluates \F_M.
  Proof. exact/tight_trans/psi_FM_sfrst/sfrst_spec. Qed.

  Section associates_for_mu_and_M.
    Definition psi_mu (KLnq': (seq (Q * A) * (nat * Q'))) :=
      let (KL,nq'):= KLnq' in
      let phi := GL2F KL in
      let K' := (mu phi nq') in
      if check_sublist K' (unzip1 KL)
      then inl K'
      else inr K'.
  
    (* Instead of inl K' it would be nicer to have (filter (fun q => ~~(q \from unzip1 KL)) K') to
       avoid unneccessary duplication. *)
    
    Lemma mu_psi_spec: (U psi_mu) \evaluates (F2MF mu).
    Proof.
      apply/sing_exte_tight => [ | phi _ <- nq']; first exact/FU_sing.
      pose K_step K := mu (trunc phi K) nq' ++ K.
      pose Kn := fix Kn n := match n with
                             | 0 => nil
                             | n.+1 => K_step (Kn n)
                             end.
      have Kn_mon : forall n m, n <= m -> (Kn n) \is_sublist_of (Kn m).
      - move => n m /subnK <-; elim: (m - n) => // k ih.
        by rewrite addSn /= /K_step; apply/subl_cat; right.
        
      pose phin n := trunc phi (Kn n).
      have val n q: q \from Kn n -> phi q = phin n q.
      - by rewrite /phin /graphs.trunc; case: ifP => /inP.
           
      have [psi lim]: exists psi, psi \from limit phin.
      - suff /choice [psi lim]: forall q, exists a, exists N, forall m, N <= m -> a = phin m q by exists psi.
        move => q.
        case: (classic (exists n, q \from Kn n)) => [[n lstn] | /not_ex_all_not nt].
        + by exists (phi q); exists n => m ineq; apply/val/(Kn_mon _ _ ineq).
        exists somea; exists 0 => m _.
        rewrite /phin /graphs.trunc; case: ifP => // /inP lstn.
        by exfalso; apply/(nt m).

      have cont: (F2MF mu) \is_continuous by apply/cont_F2MF/modf_cont/modmod.

      have lim': mu psi \from limit (fun n => mu (phin n)).
      - by have /cont_scnt scnt:= cont; apply/scnt; first exact/lim.

      have coin n: phi \coincides_with (phin n) \on (Kn n).
      - by rewrite /phin; apply/coin_agre => q lstn; exact/val.

      have ->: mu phi nq' = mu psi nq'.
      - symmetry; apply/modmod.
        have [N Nprp]:= lim' nq'; rewrite (Nprp N) //.
        move: lim => /lim_coin lim.
        have [M' Mprp]:= lim (mu (phin N) nq').
        apply/coin_trans; first exact/Mprp/(leq_maxr N.+1 M').
        by apply/coin_sym/coin_subl/coin/subs_trans/Kn_mon/leq_maxl/subl_cat; left.

      have eq : phi =1 phi by trivial.

      have gqn n: gather_queries psi_mu phi (n,nq') === Kn n.
      - elim: n => // n ih.      
        rewrite /gather_queries /= /K_step/=.
        case: ifP => /clP subs /=.
        + rewrite ih set_eq_subs; split; first by apply/subl_cat; right.
          apply/cat_subl; split => //.
          rewrite unzip1_F2GL in subs.
          rewrite -ih; apply/subs_trans/subs; rewrite -trunc_spec.
          by have /fun_ext ->:= trunc_prpr somea eq ih.
        have /fun_ext <-:= trunc_prpr somea eq ih; rewrite -trunc_spec => q.
        by split => /L2SS_cat [] ?; apply/L2SS_cat; [left|right; apply/ih|left|right; apply/ih].

    have coin' : forall n, psi \coincides_with phi \on Kn n.
    - move: lim => /lim_coin lim n; have [N Nprp]:= lim (Kn n).
      exact/coin_trans/coin_sym/coin_subl/(coin (maxn n N))/Kn_mon/leq_maxl/Nprp/leq_maxr.

    have [N Nprp]:= lim' nq'.
    set k:= nat_search (fun k => check_sublist (mu (phin k) nq') (Kn k)) N.+1.
    exists k.+1.
    rewrite US.
    suff ->: U psi_mu phi (k, nq') = None.
    - rewrite {1}/psi_mu unzip1_F2GL -trunc_spec.
      have /fun_ext -> := trunc_prpr somea eq (gqn k).
      case: ifP => /clP; rewrite gqn; last move => /clP.
      + move => subs; f_equal; apply/modmod/coin_subl; first exact/subs.
        exact/coin_sym/coin_trans/coin/coin'.
      have ->// := @nsrch_correct (fun k => check_sublist (mu (phin k) nq') (Kn k)).
      by apply/clP; rewrite -Nprp // (Nprp N)//; apply/subl_cat; left.
    move: (leqnn k).
    rewrite {2}/k.
    elim: k => // k ih ineq.
    rewrite US ih; last by apply/leq_trans/ineq.
    rewrite {1}/psi_mu unzip1_F2GL -trunc_spec; case: ifP => // /clP.
    rewrite gqn; have /fun_ext ->:= trunc_prpr somea eq (gqn k).
    move => /clP Pk.
    have  ineq':= @nsrch_min (fun k => check_sublist (mu (trunc phi (Kn k)) nq') (Kn k)) N.+1 k Pk.
    suff /leP: k.+1 <= k by lia.
    exact/leq_trans/ineq'/ineq.
  Qed.

  Lemma psi_mu_mon K K' phi n q':
    psi_mu (F2GL phi K, (n, q')) = inl K' -> psi_mu (F2GL phi (K' ++ K), (n,q')) = inl K'.
  Proof.
    rewrite /psi_mu unzip1_F2GL -!trunc_spec; case: ifP => // /clP subs [<-].    
    case: ifP => /clP subs'.
    - f_equal.
      symmetry; apply/modmod/coin_trans/coin_sym/coin_subl/trunc_coin/subl_cat; last by left.
      exact/coin_subl/trunc_coin.
    exfalso; apply/subs'; rewrite unzip1_F2GL.
    apply/subl_cat; left.
    have eq: phi =1 phi by trivial.
    have eq': (mu (trunc phi K) (n, q') ++ K) === K.
    - apply/set_eq_subs; split; last by apply/subl_cat; right.
      by apply/cat_subl; split; try by apply/subl_cat; right.
    by have /fun_ext -> := trunc_prpr somea eq eq'.
  Qed.

  Context (psi_mu: seq (Q * A) * (nat * Q') -> seq Q + seq Q).
  Hypothesis psi_mu_spec: (U psi_mu) \evaluates (F2MF mu).
  Hypothesis psi_mu_mon: forall K K' phi n q',
      psi_mu (F2GL phi K, (n, q')) = inl K' -> psi_mu (F2GL phi (K' ++ K), (n, q')) = inl K'.
                                 
  Definition psi_M (KLnq': seq (Q * A) * (nat * Q')) :=
    match psi_mu KLnq' with
    | inr K => inr K
    | inl K => if check_sublist K (unzip1 KLnq'.1)
              then inl (M (LF2F somea (GL2LF KLnq'.1)) KLnq'.2) 
              else inr K
    end.

  (* Also here, using inl filter (fun q => ~~ (q \in unzip1 KL) K) instead of inl K would be
     preferable. *)

  Lemma psi_M_spec: (U psi_M) \evaluates (F2MF M).
  Proof.
    apply/sing_exte_tight => [ | phi _ <- [n q']]; first exact/FU_sing.
    
    have [val' prp] := psi_mu_spec (@F2MF_tot _ _ mu phi).
    have [time time_spec]:= get_cost val'.
    
    specialize (time_spec (n,q')).
    move: time_spec => [tval tmin].

    exists (time (n, q')).+1.
    rewrite US.
    case teq: (time (n, q')) tval => [ | t] //.
    rewrite !US.
    
    have nn: forall k, k<= t -> U psi_mu phi (k, (n, q')) = None.
    - move => k /leP ineq; case E: U => //.
      suff: time (n, q') <= k by rewrite teq => /leP; lia.
      by apply/tmin; rewrite E.
    rewrite nn //.
 
    have psiprp: forall k, k <= t ->
                gather_queries psi_M phi (k, (n, q')) = gather_queries psi_mu phi (k, (n, q'))
                /\
                U psi_M phi (k, (n, q')) = None.
    - elim => // k ih ineq.
      have ineq': k <= t by apply/leq_trans/ineq.
      move: ih => []// gq vl.
      have := nn k.+1 ineq.
      rewrite !US vl gq {2}/psi_M nn //.
      case eq: psi_mu => // _; split => //.
      rewrite /gather_queries /=; rewrite /gather_queries /= in gq.
      by rewrite {1}/psi_M gq eq /= gq.

    case psi_mu_val: psi_mu => [K | ]// _.
    have [ | gq ->] //:= psiprp t.      
    rewrite {1}/psi_M /= gq psi_mu_val unzip1_F2GL -trunc_spec.
    case: ifP => [/clP subs | subs].
    - f_equal.
      symmetry; apply/mod.
      apply/coin_sym/coin_subl/trunc_coin.
      suff <-: K = mu phi (n, q') by trivial.
      move: val' => [Lf val'].
      rewrite (prp _ val').
      suff: Some (Lf (n, q')) = Some K by case.
      have [k eq]:= val' (n, q').
      have /mon_spec mon:= @U_mon _ _ _ _ psi_mu.
      have := mon phi (n,q') K t.+1 k.
      rewrite eq => [->] //; first by rewrite -teq; apply/tmin; rewrite eq.
      by rewrite US nn // psi_mu_val.
    rewrite {1}/psi_M .
    rewrite {1}/gather_queries /= {1}/psi_M.
    rewrite {1}/gather_queries in gq; rewrite gq psi_mu_val !unzip1_F2GL subs /=.
    rewrite psi_mu_mon; last by rewrite gq.
    have eq: K = mu phi (n, q').
    - move: val' => [Lf val'].
      rewrite (prp _ val').
      suff: Some (Lf (n, q')) = Some K by case.
      have [k eq] := val' (n, q').
      have /mon_spec mon := @U_mon _ _ _ _ psi_mu.
      have := mon phi (n, q') K t.+1 k.
      rewrite eq => [->]//; first by rewrite -teq; apply/tmin; rewrite eq.
      by rewrite US nn // psi_mu_val.
    suff /clP subs': K \is_subset_of (gather_queries psi_M phi (t.+1, (n, q'))).
    - rewrite subs'; f_equal; rewrite -trunc_spec.
      apply/mod/coin_subl/trunc_coin.
      rewrite {2}/gather_queries /= {2}/psi_M /= gq psi_mu_val unzip1_F2GL subs /=.
      rewrite eq.
      apply/subl_cat; left.
      rewrite -(@modmod phi) //.
      apply/coin_subl/coin_sym/trunc_coin/clP.
      by rewrite -eq.
    rewrite /gather_queries /= {1}/psi_M gq psi_mu_val unzip1_F2GL subs /=.
    by apply/subl_cat; left.
  Qed.
  End associates_for_mu_and_M.
End construct_associate.
