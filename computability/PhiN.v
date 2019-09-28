(* This file provides an abstract envelope for computability theoretical considerations *)
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype choice seq.
From mf Require Import all_mf.
Require Import iseg sets graphs smod cont seq_cont minm.
Require Import ClassicalChoice ConstructiveEpsilon.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Phi_assignment.
  Context (A Q: Type).
  Notation B := (Q -> A).
  Local Notation "Q ~> A" := (nat * Q -> option A) (at level 2).
    
  Definition Phi (N: Q ~> A):= make_mf (fun q a => exists n, N(n,q) = Some a).
  
  Local Notation "\Phi_ N" := (Phi N) (at level 2).
  Notation "N '\evaluates_to' phi" := (\Phi_N \tightens phi) (at level 40).

  Lemma sing_eval N phi: \Phi_N \is_singlevalued -> phi \is_singlevalued ->
                        N \evaluates_to phi <-> \Phi_N \extends phi.
  Proof. by move => sing sing'; rewrite exte_tight. Qed.

  Lemma sing_eval_F2MF N phi: \Phi_N \is_singlevalued ->
                              N \evaluates_to F2MF phi <-> \Phi_N \extends F2MF phi.
  Proof.
    by move => sing; apply/sing_eval => //; apply/F2MF_sing.
  Qed.
  
  Lemma eval_Phi N: N \evaluates_to \Phi_N.
  Proof. by move => q qfd; split. Qed.
  
  Definition monotone_in (N: Q ~> A) q := forall n, N(n,q) <> None -> N(n.+1,q) = N(n,q).
  
  Lemma mon_in_spec (N: Q ~> A) q: monotone_in N q <->
	  forall a n m, n <= m -> N(n,q) = Some a -> N(m,q) = Some a.
  Proof.
    split => [mon a' n m | mon n neq]; last by case E: (N(n,q)) neq=>[a | ]// _; apply/mon/E. 
    elim: m => [ineq eq | m ih]; first by have/eqP <-: n == 0 by rewrite -leqn0.
    rewrite leq_eqVlt; case/orP => [/eqP <- | ineq eq]//.
    by rewrite mon => //; rewrite ih; rewrite /pickle /=.
  Qed.

  Lemma mon_in_eq N q n m a b:
    monotone_in N q -> N(n,q) = Some a -> N(m,q) = Some b -> a = b.
  Proof.
    case/orP: (leq_total n m) => ineq /mon_in_spec mon eq eq'; apply /Some_inj.
      by rewrite -eq'; symmetry; apply/mon/eq.
    by rewrite -eq; apply/mon/eq'.
  Qed.

  Definition monotone N:= forall q, monotone_in N q.
  Local Notation "N '\is_monotone'" := (monotone N) (at level 2).

  Lemma mon_spec (N: Q ~> A): N \is_monotone <->
                              forall q a n m, n <= m -> N(n,q) = Some a -> N(m,q) = Some a.
  Proof.
    split => [mon q a n m | mon q].
    - have /mon_in_spec prp: monotone_in N q by apply/mon.
      exact/prp.
    by rewrite mon_in_spec => a' n m ineq eq; apply/mon/eq.
  Qed.

  Lemma mon_sing (N: Q ~> A):
    N \is_monotone -> \Phi_N \is_singlevalued.
  Proof. by move => mon q a a' [n eq] [m eq']; apply/mon_in_eq/eq'/eq/mon. Qed.
  
  Lemma mon_eval_sing N phi: N \is_monotone -> phi \is_singlevalued ->
	N \evaluates_to phi <-> \Phi_N \extends phi.
  Proof. by move => mon sing; apply/sing_eval/sing/mon_sing. Qed.

  Lemma mon_eval_F2MF N phi: N \is_monotone ->
                             N \evaluates_to F2MF phi <-> \Phi_N \extends F2MF phi.
  Proof. by move => mon; apply/mon_eval_sing/F2MF_sing. Qed.

  Definition cost N : \Phi_N \is_total -> Q -> nat.
    move => tot q.
    pose p n := N (n, q).
    apply/(constructive_ground_epsilon_nat p) => [n | ].    
    - by rewrite /p; case E: (N (n,q)) => [a |]; [left | right].
    by have [a [n eq]]:= tot q; exists n; rewrite /p eq.
  Defined.
  
  Lemma cost_spec N (tot: \Phi_N \is_total): forall q, N (cost tot q, q).
  Proof. by move => q; apply/(constructive_ground_epsilon_spec_nat (fun n => N (n, q))). Qed.
      
  Lemma tot_choice N: \Phi_N \is_total -> {phi | \Phi_N \extends (F2MF phi)}.
  Proof.
    move => tot.
    pose p q n := N (n,q).
    have p_tot: forall q, exists n, p q n.
    - by move => q; have [a [n eq]]:= tot q; exists n; rewrite /p eq.
    have p_dec: forall q n, {p q n} + {~p q n}.
    - by move => q n; rewrite /p; case E: (N (n,q)) => [a |]; [left | right].
    suff f: forall q, {a | exists n, N (n, q) = some a}.
    - by exists (fun q => sval (f q)) => q _ <-; have [n] := projT2 (f q); exists n.
    move => q.
    pose n := constructive_ground_epsilon_nat (p q) (p_dec q) (p_tot q).
    case E: (N(n,q)) => [a |]; first by exists a; exists n.
    suff: N (n, q) by rewrite E.
    exact/(constructive_ground_epsilon_spec_nat (p q)).    
  Qed.

  Definition evaluate N: \Phi_N \is_total -> Q -> A.
    by move => tot; apply/(sval (tot_choice tot)).
  Defined.

  Lemma eval_spec N (tot: \Phi_N \is_total): \Phi_N \extends (F2MF (evaluate tot)).
  Proof. exact/(svalP (tot_choice tot)). Qed.

  Lemma eval_sing_spec N (tot: \Phi_N \is_total):
    \Phi_N \is_singlevalued -> F2MF (evaluate tot) =~= \Phi_N.
  Proof.
    move => sing q a; split => val; first exact/eval_spec.
    exact/sing/val/eval_spec.
  Qed.

  Definition F2N (phi: Q -> A) (nq: nat * Q) := Some (phi nq.2).

  Lemma F2N_spec phi: \Phi_(F2N phi) =~= F2MF phi.
  Proof. by move => q a; split => [[n [<-]] | <-]//; exists 0. Qed.
End Phi_assignment.
Notation "\Phi_ N" := (Phi N) (format "'\Phi_' N", at level 2).

Lemma ovrt_po (Q A: eqType) (D: mf_set.subset (Q -> A)):
  overt D ->
  exists N, dom \Phi_N === dom (projection_on D) /\ (projection_on D) \extends \Phi_N.
Proof.
  move => [ou [fd dns]].
  pose N nKL := if ou nKL.1 is some phi
                then if check_choice phi nKL.2 then Some phi else None
                else None.
  exists N; rewrite /N; split => [KL | KL phi [n]]; last first.
  - case E: (ou _) => [phi' | ]//.
    case: ifP => // /icfP icf [<-]; split => [ | q qfd]; [apply/fd | apply/icf] => //.
    by exists n; rewrite /= E.
  split => [[phi [n val]] | [phi [phifd /icfP ckch]]].
  - exists phi.
    case E: (ou _) val => [phi' | ] //; case: ifP => //= ckch [<-].
    by split; [apply/fd | apply/icfP] => //; exists n; rewrite /= E.
  have [psi [/coin_agre agre [n /=]]]:= dns phi phifd (unzip1 KL).
  case E: (ou _) => [phi' | ] // eq.
  exists psi; exists n => /=; rewrite E.   
  suff ->: check_choice phi' KL by rewrite eq.
  apply/icfP => q [a val]; rewrite /=; move/icfP: ckch => icf.
  rewrite eq -agre //; first by apply/icf; exists a.
  by elim: (KL) val => //; case => q' a' KL' ih /= [[->] | /ih ]; [left | right].
Qed.

Section use_first.
  Context Q A (N: nat * Q -> option A).
  Local Notation "N \is_monotone" := (monotone N) (at level 2).
          
  Definition use_first nq:= N (search (fun k => N(k,nq.2)) nq.1,nq.2).

  Lemma sfrst_mon: use_first \is_monotone.
  Proof.
    move => q n neq.
    rewrite /use_first /=.
    f_equal; symmetry; f_equal.
    rewrite -search_search.
    apply/search_eq .
    move: neq; rewrite /use_first.
    - by case: (N (search (fun k => N(k,q)) n, q)).
    by apply/leq_trans; first exact/search_le.
  Qed.

  Lemma sfrst_sing: \Phi_use_first \is_singlevalued.
  Proof. exact/mon_sing/sfrst_mon. Qed.

  Lemma sfrst_spec: \Phi_use_first \tightens \Phi_N.
  Proof.
    have mon:= @sfrst_mon.
    rewrite tight_spec.
    split => [q [a [n eq]] | q a [_ [n eq]]]; last by exists (search (fun k => N(k,q)) n).
    have: is_true (isSome (N (search (fun k => N(k,q)) n, q))).
    * by apply/(@search_correct (fun k => N(k,q))); rewrite eq.
    by case E: (N (search (fun k => N(k,q)) n, q))=> [b | ] //_; exists b; exists n.
  Qed.

  Lemma sfrst_tot: \Phi_N \is_total <-> \Phi_use_first \is_total.
  Proof.
    split=>tot q'; have [a'[n eq]]:= tot q'; last by exists a'; exists (search(fun k=>N (k, q'))n).
    have : N (search (fun k => N (k, q')) n, q').
    - by apply/(@search_correct (fun k => N (k, q'))); rewrite eq.
    case E: (N (search (fun k => N (k, q')) n, q')) => [b' | ] // _.
    by exists b'; exists n.
  Qed.
    
  Lemma mon_sfrst: N \is_monotone <-> forall n q, N(n,q) = use_first(n,q).
  Proof.
    split => [/mon_spec mon n q | eq n m neq]; last by rewrite eq sfrst_mon -eq.
    rewrite /use_first.
    case E: (N (search (fun k => N(k,q)) n, q)) => [a | ].
    - apply/mon; last exact/E.
      exact/search_le.
    have := @search_le (fun k => N(k,q)) n.
    rewrite leq_eqVlt => /orP [/eqP <- | /searchP [m [Nmq mln]]] //.
    have:= @search_correct (fun k => N(k,q)) _ Nmq.
    have ->:= @search_eq (fun k => N(k,q)) m n Nmq; first by rewrite E.
    by case: (m) mln => // m' m'ln; apply/leq_trans/m'ln.
  Qed.
    
  Lemma sing_sfrst: \Phi_N \is_singlevalued <-> \Phi_N =~= \Phi_use_first.
  Proof.
    split => [sing q a| ->]; last exact/sfrst_sing.
    split => [[n val] | [n]]; last by exists (search (fun k => N(k,q)) n).
    exists n.
    rewrite /use_first.
    have Nnq: N(n,q) by rewrite val.
    have := (@search_correct (fun k => N(k,q)) n Nnq).
    case E: (N(_, q)) => [b | ] // _.
    have ->:= sing q a b => //; first by exists n.
    by exists (search (fun k => N(k,q)) n).
  Qed.
End use_first.      

Section composition.
  Context Q A D (N: nat * A -> option D) (N': nat * Q -> option A).
  
  Definition Phi_comp (nq: nat * Q) :=
    let n:= nq.1 in
    let q:= nq.2 in              
    match @pickle_inv _ n with
    | None => None
    | some mk => let m := mk.1 in
                 let k := mk.2 in
                 match (N'(m,q)) with
                 | None => None
                 | some a => N(k,a)
                 end
    end.

  Lemma Phi_rcmp_spec:
    \Phi_Phi_comp =~= \Phi_N \o_R \Phi_N'.
  Proof.
    rewrite/Phi_comp => q d.
    split => [[n] | [a [[m eq] [k eq']]]]; last by exists (pickle (m,k)); rewrite pickleK_inv eq.
    case: (pickle_inv _ n) => // [[m k]]; case E: (N'(m,q)) => [a |]// eq.
    by exists a; split; [exists m | exists k].
  Qed.

  Lemma Phi_comp_spec: \Phi_Phi_comp \tightens (\Phi_N \o \Phi_N').
  Proof. by rewrite Phi_rcmp_spec; apply/rcmp_tight. Qed.

  Definition Phi_mon_comp (nq: nat * Q) :=
    let n := nq.1 in
    let q := nq.2 in
    match N'(n,q) with
    | None => None
    | some a => N(n,a)
    end.

  Lemma Phi_mcmp_mon: monotone N -> monotone N' -> monotone Phi_mon_comp.
  Proof.
    rewrite /Phi_mon_comp => mon mon' n q neq.
    by rewrite mon'; case: (N'(q,n)) neq => // a; apply/mon.
  Qed.
    
  Lemma Phi_mcmp_spec: monotone N -> monotone N' -> \Phi_Phi_mon_comp =~= \Phi_N \o \Phi_N'.
  Proof.
    rewrite /Phi_mon_comp => mon mon'; rewrite sing_rcmp; last by apply/mon_sing.
    move: mon mon' => /mon_spec mon /mon_spec mon' q d; split => [[n] | [a [[n' eq'] [n eq]]]].
    - by case E: (N'(n,q)) => [a | ]// eq; exists a; split; exists n.
    by exists (maxn n n'); rewrite (mon' _ _ _ _ _ eq'); [apply/mon/eq/leq_maxl | exact/leq_maxr].
  Qed.
End composition.

Section evaluation_aux.
  Local Open Scope name_scope.
  Context (Q A Q' A': Type). 
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Notation subset T := (mf_set.subset T).

  Fixpoint L2LF (T: eqType) T' (KL: seq (T * T')) q:=
    match KL with
    | nil => nil
    | qa :: KL' => if qa.1 == q
                   then qa.2 :: L2LF KL' q
                   else L2LF KL' q
    end.
    
  Lemma L2LF_spec (T: eqType) T' (KL: (seq (T * T'))):
    LF2MF (L2LF KL) =~= GL2MF KL.
  Proof.    
    rewrite /GL2MF.
    elim: KL => // [[t t'] KL] ih t'' t''' /=.
    case: ifP => [/eqP eq | neq].
    - split; first by case => [-> | ]; [left; rewrite eq | right; apply/ih].
      by case => [[<- <-] | ]; [left | right; apply/ih].
    split; first by right; apply/ih.
    by case => [[/eqP] | lstn]; [rewrite neq | apply/ih].
  Qed.

  Fixpoint omap T T' (F: T -> option T') (L: seq T) :=
    match L with
    | nil => nil
    | t :: L' => match F t with
                 | Some a => a :: omap F L'
                 | None => omap F L'
                 end
    end.
End evaluation_aux.

Section N2LF.
  Local Open Scope name_scope.
  Context (Q: eqType) (A Q' A': Type). 
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Notation subset T := (mf_set.subset T).
  Context (N: nat * Q -> option A).
  Definition N2LF KL q:= omap (fun n => N(n,q)) (L2LF KL q).

  Lemma N2LF_cons q n KL q':
    N2LF ((q,n) :: KL) q' =
    if q == q' then
      match N(n,q') with
      | Some a => a :: N2LF KL q'
      | None => N2LF KL q'
      end
    else N2LF KL q'.
  Proof.
    by rewrite /N2LF /=; case: ifP.    
  Qed.

  Lemma N2LFq_cons q n KL:
    N2LF ((q,n):: KL) q = if N(n,q) is Some a then a :: N2LF KL q else N2LF KL q.
  Proof. by rewrite N2LF_cons eq_refl. Qed.
  
  Lemma N2LF_cat KL' KL q':
    N2LF (KL' ++ KL) q' = N2LF KL' q' ++ N2LF KL q'.
  Proof.
    elim: KL' => // [[q n]] KL' ih /=.
    rewrite !N2LF_cons; case: ifP => [/eqP _ | _]; last exact/ih.
    case: (N(n,q')) => [a'/= | ]; last exact/ih.
    by rewrite ih.
  Qed.

  Definition N2MF LK := LF2MF (N2LF LK).
  
  Lemma N2MF_nil: N2MF [::] =~= mf_empty.
  Proof. done. Qed.

  Lemma N2MF_ext LK LK': L2SS LK === L2SS LK' -> N2MF LK =~= N2MF LK.
  Proof. done. Qed.
  
  Lemma N2MF_spec KL: \Phi_N \extends N2MF KL.
  Proof.
    elim: KL => [q a  | [q' n] KL ih q a] // prp.
    move: prp; rewrite /=/N2LF /=.    
    case : ifP => [/eqP eq /= | neq]; last exact/ih.
    by case E: (N(n,q)) => [a' /= | ] => [[<- | ] |]; [exists n | apply/ih | apply/ih].
  Qed.

  Lemma N2MF_cons q n KL: N2MF ((q,n)::KL) \extends N2MF KL.
  Proof.
    rewrite /N2MF => q' a' /=.
    rewrite N2LF_cons.
    case: ifP => // /eqP <-.
    by case: (N(n,q)) => //; right.
  Qed.

  Lemma N2MF_cat KL' KL: N2MF (KL' ++ KL) \extends N2MF KL.
  Proof.
    elim: KL' => [ | qn KL' ih/=]; first rewrite cat0s => q //.
    by apply/exte_trans/N2MF_cons.
  Qed.
  
  Lemma N2MF_dom KL:
    dom (N2MF KL) \is_subset_of dom (GL2MF KL).
  Proof.
    move => q [a].
    elim: KL => // [[q' n] KL ih /=].
    rewrite N2LF_cons.
    case: ifP => [/eqP <- | _ lstn]; first by exists n; left.
    by have [ | n' lstn']//:= ih; exists n'; right.
  Qed.

  Lemma N2MF_dom_spec K:
    (L2SS K) \is_subset_of dom \Phi_N <-> exists KL, (L2SS K) \is_subset_of dom (N2MF KL).
  Proof.
    split => [ | [KL subs]]; last exact/subs_trans/exte_dom/N2MF_spec/KL.
    elim: K => [ | q K ih /cons_subs [[a [n val]] /ih [KL subs]]]; first by exists nil.
    exists ((q,n):: KL); apply/cons_subs.
    split; first by exists a; rewrite /N2MF /= N2LF_cons eq_refl val; left.
    move => q' lstn.
    have [a' val']:= subs q' lstn.
    exists a'.
    move : val'.
    rewrite /N2MF /= N2LF_cons.
    case: ifP => //.
    by case E: (N(n,q')) => //; right.
  Qed.
        
  Fixpoint allSome T (L: seq (seq T)) :=
    match L with
    | [::] => true
    | K :: L' => (~~ nilp K) && allSome L'
    end.    

  Lemma aSoP K (phi: Q -> seq A):
    reflect (L2SS K \is_subset_of dom (LF2MF phi)) (allSome (map phi K)).
  Proof.
    apply/(iffP idP); last by elim: K => // q K ih /cons_subs [[a /=]]; case: (phi q).
    elim: K => [_ q | ]// q K ih; rewrite map_cons => /= /andP [pq aS].
    apply/cons_subs; split; last by apply/ih.
    by case E: (phi q) pq => [ | a L]// _; exists a; rewrite /= E; left.
  Qed.
  
  Lemma last_def T (L: seq T) (t t': T):
    L <> nil -> last t L = last t' L.
  Proof. by case: L. Qed.
  
  Lemma last_lstn T (L: seq T) (t: T):
    L <> nil -> List.In (last t L) L.
  Proof.    
    case: L => // def L _.
    move: {2}(size L) (eq_refl (size L)) t def => n.
    elim: n L => [ | n ih L /eqP ]; first by case => //; left.
    case: L => // a L [sze] t def.
    rewrite last_cons; right.
    exact/ih/eqP.
  Qed.
  
  Fixpoint list_dom KL :=
    match KL with
    | nil => nil
    | qn:: KL' => if N(qn.2,qn.1) is Some a then qn.1 :: list_dom KL' else list_dom KL'
    end.

  Lemma lstd_spec KL: L2SS (list_dom KL) === dom (N2MF KL).
  Proof.
    elim: KL => [q | [q n] KL ih q' /=]; first by split; case.
    rewrite N2LF_cons.
    case: ifP => [/eqP <-| /eqP neq].
    - case E: (N(n,q)) => [a | ]; last exact/ih.
      by split => [ | [a']]; first exists a; left.
    case E: (N(n,q)) => [a | ]; last exact/ih.
    split => [/= | ]; last by right; apply/ih.
    by case => [eq | /ih [a' val]]; [exfalso; apply/neq | exists a'].
  Qed.

  Lemma lstd_zip KL: L2SS (list_dom KL) \is_subset_of L2SS (unzip1 KL).
  Proof.
    elim: KL => // [[q n]] KL ih /=.
    case: (N(n,q)) => [a | ]; last by right; apply/ih.
    by move => q' /=[<- | ]; [left | right; apply/ih].
  Qed.

  Lemma lstd_cat KL KL': list_dom (KL ++ KL') = list_dom KL ++ list_dom KL'.
  Proof. by elim: KL => // [[q n]] KL /= ->; case: (N(n,q)). Qed.
End N2LF.

Section extend.
  Local Open Scope name_scope.
  Context (Q: eqType) (A Q' A': Type). 
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Notation subset T := (mf_set.subset T).
  Context (default: A).
  Definition extend (phi: Q -> seq A) q := head default (phi q).

  Lemma extend_spec phi: (extend phi) \is_choice_for (LF2MF phi).
  Proof.
    rewrite /extend => q [a /=].
    by case: (phi q) => // q' K /= [-> | ]; left.
  Qed.

  Fixpoint check_sublist (K L: seq Q):=
    match K with
    | nil => true
    | q :: K' => (q \in L) && check_sublist K' L
    end.

  Lemma clP K L: reflect (K \is_sublist_of L) (check_sublist K L).
  Proof.
    apply/(iffP idP).
    elim: K => [_ q | q K ih ]//= /andP [lstn cl].
    by apply/cons_subs; split; [exact/inP | apply/ih].
    elim: K => // q K ih /cons_subs [lstn subl] /=.
    by apply/andP; split; [exact/inP | apply/ih].
  Qed.

  Lemma zip_nill S T (L: seq T): zip ([::]:seq S) L = nil.
  Proof. by case: L. Qed.

  Lemma zip_nilr S T (K: seq S): zip K ([::]:seq T) = nil.
  Proof. by case: K. Qed.
End extend.

Section function_application.
  Local Open Scope name_scope.
  Context (A' Q': Type) (Q: eqType) A (default: A). 
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Context (f: B -> B').
  Context (mu: B -> Q' -> seq Q).
  Notation subset T := (mf_set.subset T).
  Hypothesis modmod: mu \modulus_function_for mu.
  Context (N: nat * Q -> option A).
  
  Definition KL_step KL L q':= zip (mu (extend default (N2LF N KL)) q') L ++ KL.

  Lemma KL_step_spec KL q' phi:
    phi \is_choice_for (\Phi_N) ->
    (L2SS (mu (extend default (N2LF N KL)) q')) \is_subset_of dom \Phi_N ->
    exists L,
      size L = size (mu (extend default (N2LF N KL)) q')
      /\
      (L2SS (mu (extend default (N2LF N KL)) q')) \is_subset_of dom (N2MF N (KL_step KL L q'))
      /\
      ((extend default (N2LF N KL)) \agrees_with phi \on (dom (N2MF N KL)) ->
      (extend default (N2LF N (KL_step KL L q'))) \and phi \coincide_on (mu (extend default (N2LF N KL)) q')).
  Proof.
    rewrite /KL_step => icf subs.
    elim: (mu (extend default (N2LF N KL)) q') subs => [dm | q K ih /cons_subs [fd subs]].
    - by exists nil; split; last by split => // q [].
    have [L [sze [subs' coin]]]:= ih subs.
    have [n val']:= icf _ fd.
    exists (n :: L).
    split => [/= |]; first by rewrite sze.
    split => [ | agre].
    - apply/cons_subs; split; last exact/subs_trans/exte_dom/N2MF_cons/subs'.
      by exists (phi q) => /=; rewrite N2LF_cons eq_refl val'; left.
    apply/coin_agre => q'' /= [<- | lstn]; first by rewrite /extend N2LF_cons eq_refl val'.
    rewrite /extend N2LF_cons.
    case: ifP => [/eqP <- | _]; first by rewrite val' .
    by move: q'' lstn; apply/coin_agre/coin.
  Qed.
  
  Fixpoint KL_rec s q' := match s with
                          | nil => nil
                          | L :: s' => KL_step (KL_rec s' q') L q'
                          end.
  
  Definition phi_rec s q' := extend default (N2LF N (KL_rec s q')).

  Hypothesis (tot: \Phi_N \is_total).

  Lemma phi_rec_spec phi q':
    phi \is_choice_for (\Phi_N) ->
    exists s, phi \and (phi_rec s q') \coincide_on (mu phi q')
              /\
              L2SS (mu (phi_rec s q') q') \is_subset_of dom (N2MF N (KL_rec s q')).
  Proof.
    move => icf.
    have prp: forall KL, L2SS (mu (extend default (N2LF N KL)) q') \is_subset_of dom \Phi_N.
    - by move => KL; rewrite ((tot_spec \Phi_N).1 tot); apply/subs_all.
    have /choice [sf sfprp]:= KL_step_spec icf (prp _).
    pose KL:= fix KL n := match n with
                          | 0 => nil
                          | S n' => KL_step (KL n') (sf (KL n')) q'
                          end.
    pose phin n:= extend default (N2LF N (KL n)).

    have phin_dom: forall n m, n < m -> L2SS (mu (phin n) q') \is_subset_of dom (N2MF N (KL m)).
    - move => n m /subnK <-.
      elim: (m - n.+1) => [ | k ih]; first by rewrite add0n; have [sze []]:= sfprp (KL n).
      by rewrite addSn /= /KL_step; apply/subs_trans/exte_dom/N2MF_cat/ih.

    have phin_coin: forall n, (phin n) \and phi \coincide_on (list_dom N (KL n)).
    - elim => // n /coin_agre ih /=.
      have prp': (phin n.+1) \and phi \coincide_on (mu (phin n) q').
        by apply sfprp => q /lstd_spec; apply/ih.
      have [sze _]:= (sfprp (KL n)).
      rewrite /KL_step lstd_cat.
      apply/coin_cat; split.
      + apply/coin_subl; first by apply/lstd_zip.
        by rewrite unzip1_zip; last by rewrite sze.        
      apply/coin_agre => q lstn.
      case E: (q \in (mu (phin n) q')).
      + by move /coin_agre: prp' => -> //; apply/inP; rewrite E.
      move: E; rewrite /phin /= /KL_step {2}/extend N2LF_cat /=.
      move: (sf (KL n)).
      elim: (mu (extend default (N2LF N (KL n))) q') => [sfKL _ | a L ih' sfKL lstn'].
      + by rewrite zip_nill /=; apply/ih.
      case: (sfKL) => [ | a' L']; first by rewrite zip_nilr; apply/ih.
      rewrite /= N2LF_cons.
      move: lstn'; rewrite in_cons => /orP /not_or_and [neq nin].
      case: ifP => [/eqP eq| _]; first by exfalso; apply/neq; rewrite eq.
      by apply/ih'/negP.

    have KL_subs: forall n m, n <= m -> (list_dom N (KL n)) \is_sublist_of (list_dom N (KL m)).
    - move => n m /subnK <-.
      elim: (m - n) => // k ih.
      rewrite addSn /= lstd_cat => q lstn.
      by apply/lstn_app; right; apply/ih.
      
    have phinm_coin: forall n m, n <= m -> (phin m) \and phi \coincide_on (list_dom N (KL n)).
    - move => n m /subnK <-.
      elim: (m - n) => [ | k ih]; first by rewrite add0n; apply/phin_coin.
      by rewrite addSn; apply/coin_subl/phin_coin/KL_subs; rewrite -addSn; apply/leq_addl.

    have [psi lim]: exists psi, psi \is_limit_of phin.   
    - suff /choice [psi psiprp]: forall q, exists a, exists n, forall m, n <= m -> a = phin m q.
      + exists psi; apply/lim_coin; elim => [ | q K [n nprp]]; first by exists 0.
        have [k kprp]:= psiprp q.
        exists (maxn n k) => m; rewrite geq_max => /andP [ineq ineq'].
        by split; [apply/kprp/ineq' | apply/nprp/ineq].
      move => q.        
      case: (classic (exists n, q \from dom (N2MF N (KL n)))) => [[n /lstd_spec fd] | ].
      + exists (phin n q); exists n => m ineq.
        have /coin_agre ->:= phinm_coin n m ineq => //.
        by have /coin_agre ->:= phinm_coin n n (leqnn n).
      move => /not_ex_all_not nex.
      exists default; exists 0 => m _.
      suff : N2LF N (KL m) q = nil by rewrite /phin/=/extend/= => ->.
      case E: (N2LF N (KL m) q) => [ | a L] //.
      exfalso; apply/(nex m).
      by exists a; rewrite /N2MF /= E; left.

    have /cont_F2MF/cont_scnt scnt : mu \is_continuous_function.
    - move => phi'; exists (mu phi') => q'1 psi1 coin.
      have /modf_spec modmod' := modmod.
      by symmetry; apply/crt_icf; [ | apply/modmod' | apply/coin | ].

    have/lim_coin lim': mu psi \is_limit_of (fun n => mu (phin n)) by apply/scnt; [apply/lim | | ].

    have eq: mu phi q' = mu psi q'.
    - suff coin : psi \and phi \coincide_on (mu psi q').
      + by have /modf_spec modmod' := modmod; apply/crt_icf; [ | apply/modmod' | apply/coin | ].
      have [k kprp]:= lim' [:: q'].
      have [ | -> _] //:= kprp k.
      have /lim_coin lim'' := lim.
      have [k' k'prp]:= lim'' (mu (phin k) q').
      apply/coin_trans; first exact/(k'prp (maxn k.+1 k'))/leq_maxr.      
      apply/coin_subl/phinm_coin/leq_maxl => q lstn.
      apply/lstd_spec.
      by apply sfprp.

    have [k lmt]:= lim' [:: q'].
    have eq': L2SS (mu (phin k.+1) q') \is_subset_of dom (N2MF N (KL k.+1)).
    have [ | <- _]// := lmt k.+1.
    have [ | -> _]// := lmt k.
    exact/phin_dom.

    pose s := fix s n:= match n with
                        | 0 => nil
                        | S n => sf (KL n) :: s n
                        end.
    have crct: forall k, KL_rec (s k) q' = KL k.
    - by elim => // k' ih; rewrite /= ih.
    have crct': forall k, phi_rec (s k) q' = phin k.
    - by case => //k'; rewrite /phi_rec/= crct.
    exists (s k.+1).
    rewrite crct crct' eq; split => //.
    have [ | -> _]//:= lmt k.
    apply/coin_subl/coin_sym/phinm_coin/leqnn.
    by rewrite lstd_spec; apply/phin_dom.
  Qed.
 
  Definition apply_to_machine nq':=
    let n := nq'.1 in
    let q':= nq'.2 in
    let s:= inverse_pickle [::] n in
    let phi := phi_rec s q' in
    if check_sublist (mu phi q') (list_dom N (KL_rec s q'))
    then Some (f phi q')
    else None.

  Hypothesis mod: mu \modulus_function_for f.

  Lemma appN_icf phi:
    phi \is_choice_for (\Phi_N) -> (f phi) \is_choice_for \Phi_apply_to_machine.
  Proof.
    move => icf q' [a' val].
    have [s [coin ]]:= phi_rec_spec q' icf.
    rewrite -lstd_spec => /clP cl.
    exists (pickle s).
    rewrite /apply_to_machine /inverse_pickle pickleK_inv cl.
    have /modf_spec mod' := mod.
    by f_equal; apply/crt_icf; try apply/mod'; try apply/coin.
  Qed.

  Lemma appN_sing:
    \Phi_N \is_singlevalued -> \Phi_apply_to_machine \is_singlevalued.
  Proof.
    rewrite /apply_to_machine => sing q' a a' [n].
    case: ifP => // /clP subl [<-] [n'].
    case: ifP => // /clP subl' [<-].
    move: subl subl'.
    set s := inverse_pickle [::] n.
    set s' := inverse_pickle [::] n'.
    move => subl subl'.
    pose phi := extend default (N2LF N (KL_rec s q' ++ KL_rec s' q')).
    have /modf_spec mod' := mod.
    apply/(@eq_trans _ _ (f phi q')).
    - symmetry; apply/crt_icf; [ | apply/mod' | | ] => //.    
      apply/coin_agre => q lstn.
      apply/sing; apply/N2MF_spec/extend_spec; first exact/lstd_spec/subl.
      by apply/lstd_spec; rewrite lstd_cat; apply/lstn_app; left; apply/subl.
    apply/crt_icf; [ | apply/mod' | | ] => //.    
    apply/coin_agre => q lstn.
    have /lstd_spec [b val]:=subl' q lstn.
    apply/sing; apply/N2MF_spec/extend_spec; first exact/lstd_spec/subl'.
    by apply/lstd_spec; rewrite lstd_cat; apply/lstn_app; right; apply/subl'.
  Qed.
    
  Lemma appN_spec phi:
    F2MF phi =~= \Phi_N -> F2MF (f phi) =~= \Phi_apply_to_machine.
  Proof.
    move => eq q' a'; split => [<- | val /=].
    - have [q qfd | s [coin ]]:= @phi_rec_spec phi q'; first exact/eq.
      rewrite /= /apply_to_machine -lstd_spec => /clP cl.
      exists (pickle s).
      rewrite /inverse_pickle pickleK_inv cl.
      f_equal; have /modf_spec mod' := mod.
      apply/crt_icf; [ | apply/mod' | apply/coin | ] => //.
    apply/appN_sing/val; first by rewrite -eq; apply/F2MF_sing.
    apply/appN_icf => [q qfd' | ]; last by exists a'.
    exact/eq.
  Qed.
End function_application.

Section Baire_subset.
  Context (A Q: Type).
  Notation B := (Q -> A).
  Local Notation "Q ~> A" := (nat * Q -> option A) (at level 2).

  Definition phi (N: Q ~> A) := make_subset (fun phi => forall L, exists n,
                                         forall q, q \from L2SS L -> N(n,q) = some (phi q)).

  Local Notation "\phi_ N" := (phi N) (format "'\phi_' N", at level 2).

  Lemma cls_Phi N: closure \phi_N \is_subset_of \phi_N.
  Proof.
    move => phi phifc L.
    have [psi [/coin_agre agre val]]:= phifc L.
    have [n prp]:= val L.
    exists n => q lstn.
    by rewrite prp //; f_equal; symmetry; apply/agre.
  Qed.
End Baire_subset.