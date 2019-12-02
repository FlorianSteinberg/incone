(* This file provides an abstract envelope for computability theoretical considerations *)
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype choice seq.
From mf Require Import all_mf.
Require Import iseg sets graphs smod cont seq_cont search.
Require Import ClassicalChoice ConstructiveEpsilon.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Phi_assignment.
  Context (fuel A Q: Type).
  Notation B := (Q -> A).
  Local Notation "Q ~> A" := (fuel * Q -> option A) (at level 2).
    
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
End Phi_assignment.
Notation "\Phi_ N" := (Phi N) (format "'\Phi_' N", at level 2).

Section choice.
  Context (A Q: Type) (fuel: choiceType).
  Notation B := (Q -> A).
  Local Notation "Q ~> A" := (fuel * Q -> option A) (at level 2).

  Definition cost_dep (N: Q ~> A): \Phi_N \is_total -> forall q, {f | N (f, q)}.
    move => tot q.
    suff ex: exists f: fuel, N (f, q).
    exists (xchoose ex); apply/(xchooseP ex).
    by have [a [f val]]:= (tot q); exists f; rewrite val.
  Defined.

  Definition cost N (tot: \Phi_N \is_total) q:= sval (cost_dep tot q).
  Lemma cost_spec N (tot: \Phi_N \is_total) q: N (cost tot q, q).
  Proof. exact/(svalP (cost_dep tot q)). Qed.
      
  Lemma tot_choice (N: Q ~> A): \Phi_N \is_total -> {phi | \Phi_N \extends (F2MF phi)}.
  Proof.
    move => tot.
    suff f q: {a | N (cost tot q, q) = Some a}. 
    - by exists (fun q => sval (f q)) => q _ <-; exists (cost tot q); apply/(svalP (f q)).
    by have:= (cost_spec tot q); case eq: N => [a | ] //; exists a.
  Qed.

  Definition evaluate (N: Q ~> A): \Phi_N \is_total -> Q -> A.
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
End choice.

Section monotonicity.
  Context (A Q: Type).
  Notation B := (Q -> A).
  Local Notation "Q ~> A" := (nat * Q -> option A) (at level 2).
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
	\Phi_N \tightens phi <-> \Phi_N \extends phi.
  Proof. by move => mon sing; apply/sing_eval/sing/mon_sing. Qed.

  Lemma mon_eval_F2MF N phi: N \is_monotone ->
                             \Phi_N \tightens (F2MF phi) <-> \Phi_N \extends F2MF phi.
  Proof. by move => mon; apply/mon_eval_sing/F2MF_sing. Qed.
End monotonicity.

Lemma ovrt_po (Q A: eqType) (D: mf_set.subset (Q -> A)):
  overt D ->
  exists (N: nat * seq (Q * A) -> option (Q -> A)),
    dom \Phi_N === dom (projection_on D) /\ (projection_on D) \extends \Phi_N.
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

  Definition use_first (nq: nat * Q):=
    let (n,q) := nq in
    search (fun k => N (k,q)) (cnst true) n.

  Lemma sfrst_osrch n q:
    use_first (n, q) = N (ord_search (fun k => N (k, q)) n, q).
  Proof. by rewrite /use_first/search dsrch_osrch /=; case: N. Qed.
        
  Lemma sfrst_mon: use_first \is_monotone.
  Proof.
    move => q n.
    case eq: use_first => [a' | ]// _.
    exact/srch_eq/eq.
  Qed.

  Lemma sfrst_sing: \Phi_use_first \is_singlevalued.
  Proof. exact/mon_sing/sfrst_mon. Qed.

  Lemma sfrst_spec: \Phi_use_first \tightens \Phi_N.
  Proof.
    have mon:= @sfrst_mon.
    rewrite tight_spec.
    split => [q [a [n eq]] | q a [_ [n]]]; last first.
    - by rewrite sfrst_osrch; exists (ord_search (fun k => N(k,q)) n).
    have: is_true (isSome (N (ord_search (fun k => N(k,q)) n, q))).
    * by apply/(@osrch_correct (fun k => N(k,q))); rewrite eq.
    by case E: (N (ord_search (fun k => N(k,q)) n, q)) => [b | ] //_; exists b; exists n; rewrite sfrst_osrch.
  Qed.

  Lemma sfrst_tot: \Phi_N \is_total <-> \Phi_use_first \is_total.
  Proof.
    split=> tot q'; have [a'[n]]:= tot q'; last first.
    - by rewrite sfrst_osrch; exists a'; exists (ord_search(fun k=>N (k, q'))n).
    move => eq; have: N (ord_search (fun k => N (k, q')) n, q').
    - by apply/(@osrch_correct (fun k => N (k, q'))); rewrite eq.
    case E: (N (ord_search (fun k => N (k, q')) n, q')) => [b' | ] // _.
    by exists b'; exists n; rewrite sfrst_osrch.
  Qed.
    
  Lemma mon_sfrst: N \is_monotone <-> forall n q, N(n,q) = use_first(n,q).
  Proof.
    split => [/mon_spec mon n q | eq n m neq]; last by rewrite eq sfrst_mon -eq.
    rewrite sfrst_osrch.
    case E: (N (ord_search (fun k => N(k,q)) n, q)) => [a | ].
    - apply/mon; last exact/E.
      exact/osrch_le.
    have := @osrch_le (fun k => N(k,q)) n.
    rewrite leq_eqVlt => /orP [/eqP <- | /osrch_ltP [[/=m mln] Nmq]] //.
    have:= @osrch_correct (fun k => N(k,q)) _ Nmq.
    have -> := @osrch_eq (fun k => N(k,q)) m n _; first by rewrite E.
    - exact/(@osrch_correct (fun k => N (k,q))).
    by case: (m) mln => // m' m'ln; apply/leq_trans/m'ln.
  Qed.
    
  Lemma sing_sfrst: \Phi_N \is_singlevalued <-> \Phi_N =~= \Phi_use_first.
  Proof.
    split => [sing q a| ->]; last exact/sfrst_sing.
    split => [[n val] | [n]]; last by rewrite sfrst_osrch; exists (ord_search (fun k => N(k,q)) n).
    exists n; rewrite sfrst_osrch.
    have Nnq: N(n,q) by rewrite val.
    have := (@osrch_correct (fun k => N(k,q)) n Nnq).
    case E: (N(_, q)) => [b | ] // _.
    have ->:= sing q a b => //; first by exists n.
    by exists (ord_search (fun k => N(k,q)) n).
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
    case: (@pickle_inv _ n) => // [[m k]]; case E: (N'(m,q)) => [a |]// eq.
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

Section finite_approximations.
  Context Q A (N: nat * Q -> option A) (default: A).

  Definition phi_ n q := if N (n, q) is Some a then a else default.
  
  Fixpoint check_dom K n :=
    match K with
    | nil => true
    | q :: K' => N (n, q) && check_dom K' n
    end.

  Lemma cdP (K: seq Q) n:
    reflect (K \is_subset_of dom (pf2MF (curry N n))) (check_dom K n).
  Proof.
    apply/(iffP idP).
    - elim: K => [_ q | q K ih /andP [val /ih subs]] //=.
      apply/cons_subs; split => //; move: val; case eq: N => [a | ]// _.
      by exists a; rewrite /= /curry eq.
    elim: K => // q K ih /cons_subs [[a /=eq] /ih subs].
    by apply/andP; split; try by move: eq; rewrite /curry; case: N.
  Qed.

  Hypothesis mon: monotone N.
  
  Local Open Scope name_scope.
  Lemma icf_lim phi:
    \Phi_N \is_total -> phi \is_choice_for (\Phi_N) <-> phi \is_limit_of phi_.
  Proof.
    have /mon_spec mon' := mon.
    move => tot; split => [icf q | lim q qfd].
    - have [n eq]:= icf q (tot q).
      exists n => m ineq.
      by rewrite /phi_ (mon' q _ _ _ ineq eq) //.
    have [n nprp] := lim q.
    have [a [m mprp]] := tot q.
    exists (maxn n m).
    have := nprp (maxn n m) (leq_maxl n m).
    by rewrite /phi_ (mon' q _ _ _ (leq_maxr n m) mprp) => <-.
  Qed.
  
  Lemma phinS n: (phi_ n) \agrees_with phi_ n.+1 \on (dom (pf2MF (curry N n))).
  Proof.
    move => q [a val]; rewrite /phi_ mon //.
    by move: val; rewrite /= /curry; case: N.
  Qed.

  Lemma phin_agre n m: n <= m -> (phi_ n) \agrees_with (phi_ m) \on (dom (pf2MF (curry N n))).
  Proof.
    move => /subnK <-; elim: (m - n) => // k ih.
    rewrite addSn; apply/agre_trans/agre_subs/phinS => //.
    rewrite /curry => q [a] /=; case eq: N => [a' | ]// eq'.
    exists a; have /mon_spec mon' := mon.
    by rewrite (mon' _ _ _ _ _ eq); try apply/leq_addl.
  Qed.

  Lemma mon_eq q n m a b:
    N (n, q) = Some a -> N (m, q) = Some b -> a = b.
  Proof.
    move => eq eq'; have/mon_spec mon' := mon.
    case/orP: (leq_total n m) => ineq; first by have := mon' q _ _ _ ineq eq; rewrite eq'; case.
    by have := mon' q _ _ _ ineq eq'; rewrite eq; case.
  Qed.
  
  Lemma icf_phin phi:
    phi \is_choice_for (\Phi_N) -> forall n, phi \is_choice_for (pf2MF (curry N n)).
  Proof.
    rewrite /curry => icf n q [a /=].
    case eq: N => [a' | ]// eq'.
    have [ | m val]:= icf q; first by exists a'; exists n.
    exact/mon_eq/val/eq.
  Qed.

  Lemma cdS n K: check_dom K n -> check_dom K n.+1.
  Proof.
    move => /cdP subs.
    apply/cdP => q lstn.
    have [a val]:= subs q lstn.
    rewrite /= /curry mon; first by exists a.
    by move: val; rewrite /= /curry; case: N.
  Qed.
End finite_approximations.

Section EnumeratedTypes.
  Structure EnumeratedType :=
    {
      type:> Type;
      enumeration: nat * nat -> option type;
      surjective: \Phi_enumeration \is_cototal;
      deterministic: \Phi_enumeration \is_singlevalued;
    }.
     
  Context (T: EnumeratedType).

  Definition find (p: pred T) (n: nat):=
    match direct_search
            (enumeration T \o_p unpickle)
            (fun ot => if ot is Some t then p t else false) n with
    | Some (Some t) => Some t
    | _ => None
    end.

  Lemma find_correct (p: pred T) n x: find p n = Some x -> p x.
  Proof.
    rewrite /find.
    case E: direct_search => [ot |] //.
    have := (@dsrch_correct (option T) (enumeration T \o_p unpickle) _ _ _ E).
    by case: ot E => // t E pt [<-].
  Qed.
End EnumeratedTypes.
