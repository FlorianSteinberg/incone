(* This file provides an abstract envelope for computability theoretical considerations *)
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype choice.
From mf Require Import all_mf.
Require Import iseg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Phi_assignment.
  Context (A Q: Type).
  Notation B := (Q -> A).
  Local Notation "Q ~> A" := (nat -> Q -> option A) (at level 2).

  Definition Phi (N: Q ~> A):= make_mf (fun q a => exists n, N n q = Some a).

  Local Notation "\Phi_ N" := (Phi N) (format "'\Phi_' N", at level 2).

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
  Proof. done. Qed.
  
  Definition monotone_in (N: Q ~> A) q := forall n, N n q <> None -> N n.+1 q = N n q.
  
  Lemma mon_in_spec (N: Q ~> A) q: monotone_in N q <->
	  forall a n m, n <= m -> N n q = Some a -> N m q = Some a.
  Proof.
    split => [mon a' n m | mon n neq]; last by case E: (N n q) neq=>[a | ]// _; apply/mon/E. 
    elim: m => [ineq eq | m ih]; first by have/eqP <-: n == 0 by rewrite -leqn0.
    rewrite leq_eqVlt; case/orP => [/eqP <- | ineq eq]//.
    by rewrite mon => //; rewrite ih; rewrite /pickle /=.
  Qed.

  Lemma mon_in_eq N q n m a b:
    monotone_in N q -> N n q = Some a -> N m q = Some b -> a = b.
  Proof.
    case/orP: (leq_total n m) => ineq /mon_in_spec mon eq eq'; apply /Some_inj.
      by rewrite -eq'; symmetry; apply/mon/eq.
    by rewrite -eq; apply/mon/eq'.
  Qed.

  Definition monotone N:= forall q, monotone_in N q.
  Local Notation "N '\is_monotone'" := (monotone N) (at level 2).

  Lemma mon_spec (N: Q ~> A): N \is_monotone <->
                              forall q a n m, n <= m -> N n q = Some a -> N m q = Some a.
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
  
  Definition use_first (N: Q ~> A) n q:= N (search (fun k => N k q) n) q.
  Lemma use_first_spec N: (use_first N) \is_monotone /\ \Phi_(use_first N) \tightens \Phi_N.
  Proof.
    suff mon: (use_first N) \is_monotone => [ | q n neq].
    - split => //; rewrite tight_spec.
      split => [q [a [n eq]] | q a [_ [n eq]]]; last by exists (search (fun k => N k q) n).
      have: is_true (isSome (N (search (fun k => N k q) n) q)).
      * by apply/(@search_correct (fun k => N k q)); rewrite eq.
      by case E: (N (search (fun k => N k q) n) q) => [b | ] //_; exists b; exists n.
    rewrite /use_first.
    f_equal; symmetry.
    rewrite -search_search.
    apply/search_eq .
    move: neq; rewrite /use_first.
    by case: (N (search (fun k => N k q) n) q).
    by apply/leq_trans; first exact/search_le.
  Qed.
End Phi_assignment.
Notation "\Phi_ N" := (Phi N) (format "'\Phi_' N", at level 2).

Section composition.
  Context Q A D (N: nat -> A -> option D) (N': nat -> Q -> option A).
  
  Definition Phi_comp n (q: Q) :=
    match @pickle_inv _ n with
    | None => None
    | some mk => match (N' mk.1 q) with
                 | None => None
                 | some a => N mk.2 a
                 end
    end.

  Lemma Phi_rcmp_spec:
    \Phi_Phi_comp =~= \Phi_N \o_R \Phi_N'.
  Proof.
    rewrite/Phi_comp => q d.
    split => [[n] | [a [[m eq] [k eq']]]]; last by exists (pickle (m,k)); rewrite pickleK_inv eq.
    case: (pickle_inv _ n) => // [[m k]]; case E: (N' m q) => [a |]// eq.
    by exists a; split; [exists m | exists k].
  Qed.

  Lemma Phi_comp_spec: \Phi_Phi_comp \tightens (\Phi_N \o \Phi_N').
  Proof. by rewrite Phi_rcmp_spec; apply/rcmp_tight. Qed.

  Definition Phi_mon_comp n (q: Q) :=
    match (N' n q) with
    | None => None
    | some a => N n a
    end.

  Lemma Phi_mcmp_mon: monotone N -> monotone N' -> monotone Phi_mon_comp.
  Proof.
    rewrite /Phi_mon_comp => mon mon' n q neq.
    by rewrite mon'; case: (N' q n) neq => // a; apply/mon.
  Qed.
    
  Lemma Phi_mcmp_spec: monotone N -> monotone N' -> \Phi_Phi_mon_comp =~= \Phi_N \o \Phi_N'.
  Proof.
    rewrite /Phi_mon_comp => mon mon'; rewrite sing_rcmp; last by apply/mon_sing.
    move: mon mon' => /mon_spec mon /mon_spec mon' q d; split => [[n] | [a [[n' eq'] [n eq]]]].
    - by case E: (N' n q) => [a | ]// eq; exists a; split; exists n.
    by exists (maxn n n'); rewrite (mon' _ _ _ _ _ eq'); [apply/mon/eq/leq_maxl | exact/leq_maxr].
  Qed.
End composition.