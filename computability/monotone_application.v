(* This file provides an abstract envelope for computability theoretical considerations *)
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype choice seq bigop.
From mf Require Import all_mf.
Require Import all_cont search seq_cont PhiN.
Require Import ClassicalChoice ConstructiveEpsilon.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section monotone_application.
  (** 
     This section realizes function application on the level of specifications. That is: given a
     functional f of type (Q -> A) -> (Q' -> A') and a sequentially continuous modulus of
     continuity of this functional. It is possibe to construct an operation "apply_to_machine"
     that produces from a specification N of possible inputs (in the sense that phi is a possible
     input if it chooses through Phi_N) a specification of the return values. This only works if
     Phi_N is total and gives a full specification if Phi_N is singlevalued. In general one can    
     only obtain an underspecification.   
     From the single-valued case we restrict further to monotone case is considerably less
     involved. Notably, the prove that the specification of the return-values is monotone again
     needs a stronger assumption about the continuity of mu: we assume it to be self-modulating.
     The second section proves that an exact specification in the multivalued case is not possible
     to obtain.
   **)

  Local Open Scope name_scope.
  Context (Q A A' Q': Type) (default: A). 
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Context (f: B -> B').
  Context (mu: B -> Q' -> seq Q).
  Notation subset T := (mf_set.subset T).
  Hypothesis scnt: (F2MF mu) \is_sequentially_continuous.
  
  Context (N: nat * Q -> option A).

  Hypothesis (mon: monotone N).
  Notation phin := (phi_ N default).
  
  Definition apply_to_monotone_machine (nq': nat * Q'):=
    let (n, q') := nq' in
    if check_dom N (mu (phin n) q') n
    then Some (f (phin n) q')
    else None.

  Hypothesis mod: mu \modulus_function_for f.   
  Hypothesis mu_dom: forall n q', mu (phin n) q' \is_subset_of dom \Phi_N.
  Hypothesis tot: \Phi_N \is_total.
  
  Lemma apmm_tot_spec phi:
    phi \is_choice_for (\Phi_N) -> (F2MF (f phi)) =~= \Phi_apply_to_monotone_machine.
  Proof.
    move => icf q' a'; split => [<- | [n /=]]; last first.
    - case: ifP => // /cdP cd [<-].
      symmetry.
      apply/mod/coin_agre/agre_subs; first exact/cd.
      move => q qfd.
      have /icf [m eq]: q \from dom \Phi_N.
      + case: qfd => a val; exists a; exists n.
        by move: val; rewrite /curry /=; case eq: N => [b' | ] // ->.
      have /mon_spec mon' := mon.
      case/orP: (leq_total n m) => ineq; last by rewrite /phi_; have ->// := mon' q _ _ n _ eq.
      rewrite /phi_; case eq': N => //; first by have := mon' q _ _ m ineq eq'; rewrite eq; case.
      by have [a /=]:= qfd; rewrite /curry eq'.
    have /icf_lim lim:= icf.
    have lmt: mu phi \is_limit_of (fun n => mu (phin n)) by apply/scnt; first exact/lim.
    have [n nprp] := lmt q'.
    have /mon_spec mon' := mon.
    have [m mprp]: exists n, forall q, q \from mu phi q' -> N (n, q) = Some (phi q).
    - elim: (mu phi q') => [ | q K [k ih]]; first by exists 0.
      have [k' val']:= icf q (tot q).
      exists (maxn k k') => q0 /= [<- | lstn]; first by apply/mon'; first exact/leq_maxr.
      by apply/mon'/ih; first exact/leq_maxl.
    exists (maxn n m).
    rewrite /=.
    rewrite -nprp; last exact/leq_maxl.
    case: ifP => [/cdP subs | /cdP fls]; last first.
    - exfalso; apply/fls => q qfd; exists (phi q) => /=.
      by rewrite /curry /= (mon' q (phi q) _ _ (leq_maxr n m)); last exact/mprp.
    f_equal.
    symmetry.
    apply/mod/coin_agre => q qfd.
    rewrite /phi_ (mon' q (phi q) _ _ (leq_maxr n m))//; last exact/mprp.
  Qed.
  
  Lemma apmm_mon:
    mu \modulus_function_for mu -> monotone apply_to_monotone_machine.
  Proof.
    move => modmod q' n /=; case: ifP => // /cdP subs _.
    rewrite -(@modmod (phin n)); last exact/coin_agre/agre_subs/phinS.
    rewrite cdS //; last exact/cdP.
    by symmetry; f_equal; apply/mod/coin_agre/agre_subs/phinS.
  Qed.
End monotone_application.

Section limitations.
  (**
     This part considers a counterexample that proves that using Phi_N a full specification of
     application can not be achieved in the case of multivaluedness whenever A and Q' are
     properly infinte and A' has at least two elements. That is in particular in the case where
     f is a function from the natural numbers to cantor space. This is done by proving that any
     set of functions that choose through some \Phi_N is a closed set while there exists a
     continuous operator that does not map every such set to a closed set.
     We interpret the desired specification as follows: We are looking for some function mapp
     that takes an f, a modulus mu of f and an N and returns something that describes the value-
     sets of f on the inputset described by N, i.e. such that
     {f phi | phi \is_choice_for \Phi_N} = {fphi | fphi \is_choice_for \Phi_(mapp f mu N)}.
     We only require this to work for N that are total so that it is not partiality issues that
     make a problem here.
     We roughly proceed by first showing that the sets as above are always closed and pointing out
     that there exists a continuous operator whose image is not closed.
   **)
  Local Open Scope name_scope.
  Definition D Q A (N: nat * Q -> option A) := make_subset (fun phi => phi \is_choice_for \Phi_N).

  Lemma PhiN_clsd Q A (N: nat * Q -> option A): closed (D N).
  Proof.
    apply/clsd_subs => phi /= clsr q qfd.
    by have [psi [[-> _] icf]]:= clsr [:: q]; apply/icf.
  Qed.
    
  Definition f phi n := if n <= phi tt then false else true.

  Lemma not_clsd_codom_f: ~ closed (codom (F2MF f)).
  Proof.
    move => clsd.
    suff [phi /= eq]: cnst false \from codom (F2MF f).
    - have prp: forall q, f phi q = false by rewrite eq.
      by have := prp (phi tt).+1; rewrite /f ltnn.
    apply/clsd => K.
    exists (fun n => if n <= \max_(m <- K) m then false else true).
    split; last by exists (cnst (\max_(m <- K) m)).
    apply/coin_agre => q lstn.
    case: ifP => // /leP fls.
    by exfalso; apply/fls/leP/leq_bigmax.
  Qed.

  Lemma modf_f:
    (fun phi n => [::tt]) \modulus_function_for f.
  Proof. by rewrite /f => phi n psi [] <-. Qed.

  Lemma appN_Phi_not_sufficient:
    ~ exists machine_application,
        forall (f: (unit -> nat) -> (nat -> bool)) mu, mu \modulus_function_for f ->
                     forall N, \Phi_N \is_total ->
                               D (machine_application f mu N) === img (F2MF f) (D N).
  Proof.
    move => [mapp mapp_prp].
    apply/not_clsd_codom_f.
    pose mu (phi: unit -> nat) (n: nat):= [::tt].
    pose N (ntt: nat * unit) := Some ntt.1.
    have tot: \Phi_N \is_total by exists 0; exists 0.
    suff eq:
      codom (F2MF f) === (make_subset (fun fphi => fphi \is_choice_for (\Phi_(mapp f mu N)))).
    - apply/clsd_prpr; first exact/eq.
      by have := PhiN_clsd (mapp f mu N).
    move => fphi.
    split => [[phi <-] | /= icf].
    - apply/mapp_prp; try exact/tot; try exact/modf_f.
      by exists phi; split => // s _; exists (phi tt); case: s.
    by have [s [<- _]]:= (mapp_prp f mu modf_f N tot fphi).1 icf; exists s.
  Qed.
End limitations.
