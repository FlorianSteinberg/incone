(* This file provides an abstract envelope for computability theoretical considerations *)
From mathcomp Require Import all_ssreflect.
From mf Require Import all_mf.
Require Import all_cont search PhiN monotone_application FMop seq_cont continuous_machines.
Require Import axioms Classical Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section monotone_machine_application.
  (**
     This section reiterates the results from the file "multivalued_application" in a slightly
     more general setting, i.e. if the functional that should be applied is not concretely given
     but only specified through the operator assignment.
   **)
  Local Open Scope name_scope.
  Context (Q A A' Q': Type) (default: A). 
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Context (N: nat * Q -> option A).
  Context (M: B -> nat * Q' -> option A').
  Context (mu: B -> nat * Q' -> seq Q).
  Hypothesis mod: mu \modulus_function_for M.
  Hypothesis modmod: mu \modulus_function_for mu.
  Hypothesis (N_mon: PhiN.monotone N).
  Hypothesis (M_mon: M \is_monotone).

  Definition monotone_machine_application (nq': nat * Q'):=
    let (n, q') := nq' in
    if check_dom N (mu (phi_ N default n) (n,q')) n
    then M (phi_ N default n) (n, q')
    else None.

  Hypothesis tot: \Phi_N \is_total.

  Lemma scnt: (F2MF mu) \is_sequentially_continuous.
  Proof. by apply/cont_scnt/cont_F2MF => phi; exists (mu phi); apply/modmod. Qed.
      
  Hypothesis mu_term: terminates_with M mu.
  
  Lemma mu_subl phi q' n m: M phi (n, q') -> n <= m -> (mu phi (m, q')) \is_sublist_of (mu phi (n, q')).
  Proof.
    move => val /subnK <-; elim: (m - n) => // k ih.
    rewrite addSn; apply/subs_trans/ih/mu_term.
    move: val; case val: M => [a | ]// _.
    have /mon_spec mon' := M_mon.
    by rewrite (mon' _ _ _ _ _ _ val) //; apply/leq_addl.
  Qed.

  Lemma mmap_tot_spec phi: phi \is_choice_for (\Phi_N) ->
        \Phi_(M phi) =~= \Phi_monotone_machine_application.
  Proof.
    have /mon_spec mon' := M_mon => icf q' a'.
    have /PhiN.mon_spec mon'' := N_mon.
    split => [[n val] | [n ]]; last first.
    - simpl; case : ifP => // /cdP subs eq.
      exists n; rewrite -(@mod (phi_ N default n)) //.
      apply/coin_agre/agre_subs => [ | q qfd]; first exact/subs.
      have := icf_phin N_mon icf (n:= n) qfd.
      by rewrite /curry /phi_ /=; case: N => //.
    rewrite /=.
    have [prp _]:= apmm_tot_spec default scnt N_mon mod tot icf (n, q') (Some a').    
    have [m eq] := prp val.
    exists (maxn n m).
    move: eq; rewrite /=.
    case: ifP => // /cdP subs [<-].    
    suff ->: check_dom N (mu (phi_ N default (maxn n m))
                             (maxn n m , q')) (maxn n m).
    - move: val.
      rewrite -(@mod (phi_ N default m)) => [val | ]; last first.
      - apply/coin_agre => q qfd.
        suff: phi q \from (pf2MF (curry N m) q) by rewrite /curry /phi_ /=; case: N.
        exact/icf_phin/subs.
      have := (mon' _ _ _ _ _ (leq_maxl n m) val).
      rewrite -(@mod (phi_ N default m)) //; first by move => ->.
      apply/coin_agre/agre_subs/phin_agre/leq_maxr => //.
      by apply/subs_trans/subs/mu_subl/leq_maxl; rewrite val.
    apply/cdP.
    have coin: (phi_ N default m) \coincides_with phi \on (mu (phi_ N default m) (n, q')). 
    - apply/coin_agre/agre_subs => [ | q qfd]; first exact/subs.
      by have := icf_phin (n := m) N_mon icf qfd; rewrite /curry/phi_ /=; case: N.
    rewrite -(@modmod (phi_ N default m)).
    - apply/subs_trans; first apply/mu_subl/leq_maxl.
      + by rewrite (@mod _ _ phi) //; first by rewrite val.
      apply/subs_trans; first exact/subs; rewrite /curry => q [a vl /=]; exists a.
      case vl: N vl =>/=; case vl': N => [b | ] //; first by move => <-; apply/PhiN.mon_eq/vl'/vl.
      by move: vl; have ->:= (mon'' _ _ _ _ (leq_maxr n m) vl').
    apply/coin_agre/agre_subs/phin_agre/leq_maxr => //.
    apply/subs_trans/subs; first apply/mu_subl/leq_maxl.
    by rewrite (@mod _ _ phi) //; first by rewrite val.
  Qed.

  Lemma mmap_mon: PhiN.monotone monotone_machine_application.
  Proof.
    move => q' n /=.
    case: ifP => [/cdP subs | ] // val; rewrite cdS //.
    - rewrite -(M_mon val); symmetry; apply/mod/coin_agre/agre_subs/phinS/N_mon.
      by apply/subs_trans; first by apply/mu_term; case: M val.
      apply/cdP/subs_trans/subs.
    rewrite -(@modmod (phi_ N default n)); first by apply/mu_term; case: M val.
    apply/coin_agre/agre_subs/phin_agre => //.
    by apply/subs_trans/subs/mu_term; case: M val.
  Qed.    
End monotone_machine_application.

Section monotone_machine_application_Q_default.
  (**
     This section reiterates the results from the file "multivalued_application" in a slightly
     more general setting, i.e. if the functional that should be applied is not concretely given
     but only specified through the operator assignment.
   **)
  Local Open Scope name_scope.
  Context (Q A A' Q': Type) (someq: Q). 
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Context (N: nat * Q -> option A).
  Context (M: B -> nat * Q' -> option A').
  Context (mu: B -> nat * Q' -> seq Q).
  Hypothesis mod: mu \modulus_function_for M.
  Hypothesis modmod: mu \modulus_function_for mu.
  Hypothesis (N_mon: PhiN.monotone N).
  Hypothesis (M_mon: M \is_monotone).

  Definition monotone_machine_application_Qdefault (nq': nat * Q'):=
    let (n, q') := nq' in
    if N (n, someq) is Some default
    then if check_dom N (mu (phi_ N default n) (n,q')) n
         then M (phi_ N default n) (n, q')
         else None
    else None.

  Hypothesis tot: \Phi_N \is_total.
  
  Hypothesis mu_term:
    forall phi q' n, M phi (n, q') -> (mu phi (n.+1, q')) \is_sublist_of (mu phi (n, q')).
  
  Lemma mmapQ_tot_spec phi: phi \is_choice_for (\Phi_N) ->
        \Phi_(M phi) =~= \Phi_monotone_machine_application_Qdefault.
  Proof.
    have /mon_spec mon' := M_mon => icf q' a'.
    have /PhiN.mon_spec mon'' := N_mon.
    split => [[n val] | [n ]]; last first.
    - rewrite /=.
      case def: N => [default | ] //; case : ifP => // /cdP subs eq.
      exists n; rewrite -(@mod (phi_ N default n)) //.
      apply/coin_agre/agre_subs => [ | q qfd]; first exact/subs.
      have := icf_phin N_mon icf (n:= n) qfd.
      by rewrite /curry /phi_ /=; case: N => //.
    rewrite /=.
    have [default [k def]]:= tot someq.
    have [prp _]:= apmm_tot_spec default (scnt modmod) N_mon mod tot icf (n, q') (Some a').    
    have [m eq] := prp val.
    exists (maxn n (maxn m k)).
    rewrite (mon'' _ _ _ _ _ def); last exact/leq_trans/leq_maxr/leq_maxr.
    move: eq; rewrite /=.
    case: ifP => // /cdP subs [<-].    
    suff ->: check_dom N (mu (phi_ N default (maxn n (maxn m k)))
                             (maxn n (maxn m k), q')) (maxn n (maxn m k)).
    - move: val.
      rewrite -(@mod (phi_ N default m)) => [val | ]; last first.
      - apply/coin_agre => q qfd.
        suff: phi q \from (pf2MF (curry N m) q) by rewrite /curry /phi_ /=; case: N.
        exact/icf_phin/subs.
      have := (mon' _ _ _ _ _ (leq_maxl n (maxn m k)) val).
      rewrite -(@mod (phi_ N default m)) //; first by move => ->.
      apply/coin_agre/agre_subs/phin_agre/leq_trans/leq_maxr/leq_maxl => //.
      by apply/subs_trans/subs/(mu_subl M_mon mu_term)/leq_maxl; rewrite val.
    apply/cdP.
    have coin: (phi_ N default m) \coincides_with phi \on (mu (phi_ N default m) (n, q')). 
    - apply/coin_agre/agre_subs => [ | q qfd]; first exact/subs.
      by have := icf_phin (n := m) N_mon icf qfd; rewrite /curry/phi_ /=; case: N.
    rewrite -(@modmod (phi_ N default m)).
    - apply/subs_trans; first apply/(mu_subl M_mon mu_term)/leq_maxl.
      + by rewrite (@mod _ _ phi) //; first by rewrite val.
      apply/subs_trans; first exact/subs; rewrite /curry => q [a vl /=]; exists a.
      case vl: N vl =>/=; case vl': N => [b | ] //; first by move => <-; apply/PhiN.mon_eq/vl'/vl.
      move: vl; have vl'':= (mon'' _ _ _ _ (leq_maxl m k) vl').
      by rewrite (mon'' _ _ _ _ (leq_maxr n (maxn m k)) vl'').
    apply/coin_agre/agre_subs/phin_agre/leq_trans/leq_maxr/leq_maxl => //.
    apply/subs_trans/subs; first apply/(mu_subl M_mon mu_term)/leq_maxl.
    by rewrite (@mod _ _ phi) //; first by rewrite val.
  Qed.

  Lemma mmapQ_mon: PhiN.monotone monotone_machine_application_Qdefault.
  Proof.
    move => q' n /=.
    case def: N => [default | ] //; rewrite N_mon; last by rewrite def.
    rewrite def.
    case: ifP => [/cdP subs | ] // val; rewrite cdS //.
    - rewrite -(M_mon val); symmetry; apply/mod/coin_agre/agre_subs/phinS/N_mon.
      by apply/subs_trans; first by apply/mu_term; case: M val.
      apply/cdP/subs_trans/subs.
    rewrite -(@modmod (phi_ N default n)); first by apply/mu_term; case: M val.
    apply/coin_agre/agre_subs/phin_agre => //.
    by apply/subs_trans/subs/mu_term; case: M val.
  Qed.    
End monotone_machine_application_Q_default.

Section monotone_machine_composition.
  Local Open Scope name_scope.
  Context (Q A Q' A': Type) (default: A'). 
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Context (Q'' A'': Type) (M: B -> nat * Q' -> option A') (M': B' -> nat * Q'' -> option A'').
  Context (mu_M': B' -> nat * Q'' -> seq Q').
  Hypothesis M_mon: M \is_monotone.
  Hypothesis M'_mon: M' \is_monotone.
  Hypothesis mod: mu_M' \modulus_function_for M'.
  Hypothesis modmod: mu_M' \modulus_function_for mu_M'.
  Hypothesis mu_term: terminates_with M' mu_M'.

  Definition monotone_machine_composition phi :=
    monotone_machine_application default (M phi) M' mu_M'.

  Lemma mmcmp_val: \F_monotone_machine_composition \extends (\F_M' \o \F_M).
  Proof.
    rewrite sing_rcmp; last exact/mon_sing/M_mon.
    move => phi FF'phi [Fphi [/FM_Phi exte val']]; apply/FM_Phi.    
    have tot: \Phi_(M phi) \is_total by move => q'; exists (Fphi q'); apply/exte.    
    rewrite /monotone_machine_composition.
    have <-//:= mmap_tot_spec _ mod modmod _ M'_mon tot; try exact/FM_Phi/val'; try exact/M_mon.
    by move => q qfd; apply/exte.
  Qed.

  Lemma mmcmp_spec: monotone_machine_composition \evaluates (\F_M' \o \F_M).
  Proof.
    apply/mon_eval/mmcmp_val/comp_sing/mon_sing/M_mon/mon_sing/M'_mon.
    move => phi; rewrite /monotone_machine_composition; apply/mmap_mon => //.
    exact/M_mon.
  Qed.

  Lemma mmcmp_mon: monotone_machine_composition \is_monotone.
  Proof. by move => phi;  apply/mmap_mon/mu_term/M'_mon/M_mon. Qed.
End monotone_machine_composition.

Section modulus_composition.
  Local Open Scope name_scope.
  Context (Q A Q' A': Type) (default: A'). 
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Context (Q'' A'': Type) (M: B -> nat * Q' -> option A') (M': B' -> nat * Q'' -> option A'').
  Context (mu': B' -> nat * Q'' -> seq Q').
  Context (mu: B -> nat * Q' -> seq Q).
  
  Definition modulus_composition phi (nq'': nat * Q'') :=
    let (n, q'') := nq'' in
    gather (mu phi) (map (fun q' => (n, q')) (mu' (phi_ (M phi) default n) nq'')).

  Lemma check_dom_cont (N N': nat * Q' -> option A') K n:
    N \coincides_with N' \on (map (fun q => (n, q)) K) -> check_dom N K n = check_dom N' K n.
  Proof. by elim: K => // q' K ih /= [-> /ih ->]. Qed.

  Lemma mcmp_spec:
    mu \modulus_function_for M -> mu' \modulus_function_for M' -> mu' \modulus_function_for mu' ->
    modulus_composition \modulus_function_for monotone_machine_composition default M M' mu'.
  Proof.
    move => mod mod' modmod phi [n q''] psi /= coin.
    have coin': (M phi) \coincides_with (M psi)
                        \on (map (fun q' => (n, q')) (mu' (phi_ (M phi) default n) (n, q''))).
    - by move: coin; elim: map => // [[m q'] K] ih /=/coin_cat [coin1 /ih coin2]; split; first exact/mod.
    suff coin'': phi_ (M phi) default n \coincides_with phi_ (M psi) default n \on
                      mu' (phi_ (M phi) default n) (n, q'').
    - rewrite (check_dom_cont coin') (@modmod _ _ (phi_ (M psi) default n)) //.
      by rewrite (@mod' _ _ (phi_ (M psi) default n)).
    move: coin; rewrite /=.
    elim: mu' => // q' K ih /= /coin_cat [coin1 /ih]; split => //.
    by rewrite /phi_ (@mod _ _ psi) //.
  Qed.

  Lemma gather_cont T T' (Lf Lg :T -> seq T') (K: seq T):
    (forall q, q \from K -> Lf q = Lg q) -> gather Lf K = gather Lg K.
  Proof.
    elim: K => // q K /= ih ass.
    rewrite ass; last by left.
    by rewrite ih // => q' ?; apply/ass; right.
  Qed.
    
  Lemma mcmp_modmod:
    mu \modulus_function_for M -> mu \modulus_function_for mu -> mu' \modulus_function_for mu' ->
    modulus_composition \modulus_function_for modulus_composition.
  Proof.
    move => mod modmod modmod' phi [n q''] psi /= coin.
    have coin': (M phi) \coincides_with (M psi)
                        \on (map (fun q' => (n, q')) (mu' (phi_ (M phi) default n) (n, q''))).
    - by move: coin; elim: map => // [[m q'] K] ih /=/coin_cat [coin1 /ih coin2]; split; first exact/mod.
    suff coin'': phi_ (M phi) default n \coincides_with phi_ (M psi) default n \on
                      mu' (phi_ (M phi) default n) (n, q'').
    - rewrite (@modmod' _ _ (phi_ (M psi) default n)) //.
      apply/gather_cont => q' lstn'.
      apply/modmod/coin_subl/coin => q lstn.
      move: lstn'.
      rewrite (@modmod' _ _ (phi_ (M psi) default n)) //.
      elim: map => // nq' K' ih /= [-> | nin]; first by apply/L2SS_cat; left.
      by apply/L2SS_cat; right; apply/ih.
    move: coin; rewrite /=.
    elim: mu' => // q' K ih /= /coin_cat [coin1 /ih]; split => //.
    by rewrite /phi_ (@mod _ _ psi) //.
  Qed.

  Lemma gthr_spec T T' (Lf: T -> seq T') K t':
    t' \from gather Lf K <-> exists t, t \from K /\ t' \from Lf t.
  Proof.
    split => [ | [t []]].
    - elim: K => // t K ih /=/L2SS_cat [lstn | /ih [k []]].
      - by exists t; split; first by left.
      by exists k; split; first by right.
    by elim: K => // k K ih /= [-> lstn | tK t'Lf]; apply/L2SS_cat; [left | right; apply/ih].
  Qed.

  Lemma gthr_subl T T' (Lf: T -> seq T') K K':
    K \is_sublist_of K' -> (gather Lf K) \is_sublist_of (gather Lf K').
  Proof.
    move => subl t' /gthr_spec [t [tK t'Lf]].
    by apply/gthr_spec; exists t; split; first apply/subl.
  Qed.

  Lemma L2SS_map T T' (f: T -> T') (K: seq T) t:
    t \from K -> (f t) \from map f K.
  Proof.
    elim: K => // t' K ih /= [-> | lstn]; first by left.
    by right; apply/ih.
  Qed.

  Lemma L2SS_map_spec T T' (f: T -> T') (K: seq T) t':
    t' \from map f K <-> exists t, t \from K /\ f t = t'.
  Proof.
    split => [ | [t [tK <-]]]; last exact/L2SS_map.
    elim: K => // t K ih /= [ <- | /ih [t0 []]]; first by exists t; split; first by left.
    by exists t0; split; first by right.
  Qed.

  Lemma map_subl T T' (f: T -> T') K K':
    K \is_sublist_of K' -> (map f K) \is_subset_of (map f K').
  Proof.
    move => subs q /L2SS_map_spec [t [tK <-]].
    by apply/L2SS_map_spec; exists t; split; first apply/subs.
  Qed.
    
  Lemma mcmp_term:
    M \is_monotone ->
    mu' \modulus_function_for mu' ->
    terminates_with M mu -> terminates_with M' mu' ->
    terminates_with (monotone_machine_composition default M M' mu') modulus_composition.
  Proof.
    move => mon modmod' term term' phi q'' n /=; case: ifP => // /cdP subs val q.  
    have subl := term' (phi_ (M phi) default n) q'' n val.
    have coin: phi_ (M phi) default n
                    \coincides_with phi_ (M phi) default n.+1
                    \on mu' (phi_ (M phi) default n) (n, q'').
    - by apply/coin_agre/agre_subs/phinS/mon/subs.
    rewrite -(@modmod' (phi_ (M phi) default n)); last exact/coin_subl/coin/subl.
    move => lstn.
    have: q \from gather (mu phi)
            (map (fun q' => (n.+1, q')) (mu' (phi_ (M phi) default n) (n, q''))).
    by apply/gthr_subl/lstn/map_subl/subl.
    elim: mu' subs => // q' K' ih/= /cons_subs [q'fd subs] /L2SS_cat [stf | lstn']; last first.
    - by apply/L2SS_cat; right; apply/ih.
    apply/L2SS_cat; left; apply/term => //.
    by have [a'] := q'fd; rewrite /curry /=; case: M.
  Qed.    
End modulus_composition.

Section monotone_machines.
  Context (Q A Q' A': Type).
  Structure monotone_machine :=
    {
      M:> continuous_machine nat Q A Q' A';
      M_monotone: is_monotone M;
    }.

  Lemma monm_mon (M: monotone_machine): is_monotone M.
  Proof. exact/M_monotone. Qed.
End monotone_machines.

Section compose_monotone_machines.
  Local Open Scope name_scope.
  Context (Q A Q' A' Q'' A'': Type) (default: A').
  Context (M: monotone_machine Q A Q' A').
  Context (M': monotone_machine Q' A' Q'' A'').
  
  Lemma mon_mcmp:
    FMop.monotone (monotone_machine_composition default M M' (modulus M')).
  Proof.
    apply/mmcmp_mon.
    apply M_monotone.
    apply M_monotone.
    apply modulus_correct.
    apply modulus_selfmodulating.
    apply M_monotone.
  Qed.

  Lemma term_mcmp:
    terminates_with (monotone_machine_composition default M M' (modulus M'))
    (modulus_composition default M (modulus M') (modulus M)).
  Proof.
    apply/mcmp_term.
    apply M_monotone.
    apply modmod.
    apply M_monotone.
    apply M_monotone.
  Qed.
    
  Definition compose: monotone_machine Q A Q'' A''.
    have mod: modulus_composition default M (modulus M') (modulus M)
                               \modulus_function_for
                               monotone_machine_composition default M M' (modulus M').
    - by apply/mcmp_spec/modmod/mod/mod.
    have modmod:
      modulus_composition default M (modulus M') (modulus M)
                          \modulus_function_for
                          modulus_composition default M (modulus M') (modulus M).
    - by apply/mcmp_modmod/modmod/modmod/modulus_correct.
    exists (Build_continuous_machine mod modmod).
    split.
    - exact/mon_mcmp.
    exact/term_mcmp.
  Defined.
  
  Lemma mcpm_spec: compose \evaluates (\F_M' \o \F_M).
  Proof.
    apply/mmcmp_spec.
    apply M_monotone.
    apply M_monotone.
    apply mod.
    apply modmod.
    apply M_monotone.
  Qed.
End compose_monotone_machines.

Local Open Scope name_scope.
Definition F2MM (Q Q' : Type) A A' (f : (Q -> A) -> (Q' -> A')) mu : mu \modulus_function_for f -> mu \modulus_function_for mu -> (@monotone_machine Q A Q' A').
  move => m mm.
  have f2mm := (@F2M_mon _ _ _ _ f).
  set cm := (Build_continuous_machine (F2M_mu_mod m) (F2M_mu_modmod mm)).
  set is_mon := (@Build_is_monotone _ _ _ _ cm f2mm (F2M_mterm mm)).
  apply (Build_monotone_machine is_mon). 
Defined.
