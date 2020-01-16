(* This file provides an abstract envelope for computability theoretical considerations *)
From mathcomp Require Import all_ssreflect.
From mf Require Import all_mf.
Require Import all_cs search PhiN monotone_application FMop seq_cont continuous_machines.
Require Import Classical Psatz.

Require Import FunctionalExtensionality ClassicalChoice.
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

  Let scnt: (F2MF mu) \is_sequentially_continuous.
  Proof. by apply/cont_scnt/cont_F2MF => phi; exists (mu phi); apply/modmod. Qed.

  Let M_mono phi q' a' n m: n <= m -> M phi (n, q') = Some a' -> M phi (m, q') = Some a'.
  Proof. by move => ? eq; have /mon_spec prp:= M_mon; apply/prp/eq. Qed.

  Let N_mono q a n m: n <= m -> N (n, q) = Some a -> N (m, q) = Some a.
  Proof. by move => ? eq; have /PhiN.mon_spec prp:= N_mon; apply/prp/eq. Qed.
    
  Hypothesis mu_term: terminates_with M mu.
  
  Lemma mu_subl phi q' n m: M phi (n, q') -> n <= m -> mu phi (m, q') \is_subset_of mu phi (n, q').
  Proof.
    move => val /subnK <-; elim: (m - n) => // k ih.
    rewrite addSn; apply/subs_trans/ih/mu_term.
    move: val; case val: M => [a | ]// _.
    by have ->: M phi (k + n, q') = Some a by have/mon_spec H:= M_mon; apply/H/val/leq_addl.
  Qed.

  Lemma mmap_tot_spec phi:
    phi \is_choice_for (\Phi_N) -> \Phi_(M phi) =~= \Phi_monotone_machine_application.
  Proof.
    move => icf q' a'; split => [[n val] | [n ]]; last first.
    - simpl; case : ifP => // /cdP subs eq.
      exists n; rewrite -(@mod (phi_ N default n)) //.
      apply/coin_agre/agre_subs => [ | q qfd]; first exact/subs.
      have := icf_phin N_mon icf (n:= n) qfd.
      by rewrite /curry /phi_ /=; case: N => //.
    have [||prp _]//:= apmm_tot_spec default scnt _ mod _ icf (n,q') (Some a').
    have [m /= eq]:=prp val; exists (maxn n m); case: ifP eq => // /cdP subs [<-].    
    
    suff /cdP ->: mu (phi_ N default (maxn n m)) (maxn n m, q')
         \is_subset_of dom (pf2MF (curry N (maxn n m))). 
    - move: val; rewrite -(@mod (phi_ N default m)) => [val | ]; last first.
      + apply/coin_agre => q qfd.
        suff: phi q \from (pf2MF (curry N m) q) by rewrite/curry/phi_/=; case: N.
        exact/icf_phin/subs.
      have := M_mono (leq_maxl n m) val.
      rewrite -(mod (phi := phi_ N default m)) //; first by move ->.
      apply/coin_agre/agre_subs/phin_agre/leq_maxr => //.
      by apply/subs_trans/subs/mu_subl/leq_maxl; rewrite val.

    have coin: phi_ N default m \coincides_with phi \on mu (phi_ N default m) (n, q'). 
    - apply/coin_agre/agre_subs => [ | q qfd]; first exact/subs.
      by have := icf_phin (n := m) N_mon icf qfd; rewrite /curry/phi_ /=; case: N.

    rewrite -(modmod (phi := phi_ N default m)).
    - apply/subs_trans; first apply/mu_subl/leq_maxl.
      + by rewrite (mod (psi := phi)) //; first by rewrite val.
      apply/subs_trans; first exact/subs; rewrite /curry => q [a vl /=]; exists a.
      case vl: N vl =>/=; case vl': N => [b | ] //; first by move => <-; apply/PhiN.mon_eq/vl'/vl.
      by move: vl; have ->:= N_mono (leq_maxr n m) vl'.
    apply/coin_agre/agre_subs/phin_agre/leq_maxr => //.
    apply/subs_trans/subs; first apply/mu_subl/leq_maxl.
    by rewrite (mod (psi := phi)) //; first by rewrite val.
  Qed.

  Lemma mmap_mon: PhiN.monotone monotone_machine_application.
  Proof.
    move => q' n /=; case: ifP => [/cdP subs | ] // val; rewrite cdS //.
    - rewrite -(M_mon val); symmetry; apply/mod/coin_agre/agre_subs/phinS/N_mon.
      by apply/subs_trans; first by apply/mu_term; case: M val.
      apply/cdP/subs_trans/subs.
    rewrite -(modmod (phi:= phi_ N default n)); first by apply/mu_term; case: M val.
    apply/coin_agre/agre_subs/phin_agre => //.
    by apply/subs_trans/subs/mu_term; case: M val.
  Qed.    
End monotone_machine_application.

Section monotone_machine_application_Q_default.
  (**
     This section reiterates the results from the previous section but avoids the use of a default
     answer and substitutes a default question that comes with an represented space.
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
      
  Lemma mmap_exte_mmapQ phi: phi \is_choice_for (\Phi_N) -> 
                        \Phi_(monotone_machine_application (phi someq) N M mu) \extends
                        \Phi_monotone_machine_application_Qdefault.
  Proof.
    have /mon_spec mon' := M_mon => icf q' a'.
    have /PhiN.mon_spec mon'' := N_mon; case => [n /=].
    case eq: N => [default | ] // <-; exists n; suff ->: default = phi someq by trivial.
    have [m eq']:= icf someq (tot someq).
    case/orP: (leq_total n m) => ineq.
    - by have := mon'' _ _ _ _ ineq eq; rewrite eq'; case.
    by have := mon'' _ _ _ _ ineq eq'; rewrite eq; case.
  Qed.   
  
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
    have [|prp _]:= apmm_tot_spec default _ N_mon mod tot icf (n, q') (Some a').    
    - by apply/cont_scnt/cont_F2MF => phi'; exists (mu phi'); apply/modmod.
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

Section monotone_machine_composition_Q_default.
  Local Open Scope name_scope.
  Context (Q A Q' A': Type) (someq: Q'). 
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Context (Q'' A'': Type) (M: B -> nat * Q' -> option A') (M': B' -> nat * Q'' -> option A'').
  Context (mu_M': B' -> nat * Q'' -> seq Q').
  Hypothesis M_mon: M \is_monotone.
  Hypothesis M'_mon: M' \is_monotone.
  Hypothesis mod: mu_M' \modulus_function_for M'.
  Hypothesis modmod: mu_M' \modulus_function_for mu_M'.
  Hypothesis mu_term: terminates_with M' mu_M'.

  Definition monotone_machine_composition_Qdefault phi :=
    monotone_machine_application_Qdefault someq (M phi) M' mu_M'.

  Lemma mmcmpQ_val: \F_monotone_machine_composition_Qdefault \extends (\F_M' \o \F_M).
  Proof.
    rewrite sing_rcmp; last exact/mon_sing/M_mon.
    move => phi FF'phi [Fphi [/FM_Phi exte val']]; apply/FM_Phi.    
    have tot: \Phi_(M phi) \is_total by move => q'; exists (Fphi q'); apply/exte.    
    rewrite /monotone_machine_composition_Qdefault.
    have <-//:= mmapQ_tot_spec _ mod modmod _ M'_mon tot; try exact/FM_Phi/val'; try exact/M_mon.
    by move => q qfd; apply/exte.
  Qed.

  Lemma mmcmpQ_spec: monotone_machine_composition_Qdefault \evaluates (\F_M' \o \F_M).
  Proof.
    apply/mon_eval/mmcmpQ_val/comp_sing/mon_sing/M_mon/mon_sing/M'_mon.
    move => phi; rewrite /monotone_machine_composition; apply/mmapQ_mon => //.
    exact/M_mon.
  Qed.

  Lemma mmcmpQ_mon: monotone_machine_composition_Qdefault \is_monotone.
  Proof. by move => phi;  apply/mmapQ_mon/mu_term/M'_mon/M_mon. Qed.
End monotone_machine_composition_Q_default.

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
    by rewrite /phi_ (@mod _ _ psi).
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

Section modulus_composition_Q_default.
  Local Open Scope name_scope.
  Context (Q A Q' A': Type) (someq: Q'). 
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Context (Q'' A'': Type) (M: B -> nat * Q' -> option A') (M': B' -> nat * Q'' -> option A'').
  Context (mu': B' -> nat * Q'' -> seq Q').
  Context (mu: B -> nat * Q' -> seq Q).
  
  Definition modulus_composition_Qdefault phi (nq'': nat * Q'') :=
    let (n, q'') := nq'' in
    if M phi (n, someq) is Some default
    then gather (mu phi) ((n,someq) :: map (fun q' => (n, q')) (mu' (phi_ (M phi) default n) nq''))
    else mu phi (n,someq).

  Lemma check_dom_contQ (N N': nat * Q' -> option A') K n:
    N \coincides_with N' \on (map (fun q => (n, q)) K) -> check_dom N K n = check_dom N' K n.
  Proof. by elim: K => // q' K ih /= [-> /ih ->]. Qed.

  Lemma mcmpQ_spec:
    mu \modulus_function_for M -> mu' \modulus_function_for M' -> mu' \modulus_function_for mu' ->
    modulus_composition_Qdefault \modulus_function_for monotone_machine_composition_Qdefault someq M M' mu'.
  Proof.
    move => mod mod' modmod phi [n q''] psi /= coin.

    (* establish that the default answer queries using phi and psi are identical: *)
    have <-: M phi (n, someq) = M psi (n, someq).
    apply mod.
    move : coin.
    destruct (M phi (n, someq)).
    apply coin_cat.
    move => coinsomeq; apply coinsomeq.

    (* do away with all cases where we do not have default : A' : *)
    move : coin.
    elim (M phi (n, someq)) => [default|].
    2:{ by simpl. }
    move => coin_pre.

    (* get rid of someq from coin : *)
    have coin: phi \coincides_with psi \on
           (gather (mu phi)
              [seq (n, q') | q' <- mu' (phi_ (M phi) default n) (n, q'')]).
    move : coin_pre.
    apply coin_cat.

    have coin': (M phi) \coincides_with (M psi)
                        \on (map (fun q' => (n, q')) (mu' (phi_ (M phi) default n) (n, q''))).
    - by move: coin; elim: map => // [[m q'] K] ih /=/coin_cat [coin1 /ih coin2]; split; first exact/mod.
    suff coin'': phi_ (M phi) default n \coincides_with phi_ (M psi) default n \on
                      mu' (phi_ (M phi) default n) (n, q'').
    - rewrite (check_dom_contQ coin') (@modmod _ _ (phi_ (M psi) default n)) //.
      by rewrite (@mod' _ _ (phi_ (M psi) default n)).
    move: coin; rewrite /=.
    elim: mu' => // q' K ih /= /coin_cat [coin1 /ih]; split => //.
    by rewrite /phi_ (@mod _ _ psi) //.
  Qed.

  Lemma gather_contQ T T' (Lf Lg :T -> seq T') (K: seq T):
    (forall q, q \from K -> Lf q = Lg q) -> gather Lf K = gather Lg K.
  Proof.
    elim: K => // q K /= ih ass.
    rewrite ass; last by left.
    by rewrite ih // => q' ?; apply/ass; right.
  Qed.
    
  Lemma mcmpQ_modmod:
    mu \modulus_function_for M -> mu \modulus_function_for mu -> mu' \modulus_function_for mu' ->
    modulus_composition_Qdefault \modulus_function_for modulus_composition_Qdefault.
  Proof.
    move => mod modmod modmod' phi [n q''] psi /= coin.

    (* establish that the default answer queries using phi and psi are identical: *)
    have phipsisomeq : phi \coincides_with psi \on mu phi (n, someq).
    move : coin.
    destruct (M phi (n, someq)).
    apply coin_cat.
    move => coinsomeq; apply coinsomeq.
    have <-: M phi (n, someq) = M psi (n, someq).
    by apply mod.

    (* do away with all cases where we do not have default : A' : *)
    move : coin.
    elim (M phi (n, someq)) => [default|].
    2:{ by apply modmod. }
    move => coin.

    have coin': (M phi) \coincides_with (M psi)
                        \on ((n, someq) :: map (fun q' => (n, q')) (mu' (phi_ (M phi) default n) (n, q''))).
      move: coin => /coin_cat [coinq coin]. 
    split; first by apply mod.
    - by move: coin; elim: map => // [[m q'] K] ih /=/coin_cat [coin1 /ih coin2]; split; first exact/mod.
    
    suff coin'': phi_ (M phi) default n \coincides_with phi_ (M psi) default n \on
                      mu' (phi_ (M phi) default n) (n, q'').
    - rewrite (@modmod' _ _ (phi_ (M psi) default n)) //.
      f_equal.
      apply modmod. move : coin. apply coin_cat.

      apply/gather_contQ => q' lstn'.
      apply/modmod/coin_subl/coin => q lstn.
      move: lstn'.
      rewrite (@modmod' _ _ (phi_ (M psi) default n)) // /=.
      move => qin.
      apply /lstn_app. apply or_intror.
      move: qin.
      elim: map => // nq' K' ih /= [-> | nin]; first by apply/L2SS_cat; left.
      by apply/L2SS_cat; right; apply/ih.
    move: coin; rewrite /=.
    elim: mu' => // q' K ih /= /coin_cat [coin1 ihh]. 
    split => //.
    rewrite /phi_ (@mod _ _ psi) //.
    by move : ihh => /coin_cat [ihh1 _].
    apply ih.
    apply coin_cat.
    split => //.
    move : ihh.
    by apply coin_cat.
  Qed.

  Lemma gthr_specQ T T' (Lf: T -> seq T') K t':
    t' \from gather Lf K <-> exists t, t \from K /\ t' \from Lf t.
  Proof.
    split => [ | [t []]].
    - elim: K => // t K ih /=/L2SS_cat [lstn | /ih [k []]].
      - by exists t; split; first by left.
      by exists k; split; first by right.
    by elim: K => // k K ih /= [-> lstn | tK t'Lf]; apply/L2SS_cat; [left | right; apply/ih].
  Qed.

  Lemma gthr_sublQ T T' (Lf: T -> seq T') K K':
    K \is_sublist_of K' -> (gather Lf K) \is_sublist_of (gather Lf K').
  Proof.
    move => subl t' /gthr_specQ [t [tK t'Lf]].
    by apply/gthr_specQ; exists t; split; first apply/subl.
  Qed.

  Lemma L2SS_mapQ T T' (f: T -> T') (K: seq T) t:
    t \from K -> (f t) \from map f K.
  Proof.
    elim: K => // t' K ih /= [-> | lstn]; first by left.
    by right; apply/ih.
  Qed.

  Lemma L2SS_map_specQ T T' (f: T -> T') (K: seq T) t':
    t' \from map f K <-> exists t, t \from K /\ f t = t'.
  Proof.
    split => [ | [t [tK <-]]]; last exact/L2SS_mapQ.
    elim: K => // t K ih /= [ <- | /ih [t0 []]]; first by exists t; split; first by left.
    by exists t0; split; first by right.
  Qed.

  Lemma map_sublQ T T' (f: T -> T') K K':
    K \is_sublist_of K' -> (map f K) \is_subset_of (map f K').
  Proof.
    move => subs q /L2SS_map_specQ [t [tK <-]].
    by apply/L2SS_map_specQ; exists t; split; first apply/subs.
  Qed.
    
  Lemma mcmpQ_term:
    M \is_monotone ->
    mu' \modulus_function_for mu' ->
    terminates_with M mu -> terminates_with M' mu' ->
    terminates_with (monotone_machine_composition_Qdefault someq M M' mu') modulus_composition_Qdefault.
  Proof.
    move => mon modmod' term term' phi q'' n /= hasvalue.

    (* M phi (n, someq) is defined *)
    have Msomeq_some : M phi (n, someq) <> None.
    move: hasvalue.
    elim (M phi (n, someq)); by [].

    (* unify all matches on M ... someq *)
    have ->: M phi (n.+1, someq) = M phi (n, someq).
    by apply mon.

    (* eliminate cases where someq does not give a default : A' *)
    move: (hasvalue).
    elim (M phi (n, someq)) => [default|]; last by [].

    case: ifP => // /cdP subs val q. 
    have subl := term' (phi_ (M phi) default n) q'' n val.
    have coin: phi_ (M phi) default n
                    \coincides_with phi_ (M phi) default n.+1
                    \on mu' (phi_ (M phi) default n) (n, q'').
    - by apply/coin_agre/agre_subs/phinS/mon/subs.
    rewrite -(@modmod' (phi_ (M phi) default n)); last by exact/coin_subl/coin/subl.

    (* deal with list concatenation involving someq *)
    move => lstn.
    apply /lstn_app. 
    apply lstn_app in lstn.
    case : lstn => [lstn|lstn]. 
    apply /or_introl. move : lstn.
    apply /term. destruct M; by []. 
    apply or_intror.

    have: q \from gather (mu phi)
            (map (fun q' => (n.+1, q')) (mu' (phi_ (M phi) default n) (n, q''))).
    by apply/gthr_subl/lstn/map_subl/subl.
    elim: mu' subs => // q' K' ih/= /cons_subs [q'fd subs] /L2SS_cat [stf | lstn']; last first.
    - by apply/L2SS_cat; right; apply/ih.
    apply/L2SS_cat; left; apply/term => //.
    by have [a'] := q'fd; rewrite /curry /=; case: M.
  Qed.    
End modulus_composition_Q_default.


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

Section compose_monotone_machines_Q_default.
  Local Open Scope name_scope.
  Context (Q A Q' A' Q'' A'': Type) (someq: Q').
  Context (M: monotone_machine Q A Q' A').
  Context (M': monotone_machine Q' A' Q'' A'').
  
  Lemma mon_mcmpQ:
    FMop.monotone (monotone_machine_composition_Qdefault someq M M' (modulus M')).
  Proof. 
    apply/mmcmpQ_mon; try by apply M_monotone.
    - exact/modulus_correct.
    exact/modulus_selfmodulating.
  Qed.

  Lemma term_mcmpQ:
    terminates_with (monotone_machine_composition_Qdefault someq M M' (modulus M'))
    (modulus_composition_Qdefault someq M (modulus M') (modulus M)).
  Proof.
    apply/mcmpQ_term; try by apply M_monotone.
    exact/modmod.
  Qed.
    
  Definition composeQ: monotone_machine Q A Q'' A''.
    have mod: modulus_composition_Qdefault someq M (modulus M') (modulus M)
                               \modulus_function_for
                               monotone_machine_composition_Qdefault someq M M' (modulus M').
    - by apply/mcmpQ_spec/modmod/mod/mod.
    have modmod:
      modulus_composition_Qdefault someq M (modulus M') (modulus M)
                          \modulus_function_for
                          modulus_composition_Qdefault someq M (modulus M') (modulus M).
    - by apply/mcmpQ_modmod/modmod/modmod/modulus_correct.
    exists (Build_continuous_machine mod modmod).
    split.
    - exact/mon_mcmpQ.
    exact/term_mcmpQ.
  Defined.
  
  Lemma mcpmQ_spec: composeQ \evaluates (\F_M' \o \F_M).
  Proof.
    apply/mmcmpQ_spec.
    apply M_monotone.
    apply M_monotone.
    apply mod.
    apply modmod.
    apply M_monotone.
  Qed.

End compose_monotone_machines_Q_default.

Local Open Scope name_scope.
Local Open Scope cs_scope.
Definition F2MM Q Q' A A' (f : (Q -> A) -> Q' -> A') mu:
  mu \modulus_function_for f -> mu \modulus_function_for mu -> (@monotone_machine Q A Q' A').
  move => m mm.
  have f2mm := (@F2M_mon _ _ _ _ f).
  set cm := (Build_continuous_machine (F2M_mu_mod m) (F2M_mu_modmod mm)).
  set is_mon := (@Build_is_monotone _ _ _ _ cm f2mm (F2M_mterm mm)).
  apply (Build_monotone_machine is_mon). 
Defined.

Section monotone_machines_product.
  Context (X X' Y Y': cs).
  Context (Xdefault : A_(X')) (Ydefault : A_(Y')).
  Context (M1: monotone_machine Q_(X) A_(X) Q_(X') A_(X')).
  Context (M2: monotone_machine Q_(Y) A_(Y) Q_(Y') A_(Y')).

  Definition monotone_machine_product phi nq :=
    match nq.2 with
    | inl q => if M1 (lprj phi) (nq.1, q) is Some a then Some (a, Ydefault) else None
    | inr q => if M2 (rprj phi) (nq.1, q) is some a then Some (Xdefault, a) else None
    end.

  Definition monotone_machine_product_mu phi nq :=
    match nq.2 with
    | inl q => map inl (modulus M1 (lprj phi) (nq.1, q))
    | inr q => map inr (modulus M2 (rprj phi) (nq.1, q))
    end.

  Lemma monotone_machine_product_mod:
    monotone_machine_product_mu \modulus_function_for monotone_machine_product.
  Proof.
    rewrite/monotone_machine_product_mu/monotone_machine_product => phi [n [q' | q']] psi /= coin.
    - have/modulus_correct->//:lprj phi \coincides_with lprj psi \on modulus M1 (lprj phi) (n, q').
      by rewrite /lprj; elim: (modulus M1) coin => // a l IH /= [->]; split; last exact/IH.
    have/modulus_correct->//: rprj phi \coincides_with rprj psi \on modulus M2 (rprj phi) (n, q').
    by rewrite /rprj; elim: (modulus M2) coin => // a l IH /= [->]; split; last exact/IH.
  Qed.

  Lemma mon_mprd: FMop.monotone (monotone_machine_product).
  Proof.
    case (M_monotone M1 ) => M1_mon M1_term; case (M_monotone M2 ) => M2_mon M2_term.
    rewrite /monotone_machine_product => phi [] q' n /=.
    - by case e: (M1 _); first rewrite M1_mon e.
    by case e: (M2 _); first rewrite M2_mon e.
  Qed.

  Lemma monotone_machine_product_mod_mod:
    monotone_machine_product_mu \modulus_function_for monotone_machine_product_mu.
  Proof.
    rewrite /monotone_machine_product_mu => phi [n []] q psi /= coin.
    - have /modmod -> //: lprj phi \coincides_with lprj psi \on modulus M1 (lprj phi) (n, q).
      by rewrite/lprj; elim: (modulus M1) coin => // a l IH /= [->]; split; last exact/IH.
    have/modmod -> //: rprj phi \coincides_with rprj psi \on modulus M2 (rprj phi) (n, q).
    by rewrite/rprj; elim: (modulus M2) coin => // a l IH /= [->]; split; last exact/IH.
  Qed.

  Lemma term_mprd:
    terminates_with monotone_machine_product monotone_machine_product_mu.
  Proof.
    rewrite /monotone_machine_product_mu/monotone_machine_product => phi []q n /=.
    - case e: (M1 _) => [a1' |] // _ [a H| a]; last by elim: (modulus M1) => // y l IH [].
      apply/map_inl; apply modulus_terminating; first exact/monm_mon; try by rewrite e.
      by elim: (modulus M1) H => // ? ? ih /= [[] |]; [left | right; apply/ih].
    case e: (M2 _) => [a1' |] // _ [a| a H]; first by elim: (modulus M2) => // y l IH [] //.
    apply/map_inr; apply modulus_terminating; first exact/monm_mon; try by rewrite e.
    by elim: (modulus M2) H => // ? ? ih [[]|]; [left | right; apply/ih].
  Qed.

  Definition product:
    monotone_machine Q_(X \*_cs Y) A_(X \*_cs Y) Q_(X' \*_cs Y') A_(X' \*_cs Y').
    exists (Build_continuous_machine monotone_machine_product_mod monotone_machine_product_mod_mod).
    by split; try exact /mon_mprd; exact/term_mprd.
  Defined.

  Lemma mprd_spec F G : \F_M1 \solves F -> \F_M2 \solves G ->  \F_product \solves (F ** G).
  Proof.
    move => slvs slvs' phi [x1 x2] /prod_name_spec [phinx1 phinx2] [[x'1 x'2] [val val']].
    case: (slvs (lprj phi) x1) => // [| [f1 f1prp] P]; first by exists x'1.
    case: (slvs' (rprj phi) x2) => // [| [f2 f2prp] P']; first by exists x'2.
    split => [ | Fphi prp]; rewrite /=/monotone_machine_product/=.
    - exists (fun q => match q with inl q' => (f1 q',Ydefault) | inr q' => (Xdefault,f2 q') end).
      by case => q'; [case (f1prp q') | case (f2prp q')] => n nprp; exists n; rewrite nprp.
    have [q1' | y1' []]:= P (lprj Fphi).
    - have [n /=nprp]:= prp (inl q1').
      by exists n; move: nprp; rewrite /monotone_machine_product/lprj /=; case: (M1 _) => // a [<-].
    have [q2' | y2' []]:= P' (rprj Fphi); last by exists (y1',y2'); split; try exists (unpair Fphi).
    have [n /=nprp]:= prp (inr q2').
    by exists n; move: nprp; rewrite/monotone_machine_product/rprj/=; case: (M2 _) => // a [<-].
  Qed.
End monotone_machines_product.

Section monotone_machines_sum.
  Context (X X' Y Y': cs).
  Context (M1: monotone_machine Q_(X) A_(X) Q_(X') A_(X')).
  Context (M2: monotone_machine Q_(Y) A_(Y) Q_(Y') A_(Y')).

  Definition monotone_machine_sum phi nq :=
    match phi (someq, someq) with
    | inl a => if M1 (lslct phi a) (nq.1, nq.2.1) is Some a' then Some (inl a') else None
    | inr a => if M2 (rslct phi a) (nq.1, nq.2.2) is Some a' then Some (inr a') else None
    end.

  Definition monotone_machine_sum_mu phi nq  :=
    match phi (someq, someq) with
      | inl a =>
        [:: (someq, someq)] ++ [seq (i, someq) | i <- modulus M1 (lslct phi a) (nq.1, nq.2.1)]
      | inr a =>
        [:: (someq, someq)] ++ [seq (someq,i) | i <- modulus M2 (rslct phi a) (nq.1, nq.2.2)]
      end.
  
  Lemma monotone_machine_sum_mod:
    monotone_machine_sum_mu \modulus_function_for monotone_machine_sum.
  Proof.
    rewrite /monotone_machine_sum_mu/monotone_machine_sum => phi [n [q1 q2]] psi.
    case e : (phi (someq, someq)) => [a|a];rewrite !coin_cat => [[[<- _]]] P;rewrite e.
    have/modulus_correct->//:
        lslct phi a \coincides_with lslct psi a \on modulus M1 (lslct phi a) (n, q1).
    - by elim: (modulus M1 _) P => // x l ih [H]; split; try exact/ih; rewrite/lslct H.
    have/modulus_correct->//:
        rslct phi a \coincides_with rslct psi a \on modulus M2 (rslct phi a) (n, q2).
    by elim: (modulus M2 _) P => // x l ih [H]; split; try exact/ih; rewrite /rslct H.
  Qed.

  Lemma mon_msum: FMop.monotone (monotone_machine_sum).
  Proof.
    rewrite /monotone_machine_sum => phi q n.
    case (M_monotone M1) => M1_mon _; case (M_monotone M2) => M2_mon _.
    case: (phi (someq, someq)) => ? /= H; first by rewrite M1_mon; case: (M1 _) H.
    by rewrite M2_mon; case: (M2 _) H.
  Qed.

  Lemma monotone_machine_sum_mod_mod : monotone_machine_sum_mu \modulus_function_for monotone_machine_sum_mu.
  Proof.
    rewrite /monotone_machine_sum_mu => phi [n [q1 q2]] psi.
    case e : (phi (someq, someq)) => [a|a];rewrite !coin_cat => [[[<- _]]] P;rewrite e.
    - have/modmod->//:lslct phi a \coincides_with lslct psi a \on modulus M1 (lslct phi a) (n, q1).
      + by elim: (modulus M1 _) P => // x l ih [H]; split; try exact/ih; rewrite/lslct H.
    have/modmod->//:rslct phi a \coincides_with rslct psi a \on modulus M2 (rslct phi a) (n, q2).
    by elim: (modulus M2 _) P => // x l IH [H]; split; try exact/IH; rewrite/rslct H.
  Qed.

  Lemma term_msum:
    terminates_with monotone_machine_sum monotone_machine_sum_mu.
  Proof.
    rewrite /monotone_machine_sum_mu/monotone_machine_sum => phi [q1 q2] n.
    case: (phi (someq, someq)) => default.
    - case e : (M1 _) =>// _; apply cons_subs; split; [left | apply/subl_cat; right] => //=.
      by apply/map_subl; apply modulus_terminating; first exact/monm_mon; rewrite e.
    case e : (M2 _) =>// _; apply/cons_subs; split; [left | apply/subl_cat; right] => //=.
    by apply/map_subl; first apply modulus_terminating; first exact/monm_mon; rewrite e.
  Qed.
  
  Definition sum: monotone_machine Q_(X \+_cs Y) A_(X \+_cs Y) Q_(X' \+_cs Y') A_(X' \+_cs Y').
    exists (Build_continuous_machine monotone_machine_sum_mod  monotone_machine_sum_mod_mod).
    by split; try exact /mon_msum; apply/term_msum.
  Defined.

  Lemma msum_spec F G: \F_M1 \solves F -> \F_M2 \solves G ->  \F_sum \solves (F +s+ G).
  Proof.
    move => H1 H2 phi x [x0 [x0prp P1]] P2.
    split => [ | psi psiprp].
    - rewrite FM_dom  => q /=.
      case: x0 x0prp P1 => /= a aprp; case: x P2 => x' [[]] s sprp P //.
      + case (H1 a x' P) => [ | [psi psiprp ?]]; first by exists s.
        exists (inl (psi q.1)); rewrite/monotone_machine_sum; case (psiprp q.1) => n nprp.
        by exists n; move: aprp; rewrite /slct/=; case: (phi _)  => [? []| ] // ->; rewrite nprp.
      case (H2 a x' P) => [ | [psi psiprp Fqprp]]; first by exists s.
      exists (inr (psi q.2)); rewrite/monotone_machine_sum; case (psiprp q.2) => n nprp.
      by exists n; move: aprp; rewrite /slct/=; case: (phi _) => [ | ? []] // ->;rewrite nprp.
    case: x0 x0prp P1 => [phil | phir]; rewrite /slct/= => prp.
    - case: x P2 => x0 // [[]]// s sprp P.
      have := psiprp (someq, someq); rewrite/=/monotone_machine_sum/=.
      case e: (phi _) prp => [a0 | a0] // [prp] [?].
      rewrite prp.
      case (M1 _ _) => b0 // [] B.
      case (H1 phil x0 P) => [| dom ex]; first by exists s.
      case (ex (lslct psi b0)) => q'.
      + case (psiprp (q', someq)) => n; rewrite/=/monotone_machine_sum e prp.
        by case e1 : (M1 _ _) => [m1v | ] // [m1P]; exists n; rewrite e1 /lslct -m1P.    
      rewrite /lslct /=; case => hprp1 hprp2.
      by exists (inl q'); split; last by exists (inl (lslct psi b0)); rewrite /slct -B //.
    case: x P2 => x0 [[]]// s sprp P.
    have := psiprp (someq, someq); rewrite/=/monotone_machine_sum/=.
    case e: (phi _) prp => [a0 | a0] // [prp] [?]; rewrite prp.
    case (M2 _ _) => b0 // [] B.
    case (H2 phir x0 P) => [| dom ex]; first by exists s.
    case (ex (rslct psi b0)) => [q'| q'[]].
    - case (psiprp (someq,q')) => n; rewrite/=/monotone_machine_sum e prp. 
      by rewrite/rslct; case e1: (M2 _ _) => [] // [<-]; exists n; rewrite e1.
    by exists (inr q'); split; last by exists (inr (rslct psi b0)); rewrite /slct -B.
  Qed.
End monotone_machines_sum.

Section constructions.
  Arguments monotone_machine {Q} {A} {Q'} {A'}.

  Definition compose_monotone_machines
             (X Y Z: cs) (F: Y ->> Z) (G : X ->> Y) H (default: A_ Y) (M N: monotone_machine):
    \F_M \solves F -> \F_N \solves G -> (F \o G) \tightens H ->
    {K : monotone_machine |  \F_K \solves H}.
  Proof.
    by move => ? ? eq; exists (compose default N M); apply/tight_slvs/mcpm_spec/slvs_tight/eq/slvs_comp.
  Defined.

  Lemma cmp_mach (X Y Z: cs) (F: Y ->> Z) (G: X ->> Y)  H (a: A_ Y):
    {M : monotone_machine |  \F_M \solves F} -> {N: monotone_machine|  \F_N \solves G} ->
    (F \o G) \tightens H -> {K : monotone_machine |  \F_K \solves H}.
  Proof.
    case => M ? [N ?] eq; exists (compose a N M).
    exact/tight_slvs/mcpm_spec/slvs_tight/eq/slvs_comp.
  Defined.

  Lemma cmp_machine_equiv (X Y Z: cs) (F : X ->> Y) (G : Z ->> X)  H (a: A_ X):
    {M: monotone_machine | \F_M \solves F} -> {N: monotone_machine | \F_N \solves G} ->
    H =~= F \o G -> {K : monotone_machine | \F_K \solves H}.
  Proof.
    move => slvs slvs' eq.
    apply/cmp_mach; try exact/a; try exact/slvs; try exact/slvs'.
    by rewrite eq; apply/tight_comp/tight_ref/tight_ref.
  Qed.
  
  Lemma prd_mach (X Y Z V: cs) (F: X ->> Y) (G: Z ->> V) H (a: A_ Y) (a': A_ V):
    {M: monotone_machine |  \F_M \solves F} -> {N: monotone_machine |  \F_N \solves G} ->
    H =~= F ** G -> {K : monotone_machine | \F_K \solves H}.
  Proof. by case => M ? [N ?] eq; exists (product a a' M N); rewrite eq; apply mprd_spec. Qed.

  Lemma sum_machine (X Y Z V: cs) (F: X ->> Y) (G: Z ->> V) H:
    {M : monotone_machine |  \F_M \solves F} -> {N: monotone_machine |  \F_N \solves G} ->
    H =~= F +s+ G -> {K : monotone_machine | \F_K \solves H}.
  Proof. by case => M ? [N ?] eq; exists (sum M N); rewrite eq; apply msum_spec. Qed.
End constructions.
Arguments partial_function {S} {T}.

Local Notation subset := mf_set.subset.
Definition set_sum S T (A: subset S) (A': subset T) :=
  make_subset (fun s => match s with
                     | inl s => s \from A
                     | inr s' => s' \from A'
                     end).

Lemma inl_ssum S T (A: subset S) (A': subset T) s: inl s \from set_sum A A' <-> s \from A.
Proof. done. Qed.

Lemma inr_ssum S T (A: subset S) (A': subset T) s: inr s \from set_sum A A' <-> s \from A'.
Proof. done. Qed.

Section partial_function_sum_and_product.
  Context (S T U V: Type).

  Local Notation pf := @partial_function.
  Definition fprd_pf (f: pf S T) (g: pf U V): (pf (S*U)%type (T*V)%type) .
    exists (set_prod (domain f) (domain g)); case => [[s1 s2] /= [p1 p2]].
    by apply ((f (exist (domain f) s1 p1)), (g (exist (domain g) s2 p2))).
  Defined.
  Local Notation "f **_pf g" := (fprd_pf f g) (at level 35).

  Lemma PF2MF_fprd f g: f **_pf g =~= f ** g.
  Proof.
    move => [? ?] [].
    split => /= [[[p p' [<- <-]]] | [[p <- [p' <-]]]]; last by exists (conj p p').
    split; by [exists  p | exists p'].
  Qed.

  Definition fsum_pf (f: pf S T) (g: pf U V): (pf (S+U)%type (T+V)%type) .
    exists (set_sum (domain f) (domain g)).
    case => [[s prp | p prp]].
    by apply (inl (f (exist (domain f) s prp))).
    by apply (inr (g (exist (domain g) p prp))).
  Defined.

  Local Notation "f +s+_pf g" := (fsum_pf f g) (at level 35).

  Lemma PF2MF_fsum f g: f +s+_pf g =~= f +s+ g.
  Proof. case => s; case => /=; try firstorder => //; (try by exists x; f_equal); by case: H; exists x. Qed.
End partial_function_sum_and_product.
Notation "f **_pf g" := (fprd_pf f g) (at level 35).
Notation "f +s+_pf g" := (fsum_pf f g) (at level 35).
Notation "f \o_pf g" := (partial_composition f g) (at level 35).

Section partial_functions.
  Local Open Scope name_scope.
  Local Open Scope cs_scope.
  Lemma cmp_pf (X Y Z : cs) (F: Y ->> Z) (G: X ->> Y)  H :
    {f : partial_function | f \solves F} -> {g : partial_function |  g \solves G} ->
    H =~= F \o G -> {h : partial_function |  h \solves H}.
  Proof.
    by case => f ? [g ?] eq; exists (partial_composition f g); rewrite pcmp_spec eq; apply slvs_comp.
  Qed.

  Lemma cmp_pf_tight (X Y Z: cs) (F: Y ->> Z) (G : X ->> Y)  H:
    {f: partial_function |  f \solves F} -> {g: partial_function |  g \solves G} ->
    (F \o G) \tightens H -> {h: partial_function |  h \solves H}.
  Proof.
    case => f ? [g ?] tight; exists (partial_composition f g).
    by rewrite pcmp_spec; apply/slvs_tight/tight/slvs_comp.
  Qed.

  Definition pprd_rlzrf (X Y X' Y': cs) (f g: partial_function):=
    partial_composition
      (partial_composition  (F2PF (@pair B_(Y) B_(Y'))) (f **_pf g))
      (F2PF (fun (phipsi : B_(X) \*_ns B_(X')) => (lprj phipsi, rprj phipsi))).
  
  Lemma F2PF_spec S T (f : S -> T) : F2PF f =~= F2MF f. 
  Proof. by split => [[]| H] /=. Qed.

  Lemma pprd_rlzrf_spec (X Y X' Y' : cs) (f g: partial_function) (F: X ->> Y) (G: X' ->> Y'):
    f \solves F -> g \solves G -> pprd_rlzrf f g \solves (F ** G). 
  Proof. 
    rewrite /pprd_rlzrf !pcmp_spec PF2MF_fprd !F2PF_spec => fprp gprp.
    apply/tight_slvs; first exact/prod.fprd_rlzr_spec/gprp/fprp.
    rewrite fprd_rlzr_comp /= /mf_id.
    apply/tight_comp; first by apply/tight_comp; last split; first by rewrite tight_F2MF.
    by rewrite <- F2MF_fprd; rewrite F2MF_rcmp_F2MF tight_F2MF.
  Qed.

  Lemma pf_fprd (X Y Z V: cs) (F: X ->> Y) (G: Z ->> V) H:
    {f: partial_function |  f \solves F} -> {g: partial_function |  g \solves G} ->
    H =~= F ** G -> {h: partial_function | h \solves H}.
  Proof. by case => f ? [g ?] eq; exists (pprd_rlzrf f g); rewrite eq; apply pprd_rlzrf_spec. Qed.

  Definition fsum_rlzrpf (X Y X' Y' : cs) (f g: partial_function) :=
    partial_composition
      ((F2PF (@inc B_(Y) B_(Y'))) \o_pf (f +s+_pf g))
      (F2PF (@slct B_(X) B_(X'))).

  Lemma psum_rlzrf_spec (X Y X' Y': cs) (f g: partial_function) (F: X ->> Y) (G: X' ->> Y'):
    f \solves F -> g \solves G -> (fsum_rlzrpf f g) \solves (F +s+ G). 
  Proof.
    rewrite /fsum_rlzrpf !pcmp_spec PF2MF_fsum !F2PF_spec => fprp gprp.
    apply /tight_slvs; first exact/sum.fsum_rlzr_spec/gprp/fprp.
    rewrite fsum_rlzr_comp /=/mf_id.
    apply/tight_comp; first by apply /tight_comp; last split; first by rewrite tight_F2MF.
    by rewrite fsum_id rcmp_id_l; apply/tight_ref.
  Qed.

  Lemma sum_pf (X Y X' Y': cs) (F: X ->> Y) (G: X' ->> Y') H:
    {f: partial_function |  f \solves F} -> {g: partial_function |  g \solves G} ->
    H =~= F +s+ G -> {h: partial_function | h \solves H}.
  Proof. by case => f ? [g ?] eq; exists (fsum_rlzrpf f g); rewrite eq; apply psum_rlzrf_spec. Qed.

  Definition speedup n s := (2 ^ (n+s))%nat.

  Definition speedup_machine Q A Q' A' (M : @monotone_machine Q A Q' A') phi nq:=
    M phi (speedup nq.1 7, nq.2). 

  Definition mm2pf Q A Q' A' (M : (@monotone_machine Q A Q' A')) :=
    get_partial_function (speedup_machine M).

  (* Lemma mm2pf_spec Q A Q' A' (M : (@monotone_machine Q A Q' A')) : (mm2pf M) =~= \F_(M). *)
  (* Proof. *)
  (*   have := (@monotone _ _ _ _ _ (M_monotone M)). *)
  (*   Search _ (_ \is_monotone). *)
End partial_functions.
