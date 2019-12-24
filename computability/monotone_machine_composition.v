(* This file provides an abstract envelope for computability theoretical considerations *)
From mathcomp Require Import all_ssreflect.
From mf Require Import all_mf.
Require Import all_cont search PhiN monotone_application FMop seq_cont continuous_machines.
Require Import axioms Classical Psatz.
Require Import cs naming_spaces.
Require Import cs_names.
Require Import iso.

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
Section monotone_machines_product.
  Local Open Scope name_scope.
  Local Open Scope cs_scope.
  Context (X1 Y1 X2 Y2 : cs).
  Notation Q1 := (Q_ X1).
  Notation A1 := (A_ X1).
  Notation Q1' := (Q_ Y1).
  Notation A1' := (A_ Y1).
  Notation Q2 := (Q_ X2).
  Notation A2 := (A_ X2).
  Notation Q2' := (Q_ Y2).
  Notation A2' := (A_ Y2).
  Context (default1 : A1') (default2 : A2').
  Context (M1: monotone_machine Q1 A1 Q1' A1').
  Context (M2: monotone_machine Q2 A2 Q2' A2').
  Definition monotone_machine_product (phi : ((Q1 + Q2) -> (A1 * A2))) nq :=
    match nq.2 with
      | (inl q) => 
          match (M1 ((fst \o_f phi \o_f inl)) (nq.1, q)) with
            | (Some a) => (Some (a, default2))
            | _ => None
          end
      | (inr q) =>
          match (M2 (snd \o_f phi \o_f inr) (nq.1, q)) with
                    | (Some a) => (Some (default1, a))
                    | _ => None
                   end
    end.

  Definition monotone_machine_product_mu (phi : ((Q1 + Q2) -> (A1 * A2))) nq :=
          match nq.2 with
            | (inl q) => 
               (map inl (modulus M1 (fst \o_f phi \o_f inl) (nq.1, q)))
            | (inr q) =>
              (map inr (modulus M2 (snd \o_f phi \o_f inr) (nq.1, q)))
            end.

  Lemma monotone_machine_product_mod : monotone_machine_product_mu \modulus_function_for monotone_machine_product.
  Proof.
    rewrite /monotone_machine_product_mu/monotone_machine_product => phi [n q] psi /=.
    case q => q' c.
    - have c' : (fst \o_f phi) \o_f inl \coincides_with (fst \o_f psi) \o_f inl \on (modulus M1 ((fst \o_f phi) \o_f inl) (n, q')).
    + move : c.
      elim (modulus M1 ((fst \o_f phi) \o_f inl) (n, q')) => // a l IH /= [p1 p2].
      split; first by rewrite p1.
      by apply IH.   
    by rewrite (modulus_correct c').
    have c2' : (snd \o_f phi) \o_f inr \coincides_with (snd \o_f psi) \o_f inr \on (modulus M2 ((snd \o_f phi) \o_f inr) (n, q')).
    - move : c.
      elim (modulus M2 ((snd \o_f phi) \o_f inr) (n, q')) => // a l IH /= [p1 p2].
      split; first by rewrite p1.
      by apply IH.
    by rewrite (modulus_correct c2').
  Qed.

  Lemma mon_mprd: FMop.monotone (monotone_machine_product).
  Proof.
    move => phi q n.
    rewrite /monotone_machine_product.
    case (M_monotone M1 ) => M1_mon M1_term.
    case (M_monotone M2 ) => M2_mon M2_term.
    case q => q' /=.
    - case e : (M1 ((fst \o_f phi) \o_f inl) (n, q')) => [a1' |] //.
      by rewrite M1_mon e.
    case  e' : (M2 ((snd \o_f phi) \o_f inr) (n, q')) => [a2' |] // /= _.
    by rewrite M2_mon e'.
  Qed.

  Lemma monotone_machine_product_mod_mod : monotone_machine_product_mu \modulus_function_for monotone_machine_product_mu.
  Proof.
    rewrite /monotone_machine_product_mu => phi [n q] psi /=.
    case q => q' c.
    - have c' : (fst \o_f phi) \o_f inl \coincides_with (fst \o_f psi) \o_f inl \on (modulus M1 ((fst \o_f phi) \o_f inl) (n, q')).
      + move : c.
        elim (modulus M1 ((fst \o_f phi) \o_f inl) (n, q')) => // a l IH /= [p1 p2].
      split; first by rewrite p1.
      by apply IH.   
    by rewrite (modmod c').
    have c' : (snd \o_f phi) \o_f inr \coincides_with (snd \o_f psi) \o_f inr \on (modulus M2 ((snd \o_f phi) \o_f inr) (n, q')).
    - move : c.
      elim (modulus M2 ((snd \o_f phi) \o_f inr) (n, q')) => // a l IH /= [p1 p2].
      split; first by rewrite p1.
      by apply IH.
    by rewrite (modmod c').
  Qed.

  Lemma term_mprd:
    terminates_with monotone_machine_product
    monotone_machine_product_mu.
  Proof.
    rewrite /monotone_machine_product_mu/monotone_machine_product => phi q n.
    case q => q' /=.
    - case e : (M1 ((fst \o_f phi) \o_f inl) (n, q')) => [a1' |] // _.
      have e0 : (isSome (M1 ((fst \o_f phi) \o_f inl) (n, q'))) by rewrite e.
      move => x.
      case x => a; last by elim (modulus M1 ((fst \o_f phi) \o_f inl) (n.+1,q')) => // y l IH; case => //.
      move => H.
      apply map_inl.
      have mod_term := (modulus_terminating e0).
      apply (mod_term (monm_mon M1)).
      move : H.
      elim (modulus M1 ((fst \o_f phi) \o_f inl) (n.+1,q')) => // y l IH /=.
      case => [| P]; try by case;auto.
      apply or_intror.
      by apply IH.
    case e : (M2 ((snd \o_f phi) \o_f inr) (n, q')) => [a1' |] // _.
    have e0 : (isSome (M2 ((snd \o_f phi) \o_f inr) (n, q'))) by rewrite e.
    move => x.
    case x => a; first by elim (modulus M2 ((snd \o_f phi) \o_f inr) (n.+1,q')) => // y l IH; case => //.
    move => H.
    apply map_inr.
    have mod_term := (modulus_terminating e0).
    apply (mod_term (monm_mon M2)).
    move : H.
    elim (modulus M2 ((snd \o_f phi) \o_f inr) (n.+1,q')) => // y l IH /=.
    case => [| P]; try by case;auto.
    apply or_intror.
    by apply IH.
  Qed.

  Definition product: monotone_machine (Q1+Q2) (A1 * A2) (Q1' + Q2') (A1'*A2').
    exists (Build_continuous_machine monotone_machine_product_mod  monotone_machine_product_mod_mod).
    split.
    - exact /mon_mprd.   
    exact/term_mprd.
  Defined.

  Lemma mprd_spec F G : (\F_M1) \solves F -> (\F_M2) \solves G ->  (\F_product \solves (F ** G)).
  Proof.
  rewrite  /=/monotone_machine_product /=.
  move => H1 H2.
  move => phipsi xy.
  case => /= [[phi psi] [/= prp1 [prp2 prp3]]] .
  have -> : (fst \o_f phipsi \o_f inl) = phi by case : prp1.
  have -> : (snd \o_f phipsi \o_f inr) = psi by case : prp1.
  case => /=; move => [y1 y2] [/= y1y2prp1 y1y2prp2].
  case (H1 phi xy.1 prp2 ) => [| phid P]; first by exists y1.
  case (H2 psi xy.2 prp3 ) => [| psid P']; first by exists y2.
  case phid => f1 f1prp.
  case psid => f2 f2prp.
  split.
  exists (fun (q : Q_ (Y1 \*_cs Y2)) => (match q with
              |inl q' => (((f1 q'), default2)) 
              |inr q' => ((default1, (f2 q')))
              end)).
  move => q1q2'.
  by case q1q2' =>q'; [case (f1prp q') | case (f2prp q')] => n nprp; exists n; rewrite nprp.
  move => Fphi prp.

  have := (P (lprj Fphi)).
  case => [q1' | y1'].
  - case (prp (inl q1')) => n nprp.
    exists n.
    move : nprp.
    case (M1 phi (n,q1')) => // a.
    case.
    by rewrite /lprj /= => <-.
  move => [yprp1 yprp2].
  have := (P' (rprj Fphi)).
  case => [q' | y2'].
  case (prp (inr q')) => n nprp.
  exists n.
  move : nprp.
  case (M2 psi (n,q')) => // a.
  case.
  by rewrite /rprj /= => <-.
  move => [y2'prp1 y2'prp2].
  exists (y1',y2').
  split => //.
  by exists (unpair Fphi); split => // /=.
  Qed.
End monotone_machines_product.
Section monotone_machines_sum.
  Local Open Scope name_scope.
  Local Open Scope cs_scope.
  Context (X1 Y1 X2 Y2 : cs).
  Notation Q1 := (Q_ X1).
  Notation A1 := (A_ X1).
  Notation Q1' := (Q_ Y1).
  Notation A1' := (A_ Y1).
  Notation Q2 := (Q_ X2).
  Notation A2 := (A_ X2).
  Notation Q2' := (Q_ Y2).
  Notation A2' := (A_ Y2).
  Context (M1: monotone_machine Q1 A1 Q1' A1').
  Context (M2: monotone_machine Q2 A2 Q2' A2').
  Definition monotone_machine_sum (phi : ((Q1 * Q2) -> (A1 + A2))) nq :=
    match (phi (someq,someq)) with
    | (inl a) => match (M1 (lslct phi a) (nq.1, nq.2.1)) with
                | Some a' => (Some (inl a'))
                | _ => None
                end
               
      | (inr a) => match (M2 (rslct phi a) (nq.1, nq.2.2)) with
                | Some a' => (Some (inr a'))
                | _ => None
                end
    end.

  Definition monotone_machine_sum_mu (phi : ((Q1 * Q2) -> (A1 + A2))) nq  :=
    match (phi (someq, someq)) with
      | (inl a) =>
          [:: (someq, someq)] ++ [seq (i,someq) | i <- (modulus M1 (lslct phi a) (nq.1, nq.2.1))]
     | (inr a) =>
       [:: (someq, someq)] ++ [seq (someq,i) | i <- (modulus M2 (rslct phi a) (nq.1, nq.2.2))]
      end.
  
  Lemma monotone_machine_sum_mod : monotone_machine_sum_mu \modulus_function_for monotone_machine_sum.
  Proof.
    rewrite /monotone_machine_sum_mu/monotone_machine_sum => phi [n [q1 q2]] psi.
    case e : (phi (someq, someq)) => [a|a];rewrite !coin_cat => [[[<- _]]] P;rewrite e.
    have P1' : (lslct phi a) \coincides_with (lslct psi a) \on (modulus M1 (lslct phi a) (n, q1)).
    - have /= := P.
      elim (modulus M1 _) => // x l IH [H1 H2].
      split; by [apply IH | rewrite /lslct H1].
    by rewrite (modulus_correct P1').
    have P2' : (rslct phi a) \coincides_with (rslct psi a) \on (modulus M2 (rslct phi a) (n, q2)).
    - have /= := P.
      elim (modulus M2 _) => // x l IH [H1 H2].
      split; by [apply IH | rewrite /rslct H1].
    by rewrite (modulus_correct P2').
  Qed.

  Lemma mon_msum: FMop.monotone (monotone_machine_sum).
  Proof.
    move => phi q n.
    rewrite /monotone_machine_sum.
    case (M_monotone M1 ) => M1_mon M1_term.
    case (M_monotone M2 ) => M2_mon M2_term.
    case (phi (someq, someq)) => q0 /= H.
    rewrite M1_mon => //.
    move : H.
    by case (M1 _) => //.
    rewrite M2_mon => //.
    move : H.
    by case (M2 _) => //.
  Qed.

  Lemma monotone_machine_sum_mod_mod : monotone_machine_sum_mu \modulus_function_for monotone_machine_sum_mu.
  Proof.
    rewrite /monotone_machine_sum_mu => phi [n [q1 q2]] psi.
    case e : (phi (someq, someq)) => [a|a];rewrite !coin_cat => [[[<- _]]] P;rewrite e.
    have P1' : (lslct phi a) \coincides_with (lslct psi a) \on (modulus M1 (lslct phi a) (n, q1)).
    - have /= := P.
      elim (modulus M1 _) => // x l IH [H1 H2].
      split; by [apply IH | rewrite /lslct H1].
    by f_equal;f_equal; apply modmod.
    have P2' : (rslct phi a) \coincides_with (rslct psi a) \on (modulus M2 (rslct phi a) (n, q2)).
    - have /= := P.
      elim (modulus M2 _) => // x l IH [H1 H2].
      split; by [apply IH | rewrite /rslct H1].
    by f_equal;f_equal; apply modmod.
  Qed.

  Lemma term_msum:
    terminates_with monotone_machine_sum
    monotone_machine_sum_mu.
  Proof.
    rewrite /monotone_machine_sum_mu/monotone_machine_sum => phi [q1 q2] n.
    case (phi (someq, someq)) => q0.
    - case e : (M1 _) =>// _.
      have e0 : (isSome (M1 (lslct phi q0) (n, q1))) by rewrite e.
      have mod_term := (modulus_terminating e0).
      apply cons_subs; split; first by apply or_introl.
      apply subl_cat.
      apply or_intror => /=.
      apply func.map_subl.
      by apply (mod_term (monm_mon M1)).
    case e : (M2 _) =>// _.
    have e0 : (isSome (M2 (rslct phi q0) (n, q2))) by rewrite e.
    have mod_term := (modulus_terminating e0).
    apply cons_subs; split; first by apply or_introl.
    apply subl_cat.
    apply or_intror => /=.
    apply func.map_subl.
    by apply (mod_term (monm_mon M2)).
  Qed.

  Definition sum: monotone_machine (Q1*Q2) (A1 + A2) (Q1' * Q2') (A1' + A2').
    exists (Build_continuous_machine monotone_machine_sum_mod  monotone_machine_sum_mod_mod).
    split.
    - exact /mon_msum.   
    exact/term_msum.
  Defined.

  Lemma msum_spec F G : (\F_M1) \solves F -> (\F_M2) \solves G ->  (\F_sum \solves (F +s+ G)).
  Proof.
  rewrite  /=/monotone_machine_sum => H1 H2 phi x [x0 [x0prp P1]] P2.
  split.
  - rewrite FM_dom  => q /=.
    move : x0 x0prp P1.
    rewrite /slct /= => [[a aprp | a aprp ]]; move : P2; case x => x' [[]] s sprp P //.
    + case (H1 a x' P); first by exists s.
      case => psi psiprp Fqprp.
      exists (inl (psi q.1)).
      case (psiprp q.1) => n nprp.
      exists n.
      move : aprp.
      by case (phi (someq, someq)) => a0 [] // ->;rewrite nprp.
    case (H2 a x' P); first by exists s.
    case => psi psiprp Fqprp.
    exists (inr (psi q.2)).
    case (psiprp q.2) => n nprp.
    exists n.
    move : aprp.
    by case (phi (someq, someq)) => a0 [] // ->;rewrite nprp.
  move => psi psiprp.
  move : x0 x0prp P1.
  rewrite /slct /= => [[phil philprp | phir phirprp ]]; move : P2.
  - case x => x0 //.
    case.
    case => s sprp P //.
    have := (psiprp (someq, someq)).
    move :philprp.
    case e: (phi (someq, someq)) => [a0 | a0] // [] prp .
    rewrite prp.
    case => m0.
    case (M1 _ _) => b0 // [] B.
    case (H1 phil x0 P) => [| dom ex]; first by exists s.
    case (ex (lslct psi b0)).
    move => q'.
    case (psiprp (q', someq)) => n.
    rewrite e. 
    rewrite prp /=.
    case e1 : (M1 _ _) => [m1v | ] // [m1P].
    exists n. 
    rewrite e1.
    f_equal. 
    rewrite /lslct.
    by rewrite <- m1P.
    rewrite /lslct.
    move => h [hprp1 hprp2].
    exists (inl h).
    split => //.
    exists (inl (lslct psi b0)).
    rewrite /slct.
    rewrite <-B.
    split => //.
  case x => x0 //.
  case.
  case => s sprp P //.
  have := (psiprp (someq, someq)).
  move :phirprp.
  case e: (phi (someq, someq)) => [a0 | a0] // [] prp .
  rewrite prp.
  case => m0.
  case (M2 _ _) => b0 // [] B.
  case (H2 phir x0 P) => [| dom ex]; first by exists s.
  case (ex (rslct psi b0)).
  move => q'.
  case (psiprp (someq,q')) => n.
  rewrite e. 
  rewrite prp /=.
  case e1 : (M2 _ _) => [m2v | ] // [m2P].
  exists n. 
  rewrite e1.
  f_equal. 
  rewrite /rslct.
  by rewrite <- m2P.
  move => h [hprp1 hprp2].
  exists (inr h).
  split => //.
  exists (inr (rslct psi b0)).
  rewrite /slct.
  rewrite <-B.
  split => //.
  Qed.
End monotone_machines_sum.
Section constructions.
Local Open Scope name_scope.
Local Open Scope cs_scope.
Lemma cmp_machine (S T U : cs) (F : S ->> T) (G : U ->> S)  H (a : A_ S) : {f : (monotone_machine  Q_ S A_ S Q_ T A_ T) |  \F_f \solves F} -> {g : (monotone_machine  Q_ U A_ U Q_ S A_ S)|  \F_g \solves G} -> H =~= F \o G -> {h : (monotone_machine  Q_ U A_ U Q_ T A_ T) |  \F_h \solves H}.
Proof.
  case => f fprp.
  case => g gprp.
  exists (compose a g f).
  apply /tight_slvs; last first.
  apply mcpm_spec.
  rewrite slvbl_prpr => //.
  apply slvs_comp => //.
  apply fprp.
  apply gprp.
  by auto.
Defined.
Lemma cmp_machine_tight (S T U : cs) (F : S ->> T) (G : U ->> S)  H (a : A_ S) : {f : (monotone_machine  Q_ S A_ S Q_ T A_ T) |  \F_f \solves F} -> {g : (monotone_machine  Q_ U A_ U Q_ S A_ S)|  \F_g \solves G} -> (F \o G) \tightens H -> {h : (monotone_machine  Q_ U A_ U Q_ T A_ T) |  \F_h \solves H}.
Proof.
  case => f fprp.
  case => g gprp.
  exists (compose a g f).
  apply /tight_slvs; last first.
  apply mcpm_spec.
  apply /slvs_tight.
  apply slvs_comp => //.
  apply fprp.
  apply gprp.
  by auto.
Defined.
Lemma prd_machine (S T U V: cs) (F : S ->> T) (G : U ->> V) H (a1 : A_ T) (a2 : A_ V)  : {f : (monotone_machine  Q_ S A_ S Q_ T A_ T) |  \F_f \solves F} -> {g : (monotone_machine  Q_ U A_ U Q_ V A_ V)|  \F_g \solves G} -> H =~= (F ** G) -> {h : (monotone_machine  Q_ (S \*_cs U) A_ (S \*_cs U) Q_ (T \*_cs V) A_ (T \*_cs V)) | \F_h \solves H}.
Proof.
  case => f fprp.
  case => g gprp prp.
  exists (product a1 a2 f g).
  rewrite prp.
  by apply mprd_spec.
Defined.
Lemma sum_machine (S T U V: cs) (F : S ->> T) (G : U ->> V) H  : {f : (monotone_machine  Q_ S A_ S Q_ T A_ T) |  \F_f \solves F} -> {g : (monotone_machine  Q_ U A_ U Q_ V A_ V)|  \F_g \solves G} -> H =~= (F +s+ G) -> {h : (monotone_machine  Q_ (S \+_cs U) A_ (S \+_cs U) Q_ (T \+_cs V) A_ (T \+_cs V)) | \F_h \solves H}.
Proof.
  case => f fprp.
  case => g gprp prp.
  exists (sum f g).
  rewrite prp.
  by apply msum_spec.
Defined.

End constructions.
Section partial_function_product.
  Context (S T U V: Type).
  Local Notation pf := partial_function.
  Definition partial_product (f: pf S T) (g: pf U V): (pf (S*U)%type (T*V)%type) .
    exists (set_prod (domain f) (domain g)).
    case => [[s1 s2] /= [p1 p2]].
    by apply ((f (exist (domain f) s1 p1)), (g (exist (domain g) s2 p2))).
  Defined.
  Lemma pprd_spec f g: partial_product f g =~= f ** g.
  Proof.
    move => [s1 s2] [t1 t2].
    split => /= [[[p1 p2 [<- <-]]] | [[p1 [<- [p2 <-]]]]]; last by exists (conj p1 p2).
    split; by [exists  p1 | exists p2 ].
  Qed.
End partial_function_product.
Definition set_sum S T (P: mf_set.subset S) (Q: mf_set.subset T) :=
  make_subset (fun s => match s with
                     | inl s' => P s'
                     | inr s' => Q s'
                     end).

Section partial_function_sum.
  Context (S T U V: Type).
  Local Notation pf := partial_function.
  Definition partial_sum (f: pf S T) (g: pf U V): (pf (S+U)%type (T+V)%type) .
    exists (set_sum (domain f) (domain g)).
    case => [[s prp | p prp]].
    by apply (inl (f (exist (domain f) s prp))).
    by apply (inr (g (exist (domain g) p prp))).
  Defined.

  Lemma psum_spec f g: partial_sum f g =~= f +s+ g.
  Proof.
    move => [s [t | t']| s' [t | t']]; split => /= //; try by case => x.
    by case => [x [<-]]; exists x.
    by case => [x [<-]]; exists x.
    by case => [x [<-]]; exists x.
    by case => [x [<-]]; exists x.
  Qed.
End partial_function_sum.

Section partial_functions.
Local Open Scope name_scope.
Local Open Scope cs_scope.
Lemma cmp_pf (S T U : cs) (F : S ->> T) (G : U ->> S)  H : {f : (partial_function  B_(S) B_(T)) |  f \solves F} -> {g : (partial_function  B_(U) B_(S))|  g \solves G} -> H =~= F \o G -> {h : (partial_function  B_(U) B_(T)) |  h \solves H}.
Proof.
  case => f fprp.
  case => g gprp.
  exists (partial_composition f g).
  rewrite pcmp_spec.
  rewrite H0.
  apply slvs_comp => //.
Defined.

Lemma cmp_pf_tight (S T U : cs) (F : S ->> T) (G : U ->> S)  H  : {f : (partial_function  B_(S) B_(T)) |  f \solves F} -> {g : (partial_function  B_(U) B_(S))|  g \solves G} -> (F \o G) \tightens H -> {h : (partial_function  B_(U) B_(T)) |  h \solves H}.
Proof.
  case => f fprp.
  case => g gprp.
  exists (partial_composition f g).
  rewrite pcmp_spec.
  apply /slvs_tight.
  apply /slvs_comp/gprp/fprp.
  by apply H0.
Defined.


  Definition pprd_rlzrf (X Y X' Y' : cs) (f: partial_function B_(X) B_(Y) ) (g: partial_function B_(X') B_(Y'))  := (partial_composition (partial_composition  (F2PF (@pair B_(Y) B_(Y'))) (partial_product f g)) (F2PF (fun (phipsi : B_(X) \*_ns B_(X')) => (lprj phipsi, rprj phipsi)))).
  Lemma F2PF_spec S T (f : S -> T) : (F2PF f) =~= (F2MF f). 
  Proof.
    move => x y.
    by split => [[[ ]]| H] /= //.
  Qed.

Lemma pprd_rlzrf_spec (X Y X' Y' : cs) (f: partial_function B_(X) B_(Y) ) (g: partial_function B_(X') B_(Y'))  F G: (f \solves F) -> (g \solves G) -> (pprd_rlzrf f g) \solves (F ** G). 
Proof.
  rewrite /pprd_rlzrf => fprp gprp.
  rewrite !pcmp_spec pprd_spec  !F2PF_spec.
  apply /tight_slvs.
  apply /prod.fprd_rlzr_spec/gprp/fprp.
  rewrite fprd_rlzr_comp.
  apply /tight_comp => /= //.
  apply /tight_comp; first by rewrite tight_F2MF.
  by move => x y; by split.
  rewrite /mf_id.
  rewrite <- F2MF_fprd.
  rewrite F2MF_rcmp_F2MF tight_F2MF.
  by rewrite /unpair.
Qed.

Lemma prd_pf (S T U V: cs) (F : S ->> T) (G : U ->> V) H : {f : (partial_function  B_(S) B_(T)) |  f \solves F} -> {g : (partial_function  B_(U) B_(V))|  g \solves G} -> H =~= (F ** G) -> {h : (partial_function  B_(S \*_cs U) B_(T \*_cs V)) | h \solves H}.
Proof.
  case => f fprp.
  case => g gprp prp.
  exists (pprd_rlzrf f g).
  rewrite prp.
  by apply pprd_rlzrf_spec.
Defined.

Definition psum_rlzrf (X Y X' Y' : cs) (f: partial_function B_(X) B_(Y) ) (g: partial_function B_(X') B_(Y'))  := (partial_composition (partial_composition  (F2PF (@inc B_(Y) B_(Y'))) (partial_sum f g)) (F2PF (@slct B_(X) B_(X')))).

Lemma psum_rlzrf_spec (X Y X' Y' : cs) (f: partial_function B_(X) B_(Y) ) (g: partial_function B_(X') B_(Y'))  F G: (f \solves F) -> (g \solves G) -> (psum_rlzrf f g) \solves (F +s+ G). 
Proof.
  rewrite /psum_rlzrf => fprp gprp.
  rewrite !pcmp_spec psum_spec  !F2PF_spec.
  apply /tight_slvs.
  apply /sum.fsum_rlzr_spec/gprp/fprp.
  rewrite fsum_rlzr_comp.
  apply /tight_comp => /= //.
  apply /tight_comp; first by rewrite tight_F2MF.
  by move => x y; by split.
  rewrite fsum_id rcmp_id_l.
  exact/tight_ref.
Qed.

Lemma sum_pf (S T U V: cs) (F : S ->> T) (G : U ->> V) H : {f : (partial_function  B_(S) B_(T)) |  f \solves F} -> {g : (partial_function  B_(U) B_(V))|  g \solves G} -> H =~= (F +s+ G) -> {h : (partial_function  B_(S \+_cs U) B_(T \+_cs V)) | h \solves H}.
Proof.
  case => f fprp.
  case => g gprp prp.
  exists (psum_rlzrf f g).
  rewrite prp.
  by apply psum_rlzrf_spec.
Defined.

Definition speedup n s := (2 ^ (n+s))%nat.
Definition speedup_machine Q A Q' A' (M : (@monotone_machine Q A Q' A')) phi nq := (M phi ((speedup nq.1 7), nq.2)). 

Definition mm2pf Q A Q' A' (M : (@monotone_machine Q A Q' A')) := (get_partial_function (speedup_machine M)).

(* Lemma mm2pf_spec Q A Q' A' (M : (@monotone_machine Q A Q' A')) : (mm2pf M) =~= \F_(M). *)
(* Proof. *)
(*   have := (@monotone _ _ _ _ _ (M_monotone M)). *)
(*   Search _ (_ \is_monotone). *)
End partial_functions.
