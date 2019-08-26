(* This file provides an abstract envelope for computability theoretical considerations *)
From mathcomp Require Import all_ssreflect.
From mf Require Import all_mf.
Require Import all_cont PhiN seq_cont.
Require Import axioms Classical Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FM_operator.
  Context (B Q' A': Type).
  Notation B' := (Q' -> A').
  Local Notation "B o~> B'" := (B -> nat * Q' -> option A') (at level 2).

  Notation "M '\^' phi" := ((M:B o~> B') phi) (at level 30).
  
  Definition operator (M: B o~> B') :=
    make_mf (fun phi Mphi => forall q', exists n, M phi (n, q') = Some (Mphi q')).
  
  Notation "\F_ M" := (operator M) (format "'\F_' M", at level 2).

  Lemma FM_Phi M phi Fphi:
    Fphi \from \F_M phi <-> \Phi_(M phi) \extends F2MF Fphi.
  Proof.
    split => [val q' a' <-| exte q']; first by have [n eq]:= val q'; exists n.
    by have [ | n]//:= exte q' (Fphi q'); exists n.
  Qed.

  Lemma FN_Phi (N: nat * Q' -> option A') phi Fphi:
    Fphi \from \F_(cnst N) phi <-> \Phi_N \extends F2MF Fphi.
  Proof. exact/FM_Phi. Qed.

  Lemma FM_dom M phi: phi \from dom \F_M <-> \Phi_(M phi) \is_total.
  Proof.
    split => [[Fphi val] q' | tot]; first by have [n eq]:= val q'; exists (Fphi q'); exists n.
    by exists (evaluate tot) => q'; apply/eval_spec.
  Qed.    
    
  Notation "M '\evaluates' F" := ((\F_M) \tightens F) (at level 40).

  Lemma eval_FM M: M \evaluates \F_M.
  Proof. by split. Qed.

  Lemma exte_sym_F2MF S T (f: S ->> T) g:
    f \is_singlevalued -> f \extends (F2MF g) -> (F2MF g) \extends f.
  Proof. by move => sing exte s t fst; rewrite (sing s t (g s)) => //; apply exte. Qed.

  Lemma eval_F2MF M F:
    M \evaluates (F2MF F) <-> \F_M =~= F2MF F.
  Proof.
    split => [eval | <-]; last exact/eval_FM.
    rewrite exte_equiv; split; first exact/sing_tight_exte/eval/F2MF_sing.
    by move => s t fst; apply /(tight_val eval)/fst/F2MF_tot.
  Qed.
  
  Lemma F2MF_mach (F: B -> B'):
    (fun phi nq => Some(F phi nq.2)) \evaluates (F2MF F).
  Proof.
    move => phi _; split => [ | Fphi ev]; first by exists (F phi) => q'; exists 0.
    by apply functional_extensionality => q'; have [c val]:= ev q'; apply Some_inj.
  Qed.

  Definition monotone_in (M: B o~> B') phi q' := monotone_in (M phi) q'.
  
  Lemma monn_spec (M: B o~> B) phi q': monotone_in M phi q' <->
	  forall a' n m, n <= m -> M phi (n,q') = Some a' -> M phi (m,q') = Some a'.
  Proof. exact/mon_in_spec. Qed.

  Lemma mon_in_eq M phi q' n m a' b':
    monotone_in M phi q' -> M phi (n,q') = Some a' -> M phi (m,q') = Some b' -> a' = b'.
  Proof.
    case/orP: (leq_total n m) => ineq /mon_in_spec mon eq eq'; apply /Some_inj.
      by rewrite -eq'; symmetry; apply/mon/eq.
    by rewrite -eq; apply/mon/eq'.
  Qed.

  Definition monotone M := forall phi q', monotone_in M phi q'.
  Notation "M '\is_monotone'" := (monotone M) (at level 2).

  Lemma mon_spec (M: B o~> B'): M \is_monotone <-> forall phi q' a' n m,
	n <= m -> M phi (n,q') = Some a' -> M phi (m,q') = Some a'.
  Proof. by split => mon phi; apply/mon_spec/mon. Qed.
    
  Definition monotone_dom M := make_subset (fun phi => forall q', monotone_in M phi q').
  Lemma mon_sing_restr M: \F_M|_(monotone_dom M) \is_singlevalued.
  Proof.
    move => phi Fphi Fphi' [mon FphiFphi] [_ FphiFphi'].
    apply functional_extensionality => q'.
    have [c eq]:= FphiFphi q'.
    have [d eq']:= FphiFphi' q'.
    exact/mon_in_eq/eq'/eq/mon.
  Qed.

  Lemma mon_sing (M: B o~> B):
    M \is_monotone -> \F_M \is_singlevalued.
  Proof. by move => mon; rewrite -(restr_dom \F_M); apply/restr_sing/mon_sing_restr => phi _. Qed.
    
  Lemma mon_eval M F: M \is_monotone -> F \is_singlevalued ->
	M \evaluates F <-> \F_M \extends F.
  Proof.
    move => mon sing; split => [eval | eval]; first exact/sing_tight_exte.
    exact/exte_tight/eval/mon_sing.
  Qed.

  Definition right_away (M: B o~> B') phi := make_mf (fun q' a' => M phi (0,q') = some a').

  Lemma ra_sing M phi: (right_away M phi) \is_singlevalued.
  Proof. by move => q' a' b' /=eq1 eq2; apply/Some_inj; rewrite -eq1 -eq2. Qed.

  Definition static (M: B o~> B') phi:= make_mf (fun q a => forall n, M phi (n,q) = some a).

  Definition F2M (F: B -> (Q' -> A')) phi nq' := F2N (F phi) nq'.

  Lemma F2M_spec F: \F_(F2M F) =~= F2MF F.
  Proof.
    move => phi Fphi; split => [val | <-]; last by exists 0.
    by apply/functional_extensionality => q'; have [_ []]:= val q'.
  Qed.
End FM_operator.
Notation "\F_ M" := (operator M) (format "'\F_' M", at level 2).
Notation "M '\evaluates' F" := (\F_M \tightens F) (at level 2).
Notation "M '\is_monotone'" := (monotone M) (at level 2).

Section use_first.
  Context (B Q' A': Type).
  Notation B' := (Q' -> A').
  Context (M: B -> nat * Q' -> option A').
  
  Definition use_first phi nq:= use_first (M phi) nq.
  
  Lemma sfrst_mon: use_first \is_monotone.
  Proof. by move => phi; apply/sfrst_mon. Qed.

  Lemma sfrst_sing: \F_use_first \is_singlevalued.
  Proof. exact/mon_sing/sfrst_mon. Qed.

  Lemma sfrst_spec: \F_use_first \tightens \F_M.
  Proof.
    rewrite tight_spec.
    split => [phi [Fphi val] | phi Fphi [phifd val q']]; last first.
    - by have [n eq]:= val q';exists (search (fun k => M phi (k,q')) n).
    rewrite /=.
    suff /full_choice: forall q', exists a', exists n, use_first phi (n,q') = Some a' by trivial.
    move => q'; have [n eq]:= val q'.
    have: M phi (search (fun k => M phi (k,q')) n, q').
    - by apply/(@search_correct (fun k => M phi (k,q'))); rewrite eq.
    by case E: (M phi (search (fun k => M phi (k,q')) n, q')) => [b | ] //_; exists b; exists n.
  Qed.

  Lemma sfrst_dom: dom (\F_M) === dom (\F_use_first).
  Proof. by move => phi; split => [phifd | ]; rewrite FM_dom -sfrst_tot -FM_dom. Qed.

  Lemma mon_sfrst_spec: M \is_monotone <-> forall phi n q', M phi (n,q') = use_first phi (n,q').
  Proof. by split => mon phi; apply/mon_sfrst/mon. Qed.

  Lemma mon_sfrst: M \is_monotone -> forall phi n q', M phi (n,q') = use_first phi (n,q').
  Proof. by move => mon; apply/mon_sfrst_spec. Qed.
  
  Lemma sing_sfrst_spec: \F_M \is_singlevalued <-> \F_M =~= \F_(use_first).
  Proof.
    split => [sing phi Fphi | ->]; last exact/sfrst_sing.
    rewrite !FM_Phi.
    split => exte.
    - have tot: \Phi_(use_first phi) \is_total.
      + by rewrite -sfrst_tot => q'; exists (Fphi q'); apply/exte.
      rewrite -(@eval_sing_spec _ _ _ tot); last exact/PhiN.sfrst_sing.
      suff ->: (evaluate tot) = Fphi by apply/exte_refl.
      apply/sing/FM_Phi/exte/FM_Phi/exte_trans/tot_tight_exte/PhiN.sfrst_spec.
      + exact/eval_spec.
      exact/sfrst_tot.
    apply/exte_trans; first exact/exte.
    apply/tot_tight_exte/PhiN.sfrst_spec/sfrst_tot => q'.
    by exists (Fphi q'); apply/exte.
  Qed.    

  Lemma sing_sfrst: \F_M \is_singlevalued -> \F_M =~= \F_(use_first).
  Proof. by move => sing; apply/sing_sfrst_spec. Qed.
End use_first.

Section use_first_continuous.
  Local Open Scope name_scope.
  Context (Q A Q' A': Type).
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Context (M: B -> nat * Q' -> option A').

  Lemma sfrst_cont: \F_M \is_continuous -> \F_(use_first M) \is_continuous.
  Proof. by move => cont; rewrite -sing_sfrst; last exact/cont_sing. Qed.

  Lemma sfrst_cntf: M \is_continuous_function -> (use_first M) \is_continuous_function.
  Proof.
    move => cntf phi.
    have [mf mod]:= cntf phi.
    exists (fun nq' => (fix L n q' := match n with
                                     | 0 => mf (0, q')
                                     | S n' => L n' q' ++ mf (n, q')
                                     end) nq'.1 nq'.2); case => [n q'] psi /= coin.
    rewrite /use_first /PhiN.use_first/=.
    have coin': forall k, k <= n -> phi \coincides_with psi \on (mf (k,q')).
    - move => k ineq; apply/coin_subl/coin; move: ineq => /subnK <-.
      elim: (n - k) => [ | m ih q lstn]; last by apply/L2SS_cat; left; apply/ih.
      by rewrite add0n; case: (k) => // k' q lstn; first apply/L2SS_cat; right.
    suff ->: search (fun k => M phi (k,q')) n = search (fun k => M psi (k, q')) n.
    - exact/mod/coin'/search_le.
    apply/search_cont => k ineq.
    rewrite (@mod (k,q') psi) //.
    by apply/coin'/leq_trans; first exact/ineq; exact/search_le.
  Qed.
  
  Definition get_pf: partial_function B B'.
    exists (make_subset (fun phi => \Phi_(use_first M phi) \is_total)); case => phi tot.
    exact/(evaluate tot).
  Defined.

  Lemma gtpf_dom phi: phi \from dom get_pf <-> \Phi_(M phi) \is_total.
  Proof. by rewrite -PF2MF_dom /=; symmetry; apply/sfrst_tot. Qed.

  Lemma gtpf_spec: get_pf =~= \F_(use_first M).
  Proof.
    apply/exte_equiv; split => [phi Fphi val | phi Fphi [phifd <-]]; last exact/FM_Phi/eval_spec.
    have P : \Phi_(use_first M phi) \is_total by apply/FM_dom; exists Fphi.
    by exists P; apply/sfrst_sing/val => q'; apply/ (@eval_spec _ _ _ P q').
  Qed.

  Lemma gtpf_cont: \F_M \is_continuous -> get_pf \is_continuous.
  Proof. by move => cont; rewrite gtpf_spec; apply/sfrst_cont. Qed.

  Definition monotone_listfunction (Lf: Q' -> nat -> seq Q) :=
    forall q' n, (Lf q' n) \is_sublist_of (Lf q' n.+1).

  Lemma mnlf_spec Lf:
    monotone_listfunction Lf <-> forall q' n m, n <= m -> (Lf q' n) \is_sublist_of (Lf q' m).
  Proof.
    split => [mon q' n m /subnK <- | mon q' n]; last exact/mon.
    by elim: (m - n) => // k ih; rewrite addSn; apply/subs_trans/mon.
  Qed.

  Definition monotone_modulus (mu: B -> nat * Q' -> seq Q):=
    forall phi q' n, (mu phi (n, q')) \is_sublist_of (mu phi (n.+1, q')).

  Lemma monm_spec mu:
    monotone_modulus mu <-> forall phi q' n m, n <= m -> (mu phi (n, q')) \is_sublist_of (mu phi (m, q')).
  Proof. by split => mon phi; apply/mnlf_spec/mon. Qed.

  Lemma sfrst_modf_mon mu: mu \modulus_function_for M -> monotone_modulus mu ->
                           mu \modulus_function_for (use_first M).
  Proof.
    move => /modf_spec mod /monm_spec mon.
    apply/modf_spec => phi.
    rewrite cmod_F2MF;case => n q' phi' coin.
    specialize (mod phi); move: mod; rewrite cmod_F2MF => mod.
    rewrite /use_first /PhiN.use_first /=.
    suff <-: search (fun k => M phi (k, q')) n = search (fun k => M phi' (k, q')) n.
    - exact/mod/coin_subl/coin/mon/search_le.
    apply/search_cont => k ineq.
    have -> := (mod (k, q') phi' _) => //.
    apply/coin_subl/coin/mon/leq_trans; first exact/ineq.
    exact/search_le.      
  Qed.

  Fixpoint make_monotone (Lf: nat * Q' -> seq Q) q' n :=
    match n with
    | 0 => Lf (0,q')
    | n'.+1 => make_monotone Lf q' n' ++ Lf (n,q')
    end.

  Lemma mkm_mon Lf: monotone_listfunction (make_monotone Lf).
  Proof. by move => q' n /= q'' lstn; apply/L2SS_cat; left. Qed.

  Lemma mkm_subl Lf  q' n: (Lf (n, q')) \is_sublist_of (make_monotone Lf q' n).
  Proof. by case: n => // n /= q'' lstn; apply/L2SS_cat; right. Qed.
    
  Definition make_mod_mon (mu: B -> nat * Q' -> seq Q) phi nq' := make_monotone (mu phi) nq'.2 nq'.1.

  Lemma mkmm_mon mu: monotone_modulus (make_mod_mon mu).
  Proof. by move => phi q' n /= q'' lstn; apply/L2SS_cat; left. Qed.

  Lemma sfrst_modf mu:
    mu \modulus_function_for M -> (make_mod_mon mu) \modulus_function_for (use_first M).      
  Proof.
    move => /modf_spec mod.
    apply/sfrst_modf_mon/mkmm_mon.
    apply/modf_spec => phi.
    apply/cmod_F2MF; case => n q' phi' coin.
    specialize (mod phi); move: mod; rewrite cmod_F2MF => mod.
    apply/mod/coin_subl/coin => q''.
    elim: (n) => //n' ih lstn.
    rewrite /make_mod_mon.
    by apply/L2SS_cat; right.
  Qed.
End use_first_continuous.      

Section cost_bounds.
  Local Open Scope name_scope.
  Context (A A' Q Q': Type).
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Local Notation "B o~> B'" := (B -> nat * Q' -> option A') (at level 2).

  Definition cstb (M: B o~> B') phi nq' :=
    let n := nq'.1 in
    let q' := nq'.2 in
    if M phi (n, q') then Some n else None.

  Lemma cstb_spec (M: B o~> B') phi cf: cf \from \F_(cstb M) phi <-> forall q', M phi (cf q', q').
  Proof.
    split => val q'; have := val q'; rewrite/cstb/=; first by case => n; case: ifP => //= Pn [<-].
    by move => Pn; exists (cf q'); rewrite Pn.
  Qed.

  Lemma cstb_dom M: dom \F_(cstb M) === dom \F_M.
  Proof.
    move => phi; split => [/FM_dom tot | /FM_dom tot].
    - apply/FM_dom => q'.
      have [n [m]]:= tot q'.
      rewrite /cstb /=; case: ifP => //.
      case val: (M phi (m, q')) => [a' | ]// _ _.
      by exists a'; exists m.
    apply/FM_dom => q'.
    have [a' [n val]]:= tot q'.
    by exists n; exists n; rewrite /cstb; case: ifP => //; rewrite val.
  Qed.

  Definition cost_machine M := use_first (cstb M).
  
  Lemma cstm_spec M phi cf: cf \from \F_(cost_machine M) phi <->
                          forall q', M phi (cf q', q') /\ (forall n, M phi (n, q') -> cf q' <= n).
  Proof.
    split => [cst q' | prp q'].
    - split; have [n]:= cst q'; rewrite/cost_machine/use_first/PhiN.use_first/cstb/=; case: ifP => // Pn [<-] //.
      by move => k Pk; apply/search_min; rewrite Pk.
    exists (cf q').
    have [Pc min]:= prp q'.
    rewrite /cost_machine/use_first/PhiN.use_first/cstb /=.
    case: ifP => [Ps | fls].
    f_equal.
    have /leP:= min _ Ps.
    suff /leP: search (fun k => if M phi (k, q') then some k else None) (cf q') <= cf q' by lia.
    exact/search_le.
    exfalso; suff: false by trivial.
    rewrite -fls.
    have := @search_correct (fun k => if M phi (k, q') then some k else None) (cf q').
    rewrite Pc; case: ifP => //<- fls'.
    exfalso; suff: @None A' by trivial.
    exact/fls'.
  Qed.

  Definition cost M:= get_pf (cstb M).
  
  Lemma cost_spec M phi:
    forall q', M (sval phi) (cost M phi q', q')
               /\
               forall n, M (sval phi) (n, q') -> cost M phi q' <= n.
  Proof. by move: phi => [phi phifd]; apply/cstm_spec; apply/gtpf_spec; exists phifd. Qed.

  Lemma cost_dom M: dom (cost M) === dom \F_M.
  Proof. by move => phi; rewrite -cstb_dom gtpf_dom -FM_dom. Qed.
    
  Lemma cstb_modf M mu: mu \modulus_function_for M -> mu \modulus_function_for (cstb M).
  Proof.
    move => /modf_spec mod.
    rewrite modf_spec => phi.
    rewrite cmod_F2MF; case => n q' phi' coin.
    move : (mod phi); rewrite cmod_F2MF => mod'.
    by rewrite /cstb (mod' _ _ coin).
  Qed.  
  
  Lemma cstb_cntf M: M \is_continuous_function -> cstb M \is_continuous_function.
  Proof.
    move => cont phi.
    have [Lf mod]:= cont phi.
    exists Lf; case => n q' phi' coin.
    by rewrite /cstb (mod _ _ coin).
  Qed.

  Lemma cost_val_spec (M: B -> nat * Q' -> option A') phi q' n:
    M (sval phi) (n, q') -> cost M phi q' = search (fun k => M (sval phi) (k, q')) n.
  Proof.
    move => val.
    have [val' min]:= cost_spec phi q'.
    have /leP : cost M phi q' <= search (fun k => M (sval phi) (k, q')) n.
    - exact/min/(@search_correct (fun k => M (sval phi) (k, q'))).
    suff /leP: search (fun k => M (sval phi) (k, q')) n <= cost M phi q' by lia.
    exact/search_min.
  Qed.

  Lemma sfrst_cntf_cont (M: B -> nat * Q' -> option A'):
    M \is_continuous_function -> \F_(use_first M) \is_continuous.
  Proof.
    move => cntf phi Fphi val; have [Lf mod] := cntf phi.
    have phifd: phi \from domain (cost M).
    - by rewrite PF2MF_dom; apply/cost_dom/sfrst_dom; exists Fphi.
    exists (fun q' => make_monotone Lf q' (cost M (exist _ phi phifd) q')).
    move => q' phi' coin Fphi' val'.
    apply/Some_inj.
    have [n eq]:= val q'; have [m eq']:= val' q'; rewrite -eq -eq'.
    rewrite /use_first /PhiN.use_first /=.
    set cst := cost M (exist _ phi phifd) q'.
    have [/=vl min]:= cost_spec (exist _ phi phifd) q'.
    have ->: search (fun k => M phi (k, q')) n = cst.
    - have /leP : cst <= search (fun k => M phi (k, q')) n.
      + by apply/min; have := eq; rewrite /use_first /PhiN.use_first => ->.
      suff /leP: search (fun k => M phi (k, q')) n <= cst by lia.
      exact/search_min.
    suff ->: search (fun k => M phi' (k, q')) m = cst.
    - by have -> //:= (mod _ phi'); apply/coin_subl/coin/mkm_subl.
    have /leP: search (fun k => M phi' (k, q')) m <= cst.
    - by apply/search_min; rewrite -(mod _ phi') //; apply/coin_subl/coin/mkm_subl.
    suff /leP : cst <= search (fun k => M phi' (k, q')) m by lia.
    apply/min; have := eq'.
    rewrite /use_first /PhiN.use_first /= -(mod _ phi') => [-> |] //.
    apply/coin_subl/coin/subs_trans; first exact/mkm_subl.
    have /mnlf_spec mon := @mkm_mon _ _ Lf; apply/mon/search_min => /=.
    by rewrite -(mod _ phi') //; apply/coin_subl/coin/mkm_subl.
  Qed.

  Definition use_first_mod M (mu: B -> nat * Q' -> seq Q) phi nq' :=
    match cost_machine M phi (nq'.1,nq'.2) with
    | Some m => Some (mu phi (m,nq'.2))
    | None => None
    end.

  Lemma sfrst_mod_prp M mu phi Lf:
    Lf \from \F_(use_first_mod M mu) phi
    <->
    exists cf, cf \from \F_(cost_machine M) phi /\ forall q', Lf q' = mu phi (cf q', q').
  Proof.
    split => [val | [cf [val eq]] q']; last first.
    by have [n cstf]:= val q'; exists n; rewrite /use_first_mod cstf /= -eq.
    have [cf costf]: phi \from dom \F_(cost_machine M).
    + apply/FM_dom => q'; have [n ]:= val q'; rewrite /use_first_mod.
      case E: (cost_machine M phi (n, q')) => [n' | ] //.
      by exists n'; exists n. 
    exists cf; split => // q'.
    have [n]:= val q'; rewrite /use_first_mod.
    case E: (cost_machine M phi (n, q')) => [n' | ] // [<-].
    move: E (costf q'); rewrite /cost_machine /use_first /PhiN.use_first/cstb/=.
    case: ifP => // vl [<-] [m]; case: ifP => // vl' [<-].
    do 2 f_equal; rewrite -search_search -[RHS]search_search.
    apply/search_eq; first by rewrite vl.
    by apply/search_min; rewrite vl'.
  Qed.
      
  Lemma sfrst_modf_mod (M: B -> nat * Q' -> option A') mu:
    mu \modulus_function_for M -> monotone_modulus mu ->
    \F_(use_first_mod M mu) \modulus_for \F_(use_first M).
  Proof.
    move => /modf_spec mod /monm_spec mon.
    split => [phi | phi Lf /sfrst_mod_prp [cf [cstf eq]] q'].
    - rewrite -sfrst_dom -cstb_dom => /sfrst_dom [cf costf].
      by exists (fun q' => mu phi (cf q', q')); apply/sfrst_mod_prp; exists cf.
    specialize (mod phi); move: mod; rewrite cmod_F2MF => mod.
    have [n]:= cstf q'; rewrite /cost_machine /use_first /PhiN.use_first /cstb /=.
    case: ifP => //; case E: (M phi _) => [a' | ] // _ [src].
    exists a' => psi coin Fpsi val'.
    have [m eq']:= val' q'; apply/Some_inj; rewrite -E -eq'.
    suff -> : search (fun k => M psi (k, q')) m = search (fun k => M phi (k, q')) n.
    - symmetry; have -> //:= (mod _ psi); first by do 2 f_equal; apply/search_ext => k; case: ifP.
      move: coin; rewrite eq.
      suff ->: cf q' = search (fun k => if isSome (M phi (k, q')) then Some k else None) n.
      + by trivial.
      have /cstm_spec prp := cstf.
      have [vl min]:= prp q'.
      have /leP : search (fun k => if isSome (M phi (k, q')) then Some k else None) n <= cf q'.
      + by apply/search_min; rewrite vl.
      suff /leP: cf q' <= search (fun k => if isSome (M phi (k, q')) then Some k else None) n.
      + by lia.
      by apply/min; rewrite E.
    have ->: search (fun k => M phi (k, q')) n = search (fun k => M phi (k, q')) m.
    - rewrite -search_search -[RHS]search_search; apply/search_eq.
      + suff ->: M phi (search (fun k => M phi (k, q')) n, q') = some a' by trivial.
        by rewrite -E; do 2 f_equal; apply/search_ext => k ineq; case: ifP.
      apply/search_min; rewrite (mod _ psi).
      + have ->:= (@search_cont (fun k => M phi (k, q')) m (fun k => M psi (k, q'))).
        * by rewrite eq'.
        move => k ineq; have -> //:= (mod _ psi).
        apply/coin_subl/coin; rewrite eq.
        apply/mon/leq_trans; first exact/ineq.
        by apply/search_min; rewrite -src E.
      apply/coin_subl/coin.
      rewrite eq; apply/mon.
      by apply/search_min; rewrite -src E.
    apply/search_cont => k ineq.
    symmetry; have ->// := (mod _ psi).
    apply/coin_subl/coin.
    rewrite eq; apply/mon.
    apply/leq_trans; first exact/ineq.
    apply/search_min.
    have <-//:= (mod _ psi); first by rewrite -src E.
    by rewrite -eq.
  Qed.

  Lemma sfrst_mod_dom M mu: mu \modulus_function_for M -> dom \F_(use_first_mod M mu) === dom \F_M.
  Proof.
    move => mod phi.
    split => [[Lf /sfrst_mod_prp [cf [/cstm_spec prp eq]]] | ].
    - apply/FM_dom => q'.
      have [vl min]:= prp q'.
      move: vl; case eq': (M phi (cf q', q')) => [a' | ]// _.
      by exists a'; exists (cf q').
    rewrite -cstb_dom sfrst_dom; case => cf costf.
    by exists (fun q' => mu phi (cf q', q')); apply/sfrst_mod_prp; exists cf.
  Qed.

  Lemma modf_sing_cont (M: B -> nat * Q' -> option A'):
    M \is_continuous_function -> \F_M \is_singlevalued -> \F_M \is_continuous.
  Proof. by move => cntf /sing_sfrst_spec ->; apply/sfrst_cntf_cont. Qed.

  Lemma modf_mod_cont (M: B -> nat * Q' -> option A'):
    M \is_continuous_function -> M \is_monotone -> \F_M \is_continuous.
  Proof. by move => cntf /mon_sing; apply/modf_sing_cont. Qed.

  Lemma sfrst_modmod M mu:
    mu \modulus_function_for mu -> mu \modulus_function_for M -> monotone_modulus mu ->
    \F_(use_first_mod M mu) \modulus_for \F_(use_first_mod M mu).
  Proof.
    move => modmod mod /monm_spec mon; split =>//phi Lf/sfrst_mod_prp [cf [/cstm_spec prp eq]] q'.
    exists (Lf q') => phi' coin _ /sfrst_mod_prp [cf' [/cstm_spec prp' ->]].
    rewrite eq; suff ->: cf' q' = cf q' by symmetry; have ->// := modmod phi _ phi'; rewrite -eq.
    have := (prp' q').2 (cf q'); have ->:= (mod phi' _ phi); last first.
    - by apply/coin_sym; have <-:= modmod phi _ phi'; rewrite -eq.
    move => ineq; have /leP ineq1:= ineq (prp q').1.
    have := (prp q').2 (cf' q'); have ->:= (mod phi _ phi').
    - by move => ineq'; have /leP:= ineq' (prp' q').1; lia.
    apply/coin_subl/coin; rewrite eq.
    exact/mon/leP.
  Qed.

  Lemma gtpf_cntf_cont (M: B -> nat * Q' -> option A'):
    M \is_continuous_function -> (get_pf M) \is_continuous.
  Proof. by rewrite gtpf_spec; apply/sfrst_cntf_cont. Qed.
End cost_bounds.

Local Open Scope name_scope.
Lemma cost_cont Q A Q' A' (M: (Q -> A) -> nat * Q' -> option A'):
  M \is_continuous_function -> (cost M) \is_continuous.
Proof. by move => cntf; rewrite /cost gtpf_spec; apply/sfrst_cntf_cont/cstb_cntf. Qed.

Section continuous_machines.
  Local Open Scope name_scope.
  Context (Q Q': eqType) A A' (M: (Q -> A) -> nat * Q' -> option A').
  Notation B := (Q -> A).

  Lemma FM_sing_val F phi Fphi q' n: M \evaluates F -> F \is_singlevalued -> F phi Fphi ->
                   M phi (n,q') -> M phi (n,q') = Some (Fphi q').
  Proof.
    move => tight sing val.
    case E: (M phi (n,q')) => [a' | ]// _; f_equal.
    have ->:= sing _ _ (fun q => if q == q' then a' else Fphi q) val; first by rewrite eq_refl.
    have phifd: phi \from dom F by exists Fphi.
    have [[Fphi' val'] Fval]:= tight phi phifd.
    apply/Fval.
    move => q.
    case E': (q == q'); first by exists n; move: E' => /eqP ->.
    have [k eq]:= val' q.
    exists k; rewrite eq; f_equal.
    have -> //:= sing _ _ Fphi' val.
    exact/Fval.
  Qed.

Section operator_to_functional.
  Notation B' := (Q' -> A').
  Context (ML: B -> nat *Q' -> option (seq Q)).
  Context (F: B ->> B') (mu: B ->> (Q' -> seq Q)).
  Hypothesis (M_spec: \F_M \tightens F).
  Hypothesis (ML_spec: \F_ML \tightens mu).
  Hypothesis mod: mu \modulus_for F.
  Hypothesis modmod: mu \modulus_for mu.
  Context (dp_N: nat * seq (Q * A) -> option B).
  Hypothesis (dp_spec: \Phi_dp_N \tightens (projection_on (dom F))).
  
  Lemma dp_val phi L: phi \from dom F -> \Phi_dp_N (zip L (map phi L)) \is_subset_of dom F.
  Proof.
    move => phifd psi dpdm.
    have: zip L (map phi L) \from dom (projection_on (dom F)) by exists phi; split; last exact/icf_GL2MF.
    move => /dp_spec [_ prp].
    by have []:= prp psi dpdm.
  Qed.

  Lemma dp_dom phi L: phi \from dom F -> (zip L (map phi L)) \from dom \Phi_dp_N.
  Proof.
    move => phifd; apply dp_spec.
    by exists phi; split; last exact/icf_GL2MF.
  Qed.

  Lemma dp_val_dom phi psi L:
    phi \from dom F -> \Phi_dp_N (zip L (map phi L)) psi -> psi \from dom F.
  Proof.
    move => /dom_po prp dm.
    have /dp_spec [_ prp']:= prp L.
    by apply prp'.
  Qed.
  
  Lemma dp_coin phi psi L: phi \from dom F -> \Phi_dp_N (zip L (map phi L)) psi ->
                       phi \and psi \coincide_on L.
  Proof.
    move => /dom_po prp.
    have /dp_spec [_ prp']:= prp L.
    by move => /prp' [_ /coin_GL2MF coin]; symmetry.
  Qed.
                                             
  Definition trunc T (K: B -> nat * Q' -> option T) phi nq' :=
    let n := nq'.1 in
    let q' := nq'.2 in
    match ML phi ((inverse_pickle ((0,0),0) n).1.1,q') with
    | Some L =>
      match dp_N ((inverse_pickle ((0,0),0) n).2,zip L (map phi L)) with
      | Some psi => K psi ((inverse_pickle ((0,0),0) n).1.2, q')
      | None => None
      end            
    | None => None
    end.

  Lemma mu_cont: mu \is_continuous.
  Proof.
    move => phi Lf md.
    exists Lf => q'.
    apply/crt_icf => //.
    by have := modmod.2 phi Lf md q'.
  Qed.

  Lemma mu_sing: mu \is_singlevalued.
  Proof. exact/cont_sing/mu_cont. Qed.

  Lemma F_cont: F \is_continuous.
  Proof.
    move => phi Fphi val.
    have [ | Lf md]:= mod.1 phi; first by exists Fphi.
    exists Lf => q'.
    apply/crt_icf => //.
    by have := mod.2 phi Lf md q'.
  Qed.

  Lemma F_sing: F \is_singlevalued.
  Proof. exact/cont_sing/F_cont. Qed.

  Lemma trnc_spec: mu \is_singlevalued -> \F_(trunc M) \tightens F.
  Proof.
    move => sing phi phifd.
    have /mod.1 /ML_spec [[Lf md] muval]:= phifd.
    have /M_spec [[Fphi val] Fval]:= phifd.
    split => [ | Fphi' val'].
      suff /full_choice: forall q', exists a', exists n, trunc M phi (n,q') = Some a' by trivial.
      move => q'.
      have [k eq]:= md q'.
      have [m eq']:= val q'.
      have [psi [l eq'']]:= dp_dom (Lf q') phifd.
      have /M_spec [[Fpsi val'] Fval']: psi \from dom F.
      - by apply/dp_val; first exact/phifd; exists l; exact/eq''.
      have [n vl]:= val' q'.
      exists (Fpsi q'); exists (pickle ((k,n),l)).      
      by rewrite /trunc /inverse_pickle pickleK_inv eq eq''/=.
    apply/Fval => q'.
    have [n]:= val' q'.
    rewrite /trunc.
    set k:= (inverse_pickle (0,0,0) n).1.1.
    set l:= (inverse_pickle (0,0,0) n).1.2.
    set m:= (inverse_pickle (0,0,0) n).2.
    case E: (ML phi (k,q')) => [L | ]//.
    case E': (dp_N (m,(zip L (map phi L)))) => [phi' | ]// E''.
    have phi'fd : phi' \from dom F.
    - by apply/dp_val_dom; last by exists m; exact/E'.
    have /M_spec [[Fphi'' val''] Fval'']:= phi'fd.
    have [r eq']:= val q'.
    exists r; rewrite eq'.
    have [l' eq'']:= val'' q'.
    have:= E''.
    have val''': \F_M|_(dom F) phi' Fphi'' by split.
    have -> //:= FM_sing_val _ _ (Fval'' _ val''); last by rewrite E''.
    move => [<-]; f_equal.
    have [a' crt]:= mod.2 phi Lf (muval _ md) q'.
    have ->//:= crt phi' _ Fphi''.
    have ->//:= crt phi (coin_ref _ _ ) Fphi.
    exact/Fval.
    apply/dp_coin => //.
    exists m.
    suff <-: L = Lf q' by apply/E'.
    have [k' mvl]:= md q'.
    have muval': mu phi (fun q => if q == q' then L else Lf q).
    - by apply/muval => q; case eq: (q == q'); [exists k; move: eq => /eqP -> | exact/md].
    by have ->:= sing _ _ _ (muval _ md) muval'; rewrite eq_refl.
    exact/Fval''.
    exact/F_sing.
  Qed.
End operator_to_functional.
  
End continuous_machines.

Section machine_evaluation.
  Local Open Scope name_scope.
  Context (A': Type) (Q Q': eqType) A (default: A). 
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Context (M: B -> nat * Q' -> option A').
  Context (LM: B -> nat * Q' -> seq Q).
  Notation subset T := (mf_set.subset T).
  Context (N: nat * Q -> option A).

  Lemma modmod_spec:
    continuity_modulus (F2MF LM) \extends (F2MF LM)
    <-> 
    forall phi n,
      (fun q' => LM phi (n,q')) \is_modulus_of (F2MF (fun phi q' => LM phi (n,q'))) \on_input phi.
  Proof.
    split => [cont phi n q'| prp phi _ <- [n q']].
    - have [ | L crt]//:= cont phi (LM phi) _ (n,q').
      exists L => psi coin _ <-.
      by apply/crt; first exact/coin.
    have [L crt]:= prp phi n q'.
    exists L => psi coin _ <-.
    exact/(crt psi coin (fun q' => LM psi (n,q'))).
  Qed.

  Hypothesis modmod: (continuity_modulus (F2MF LM)) \extends (F2MF LM).

  Lemma mdmd phi n:
    (fun q' => LM phi (n,q')) \is_modulus_of (F2MF (fun phi q' => LM phi (n,q'))) \on_input phi.
  Proof. by move: phi n; apply/modmod_spec/modmod. Qed.

  Definition KL_step n KL L q':= zip (LM (extend default (N2LF N KL)) (n,q')) L ++ KL.

  Context (phi: B).
  Hypothesis (tot: \Phi_N \is_total).
  Hypothesis icf: phi \is_choice_for (\Phi_N).

  Lemma KL_step_spec KL q' n:
    exists L,
      let K := LM (extend default (N2LF N KL)) (n,q') in
      size L = size K
      /\
      ((L2SS K) \n (dom \Phi_N)) \is_subset_of dom (N2MF N (KL_step n KL L q'))
      /\
      ((extend default (N2LF N KL)) \agrees_with phi \on (dom (N2MF N KL)) ->
       (extend default (N2LF N (KL_step n KL L q'))) \agrees_with phi \on ((L2SS K) \n (dom \Phi_N))).
  Proof.
    rewrite /KL_step.
    elim: (LM (extend default (N2LF N KL)) (n,q')) => [ | q K [L [sze [subs agre]]]].
    - by exists nil; split => //; split => [q [] | agre' q []].
    case: (classic (q \from dom \Phi_N)) => [/icf [k val] | ndm].
    - exists (k :: L); split; first by rewrite /= sze.
      split => [q1 [/= [<- | lstn ex]] | agre' q1 [/= [<- _ | lstn ex]]].
      + by exists (phi q); rewrite N2LFq_cons val; left.
      + have [ | a' prp]//:= subs q1.
        exists a'; move: prp; rewrite N2LF_cons.
        by case: ifP => // /eqP <-; rewrite val; right.          
      + by rewrite /extend N2LFq_cons val.
      by rewrite /extend N2LF_cons; case: ifP => [/eqP <- | _]; [rewrite val | apply/agre].
    exists (0:: L); split; first by rewrite /= sze.
    split => [q1 [/=[<- ex | lstn dm]] | agre' q1 [/=[<- dm | lstn ex]]].
    - by exfalso; apply/ndm/ex.
    - by rewrite /extend N2LF_cons; case: ifP => //.
    - by exfalso; apply/ndm/dm.
    by have [ | a prp]//:= subs q1; exists a; rewrite N2LFq_cons; case: ifP => // /eqP eq.
  Qed.

  Fixpoint KL_rec n s q' := match s with
                            | nil => nil
                            | L :: s' => KL_step n (KL_rec n s' q') L q'
                            end.
  
  Definition phi_rec n s q' := extend default (N2LF N (KL_rec n s q')).

  Lemma phi_rec_spec n q':
    exists s, phi \and (phi_rec n s q') \coincide_on (LM phi (n,q'))
              /\
              L2SS (LM phi (n,q')) \is_subset_of dom (N2MF N (KL_rec n s q')).
  Proof.
    have /full_choice [sf sfprp]:= KL_step_spec _ q' n.    
    pose KL:= fix KL m := match m with
                          | 0 => nil
                          | S m' => KL_step n (KL m') (sf (KL m')) q'
                          end.
    pose phin m:= extend default (N2LF N (KL m)).

    have phin_agre: forall m, (phin m) \agrees_with phi \on (dom (N2MF N (KL m))).
    - elim => [q [] | m ih q dm]//.
     have qfd: q \from dom \Phi_N by apply/exte_dom/dm/N2MF_spec.
     have [sze [_ agre]] := sfprp (KL m).
     case: dm => a.
     rewrite /= /KL_step N2LF_cat => /lstn_app []lstn.
     + apply/(agre ih); split => //; move: lstn.
       elim: (LM _ (n,q')) (sf (KL m)) sze=> [L | qK K ih' [] // a' L [sze] /=].
       * by rewrite zip_nill.
       by rewrite N2LF_cons; case: ifP => [/eqP | _ lstn]; [left | right; apply/ih'/lstn].
      case E: (q \in (LM (phin m) (n,q'))); first by apply/agre; last split; try apply/inP.
      move: E; rewrite /phin /= /KL_step {2}/extend N2LF_cat /=.
      move: (sf (KL m)).
      elim: (LM (extend default (N2LF N (KL m))) (n,q')) => [sfKL _ | a' L ih' sfKL lstn'].
      + by rewrite zip_nill /=; apply/ih; exists a.
        case: (sfKL) => [ | a'' L']; first by rewrite zip_nilr; apply/ih; exists a.
      rewrite /= N2LF_cons.
      move: lstn'; rewrite in_cons => /orP /not_or_and [neq nin].
      case: ifP => [/eqP eq| _]; first by exfalso; apply/neq; rewrite eq.
      by apply/ih'/negP.
     
    have KL_subs: forall m k, m <= k -> (dom (N2MF N (KL m))) \is_subset_of (dom (N2MF N (KL k))).
    - move => m k /subnK <-.
      rewrite -!lstd_spec.
      elim: (k - m) => // l ih.
      rewrite addSn /= lstd_cat => q lstn.
      by apply/lstn_app; right; apply/ih.
      
    have phinm_agre: forall n m, n <= m -> (phin m) \agrees_with phi \on (dom (N2MF N (KL n))).
    - move => m k /subnK <-.
      elim: (k - m) => [ | l ih]; first by rewrite add0n; apply/phin_agre.
      by rewrite addSn; apply/agre_subs/phin_agre/KL_subs; rewrite -addSn; apply/leq_addl.

    have [psi lim]: exists psi, psi \is_limit_of phin.   
    - suff /full_choice [psi psiprp]: forall q, exists a, exists n, forall m, n <= m -> a = phin m q.
      + exists psi; apply/lim_coin; elim => [ | q K [m mprp]]; first by exists 0.
        have [k kprp]:= psiprp q.
        exists (maxn m k) => l; rewrite geq_max => /andP [ineq ineq'].
        by split; [apply/kprp/ineq' | apply/mprp/ineq].
      move => q.        
      case: (classic (exists m, q \from dom (N2MF N (KL m)))) => [[m fd] | ].
      + exists (phin m q); exists m => l ineq.
        rewrite (phinm_agre m) //.
        symmetry.
        exact/phinm_agre/fd.
      move => /not_ex_all_not nex.
      exists default; exists 0 => m _.
      suff : N2LF N (KL m) q = nil by rewrite /phin/=/extend/= => ->.
      case E: (N2LF N (KL m) q) => [ | a L] //.
      exfalso; apply/(nex m).
      by exists a; rewrite /N2MF /= E; left.

    have /cont_F2MF/cont_scnt scnt : LM \is_continuous_function.
    - move => phi'; exists (LM phi') => nq' psi1 coin.
      by symmetry; apply/crt_icf; [ | apply/modmod | exact/coin | ].
      
    have /lim_coin lim': LM psi \is_limit_of (fun m => LM (phin m)) by apply/scnt; first exact/lim.
      
    have eq: LM phi (n,q') = LM psi (n,q').
    - suff coin : psi \and phi \coincide_on (LM psi (n,q')).
      + by apply/crt_icf; [ | apply/modmod | apply/coin | ].
      have [k kprp]:= lim' [:: (n,q')].
      have [ | -> _] //:= kprp k.
      move: lim => /lim_coin lim.
      have [k' k'prp]:= lim (LM (phin k) (n,q')).
      apply/coin_trans; first exact/(k'prp (maxn k.+1 k'))/leq_maxr.      
      apply/coin_agre/agre_subs/phinm_agre/leq_maxl => q lstn.
      by apply sfprp; split; last exact/tot.

    have [k lmt]:= lim' [:: (n,q')].
    pose s := fix s n:= match n with
                        | 0 => nil
                        | S n => sf (KL n) :: s n
                        end.
    have crct: forall k, KL_rec n (s k) q' = KL k.
    - by elim => // k' ih; rewrite /= ih.
    have crct': forall k, phi_rec n (s k) q' = phin k.
    - by case => //k'; rewrite /phi_rec/= crct.
    exists (s k.+1).
    rewrite crct crct' eq.
    have [ | -> _]//:= lmt k.
    suff: L2SS (LM (phin k) (n,q')) \is_subset_of dom (N2MF N (KL k.+1)).
    - by split; first apply/coin_agre/agre_subs/agre_sym/phinm_agre/leqnn.
    apply/subs_trans; last by apply sfprp.
    by move => q lstn; split; last exact/tot.
  Qed.
 
  Definition machine_application nq':=
    let n := nq'.1 in let q' := nq'.2 in
    let ks:= inverse_pickle (0,[::]) n in
    let k := ks.1 in let s := ks.2 in
    let phi := phi_rec k s q' in
    if check_sublist (LM phi (k,q')) (list_dom N (KL_rec k s q'))
    then (M phi (k,q'))
    else None.
    
  Lemma mapp_val n q' a':
    M phi (n,q') = Some a' ->
    certificate (F2MF M) (LM phi (n,q')) phi (n,q') ->
    \Phi_machine_application q' a'.
  Proof.
    move => val crt /=.
    have [s [coin]]:= phi_rec_spec n q'.
    rewrite -lstd_spec => /clP cl.
    exists (pickle (n, s)).
    rewrite /machine_application /inverse_pickle pickleK_inv /=.
    have ->: LM (phi_rec n s q') (n,q') = LM phi (n,q').
    - by apply/crt_icf; [ | apply/modmod | apply/coin | ].
    rewrite cl -val.
    have [a crt'] := crt.
    by apply/crt_icf; [ | exists a; apply/crt' | apply/coin | ].
  Qed.

  Hypothesis mod: (continuity_modulus (F2MF M)) \extends (F2MF LM).

  Lemma mapp_exte Fphi:
    \F_M phi Fphi -> (\Phi_machine_application) \extends (F2MF Fphi).
  Proof.
    move => val q' _ <-.
    have [n val']:= val q'.
    apply/mapp_val; first exact/val'.
    exists (Some (Fphi q')) => psi coin Fpsi <-.
    by rewrite -val'; apply/crt_icf; [ | apply/mod | apply/coin |].
  Qed.

  Lemma mapp_tot: phi \from dom \F_M -> \Phi_machine_application \is_total.
  Proof.
    case => Fphi val q'.
    exists (Fphi q').
    by apply/mapp_exte; first exact/val.
  Qed.
  
  Lemma mapp_sing: \Phi_N \is_singlevalued -> phi \from dom \F_M -> \F_M \is_singlevalued ->
                   \Phi_machine_application \is_singlevalued.
  Proof.
    rewrite /machine_application => sing [Fphi val] Fsing q' a a' [k] /=.
    set n := (inverse_pickle (0, nil) k).1.
    set s := (inverse_pickle (0, nil) k).2.
    case: ifP => // /clP subl eq [k'].
    set n' := (inverse_pickle (0, nil) k').1.
    set s' := (inverse_pickle (0, nil) k').2.
    case: ifP => // /clP subl' eq'.
    pose Fphia q := if q == q' then a else Fphi q.
    pose Fphia' q:= if q == q' then a' else Fphi q.
    suff val' : \F_M phi Fphia.
    - suff val'': \F_M phi Fphia'.
      + have ->: a = Fphia q' by rewrite /Fphia eq_refl.
        have ->: a' = Fphia' q' by rewrite /Fphia' eq_refl.
        by rewrite (Fsing phi _ _ val' val'').
      rewrite /Fphia' => q'1.
      case: ifP => [/eqP -> | _]; last exact/val.
      exists n'.
      suff coin : (phi_rec n' s' q') \and phi \coincide_on (LM (phi_rec n' s' q') (n',q')).
      + by rewrite -eq'; apply/crt_icf; [ | apply/mod | apply/coin | ].
      apply/coin_subl; first exact/subl'.
      apply/coin_agre => q /lstd_spec fd.
      apply/sing; last exact/icf.
      exact/N2MF_spec/extend_spec.
    rewrite /Fphia => q'1.
    case: ifP => [/eqP -> | _]; last exact/val.
    exists n.
    suff coin : (phi_rec n s q') \and phi \coincide_on (LM (phi_rec n s q') (n,q')).
    + by rewrite -eq; apply/crt_icf; [ | apply/mod | apply/coin | ].
    apply/coin_subl; first exact/subl.
    apply/coin_agre => q /lstd_spec fd.
    apply/sing; last exact/icf.
    exact/N2MF_spec/extend_spec.
  Qed.

  Lemma mapp_sing_spec Fphi:
    \Phi_N \is_singlevalued -> \F_M \is_singlevalued ->
    \F_M phi Fphi -> F2MF phi =~= \Phi_N -> F2MF Fphi =~= \Phi_machine_application.
  Proof.
    move => sing Fsing val eq q' a'; split => [ | val' /=]; first exact/mapp_exte.
    apply/mapp_sing/val' => //; first by exists Fphi.
    by apply/mapp_exte; first exact/val.
  Qed.

  Lemma mapp_spec Fphi: \F_M phi Fphi -> forall q', \Phi_machine_application q' (Fphi q').
  Proof. by move => val q'; apply/mapp_exte; first exact/val. Qed.
End machine_evaluation.

Section machine_composition.
  Local Open Scope name_scope.
  Context (A': Type) (Q Q': eqType) A (default: A) (default': A'). 
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Notation subset T := (mf_set.subset T).
  Context (Q'': eqType) A'' (M: B -> nat * Q' -> option A') (M': B' -> nat * Q'' -> option A'').
  Context (LM': B' -> nat * Q'' -> seq Q').
  Hypothesis mod: continuity_modulus (F2MF M') \extends (F2MF LM').
  Hypothesis modmod: continuity_modulus (F2MF LM') \extends (F2MF LM').

  Definition machine_composition phi:= machine_application default' M' LM' (M phi).

  Lemma mcmp_spec: \F_M \is_singlevalued -> machine_composition \evaluates \F_M' \o \F_M.
  Proof.
    rewrite /machine_composition => sing phi [Fphi [[Mphi [val val']] subs]].
    split => [ | Fphi'].
    - exists Fphi.
      apply/mapp_spec/val'/mod; first exact/modmod.
      + by move => q'; exists (Mphi q'); apply/val.
      by move => q' _; apply/val.
    move => /full_choice [bnd bndprp].
    split; last by move => Mphi' val''; exists Fphi; rewrite (sing _ _ _ val'' val).
    exists Mphi.
    split => // q''.
    have := bndprp q''; rewrite /machine_application.
    set n := (inverse_pickle (0, [::]:seq (seq nat)) (bnd q'')).1.
    set s := (inverse_pickle (0, [::]:seq (seq nat)) (bnd q'')).2.
    case: ifP => // /clP subl <- /=.
    exists n.
    apply/crt_icf; [ | exact/mod | | reflexivity]; first by reflexivity.
    apply/coin_agre => q' lstn.
    have/lstd_spec := subl q' lstn.
    rewrite /phi_rec => fd.    
    have vl:= @extend_spec _ _ default' _ q' fd.
    have /=[k eq]:= N2MF_spec vl.
    pose Mphi' q'0 := if q'0 == q'
                      then (extend default'
                                   (N2LF (M phi)
                                         (KL_rec default' LM' (M phi) n s q'')
                                   )
                                   q')
                      else Mphi q'0.
    have val''': \F_M phi Mphi'.
    - move => q'0.
      by rewrite /Mphi'; case: ifP => [/eqP -> | _]; first by exists k.
    have ->:= sing _ _ _ val val'''.    
    by rewrite /Mphi' eq_refl.
  Qed.
End machine_composition.