(* This file provides an abstract envelope for computability theoretical considerations *)
From mathcomp Require Import all_ssreflect.
From mf Require Import all_mf.
Require Import baire all_cont iseg PhiN seq_cont.
Require Import FunctionalExtensionality ClassicalChoice ChoiceFacts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FM_operator.
  Context (A A' Q Q': Type).
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Notation "B o~> B'" := (nat -> B -> Q' -> option A') (at level 2).
    
  Definition operator (M: B o~> B') :=
    make_mf (fun phi Mphi => forall q', exists c, M c phi q' = Some (Mphi q')).
  
  Notation "\F_ M" := (operator M) (format "'\F_' M", at level 2).

  Lemma Phi_FM (N: nat -> Q' -> option A') phi Fphi:
    (\F_(fun n phi q => N n q)) phi Fphi <-> \Phi_N \extends F2MF Fphi.
  Proof.
    split => [val q' a' <-| exte q']; first by have [n eq]:= val q'; exists n.
    by have [ | n]//:= exte q' (Fphi q'); exists n.
  Qed.
  
  Notation "M '\evaluates_to' F" := ((\F_M) \tightens F) (at level 40).

  Lemma eval_FM M: M \evaluates_to \F_M.
  Proof. done. Qed.

  Lemma exte_sym_F2MF S T (f: S ->> T) g:
    f \is_singlevalued -> f \extends (F2MF g) -> (F2MF g) \extends f.
  Proof. by move => sing exte s t fst; rewrite (sing s t (g s)) => //; apply exte. Qed.

  Lemma eval_F2MF M F:
    M \evaluates_to (F2MF F) <-> \F_M =~= F2MF F.
  Proof.
    split => [eval | <-] //; rewrite exte_equiv; split; first exact/sing_tight_exte/eval/F2MF_sing.
    move => s t fst; apply /(tight_val eval)/fst/F2MF_tot.
  Qed.
  
  Lemma F2MF_mach (F: B -> B'):
    (fun n phi q => Some(F phi q)) \evaluates_to (F2MF F).
  Proof.
    move => phi _; split => [ | Fphi ev]; first by exists (F phi) => q'; exists 0.
    by apply functional_extensionality => q'; have [c val]:= ev q'; apply Some_inj.
  Qed.
  
  Definition cost_bound cf (M: B o~> B') :=
    forall phi q', exists n a', n <= cf phi q' /\ M n phi q' = Some a'.
  
  Definition monotone_in (M: B o~> B') phi q' :=
    forall n, M n phi q' <> None -> M n.+1 phi q' = M n phi q'.
  
  Lemma mon_in_spec (M: B o~> B) phi q': monotone_in M phi q' <->
	  forall a' n m, n <= m -> M n phi q' = Some a' -> M m phi q' = Some a'.
  Proof.
    split => [mon a' n m | mon n neq]; last by case E: (M n phi q') neq=>[a' | ]// _; apply/mon/E. 
    elim: m => [ineq eq | m ih]; first by have/eqP <-: n == 0 by rewrite -leqn0.
    rewrite leq_eqVlt; case/orP => [/eqP <- | ineq eq]//.
    by rewrite mon => //; rewrite ih; rewrite /pickle /=.
  Qed.

  Lemma mon_in_eq M phi q' n m a' b':
    monotone_in M phi q' -> M n phi q' = Some a' -> M m phi q' = Some b' -> a' = b'.
  Proof.
    case/orP: (leq_total n m) => ineq /mon_in_spec mon eq eq'; apply /Some_inj.
      by rewrite -eq'; symmetry; apply/mon/eq.
    by rewrite -eq; apply/mon/eq'.
  Qed.

  Definition monotone M := forall phi q', monotone_in M phi q'.
  Notation "M '\is_monotone'" := (monotone M) (at level 2).

  Lemma mon_spec (M: B o~> B'): M \is_monotone <-> forall phi q' a' n m,
	n <= m -> M n phi q' = Some a' -> M m phi q' = Some a'.
  Proof.
    split => [mon phi q' a' n m phifd| mon phi q'].
    - have /mon_in_spec prp: monotone_in M phi q' by apply/mon.
      exact/prp.
    by rewrite mon_in_spec => a' n m ineq eq; apply/mon/eq.
  Qed.

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
	M \evaluates_to F <-> \F_M \extends F.
  Proof.
    move => mon sing; split => [eval | eval]; first exact/sing_tight_exte.
    exact/exte_tight/eval/mon_sing.
  Qed.

  Definition right_away (M: B o~> B') phi := make_mf (fun q' a' => M 0 phi q' = some a').

  Lemma ra_sing M phi: (right_away M phi) \is_singlevalued.
  Proof. by move => q' a' b' /=eq1 eq2; apply/Some_inj; rewrite -eq1 -eq2. Qed.

  Definition static (M: B o~> B') phi:= make_mf (fun q a => forall c, M c phi q = some a).
End FM_operator.
Notation "\F_ M" := (operator M) (format "'\F_' M", at level 2).
Notation "M '\evaluates_to' F" := (\F_M \tightens F) (at level 2).
Notation "M '\is_monotone'" := (monotone M) (at level 2).
Notation "cf '\bounds_cost_of' M" := (cost_bound cf M) (at level 2).

Section use_first.
  Context (Q A Q' A': Type).
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Context (M: nat -> B -> Q' -> option A').
  
  Definition use_first n phi q:= M (search (fun k => M k phi q) n) phi q.
  
  Lemma sfrst_mon: use_first \is_monotone.
  Proof.
    move => phi q n neq.
    rewrite /use_first.
    f_equal; symmetry.
    rewrite -search_search.
    apply/search_eq .
    move: neq; rewrite /use_first.
    - by case: (M (search (fun k => M k phi q) n) phi q).
    by apply/leq_trans; first exact/search_le.
  Qed.

  Lemma sfrst_sing: \F_use_first \is_singlevalued.
  Proof. exact/mon_sing/sfrst_mon. Qed.

  Lemma sfrst_spec: \F_use_first \tightens \F_M.
  Proof.
    rewrite tight_spec.
    split => [phi [Fphi val] | phi Fphi [phifd val q']]; last first.
    - by have [n eq]:= val q';exists (search (fun k => M k phi q') n).
    rewrite /=.
    suff /choice: forall q', exists a', exists c, use_first c phi q' = Some a' by trivial.
    move => q'; have [n eq]:= val q'.
    have: M (search (fun k => M k phi q') n) phi q'.
    - by apply/(@search_correct (fun k => M k phi q')); rewrite eq.
    by case E: (M (search (fun k => M k phi q') n) phi q') => [b | ] //_; exists b; exists n.
  Qed.

  Lemma sfrst_dom: dom (\F_M) === dom (\F_use_first).
  Proof.
    move => phi.
    split; case => Fphi val; last first.
    - exists Fphi => q'; have [n eq]:= val q'.
      by exists (search (fun k => M k phi q') n).
    suff /choice: forall q', exists a', exists n, use_first n phi q' = Some a' by trivial.
    move => q'; have [n eq]:= val q'; have Mnphiq': M n phi q' by rewrite eq.
    case E: (M (search (fun k => M k phi q') n) phi q') => [a' | ]; first by exists a'; exists n.
    by have:= @search_correct (fun k => M k phi q') n Mnphiq'; rewrite E.
  Qed.

  Lemma mon_sfrst: M \is_monotone <-> forall n phi q, M n phi q = use_first n phi q.
  Proof.
    split => [/mon_spec mon n phi q' | eq phi q' n neq]; last first.
    - rewrite eq sfrst_mon //; have Mnphiq': M n phi q' by case E: (M n phi q') neq.
      case: (@search_correct (fun k => M k phi q') _ Mnphiq').
      by rewrite /use_first; case: (M (search (fun k => M k phi q') n) phi q').    
    rewrite /use_first.
    case E: (M (search (fun k => M k phi q') n) phi q') => [a | ].
    - apply/mon; last exact/E.
      exact/search_le.
    have := @search_le (fun k => M k phi q') n.
    rewrite leq_eqVlt => /orP [/eqP <- | /searchP [m [Nmq mln]]] //.
    have:= @search_correct (fun k => M k phi q') _ Nmq.
    have ->:= @search_eq (fun k => M k phi q') m n Nmq; first by rewrite E.
    by case: (m) mln => // m' m'ln; apply/leq_trans/m'ln.
  Qed.
    
  Lemma sing_sfrst: \F_M \is_singlevalued <-> \F_M =~= \F_(use_first).
  Proof.
    split => [sing phi Fphi| ->]; last exact/sfrst_sing.
    split => val q'; last by have [n eq]:= val q'; exists (search (fun k => M k phi q') n).
    have [n eq]:= val q'; exists n; rewrite /use_first.
    have Nnq: M n phi q' by rewrite eq.
    have := (@search_correct (fun k => M k phi q') n Nnq).
    case E: (M _ phi q') => [b | ] // _.
    f_equal.
    have/choice [Fphi' Fphi'prp]: forall q, exists a',
          (q = q' /\ a' = b) \/ (q <> q' /\ a' = Fphi q).
    - by move => q; case: (classic (q = q')); [exists b; left | exists (Fphi q); right].
    rewrite (sing phi Fphi Fphi') //.
    by case: (Fphi'prp q'); case.
    move => q.
    case: (classic (q = q')) => [eq' | neq].
    exists (search (fun k => M k phi q') n).
    by rewrite eq' E; f_equal; case: (Fphi'prp q); case => // ->.
    have [m eq']:= val q.
    exists m.
    by case: (Fphi'prp q); case => // _ ->.
  Qed.
End use_first.      

Require Import Psatz.
Lemma search_cont p n p':
  (forall k, k <= search p n -> p k = p' k) -> search p n = search p' n.
Proof.
  elim: n => [ | n ih prp] //.
  have eq: search p n = search p' n.
  - by apply/ih => k ineq; apply/prp/leq_trans/search_inc/leqW/leqnn.
  rewrite !searchS ih; last by move => k ineq; apply/prp/leq_trans/search_inc/leqW/leqnn.
  case: ifP => // /eqP eq'.
  rewrite prp // -{1}eq' -eq.
  exact/search_inc.
Qed.

Section continuous_machines.
  Local Open Scope baire_scope.
  Definition modulus_for Q A Q' A' (F: (Q -> A) ->> (Q' -> A')) (mu: (Q -> A) ->> (Q' -> seq Q)):=
    dom F \is_subset_of dom mu /\ continuity_modulus F \extends mu.
  Notation "mu \is_modulus_for F" := (modulus_for F mu) (at level 2).
  Context (Q Q': eqType) A A' (M: nat -> (Q -> A) -> Q' -> option A').
  Notation B := (Q -> A).
  Lemma FM_sing_val F phi Fphi q' n: M \evaluates_to F -> F \is_singlevalued -> F phi Fphi ->
                   M n phi q' -> M n phi q' = Some (Fphi q').
  Proof.
    move => tight sing val.
    case E: (M n phi q') => [a' | ]// _; f_equal.
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

 Section functional_to_operator.
  Context (mu: B -> Q'*nat -> seq Q).
  Hypothesis mod: (F2MF mu) \is_modulus_for (F2MF (fun phi q'n => M q'n.2 phi q'n.1)).
  
  Fixpoint mu' n phi q' :=
    match n with
    | 0 => mu phi (q',0)
    | n'.+1 => mu' n' phi q' ++ mu phi (q',n)
    end.

  Lemma mu'_spec n phi m:
    m <= n -> (mu' n phi) \is_modulus_of (F2MF (M m)) \on_input phi.
  Proof.
    elim: n => [ | n ih].
    - rewrite leqn0 => /eqP -> q'.
      exists (M 0 phi q') => psi coin Fpsi <-.
      have [ | oa' crt]//:= @mod.2 phi (mu phi) _ (q',0).
      have -> //:= crt psi coin (fun q'n => M q'n.2 psi q'n.1).
      by have ->//:= crt phi (coin_ref _ _) (fun q'n => M q'n.2 phi q'n.1).
    rewrite leq_eqVlt => /orP [/eqP -> q' | ineq q'].
    - exists (M n.+1 phi q') => psi.
      rewrite /= => /coin_cat [_ coin] _ <-.
      have [ | oa' crt]//:= @mod.2 phi (mu phi) _ (q',n.+1).      
      have ->//:= crt psi coin (fun q'n => M q'n.2 psi q'n.1).
      by have ->:= crt phi (coin_ref _ _) (fun q'n => M q'n.2 phi q'n.1).
    exists (M m phi q') => psi. 
    rewrite /= => /coin_cat [coin _] _ <-.
    have [ | oa crt]//:= ih _ q'.
    have -> //:= crt psi coin (M m psi).
    by have -> := crt phi (coin_ref _ _) (M m phi).
  Qed.

  Definition use_first_mod n phi q' :=
    match use_first M n phi q' with
    | None => None
    | Some a => Some (mu' (search (fun k => M k phi q') n) phi q')
    end.
  
  Lemma ufmod_spec: \F_(use_first_mod) \is_modulus_for \F_(use_first M).
  Proof.
    split => [phi [Fphi val] | phi Fphi mod' q'].
    - suff /choice: forall q', exists a' n, use_first_mod n phi q' = Some a' by trivial.
      move => q'; have [n eq]:= val q'.
      rewrite /use_first_mod.
      exists (mu' (search (fun k => M k phi q') n) phi q'); exists n.
      by rewrite eq.
    have [n]:= mod' q'.
    rewrite /use_first_mod.
    case E: (use_first M n phi q') => [a' | ]// [<-].
    exists a'=> psi coin Fpsi val.
    apply/Some_inj; rewrite -E; symmetry.
    have [k val']:= val q'; rewrite -val'.
    have [oa' crt]:= mu'_spec phi (leqnn (search (fun k => M k phi q') n)) q'.
    rewrite /use_first.
    have eq:search (fun k => M k phi q') n = search (fun k => M k psi q') n.
    - apply/search_cont => l ineq.
      have [ob' crt']:= mu'_spec phi ineq q'.
      have ->//:= crt' psi coin (M l psi).
      by have ->:= crt' phi (coin_ref _ _) (M l phi).
    have <-: search (fun k => M k psi q') n = search (fun k => M k psi q') k.
    - rewrite -search_search.
      have -> := (@search_eq (fun k => M k psi q'))
                 (search (fun k => M k psi q') n)
                 (search (fun k => M k psi q') k); last first.
      + by apply/search_min; move: val'; rewrite /use_first => ->.
      + rewrite -eq.
        have /=->//:= crt psi coin (M (search (fun k => M k phi q') n) psi).
        have /=<-//:= crt phi (coin_ref _ _) (M (search (fun k => M k phi q') n) phi).
        by move: E; rewrite /use_first => ->.
      by rewrite search_search.
    have -> //:= crt phi (coin_ref _ _) (M (search ( fun k => M k phi q') n) phi).
    by rewrite -eq; have -> //:= crt psi coin (M (search ( fun k => M k phi q') n) psi).
  Qed.

  Lemma ufmod_domM:
    dom \F_(use_first_mod) === dom \F_M.
  Proof.
    move => phi; split => [[Lf val] | /sfrst_dom [Fphi val]].
    - suff /choice: forall q', exists a' n, M n phi q' = some a' by trivial.
      move => q'.
      have [n ]:= val q'.
      rewrite /use_first_mod /use_first.
      case E: (M (search _ n) phi q') => [a' | ]//; exists a'.
      by exists (search (fun k => M k phi q') n).
    suff /choice: forall q', exists L n, use_first_mod n phi q' = some L by trivial.
    move => q'.
    have [n eq]:= val q'.
    exists (mu' (search (fun k => M k phi q') n) phi q'); exists n.
    by rewrite /use_first_mod eq.
  Qed.

  Lemma ufmod_dom:
    dom \F_(use_first_mod) === dom \F_(use_first M).
  Proof.
    rewrite -sfrst_dom.
    exact/ufmod_domM.
  Qed.

  Lemma sfrst_cont: \F_(use_first M) \is_continuous.
  Proof.
    move => phi Fphi' val'.
    have [ | Lf val]:= (ufmod_dom phi).2; first by exists Fphi'.
    exists Lf => q'.
    apply/crt_icf => //.
    have [a' crt]:= ufmod_spec.2 phi Lf val q'.
    exists a' => psi coin Fpsi FpsiFpsi.
    by apply/crt; first exact/coin.
  Qed.

  Lemma mu'mod_mod: (F2MF mu) \is_modulus_for (F2MF mu) ->
        forall n phi, mu' n phi \is_modulus_of (F2MF (mu' n)) \on_input phi.
  Proof.
    move => modmod n phi q'.
    elim: n => [ | n [L crt]].
    - have [ | L crt]//:= modmod.2 phi (mu phi) _ (q', 0).
      exists L; rewrite /mu' /= => psi coin Fpsi <-.
      apply/crt; first exact/coin.
      by split => //; apply/F2MF_dom.
    exists (L ++ mu phi (q',n.+1)) => psi.
    rewrite /= => /coin_cat [coin coin'] Fpsi <-.
    rewrite /=; f_equal; first by apply/crt; first exact/coin.
    have [ | L' crt']//:= modmod.2 phi (mu phi) _ (q', n.+1).
    have -> //:= crt' psi coin' (mu psi).
    by have ->:= crt' phi (coin_ref _ _) (mu phi).
  Qed.

  Lemma ufmod_mod: (F2MF mu) \is_modulus_for (F2MF mu) ->
                   \F_(use_first_mod) \is_modulus_for \F_(use_first_mod).
  Proof.
    move =>/mu'mod_mod modmod; split => // phi Lf val q'. 
    exists (Lf q').
    have [n]:= val q'.
    rewrite {1}/use_first_mod.
    case E: (use_first M n phi q') => [a' | ] // [<-].
    move => psi coin Fpsi val'.
    have [b' crt]:= modmod (search (fun k => M k phi q') n) phi q'.
    have ->//:= crt phi (coin_ref _ _) (mu' (search (fun k => M k phi q') n) phi).
    apply/Some_inj.
    have [k eq]:= val' q'.
    rewrite -eq; move: eq.
    rewrite /use_first_mod.
    case E': (use_first M k psi q') => [c' | ] //.
    have -> //:= crt psi coin (mu' (search (fun k => M k psi q') k) psi).
    simpl; f_equal.
    have prp : forall l, l <= search (fun m => M m phi q') n -> M l phi q' = M l psi q'.
    - move => l ineq.
      have [d' crt']:= mu'_spec phi ineq q'.
      have ->//:= crt' phi (coin_ref _ _).
      by  have -> //:= crt' psi coin.
    have eq: search (fun k => M k phi q') n = search (fun k => M k psi q') n.
    - by apply/search_cont => l ineq; rewrite prp.
    rewrite eq.
    suff ->: search (fun k => M k psi q') n = search (fun k => M k psi q') k by trivial.
    rewrite -search_search -[RHS]search_search.
    apply/search_eq.
    - rewrite -eq.
      have [d' crt']:= mu'_spec phi (leqnn (search (fun k => M k phi q') n)) q'.
      have -> //:= crt' psi _ (M _ psi).
      have <- //:= crt' phi (coin_ref _ _) (M (search (fun k => M k phi q') n) phi).
      by move: E; rewrite /use_first => ->.
    apply/search_min.
    by move : E'; rewrite /use_first => ->.
  Qed.
End functional_to_operator.

Section operator_to_functional.
  Notation B' := (Q' -> A').
  Context (ML: nat -> B -> Q' -> option (seq Q)).
  Context (F: B ->> B') (mu: B ->> (Q' -> seq Q)).
  Hypothesis (M_spec: \F_M \tightens F).
  Hypothesis (ML_spec: \F_ML \tightens mu).
  Hypothesis mod: mu \is_modulus_for F.
  Hypothesis modmod: mu \is_modulus_for mu.

  Definition domain_projection:=
    make_mf (fun L phi => phi \from dom F /\ phi \is_choice_for (L2MF L)).
  Context (dp_N: nat -> seq (Q * A) -> option B).
  Hypothesis (dp_spec: \Phi_dp_N \tightens domain_projection).

  Lemma icf_L2MF (phi: B) L: phi \is_choice_for (L2MF (zip L (map phi L))).
  Proof.
    elim: L => [q [] | q L ih q' [a /=[[<-] | lstn]]] //=; first by left.
    by right; apply/ih; exists a.
  Qed.

  Lemma coin_L2MF (phi psi: B) L:
    phi \and psi \coincide_on L <-> phi \is_choice_for (L2MF (zip L (map psi L))).
  Proof.
  Admitted.

  Lemma dom_dp phi L: phi \from dom F -> zip L (map phi L) \from dom domain_projection.
  Proof. by move => phifd; exists phi; split; last exact/icf_L2MF.  Qed.
  
  Lemma dp_val phi L: phi \from dom F -> \Phi_dp_N (zip L (map phi L)) \is_subset_of dom F.
  Proof.
    move => phifd psi dpdm.
    have: zip L (map phi L) \from dom domain_projection by exists phi; split; last exact/icf_L2MF.
    move => /dp_spec [_ prp].
    by have []:= prp psi dpdm.
  Qed.

  Lemma dp_dom phi L: phi \from dom F -> (zip L (map phi L)) \from dom \Phi_dp_N.
  Proof.
    move => phifd; apply dp_spec.
    by exists phi; split; last exact/icf_L2MF.
  Qed.

  Lemma dp_val_dom phi psi L:
    phi \from dom F -> \Phi_dp_N (zip L (map phi L)) psi -> psi \from dom F.
  Proof.
    move => /dom_dp prp dm.
    have /dp_spec [_ prp']:= prp L.
    by apply prp'.
  Qed.
  
  Lemma dp_coin phi psi L: phi \from dom F -> \Phi_dp_N (zip L (map phi L)) psi ->
                       phi \and psi \coincide_on L.
  Proof.
    move => /dom_dp prp.
    have /dp_spec [_ prp']:= prp L.
    by move => /prp' [_ /coin_L2MF coin]; symmetry.
  Qed.
                                             
  Definition trunc T (K: nat -> B -> Q' -> option T) n phi q' :=
    match ML (inverse_pickle ((0,0),0) n).1.1 phi q' with
    | Some L =>
      match (dp_N (inverse_pickle ((0,0),0) n).2 (zip L (map phi L))) with
      | Some psi => K (inverse_pickle ((0,0),0) n).1.2 psi q'
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
      suff /choice: forall q', exists a', exists n, trunc M n phi q' = Some a' by trivial.
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
    case E: (ML k phi q') => [L | ]//.
    case E': (dp_N m (zip L (map phi L))) => [phi' | ]// E''.
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
  Local Open Scope baire_scope.
  Context (A': Type) (Q Q': eqType) A (default: A). 
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Context (M: nat -> B -> Q' -> option A').
  Context (LM: nat -> B -> Q' -> seq Q).
  Notation subset T := (mf_set.subset T).
  Context (N: nat -> Q -> option A).
  
  Hypothesis modmod: forall n phi, (LM n phi) \is_modulus_of (F2MF (LM n)) \on_input phi.

  Definition KL_step n KL L q':= zip (LM n (extend default (N2LF N KL)) q') L ++ KL.

  Context (phi: B).
  Hypothesis (tot: \Phi_N \is_total).
  Hypothesis icf: phi \is_choice_for (\Phi_N).

  Lemma KL_step_spec KL q' n:
    exists L,
      let K := LM n (extend default (N2LF N KL)) q' in
      size L = size K
      /\
      ((L2SS K) \n (dom \Phi_N)) \is_subset_of dom (N2MF N (KL_step n KL L q'))
      /\
      ((extend default (N2LF N KL)) \agrees_with phi \on (dom (N2MF N KL)) ->
       (extend default (N2LF N (KL_step n KL L q'))) \agrees_with phi \on ((L2SS K) \n (dom \Phi_N))).
  Proof.
    rewrite /KL_step.
    elim: (LM n (extend default (N2LF N KL)) q') => [ | q K [L [sze [subs agre]]]].
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
    exists s, phi \and (phi_rec n s q') \coincide_on (LM n phi q')
              /\
              L2SS (LM n phi q') \is_subset_of dom (N2MF N (KL_rec n s q')).
  Proof.
    have /choice [sf sfprp]:= KL_step_spec _ q' n.    
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
       elim: (LM n _ q') (sf (KL m)) sze=> [L | qK K ih' [] // a' L [sze] /=].
       * by rewrite zip_nill.
       by rewrite N2LF_cons; case: ifP => [/eqP | _ lstn]; [left | right; apply/ih'/lstn].
      case E: (q \in (LM n (phin m) q')); first by apply/agre; last split; try apply/inP.
      move: E; rewrite /phin /= /KL_step {2}/extend N2LF_cat /=.
      move: (sf (KL m)).
      elim: (LM n (extend default (N2LF N (KL m))) q') => [sfKL _ | a' L ih' sfKL lstn'].
      + by rewrite zip_nill /=; apply/ih; exists a.
        case: (sfKL) => [ | a'' L']; first by rewrite zip_nilr; apply/ih; exists a.
      rewrite /= N2LF_cons.
      move: lstn'; rewrite in_cons => /orP /not_or_and [neq nin].
      case: ifP => [/eqP eq| _]; first by exfalso; apply/neq; rewrite eq.
      by apply/ih'/negP.
     
    have KL_subs: forall m k, m <= k -> (dom (N2MF N (KL m))) \is_subset_of (dom (N2MF N (KL k))).
    - move => m k /subnK <-.
      rewrite -!lstd_spec -L2SS_subs.
      elim: (k - m) => // l ih.
      rewrite addSn /= lstd_cat => q lstn.
      by apply/lstn_app; right; apply/ih.
      
    have phinm_agre: forall n m, n <= m -> (phin m) \agrees_with phi \on (dom (N2MF N (KL n))).
    - move => m k /subnK <-.
      elim: (k - m) => [ | l ih]; first by rewrite add0n; apply/phin_agre.
      by rewrite addSn; apply/agre_subs/phin_agre/KL_subs; rewrite -addSn; apply/leq_addl.

    have [psi lim]: exists psi, psi \is_limit_of phin.   
    - suff /choice [psi psiprp]: forall q, exists a, exists n, forall m, n <= m -> a = phin m q.
      + exists psi; elim => [ | q K [m mprp]]; first by exists 0.
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

    have /cont_F2MF/cont_scnt scnt : (LM n) \is_continuous_function.
    - move => phi'; exists (LM n phi') => q'1 psi1 coin.
      by symmetry; apply/crt_icf; [ | apply/modmod/n | apply/coin | ].

    have lim': LM n psi \is_limit_of (fun m => LM n (phin m)) by apply/scnt; [apply/lim | | ].

    have eq: LM n phi q' = LM n psi q'.
    - suff coin : psi \and phi \coincide_on (LM n psi q').
      + by apply/crt_icf; [ | apply/modmod/n | apply/coin | ].
      have [k kprp]:= lim' [:: q'].
      have [ | -> _] //:= kprp k.
      have [k' k'prp]:= lim (LM n (phin k) q').
      apply/coin_trans; first exact/(k'prp (maxn k.+1 k'))/leq_maxr.      
      apply/coin_agre/agre_subs/phinm_agre/leq_maxl => q lstn.
      by apply sfprp.

    have [k lmt]:= lim' [:: q'].
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
    have [ | -> _]//:= lmt k;split; last by apply/subs_trans; last by apply sfprp.
    apply/coin_agre/agre_subs/agre_sym/phinm_agre/leqnn.
    by apply/subs_trans; last by apply sfprp.
  Qed.
 
  Definition machine_application n q':=
    let ns:= inverse_pickle (0,[::]) n in
    let n := ns.1 in let s := ns.2 in
    let phi := phi_rec ns.1 ns.2 q' in
    if check_sublist (LM n phi q') (list_dom N (KL_rec n s q'))
    then (M n phi q')
    else None.
    
  Lemma mapp_val n q' a':
    M n phi q' = Some a' ->
    certificate (F2MF (M n)) (LM n phi q') phi q' ->
    \Phi_machine_application q' a'.
  Proof.
    move => val crt /=.
    have [s [coin]]:= phi_rec_spec n q'.
    rewrite -lstd_spec -L2SS_subs => /clP cl.
    exists (pickle (n, s)).
    rewrite /machine_application /inverse_pickle pickleK_inv /=.
    have ->: LM n (phi_rec n s q') q' = LM n phi q'.
    - by apply/crt_icf; [ | apply/modmod | apply/coin | ].
    rewrite cl -val.
    have [a crt'] := crt.
    by apply/crt_icf; [ | exists a; apply/crt' | apply/coin | ].
  Qed.

  Hypothesis mod: forall n phi, (LM n phi) \is_modulus_of (F2MF (M n)) \on_input phi.

  Lemma mapp_exte Fphi:
    \F_M phi Fphi ->
    (\Phi_machine_application) \extends (F2MF Fphi).
  Proof.
    move => val q' _ <-.
    have [n val']:= val q'.
    apply/mapp_val; first exact/val'.
    exists (Some (Fphi q')) => psi coin Fpsi <-.
    by rewrite -val'; apply/crt_icf; [ | apply/mod/n | apply/coin |].
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
      suff coin : (phi_rec n' s' q') \and phi \coincide_on (LM n' (phi_rec n' s' q') q').
      + by rewrite -eq'; apply/crt_icf; [ | apply/mod/n' | apply/coin | ].
      apply/coin_subl; first exact/subl'.
      apply/coin_agre => q /lstd_spec fd.
      apply/sing; last exact/icf.
      exact/N2MF_spec/extend_spec.
    rewrite /Fphia => q'1.
    case: ifP => [/eqP -> | _]; last exact/val.
    exists n.
    suff coin : (phi_rec n s q') \and phi \coincide_on (LM n (phi_rec n s q') q').
    + by rewrite -eq; apply/crt_icf; [ | apply/mod/n | apply/coin | ].
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

  (*
  Lemma mapp_spec' Fphi: (\Phi_machine_application) \extends (F2MF Fphi) <-> \F_M phi Fphi.
  Proof.
    split => [icf' q' | val q' _ <-]; last exact/mapp_exte.
    have [ | n eq]//:= icf' q' (Fphi q').
    move: eq; rewrite /machine_application; case: ifP => // /clP.
    set ms:= inverse_pickle (0,nil: seq_countType (seq_countType nat_countType)) n.
    set m := ms.1; set s := ms.2 => subl val.
    exists m; rewrite -val.
    apply/crt_icf; [ | apply/mod/ms.1 | | rewrite /=; reflexivity].
    - by rewrite /=; reflexivity.      
    
      apply/coin_agre => q lstn.
      
  Admitted.
*)
End machine_evaluation.

Section machine_composition.
  Local Open Scope baire_scope.
  Context (A': Type) (Q Q': eqType) A (default: A) (default': A'). 
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Notation subset T := (mf_set.subset T).
  Context (Q'': eqType) A'' (M: nat -> B -> Q' -> option A') (M': nat -> B' -> Q'' -> option A'').
  Context (LM': nat -> B' -> Q'' -> seq Q').
  Hypothesis mod: forall n phi, LM' n phi \is_modulus_of (F2MF (M' n)) \on_input phi.
  Hypothesis modmod: forall n phi, LM' n phi \is_modulus_of (F2MF (LM' n)) \on_input phi.

  Definition machine_composition k phi q:=
    machine_application default' M' LM' (fun k q' => M k phi q') k q.

  Lemma mcmp_spec: \F_M \is_singlevalued -> machine_composition \evaluates_to \F_M' \o \F_M.
  Proof.
    rewrite /machine_composition => sing phi [Fphi [[Mphi [val val']] subs]].
    split => [ | Fphi'].
    - exists Fphi.
      apply/mapp_spec/val'/mod; first exact/modmod.
      + by move => q'; exists (Mphi q'); apply/val.
      by move => q' _; apply/val.
    move => /choice [bnd bndprp].
    split; last by move => Mphi' val''; exists Fphi; rewrite (sing _ _ _ val'' val).
    exists Mphi.
    split => // q''.
    have := bndprp q''; rewrite /machine_application.
    set n := (inverse_pickle (0, [::]:seq (seq nat)) (bnd q'')).1.
    set s := (inverse_pickle (0, [::]:seq (seq nat)) (bnd q'')).2.
    case: ifP => // /clP subl <-.
    exists n.
    have [oa'' crt]:= mod n (phi_rec default' LM' (fun k => [eta M k phi]) n s q'') q''.
    symmetry; have ->// := crt _ (coin_ref _ _).
    symmetry; apply/crt; last by f_equal.
    apply/coin_lstn => q' lstn.
    have/lstd_spec := subl q' lstn.
    rewrite /phi_rec => fd.    
    have vl:= @extend_spec _ _ default' _ q' fd.
    have /=[k eq]:= N2MF_spec vl.
    pose Mphi' q'0 := if q'0 == q'
                      then (extend default'
                                   (N2LF (fun k => [eta M k phi])
                                         (KL_rec default' LM' (fun k => [eta M k phi]) n s q'')
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