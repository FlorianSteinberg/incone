(* This file provides an abstract envelope for computability theoretical considerations *)
From mathcomp Require Import all_ssreflect.
From mf Require Import all_mf.
Require Import iseg PhiN.
Require Import FunctionalExtensionality.

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

  Definition monotone M:= make_subset (fun phi => forall q', monotone_in M phi q').
  Notation "M '\is_monotone'" := ((dom \F_M) \is_subset_of (monotone M)) (at level 2).

  Lemma mon_spec (M: B o~> B'): M \is_monotone <-> forall phi q' a' n m,
	phi \from dom \F_M -> n <= m -> M n phi q' = Some a' -> M m phi q' = Some a'.
  Proof.
    split => [mon phi q' a' n m phifd| mon phi phfd q'].
    - have /mon_in_spec prp: monotone_in M phi q' by apply/mon.
      exact/prp.
    by rewrite mon_in_spec => a' n m ineq eq; apply/mon/eq.
  Qed.

  Lemma mon_sing_restr M: \F_M|_(monotone M) \is_singlevalued.
  Proof.
    move => phi Fphi Fphi' [mon FphiFphi] [_ FphiFphi'].
    apply functional_extensionality => q'.
    have [c eq]:= FphiFphi q'.
    have [d eq']:= FphiFphi' q'.
    exact/mon_in_eq/eq'/eq/mon.
  Qed.

  Lemma mon_sing (M: B o~> B):
    M \is_monotone -> \F_M \is_singlevalued.
  Proof. by move => mon; rewrite -(restr_dom \F_M); exact/restr_sing/mon_sing_restr. Qed.
  
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
Notation "M '\is_monotone'" := (dom \F_M \is_subset_of (monotone M)) (at level 2).
Notation "cf '\bounds_cost_of' M" := (cost_bound cf M) (at level 2).

Require Import baire all_cont.
Section evaluation.
  Local Open Scope baire_scope.
  Context (Q' A': Type).
  Context (Q: eqType) A (default: A).
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Context (N: nat -> Q -> option A).
  Context (M: B -> Q' -> A').
  Context (Lf: B -> Q' -> seq Q).

  Lemma cons_subs T t (L: seq T) P:
    L2SS (t :: L) \is_subset_of P <-> t \from P /\ L2SS L \is_subset_of P.
  Proof.
    split => [subs | [Pa subs] q /=[<- | ]]//; last by apply/subs.
    by split => [ | q lstn]; apply/subs; [left | right].
  Qed.

  Fixpoint N2LF_rec LK q:=
    match LK with
    | nil => nil
    | nq:: LK' => if nq.2 == q
                  then match N nq.1 q with
                       | Some a => a :: N2LF_rec LK' q
                       | None => N2LF_rec LK' q
                       end
                  else N2LF_rec LK' q
    end.


  Lemma N2LF_nil L q: N2LF L nil q = nil.
  Proof. by rewrite /N2LF /= subn0 drop_size. Qed.
  
  Definition N2MF n K := LF2MF (N2LF n K).

  Lemma N2MF_nil L: N2MF L [::] =~= mf_empty.
  Proof. by move => q a /=; rewrite N2LF_nil. Qed.
    
  Lemma N2MF_cons L q K: N2MF L (q :: K) \extends N2MF L K.
  Proof.
  Admitted.

  Lemma N2MF_cat L K' K: N2MF L (K' ++ K) \extends N2MF L K.
  Proof.
    by elim: K' => [q | q' K' ih/=]; [rewrite cat0s | apply/exte_trans/N2MF_cons/ih].
  Qed.
  
  Lemma N2MF_exte L K: \Phi_N \extends N2MF L K.
  Proof.
    rewrite /N2MF/N2LF.
    elim: (zip _ _) => [q | [n q] LK ih q' a']//=.
    case: ifP => [/eqP <- | _ lstn]; last exact/ih.
    by case E: (N n q) => [a | ] => /= [[<-| ]|]; [exists n | exact/ih | exact/ih].
  Qed.

  Lemma N2MF_dom L K:
    dom (N2MF L K) \is_subset_of L2SS K.
  Proof.
    elim: K => [q []| q K ih q']; first by rewrite /= N2LF_nil.
  Admitted.
    
  Lemma N2MF_dom_spec K:
    (L2SS K) \is_subset_of dom \Phi_N <-> exists n, (L2SS K) \is_subset_of dom (N2MF n K).
  Proof.
  Admitted.
              
  Lemma size_zip_drop S T (L: seq S) (K: seq T):
    size (zip (drop (size L - size K) L) (drop (size K - size L) K)) = minn (size K) (size L).
  Proof.
    rewrite size_zip !size_drop.
    case /orP: (leq_total (size L) (size K)) => ineq.
    rewrite !minnE.
    have ->: size L - size K = 0 by apply/eqP; rewrite subn_eq0.
    by rewrite !subn0 !(@subKn (size L) (size K)) // subnn subn0.
    rewrite !minnE.
    have ->: size K - size L = 0 by apply/eqP; rewrite subn_eq0.
    by rewrite subn0 !subKn //.
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
  
  Definition extend (phi: Q -> seq A) q:= head default (phi q).

  Lemma extend_spec phi: (extend phi) \is_choice_for (LF2MF phi).
  Proof.
    by rewrite /extend => q a /=; case: (phi q) => //; left.
  Qed.

  Fixpoint K_rec k L q':=
    match k with
    | 0 => nil
    | S k' => Lf (extend (N2LF L (K_rec k' L q'))) q'
    end.

  Lemma K_rec_inc k k' L q': k <= k' -> (K_rec k L q') \is_sublist_of (K_rec k' L q').
  Proof.
  Admitted.

  Lemma K_rec_term k k' L q':
    k <= k' -> K_rec k L q' = K_rec k.+1 L q' -> K_rec k L q' = K_rec k' L q'.
  Proof.
  Admitted.



    Definition phi_rec k L q':=
    let K := K_rec k L q' in
    if allSome (map (N2LF L K) K)
    then Some (extend (N2LF L K))
    else None.

  Lemma phi_recS_inl k L K K' q': phi_rec k L q' = inl K ->  phi_rec k.+1 L q' = inl K'
                                 -> K' = Lf (extend (N2LF L K)) q' ++ K.
  Proof.
    by rewrite /=; case: (phi_rec k L q') => // _ [->]; case: ifP => // _ [<-].
  Qed.

  Lemma phi_rec_inc k k' L K K' q: k <= k' -> phi_rec k L q = inl K -> phi_rec k' L q = inl K' ->
                                   exists K'', K' = K'' ++ K.
  Proof.
    move => /subnK <-.
    elim: (k' - k) K' => [K' | l ih K' eq]; first by rewrite add0n => -> [->]; exists nil.
    move: ih.
    rewrite addSn /=; case E: (phi_rec (l + k) L q) => [pK | ]// ih.
    case: ifP => // _ [] <-; have [ | | K'' -> ]//:= ih pK.
    by exists (Lf (extend (N2LF L (K'' ++ K))) q ++ K''); rewrite catA.
  Qed.

  Lemma phi_rec_dom k k' L phi K q': phi_rec k L q' = inr phi -> phi_rec k' L q' = inl K ->
                                     L2SS K \is_subset_of dom \Phi_N.
  Proof.
    case: (leqVlt k k') => [ /subnK<- eq | ineq eq eq'].
    - suff ->: phi_rec (k' - k + k) L q' = inr phi by trivial.
      by elim: (k' - k) => [ | l ih]; [rewrite add0n | rewrite addSn /= ih].
    move => q lstn /=.
    move: ineq eq => /subnK <-.
    rewrite addnS -addSn.
    elim: (k - k'.+1).+1 => [ | l /=]; first by rewrite add0n eq'.
    case E: (phi_rec (l + k') L q') => [K' | ]// _.
    case: ifP => // /aSoP subs _.
    suff /N2MF_dom_spec subs' : exists n, L2SS K' \is_subset_of dom (N2MF n K').
    have [ | a [m val]]:= subs' q.
    have [ | K'' ->]:= @phi_rec_inc k' (l + k') L _ _ _ _ eq' E; first exact/leq_addl.
    by rewrite L2SS_cat; right.
    by exists a; exists m.
    exists L.
    apply/subs_trans/subs => q'' lstn'.
    by rewrite L2SS_cat; right.
  Qed.
    
  Lemma phi_rec_crct k L phi q' q:
    phi_rec k L q' = inr phi -> q \in Lf phi q' -> \Phi_N q (phi q).
  Proof.
    elim: k => // k /=.
    case: (phi_rec k L q') => // K' _.
    case: ifP => // /aSoP subs [<-] /inP lstn.
    suff val: (N2MF L K' q) (extend (N2LF L K') q) by apply/N2MF_exte/val.
    have [ | a val']:= subs q; first by rewrite L2SS_cat; left.
    exact/extend_spec/val'.
  Qed.
  
  Lemma phi_rec_term q' phi:
    (forall k' L K, phi_rec k' L q' = inl K -> L2SS K \is_subset_of dom \Phi_N) ->
    phi \is_choice_for (\Phi_N) -> certificate (F2MF Lf) (Lf phi q') phi q' ->
    exists k L psi, phi_rec k L q' = inr psi /\ phi \and psi \coincide_on (Lf phi q').
  Proof.
    move => dm icf crt.
    exists (size (Lf phi q')).
    
  Admitted    

    Definition MN n q':=
    let kL:= inverse_pickle (0,[::]) n in
    match phi_rec kL.1 kL.2 q' with
    | inl _ => None
    | inr a => Some (M a q')
    end.
  
  Lemma MphiN_spec phi q':
    certificate (F2MF Lf) (Lf phi q') phi q' (Lf phi q') ->
    certificate (F2MF M) (Lf phi q') phi q' (M phi q') ->
    phi \is_choice_for (\Phi_N) -> \Phi_MN q' (M phi q').
  Proof.
  
  Fixpoint Lf_rec ophi q' k q:=
    match k with
    | 0 => None
    | S k' => match Lf_rec ophi q' k' q with
              | Some a => Some a
              | None => ophi (Lf (extend (Lf_rec ophi q' k')) q') q
              end
    end.
  
  Lemma Lf_rec_spec ophi phi q':
    certificate (F2MF Lf) (Lf phi q') phi q' (Lf phi q') ->
    phi \is_choice_for (PF2MF (ophi (Lf phi q'))) ->
    exists k, Lf (extend (Lf_rec ophi q' k)) q' = Lf phi q'.
  Proof.
    move => crt icf.
    have:= cont_scnt.
    move: {2}(Lf phi q') (eq_refl (Lf phi q')) => L.
    elim: L phi ophi.
    
    
  Lemma PhiN_rec_spec phi q':
    L2SS (Lf phi q') \is_subset_of dom \Phi_N -> phi \is_choice_for (\Phi_N) ->
    certificate (F2MF Lf) (Lf phi q') phi q' (Lf phi q') ->
    exists k, exists n, (extend (PhiN_rec q' k n)) \and phi \coincide_on (Lf phi q').
  Proof.
    ove => /(@PhiN_spec _ phi) prp.
    move: {2}(Lf phi q') (eq_refl (Lf phi q')).
    elim => [/eqP eq subs /=crt | q K ih /eqP -> /cons_subs [dm subs] crt].
    - exists 0 => /=.
      have [ | n /oextendN_spec ]//:= @extendN_tot (Lf (fun _ => default) q').
      - suff ->: (Lf (fun q => default) q') = nil by trivial.
        by rewrite -eq; apply/(@crt (fun _ => default)) => //; rewrite eq.
      case E: (oextendN (Lf (fun _ => default) q')) => [psi | ]// _.
      by exists n; exists psi; rewrite eq.
                
  Admitted.
                
  Definition evaluate_in_Phi n q' :=
    let mk := inverse_pickle (0,0) n in
    match PhiN_rec mk.1 mk.2 q' with
    | None => None
    | Some phi => Some (M phi q')
    end.

  Lemma eval_mod phi q':
    certificate (F2MF M) (Lf phi q') phi q' (M phi q') ->
    forces \Phi_evaluate_in_Phi q' (M phi q').
  Proof.
    move => crt a'.
    rewrite /evaluate_in_Phi => [[n]].
    case E: (PhiN_rec _ _ q') => [psi | ]// [<-].
    apply/(crt psi) => //.
    rewrite /PhiN_rec in E.
    .
  Lemma eval_sing: \Phi_evaluate_in_Phi \is_singlevalued.
  Proof.
    move => phi Mphi Mphi' val val'.

  Lemma eval_icf phi:
    (Lf phi) \is_modulus_of (F2MF M) \on_input phi ->
    (Lf phi) \is_modulus_of (F2MF Lf) \on_input phi ->
    (forall q', L2SS (Lf phi q') \is_subset_of dom \Phi_N)->
     phi \is_choice_for (\Phi_N) -> (M phi) \is_choice_for \Phi_evaluate_in_Phi.
  Proof.
    rewrite /evaluate_in_Phi => /cmod_F2MF mod /cmod_F2MF modmod subs icf q' a' _.
    have [ | k [n [psi [eq coin]]]]:= @PhiN_spec phi  q' icf (subs q').
    - by move => psi coin Fpsi /= <-; symmetry; apply/modmod.
    exists (pickle (k,n)).
    rewrite /inverse_pickle pickleK_inv eq.
    f_equal; symmetry.
    exact/mod/coin_sym.
  Qed.

  Definition phi k n q := 

  Definition ophiN n K :=
    if mapN n K is Some L
    then some (fun q' => if N n q' is Some a' then a' else somea')
    else None.

  Definition 0phi k n q:=
    match k with
    | 0 => somea'
    | S k' => match ophiN n 
  
  Lemma phi Fphi: \F_M phi Fphi ->
                            forall q'', exists n, exists Mphi,
                                oMphi n phi q'' = Some Mphi
                                /\
                                Mphi \and Fphi \coincide_on (mu Mphi q'').
  Proof.
    move => val q''.
    have [n [Mphi [eq coin]]]:= mapM_spec val (mu Fphi q'').
    exists n; exists Mphi.
    split.
    rewrite /oMphi.
    
  Definition monotone_machine_composition n phi q'':=
    match phi' n phi q'' with
    | None => None
    | Some Mphi => match mu n Mphi q'' with
                   | None => None
                   | Some K => let L := mapM n phi K in
                               if has (fun a => ~~ isSome a) L
                               then None
                               else M' n (fun q' => if nth None L (index q' K) is Some a'
                                                    then a'
                                                    else somea') q''
                   end
    end.

  Notation M'_o_M := monotone_machine_composition.

  Lemma mcmp_mon: M \is_monotone -> M' \is_monotone -> (M'_o_M) \is_monotone.
  Proof.
    rewrite/monotone_machine_composition => mon mon' phi phifd q'' n.
    case E: (phi' n phi q'') =>// Mphi.
  Qed.
    
    Lemma mcmp_spec: M \is_monotone -> M' \is_monotone ->
                   \F_(M' \o_M M) \tightens \F_M' \o \F_M.
  Proof.
    move=> /mon_spec mon /mon_spec mon'.

 