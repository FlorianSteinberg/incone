(* This file provides an abstract envelope for computability theoretical considerations *)
From mathcomp Require Import all_ssreflect.
From mf Require Import all_mf.
Require Import all_cont search PhiN multivalued_application FMop seq_cont.
Require Import axioms Classical Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section continuous_machines.
  Local Open Scope name_scope.
  Context (Q Q': eqType) A A' (M: (Q -> A) -> nat * Q' -> option A').
  Notation B := (Q -> A).

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
                       phi \coincides_with psi \on L.
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

  Definition KL_step n KL L q':= zip (LM (LF2F default (N2LF N KL)) (n,q')) L ++ KL.

  Context (phi: B).
  Hypothesis (tot: \Phi_N \is_total).
  Hypothesis icf: phi \is_choice_for (\Phi_N).

  Lemma KL_step_spec KL q' n:
    exists L,
      let K := LM (LF2F default (N2LF N KL)) (n,q') in
      size L = size K
      /\
      ((L2SS K) \n (dom \Phi_N)) \is_subset_of dom (N2MF N (KL_step n KL L q'))
      /\
      ((LF2F default (N2LF N KL)) \agrees_with phi \on (dom (N2MF N KL)) ->
       (LF2F default (N2LF N (KL_step n KL L q'))) \agrees_with phi \on ((L2SS K) \n (dom \Phi_N))).
  Proof.
    rewrite /KL_step.
    elim: (LM (LF2F default (N2LF N KL)) (n,q')) => [ | q K [L [sze [subs agre]]]].
    - by exists nil; split => //; split => [q [] | agre' q []].
    case: (classic (q \from dom \Phi_N)) => [/icf [k val] | ndm].
    - exists (k :: L); split; first by rewrite /= sze.
      split => [q1 [/= [<- | lstn ex]] | agre' q1 [/= [<- _ | lstn ex]]].
      + by exists (phi q); rewrite N2LFq_cons val; left.
      + have [ | a' prp]//:= subs q1.
        exists a'; move: prp; rewrite N2LF_cons.
        by case: ifP => // /eqP <-; rewrite val; right.          
      + by rewrite /LF2F N2LFq_cons val.
      by rewrite /LF2F N2LF_cons; case: ifP => [/eqP <- | _]; [rewrite val | apply/agre].
    exists (0:: L); split; first by rewrite /= sze.
    split => [q1 [/=[<- ex | lstn dm]] | agre' q1 [/=[<- dm | lstn ex]]].
    - by exfalso; apply/ndm/ex.
    - by rewrite /LF2F N2LF_cons; case: ifP => //.
    - by exfalso; apply/ndm/dm.
    by have [ | a prp]//:= subs q1; exists a; rewrite N2LFq_cons; case: ifP => // /eqP eq.
  Qed.

  Fixpoint KL_rec n s q' := match s with
                            | nil => nil
                            | L :: s' => KL_step n (KL_rec n s' q') L q'
                            end.
  
  Definition phi_rec n s q' := LF2F default (N2LF N (KL_rec n s q')).

  Lemma phi_rec_spec n q':
    exists s, phi \coincides_with (phi_rec n s q') \on (LM phi (n,q'))
              /\
              L2SS (LM phi (n,q')) \is_subset_of dom (N2MF N (KL_rec n s q')).
  Proof.
    have /full_choice [sf sfprp]:= KL_step_spec _ q' n.    
    pose KL:= fix KL m := match m with
                          | 0 => nil
                          | S m' => KL_step n (KL m') (sf (KL m')) q'
                          end.
    pose phin m:= LF2F default (N2LF N (KL m)).

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
      move: E; rewrite /phin /= /KL_step {2}/LF2F N2LF_cat /=.
      move: (sf (KL m)).
      elim: (LM (LF2F default (N2LF N (KL m))) (n,q')) => [sfKL _ | a' L ih' sfKL lstn'].
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
      suff : N2LF N (KL m) q = nil by rewrite /phin/=/LF2F/= => ->.
      case E: (N2LF N (KL m) q) => [ | a L] //.
      exfalso; apply/(nex m).
      by exists a; rewrite /N2MF /= E; left.

    have /cont_F2MF/cont_scnt scnt : LM \is_continuous_function.
    - move => phi'; exists (LM phi') => nq' psi1 coin.
      by symmetry; apply/crt_icf; [ | apply/modmod | exact/coin | ].
      
    have /lim_coin lim': LM psi \is_limit_of (fun m => LM (phin m)) by apply/scnt; first exact/lim.
      
    have eq: LM phi (n,q') = LM psi (n,q').
    - suff coin : psi \coincides_with phi \on (LM psi (n,q')).
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
      suff coin : (phi_rec n' s' q') \coincides_with phi \on (LM (phi_rec n' s' q') (n',q')).
      + by rewrite -eq'; apply/crt_icf; [ | apply/mod | apply/coin | ].
      apply/coin_subl; first exact/subl'.
      apply/coin_agre => q /lstd_spec fd.
      apply/sing; last exact/icf.
      exact/N2MF_spec/LF2F_spec.
    rewrite /Fphia => q'1.
    case: ifP => [/eqP -> | _]; last exact/val.
    exists n.
    suff coin : (phi_rec n s q') \coincides_with phi \on (LM (phi_rec n s q') (n,q')).
    + by rewrite -eq; apply/crt_icf; [ | apply/mod | apply/coin | ].
    apply/coin_subl; first exact/subl.
    apply/coin_agre => q /lstd_spec fd.
    apply/sing; last exact/icf.
    exact/N2MF_spec/LF2F_spec.
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
    have vl:= @LF2F_spec _ _ default' _ q' fd.
    have /=[k eq]:= N2MF_spec vl.
    pose Mphi' q'0 := if q'0 == q'
                      then (LF2F default'
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
