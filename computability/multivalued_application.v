(* This file provides an abstract envelope for computability theoretical considerations *)
From mathcomp Require Import all_ssreflect.
From mf Require Import all_mf.
Require Import all_cont search PhiN FMop seq_cont.
Require Import axioms Classical Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
  
Section N2LF.
  Local Open Scope name_scope.
  Context (Q: eqType) (fuel A: Type). 
  Notation B := (Q -> A).
  Notation subset T := (mf_set.subset T).
  Context (N: fuel * Q -> option A).

  Fixpoint omap T T' (F: T -> option T') (L: seq T) :=
    match L with
    | nil => nil
    | t :: L' => match F t with
                 | Some a => a :: omap F L'
                 | None => omap F L'
                 end
    end.

  Definition N2LF KL q:= omap (fun n => N(n,q)) (GL2LF KL q).

  Lemma N2LF_cons q n KL q':
    N2LF ((q,n) :: KL) q' =
    if q == q' then
      match N(n,q') with
      | Some a => a :: N2LF KL q'
      | None => N2LF KL q'
      end
    else N2LF KL q'.
  Proof. by rewrite /N2LF /=; case: ifP. Qed.

  Lemma N2LFq_cons q n KL:
    N2LF ((q,n):: KL) q = if N(n,q) is Some a then a :: N2LF KL q else N2LF KL q.
  Proof. by rewrite N2LF_cons eq_refl. Qed.
  
  Lemma N2LF_cat KL' KL q':
    N2LF (KL' ++ KL) q' = N2LF KL' q' ++ N2LF KL q'.
  Proof.
    elim: KL' => // [[q n]] KL' ih /=.
    rewrite !N2LF_cons; case: ifP => [/eqP _ | _]; last exact/ih.
    case: (N(n,q')) => [a'/= | ]; last exact/ih.
    by rewrite ih.
  Qed.

  Definition N2MF LK := LF2MF (N2LF LK).
  
  Lemma N2MF_nil: N2MF [::] =~= mf_empty.
  Proof. done. Qed.

  Lemma N2MF_ext LK LK': L2SS LK === L2SS LK' -> N2MF LK =~= N2MF LK.
  Proof. done. Qed.
  
  Lemma N2MF_spec KL: \Phi_N \extends N2MF KL.
  Proof.
    elim: KL => [q a  | [q' n] KL ih q a] // prp.
    move: prp; rewrite /=/N2LF /=.    
    case : ifP => [/eqP eq /= | neq]; last exact/ih.
    by case E: (N(n,q)) => [a' /= | ] => [[<- | ] |]; [exists n | apply/ih | apply/ih].
  Qed.

  Lemma N2MF_cons q n KL: N2MF ((q,n)::KL) \extends N2MF KL.
  Proof.
    rewrite /N2MF => q' a' /=.
    rewrite N2LF_cons.
    case: ifP => // /eqP <-.
    by case: (N(n,q)) => //; right.
  Qed.

  Lemma N2MF_cat KL' KL: N2MF (KL' ++ KL) \extends N2MF KL.
  Proof.
    elim: KL' => [ | qn KL' ih/=]; first rewrite cat0s => q //.
    by apply/exte_trans/N2MF_cons.
  Qed.
  
  Lemma N2MF_dom KL:
    dom (N2MF KL) \is_subset_of dom (GL2MF KL).
  Proof.
    move => q [a].
    elim: KL => // [[q' n] KL ih /=].
    rewrite N2LF_cons.
    case: ifP => [/eqP <- | _ lstn]; first by exists n; left.
    by have [ | n' lstn']//:= ih; exists n'; right.
  Qed.

  Lemma N2MF_dom_spec K:
    (L2SS K) \is_subset_of dom \Phi_N <-> exists KL, (L2SS K) \is_subset_of dom (N2MF KL).
  Proof.
    split => [ | [KL subs]]; last exact/subs_trans/exte_dom/N2MF_spec/KL.
    elim: K => [ | q K ih /cons_subs [[a [n val]] /ih [KL subs]]]; first by exists nil.
    exists ((q,n):: KL); apply/cons_subs.
    split; first by exists a; rewrite /N2MF /= N2LF_cons eq_refl val; left.
    move => q' lstn.
    have [a' val']:= subs q' lstn.
    exists a'.
    move : val'. 
    rewrite /N2MF /= N2LF_cons.
    case: ifP => //.
    by case E: (N(n,q')) => //; right.
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
  
  Lemma last_def T (L: seq T) (t t': T):
    L <> nil -> last t L = last t' L.
  Proof. by case: L. Qed.
  
  Lemma last_lstn T (L: seq T) (t: T):
    L <> nil -> List.In (last t L) L.
  Proof.    
    case: L => // def L _.
    move: {2}(size L) (eq_refl (size L)) t def => n.
    elim: n L => [ | n ih L /eqP ]; first by case => //; left.
    case: L => // a L [sze] t def.
    rewrite last_cons; right.
    exact/ih/eqP.
  Qed.
  
  Fixpoint list_dom KL :=
    match KL with
    | nil => nil
    | qn:: KL' => if N(qn.2,qn.1) is Some a then qn.1 :: list_dom KL' else list_dom KL'
    end.

  Lemma lstd_spec KL: L2SS (list_dom KL) === dom (N2MF KL).
  Proof.
    elim: KL => [q | [q n] KL ih q' /=]; first by split; case.
    rewrite N2LF_cons.
    case: ifP => [/eqP <-| /eqP neq].
    - case E: (N(n,q)) => [a | ]; last exact/ih.
      by split => [ | [a']]; first exists a; left.
    case E: (N(n,q)) => [a | ]; last exact/ih.
    split => [/= | ]; last by right; apply/ih.
    by case => [eq | /ih [a' val]]; [exfalso; apply/neq | exists a'].
  Qed.

  Lemma lstd_zip KL: L2SS (list_dom KL) \is_subset_of L2SS (unzip1 KL).
  Proof.
    elim: KL => // [[q n]] KL ih /=.
    case: (N(n,q)) => [a | ]; last by right; apply/ih.
    by move => q' /=[<- | ]; [left | right; apply/ih].
  Qed.

  Lemma lstd_cat KL KL': list_dom (KL ++ KL') = list_dom KL ++ list_dom KL'.
  Proof. by elim: KL => // [[q n]] KL /= ->; case: (N(n,q)). Qed.
End N2LF.

Section machine_application.
  Local Open Scope name_scope.
  Context (fuel fuel' A': Type) (Q Q': eqType) A (default: A) (no_fuel: fuel). 
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Context (M: B -> fuel' * Q' -> option A').
  Context (mu: B -> fuel' * Q' -> seq Q).
  Context (N: fuel * Q -> option A).
  Notation LM := mu.
  
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
      (K \n (dom \Phi_N)) \is_subset_of dom (N2MF N (KL_step n KL L q'))
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
    exists (no_fuel :: L); split; first by rewrite /= sze.
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
              (LM phi (n,q')) \is_subset_of dom (N2MF N (KL_rec n s q')).
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

  Definition machine_application (ksq': fuel' * seq (seq (fuel)) * Q')  :=
    let (ks, q'):= ksq' in
    let (k,s) := ks in 
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
    exists (n, s).
    rewrite /machine_application /=.
    have ->: LM (phi_rec n s q') (n,q') = LM phi (n,q').
    - by apply/crt_icf; [ | apply/modmod | apply/coin | ].
    rewrite cl -val.
    have [a crt'] := crt.
    by apply/crt_icf; [ | exists a; apply/crt' | apply/coin | ].
  Qed.

  Hypothesis mod: (continuity_modulus (F2MF M)) \extends (F2MF LM).

  Lemma mapp_exte Fphi:
    Fphi \from \F_M phi -> (\Phi_machine_application) \extends (F2MF Fphi).
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
             
  Lemma mapp_sing:
    \Phi_N \is_singlevalued -> phi \from dom \F_M -> \F_M \is_singlevalued ->
    \Phi_machine_application \is_singlevalued.
  Proof.
    rewrite /machine_application => sing [Fphi val] Fsing q' a a' [[n s]] /=.
    case: ifP => // /clP subl eq [[n' s']].
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

  Lemma mapp_spec Fphi: Fphi \from \F_M phi -> forall q', \Phi_machine_application q' (Fphi q').
  Proof. by move => val q'; apply/mapp_exte; first exact/val. Qed.
End machine_application.
  
    
Section operator_to_functional.
  Local Open Scope name_scope.
  Context (Q Q': eqType) A A' (M: (Q -> A) -> nat * Q' -> option A').
  Notation B := (Q -> A).
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
