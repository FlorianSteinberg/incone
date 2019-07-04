(* This file provides an abstract envelope for computability theoretical considerations *)
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype choice seq.
From mf Require Import all_mf.
Require Import iseg baire cont ClassicalChoice seq_cont.

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

End Phi_assignment.
Notation "\Phi_ N" := (Phi N) (format "'\Phi_' N", at level 2).

Section use_first.
  Context Q A (N: nat -> Q -> option A).
  Local Notation "N \is_monotone" := (monotone N) (at level 2).
          
  Definition use_first n q:= N (search (fun k => N k q) n) q.

  Lemma sfrst_mon: use_first \is_monotone.
  Proof.
    move => q n neq.
    rewrite /use_first.
    f_equal; symmetry.
    rewrite -search_search.
    apply/search_eq .
    move: neq; rewrite /use_first.
    by case: (N (search (fun k => N k q) n) q).
    by apply/leq_trans; first exact/search_le.
  Qed.

  Lemma sfrst_sing: \Phi_use_first \is_singlevalued.
  Proof. exact/mon_sing/sfrst_mon. Qed.

  Lemma sfrst_spec: \Phi_use_first \tightens \Phi_N.
  Proof.
    have mon:= @sfrst_mon.
    rewrite tight_spec.
    split => [q [a [n eq]] | q a [_ [n eq]]]; last by exists (search (fun k => N k q) n).
    have: is_true (isSome (N (search (fun k => N k q) n) q)).
    * by apply/(@search_correct (fun k => N k q)); rewrite eq.
    by case E: (N (search (fun k => N k q) n) q) => [b | ] //_; exists b; exists n.
  Qed.

  Lemma mon_sfrst: N \is_monotone <-> forall n q, N n q = use_first n q.
  Proof.
    split => [/mon_spec mon n q | eq n m neq]; last by rewrite eq sfrst_mon -eq.
    rewrite /use_first.
    case E: (N (search (fun k => N k q) n) q) => [a | ].
    - apply/mon; last exact/E.
      exact/search_le.
    have := @search_le (fun k => N k q) n.
    rewrite leq_eqVlt => /orP [/eqP <- | /searchP [m [Nmq mln]]] //.
    have:= @search_correct (fun k => N k q) _ Nmq.
    have ->:= @search_eq (fun k => N k q) m n Nmq; first by rewrite E.
    by case: (m) mln => // m' m'ln; apply/leq_trans/m'ln.
  Qed.
    
  Lemma sing_sfrst: \Phi_N \is_singlevalued <-> \Phi_N =~= \Phi_use_first.
  Proof.
    split => [sing q a| ->]; last exact/sfrst_sing.
    split => [[n val] | [n]]; last by exists (search (fun k => N k q) n).
    exists n.
    rewrite /use_first.
    have Nnq: N n q by rewrite val.
    have := (@search_correct (fun k => N k q) n Nnq).
    case E: (N _ q) => [b | ] // _.
    have ->:= sing q a b => //; first by exists n.
    by exists (search (fun k => N k q) n).
  Qed.
End use_first.      

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

Section evaluation_aux.
  Local Open Scope baire_scope.
  Context (A A': Type) (Q Q': eqType). 
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Notation subset T := (mf_set.subset T).

  Lemma cons_subs T t (L: seq T) P:
    L2SS (t :: L) \is_subset_of P <-> t \from P /\ L2SS L \is_subset_of P.
  Proof.
    split => [subs | [Pa subs] q /=[<- | ]]//; last by apply/subs.
    by split => [ | q lstn]; apply/subs; [left | right].
  Qed.

  Definition G2MF S T (G: subset (S * T)):= make_mf (fun s t => (s,t) \from G).

  Lemma G2MF_eq S T (G G': subset (S * T)): G === G' <-> G2MF G =~= G2MF G'.
  Proof. by split => [eq s t | eq [s t]]; apply/eq. Qed.
  
  Definition L2MF T T' (KL: seq (T * T')):= G2MF (L2SS KL).
  
  Fixpoint L2LF (T: eqType) T' (KL: seq (T * T')) q:=
    match KL with
    | nil => nil
    | qa :: KL' => if qa.1 == q
                   then qa.2 :: L2LF KL' q
                   else L2LF KL' q
    end.
    
  Lemma L2LF_spec (T: eqType) T' (KL: (seq (T * T'))):
    LF2MF (L2LF KL) =~= L2MF KL.
  Proof.    
    rewrite /L2MF.
    elim: KL => // [[t t'] KL] ih t'' t''' /=.
    case: ifP => [/eqP eq | neq].
    - split; first by case => [-> | ]; [left; rewrite eq | right; apply/ih].
      by case => [[<- <-] | ]; [left | right; apply/ih].
    split; first by right; apply/ih.
    by case => [[/eqP] | lstn]; [rewrite neq | apply/ih].
  Qed.      

  Fixpoint omap T T' (F: T -> option T') (L: seq T) :=
    match L with
    | nil => nil
    | t :: L' => match F t with
                 | Some a => a :: omap F L'
                 | None => omap F L'
                 end
    end.

Section N2LF.
  Context (N: nat -> Q -> option A).
  Definition N2LF KL q:= omap (fun n => N n q) (L2LF KL q).

  Lemma N2LF_cons q n KL q':
    N2LF ((q,n) :: KL) q' =
    if q == q' then
      match (N n q') with
      | Some a => a :: N2LF KL q'
      | None => N2LF KL q'
      end
    else N2LF KL q'.
  Proof.
    by rewrite /N2LF /=; case: ifP.    
  Qed.

  Lemma N2LFq_cons q n KL:
    N2LF ((q,n):: KL) q = if N n q is Some a then a :: N2LF KL q else N2LF KL q.
  Proof. by rewrite N2LF_cons eq_refl. Qed.
  
  Lemma N2LF_cat KL' KL q':
    N2LF (KL' ++ KL) q' = N2LF KL' q' ++ N2LF KL q'.
  Proof.
    elim: KL' => // [[q n]] KL' ih /=.
    rewrite !N2LF_cons; case: ifP => [/eqP _ | _]; last exact/ih.
    case: (N n q') => [a'/= | ]; last exact/ih.
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
    by case E: (N n q) => [a' /= | ] => [[<- | ] |]; [exists n | apply/ih | apply/ih].
  Qed.

  Lemma N2MF_cons q n KL: N2MF ((q,n)::KL) \extends N2MF KL.
  Proof.
    rewrite /N2MF => q' a' /=.
    rewrite N2LF_cons.
    case: ifP => // /eqP <-.
    by case: (N n q) => //; right.
  Qed.

  Lemma N2MF_cat KL' KL: N2MF (KL' ++ KL) \extends N2MF KL.
  Proof.
    elim: KL' => [ | qn KL' ih/=]; first rewrite cat0s => q //.
    by apply/exte_trans/N2MF_cons.
  Qed.
  
  Lemma N2MF_dom KL:
    dom (N2MF KL) \is_subset_of dom (L2MF KL).
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
    by case E: (N n q') => //; right.
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
    | qn:: KL' => if N qn.2 qn.1 is Some a then qn.1 :: list_dom KL' else list_dom KL'
    end.

  Lemma lstd_spec KL: L2SS (list_dom KL) === dom (N2MF KL).
  Proof.
    elim: KL => [q | [q n] KL ih q' /=]; first by split; case.
    rewrite N2LF_cons.
    case: ifP => [/eqP <-| /eqP neq].
    - case E: (N n q) => [a | ]; last exact/ih.
      by split => [ | [a']]; first exists a; left.
    case E: (N n q) => [a | ]; last exact/ih.
    split => [/= | ]; last by right; apply/ih.
    by case => [eq | /ih [a' val]]; [exfalso; apply/neq | exists a'].
  Qed.

  Lemma lstd_zip KL: L2SS (list_dom KL) \is_subset_of L2SS (unzip1 KL).
  Proof.
    elim: KL => // [[q n]] KL ih /=.
    case: (N n q) => [a | ]; last by right; apply/ih.
    by move => q' /=[<- | ]; [left | right; apply/ih].
  Qed.

  Lemma lstd_cat KL KL': list_dom (KL ++ KL') = list_dom KL ++ list_dom KL'.
  Proof. by elim: KL => // [[q n]] KL /= ->; case: (N n q). Qed.
End N2LF.

Section extend.
  Context (default: A).
  Definition extend (phi: Q -> seq A) q := head default (phi q).

  Lemma extend_spec phi: (extend phi) \is_choice_for (LF2MF phi).
  Proof.
    rewrite /extend => q [a /=].
    by case: (phi q) => // q' K /= [-> | ]; left.
  Qed.

  Fixpoint check_sublist (K L: seq Q):=
    match K with
    | nil => true
    | q :: K' => (q \in L) && check_sublist K' L
    end.

  Lemma clP K L: reflect (K \is_sublist_of L) (check_sublist K L).
  Proof.
    apply/(iffP idP).
    elim: K => [_ q | q K ih ]//= /andP [lstn cl].
    by apply/L2SS_subs/cons_subs; split; [exact/inP | apply/L2SS_subs/ih].
    elim: K => // q K ih /L2SS_subs/cons_subs [lstn /L2SS_subs subl] /=.
    by apply/andP; split; [exact/inP | apply/ih].
  Qed.

  Lemma zip_nill S T (L: seq T): zip ([::]:seq S) L = nil.
  Proof. by case: L. Qed.

  Lemma zip_nilr S T (K: seq S): zip K ([::]:seq T) = nil.
  Proof. by case: K. Qed.
End extend.
End evaluation_aux.

Section function_application.
  Local Open Scope baire_scope.
  Context (A': Type) (Q Q': eqType) A (default: A). 
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Context (F: B -> B').
  Context (Lf: B -> Q' -> seq Q).
  Notation subset T := (mf_set.subset T).
  Hypothesis modmod: forall phi, Lf phi \is_modulus_of (F2MF Lf) \on_input phi.
  Context (N: nat -> Q -> option A).
  
  Definition KL_step KL L q':= zip (Lf (extend default (N2LF N KL)) q') L ++ KL.

  Lemma KL_step_spec KL q' phi:
    phi \is_choice_for (\Phi_N) ->
    (L2SS (Lf (extend default (N2LF N KL)) q')) \is_subset_of dom \Phi_N ->
    exists L,
      size L = size (Lf (extend default (N2LF N KL)) q')
      /\
      (L2SS (Lf (extend default (N2LF N KL)) q')) \is_subset_of dom (N2MF N (KL_step KL L q'))
      /\
      ((extend default (N2LF N KL)) \agrees_with phi \on (dom (N2MF N KL)) ->
      (extend default (N2LF N (KL_step KL L q'))) \and phi \coincide_on (Lf (extend default (N2LF N KL)) q')).
  Proof.
    rewrite /KL_step => icf subs.
    elim: (Lf (extend default (N2LF N KL)) q') subs => [dm | q K ih /cons_subs [fd subs]].
    - by exists nil; split; last by split => // q [].
    have [L [sze [subs' coin]]]:= ih subs.
    have [n val']:= icf _ fd.
    exists (n :: L).
    split => [/= |]; first by rewrite sze.
    split => [ | agre].
    - apply/cons_subs; split; last exact/subs_trans/exte_dom/N2MF_cons/subs'.
      by exists (phi q) => /=; rewrite N2LF_cons eq_refl val'; left.
    apply/coin_lstn => q'' /= [<- | lstn]; first by rewrite /extend N2LF_cons eq_refl val'.
    rewrite /extend N2LF_cons.
    case: ifP => [/eqP <- | _]; first by rewrite val' .
    by move: q'' lstn; apply/coin_lstn/coin.
  Qed.
  
  Fixpoint KL_rec s q' := match s with
                          | nil => nil
                          | L :: s' => KL_step (KL_rec s' q') L q'
                          end.
  
  Definition phi_rec s q' := extend default (N2LF N (KL_rec s q')).

  Hypothesis (tot: \Phi_N \is_total).

  Lemma phi_rec_spec phi q':
    phi \is_choice_for (\Phi_N) ->
    exists s, phi \and (phi_rec s q') \coincide_on (Lf phi q')
              /\
              L2SS (Lf (phi_rec s q') q') \is_subset_of dom (N2MF N (KL_rec s q')).
  Proof.
    move => icf.
    have prp: forall KL, L2SS (Lf (extend default (N2LF N KL)) q') \is_subset_of dom \Phi_N.
    - by move => KL; rewrite ((tot_spec \Phi_N).1 tot); apply/subs_all.
    have /choice [sf sfprp]:= KL_step_spec icf (prp _).
    pose KL:= fix KL n := match n with
                          | 0 => nil
                          | S n' => KL_step (KL n') (sf (KL n')) q'
                          end.
    pose phin n:= extend default (N2LF N (KL n)).

    have phin_dom: forall n m, n < m -> L2SS (Lf (phin n) q') \is_subset_of dom (N2MF N (KL m)).
    - move => n m /subnK <-.
      elim: (m - n.+1) => [ | k ih]; first by rewrite add0n; have [sze []]:= sfprp (KL n).
      by rewrite addSn /= /KL_step; apply/subs_trans/exte_dom/N2MF_cat/ih.

    have phin_coin: forall n, (phin n) \and phi \coincide_on (list_dom N (KL n)).
    - elim => // n /coin_agre ih /=.
      have prp': (phin n.+1) \and phi \coincide_on (Lf (phin n) q').
        by apply sfprp => q /lstd_spec; apply/ih.
      have [sze _]:= (sfprp (KL n)).
      rewrite /KL_step lstd_cat.
      apply/coin_cat; split.
      + apply/coin_subl; first by apply/lstd_zip.
        by rewrite unzip1_zip; last by rewrite sze.        
      apply/coin_agre => q lstn.
      case E: (q \in (Lf (phin n) q')).
      + by move /coin_agre: prp' => -> //; apply/inP; rewrite E.
      move: E; rewrite /phin /= /KL_step {2}/extend N2LF_cat /=.
      move: (sf (KL n)).
      elim: (Lf (extend default (N2LF N (KL n))) q') => [sfKL _ | a L ih' sfKL lstn'].
      + by rewrite zip_nill /=; apply/ih.
      case: (sfKL) => [ | a' L']; first by rewrite zip_nilr; apply/ih.
      rewrite /= N2LF_cons.
      move: lstn'; rewrite in_cons => /orP /not_or_and [neq nin].
      case: ifP => [/eqP eq| _]; first by exfalso; apply/neq; rewrite eq.
      by apply/ih'/negP.

    have KL_subs: forall n m, n <= m -> (list_dom N (KL n)) \is_sublist_of (list_dom N (KL m)).
    - move => n m /subnK <-.
      elim: (m - n) => // k ih.
      rewrite addSn /= lstd_cat => q lstn.
      by apply/lstn_app; right; apply/ih.
      
    have phinm_coin: forall n m, n <= m -> (phin m) \and phi \coincide_on (list_dom N (KL n)).
    - move => n m /subnK <-.
      elim: (m - n) => [ | k ih]; first by rewrite add0n; apply/phin_coin.
      by rewrite addSn; apply/coin_subl/phin_coin/KL_subs; rewrite -addSn; apply/leq_addl.

    have [psi lim]: exists psi, psi \is_limit_of phin.   
    - suff /choice [psi psiprp]: forall q, exists a, exists n, forall m, n <= m -> a = phin m q.
      + exists psi; elim => [ | q K [n nprp]]; first by exists 0.
        have [k kprp]:= psiprp q.
        exists (maxn n k) => m; rewrite geq_max => /andP [ineq ineq'].
        by split; [apply/kprp/ineq' | apply/nprp/ineq].
      move => q.        
      case: (classic (exists n, q \from dom (N2MF N (KL n)))) => [[n /lstd_spec fd] | ].
      + exists (phin n q); exists n => m ineq.
        have /coin_agre ->:= phinm_coin n m ineq => //.
        by have /coin_agre ->:= phinm_coin n n (leqnn n).
      move => /not_ex_all_not nex.
      exists default; exists 0 => m _.
      suff : N2LF N (KL m) q = nil by rewrite /phin/=/extend/= => ->.
      case E: (N2LF N (KL m) q) => [ | a L] //.
      exfalso; apply/(nex m).
      by exists a; rewrite /N2MF /= E; left.

    have /cont_F2MF/cont_scnt scnt : Lf \is_continuous_function.
    - move => phi'; exists (Lf phi') => q'1 psi1 coin.
      by symmetry; apply/crt_icf; [ | apply/modmod | apply/coin | ].

    have lim': Lf psi \is_limit_of (fun n => Lf (phin n)) by apply/scnt; [apply/lim | | ].

    have eq: Lf phi q' = Lf psi q'.
    - suff coin : psi \and phi \coincide_on (Lf psi q').
      + by apply/crt_icf; [ | apply/modmod | apply/coin | ].
      have [k kprp]:= lim' [:: q'].
      have [ | -> _] //:= kprp k.
      have [k' k'prp]:= lim (Lf (phin k) q').
      apply/coin_trans; first exact/(k'prp (maxn k.+1 k'))/leq_maxr.      
      apply/coin_subl/phinm_coin/leq_maxl => q lstn.
      apply/lstd_spec.
      by apply sfprp.

    have [k lmt]:= lim' [:: q'].
    have eq': L2SS (Lf (phin k.+1) q') \is_subset_of dom (N2MF N (KL k.+1)).
    have [ | <- _]// := lmt k.+1.
    have [ | -> _]// := lmt k.
    exact/phin_dom.

    pose s := fix s n:= match n with
                        | 0 => nil
                        | S n => sf (KL n) :: s n
                        end.
    have crct: forall k, KL_rec (s k) q' = KL k.
    - by elim => // k' ih; rewrite /= ih.
    have crct': forall k, phi_rec (s k) q' = phin k.
    - by case => //k'; rewrite /phi_rec/= crct.
    exists (s k.+1).
    rewrite crct crct' eq; split => //.
    have [ | -> _]//:= lmt k.
    apply/coin_subl/coin_sym/phinm_coin/leqnn/L2SS_subs.
    by rewrite lstd_spec; apply/phin_dom.
  Qed.
 
  Definition apply_to_machine n q':=
    let s:= inverse_pickle [::] n in
    let phi := phi_rec s q' in
    if check_sublist (Lf phi q') (list_dom N (KL_rec s q'))
    then Some (F phi q')
    else None.

  Hypothesis mod: forall phi, Lf phi \is_modulus_of (F2MF F) \on_input phi.

  Lemma appN_icf phi:
    phi \is_choice_for (\Phi_N) -> (F phi) \is_choice_for \Phi_apply_to_machine.
  Proof.
    move => icf q' [a' val].
    have [s [coin ]]:= phi_rec_spec q' icf.
    rewrite -lstd_spec => /L2SS_subs /clP cl.
    exists (pickle s).
    rewrite /apply_to_machine /inverse_pickle pickleK_inv cl.
    by f_equal; apply/crt_icf; try apply/mod; try apply/coin.
  Qed.

  Lemma appN_sing:
    \Phi_N \is_singlevalued -> \Phi_apply_to_machine \is_singlevalued.
  Proof.
    rewrite /apply_to_machine => sing q' a a' [n].
    case: ifP => // /clP subl [<-] [n'].
    case: ifP => // /clP subl' [<-].
    move: subl subl'.
    set s := inverse_pickle [::] n.
    set s' := inverse_pickle [::] n'.
    move => subl subl'.
    pose phi := extend default (N2LF N (KL_rec s q' ++ KL_rec s' q')).
    apply/(@eq_trans _ _ (F phi q')).
    - symmetry; apply/crt_icf; [ | apply/mod | | ] => //.    
      apply/coin_lstn => q lstn.
      apply/sing; apply/N2MF_spec/extend_spec; first exact/lstd_spec/subl.
      by apply/lstd_spec; rewrite lstd_cat; apply/lstn_app; left; apply/subl.
    apply/crt_icf; [ | apply/mod | | ] => //.    
    apply/coin_lstn => q lstn.
    have /lstd_spec [b val]:=subl' q lstn.
    apply/sing; apply/N2MF_spec/extend_spec; first exact/lstd_spec/subl'.
    by apply/lstd_spec; rewrite lstd_cat; apply/lstn_app; right; apply/subl'.
  Qed.
    
  Lemma appN_spec phi:
    F2MF phi =~= \Phi_N -> F2MF (F phi) =~= \Phi_apply_to_machine.
  Proof.
    move => eq q' a'; split => [<- | val /=].
    - have [q qfd | s [coin ]]:= @phi_rec_spec phi q'; first exact/eq.
      rewrite /= /apply_to_machine -lstd_spec => /L2SS_subs /clP cl.
      exists (pickle s).
      rewrite /inverse_pickle pickleK_inv cl.
      f_equal.
      apply/crt_icf; [ | apply/mod | apply/coin | ] => //.
    apply/appN_sing/val; first by rewrite -eq; apply/F2MF_sing.
    apply/appN_icf => [q qfd' | ]; last by exists a'.
    exact/eq.
  Qed.
End function_application.
