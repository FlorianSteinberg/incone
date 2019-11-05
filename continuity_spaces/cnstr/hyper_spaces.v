From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_rlzrs.
Require Import axioms all_cs_base classical_func classical_cont dscrt cprd.
Require Import Classical Morphisms ChoiceFacts.
Require Import Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Sirpinskispace.
  Definition Sirp := option unit.

  Local Notation top := (Some tt: Sirp).
  Local Notation bot := (None: Sirp).

  Definition names_Sirp := Build_naming_space 0 nat_count bool_count.
  Definition rep_Sirp := make_mf (fun (phi: names_Sirp) s => (exists n: nat, phi n = true) <-> s = top).

  Lemma rep_Sirp_tot: rep_Sirp \is_total.
  Proof.
    move => phi.
    by case: (classic (exists n, phi n = true)) => [ | nex]; [exists top | exists bot].
  Qed.
                                                                          
  Lemma rep_Sirp_rep: rep_Sirp \is_representation.
  Proof.
    split => [[[] | ] | ? s s' [imp imp'] [pmi pmi']]; first by exists (cnst true); split => // _; exists 0.
    - by exists (cnst false); split => //; case.
    case E: s => [[]|]; first by symmetry; apply/pmi/imp'.
    by case E': s' => [[]|]; first by rewrite -E; apply/imp/pmi'.
  Qed. 

  Canonical Sirpinski_representation:= Build_representation_of rep_Sirp_rep.

  Canonical cs_Sirp:= repf2cs Sirpinski_representation.

  Context (X: Type).

  Definition CF2SS (chi: X -> cs_Sirp) := make_subset (fun (t: X) => chi t = top).

  Lemma CF2SS_spec chrf: CF2SS chrf === dom (pf2MF (chrf)).
  Proof. by move => x /=; case: (chrf x) => [[]|]//; split => //; [exists tt | case]. Qed.

  Definition characteristic_function (A: subset X) :=
    make_mf (fun x (s: cs_Sirp) => s = top <-> x \from A).
  Local Notation "'chi_' A":= (characteristic_function A) (at level 2, format "'chi_' A").

  Global Instance chrf_prpr: Proper (@set_equiv X ==> @equiv X cs_Sirp) characteristic_function.
  Proof. by move => O U eq x s /=; rewrite eq. Qed.

  Lemma chrf_sing A: chi_ A \is_singlevalued.
  Proof.
    move => x s s' /= [imp imp'] [pmi pmi'].
    case E: s => [[]|]; symmetry; first exact/pmi'/imp.
    by case E': s' => [[]|]//; rewrite -E; symmetry; apply/imp'/pmi.
  Qed.

  Lemma chrf_tot A: chi_ A \is_total.
  Proof. by move => x; case: (classic (x \from A)); [exists top | exists bot]. Qed.

  Lemma chrf_CF2SS chrf: chi_ (CF2SS chrf) =~= F2MF chrf.
  Proof.
    move => x [[] | ] /=; first by split => [[->] | ]//.
    by split => [[] | ->]//; case: (chrf x) => // [[_ prp]]; symmetry; apply/prp.
  Qed.

  Lemma SF2SS_chrf A f: F2MF f =~= chi_ A -> CF2SS f === A.
  Proof. by move => eq x /=; have /=-> := eq x top; split => [<- | ]//. Qed.

  Definition P2CF T p (t: T):=
    match p t with
    | true => top
    | false => bot
    end.

  Definition CF2P T (chi: T -> Sirp) t:=
    match chi t with
    | Some _ => true
    | None => false
    end.

  Lemma P2CFK T: cancel (@P2CF T) (@CF2P T).
  Proof.
    move => chi; apply/functional_extensionality => t.
    by rewrite /P2CF /CF2P; case: ifP.
  Qed.

  Lemma CF2PK T: cancel (@CF2P T) (@P2CF T).
  Proof.
    move => chi; apply/functional_extensionality => t.
    by rewrite /P2CF /CF2P; case: (chi t) => // [[]].
  Qed.

  Definition complement T (A: pred T) t := 
    match A t with
    | true  => false
    | false => true
    end.

  Lemma complement_involutive T: involutive (@complement T).
  Proof.
    move => A; apply/functional_extensionality => x.
    by rewrite /complement; case: (A x) => //; case.
  Qed.
  End Sirpinskispace.
Notation top := (Some tt).
Notation bot := (@None unit).
Notation "'chi_' A":= (characteristic_function A) (at level 2, format "'chi_' A").
Arguments P2CF {T}.
Arguments CF2P {T}.

Section Opens_and_closeds.
  Context (X: cs).

  Definition cs_opens:= X c-> cs_Sirp.
  Notation "\O( X )" := cs_opens (at level 2, format "'\O(' X ')'").
  
  Definition O2SS (O: \O(X)) := CF2SS (sval O).

  Lemma O2SS_spec O: O2SS O === dom (pf2MF (sval O)).
  Proof. exact/CF2SS_spec. Qed.

  Definition open O := exists (O': \O(X)), O === O2SS O'.

  Global Instance open_prpr: Proper (@set_equiv X ==> iff) open.
  Proof.
    move => O U eq; split => [[O' eq'] | [O' eq']]; exists O'.
    - by rewrite -eq.
    by rewrite eq.
  Qed.
  
  Lemma open_open (O: \O(X)): open (O2SS O).
  Proof. by exists O. Qed.
    
  Lemma chrf_open (O: subset X):
    FunctionalChoice_on X Sirp ->
    open O <-> chi_ O \has_continuous_realizer.
  Proof.
    move => choice; split => [[U ->] | cont].
    - by rewrite chrf_CF2SS; move: U => [U /cfun_spec cont/=].
    have [ | | chrf eq]//:= (classical_mf.fun_spec (chi_ O) top _).2.
    - by split; [apply/chrf_sing | apply/chrf_tot].
    rewrite <-eq in cont; exists (exist_c cont) => x.
    split => [Ox/= | /= eq']; first by apply/eq.
    by apply/((eq x top).1 eq').1.
  Qed.

  Lemma all_open: open (@All X).
  Proof.
    suff cont: continuous (cnst top: X -> cs_Sirp) by exists (exist_c cont).
    exists (mf_cnst (cnst true)).  
    split; try by apply/F2MF_rlzr_F2MF; split => //; exists 0.
    by rewrite cont_F2MF; apply cnst_cont.
  Qed.

  Lemma empty_open: open (@empty X).
  Proof.
    suff cont: continuous (cnst bot: X -> cs_Sirp).
    - by exists (exist_c cont).
    exists (F2MF (fun phi q => false)).  
    split; try by apply/F2MF_rlzr_F2MF; split => [[] | ].
    by rewrite cont_F2MF; apply cnst_cont.
  Qed.

  Definition closeds:= make_subset (fun (A: X -> cs_Sirp) =>
                                      (P2CF (complement A)) \from codom (associate X cs_Sirp)).
  
  Lemma clos_open A: A \from closeds <-> exists (O: \O(X)), projT1 O = P2CF (complement A).
  Proof. by split => [/cfun_spec cont | [[O Ocont/=] <-]] //; exists (exist_c cont). Qed.

  Definition names_closeds:= Build_naming_space someq (Q_count \O(X)) (A_count \O(X)).

  Definition rep_clsd := make_mf (fun (phi: names_closeds) (A: closeds) =>
                                    associate X cs_Sirp phi (P2CF (complement (projT1 A)))).

  Lemma rep_clsd_rep: rep_clsd \is_representation.
  Proof.
    split; first by move => [A [psi ass]/=]; exists psi.
    move => phi A A' /= phinA phinA'; apply/eq_sub => /=.
    rewrite -(CF2PK (sval A)) -(CF2PK (sval A')).
    rewrite -(complement_involutive (CF2P (sval A))) -(complement_involutive (CF2P (sval A'))).
    f_equal; f_equal; rewrite -[LHS]P2CFK -[RHS]P2CFK.
    by have /= ->:= choice_dict.mf_rlzr_f_sing phinA phinA'.    
  Qed.  

  Definition closeds_representation:= Build_representation_of rep_clsd_rep.
  Definition cs_closeds:= repf2cs closeds_representation.
  
  Local Notation "\A(X)" := cs_closeds.

  Definition A2SS (A: \A(X)) := CF2SS (sval A).

  Lemma A2SS_spec A: A2SS A === dom (pf2MF (sval A)).
  Proof. exact/CF2SS_spec. Qed.
  
  Definition closed (A: subset X) := exists (A': \A(X)), A === A2SS A'.

  Global Instance clsd_prpr: Proper (@set_equiv X ==> iff) closed.
  Proof.
    move => A B eq; split => [[A' eq'] | [A' eq']]; exists A'.
    - by rewrite -eq'; symmetry.
    by rewrite -eq'.
  Qed.

  Lemma P2CF_cmpl T (O: T -> Sirp):
    P2CF (complement (fun x => P2CF (complement (fun y => O y)) x)) = O.
  Proof.
    rewrite /P2CF/complement /=.
    by apply/functional_extensionality => x; do 4 case: ifP => //; case: (O x) => // [[]].
  Qed.
  
  Lemma complement_closed (O: \O(X)): P2CF (complement (sval O)) \from closeds.
  Proof. by case: O => [O ass /=]; rewrite P2CF_cmpl. Qed.

  Definition complement_opens (O: \O(X)): \A(X) := exist _ _ (complement_closed O).

  Lemma cmplO_cont: complement_opens \is_continuous.
  Proof.
    exists mf_id.
    split; try by apply /cont_F2MF => phi; exists (fun n => [:: n]) => q' psi [].
    apply/F2MF_rlzr_F2MF => psi O psinO phi x phinx fd.
    have [ | dm prp]:= psinO phi x phinx; first by exists (sval O x).
    split => // Fphi val.
    have [s [Fphins /= eq]]:= prp Fphi val.
    exists s; split => //=.
    by rewrite P2CF_cmpl.
  Qed.

  Lemma complement_open (A: \A(X)): (P2CF (complement (sval A))) \is_continuous.
  Proof. by case: A => [A /= [psi ass]]; apply/ass_cont; exists psi. Qed.

  Definition complement_closeds (A: \A(X)): \O(X) := exist_c (complement_open A).
  
  Lemma cmplA_cont: complement_closeds \is_continuous.
  Proof.
    exists mf_id.
    split; try by apply/cont_F2MF => phi; exists (fun n => [:: n]) => q' psi [].
    apply/F2MF_rlzr_F2MF => psi A psinA phi x phinx fd.
    by have [ | dm prp]:= psinA phi x phinx; first by exists (P2CF (complement (sval A)) x).
  Qed.
  
  Lemma clsd_iso_open: \O(X) ~=~ \A(X).
  Proof.
    exists (exist_c cmplO_cont).
    exists (exist_c cmplA_cont).
    by split => O; apply/eq_sub/P2CF_cmpl.
  Qed.

  Lemma all_clsd: closed All.
  Proof.
    have [A eq]:= empty_open.
    exists (complement_opens A) => x; split => // _ /=.
    by rewrite /P2CF/complement; have /=:= eq x; case: (sval A x) => [[[]]|]//.
  Qed.

  Lemma empty_clsd: closed empty.
  Proof.
    have [A eq]:= all_open.
    exists (complement_opens A) => x; split => //=.
    by rewrite /P2CF/complement; have [->]:= eq x.
  Qed.
End Opens_and_closeds.
Notation "\O( X )" := (cs_opens X) (at level 2, format "'\O(' X ')'").
Arguments open {X}.
Arguments O2SS {X}.
Arguments complement {T}.
Notation "\A( X )" := (cs_closeds X) (at level 2, format "'\A(' X ')'").
Arguments A2SS {X}.
Arguments closed {X}.
Arguments complement_opens {X}.
Arguments complement_closeds {X}.

Section admissibility.
  Definition OO_fun (X: cs) (x: X) := (point_evaluation cs_Sirp x) : \O(\O(X)).

  Lemma OO_fun_cont (X: cs): (@OO_fun X) \is_continuous.
  Proof. exact/ptvl_cont. Qed.  
  
  Definition admissible (X: cs) := F2MF (@OO_fun X)\^-1 \has_continuous_realizer.
End admissibility.

Section Kleeneans.
  Inductive Kleeneans := false_K | true_K | bot_K.

  Definition names_Kleeneans:= Build_naming_space 0 nat_count (option_count bool_count).

  Definition rep_K :=
    make_mf (fun (phi: names_Kleeneans) (t: Kleeneans) =>
	       match t with
	       | false_K => exists (n: nat), phi n = Some false /\ forall m, m < n -> phi m = None
	       | true_K => exists (n: nat), phi n = Some true /\ forall m, m < n -> phi m = None
	       | bot_K => forall n, phi n = None
	       end).
  
  Lemma rep_K_rep: rep_K \is_representation.
  Proof.
    split; first by case; [exists (cnst (Some false)) | exists (cnst (Some true))|exists (cnst None)]; try exists 0.
    move => phi t t'.
    case: t; case t' => //; try (move => [n [eq prp]] prp'; by rewrite prp' in eq);
      try (move => prp; case => n []; by rewrite prp); move => [n [eq prp]] [m []].
    - case/orP: (leq_total m n) => ineq; rewrite leq_eqVlt in ineq.
      + by case/orP: ineq => [/eqP -> | ineq]; [rewrite eq | rewrite prp].
      by case/orP: ineq => [/eqP <- | ineq eq' prp']; [rewrite eq | rewrite prp' in eq].
    case/orP: (leq_total m n) => ineq; rewrite leq_eqVlt in ineq.
    - by case/orP: ineq => [/eqP -> | ineq]; [rewrite eq | rewrite prp].
    by case/orP: ineq => [/eqP <- | ineq eq' prp']; [rewrite eq | rewrite prp' in eq].
  Qed.

  Canonical Kleeneans_representation := Build_representation_of rep_K_rep.

  Canonical cs_Kleeneans:= repf2cs Kleeneans_representation.
  

  Definition choose := make_mf (fun s1s2 k => (s1s2.1 = top /\ k = true_K) \/ (s1s2.2 = top /\ k = false_K) \/ (s1s2.1 = bot /\ s1s2.2 = bot /\ k = bot_K)).
  Definition choose_rlzrf (phi : (names_Sirp \*_ns names_Sirp)) n := match (lprj phi n) with
                                   | true => (Some true)
                                   | false =>
                                     match (rprj phi n) with
                                    | true => (Some false)
                                    | _ => None
                                     end
                                   end.
Lemma choose_rlzrf_spec : (F2MF choose_rlzrf) \solves choose.
Proof.
  rewrite F2MF_slvs => phi /= [k1 k2] /prod_name_spec [/=k1ephin k2ephin].
  have cases : (k1 = top /\ k2 = top \/ k1 = top /\ k2 = bot \/ k1 = bot /\ k2 = top \/ k1 = bot /\ k2 = bot).
  - case k1; case k2; try by auto; (try by case;auto).
      case; case; by auto.
  have P' prp: (exists (n: nat), prp n = true) -> (exists (n: nat), prp n = true /\ forall m, (m < n) -> prp m = false).
    move => H.
    suff :  (exists (n: nat), prp n = true /\ forall m,  prp m = true -> (n <= m)).
    case  => n [nprp1 nprp2]; exists n.
    split => [| m mprp]; first by auto.
    apply Bool.not_true_is_false => B.
    have /leP := (nprp2 m B) => mprp'.
    move /ltP : mprp => mprp.
    by lia.
    by apply classical_count.well_order_nat.
  have P1 : (k1 = top -> (exists (n: nat), lprj phi n = true /\ forall m,  (m < n) -> (lprj phi m = false))).
  - move => H.
    by apply P';apply k1ephin. 
  have P1' : (k1 = bot -> (forall (n: nat), lprj phi n = false)).
  - move => H n.
    have kp1' : (k1 <> top) by rewrite H.
    by rewrite (Bool.not_true_is_false _ (not_ex_all_not _ _ (iffRLn k1ephin kp1') n)).
  have P2 : (k2 = top -> (exists (n: nat), rprj phi n = true /\ forall m, (m < n) -> (rprj phi m = false))).
  - move => H.
    by apply P';apply k2ephin. 
  have P2' : (k2 = bot -> (forall (n: nat), rprj phi n = false)).
  - move => H n.
    have kp2' : (k2 <> top) by rewrite H.
    by rewrite (Bool.not_true_is_false _ (not_ex_all_not _ _ (iffRLn k2ephin kp2') n)).
  case cases; [| case; [| case]]; move => [kp1 kp2].
  - case  (P1 kp1) => m [mprp1 mprp2]; case (P2 kp2) => n [nprp1 nprp2]; move => _.
    case e: (m <= n).
    + exists true_K; split; first by auto.
      exists m.
      rewrite /choose_rlzrf mprp1; split => [ | m' m'prp]; first by auto.
      rewrite (mprp2 _ m'prp).
      have m'prp2 : (m' < n).
      apply /leP;move /leP : e; move /leP : m'prp.
      by lia.
      by rewrite (nprp2 _ m'prp2).
   exists false_K; split; first by auto.   
   exists n.
   rewrite /choose_rlzrf nprp1 mprp2 ; last by (apply /leP; move /leP : e;lia).
   split => [ | n' n'prp]; first by auto.
   rewrite nprp2; last by (apply /leP; move /leP : n'prp;lia).
   rewrite mprp2 //.
   by apply /leP; move /ltP : n'prp; move /leP : e;lia.
  - move => _.
    exists true_K.
    split; first by auto.
    case (P1 kp1) => n [nprp1 nprp2].
    exists n; split => [| m mprp]; rewrite /choose_rlzrf;first by rewrite nprp1.
    rewrite (nprp2 _ mprp).
    by rewrite (P2' kp2).
  - move => _.
    exists false_K.
    split; first by auto.
    case (P2 kp2) => n [nprp1 nprp2].
    exists n; split => [| m mprp]; rewrite /choose_rlzrf; first by rewrite nprp1 (P1' kp1).
    by rewrite (P1' kp1) (nprp2 _ mprp).
  move => _.
  exists bot_K; split => [ | n ]; first by auto.
  by rewrite /choose_rlzrf (P1' kp1) (P2' kp2).
Qed.
End Kleeneans.

Section Open_subsets_of_nat.

  Lemma ON_iso_Sirpw : \O(cs_nat) ~=~ (cs_Sirp\^w).
  Proof. by rewrite sig_iso_fun; apply/iso_ref. Qed.
  Definition names_ON:= Build_naming_space 0 nat_count nat_count.

  Definition rep_ON := make_mf(fun (phi: names_ON) (p: pred nat) =>
                               forall n, p n <-> exists m, phi m = n.+1).

  Lemma rep_ON_rep: rep_ON \is_representation.
  Proof.
    split => [p /= | phi A B phinA phinB].
    - exists (fun n => if p n then n.+1 else 0) => n.
      split => [eq | [m]]; first by exists n; rewrite eq.
      by case E: (p m) => [|] => [[<-] | ].                                     
    apply/fun_ext => n; have := phinA n; have <-:= phinB n.
    case: (A n); case: (B n) => // eq; last exact/eq.
    by symmetry; apply/eq.
  Qed.

  Canonical ON_representation := Build_representation_of rep_ON_rep.

  Canonical cs_ON:= repf2cs ON_representation.
  
  Definition ON2Sw_rlzrf (phi: nat -> nat) (nm: nat * nat):= ((phi nm.2) == nm.1.+1).

  Definition ON2Sw_rlzr:= F2MF ON2Sw_rlzrf: B_ cs_ON ->> B_(cs_Sirp\^w).
  
  Lemma ON2Sw_rlzr_spec: ON2Sw_rlzr \realizes (@P2CF nat: cs_ON -> cs_Sirp\^w).
  Proof.
    apply/F2MF_rlzr_F2MF => phi A phinA n.
    have := phinA n; rewrite /P2CF.
    case: (A n).
    - case => [[]// m /eqP eq _].
      split => // _; exists m; rewrite /ON2Sw_rlzrf /=.
      by rewrite eq.
    case => [_ prp].
    rewrite /ON2Sw_rlzrf /=.
    split => // [[m /= /eqP eq]].
    suff: false by trivial.
    by apply/prp; exists m.
  Qed.  

  Lemma ON2Sw_rlzr_cntop: ON2Sw_rlzr \is_continuous_operator.
  Proof.
    rewrite cont_F2MF => phi.
    by exists (fun nm => [:: nm.2]) => nm psi /= []; rewrite /= /ON2Sw_rlzrf => ->.
  Qed.

  Definition Sw2ON_rlzrf (phi: nat * nat -> bool) (n: nat):=
    match unpickle n with
    | None => 0%nat
    | Some nm => if phi nm then nm.1.+1 else 0
    end.

  Definition Sw2ON_rlzr:= F2MF Sw2ON_rlzrf : B_(cs_Sirp\^w) ->> B_ cs_ON.
             
  Lemma Sw2ON_rlzr_spec: Sw2ON_rlzr \realizes (@CF2P nat: cs_Sirp\^w -> cs_ON).
  Proof.
    rewrite F2MF_rlzr => phi A phinA n.
    have := phinA n; rewrite/CF2P.
    case: (A n) => [[]|].
    - case => [_ []// m eq]; split => // _.
      exists (pickle (n, m)).
      by rewrite /Sw2ON_rlzrf pickleK eq.
    case => prp _; rewrite /Sw2ON_rlzrf; split => // [[m]].
    case: (unpickle m) => // [[m' k]] eq.
    suff: bot = top by trivial.
    by apply/prp; exists k; move: eq; case: ifP => // pr [<-].
  Qed.

  Lemma Sw2AN_rlzr_cntop: Sw2ON_rlzr \is_continuous_operator.
  Proof.
    apply/cont_F2MF => phi /=.
    exists (fun n => match unpickle n with | None => nil | Some nm => [:: nm] end).
    move => n psi; rewrite /Sw2ON_rlzrf.
    by case: (unpickle n) => // nm [->].
  Qed.  
 
  Lemma ON2Sw_cont: (@P2CF nat: cs_ON -> cs_Sirp\^w) \is_continuous.
  Proof. by exists ON2Sw_rlzr; split; try exact/ON2Sw_rlzr_spec; apply/ON2Sw_rlzr_cntop. Qed.

  Lemma Sw2ON_cont: (@CF2P nat: cs_Sirp\^w -> cs_ON) \is_continuous. 
  Proof. by exists Sw2ON_rlzr; split; try exact/Sw2ON_rlzr_spec; apply/Sw2AN_rlzr_cntop. Qed.

  Definition Onat2ON:= CF2P \o_f sval: \O(cs_nat) -> cs_ON.

  Lemma Onat2ON_cont: Onat2ON \is_continuous.
  Proof.
    rewrite /continuous -F2MF_comp_F2MF.
    exact/(@comp_hcs _ (cs_Sirp\^w))/Sw2ON_cont/fun2sig_cont.
  Qed.

  Definition ON2Onat : cs_ON -> \O(cs_nat):= (@sig2fun _ 0 nat_count cs_Sirp) \o_f P2CF.

  Lemma ON2Onat_cont: ON2Onat \is_continuous.
  Proof.
    rewrite /continuous -F2MF_comp_F2MF.
    exact/(@comp_hcs _ (cs_Sirp\^w))/sig2fun_cont/ON2Sw_cont.    
  Qed.

    
    Lemma ON_iso_Sw: cs_ON ~=~ (cs_Sirp\^w).
  Proof.
    by exists (exist_c ON2Sw_cont); exists (exist_c Sw2ON_cont); split; [apply P2CFK | apply CF2PK].
  Qed.

  Lemma ON_iso_Onat: cs_ON ~=~ \O(cs_nat).
  Proof. by rewrite ON_iso_Sw; apply/sig_iso_fun. Qed.
End Open_subsets_of_nat.

Section Closed_subsets_of_nat.
  Definition names_AN := Build_naming_space 0 nat_count nat_count.
  Definition rep_AN := make_mf(fun (phi: names_AN) (A: pred nat) =>
                                 forall n, ~~ A n <-> exists m, phi m = n.+1).

  Lemma rep_AN_spec : rep_AN =~= (F2MF complement) \o rep_ON.
  Proof.
    move => phi A; split => [phinA | [[cA [phincA <-]] _] n].
    - split; last by rewrite F2MF_dom; apply/subs_all.
      exists (complement A); split => [n | ]; last exact/complement_involutive.
      by have <-:= phinA n; rewrite /complement; case : (A n).
    by have <-:= phincA n; rewrite /complement; case : (cA n).
  Qed.

  Lemma involutive_sur T (f: T -> T): involutive f -> f \is_surjective.
  Proof. by move => invo t; exists (f t); apply/invo. Qed.

  Lemma rep_AN_rep: rep_AN \is_representation.
  Proof.
    split; last by rewrite rep_AN_spec; apply/comp_sing/(@rep_sing cs_ON)/F2MF_sing.
    rewrite rep_AN_spec; apply/comp_cotot/rep_sur; first exact/(@rep_sing cs_ON).
    by rewrite -F2MF_cotot; apply/involutive_sur/complement_involutive.
  Qed.

  Canonical AN_representation:= Build_representation_of rep_AN_rep.
  Definition cs_AN:= repf2cs AN_representation.

  Lemma id_cntop Q A: (@mf_id (Q -> A)) \is_continuous_operator.
  Proof. by apply/cont_F2MF => phi; exists (fun n => [:: n]) => q psi []. Qed.

  Lemma cmpl_cont: (complement: cs_AN -> cs_ON) \is_continuous.
  Proof.
    exists mf_id; split; try exact/id_cntop.
    apply/F2MF_rlzr_F2MF => phi A /rep_AN_spec [[cA [phincA <-]] _].
    by rewrite /= complement_involutive.
  Qed.

  Lemma cont_cmpl: (complement: cs_ON -> cs_AN) \is_continuous.
  Proof.
    exists mf_id; split; try exact/id_cntop.
    apply/F2MF_rlzr_F2MF => phi O phinO.
    by apply/rep_AN_spec; split; [exists O | rewrite F2MF_dom; apply/subs_all].
  Qed.
 
  Lemma AN_iso_Anat: cs_AN ~=~ \A(cs_nat).
  Proof.
    rewrite -clsd_iso_open -ON_iso_Onat.
    exists (exist_c cmpl_cont).
    exists (exist_c cont_cmpl).
    by split; apply/complement_involutive.
  Qed.

  Definition Anat2AN := sval: \A(cs_nat) -> cs_AN.

  Lemma Anat2AN_cont: Anat2AN \is_continuous.
  Proof.
    rewrite /continuous -(comp_id_r (F2MF _)).
    have <-: F2MF (complement_opens \o_f complement_closeds) =~= @mf_id \A(cs_nat).
    - by split => <-//; apply/eq_sub/functional_extensionality => x/=; rewrite P2CF_cmpl.
    rewrite -F2MF_comp_F2MF -comp_assoc.
    apply/comp_hcs; first exact/cmplA_cont.
    rewrite /continuous -(comp_id_l (F2MF _)).
    have <-: F2MF (complement \o_f complement) =~= @mf_id cs_AN.
    - by move => p A /=; rewrite complement_involutive.
    rewrite -F2MF_comp_F2MF !comp_assoc.
    apply/(@comp_hcs _ cs_ON); last exact/cont_cmpl.
    suff ->: F2MF (@complement cs_nat) \o (F2MF (fun e n => isSome (sval e n)) \o F2MF complement_opens) =~= (F2MF CF2P) \o F2MF sval.
    - by apply/(@comp_hcs _ (cs_Sirp\^w))/Sw2ON_cont/fun2sig_cont.
    move => x y; rewrite !comp_F2MF /=; split => <-.
    - by rewrite -{1}(P2CF_cmpl (sval x)) P2CFK.
    by rewrite -{2}(P2CF_cmpl (sval x)) P2CFK.
  Qed.

  Definition AN2Anat (p: cs_AN): \A(cs_nat).
    exists (P2CF p); apply/cfun_spec/nat_dscrt.
  Defined.
  
  Lemma AN2Anat_cont: AN2Anat \is_continuous.
  Proof.
    rewrite /continuous -(comp_id_l (F2MF _)).
    have <-: F2MF (complement_opens \o_f complement_closeds) =~= @mf_id \A(cs_nat).
    - by split => <-//; apply/eq_sub/functional_extensionality => x/=; rewrite P2CF_cmpl.
    rewrite -F2MF_comp_F2MF comp_assoc.
    apply/comp_hcs; last exact/cmplO_cont.
    rewrite -(comp_id_r (F2MF AN2Anat)).
    have <-: F2MF (complement \o_f complement) =~= @mf_id cs_AN.
    - by move => p A /=; rewrite complement_involutive.
    rewrite -F2MF_comp_F2MF -!comp_assoc.
    apply/(@comp_hcs _ cs_ON); first exact/cmpl_cont.
    suff ->: (F2MF complement_closeds \o F2MF AN2Anat) \o F2MF complement =~= F2MF ON2Onat.
    - by apply/ON2Onat_cont.
    move => x y; rewrite !comp_F2MF /=; split => <-.
    - apply/eq_sub/functional_extensionality => n /=.
      by rewrite /P2CF/complement; case: ifP => //.
    apply/eq_sub/functional_extensionality => n /=.
    by rewrite /P2CF/complement; do 4 case: ifP => //.
  Qed.    
End Closed_subsets_of_nat.
  
