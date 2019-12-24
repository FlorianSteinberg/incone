From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_rlzrs.
Require Import axioms all_cs_base dscrt cprd classical_func classical_cont.
Require Import Classical Morphisms ChoiceFacts.
Require Import Psatz. 
Require Import search.

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
                                                                          
  Lemma rep_Sirp_sur: rep_Sirp \is_cototal.
  Proof.
    case; first by case; exists (cnst true); split => // _; exists 0.
    by exists (cnst false); split => //; case.
  Qed.

  Lemma rep_Sirp_sing: rep_Sirp \is_singlevalued.
  Proof.
    move => ? s s' [imp imp'] [pmi pmi'].
    case E: s => [[]|]; first by symmetry; apply/pmi/imp'.
    by case E': s' => [[]|]; first by rewrite -E; apply/imp/pmi'.
  Qed. 

  Canonical Sirpinski_representation: representation_of Sirp.
    by exists names_Sirp; exists rep_Sirp; try exact/rep_Sirp_sur; apply/rep_Sirp_sing.
  Defined.

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

  Lemma rep_clsd_sur: rep_clsd \is_cototal.
  Proof.
    by move => [A [psi ass]/=]; exists psi.
  Qed.
  
  Lemma rep_clsd_sing: rep_clsd \is_singlevalued.
    move => phi A A' /= phinA phinA'; apply/eq_sub => /=.
    rewrite -(CF2PK (sval A)) -(CF2PK (sval A')).
    rewrite -(complement_involutive (CF2P (sval A))) -(complement_involutive (CF2P (sval A'))).
    f_equal; f_equal; rewrite -[LHS]P2CFK -[RHS]P2CFK.
    by have /fun_ext -> := dict.rlzr_F2MF_eq (D:= cs_Sirp) (I:= X) phinA' phinA.    
  Qed.  

  Definition closeds_representation: representation_of closeds.
    by exists names_closeds; exists rep_clsd; try exact/rep_clsd_sur; apply/rep_clsd_sing.
  Defined.

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
  
  Lemma rep_K_sur: rep_K \is_cototal.
  Proof. by case; [exists (cnst (Some false)) | exists (cnst (Some true))|exists (cnst None)]; try exists 0. Qed.

  Lemma rep_K_sing: rep_K \is_singlevalued.
  Proof.
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

  Canonical Kleeneans_representation: representation_of Kleeneans.
    by exists names_Kleeneans; exists rep_K; try exact/rep_K_sur; apply/rep_K_sing.
  Defined.

  Canonical cs_Kleeneans:= Build_continuity_space Kleeneans_representation.

  Definition clean (phi: B_(cs_Kleeneans)) n := phi (ord_search (fun k => phi k) n).

  Lemma cln_mon phi n: clean phi n <> None -> clean phi n = clean phi n.+1.
  Proof.
    rewrite/clean osrchS.
    by case: ifP => //; case: (phi _).
  Qed.
    
  Lemma cln_rlzr_id: (F2MF clean) \realizes id.
  Proof.
    rewrite F2MF_rlzr => phi [[n [eq min]] | [n [eq min]] | prp]; last by case => [|n]; exact/prp.
    exists n; split => [ | m ineq].
    - rewrite /clean; suff <-: n = ord_search (fun k => phi k) n by trivial.
      by symmetry; apply/eqP/osrch_eqP => [[[m lt /=]]]; rewrite min //.
    suff /osrchP: ~ exists k, k <= m /\ phi k by rewrite /clean; case: (phi _) => //.
    case => k [leq val].
    suff: phi k = None by case: (phi _) val.
    by apply/min/leq_trans/ineq.
    exists n; split => [ | m ineq].
    - rewrite /clean; suff <-: n = ord_search (fun k => phi k) n by trivial.
      by symmetry; apply/eqP/osrch_eqP => [[[m lt /=]]]; rewrite min //.
    suff /osrchP: ~ exists k, k <= m /\ phi k by rewrite /clean; case: (phi _) => //.
    case => k [leq val].
    suff: phi k = None by case: (phi _) val.
    by apply/min/leq_trans/ineq.    
  Qed.

  Definition which := make_mf (fun (s1s2 : (Sirp * Sirp)) k => (s1s2.1 = top /\ k = true_K) \/ (s1s2.2 = top /\ k = false_K) \/ (s1s2.1 = bot /\ s1s2.2 = bot /\ k = bot_K)).

  Definition which_rlzrf (phi : (names_Sirp \*_ns names_Sirp)) n := match (lprj phi n) with
                                   | true => (Some true)
                                   | false =>
                                     match (rprj phi n) with
                                    | true => (Some false)
                                    | _ => None
                                     end
                                   end.

  Lemma which_spec xy : ((xy.1 = top) <-> (true_K \from (which (xy)))) /\ ((xy.2 = top) <-> (false_K \from (which (xy)))). 
  Proof.
  split;split; try by simpl;auto.
  rewrite /which /=.
  - case e : xy => [x y]; case x;case y;[case;case |case |case | ]; rewrite /=; try by auto.
    by case => [[H1 H2] | ]; [ | case => [[H1 H2] | [H1 [H2 H3]]]].
    by case => [[H1 H2] | ]; [ | case => [[H1 H2] | [H1 [H2 H3]]]].
  case e : xy => [x y]; case x;case y;[case;case |case |case | ]; rewrite /=; try by auto.
  by case => [[H1 H2] | ]; [ | case => [[H1 H2] | [H1 [H2 H3]]]].
  by case => [[H1 H2] | ]; [ | case => [[H1 H2] | [H1 [H2 H3]]]].
  Qed.

  Lemma dom_which : dom which === All.
  Proof.
    move => [s1 s2].
    split => [ | _] //.
    case e : s1 => [a |].
    - by case a; exists true_K;rewrite /=;auto.
    case e' : s2 => [a |].
    - by case a; exists false_K;rewrite /=;auto.
    by exists bot_K; rewrite /=;auto.
  Qed.
  Lemma which_rlzrf_spec : ((F2MF which_rlzrf) : (B_(cs_Sirp \*_cs cs_Sirp) ->> B_(cs_Kleeneans))) \solves which.
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
      rewrite /which_rlzrf mprp1; split => [ | m' m'prp]; first by auto.
      rewrite (mprp2 _ m'prp).
      have m'prp2 : (m' < n).
      apply /leP;move /leP : e; move /leP : m'prp.
      by lia.
      by rewrite (nprp2 _ m'prp2).
   exists false_K; split; first by auto.   
   exists n.
   rewrite /which_rlzrf nprp1 mprp2 ; last by (apply /leP; move /leP : e;lia).
   split => [ | n' n'prp]; first by auto.
   rewrite nprp2; last by (apply /leP; move /leP : n'prp;lia).
   rewrite mprp2 //.
   by apply /leP; move /ltP : n'prp; move /leP : e;lia.
  - move => _.
    exists true_K.
    split; first by auto.
    case (P1 kp1) => n [nprp1 nprp2].
    exists n; split => [| m mprp]; rewrite /which_rlzrf;first by rewrite nprp1.
    rewrite (nprp2 _ mprp).
    by rewrite (P2' kp2).
  - move => _.
    exists false_K.
    split; first by auto.
    case (P2 kp2) => n [nprp1 nprp2].
    exists n; split => [| m mprp]; rewrite /which_rlzrf; first by rewrite nprp1 (P1' kp1).
    by rewrite (P1' kp1) (nprp2 _ mprp).
  move => _.
  exists bot_K; split => [ | n ]; first by auto.
  by rewrite /which_rlzrf (P1' kp1) (P2' kp2).
Qed.

Definition which_rlzrf_mu (phi : (names_Sirp \*_ns names_Sirp)) (q : nat) : (seq (nat + nat)) := [:: (inl q);(inr q)].

Lemma which_rlzrf_mu_mod : which_rlzrf_mu \modulus_function_for which_rlzrf.
Proof.
  by rewrite /which_rlzrf_mu/which_rlzrf/lprj/rprj/= => phi q' psi [-> [-> _]] .
Qed.

Lemma which_rlzrf_mu_modmod : which_rlzrf_mu \modulus_function_for which_rlzrf_mu.
Proof.
by trivial.
Qed.
Definition K_truthf (K : Kleeneans) := match K with
                         | bot_K | false_K => bot
                         | top_K => top
                        end : Sirp.
Definition K_truth := (F2MF K_truthf).
Definition K_truth_rlzrf (phi : names_Kleeneans) :=  (fun n => (let m := ord_search (fun m => (isSome (phi m))) n in
                                                         if m == n 
                                                           then false
                                                            else
                                                                (match (phi m) with
                                                                   | (Some true) => true
                                                                   | _ => false
                                                                 end))) : names_Sirp.

Lemma K_truth_search_correct phi n : (K_truth_rlzrf phi n) = true <-> (ord_search (fun m => (isSome (phi m))) n) < n /\ (phi (ord_search (fun m => (isSome (phi m))) n)) = (Some true).
Proof.
  split.
  - move => H.
    case (PeanoNat.Nat.lt_trichotomy (ord_search (fun m => (isSome (phi m))) n) n); [| case] => H'; try by have /leP := (osrch_le (fun m => phi m) n);lia. 
    + split; first by apply /leP; lia.
      have P : ((ord_search (fun m => phi m) n) == n) = false by apply /eqP => p;move : H; rewrite /K_truth_rlzrf p eq_refl.
      move : H.
      rewrite /K_truth_rlzrf P.
      by case e  : (phi (ord_search (fun m => phi m) n)) => [b |]; try case e' : b.
    by rewrite /K_truth_rlzrf H' eq_refl in H.
  move => [H1 H2].
  rewrite /K_truth_rlzrf ifF; last by apply /eqP => p; move /leP: H1; rewrite p;lia.
  by rewrite H2.
Qed.


Lemma Ktruth_rlzr_spec : ((F2MF K_truth_rlzrf) : (B_(cs_Kleeneans) ->> B_(cs_Sirp))) \realizes K_truthf.
Proof.
  rewrite F2MF_rlzr => phi k phin /=.
  split.
  - case => n H.
    have [P _] := (K_truth_search_correct phi n).   
    have [P1 P2] := (P H).
    suff e : phi \is_description_of true_K by rewrite (rep_sing phin e).
    exists (ord_search (fun m => phi m) n); split => [| m /leP mprp]; first by auto.
    suff : not (isSome (phi m)) by case (phi m).
    move  => mprp'.
    have /leP := (@osrch_min (fun m => phi m) n m mprp').
    by lia.   
    move => H.
    move : phin.
    have -> : (k = true_K) by move : H;case k; auto.
    case => n [nprp1 nprp2].
    have nprp1' : (isSome (phi n)) by rewrite nprp1.
    exists n.+1.
    apply K_truth_search_correct.
    have /leP sm := (@osrch_min (fun m => phi m) (n.+1) n nprp1').
    split; first by apply /leP;lia.
    suff -> : (ord_search (fun m => phi m) n.+1) = n by auto.
    suff /leP: n <= (ord_search (fun m => phi m) n.+1) by lia.
    apply /leP;apply  PeanoNat.Nat.nlt_ge => /leP P.
    have := (nprp2 (ord_search (fun m => phi m) n.+1) P).
    have prp':= (@osrch_correct (fun m => phi m) n nprp1' ).
    rewrite osrchS.
    rewrite prp'.
    move : prp'.
    by case : (phi _).
Qed. 

Definition K_truth_mu (phi : nat -> (option bool)) n := init_seg (ord_search (fun m => (isSome (phi m))) n).+1.
Lemma coin_iseq_issome (phi : nat -> (option bool)) psi n: (phi \coincides_with psi \on (init_seg n.+1)) -> forall k, (k <= n)%nat -> (isSome (phi k)) = (isSome (psi k)).
Proof.
 elim n => [[coin _] k /leP kprp  | n' IH coin k /leP kprp].
 - have -> : (k = 0 ) by lia.
   by rewrite coin.
 case e: (k <= n').
 - apply IH => //.
   by apply coin.
  move /leP :  e => e.
 have -> : (k = n'.+1) by lia.
 by have [-> _]:= coin. 
Qed.

Lemma K_truth_mu_mod : K_truth_mu \modulus_function_for K_truth_rlzrf.
Proof.
  rewrite /K_truth_rlzrf => phi q psi coin.
  have [-> _] := coin.
  rewrite (osrch_cont (coin_iseq_issome coin)).
  by case ((ord_search (fun k => psi k) q) == q) => //.
Qed.

Lemma K_truth_mu_modmod : K_truth_mu \modulus_function_for K_truth_mu.
Proof.
  rewrite /K_truth_mu => phi n psi.
  elim n => // n' IH coin.
  f_equal.
  by rewrite (osrch_cont (coin_iseq_issome coin)).
Qed.

Definition B2K (b : bool) := match b with
                    | true => true_K
                    | false => false_K
                    end.

Definition K2B_rlzrM phi (un : nat * unit) := let m := (ord_search (fun m => (isSome (phi m))) un.1) in
                              match (phi m) with
                              | (Some true) => (Some true)
                              | (Some false) => (Some false)
                              | _ => None
                              end.

Definition K2B_mu (phi : nat -> (option bool)) (nq : (nat * (Q_(cs_bool)))) := init_seg (ord_search (fun m => (isSome (phi m))) nq.1).+1.

Lemma K2B_mu_mod : K2B_mu \modulus_function_for K2B_rlzrM.
Proof.
  rewrite /K2B_rlzrM => phi [n q] psi coin.
  have [-> _] := coin.
  rewrite (osrch_cont (coin_iseq_issome coin)).
  by case ((ord_search (fun k => psi k) n) == n) => //.
Qed.

Lemma K2B_mu_modmod : K2B_mu \modulus_function_for K2B_mu.
Proof.
  rewrite /K2B_mu => phi n psi.
  elim n => // n' IH coin.
  f_equal.
  by rewrite (osrch_cont (coin_iseq_issome coin)).
Qed.
Lemma F_K2B_rlzrM_spec : \F_K2B_rlzrM \solves ((F2MF B2K)\^-1).
Proof.
  move => /= phi k phin [b bp].
  split.
  - exists (fun u => b).
    case.
    move : phin.
    rewrite <- bp.
    rewrite /B2K/K2B_rlzrM.
    case b; case => n [nprp1 nprp2];exists n.
    + have nprp2' m : (m < n) -> ~ (isSome (phi m)) by move => H; rewrite (nprp2 m H).
      rewrite osrch_fail; last by move => m;apply (nprp2' m).
      by rewrite nprp1.
    have nprp2' m : (m < n) -> ~ (isSome (phi m)) by move => H; rewrite (nprp2 m H).
    rewrite osrch_fail; last by move => m;apply (nprp2' m).
    by rewrite nprp1.
  move => Fq.
  rewrite /K2B_rlzrM.
  move => H.
  suff H0 : (Fq tt) = b by exists b.
  move : phin.
  rewrite <- bp.
  rewrite /B2K.
  case b => H'; case (H tt) => n nprp; case H' => m [mprp1 mprp2].
  - have mprp2' m' : (m' < m) -> ~ (isSome (phi m')) by move => Hp; rewrite (mprp2 m' Hp).
    move : nprp.
    case e : (n < m).
    simpl;rewrite osrch_fail //.
    by rewrite (mprp2 n).
    move => m0 /=; apply  (mprp2' m0).
    apply /leP.
    have /leP : (m0 < n) by auto.
    move /leP : e.
    by lia.
    have mprp1' : (isSome (phi m)) by rewrite mprp1.
    have e' : (m <= n) by apply /leP; move /leP : e; lia.
    simpl.
    rewrite  <- (osrch_eq (@osrch_correct (fun m => (isSome (phi m))) m mprp1') e' ).
    rewrite osrch_fail.
    rewrite mprp1.
    by case (Fq tt).
    by move => m0; apply (mprp2' m0).
  - have mprp2' m' : (m' < m) -> ~ (isSome (phi m')) by move => Hp; rewrite (mprp2 m' Hp).
    move : nprp.
    case e : (n < m).
    simpl;rewrite osrch_fail //.
    by rewrite (mprp2 n).
    move => m0 /=; apply  (mprp2' m0).
    apply /leP.
    have /leP : (m0 < n) by auto.
    move /leP : e.
    by lia.
    have mprp1' : (isSome (phi m)) by rewrite mprp1.
    have e' : (m <= n) by apply /leP; move /leP : e; lia.
    simpl.
    rewrite  <- (osrch_eq (@osrch_correct (fun m => (isSome (phi m))) m mprp1') e' ).
    rewrite osrch_fail.
    rewrite mprp1.
    by case (Fq tt).
    by move => m0; apply (mprp2' m0).
Qed.

Lemma K2B_rlzrM_terms phi b : (phi \is_name_of (B2K b)) -> exists m, (K2B_rlzrM phi (m,tt)) = (Some b).
  move => phin.
  have := (F_K2B_rlzrM_spec phin).
  case; first by exists b.
  move => H.
  move => H'.
  case H => b' b'prp.
  case  (b'prp tt) => m mprp.
  exists m.
  suff <- : (b' tt) = b by auto.
  case (H' _ b'prp) => b'' /=.
  rewrite /B2K.
  by case b'';case b';case b; move => // [H1 H2].
Qed.

Lemma K2B_rlzrM_monotonic phi b m : (K2B_rlzrM phi (m, tt)) = (Some b) -> forall m', (m <= m')%coq_nat -> (K2B_rlzrM phi (m',tt)) = (Some b).
Proof.
  rewrite /K2B_rlzrM.
  move => /= H m' m'prp.
  suff <- : ((ord_search (fun m0 : nat => phi m0) m)) = ((ord_search (fun m0 : nat => phi m0) m')) by rewrite H.
  apply osrch_eq; last by apply /leP.
  by move : H;case e: (phi (ord_search (fun m0 : nat => phi m0) m)) => [b' | ] //; case b'.
Qed.

Lemma K2B_rlzrM_name (phi : B_(cs_Kleeneans)) m b : (K2B_rlzrM phi m) = (Some b) -> (phi \is_name_of (B2K b)).
Proof.
  - rewrite /K2B_rlzrM /B2K /=.
    case e :(phi (ord_search (fun m0 : nat => phi m0) m.1)) => [a | ]; try by auto.
    move : e.
    case a;case b => e; try by auto.
    exists (ord_search (fun m0 : nat => phi m0) m.1).
    rewrite e; split; try by auto.
    move => n nprp.
    case e' : (phi n) => [b'|]; try by auto.
    have t : (is_true (phi n)) by rewrite e'.
    have /leP := (@osrch_min (fun m0 => phi m0) m.1 n t).
    move /leP : nprp.
    by lia.
    exists (ord_search (fun m0 : nat => phi m0) m.1).
    rewrite e; split; try by auto.
    move => n nprp.
    case e' : (phi n) => [b'|]; try by auto.
    have t : (is_true (phi n)) by rewrite e'.
    have /leP := (@osrch_min (fun m0 => phi m0) m.1 n t).
    move /leP : nprp.
    by lia.
Qed.

End Kleeneans.

Section Open_subsets_of_nat.

  Lemma ON_iso_Sirpw : \O(cs_nat) ~=~ (cs_Sirp\^w).
  Proof. by rewrite sig_iso_fun; apply/iso_ref. Qed.
  Definition names_ON:= Build_naming_space 0 nat_count nat_count.

  Definition rep_ON := make_mf(fun (phi: names_ON) (p: pred nat) =>
                               forall n, p n <-> exists m, phi m = n.+1).

  Lemma rep_ON_sur: rep_ON \is_cototal.
  Proof.
    move => p/=.
    exists (fun n => if p n then n.+1 else 0) => n.
    split => [eq | [m]]; first by exists n; rewrite eq.
    by case E: (p m) => [|] => [[<-] | ].
  Qed.

  Lemma rep_ON_sing: rep_ON \is_singlevalued.
  Proof.
    move => phi A B phinA phinB.
    apply/fun_ext => n; have := phinA n; have <-:= phinB n.
    case: (A n); case: (B n) => // eq; last exact/eq.
    by symmetry; apply/eq.
  Qed.

  Canonical ON_representation: representation_of (pred nat).
    by exists names_ON; exists rep_ON; try exact/rep_ON_sur; apply/rep_ON_sing.
  Defined.

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

  Lemma rep_AN_sur: rep_AN \is_cototal.
  Proof.
    rewrite rep_AN_spec; apply/comp_cotot/rep_sur; first exact/(@rep_sing cs_ON).
    by rewrite -F2MF_cotot; apply/involutive_sur/complement_involutive.
  Qed.

  Lemma rep_AN_sing: rep_AN \is_singlevalued.
  Proof. by rewrite rep_AN_spec; apply/comp_sing/(@rep_sing cs_ON)/F2MF_sing. Qed.
    
  Definition AN_representation: representation_of (pred nat).
    by exists names_AN; exists rep_AN; try exact/rep_AN_sur; apply/rep_AN_sing.
  Defined.

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
  
