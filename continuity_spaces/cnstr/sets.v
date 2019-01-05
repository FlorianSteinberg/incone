From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_rlzrs.
Require Import all_cs_base classical_func dscrt cprd.
Require Import Classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SIERPINSKISPACE.
Inductive Sirp := top | bot.

Definition rep_Sirp := make_mf (fun phi s => (exists n:nat, phi n = true) <-> s = top).

Lemma rep_Sirp_sur: rep_Sirp \is_cototal.
Proof.
case; first by exists (fun _ => true); split => // _; exists 0.
by exists (fun _ => false); split => //; case.
Qed.

Lemma rep_Sirp_sing: rep_Sirp \is_singlevalued.
Proof.
move => phi s s' [imp imp'] [pmi pmi'].
case: s imp imp' => [_ []// n val | prp _]; first by case: s' pmi pmi' => [_ []// | -> //]; exists n.
by case: s' pmi pmi' => // _[]// n val; apply prp; exists n.
Qed.

Canonical cs_Sirp_class:= @continuity_space.Class _ _ _
  (interview.Mixin rep_Sirp_sur) (dictionary.Mixin rep_Sirp_sing)
  (continuity_space.Mixin 0%nat false nat_count bool_count).

Canonical cs_Sirp:= continuity_space.Pack cs_Sirp_class.
End SIERPINSKISPACE.

Section Kleeneans.
Inductive Kleeneans := false_K | true_K | bot_K.

Definition rep_K := make_mf (fun phi (t: Kleeneans) =>
	match t with
		| false_K => exists (n: nat), phi n = Some false /\ forall m, m < n -> phi m = None
		| true_K => exists (n: nat), phi n = Some true /\ forall m, m < n -> phi m = None
		| bot_K => forall n, phi n = None
	end).

Lemma rep_K_sur: rep_K \is_cototal.
Proof.
by case; [exists (fun _ => Some false) | exists (fun _ => Some true) | exists (fun _ => None)]; try exists 0.
Qed.

Lemma rep_K_sing: rep_K \is_singlevalued.
Proof.
move => phi t t'.
case: t; case t' => //; try (move => [n [eq prp]] prp'; by rewrite prp' in eq);
  try (move => prp; case => n []; by rewrite prp); move => [n [eq prp]] [m []].
- case/orP: (leq_total m n) => ineq; rewrite leq_eqVlt in ineq.
  - by case/orP: ineq => [/eqP -> | ineq]; [rewrite eq | rewrite prp].
  by case/orP: ineq => [/eqP <- | ineq eq' prp']; [rewrite eq | rewrite prp' in eq].
case/orP: (leq_total m n) => ineq; rewrite leq_eqVlt in ineq.
- by case/orP: ineq => [/eqP -> | ineq]; [rewrite eq | rewrite prp].
by case/orP: ineq => [/eqP <- | ineq eq' prp']; [rewrite eq | rewrite prp' in eq].
Qed.

Canonical cs_Kleeneans_class:= @continuity_space.Class _ _ _
  (interview.Mixin rep_K_sur) (dictionary.Mixin rep_K_sing)
  (continuity_space.Mixin 0%nat None nat_count (option_count bool_count)).
Canonical cs_Kleeneans:= continuity_space.Pack cs_Kleeneans_class.
End Kleeneans.

Section Opens.
  Definition opens (X: cs):= X c-> cs_Sirp.
  Notation "\O( X )" := (opens X) (at level 2, format "'\O(' X ')'").
  
  Definition OO_fun (X: cs) (x: X) := (point_evaluation cs_Sirp x) : \O(\O(X)).

  Lemma OO_fun_cont (X: cs): (@OO_fun X) \is_continuous.
  Proof. exact/ptvl_cont. Qed.  
  
  Definition admissible (X: cs) := F2MF (@OO_fun X)\^-1 \has_continuous_realizer.

  Lemma ON_iso_Sirpw : \O(cs_nat) ~=~ (cs_Sirp\^w).
  Proof. by rewrite/opens sig_iso_fun; apply iso_ref. Qed.

  Definition O2SS X (O: \O(X)) := make_subset (fun x => projT1 O x = top).

  Lemma all_open X: exists (O: \O(X)), (O2SS O) === All.
  Proof.
    suff cont: (fun (_: X) => top: cs_Sirp) \is_continuous by exists (exist_c cont).
    exists (F2MF (fun phi q => true)).  
    by split; [apply/F2MF_rlzr_F2MF; split => //; exists 0 | rewrite cont_F2MF; apply cnst_cont].
  Qed.

  Lemma empty_open X: exists (O: \O(X)), (O2SS O) === empty.
  Proof.
    suff cont: (fun (_: X) => bot: cs_Sirp) \is_continuous by exists (exist_c cont).
    exists (F2MF (fun phi q => false)).  
    by split; [apply/F2MF_rlzr_F2MF; split => [[] | ] | rewrite cont_F2MF; apply cnst_cont].
  Qed.
End Opens.
Notation "\O( X )" := (opens X) (at level 2, format "'\O(' X ')'").

Section Closeds.  
  Definition complement X (A: X -> Sirp) x :=
    match A x with
    | top => bot
    | bot => top
    end.

  Arguments complement {X}.
  Lemma complement_involutive X: involutive (@complement X).
  Proof.
    move => A; rewrite /complement.
    apply/functional_extensionality => x.  
    by case: (A x).
  Qed.

  Definition closeds (X: cs):= make_subset (fun (A: X -> cs_Sirp) =>
                                              (complement A) \is_continuous).

  Lemma clos_open (X: cs) A: A \from (closeds X) <-> exists (O: \O(X)), projT1 O = complement A.
  Proof. by split => [cont | [[O /ass_cont Ocont/=] <-]]; first by exists (exist_c cont). Qed.

  Definition rep_clsd X := make_mf (fun phi (A: closeds X) =>
                                      associate X cs_Sirp phi (complement (projT1 A))).

  Lemma rep_clsd_sur X: (@rep_clsd X) \is_cototal.
  Proof. by move => [A /ass_cont [psi ass]/=]; exists psi. Qed.
  
  Lemma rep_clsd_sing X: (@rep_clsd X) \is_singlevalued.
  Proof.
    move => phi A A' /= phinA phinA'; apply/eq_sub => /=.
    rewrite -(complement_involutive (sval A)) -(complement_involutive (sval A')).
    by have ->:= choice_dict.mf_rlzr_f_sing phinA phinA'.
  Qed.  

  Definition cs_closeds X := make_cs (someq \O(X))
                                     (somea \O(X))
                                     (Q_count \O(X))
                                     (A_count \O(X))
                                     (@rep_clsd_sur X)
                                     (@rep_clsd_sing X).

  Local Notation "\A( X )" := (cs_closeds X) (at level 2, format "'\A(' X ')'").

  Lemma complement_closed X (O: \O(X)): complement (sval O) \from closeds X.
  Proof. by move: O => [O /ass_cont /=]; rewrite complement_involutive. Qed.

  Definition complement_opens X (O: \O(X)): \A(X) := exist _ _ (complement_closed O).

  Lemma cmplO_cont X: (@complement_opens X) \is_continuous.
  Proof.
    exists mf_id.
    split; last by apply /cont_F2MF => phi; exists (fun n => [:: n]) => q' psi [].
    apply/F2MF_rlzr_F2MF => psi O psinO phi x phinx fd.
    have [ | dm prp]:= psinO phi x phinx; first by exists (sval O x).
    split => // Fphi val.
    have [s [Fphins /= eq]]:= prp Fphi val.
    exists s; split => //=; rewrite -eq.
    by rewrite complement_involutive.
  Qed.

  Lemma complement_open X (A: \A(X)): (complement (sval A)) \is_continuous.
  Proof. by case: A. Qed.

  Definition complement_closeds X (A: \A(X)): \O(X) := exist_c (complement_open A).
  
  Lemma cmplA_cont X: (@complement_closeds X) \is_continuous.
  Proof.
    exists mf_id.
    split; last by apply/cont_F2MF => phi; exists (fun n => [:: n]) => q' psi [].
    apply/F2MF_rlzr_F2MF => psi A psinA phi x phinx fd.
    by have [ | dm prp]:= psinA phi x phinx; first by exists (complement (sval A) x).
  Qed.
  
  Lemma clsd_iso_open X: \O(X) ~=~ \A(X).
  Proof.
    exists (exist_c (cmplO_cont X)).
    exists (exist_c (cmplA_cont X)).
    by split => O; apply/eq_sub/complement_involutive.
  Qed.

  Definition A2SS X (f: \A(X)) := make_subset (fun x => projT1 f x = top).

  Lemma all_closed X: exists (A: \A(X)), (A2SS A) === All.
  Proof.  
    have [A eq]:= empty_open X.
    exists (complement_opens A) => x; split => // _ /=.
    rewrite /complement.
    have [/=]:= eq x.
    by case: (sval A x).
  Qed.

  Lemma empty_closed X: exists (A: \A(X)), (A2SS A) === empty.
  Proof.
    have [A eq]:= all_open X.
    exists (complement_opens A) => x; split => //=.
    rewrite /complement; have /=[]:= eq x; case: (sval A x) => // _ prp _.
    by have: bot = top by apply/prp.
  Qed.
End Closeds.
Notation "\A( X )" := (cs_closeds X) (at level 2, format "'\A(' X ')'").
Arguments complement {X}.

Section Open_subsets_of_nat.  
  Definition rep_ON := make_mf(fun (phi: nat -> nat) (A: nat -> Sirp) =>
                               forall n, A n = top <-> exists m, phi m = n.+1).

  Lemma rep_ON_sur: rep_ON \is_cototal.
  Proof.
    move => A /=.
    exists (fun n => if A n is top then n.+1 else 0) => n.
    split => [eq | [m]]; first by exists n; rewrite eq.
    by case E: (A m) => [] => [[<-] | ].
  Qed.

  Lemma rep_ON_sing: rep_ON \is_singlevalued.
  Proof.
    move => phi A B phinA phinB.
    apply/functional_extensionality => n.
    have := phinA n.
    have <-:= phinB n.
    case: (A n); case: (B n) => // eq; last exact/eq.
    by symmetry; apply/eq.
  Qed.

  Definition cs_ON := make_cs 0%nat 0%nat nat_count nat_count rep_ON_sur rep_ON_sing.

  Definition ON2Sw_rlzrf (phi: nat -> nat) (nm: nat * nat):= ((phi nm.2) == nm.1.+1).

  Definition ON2Sw_rlzr:= F2MF ON2Sw_rlzrf: names cs_ON ->> names (cs_Sirp\^w).

  Lemma ON2Sw_rlzr_spec:
    ON2Sw_rlzr \realizes mf_id.
  Proof.
    apply/F2MF_rlzr_F2MF => phi A phinA n.
    have := phinA n.
    case: (A n).
    - case => [[]// m /eqP eq _].
      split => // _; exists m; rewrite /ON2Sw_rlzrf /=.
      by rewrite eq.
    case => [_ prp].
    rewrite /ON2Sw_rlzrf /=.
    split => // [[m /= /eqP eq]].
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

  Definition Sw2ON_rlzr:= F2MF Sw2ON_rlzrf : names (cs_Sirp\^w) ->> names cs_ON.
  
  Lemma Sw2ON_rlzr_spec:
    Sw2ON_rlzr \realizes mf_id.
  Proof.
    rewrite F2MF_rlzr_F2MF => phi A phinA n.
    have := phinA n.
    case: (A n).
    - case => [_ []// m eq]; split => // _.
      exists (pickle (n, m)).
      by rewrite /Sw2ON_rlzrf pickleK eq.
    case => prp _; rewrite /Sw2ON_rlzrf; split => // [[m]].
    case: (unpickle m) => // [[m' k]] eq.
    by apply/prp; exists k; move: eq; case: ifP => // pr [<-].
  Qed.

  Lemma Sw2AN_rlzr_cntop: Sw2ON_rlzr \is_continuous_operator.
  Proof.
    apply/cont_F2MF => phi /=.
    exists (fun n => match unpickle n with | None => nil | Some nm => [:: nm] end).
    move => n psi; rewrite /Sw2ON_rlzrf.
    by case: (unpickle n) => // nm [->].
  Qed.  
 
  Lemma ON2Sw_cont: (id: cs_ON -> cs_Sirp\^w) \is_continuous.
  Proof. by exists ON2Sw_rlzr; split; [apply/ON2Sw_rlzr_spec | apply/ON2Sw_rlzr_cntop]. Qed.

  Lemma Sw2ON_cont: (id: cs_Sirp\^w -> cs_ON) \is_continuous. 
  Proof. by exists Sw2ON_rlzr; split; [apply/Sw2ON_rlzr_spec | apply/Sw2AN_rlzr_cntop]. Qed.

  Lemma ON_iso_Sw: cs_ON ~=~ (cs_Sirp\^w).
  Proof. by exists (exist_c ON2Sw_cont); exists (exist_c Sw2ON_cont). Qed.

  Lemma ON_iso_Onat: cs_ON ~=~ \O(cs_nat).
  Proof. by rewrite ON_iso_Sw; apply/sig_iso_fun. Qed.
End Open_subsets_of_nat.

Section Closed_subsets_of_nat.
  Definition rep_AN := make_mf(fun (phi: nat -> nat) (A: nat -> Sirp) =>
                                 forall n, A n = bot <-> exists m, phi m = n.+1).

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
    rewrite rep_AN_spec; apply/comp_cotot/rep_ON_sur; first exact/rep_ON_sing.
    by rewrite -F2MF_cotot; apply/involutive_sur/complement_involutive.
  Qed.

  Lemma rep_AN_sing: rep_AN \is_singlevalued.
  Proof. by rewrite rep_AN_spec; apply/comp_sing/rep_ON_sing/F2MF_sing. Qed.
  
  Definition cs_AN:= make_cs 0 0 nat_count nat_count rep_AN_sur rep_AN_sing.  

  Lemma id_cntop Q A: (@mf_id (Q -> A)) \is_continuous_operator.
  Proof. by apply/cont_F2MF => phi; exists (fun n => [:: n]) => q psi []. Qed.

  Lemma cmpl_cont: (complement: cs_AN -> cs_ON) \is_continuous.
  Proof.
    exists mf_id; split; last exact/id_cntop.
    apply/F2MF_rlzr_F2MF => phi A /rep_AN_spec [[cA [phincA <-]] _].
    by rewrite complement_involutive.
  Qed.

  Lemma cont_cmpl: (complement: cs_ON -> cs_AN) \is_continuous.
  Proof.
    exists mf_id; split; last exact/id_cntop.
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
End Closed_subsets_of_nat.