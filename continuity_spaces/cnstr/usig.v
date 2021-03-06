From mathcomp Require Import ssreflect ssrfun seq ssrnat.
Require Import classical_count classical_cont classical_mach classical_func all_cs_base dscrt.
Require Import FunctionalExtensionality ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section USIGPROD.
Definition rep_usig_prod (X: cs) := make_mf
(fun phi (xn: nat -> X) => forall n, (fun p => (phi (n,p))) \is_description_of (xn n)).

Lemma rep_usig_prod_sur (X: cs): (@rep_usig_prod X) \is_cototal.
Proof.
move => xn.
pose R n phi:= phi \is_description_of (xn n).
have [ | phi phiprp]:= choice R; last by exists (fun p => phi p.1 p.2).
by move => n; have [phi phinx]:= (get_description (xn n)); exists phi.
Qed.

Definition cs_usig_interview_mixin (X: cs):
	interview_mixin.type (nat * (questions X) -> answers X) (nat -> X).
Proof. exists (rep_usig_prod X); exact/rep_usig_prod_sur. Defined.

Lemma rep_usig_prod_sing (X: cs): (@rep_usig_prod X) \is_singlevalued.
Proof.
move => phi xn yn phinxn phinyn.
apply functional_extensionality => n.
by apply/ (rep_sing); [apply phinxn | apply phinyn ].
Qed.

Definition cs_usig_dictionary_mixin (X: cs):
	dictionary_mixin.type (interview.Pack (cs_usig_interview_mixin X)).
Proof. split; exact/rep_usig_prod_sing. Defined.

Canonical cs_sig_prod (X: cs) := @continuity_space.Pack
	(nat * questions X)
	(answers X)
	((0%nat, someq X))
	(somea X)
  (prod_count nat_count (questions_countable X))
  (answers_countable X)
  (dictionary.Pack (cs_usig_dictionary_mixin X)).

Notation "X '\^w'" := (cs_sig_prod X) (at level 35, format "X '\^w'").

Lemma sigprd_base (X: cs) (an: X\^w) (phi: names (cs_sig_prod X)):
	phi \is_description_of an <-> forall n, (fun q => phi (n,q)) \is_description_of (an n).
Proof. done. Qed.

Definition ptw (X: cs) (op: X * X -> X) (fg: (nat -> X) * (nat -> X)) :=
	(fun n => op (fg.1 n, fg.2 n)).

Lemma ptw_cont X (op: X \*_cs X -> X): op \is_continuous ->
	(ptw op: X\^w \*_cs X\^w -> X\^w) \is_continuous.
Proof.
move => [F [/rlzr_F2MF Frop Fcont]].
pose np := (@name_pair X X: names X -> names X -> names (X \*_cs X)).
exists (make_mf (fun (phi: names (cs_sig_prod _ \*_cs cs_sig_prod _)) psi => forall n,
	F (np (fun q => lprj phi (n, q)) (fun q => rprj phi (n, q))) (fun q => psi (n, q)))).
split.
	rewrite rlzr_F2MF => phi [xn yn] [/=phinxn phinyn].
	have nms n: (np (fun q : questions X => lprj phi (n, q))
		(fun q : questions X => rprj phi (n, q))) \is_description_of ((xn n, yn n): cs_prod X X).
		by split => /=; [apply/phinxn | apply/phinyn].
	split => [ | psi FpsiFpsi n].
		have fd n:= (Frop (np (fun q => lprj phi (n, q))
			(fun q => rprj phi (n, q))) (xn n, yn n) (nms n)).1.
		have [Fphi Fphiprp]:= choice _ fd.
		by exists (fun nq => Fphi nq.1 nq.2) => n /=; apply Fphiprp.
	have val n:= (Frop (np (fun q => lprj phi (n, q))
		(fun q => rprj phi (n, q))) (xn n, yn n) (nms n)).2.
	by rewrite /ptw/=; apply/val.
apply cont_choice => phi Fphi /=FphiFphi [n q].
pose phin:= np (fun q => lprj phi (n, q)) (fun q => rprj phi (n, q)).
have [ | Lf mod]:= Fcont phin (fun q' => Fphi (n, q')); first exact/FphiFphi.
exists (map (fun q' => match q' with
	| inl q'' => inl (n, q'')
	| inr q'' => inr (n, q'')
	end) (Lf q)) => psi /coin_lstn coin Fpsi eq.
apply/(mod q (fun q' => match q' with
	| inl q'' => ((psi (inl (n, q''))).1, somea _)
	| inr q'' => (somea _, (psi (inr (n, q''))).2)
end) _ (fun q => Fpsi (n, q))); last by apply eq.
apply/coin_lstn => [[q' | q'] lstn].
	rewrite /phin/= -(coin (inl (n,q'))) /lprj//.
	by elim: (Lf q) lstn => // a L ih /= [ -> | ]; [left | right; apply/ih].
rewrite /phin/= -(coin (inr (n,q'))) /rprj//.
by elim: (Lf q) lstn => // a L ih /= [ -> | ]; [left | right; apply/ih].
Qed.
End USIGPROD.
Notation "X '\^w'" := (cs_sig_prod X) (at level 35, format "X '\^w'").

Section isomorphism.
Definition sig2fun (X: cs) (f: X\^w) := exist_c (nat_dscrt f): cs_nat c-> X.

Definition sig2fun_rlzrf (X: cs) (phi: names (X\^w)) Lq' := match Lq'.1 with
	| nil => inl [:: tt]
	| (n :: L) => inr (phi (n, Lq'.2))
end.

Definition sig2fun_rlzr (X: cs) := F2MF (@sig2fun_rlzrf X).

Lemma sig2fun_rlzr_spec (X: cs): (@sig2fun_rlzr X) \realizes (F2MF (@sig2fun X)).
Proof.
rewrite F2MF_rlzr_F2MF => phi xn phinxn.
rewrite /= rlzr_F2MF => nf /= n eq.
split; first by exists (fun q => phi (n, q)) => q'; exists 2; rewrite /U/= eq.
move => psi val.
suff <-: (fun q => phi (n, q)) = psi by apply/phinxn.
apply/functional_extensionality => q.
have [m eq']:= val q; case: m eq' => //m; case: m => //m.
have ->: U (sig2fun_rlzrf phi) m.+2 nf q = U (sig2fun_rlzrf phi) 2 nf q.
- elim: m => // m; rewrite -addn1 -addn1 /U /=.
  by case: (U_rec (sig2fun_rlzrf phi) (m + 1 + 1) nf q).
by rewrite /U/= eq => [[]].
Qed.

Lemma sig2fun_rlzr_cntop (X: cs): (@sig2fun_rlzr X) \is_continuous_operator.
Proof.
rewrite F2MF_cont_choice => phi Lq'.
case E: Lq'.1 => [ | n L]; first by exists [::] => psi _; rewrite /sig2fun_rlzrf E.
by exists ([:: (n, Lq'.2)]); rewrite /sig2fun_rlzrf E => psi [->].
Qed.

Lemma sig2fun_cont (X: cs): (@sig2fun X) \is_continuous.
Proof.
by exists (@sig2fun_rlzr X); split; [apply/sig2fun_rlzr_spec | apply/sig2fun_rlzr_cntop].
Qed.

Definition fun2sig (X: cs) (xn: cs_nat c-> X):= projT1 xn: X\^w.

Definition fun2sig_rlzr X:= make_mf (fun (psi: names cs_nat c-> X) phi =>
	forall n, \F_(U psi) (fun _ => n) (fun q => phi (n, q))).

Lemma fun2sig_rlzr_spec X: (@fun2sig_rlzr X) \realizes (F2MF (@fun2sig X)).
Proof.
rewrite rlzr_F2MF => psi xn /rlzr_F2MF rlzr.
split => [ | phin Fpsiphi n].
	have prp: forall (n: nat), exists phi: questions X -> answers X, forall q,
  exists c : nat, U psi c (fun _ : unit => n) q = Some (phi q).
  	move => n.
  	have [ | [phi val prp]]//:= rlzr (fun _ => n) n.
  	exists phi => q; apply/val.
  have [phin nm]:= choice _ prp.
  exists (fun nq => phin nq.1 nq.2).
  move => n q /=; apply nm.
have [ | [phi val prp]]//:= rlzr (fun _ => n) n.
apply/prp => q.
apply/Fpsiphi.
Qed.

Lemma fun2sig_rlzr_cntop X: (@fun2sig_rlzr X) \is_continuous_operator.
Proof.
apply/cont_choice.
rewrite /fun2sig_rlzr => psi phi Fpsiphi [n q'].
have [ | mf mod]:= @FM_val_cont _ _ _ _ (fun _ => n) psi (fun q => phi (n, q)); first exact/(Fpsiphi n).
exists (mf q') => psi' coin Fpsi' val.
exact/(mod q' psi' coin (fun q => Fpsi' (n, q)))/val.
Qed.

Lemma fun2sig_cont X: (@fun2sig X) \is_continuous.
Proof.
exists (fun2sig_rlzr X); split; [exact/fun2sig_rlzr_spec | exact/fun2sig_rlzr_cntop].
Qed.

Lemma sig_iso_fun X: X\^w ~=~ (cs_nat c-> X).
Proof.
exists (exist_c (sig2fun_cont X)).
exists (exist_c (fun2sig_cont X)).
by split => [f | f]; last apply/eq_sub; apply functional_extensionality => n /=.
Qed.
End isomorphism.