From mathcomp Require Import all_ssreflect.
Require Import all_cs_base classical_mach cs_nat.
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

Lemma usig_base (X: cs) (an: cs_sig_prod X) (phi: names (cs_sig_prod X)):
	phi \is_description_of an -> forall n, (fun q => phi (n,q)) \is_description_of (an n).
Proof. done. Qed.

Definition ptw (X: cs) (op: X * X -> X) (fg: (nat -> X) * (nat -> X)) :=
	(fun n => op (fg.1 n, fg.2 n)).

(*
Lemma ptw_cont X (op: X \*_cs X -> X): op \is_continuous ->
	(ptw op: cs_sig_prod _ \*_cs cs_sig_prod _ -> cs_sig_prod _) \is_continuous.
Proof.
move => [F [Frop Fcont]]; rewrite /continuous/hcr.
exists (fun phi psi => forall q,
	F (name_pair (fun q' => lprj phi (q, q')) (fun q' => rprj phi (q, q'))) (psi q)).
abstract by move => phi [an bn] [/=phinan phinbn] n/=; rewrite /ptw/=;
	apply ((Mprop (name_pair (fun q' => lprj phi (n, q')) (fun q' => rprj phi (n, q')))) (an n, bn n));
	split; rewrite rprj_pair lprj_pair/=; [apply phinan | apply phinbn].
Defined.

Lemma sig_iso_fun X:
	(cs_sig_prod X) ~=~ (cs_nat c-> X).
Proof.
have crlzr: forall xn: nat -> X, hcr (F2MF xn).
	move => xn.
	pose R phi psi := psi \is_name_of (xn (phi star)).
	have Rtot: R \is_total by move => phi; apply (rep_sur X).
	have [F icf]:= choice R Rtot.
	exists F; split.
		by apply rlzr_mfrlzr => phi x phinx; rewrite -phinx; apply/icf.
	move => phi q phifd; exists ([::star]) => Fphi /= FphiFphi psi coin.
	have eq: phi = psi.
		by apply functional_extensionality => /= str; elim: str; apply coin.
	by rewrite -eq => Fpsi FpsiFpsi; rewrite -FpsiFpsi -FphiFphi.
Admitted. *)
End USIGPROD.