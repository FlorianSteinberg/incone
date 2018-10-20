From mathcomp Require Import all_ssreflect.
Require Import all_cs_base.
Require Import FunctionalExtensionality ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section USIGPROD.
Definition rep_usig_prod (X: cs) := make_mf
(fun phi (xn: nat -> X) => forall n, (fun p => (phi (n,p))) \is_name_of (xn n)).

Lemma rep_usig_prod_sur (X: cs): (@rep_usig_prod X) \is_cototal.
Proof.
move => xn.
pose R n phi:= phi \is_name_of (xn n).
have [ | phi phiprp]:= choice R; last by exists (fun p => phi p.1 p.2).
by move => n; have [phi phinx]:= (get_name (xn n)); exists phi.
Qed.

Definition cs_usig_assembly_mixin (X: cs):
	interview_mixin.type (nat * (questions X) -> answers X) (nat -> X).
Proof. exists (rep_usig_prod X); exact/rep_usig_prod_sur. Defined.

Lemma rep_usig_prod_sing (X: cs): (@rep_usig_prod X) \is_singlevalued.
Proof.
move => phi xn yn phinxn phinyn.
apply functional_extensionality => n.
by apply/ (rep_sing); [apply phinxn | apply phinyn ].
Qed.

Definition cs_usig_modest_set_mixin (X: cs):
	dictionary_mixin.type (interview.Pack (cs_usig_assembly_mixin X)).
Proof. split; exact/rep_usig_prod_sing. Defined.

Canonical cs_usig_prod (X: cs) := @cs.Pack
	(nat * questions X)
	(answers X)
	((0%nat, someq X))
	(somea X)
  (prod_count nat_count (cs.Qcount X))
  (cs.Acount X)
  (dictionary.Pack (cs_usig_modest_set_mixin X)).

Lemma usig_base (X: cs) (an: nat -> X) (phi: names (cs_usig_prod X)):
	phi \is_name_of an -> forall n, (fun q => phi (n,q)) \is_name_of (an n).
Proof. done. Qed.

Definition ptw (X: cs) (op: X * X -> X) (fg: (nat -> X) * (nat -> X)) :=
	(fun n => op (fg.1 n, fg.2 n)).

(*
Lemma ptw_rec X (op: rep_space_prod X X -> X):
	op \is_recursive_function -> (ptw op) \is_recursive_function.
Proof.
move => [Mop Mprop].
exists (fun (phi: names (rep_space_prod (rep_space_usig_prod X)(rep_space_usig_prod X))) q =>
	Mop (name_pair (fun q' => lprj phi (q.1, q')) (fun q' => rprj phi (q.1, q'))) q.2).
abstract by move => phi [an bn] [/=phinan phinbn] n/=; rewrite /ptw/=;
	apply ((Mprop (name_pair (fun q' => lprj phi (n, q')) (fun q' => rprj phi (n, q')))) (an n, bn n));
	split; rewrite rprj_pair lprj_pair/=; [apply phinan | apply phinbn].
Defined.

Lemma wiso_usig X:
	wisomorphic (rep_space_usig_prod X) (rep_space_cont_fun rep_space_nat X).
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