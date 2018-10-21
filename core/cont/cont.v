(* This file provides a definition of continuity of functions between spaces of the form
Q -> A for some arbitrary types Q and A. It also proves some basic Lemmas about this notion.*)
From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mpf.
Require Import baire.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section continuity.
Context (Q A Q' A' : Type).
(* Q is for questions, A is for answers*)
Notation B := (Q -> A).
Notation B' := (Q' -> A').
(* B is for Baire space. *)
Context (F: B ->> B').

Definition determines phi q' a' := forall Fphi, F phi Fphi -> a' = Fphi q'.

Definition cert L phi q' a' :=
	forall psi, phi \and psi \coincide_on L -> determines psi q' a'.
(* cert is for certificate and cert L phi q' a' means that the values of phi on the list L
is enough to determine the return value a' on input q'. *)

Definition modulus mf := forall phi Fphi, F phi Fphi -> forall q', cert (mf phi q') phi q' (Fphi q').

Definition continuous := exists mf, modulus mf.

Lemma det_sing:
	(forall phi, phi \from dom F -> forall q', exists a', determines phi q' a') <-> F \is_singlevalued.
Proof.
split => [detall | sing].
	move => phi Fphi Fphi' FphiFphi FphiFphi'.
	apply functional_extensionality => q'.
	have [ | a' det] := (detall phi _ q'); first by exists Fphi.
	by rewrite -(det Fphi); first rewrite -(det Fphi').
move => phi [Fphi FphiFphi] q'.
exists (Fphi q') => Fphi' FphiFphi'.
by rewrite (sing phi Fphi Fphi').
Qed.

Lemma cert_det phi q' a':
	(exists L, cert L phi q' a') -> determines phi q' a'.
Proof. by move => [L crt elg]; apply/crt/coin_ref. Qed.

Lemma cert_subl L K phi q' a':
	L \is_sublist_of K -> cert L phi q' a' -> cert K phi q' a'.
Proof. by move => subl det psi coin; apply: det; apply (coin_subl subl). Qed.

Lemma cert_c L phi psi q' a':
	phi \and psi \coincide_on L -> cert L phi q' a' -> cert L psi q' a'.
Proof.
by move => coin det psi' coin'; apply/(det psi'); first exact/(coin_trans coin coin').
Qed.

Definition eligible phi q' a' := exists Fphi, F phi Fphi /\ a' = Fphi q'.

Lemma dom_elig:
	F \is_total -> forall phi q', exists a', eligible phi q' a'.
Proof.
move => tot phi q'; have [Fphi FphiFphi]:= tot phi.
by exists (Fphi q'); exists Fphi.
Qed.

Lemma elig_dom:
	inhabited Q' -> F \is_total <-> forall phi q', exists a', eligible phi q' a'.
Proof.
move => [q']; split; first exact dom_elig; move => eligall phi.
by have [_ [Fphi [FphiFphi _]]]:= eligall phi q'; exists Fphi.
Qed.
End continuity.
Notation "mf '\is_modulus_of' F" := (modulus F mf) (at level 2).
Notation "F '\is_continuous'" := (continuous F) (at level 2).

Section continuity_lemmas.
Context (Q A Q' A' : Type).
Notation B := (Q -> A).
Notation B' := (Q' -> A').

Lemma det_exte (F G: B ->> B') phi q' a':
	G \extends F -> determines G phi q' a' -> determines F phi q' a'.
Proof.
move => GeF det Fpsi FpsiFpsi.
by apply det; apply GeF.
Qed.

Lemma det_restr P (F: B ->> B') phi q' a':
	determines (F \restricted_to P) phi q' a' <-> (P phi -> determines F phi q' a').
Proof.
split; first by move => det Pphi Fphi val; apply det.
by move => prop Fphi [] Pphi; apply: (prop Pphi).
Qed.

Lemma cert_exte (F G: B ->> B') L phi q' a':
	G \extends F -> cert G L phi q' a' -> cert F L phi q' a'.
Proof. by move => GeF certi psi coin; apply/ det_exte; [apply GeF | apply certi]. Qed.

Lemma elig_exte (F G: B ->> B') phi q' a':
	F \extends G -> eligible G phi q' a' -> eligible F phi q' a'.
Proof.
move => GeF [] Gphi [] GphiGphi eq.
by exists Gphi; split => //; apply/ GeF.
Qed.

Lemma elig_restr P (F: B ->> B') phi q' a':
	eligible (F \restricted_to P) phi q' a' -> P phi /\ eligible F phi q' a'.
Proof. by move => [] Fphi [] []; split => //; exists Fphi. Qed.

Lemma restr_elig (P: mf_subset.type B) (F: B ->> B') phi q' a':
	P phi -> eligible F phi q' a' -> eligible (F \restricted_to P) phi q' a'.
Proof. by move => Pphi [] Fphi []; exists Fphi. Qed.

Lemma cont_sing (F: B ->> B'):
	F \is_continuous -> F \is_singlevalued.
Proof.
move => [mf mod]; apply det_sing => phi [Fphi FphiFphi] q'.
by exists (Fphi q'); apply/mod/coin_ref.
Qed.

Lemma cont_exte (F G: B ->> B'):
	G \tightens F -> G \is_continuous -> F \is_singlevalued -> F \is_continuous.
Proof.
move => /sing_tight_exte exte [mf mod] sing.
exists mf => phi Fphi FphiFphi q'.
by apply/cert_exte/mod/exte; first apply/exte.
Qed.

Lemma cnst_cont (Fphi: B'):
	(F2MF (fun phi: B => Fphi)) \is_continuous.
Proof. by exists (fun phi q' => nil) => phi _ <- q' _ _ _ <-. Qed.
End continuity_lemmas.