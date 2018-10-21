From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mpf.
Require Import cont ptw_cont.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section closures.
Context (Q A : Type).
Notation B := (Q -> A).

Definition closure (P: mf_subset.type B):=
	make_subset (fun phi => forall L, exists psi, phi \and psi \coincide_on L /\ P psi).

Lemma subs_clos P: P \is_subset_of (closure P).
Proof. by move => phi; exists phi; split => //; apply: coin_ref. Qed.
Arguments subs_clos (P) : clear implicits.

Lemma clos_subs P P': P \is_subset_of P' -> (closure P) \is_subset_of (closure P').
Proof.
move => subs phi cPphi L; have [psi []]:= cPphi L.
by exists psi; split => //; apply subs.
Qed.

Lemma clos_clos P: closure (closure P) === closure P.
Proof.
rewrite set_eq_subs; split; last exact/subs_clos.
move => phi ccPphi L; have [psi [coin cPpsi]] := ccPphi L; have [psi' [coin' Ppsi']] := cPpsi L.
by exists psi'; split => //; apply: coin_trans coin coin'.
Qed.

Context (Q' A': Type).
Notation B':= (Q' -> A').
Context (F: B ->> B').

Definition dom_cont :=
	make_subset (fun phi => (forall q', (phi, q') \from dom (mf_mod F))).

Lemma dom_domc:
	ptw_continuous F <-> forall phi, phi \from dom F -> phi \from dom_cont.
Proof. by split => cont phi phifd; last split => //; move => q'; apply cont. Qed.

Lemma ptw_cont_domc: (F|_dom_cont) \is_pointwise_continuous.
Proof.
move => phi [Fphi [domc FphiFphi]].
split => [ | q']; first by exists Fphi.
have [L [/= phifd Lprop]]:= domc q'; exists L; split; first by exists Fphi.
move => Fphi' [/= _ val] psi coin.
by apply/ det_restr => domcpsi; apply/ Lprop.
Qed.
End closures.