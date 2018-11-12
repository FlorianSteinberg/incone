From mathcomp Require Import ssreflect seq ssrfun.
Require Import all_core classical_cont cs prod cs_unit.
Require Import ClassicalChoice FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NATURALS.

Canonical cs_nat := continuity_space.Pack
	tt
	0%nat
	unit_count
	nat_count
	(dictionary.Pack (cs_id_modest_set_mixin nat)).

Lemma S_rec_fun: (S: cs_nat -> cs_nat) \is_continuous.
Proof.
exists (F2MF (fun phi q =>S (phi q))).
split; first by rewrite F2MF_rlzr => /= phi n -> [m]; by exists m.
by rewrite F2MF_cont => phi; exists (fun _ => [:: tt]) => psi str []; elim: str => ->.
Qed.

Lemma nat_dscrt (X: cs) (f: cs_nat -> X): f \is_continuous.
Proof.
pose R:= make_mf (fun phi psi => psi \is_description_of (f (phi tt))).
have Rtot: R \is_total by move => phi; apply/rep_sur.
have [F icf]:= choice _ Rtot.
exists (F2MF F); split; first by rewrite F2MF_rlzr_F2MF => fn n <-/=; apply/icf.
rewrite F2MF_cont_choice => phi q'; exists [::tt] => psi [eq _].
by have ->: phi = psi by apply functional_extensionality => str; elim str.
Qed.

Lemma nat_nat_cont (f: nat -> nat -> nat):
	(fun (p: cs_nat \*_cs cs_nat) => f p.1 p.2: cs_nat) \is_continuous.
Proof.
exists (F2MF (fun phi q => f (phi (inl tt)).1 (phi (inr tt)).2)); split.
	by rewrite F2MF_rlzr_F2MF => phi [n m] [/= <- <-].
by rewrite F2MF_cont => phi; exists (fun _ => [:: inl tt; inr tt]) => psi str [-> [->]].
Qed.
End NATURALS.