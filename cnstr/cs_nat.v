From mathcomp Require Import all_ssreflect.
Require Import all_core classical_cont all_cs_base cs_one.
Require Import ClassicalChoice FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NATURALS.

Canonical cs_nat := @continuity_space.Pack
	one
	nat
	star
	0%nat
	one_count
	nat_count
	(dictionary.Pack (cs_id_modest_set_mixin nat)).

Lemma S_rec_fun: (S: cs_nat -> cs_nat) \is_continuous.
Proof.
exists (F2MF (fun phi q =>S (phi q))).
split; first by rewrite F2MF_rlzr => /= phi n -> [m]; by exists m.
by rewrite F2MF_cont => phi; exists (fun _ => [:: star]) => psi str []; elim: str => ->.
Qed.

Lemma nat_dscrt (X: cs) (f: cs_nat -> X): f \is_continuous.
Proof.
pose R:= make_mf (fun phi psi => psi \is_description_of (f (phi star))).
have Rtot: R \is_total by move => phi; apply/rep_sur.
have [F icf]:= choice _ Rtot.
exists (F2MF F); split; first by rewrite F2MF_rlzr_F2MF => fn n <-/=; apply/icf.
rewrite F2MF_cont_choice => phi q'; exists [::star] => psi [eq _].
by have ->: phi = psi by apply functional_extensionality => str; elim str.
Qed.

Lemma nat_nat_cont (f: nat -> nat -> nat):
	(fun (p: cs_nat \*_cs cs_nat) => f p.1 p.2: cs_nat) \is_continuous.
Proof.
exists (F2MF (fun phi q => f (phi (inl star)).1 (phi (inr star)).2)); split.
	by rewrite F2MF_rlzr_F2MF => phi [n m] [/= <- <-].
by rewrite F2MF_cont => phi; exists (fun _ => [:: inl star; inr star]) => psi str [-> [->]].
Qed.

(*
Lemma nat_rs_rec_pind (Z X: rep_space) (f0: Z -> X) (fS: (Z * X) -> X) (f: (Z * nat) -> X):
	f0 \is_recursive_function -> fS \is_recursive_function ->
		(forall p, f p = (fix f' z n := match n with
			| 0 => f0 z
			| S n' => fS (z, f' z n')
		end) p.1 p.2) -> f \is_recursive_function.
Proof.
move => [M0 M0prop] [/=MS MSprop] feq.
pose Mf:= fix Mf phi n q := match n with
	| 0 => M0 phi q
	| S n' => MS (name_pair phi (Mf phi n')) q
end.
exists (fun (phi: names (rep_space_prod Z rep_space_nat)) q => Mf (lprj phi) (rprj phi star) q).
move => phi [z n] [/=phinz phinn]; rewrite /Mf/=.
rewrite /id_rep in phinn.
elim: n phi phinz phinn => [phi phinz -> | n ih phi phinz ->]; first by rewrite feq/=; apply M0prop.
rewrite feq /=; apply MSprop.
split; rewrite lprj_pair rprj_pair => //=.
specialize (ih (name_pair (lprj phi) (fun _ => n))).
by rewrite lprj_pair rprj_pair feq/= in ih; apply ih.
Defined.

Lemma nat_rs_rec_ind (X: rep_space) (f0: X) (fS: X -> X) (f: nat -> X):
	f0 \is_recursive_element -> fS \is_recursive_function ->
		(forall n, f n = (fix f' n := match n with
			| 0 => f0
			| S n' => fS (f' n')
		end) n) -> f \is_recursive_function.
Proof.
move => [M0 M0prop] [/=MS MSprop] feq.
pose Mf:= fix Mf n q := match n with
	| 0 => M0 q
	| S n' => MS (Mf n') q
end.
exists (fun (phi: names (rep_space_nat)) q => Mf (phi star) q).
move => phi n phinn; rewrite /Mf/=.
rewrite /id_rep in phinn.
elim: n phi phinn => [phi -> | n ih phi ->]; first by rewrite feq/=; apply M0prop.
rewrite feq /=; apply MSprop.
specialize (ih (fun _ => n)).
by rewrite feq/= in ih; apply ih.
Qed.
*)
End NATURALS.