From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mpf choice_mf.
Import ClassicalChoice.
Require Import baire cont iseg minm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma well_order_nat (P : nat -> Prop):
	(exists n, P n) -> exists n, P n /\ forall m, P m -> n <= m.
Proof.
set R:= (fun n b => P n <-> is_true b).
have [ | p prop]:= choice R.
	by move => n; case: (classic (P n)) => pn; [exists true|exists false]; split.
move => [m Pm].
have ex: exists n, p n by exists m; apply prop.
have [n [pn min]]:= (worder_nat ex).
by exists n; split => [ | k Pk ]; [ | apply min]; apply prop.
Qed.

(*
Lemma minimal_section Q (cnt: nat -> Q):
	cnt \is_surjective_function -> exists sec, is_min_sec cnt sec.
Proof.
move => sur.
set R := make_mf (fun s n => cnt n = s /\ (forall m, cnt m = s -> n <= m)).
have Rtot: R \is_total by move => s; have [n]:= well_order_nat (sur s); exists n.
by have [sec]:= (choice _ Rtot); exists sec; split => s; have []:= p s.
Qed.
*) 

Section classical_lemmas.
Context (Q Q' A A': Type) (noq: Q).
Notation B := (Q -> A).
Notation B' := (Q' -> A').
Context (cnt: nat -> Q) (sec: Q -> nat) (ms: minimal_section cnt sec).
Notation minimal_modulus := (minimal_modulus cnt sec).
Notation init_seg := (iseg cnt).
Notation max_elt := (max_elt sec).

Lemma cont_choice (F: B ->> B'): F \is_continuous_operator <->
	forall phi Fphi, F phi Fphi -> forall q', exists L, cert F (L2SS L) phi q' (Fphi q').
Proof.
rewrite cntop_spec.
split => cont phi Fphi FphiFphi; first move => q'.
	by have [Lf mod] := cont phi Fphi FphiFphi; exists (Lf q'); apply/mod.
by have [Lf mod]:= choice _ (cont phi Fphi FphiFphi); exists Lf.
Qed.

Lemma F2MF_cont_choice (F: B -> B'): (F2MF F) \is_continuous_operator <->
	forall phi q', exists L, forall psi, phi \and psi \coincide_on L -> F phi q' = F psi q'.
Proof.
rewrite F2MF_cont; split=> [cont phi q' | cont phi].
	by have [Lf mod]:= cont phi; exists (Lf q') => psi; apply/mod.
by have [Lf mod]:= choice _ (cont phi); exists Lf => q' psi; apply/mod.
Qed.

Lemma cert_cdom (F: B ->> B') phi q' a':
	~ phi \from closure (dom F) -> exists L, cert F (L2SS L) phi q' a'.
Proof.
move => neg.
have [L Lprop]: exists L, forall psi, ~ (phi \and psi \coincide_on L /\ psi \from dom F).
	apply NNPP => ex; apply neg => L; apply NNPP => negi.
	exfalso; apply ex; exists L => psi [] coin val.
	by apply negi; exists psi.
exists L => psi coin Fpsi FpsiFpsi.
exfalso; apply (Lprop psi).
by split; [apply/coin_spec | exists Fpsi].
Qed.

Lemma dom_minmod (F: B ->> B'):
	dom (minimal_modulus F) === dom (continuity_modulus F).
Proof.
move => phi; split => [[mf [mod min]] | [Lf mod]]; first by exists (fun q' => init_seg (mf q')).
pose R q' n :=
	(exists a', cert F (L2SS (init_seg n)) phi q' a')
	/\
	forall (Lf': Q' -> seq Q), continuity_modulus F phi Lf' -> n <= max_elt (Lf' q').
have Rtot: forall q', exists n, R q' n.
	move => q'; pose p n := exists a', cert F (L2SS (init_seg n)) phi q' a'.
	have ex: exists n, p n.
		exists (max_elt (Lf q')); have [a' crt]:= (mod q').
		by exists a'; apply/cert_exte/crt; rewrite -L2SS_subs; apply/iseg_melt.
	have [n [prp min]]:= well_order_nat ex.
	exists n; split => // Lf' mod'; apply/min; rewrite /p; have [a' crt]:= mod' q'.
	by exists a'; apply/cert_exte/crt; rewrite -L2SS_subs; apply/iseg_melt.
have [mf mfprop] := choice R Rtot.
exists mf.
by split => [q' | Lf' mod' q']; [exact/(mfprop q').1 | exact/(mfprop q').2].
Qed.

Lemma exists_minmod (F: B ->> B'): F \is_continuous_operator ->
	exists mf, forall phi, phi \from dom F -> minimal_modulus F phi (mf phi).
Proof.
move => cont; have [mf icf]:= exists_choice (minimal_modulus F) (fun _ => 0).
by exists mf => phi phifd; have:= cont phi phifd; rewrite -dom_minmod => [[]]; apply/icf.
Qed.
End classical_lemmas.
