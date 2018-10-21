From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mpf choice_mf.
Import ClassicalChoice.
Require Import baire cont ptw_cont.

Section classical_lemmas.
Context (Q A Q' A': Type).
Notation B := (Q -> A).
Notation B' := (Q' -> A').

Lemma choice_ptw_cont_cont (F: B ->> B'):
	ptw_continuous F -> F \is_continuous.
Proof.
move => cont.
have [mf mprop] := exists_choice (mf_mod F) nil; exists (fun phi q' => mf (phi, q')).
by rewrite mod_mf_mod => phi q' phifd; have [L]:=(cont phi phifd q'); apply/mprop.
Qed.

Lemma choice_cont_ptw_cont (F: B ->> B'):
	continuous F <-> ptw_continuous F.
Proof. by split; [apply/cont_ptw_cont | apply/choice_ptw_cont_cont]. Qed.

(*The following is the reason why the phi \from_dom F is part of many definitions *)
Lemma cert_cdom (F: B ->> B') phi q' a':
	~ phi \from closure (dom F) -> exists L, cert F L phi q' a'.
Proof.
move => neg.
have [L Lprop]: exists L, forall psi, ~ (phi \and psi \coincide_on L /\ psi \from dom F).
	apply NNPP => ex; apply neg => L; apply NNPP => negi.
	exfalso; apply ex; exists L => psi [] coin val.
	by apply negi; exists psi.
exists L => psi coin Fpsi FpsiFpsi.
exfalso; apply (Lprop psi).
by split; last by exists Fpsi.
Qed.

Lemma cont_domc (F: B ->> B'): (F|_(dom_cont F)) \is_continuous.
Proof. by rewrite choice_cont_ptw_cont; apply/ptw_cont_domc. Qed.
End classical_lemmas.

Lemma cont_comp Q A Q' A' Q'' A'' (F: (Q -> A) ->> (Q' -> A')) (G: _ ->> (Q'' -> A'')):
	F \is_continuous -> G \is_continuous -> G o F \is_continuous.
Proof. move => cont; rewrite !choice_cont_ptw_cont; exact/ptw_cont_comp. Qed.