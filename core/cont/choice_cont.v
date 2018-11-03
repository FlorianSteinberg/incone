From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mpf choice_mf.
Import ClassicalChoice.
Require Import baire cont.

Section classical_lemmas.
Context (Q A Q' A': Type).
Notation B := (Q -> A).
Notation B' := (Q' -> A').

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
End classical_lemmas.
