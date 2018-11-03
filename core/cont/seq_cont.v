(* This file provides a definition of continuity of functions between spaces of the form
Q -> A for some arbitrary types Q and A. It also proves some basic Lemmas about this notion.*)
From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mpf.
Require Import baire cont.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section sequential_continuity.
Context (Q A Q' A' : Type).
(* Q is for questions, A is for answers*)
Notation B := (Q -> A).
Notation B' := (Q' -> A').
(* B is for Baire space. *)
Context (F: B ->> B').

Definition seq_cont :=
	forall phi phin Fphin Fphi, lim phin phi -> (forall n, F (phin n) (Fphin n)) -> F phi Fphi ->
		lim Fphin Fphi.

Lemma seq_cont_sing: seq_cont -> F \is_singlevalued.
Proof.
move => cont phi Fphi Fphi' FphiFphi FphiFphi'.
pose phin (n: nat) := phi.
pose Fphin (n: nat) := Fphi'.
have limF': lim Fphin Fphi' by move => L; exists 0 => m _; apply coin_ref.
apply/(lim_sing _ limF').
apply/cont; last exact FphiFphi; last by move => n; apply FphiFphi'.
by move => L; exists 0 => m _; apply coin_ref.
Qed.

(*
Lemma cont_seq_cont: F \is_continuous -> seq_cont.
Proof.
move => [mf mod] phi phin Fphin Fphi lm prp FphiFphi L.
elim: L => [ | q' L [n ih]]; first by exists 0.
have:= mod phi Fphi FphiFphi q'; rewrite /cert.
elim: (mf phi q') => [cnd | q K ihK cnd]; first by exists n; split; [apply/cnd | apply/ih].
Admitted.
*)
End sequential_continuity.