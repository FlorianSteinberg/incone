From mathcomp Require Import ssreflect ssrnat ssrbool.
From rlzrs Require Import all_mf.
Require Import baire cont.

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
	forall phin phi Fphin Fphi, baire_limit phin phi -> (forall n, F (phin n) (Fphin n)) -> F phi Fphi ->
		baire_limit Fphin Fphi.

Lemma seq_cont_sing: seq_cont -> F \is_singlevalued.
Proof.
move => cont phi Fphi Fphi' FphiFphi FphiFphi'.
pose phin (n: nat) := phi.
pose Fphin (n: nat) := Fphi'.
have limF': baire_limit Fphin Fphi' by move => L; exists 0 => m _; apply coin_ref.
apply/(lim_sing _ limF').
apply/cont; last exact FphiFphi; last by move => n; apply FphiFphi'.
by move => L; exists 0 => m _; apply coin_ref.
Qed.

Lemma cmtop_scnt: F \is_continuous_operator -> seq_cont.
Proof.
move => cont phin phi Fphin Fphi lim vals val L.
have [Lf mod]:= cont phi Fphi val.
have [n prp]:= lim (gather Lf L).
exists n => m ineq.
elim: L prp => [ | q' L ih prp]//.
split.
- symmetry; apply/mod/vals.
  by have /coin_cat []:= prp m ineq.
by apply/ih => m' ineq'; have /coin_cat []:= prp m' ineq'.
Qed.
End sequential_continuity.