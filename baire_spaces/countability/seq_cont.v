From mathcomp Require Import ssreflect ssrnat ssrbool ssrfun seq.
From rlzrs Require Import all_mf.
Require Import baire cont count iseg.

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

Definition sequential_continuity_point phi:=
  forall phin Fphin Fphi,
    baire_limit phin phi -> (forall n, F (phin n) (Fphin n)) -> F phi Fphi ->
		baire_limit Fphin Fphi.

Definition sequential_continuity_points:= make_subset (fun phi => sequential_continuity_point phi).

Definition sequentially_continuous:=
  forall phi, sequential_continuity_point phi.

Lemma scnt_spec:
  sequentially_continuous <-> dom F \is_subset_of sequential_continuity_points.
Proof.
  split => [scnt phi [Fphi val]| scnt phi phin Fphin Fphi lmt lmts val] ; first exact/scnt.
  by apply/scnt/val/lmts/lmt; exists Fphi.
Qed.

Lemma scnt_sing: sequentially_continuous -> F \is_singlevalued.
Proof.
  move => cont phi Fphi Fphi' FphiFphi FphiFphi'.
  pose phin (n: nat) := phi.
  pose Fphin (n: nat) := Fphi'.
  have limF': baire_limit Fphin Fphi' by move => L; exists 0 => m _; apply coin_ref.
  apply/(lim_sing _ limF').
  apply/cont; last exact FphiFphi; last by move => n; apply FphiFphi'.
  by move => L; exists 0 => m _; apply coin_ref.
Qed.

Lemma cntop_scnt: F \is_continuous_operator -> sequentially_continuous.
Proof.
  move => cont phi phin Fphin Fphi lim vals val L.
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