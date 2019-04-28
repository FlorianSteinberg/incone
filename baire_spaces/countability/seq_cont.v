From mathcomp Require Import ssreflect ssrnat ssrbool ssrfun seq.
From mf Require Import all_mf.
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
  Local Open Scope baire_scope.
  Context (F: B ->> B').

  Definition sequential_continuity_point phi:=
    forall phin Fphin Fphi,
      phi \is_limit_of phin -> (forall n, F (phin n) (Fphin n)) -> F phi Fphi ->
      Fphi \is_limit_of Fphin.

  Definition sequential_continuity_points:=
    make_subset (fun phi => sequential_continuity_point phi).
  
  Definition sequentially_continuous:=
    forall phi, sequential_continuity_point phi.
  
  Lemma scnt_spec:
    sequentially_continuous <-> dom F \is_subset_of sequential_continuity_points.
  Proof.
    split => [scnt phi [Fphi val]| scnt phi phin Fphin Fphi lmt lmts val] ; first exact/scnt.
    by apply/scnt/val/lmts/lmt; exists Fphi.
  Qed.

  Lemma scnt_frcs phi: phi \from dom F -> sequential_continuity_point phi -> phi \from dom (forces F).
  Proof.
    move => [Fphi val] cont.
    exists Fphi => Fphi' val'.
    apply/lim_sing/lim_const/cont/val'.
    - exact/lim_const.
    by rewrite /cnst.
  Qed.
  
  Lemma scnt_sing: sequentially_continuous -> F \is_singlevalued.
  Proof.
    move => cont; apply/sing_spec => phi dm.
    exact/scnt_frcs.
  Qed.

  Definition continuity_point phi :=
    forall Fphi, F phi Fphi -> exists Lf, Lf \is_modulus_of F \on_input phi.

  Lemma cntp_spec: F \is_continuous <-> forall phi, continuity_point phi.
  Proof.
    split => [cont phi Fphi val | cont].
    - by have [Lf]:= cont phi Fphi val; exists Lf => q'; exists (Fphi q').
    apply/cont_spec => phi [Fphi val].
    exact/cont/val.
  Qed.

  Lemma imod_spec Lf phi Fphi: F phi Fphi -> Lf \is_modulus_of F \on_input phi <->
    forall q', certificate F (Lf q') phi q' (Fphi q').
  Proof.
    move => val; split => mod q'; last by exists (Fphi q').
    by have [a' crt]:= mod q'; apply/crt_icf/crt/val.
  Qed.
    
  Lemma cntp_scntp phi: continuity_point phi -> sequential_continuity_point phi.
  Proof.
    move => cont phin Fphin Fphi lim vals val L.
    have [Lf /(imod_spec _ val) mod]:= cont Fphi val.
    have [n prp]:= lim (gather Lf L).
    exists n => m ineq.
    elim: L prp => [ | q' L ih prp]//.
    split; last by apply/ih => m' ineq'; have /coin_cat []:= prp m' ineq'.
    symmetry; apply/mod/vals.
    by have /coin_cat []:= prp m ineq.    
  Qed.

  Lemma cont_scnt: F \is_continuous -> sequentially_continuous.
  Proof. by move => /cntp_spec cont phi; apply/cntp_scntp/cont. Qed.
End sequential_continuity.
Notation "F \is_sequentially_continuous_in phi" := (sequential_continuity_point F phi) (at level 40): baire_scope.
Notation "F \is_sequentially_continuous" := (sequentially_continuous F) (at level 40): baire_scope.
