(* This file provides an abstract envelope for computability theoretical considerations *)
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype choice seq bigop.
From mf Require Import all_mf.
Require Import all_cont search seq_cont PhiN FMop multivalued_application.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section continuous_machines.
  Local Open Scope name_scope.
  Context (fuel Q A Q' A': Type).
  Structure continuous_machine :=
    {
      machine:> (Q -> A) -> fuel * Q' -> option A';
      modulus: (Q -> A) -> fuel * Q' -> seq Q;
      modulus_correct: modulus \modulus_function_for machine;
      modulus_selfmodulating: modulus \modulus_function_for modulus;
    }.

  Context (M: continuous_machine).

  Lemma mod: modulus M \modulus_function_for M.
  Proof. exact/modulus_correct. Qed.

  Lemma modmod: modulus M \modulus_function_for modulus M.
  Proof. exact/modulus_selfmodulating. Qed.

  Lemma mach_cntf: M \is_continuous_function.
  Proof.
    move => phi.
    exists (modulus M phi).
    exact/modulus_correct.
  Qed.

  Lemma mod_cntf: modulus M \is_continuous_function.
  Proof.
    move => phi.
    exists (modulus M phi).
    exact/modulus_selfmodulating.
  Qed.
End continuous_machines.

Section evaluate_continuous_machine.
  Context (Q Q': eqType) fuel fuel' A A' (M: continuous_machine fuel Q A Q' A') (default: A) (no_fuel: fuel').

  Definition run_on (N: fuel'* Q -> option A) :=
    machine_application default M (modulus M) N.

  Lemma run_exte_tight N phi:
    \Phi_N =~= (F2MF phi) -> \Phi_(run_on N) \tightens \Phi_(M phi).
  Proof.
    move => exte q' [a' [n val]].
    split => [ | q].
    - exists a'; apply/mapp_val.
      + exact/no_fuel.
      + by move => phi' _ <-; apply/cmod_F2MF/modmod.
      + by move => q; exists (phi q); apply/exte.
      + suff icf: phi \is_choice_for (\Phi_N) by apply/icf.
        by move => q qfd; apply/exte.
      + exact/val.
      by exists (some a') => psi coin _ <-; rewrite -(mod coin).
    rewrite /=.
    move => [[k s]].
    case: ifP => // /clP subl <-.
    exists k.
    symmetry.
    apply/mod/coin_subl/coin_agre; first exact/subl.
    move => q0 /lstd_spec [a].
    rewrite /phi_rec.
    elim: KL_rec => // [[q1 f]] KL ih.
    rewrite /N2MF /= !N2LF_cons.
    rewrite /LF2F N2LF_cons.
    case: ifP => //.
    case Neq: (N _) => [a1 |] // a0 eq /=.
    have [/=vl _ ]:= exte q0 a1.
    symmetry; apply/vl.
    by exists f; rewrite Neq.    
  Qed.
End evaluate_continuous_machine. 
  
Section monotonicity.
  Context (Q A Q' A': Type).
  Notation machine := (continuous_machine nat Q A Q' A').
  
  Class is_monotone (M: machine):=
    {
      monotone: monotone M;
      modulus_terminating: terminates_with M (modulus M);
    }.

  Definition make_monotone (M: machine): machine.
    exists (use_first M) (truncate_along M (make_monotone (modulus M))).
    exact/trunc_mod/mkmm_mod/mod/mkmm_mon.
    exact/trunc_modmod/mkmm_mod/mod/mkmm_modmod/modmod/mkmm_mon.
  Defined.

  Lemma mkmn_spec (M: machine): is_monotone (make_monotone M).
  Proof.
    split; first exact/sfrst_mon.
    move => phi q' n.
    have ->: make_monotone M phi (n, q') = M phi (ord_search (fun k => M phi (k, q')) n, q').
    - by rewrite -sfrst_osrch.
    by rewrite /FMop.make_monotone /= osrchS => ->.
  Qed.
End monotonicity.
