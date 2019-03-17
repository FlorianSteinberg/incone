From mathcomp Require Import ssreflect ssrnat ssrbool eqtype.
From mf Require Import all_mf.
Require Import baire cont iseg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section minimal_modulus.
  Context (Q Q' A A': Type).
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Local Open Scope baire_scope.
  Context (F: B ->> B').
  Context (cnt: nat -> Q).
  Context (sec: Q -> nat).
  Notation init_seg := (iseg cnt).
  Notation max_elt := (max_elt sec).
  Definition minimal_modulus S T (F: B ->> (S -> T)) := make_mf (fun phi mf =>
	((fun q' => init_seg (mf q')) \is_modulus_of F \on_input phi)
	/\
	forall Lf, Lf \is_modulus_of F \on_input phi -> forall q', mf q' <= max_elt (Lf q')).

  Lemma cntp_spec: continuity_points F === dom (continuity_modulus F)|_(dom F).
  Proof.
      by move => phi; split => [[] | [Fphi] []]; [rewrite dom_restr_spec | split; first by exists Fphi].
  Qed.
End minimal_modulus.

Section minimal_moduli.
  Context (Q': eqType) (Q A A': Type).
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Local Open Scope baire_scope.
  Context (F: B ->> B').
  Context (cnt: nat -> Q).
  Context (sec: Q -> nat).
  Context (ms: minimal_section cnt sec).
  Notation init_seg := (iseg cnt).
  Notation max_elt := (max_elt sec).
  Notation minimal_modulus := (minimal_modulus cnt sec).

  Lemma mod_minmod phi mf: (minimal_modulus F) phi mf ->
    (fun q' => init_seg (mf q')) \is_modulus_of (minimal_modulus F) \on_input phi.
  Proof.
    move => [mod min] q'.
    exists (mf q') => psi coin mf' [mod' min'].
    apply/eqP; rewrite eqn_leq; apply/andP.
    case/orP: (leq_total (mf q') (mf' q')) => ineq; split => //.
    - apply/leq_trans; last first;
        last apply/(min' (fun q => if q == q' then init_seg (mf q) else init_seg (mf' q))).
      + by rewrite /=; case: ifP => /eqP // _; apply/melt_iseg.
      move => q''; case E: (q'' == q'); last by have [a' crt']:= mod' q''; exists a'; exact/crt'.
      move: E => /eqP ->; 	have [a' crt'] := mod q'; exists a' => psi' coin' Fpsi' Fpsi'Fpsi'.
      by apply/crt'; first exact/coin_trans/coin'/coin.
    apply/leq_trans; last first;
      last apply/(min (fun q => if q == q' then init_seg (mf' q) else init_seg (mf q))).
    + by rewrite /=; case: ifP => /eqP // _; exact/melt_iseg.
    move => q''; case E: (q'' == q'); last by have [a' crt]:= mod q''; exists a'; exact/crt.
    move: E => /eqP ->; 	have [a' crt'] := mod' q'; exists a' => psi' coin' Fpsi' Fpsi'Fpsi'.
    exact/crt'/Fpsi'Fpsi'/coin_trans/coin'/coin_subl/coin_sym/coin/iseg_subl.
  Qed.

  Lemma minmod_cont: (minimal_modulus F) \is_continuous.
  Proof.
    move => phi mf mod; exists (fun q' => init_seg (mf q')) => q'.
    by have [a' mod']:=(mod_minmod mod q'); exact/crt_icf/mod'.
  Qed.
End minimal_moduli.
