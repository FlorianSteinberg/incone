(** This file considers the function that searches for the minimal input such that a function vanishes
    as an example of a continuous partial operator on baire space and shows that the continuity
    on baire spaces is equivalent to the traditional definition for nat -> nat. **)
Require Import Psatz.
From mathcomp Require Import all_ssreflect.
From metric Require Import all_metric.
Require Import all_baire baire_metric classical_cont.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope baire_scope.
Section baire_space.
  Context (Q A Q' A': Type).
  Notation B := (nat -> nat).
  Notation N := (unit -> nat).
  Notation max_elt:= (max_elt id).

  Lemma ms: minimal_section id id.
  Proof. by split => // m n ->. Qed.

  Lemma leq_max (F: nat -> nat) n : forall i, i < n -> F i <= \max_(i <- init_seg n) F i.
  Proof.
    elim: n => //n ih i; rewrite leq_eqVlt/= big_cons /=.
    by case /orP => [/eqP [->] | ineq]; [exact/leq_maxl | exact/leq_trans/leq_maxr/ih].
  Qed.

  (** This is a more traditional description of continuity on baire space: **)
  Lemma cont_spec (F: B -> B): F \is_continuous_function <->
                               forall phi n, exists m, forall phi',
                                     {in init_seg m, phi =1 phi'} -> {in init_seg n, F phi =1 F phi'}.
  Proof.
    split => [cont phi n | cont].
    - have [Lf mod] := cont phi.
      set m := \max_(i <- init_seg n) max_elt (Lf i).
      exists m => psi/coin_funeq/coin_subl coin; rewrite -coin_funeq coin_lstn => q lstn.
      apply/mod/coin/subl_trans; first exact/iseg_melt/ms.
      exact/iseg_subl/leq_max/(@iseg_base _ id id)/lstn/ms.
    rewrite F2MF_cont_choice => phi n.
    have [m mod]:= cont phi n.+1.
    exists (init_seg m) => psi /coin_funeq coin.
    have /coin_funeq/coin_lstn prp:= mod psi coin.
    by apply/prp/lstn_iseg; exists n.
  Qed.

  (* The same can be done for partial operators: *)
  Lemma PF2MF_continuous (F: B -> option B): (PF2MF F) \is_continuous <->
    forall phi psi, F phi = Some psi -> forall n, exists m,
          forall phi' psi', F phi' = some psi' -> 
	                    {in init_seg m, phi =1 phi'} -> {in init_seg n, psi =1 psi'}.
  Proof.
    split => [cont phi psi val n | cont].
    - have [ | Lf mod]/=:= cont phi psi; first by rewrite val.
      set m := \max_(i <- init_seg n) max_elt (Lf i).
      exists m => phi' psi' val'/coin_funeq coin.
      apply/coin_funeq/coin_lstn => k lstn; symmetry; apply/mod.
      + apply/coin_subl/coin/subl_trans/iseg_subl/leq_max/iseg_base/lstn/ms.
        exact/iseg_melt/ms.
      by rewrite /= val'.
    rewrite cont_choice => phi /=.
    case val: (F phi) => [psi | ]// _ <- n.
    have [m mod]:= cont phi psi val n.+1.
    exists (init_seg m)=> phi' /coin_funeq coin.
    case val': (F phi') => [psi' | ]// _ <-.
    have /coin_funeq/coin_lstn prp:= mod phi' psi' val' coin.
    by symmetry; apply/prp/lstn_iseg; exists n.
  Qed.

  (** To have functions from baire space to natural numbers, we identify nat with one -> nat. **)
  Definition F := make_mf (fun phi n => phi (n tt) = 0 /\ forall m, phi m = 0 -> n tt <= m).
  (** F is a partial function: if phi is never zero, the right hand side is always false and
      phi is not assinged any value. On the other hand the function is single valued, as only
      the smalles number where phi is zero allowed as return value. More generally, the function
      is continuous: **)

  Lemma F_cont: F \is_continuous.
  Proof.
    apply cont_choice => phi nf [val prp] str.
    exists (init_seg (nf tt).+1) => psi /coin_lstn coin nf' [val' prp'].  
    elim str; apply/eqP; rewrite eqn_leq; apply/andP.
    split; [apply/prp'; rewrite -coin// | apply/prp]; first by apply/lstn_iseg; exists (nf tt).
    rewrite -coin // in val'.
    apply/lstn_iseg; exists (nf' tt); split => //.
    suff ineq: (nf' tt).+1 <= (nf tt).+1 by apply/ineq.
    by apply/prp'; rewrite -coin //; apply/lstn_iseg; exists (nf tt).
  Qed.

  Lemma F_sing: F \is_singlevalued.
  Proof. exact: cont_sing F_cont. Qed.
End baire_space.