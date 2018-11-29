(*This file considers Baire space nat -> nat as example for
a space that can be thought about continuity on. *)
From Coq.micromega Require Import Psatz.
From mathcomp Require Import all_ssreflect.
Require Import all_cs classical_cont.
Require Import ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section BAIRE_SPACE.
Context (Q A Q' A': Type).
Notation B := (nat -> nat).
Notation N := (unit -> nat).
Notation init_seg := (iseg id).
Notation max_elt:= (max_elt id).

Lemma ms: minimal_section id id.
Proof. by split => // m n ->. Qed.

Lemma leq_max (F: nat -> nat) n : forall i, i < n -> F i <= \max_(i <- init_seg n) F i.
Proof.
elim: n => //n ih i; rewrite leq_eqVlt/= big_cons /=.
case /orP => [/eqP [->] | ineq]; [exact/leq_maxl | exact/leq_trans/leq_maxr/ih].
Qed.

(* This is the more conventional continuity using intial segments.
It is equivalent to the corresponding multifunction being continuous
in the sense of "continuity.v" *)
Definition continuous_operator_f (G: B -> B) := forall phi n, exists m, forall phi',
        {in init_seg m, phi =1 phi'} -> {in init_seg n, G phi =1 G phi'}.

Lemma F2MF_continuous (F: B -> B):
  continuous_operator_f F <-> (F2MF F) \is_continuous_operator.
Proof.
split => [cont | /F2MF_cont cont phi n].
- rewrite F2MF_cont_choice => phi n.
  have [m mod]:= cont phi n.+1.
  exists (init_seg m) => psi /coin_funeq coin.
  have /coin_funeq/coin_lstn prp:= mod psi coin.
  by apply/prp/lstn_iseg; exists n.
have [Lf mod] := cont phi.
set m := \max_(i <- init_seg n) max_elt (Lf i).
exists m => psi/coin_funeq/coin_subl coin; rewrite -coin_funeq coin_lstn => q lstn.
apply/mod/coin/subl_trans; first exact/iseg_melt/ms.
exact/iseg_subl/leq_max/(@iseg_base _ id id)/lstn/ms.
Qed.

Definition continuous_operator_p (G: B -> option B) := forall phi psi,
    G phi = Some psi -> forall n, exists m,
                    forall phi' psi', G phi' = some psi' -> 
	{in init_seg m, phi =1 phi'} -> {in init_seg n, psi =1 psi'}.

Lemma PF2MF_continuous (F: B -> option B):
  continuous_operator_p F <-> (PF2MF F) \is_continuous_operator.
Proof.
split => [cont | cont phi psi val n].
- rewrite cont_choice => phi /=.
  case val: (F phi) => [psi | ]// _ <- n.
  have [m mod]:= cont phi psi val n.+1.
  exists (init_seg m)=> phi' /coin_agre /coin_funeq coin.
  case val': (F phi') => [psi' | ]// _ <-.
  have /coin_funeq/coin_lstn prp:= mod phi' psi' val' coin.
  by symmetry; apply/prp/lstn_iseg; exists n.
have [ | Lf mod]:= cont phi _; first by exists psi; rewrite /= val.
set m := \max_(i <- init_seg n) max_elt (Lf i).
exists m => phi' psi' val'/coin_funeq coin.
apply/coin_funeq/coin_lstn => k lstn.
have [a' crt]:= mod k.
suff -> : psi' k = a' by apply/(crt phi); [apply/coin_agre/coin_ref | rewrite /= val].
apply/(crt phi'); last by rewrite /= val'.
apply/coin_agre/coin_subl/coin.
apply/subl_trans/iseg_subl/leq_max/(@iseg_base _ id id)/lstn/ms.
exact/iseg_melt/ms.
Qed.

(*To have function from baire space to natural numbers, we identify nat with one -> nat.*)
Definition F := make_mf (fun phi n => phi (n tt) = 0 /\ forall m, phi m = 0 -> n tt <= m).
(* F is a partial function: if phi is never zero, the right hand side is always false and
phi is not assinged any value. On the other hand the function is single valued, as only
the smalles number where phi is zero allowed as return value. More generally, the function
is continuous:*)

Lemma F_cont: F \is_continuous_operator.
Proof.
apply cont_choice => phi nf [val prp] str.
exists (init_seg (nf tt).+1) => psi/coin_agre/coin_lstn coin nf' [val' prp'].  
elim str; apply/eqP; rewrite eqn_leq; apply/andP.
split; [apply/prp'; rewrite -coin// | apply/prp]; first by apply/lstn_iseg; exists (nf tt).
rewrite -coin // in val'.
apply/lstn_iseg; exists (nf' tt); split => //.
suff ineq: (nf' tt).+1 <= (nf tt).+1 by apply/ineq.
by apply/prp'; rewrite -coin //; apply/lstn_iseg; exists (nf tt).
Qed.

Lemma F_sing: F \is_singlevalued.
Proof. exact: cont_sing F_cont. Qed.

(*
Lemma no_extension G: G \is_continuous_operator -> G \extends F -> G =~= F.
Proof.
move => /cntop_spec cont exte; rewrite exte_equiv.
split => [ | phi nf val]; first exact/exte.
have [Lf mod]:= cont phi nf val.
pose L := Lf star.
case: (classic (exists k, k \in L /\ phi k = 0)).
set m := maxn (nf star).+1 (max_elt L).+1.
pose psi k := if k == m then 0 else phi k.
case: (classic (exists k, k < m /\ phi k = 0)).
have /coin_spec coin: phi \and psi \coincide_on L.
	admit.
have psifdF: psi \from dom F.
 admit.
Admitted. *)

(* Since classically, any multi function can be extended to a total multi function and
we get the following:
Lemma no_extension':
	~ exists G, G extends F /\ G is_continuous /\ G is_total.
But I don't feel like proving that now. *)
End BAIRE_SPACE.