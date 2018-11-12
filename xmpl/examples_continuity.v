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
Definition continuity (G: (nat -> nat) -> nat -> nat) := forall phi n, exists m, forall psi,
	{in init_seg m, phi =1 psi} -> {in init_seg n, G phi =1 G psi}.
(*
Lemma continuity1 (F: B -> B): continuity F <-> (F2MF F) \is_continuous_operator.
Proof.
split => [cont | /F2MF_cont cont phi n].
	rewrite F2MF_cont_choice => phi n.
	have [m mod]:= cont phi n.+1.
	exists (init_seg m) => psi /coin_funeq coin.
	have /coin_funeq/coin_lstn prp:= mod psi coin.
	exact/prp/lstn_iseg.
have [Lf mod] := cont phi.
set m := \max_(i <- init_seg n) max_elt (Lf i).
exists m => psi/coin_funeq/coin_subl coin; rewrite -coin_funeq coin_lstn => q lstn.
apply/mod/coin/subl_trans; first exact/iseg_melt/ms.
exact/iseg_subl/leq_max/(@iseg_base _ id id)/lstn/ms.
Qed.
*)
(*To have function from baire space to natural numbers, we identify nat with one -> nat.*)
Definition F := make_mf (fun phi n => phi (n tt) = 0 /\ forall m, phi m = 0 -> n tt <= m).
(* F is a partial function: if phi is never zero, the right hand side is always false and
phi is not assinged any value. On the other hand the function is single valued, as only
the smalles number where phi is zero allowed as return value. More generally, the function
is continuous:*)
(*
Lemma F_cont: F \is_continuous_operator.
Proof.
apply cont_choice => phi nf [val prp] str.
exists (init_seg (nf tt).+1) => psi/coin_spec/coin_lstn coin nf' [val' prp'].
elim str; apply/eqP; rewrite eqn_leq; apply/andP.
split; [apply/prp'; rewrite -coin// | apply/prp]; first exact/(@lstn_iseg _ id id (nf tt)).
rewrite -coin in val' => //;
apply/iseg_subl; [suff e: (nf' tt).+1 <= (nf tt).+1 by apply/e | exact/(@lstn_iseg _ id id)].
by apply/prp'; rewrite -coin //; apply/(@lstn_iseg _ id id).
Qed.

Lemma F_sing: F \is_singlevalued.
Proof. exact: cont_sing F_cont. Qed.
*)
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