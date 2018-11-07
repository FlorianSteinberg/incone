From mathcomp Require Import ssreflect ssrnat ssrbool eqtype.
From rlzrs Require Import all_mf.
Require Import baire cont iseg.
Require Import Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section search.
(* Most code from this section was provided by Vincent *)
Context (p: nat -> bool).

Let Fixpoint searchU m k : nat :=
	match k with
  | 0 => m
  | k'.+1 => let n := m - k in if p n then n else searchU m k'
  end.

Let searchU_correct m k :
  p m -> p (searchU m k).
Proof.
move => hm.
by elim: k => // n ih /=; case: ifP.
Qed.

Let searchU_le m k :
  searchU m k <= m.
Proof.
elim: k => // n ih /=; case: ifP => // _.
rewrite /subn /subn_rec; apply /leP; lia.
Qed.

Let searchU_minimal m k :
  (forall n, p n -> m - k <= n) -> forall n, p n -> searchU m k <= n.
Proof.
elim: k.
- move => h n /=; rewrite -(subn0 m); exact: h.
move => k ih h n /=; case: ifP.
- move => _; exact: h.
move => hk; apply: ih => i hi.
case: (i =P m - k.+1).
move => eq.
rewrite -eq in hk.
by rewrite hk in hi.
move: (h i hi).
rewrite /subn /subn_rec => /leP prp cnd; apply/leP; lia.
Qed.

Definition search n := searchU n n.

Lemma search_correct n:
	p n -> p (search n).
Proof.
exact: searchU_correct.
Qed.

Lemma search_le n:
	search n <= n.
Proof.
exact: searchU_le.
Qed.

Lemma search_min n m:
	p m -> search n <= m.
Proof.
apply searchU_minimal.
move => k pk.
rewrite /subn/subn_rec; apply/leP; lia.
Qed.

Lemma worder_nat:
	(exists n, p n) -> exists n, p n /\ forall m, p m -> n <= m.
Proof.
move => [m pm].
exists (search m ).
split; first exact: search_correct.
exact: search_min.
Qed.
End search.

Section minimal_modulus.
Context (Q Q' A A': Type).
Notation B := (Q -> A).
Notation B' := (Q' -> A').
Context (F: B ->> B').
Context (cnt: nat -> Q).
Context (sec: Q -> nat).
Notation init_seg := (iseg cnt).
Notation max_elt := (max_elt sec).

Definition minimal_modulus S T (F: B ->> (S -> T)) := make_mf (fun phi mf =>
	(continuity_modulus F phi (fun q' => init_seg (mf q')))
	/\
	forall Lf, continuity_modulus F phi Lf -> forall q', mf q' <= max_elt (Lf q')).

Lemma cont_pt_spec: continuity_points F === dom (continuity_modulus F)|_(dom F).
Proof.
by move => phi; split => [[] | [Fphi] []]; [rewrite dom_restr_spec | split; first by exists Fphi].
Qed.
End minimal_modulus.

Section minimal_moduli.
Context (Q': eqType) (Q A A': Type).
Notation B := (Q -> A).
Notation B' := (Q' -> A').
Context (F: B ->> B').
Context (cnt: nat -> Q).
Context (sec: Q -> nat).
Context (ms: minimal_section cnt sec).
Notation init_seg := (iseg cnt).
Notation max_elt := (max_elt sec).
Notation minimal_modulus := (minimal_modulus cnt sec).

Lemma mod_minmod phi mf: (minimal_modulus F) phi mf ->
	continuity_modulus (minimal_modulus F) phi (fun q' => init_seg (mf q')).
Proof.
move => [mod min] q'.
exists (mf q') => psi coin mf' [mod' min'].
apply/eqP; rewrite eqn_leq; apply/andP.
case/orP: (leq_total (mf q') (mf' q')) => ineq; split => //.
	apply/leq_trans; last first;
			last apply/(min' (fun q => if q == q' then init_seg (mf q) else init_seg (mf' q))).
		by rewrite /=; case: ifP => /eqP // _; apply/melt_iseg.
	move => q''; case E: (q'' == q'); last by have [a' crt']:= mod' q''; exists a'; exact/crt'.
	move: E => /eqP ->; 	have [a' crt'] := mod q'; exists a' => psi' coin' Fpsi' Fpsi'Fpsi'.
	by apply/crt'/Fpsi'Fpsi'; rewrite coin coin'.
apply/leq_trans; last first;
		last apply/(min (fun q => if q == q' then init_seg (mf' q) else init_seg (mf q))).
	by rewrite /=; case: ifP => /eqP // _; exact/melt_iseg.
move => q''; case E: (q'' == q'); last by have [a' crt]:= mod q''; exists a'; exact/crt.
move: E => /eqP ->; 	have [a' crt'] := mod' q'; exists a' => psi' /coin_spec coin' Fpsi' Fpsi'Fpsi'.
exact/crt'/Fpsi'Fpsi'/coin_spec/coin_trans/coin'/coin_subl/coin_sym/coin_spec/coin/iseg_subl.
Qed.

Lemma minmod_cont: (minimal_modulus F) \is_continuous_operator.
Proof.
move => phi [mf mod]; exists (fun q' => init_seg (mf q')); exact/mod_minmod.
Qed.
End minimal_moduli.