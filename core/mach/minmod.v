From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mpf choice_mf.
Require Import all_cont iseg exec Psatz ClassicalChoice.

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

Section minimal_moduli.
Context (Q: countType) (Q': eqType) (noq: Q) (noq_spec: pickle noq = 0) (A A': Type).
Notation B := (Q -> A).
Notation B' := (Q' -> A').
Context (F: B ->> B').
Notation init_seg := (iseg noq).

Definition minimal_modulus S T (F: B ->> (S -> T)) := make_mf (fun phi mf =>
	(continuity_modulus F phi (fun q' => init_seg (mf q')))
	/\
	forall Lf, continuity_modulus F phi Lf -> forall q', mf q' <= max_elt (Lf q')).

Lemma cont_pt_spec: continuity_points F === dom (continuity_modulus F)|_(dom F).
Proof.
by move => phi; split => [[] | [Fphi] []]; [rewrite dom_restr_spec | split; first by exists Fphi].
Qed.

Lemma minmod_minmod phi mf: (minimal_modulus F) phi mf ->
	continuity_modulus (minimal_modulus F) phi (fun q' => init_seg (mf q')).
Proof.
move => [mod min] q'.
exists (mf q') => psi coin mf' [mod' min'].
apply/eqP; rewrite eqn_leq; apply/andP.
case/orP: (leq_total (mf q') (mf' q')) => ineq; split => //.
	apply/leq_trans; last first;
			last apply/(min' (fun q => if q == q' then init_seg (mf q) else init_seg (mf' q))).
		by rewrite /=; case: ifP => /eqP // _; exact/melt_iseg.
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

Lemma minmod_cont: (minimal_modulus F) \is_continuous.
Proof.
move => phi [mf mod]; exists (fun q' => init_seg (mf q')); exact/minmod_minmod.
Qed.

Lemma well_order_nat (P : nat -> Prop):
	(exists n, P n) -> exists n, P n /\ forall m, P m -> n <= m.
Proof.
set R:= (fun n b => P n <-> is_true b).
have [ | p prop]:= choice R.
	by move => n; case: (classic (P n)) => pn; [exists true|exists false]; split.
move => [m Pm].
have ex: exists n, p n by exists m; apply prop.
have [n [pn min]]:= (worder_nat ex).
by exists n; split => [ | k Pk ]; [ | apply min]; apply prop.
Qed.

Lemma dom_minmod: dom (minimal_modulus F) === dom (continuity_modulus F).
Proof.
move => phi; split => [[mf [mod min]] | [Lf mod]]; first by exists (fun q' => init_seg (mf q')).
pose R q' n :=
	(exists a', cert F (L2SS (init_seg n)) phi q' a')
	/\
	forall (Lf': Q' -> seq Q), continuity_modulus F phi Lf' -> n <= max_elt (Lf' q').
have Rtot: forall q', exists n, R q' n.
	move => q'; pose p n := exists a', cert F (L2SS (init_seg n)) phi q' a'.
	have ex: exists n, p n.
		exists (max_elt (Lf q')); have [a' crt]:= (mod q').
		by exists a'; apply/cert_exte/crt; rewrite -L2SS_subs; apply/iseg_melt.
	have [n [prp min]]:= well_order_nat ex.
	exists n; split => // Lf' mod'; apply/min; rewrite /p; have [a' crt]:= mod' q'.
	by exists a'; apply/cert_exte/crt; rewrite -L2SS_subs; apply/iseg_melt.
have [mf mfprop] := choice R Rtot.
exists mf.
by split => [q' | Lf' mod' q']; [exact/(mfprop q').1 | exact/(mfprop q').2].
Qed.
End minimal_moduli.