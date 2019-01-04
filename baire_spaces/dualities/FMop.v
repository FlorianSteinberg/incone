(* This file provides an abstract envelope for computability theoretical considerations *)
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype choice.
From rlzrs Require Import all_mf.
Require Import iseg.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FM_operator.
Context (A A' Q Q': Type).
Notation B := (Q -> A).
Notation B' := (Q' -> A').
Notation "B o~> B'" := (nat -> B -> Q' -> option A') (at level 2).

Definition operator (M: B o~> B') :=
	make_mf (fun phi Mphi => forall q', exists c, M c phi q' = Some (Mphi q')).

Notation "\F_ M" := (operator M) (format "'\F_' M", at level 2).


Notation "M '\evaluates_to' F" := ((\F_M) \tightens F) (at level 40).

Lemma eval_FM M: M \evaluates_to \F_M.
Proof. done. Qed.

Lemma exte_sym_F2MF S T (f: S ->> T) g:
	f \is_singlevalued -> f \extends (F2MF g) -> (F2MF g) \extends f.
Proof. by move => sing exte s t fst; rewrite (sing s t (g s)) => //; apply exte. Qed.

Lemma eval_F2MF M F:
	M \evaluates_to (F2MF F) <-> \F_M =~= F2MF F.
Proof.
split => [eval | <-] //; rewrite exte_equiv; split; first exact/sing_tight_exte/eval/F2MF_sing.
move => s t fst; apply /(tight_val eval)/fst/F2MF_tot.
Qed.

Lemma F2MF_mach (F: B -> B'):
	(fun n phi q => Some(F phi q)) \evaluates_to (F2MF F).
Proof.
move => phi _; split => [ | Fphi ev]; first by exists (F phi) => q'; exists 0.
by apply functional_extensionality => q'; have [c val]:= ev q'; apply Some_inj.
Qed.

Definition cost_bound cf (M: B o~> B') :=
	forall phi q', exists n a', n <= cf phi q' /\ M n phi q' = Some a'.

Definition monotone_in (M: B o~> B') phi q' :=
	forall n, M n phi q' <> None -> M n.+1 phi q' = M n phi q'.

Lemma mon_in_spec (M: B o~> B) phi q': monotone_in M phi q' <->
	forall a' n m, n <= m -> M n phi q' = Some a' -> M m phi q' = Some a'.
Proof.
split => [mon a' n m | mon n neq]; last by case E: (M n phi q') neq=>[a' | ]// _; apply/mon/E. 
elim: m => [ineq eq | m ih]; first by have/eqP <-: n == 0 by rewrite -leqn0.
rewrite leq_eqVlt; case/orP => [/eqP <- | ineq eq]//.
by rewrite mon => //; rewrite ih; rewrite /pickle /=.
Qed.

Lemma mon_in_eq M phi q' n m a' b':
	monotone_in M phi q' -> M n phi q' = Some a' -> M m phi q' = Some b' -> a' = b'.
Proof.
case/orP: (leq_total n m) => ineq /mon_in_spec mon eq eq'; apply /Some_inj.
	by rewrite -eq'; symmetry; apply/mon/eq.
by rewrite -eq; apply/mon/eq'.
Qed.

Definition monotone M:= make_subset (fun phi => forall q', monotone_in M phi q').
Notation "M '\is_monotone'" := ((dom \F_M) \is_subset_of (monotone M)) (at level 2).

Lemma mon_spec (M: B o~> B'): M \is_monotone <-> forall phi q' a' n m,
	phi \from dom \F_M -> n <= m -> M n phi q' = Some a' -> M m phi q' = Some a'.
Proof.
split => [mon phi q' a' n m phifd| mon phi phfd q'].
	have /mon_in_spec prp: monotone_in M phi q' by apply/mon.
	exact/prp.
by rewrite mon_in_spec => a' n m ineq eq; apply/mon/eq.
Qed.

Lemma mon_sing_restr M: \F_M|_(monotone M) \is_singlevalued.
Proof.
move => phi Fphi Fphi' [mon FphiFphi] [_ FphiFphi'].
apply functional_extensionality => q'.
have [c eq]:= FphiFphi q'.
have [d eq']:= FphiFphi' q'.
exact/mon_in_eq/eq'/eq/mon.
Qed.

Lemma mon_sing (M: B o~> B):
	M \is_monotone -> \F_M \is_singlevalued.
Proof. by move => mon; rewrite -(restr_dom \F_M); exact/restr_sing/mon_sing_restr. Qed.

Lemma mon_eval M F: M \is_monotone -> F \is_singlevalued ->
	M \evaluates_to F <-> \F_M \extends F.
Proof.
move => mon sing; split => [eval | eval]; first exact/sing_tight_exte.
exact/exte_tight/eval/mon_sing.
Qed.

Definition right_away (M: B o~> B') phi :=	make_mf (fun q' a' =>
		M 0 phi q' = some a').

Lemma ra_sing M phi: (right_away M phi) \is_singlevalued.
Proof. by move => q' a' b' /=eq1 eq2; apply/Some_inj; rewrite -eq1 -eq2. Qed.

Definition static (M: B o~> B') phi:= make_mf (fun q a =>
	forall c, M c phi q = some a).

End FM_operator.
Notation "\F_ M" := (operator M) (format "'\F_' M", at level 2).
Notation "M '\evaluates_to' F" := (\F_M \tightens F) (at level 2).
Notation "M '\is_monotone'" := (dom \F_M \is_subset_of (monotone M)) (at level 2).
Notation "cf '\bounds_cost_of' M" := (cost_bound cf M) (at level 2).
