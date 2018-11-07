(* This file provides an abstract envelope for computability theoretical considerations *)
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype choice.
From rlzrs Require Import all_mf.
Require Import iseg.
Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section oracle_computation.
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


(*
Let op (M: B o~> B') (c: fuel) phi q n:= if n < (pickle c) then
	match (pickle_inv fuel n) with
		| None => false
		| Some c' => match M c' phi q with
			| None => false
			| Some a => true
		end
	end
else true.

Lemma op_spec M c phi q' n:
	op M c phi q' n -> n < pickle c -> exists (c': fuel), pickle c' = n.
Proof.
rewrite /op; case: ifP => //.
case E: (pickle_inv fuel n) => [c' | ] ineq => //.
by case: (M c' phi q') => //; exists c'; rewrite -(pickle_invK fuel n) E.
Qed.

Lemma op_search M c phi q':
	exists (c': fuel), pickle c' = search (op M c phi q') (pickle c).
Proof.
pose r c phi q' := search (op M c phi q') (pickle c).
case E: (r c phi q' == pickle c); first by exists c; apply /esym/eqP; rewrite E.
have ineq: r c phi q' < pickle c.
	by rewrite ltn_neqAle; apply /andP; split; [rewrite E | apply/search_le].
by apply/(@op_spec M c _ q') => //; apply search_correct; rewrite /op pickleK_inv (ltnn (pickle c)).
Qed.

Definition oracle_use_first M c phi q := match (pickle_inv fuel (search (op M c phi q) (pickle c))) with
	| None => None
	| Some c' =>  M c' phi q
end.

Lemma oracle_use_first_mon M: (oracle_use_first M) \is_monotone.
Proof.
move => phi phifd q' a' n m ineq evl.
case E: (pickle n < pickle m)%N.
	have[c rneqc]:= op_search M n phi q'.
	have[c' rmeqc']:= op_search M m phi q'.
	rewrite /oracle_use_first -rneqc pickleK_inv in evl.
	pose r m phi q' := search (op M m phi q') (pickle m).
	have rmlrn: r m phi q' <= r n phi q'.
		by apply/search_min; rewrite /op /r -rneqc pickleK_inv evl; case: ifP.
	suffices rnlrm: r n phi q' <= r m phi q'.
		have /eqP eq: r m phi q' == r n phi q' by rewrite eqn_leq; apply /andP.
		by rewrite /r in eq; rewrite /oracle_use_first eq -rneqc pickleK_inv.
	apply/search_min; rewrite /op/r -rmeqc' pickleK_inv; case: ifP => // ha.
	have: (op M m phi q' (r m phi q')).
		by rewrite search_correct => //; rewrite /op/r; case: ifP => //; rewrite (ltnn (pickle m)).
	rewrite /op/r -rmeqc' pickleK_inv; case: ifP => [ | <- _]; case: (M c' phi q') => //.
	by apply/leq_trans; first apply/ ha; apply/leq_trans; [apply: ineq | apply/ leqnn].
have ineq': pickle m <= pickle n by rewrite leqNgt E.
rewrite -evl; f_equal; apply Some_inj; rewrite -!pickleK_inv; f_equal.
by apply/eqP; rewrite eqn_leq; apply /andP.
Qed.

Lemma oracle_use_first_crct M F: M \evaluates_to F -> F \is_singlevalued
	-> (oracle_use_first M) \evaluates_to F.
Proof.
move => comp sing.
pose r (c: fuel) phi q':= search (op M c phi q') (pickle c).
rewrite mon_eval => // phi Fphi FphiFphi q'; last exact: oracle_use_first_mon.
have phifd: phi \from dom F by exists Fphi.
have [[Mphi MphiMphi] prop]:= comp phi phifd.
have [c val]:= MphiMphi q'.
have pqrc: op M c phi q' (r c phi q').
	apply search_correct; rewrite /op.
	by case: ifP => // _; rewrite pickleK_inv val.
have [c' uprcq]:= op_search M c phi q'.
rewrite /op /r -uprcq in pqrc.
case E: (pickle c' < pickle c)%N pqrc.
	rewrite pickleK_inv.
	case E': (M c' phi q') => // _.
	exists c; rewrite /oracle_use_first -uprcq pickleK_inv.
	by rewrite -(sing_cmpt_elt comp sing FphiFphi E').
move => _.
have eq: c' = c.
	suffices eq: pickle c' = pickle c by apply Some_inj; rewrite -!pickleK_inv -eq.
	have ineq: pickle c' <= pickle c by rewrite uprcq; apply/search_le.
	by apply/eqP; rewrite eqn_leq; apply/andP; split => //; rewrite leqNgt E.
exists c; rewrite /oracle_use_first -uprcq pickleK_inv eq (sing phi Fphi Mphi) => //.
by apply prop.
Qed.

Lemma mon_sing_cmpt_op M (F: B ->> B'):
	F \is_singlevalued -> M \evaluates_to F -> {K | K \is_monotone /\ K \evaluates_to F}.
Proof.
move => sing cmpt; exists (oracle_use_first M); split.
	exact: oracle_use_first_mon.
exact: oracle_use_first_crct.
Qed.

(*
Definition mon_comp N N' n phi q := match (oracle_use_first N') n phi q with
	|None => None
	|some q' => N n phi q'
end.

Lemma cmpt_comp Q':
	{K | forall N N' (f: Q' ->> A) (g: Q ->> Q'), N \evaluates_to f -> N' \evaluates_to g -> (K N N') \evaluates_to (f o g)}.
Proof.
exists (fun (N: fuel -> Q' -> option A) (N': fuel -> Q -> option Q') n q => ).
move => N N' f g Ncomp N'comp.
move => q [a't [[q't [gqq't fq'ta't]] prop]].
have qfd: q \from_dom g by exists q't.
split => [ | a' [/= c evl]]; last first.
	split; last by intros; apply prop.
	case E: (N' c q) evl => [q' | ] // evl.
	exists q'; split; first by apply/ (N'comp q qfd).2; exists c.
	apply/ (Ncomp q' _).2; last by exists c.
	by apply prop; apply N'comp; [exists q't | exists c].
have [[q' [c evl]] prop']:= (N'comp q qfd).
have [ | [a' [c' val']] prop'']:= (Ncomp q' _); first by apply/prop/prop'; exists c.
exists a'; case E: (pickle c' <= pickle c)%N.
	admit.
(* 	by exists c; rewrite evl; apply/ Mmon; last apply val'; first rewrite E. *)
admit. 
(* exists c'; suffices ->: N' c' q = Some q' => //; apply/ N'mon; last exact: evl. *)
(* by apply /leq_trans; [exact: leqnSn | rewrite ltnNge E]. *)
Qed.

Lemma cmpt_op_rec_fun f (F: B ->> B') M:
	f \from dom F -> M \oracle_evaluates_to F -> F \is_singlevalued
	-> exists (N: fuel -> Q' -> option A'),
		N \evaluates_to (make_mf (fun q' a' => exists Ff, F f Ff /\ (Ff q') = a')).
Proof.
move => fd comp' sing.
pose N c q' := oracle_use_first M c f q'; exists N.
have Nmon: N \does_not_revise by rewrite /N => c c' q a; apply/oracle_use_first_mon.
apply/ra_cmpt_cmpt => //.
	by move => q a a' [Ff [H <-]] [Ff' [H0 <-]]; rewrite (sing f Ff Ff').
have comp := oracle_use_first_crct comp' sing.
have [[Mf MfMf] prop]:= (comp f fd) => q' a' []Ff[]; have [c val]:= (MfMf q').
by exists c; rewrite /N -b val; f_equal; apply/sing_cmpt_elt; [apply /comp | | | apply val].
Qed.*)
*)
Definition right_away (M: B o~> B') phi :=	make_mf (fun q' a' =>
		M 0 phi q' = some a').

Lemma ra_sing M phi: (right_away M phi) \is_singlevalued.
Proof. by move => q' a' b' /=eq1 eq2; apply/Some_inj; rewrite -eq1 -eq2. Qed.

Definition static (M: B o~> B') phi:= make_mf (fun q a =>
	forall c, M c phi q = some a).

End oracle_computation.
Notation "\F_ M" := (operator M) (format "'\F_' M", at level 2).
Notation "M '\evaluates_to' F" := (\F_M \tightens F) (at level 2).
Notation "M '\is_monotone'" := (dom \F_M \is_subset_of (monotone M)) (at level 2).
Notation "cf '\bounds_cost_of' M" := (cost_bound cf M) (at level 2).
