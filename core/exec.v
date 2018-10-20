(* This file provides an abstract envelope for computability theoretical considerations *)
From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mpf.
Require Import inseg.
Import FunctionalExtensionality ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section executions.
Context (Q A: Type) (fuel: countType) (zero: fuel).
Notation "Q ~> A" := (fuel -> Q -> option A) (at level 2).

Definition is_val Q A (N: Q ~> A) := make_mf (fun q a => exists c, N c q = some a).
Notation "N '\evaluates_to' f" := ((is_val N) \tightens f) (at level 2).

Definition is_stat_val Q A (N: Q ~> A):= make_mf (fun q a => forall c, N c q = some a).

Lemma val_stat_val (N: Q ~> A): (is_val N) \extends (is_stat_val N).
Proof. by move => q a recval; exists zero. Qed.

Lemma stat_val_sing (N: Q ~> A): (is_stat_val N) \is_singlevalued.
Proof. by move => q a a' vala vala'; have := vala zero; have ->:= vala' zero; case. Qed.

Definition nrev Q A (N: Q ~> A):=
	forall c c' q a, pickle c <= pickle c' -> N c q = Some a -> N c' q = Some a.
Notation "N '\does_not_revise'" := (nrev N) (at level 2).

Lemma	nrev_sing (N: Q ~> A):
	N \does_not_revise -> (is_val N) \is_singlevalued.
Proof.
move => mon q t t' [n ev] [n' ev']; apply Some_inj.
case/orP: (leq_total (pickle n) (pickle n')) => ineq.
	by rewrite -(mon n n' q t _ ev).
by rewrite -ev; apply/ (mon n' n).
Qed.

Lemma ra_cmpt_cmpt (N: Q ~> A) f: f \is_singlevalued ->
	N \does_not_revise -> ((is_val N) \extends  f <-> N \evaluates_to f).
Proof. move => sing /nrev_sing nrev; exact/exte_tight. Qed.

Lemma nrev_cmpt_fun (N: Q ~> A) f: N \does_not_revise ->
	N \evaluates_to (F2MF f) <-> forall q, (is_val N) q (f q).
Proof.
move => /nrev_sing sing; rewrite -exte_tight => //; last exact/ F2MF_sing.
by rewrite /F2MF; split => [/=comp q | prop q a <-]; [apply comp | apply prop].
Qed.

Let p (N: Q ~> A) (c: fuel) q n:= if n < (pickle c) then
match (pickle_inv fuel n) with
	| None => false
	| Some c' => match N c' q with
		| None => false
		| Some a => true
	end
end else true.

Lemma p_spec N c q' n: p N c q' n -> n < pickle c -> exists (c': fuel), pickle c' = n.
Proof.
rewrite /p; case: ifP => // ineq.
case E: (pickle_inv fuel n) => [c' | ]//; case: (N c' q') => // _ _ _.
by exists c'; rewrite -(pickle_invK fuel n) E /=.
Qed.

Lemma p_search N c q: exists (c': fuel), pickle c' = search (p N c q) (pickle c).
Proof.
case E: (search (p N c q) (pickle c) == pickle c); first by exists c; apply /esym/eqP; rewrite E.
have ineq: search (p N c q) (pickle c) < pickle c.
	by rewrite ltn_neqAle; apply /andP; split; [apply/esym/negP; rewrite E |apply search_le].
apply /(@p_spec N c q) => //; apply search_correct.
by rewrite /p pickleK_inv; case: ifP => //;rewrite (ltnn (pickle c)).
Qed.

Definition use_first N c q:= match (pickle_inv fuel (search (p N c q) (pickle c))) with
	| None => None
	| Some c' =>  N c' q
end.

Lemma use_first_nrev: forall N, (use_first N) \does_not_revise.
Proof.
move => N n m q' a' ineq.
case E: (pickle n < pickle m)%N;[move => evl | move <-; f_equal]; last first.
	suffices eq: pickle n = pickle m by apply Some_inj; rewrite -!pickleK_inv eq.
	by apply/eqP; rewrite eqn_leq; apply /andP; split => //; rewrite leqNgt E.
have[c rneqc]:= p_search N n q'.
have[c' rmeqc']:= p_search N m q'.
rewrite /use_first -rneqc pickleK_inv in evl.
pose r c q := search (p N c q) (pickle c).
have rmlrn: r m q' <= r n q'.
	by apply/search_min; rewrite /p/r -rneqc pickleK_inv evl; case: ifP.
suffices rnlrm: r n q' <= r m q'.
	have eq: r m q' = r n q' by apply/eqP; rewrite eqn_leq; apply /andP.
	by rewrite /r in eq; rewrite /use_first eq -rneqc pickleK_inv.
apply/search_min; rewrite /p/r -rmeqc' pickleK_inv; case: ifP => // ha.
have: (p N m q' (r m q')).
	by rewrite search_correct => //; rewrite /p; case: ifP => //; rewrite ltnn.
rewrite /p; have ->: r m q' < pickle m by rewrite /r -rmeqc'; apply /(leq_trans ha).
by rewrite /r -rmeqc' pickleK_inv.
Qed.

Lemma use_first_crct N psi: N \evaluates_to psi -> (use_first N) \evaluates_to psi.
Proof.
move => comp q qfd; split; last first.
	move => a [c Nqa]; apply (comp q qfd).2.
	have [c' rc]:= @p_search N c q.
	by exists (c'); rewrite /use_first -rc pickleK_inv in Nqa.
have [[a [c Mqa]] prop]:= comp q qfd.
pose r c' q':= search (p N c' q') (pickle c').
have: p N c q (r c q).
	by apply search_correct; rewrite /p; case: ifP => //; rewrite pickleK_inv Mqa.
have [c' rc]:= p_search N c q.
rewrite /p /r -rc; case: ifP => ass.
	rewrite pickleK_inv; case E': (N c' q) => [a' | ] // _.
	by exists a'; exists c; rewrite /use_first -/r -rc pickleK_inv.
suffices eq: c' = c by exists a; exists c; rewrite /use_first -/r -rc pickleK_inv eq.
suffices eq: pickle c' = pickle c by apply Some_inj; rewrite -!pickleK_inv -eq.
have ineq: pickle c' <= pickle c by rewrite rc; apply/search_le.
by apply /eqP; rewrite eqn_leq; apply /andP; split; last rewrite leqNgt ass.
Qed.
End executions.
Notation "Q ~> A" := (nat -> Q -> option A) (at level 2).
Notation "M '\does_not_revise'" := (nrev M) (at level 2).
Notation eval N q a := (is_val N q a).
Notation "N '\evaluates_to' f" := ((is_val N) \tightens f) (at level 2).

Section oracle_computation.
Context (A A' Q Q': Type) (fuel: countType) (zero: fuel).
Notation B := (Q -> A).
Notation B' := (Q' -> A').
Notation "B o~> B'" := (fuel -> B -> Q' -> option A') (at level 2).

Definition is_oval (M: B o~> B') :=
	make_mf (fun phi Mphi => forall q', exists c, M c phi q' = some (Mphi q')).

Notation "M '\oracle_evaluates_to' F" := ((is_oval M) \tightens F) (at level 2).

Lemma rec_F2MF_op (F: B -> B'):
	(fun n phi q => Some(F phi q)) \oracle_evaluates_to (F2MF F).
Proof.
move => phi _.
split => [ | Fphi ev].
	by exists (F phi) => q'; exists zero.
apply functional_extensionality => q'.
have [c val]:= ev q'.
by apply Some_inj.
Qed.

Definition is_stat_oval (N: B o~> B') :=
	make_mf (fun phi Nphi => forall c q, N c phi q = some (Nphi q)).

Lemma stat_oval_sing (N: B o~> B'): (is_stat_oval N) \is_singlevalued.
Proof.
move => phi Fphi Fphi' FphiFphi FphiFphi'.
apply functional_extensionality => q'.
by apply Some_inj; rewrite -(FphiFphi zero q') -(FphiFphi' zero q').
Qed.

Definition is_stat_oval' (N: B o~> B') phi q a:= forall c, N c phi q = some a.

Definition is_mon (M: B o~> B):=
	forall c c' phi q' a', pickle c <= pickle c' -> M c phi q' = Some a' -> M c' phi q' = Some a'.
Notation "M '\is_monotone'" := (is_mon M) (at level 2).

Lemma eq_mon M c c' phi q' a' b': M c phi q' = Some a' -> M c' phi q' = Some b' ->
	M \is_monotone -> a' = b'.
Proof.
case/orP: (leq_total (pickle c) (pickle c')) => ineq eq eq' mon; apply /Some_inj.
	by rewrite -(mon c c' phi q' a' ineq) => //.
by apply esym; rewrite -(mon c' c phi q' b' ineq) => //.
Qed.

Lemma mon_sing_op (M: B o~> B):
	M \is_monotone -> (is_oval M) \is_singlevalued.
Proof.
move => mon phi Fphi Fphi' ev ev'; apply functional_extensionality => q'.
by move: (ev q') (ev' q') => [n val] [n' val']; apply /(eq_mon val val').
Qed.

Definition mon_cmpt (M: B o~> B') (F: B ->> B'):=
	forall phi Fphi, F phi Fphi -> (is_oval M) phi Fphi.
Notation "M '\monotone_computes' F" := (mon_cmpt M F) (at level 2).

Lemma cmpt_mon_sing_op M F: M \is_monotone -> F \is_singlevalued ->
	(M \monotone_computes F <-> M \oracle_evaluates_to F).
Proof.
split => [comp phi [] | comp phi]; intros; first (split; first by exists x; apply/ comp).
	by move => y val; have <-: x = y by apply/ mon_sing_op => //; last by apply/ comp.
have [ | [Mphi MphiMphi] prop] := (comp phi _); first by exists Fphi.
by have ->: Fphi = Mphi by apply/ H0; [ | apply prop].
Qed.

Lemma mon_cmpt_op M F:
	M \is_monotone -> M \oracle_evaluates_to (F2MF F) <-> forall phi, (is_oval M) phi (F phi).
Proof.
split => [comp phi q' | prop]; last first.
	apply cmpt_mon_sing_op => //; first exact: F2MF_sing; move => phi Fphi eq q'.
	by have [c val]:= (prop phi q'); exists c; rewrite -eq.
have [ | [Mphi evl] prop]:= (comp phi _); first by exists (F phi).
have [c val] := (evl q'); exists c; rewrite val.
by have ->: Mphi = (F phi) by rewrite (prop Mphi).
Qed.

Lemma sing_cmpt_elt M F c phi Fphi q' a':	M \oracle_evaluates_to F -> F \is_singlevalued ->
	F phi Fphi -> M c phi q' = Some a' -> a' = Fphi q'.
Proof.
move => comp sing FphiFphi ev.
have [ | [Mphi MphiFphi] prop]:= (comp phi _); first by exists Fphi.
have eq: Mphi = Fphi by rewrite -(sing phi Fphi Mphi); last apply prop.
move: Mphi eq MphiFphi => _ -> MphiFphi.
pose Nphi := (fun q a => (q <> q' /\ Fphi q = a) \/ (q' = q /\ a' = a)).
have [q | Mphi Mphiprop]:= choice Nphi.
	by case: (classic (q = q')) => ass; [exists a'; right | exists (Fphi q); left].
have MphiMphi: (is_oval M) phi Mphi => [q | ].
	by case: (Mphiprop q) => [[_ <-] | [<- <-]]; [ | exists c].
apply Some_inj; case: (Mphiprop q') => [[ctr] | [_ ->]] //.
by have <-: Mphi = Fphi by apply/ sing; apply prop.
Qed.

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
move => n m phi q' a' ineq evl.
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

Lemma oracle_use_first_crct M F: M \oracle_evaluates_to F -> F \is_singlevalued
	-> (oracle_use_first M) \oracle_evaluates_to F.
Proof.
move => comp sing.
pose r (c: fuel) phi q':= search (op M c phi q') (pickle c).
rewrite -cmpt_mon_sing_op => // phi Fphi FphiFphi q'; last exact: oracle_use_first_mon.
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
	F \is_singlevalued -> M \oracle_evaluates_to F -> {K | K \is_monotone /\ K \oracle_evaluates_to F}.
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
Qed. *)

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
Qed.

End oracle_computation.
Notation oeval M := (@is_oval _ _ _ _ nat_countType M).
Notation "M '\oracle_evaluates_to' F" := ((is_oval M) \tightens F) (at level 2).
Notation "M '\is_monotone'" := (is_mon M) (at level 2).