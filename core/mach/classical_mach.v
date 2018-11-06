From mathcomp Require Import ssreflect ssrfun seq ssrnat ssrbool eqtype.
From mpf Require Import all_mpf choice_mf.
Require Import all_cont classical_count classical_cont exec Mmach.
Require Import ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section classical_machines.
Context (Q Q' A A': Type).
Notation B := (Q -> A).
Notation B' := (Q' -> A').

Lemma mach_choice M (phi: B):
	(forall (q': Q'), exists (a': A') n, M n phi q' = Some a') -> phi \from dom \F_M.
Proof. by move => Rtot; have [Fphi FphiFphi]:= choice _ Rtot; exists Fphi. Qed.

Lemma sing_cmpt_elt M F c (phi: B) (Fphi: B') q' a': M \evaluates_to F -> F \is_singlevalued ->
	F phi Fphi -> M c phi q' = Some a' -> a' = Fphi q'.
Proof.
move => comp sing FphiFphi ev.
have [ | [Mphi MphiFphi] prop]:= (comp phi _); first by exists Fphi.
have eq: Mphi = Fphi by rewrite -(sing phi Fphi Mphi); last apply prop.
move: Mphi eq MphiFphi => _ -> MphiFphi.
pose Nphi := (fun q a => (q <> q' /\ Fphi q = a) \/ (q' = q /\ a' = a)).
have [q | Mphi Mphiprop]:= choice Nphi.
	by case: (classic (q = q')) => ass; [exists a'; right | exists (Fphi q); left].
have MphiMphi: (\F_M) phi Mphi => [q | ].
	by case: (Mphiprop q) => [[_ <-] | [<- <-]]; [ | exists c].
apply Some_inj; case: (Mphiprop q') => [[ctr] | [_ ->]] //.
by have <-: Mphi = Fphi by apply/ sing; apply prop.
Qed.

Lemma FM_dom_spec (psi: seq A * Q' -> seq Q + A') (phi: B):
	phi \from dom \F_(M psi) <-> (communication psi phi) \is_total.
Proof.
split => [[Fphi /FM_val_spec FphiFphi] q' | tot].
	by have [Ln prp]:= FphiFphi q'; exists (Ln, (Fphi q')).
have [LnFphi prp]:= choice _ tot.
exists (fun q' => (LnFphi q').2); rewrite FM_val_spec => q'.
by exists (LnFphi q').1; exact/(prp q').
Qed.

Lemma exists_listf (somea: A) (cnt: nat -> Q) (F: B ->> B'): cnt \is_surjective_function ->
	exists listf, 	forall phi n, phi \from dom F ->
		listf (map phi (iseg cnt n)) \from dom F /\
		(listf (map phi (iseg cnt n))) \and phi \coincide_on (iseg cnt n).
Proof.
move => sur; have [sec min]:= exists_minsec sur.
pose R := make_mf (fun L psiL =>
	(exists phi, phi \from dom F /\ map phi (iseg cnt (size L)) = L) ->
	(psiL \from dom F /\ map psiL (iseg cnt (size L)) = L)).
have Rtot: R \is_total.
	move => L.
	case: (classic (exists phi, phi \from dom F /\ 
		(map phi (iseg cnt (size L)) = L))) => [[psil [fd eq]] | neg]; first by exists psil.
	by exists (fun _ => somea) => cntr; exfalso; apply neg.
have [listf listfprp]:= choice _ Rtot.
exists listf => phi n phifd.
have [ | fd eq]:= listfprp (map phi (iseg cnt n)).
	by exists phi; split => //; rewrite !size_map !size_iseg.
move: eq; rewrite size_map size_iseg; split => //; move: fd => _.
rewrite coin_lstn => q lstn.
have [m [ineq <-]]:= iseg_ex lstn.
have: nth (phi (cnt 0)) ([seq listf [seq phi i | i <- iseg cnt n] i | i <- iseg cnt n]) (n - m).-1 =
	nth (phi (cnt 0)) ([seq phi i | i <- iseg cnt n]) (n - m).-1.
	by rewrite eq.
rewrite !(nth_map (cnt 0));
	try by case: (n) ineq =>// n' ineq; rewrite size_iseg subSn //=; have: n' - m <= n' by rewrite leq_subr.
rewrite nth_iseg; suff ->: (n - (n - m).-1).-1 = m by trivial.
case: n eq ineq lstn => //n eq ineq lstn.
by rewrite !subSn //; [ rewrite subKn | rewrite leq_subr].
Qed.

Lemma M_universal (someq: Q) (somea : A) (somephi': B') (F: B ->> B'):
 	Q \is_countable -> F \is_continuous_operator -> exists psiF, (M psiF) \evaluates_to F.
Proof.
have [eqQ' _]:= classic_eqClass Q'.
set Q'eqType:= EqType Q' eqQ'.
move => count cont.
have [ | cnt sur]//:= (count_sur Q).2.
have [Ff Fprop] := exists_choice (F: _ ->>(Q'eqType -> _)) somephi'.
have [sec ms] := exists_minsec sur.
have [mf mfmod]:= exists_minmod ms (cont: (F: _ ->> (Q'eqType -> _)) \is_continuous_operator).
have [listf listfprop] := exists_listf somea (F: _ ->> (Q'eqType -> _)) sur.
exists (psiF cnt listf mf Ff).
rewrite mon_eval; last exact/cont_sing; last exact/M_mon.
move => phi Fphi FphiFphi.
have phifd: phi \from dom F by exists Fphi.
apply/(MpsiF_spec phifd) => //; try by move => n; have []:= listfprop phi n phifd.
	move => q' n ineq.
	have [a' crt]:= mod_minmod ms (mfmod phi phifd) q'.
	rewrite [mf phi q'](crt phi) //.
	have -> //:= crt (listf (map phi (iseg cnt n))) _ (mf (listf (map phi (iseg cnt n)))).
			have [_ coin]:= listfprop phi n phifd.
			by rewrite -coin_spec; apply/coin_sym/coin_subl/coin/iseg_subl.
		by apply/mfmod; have []:= listfprop phi n phifd.
	exact/mfmod.
by move => psi psifd; have [mod min]:= mfmod psi psifd.
Qed.
End classical_machines.