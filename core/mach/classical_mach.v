From mathcomp Require Import ssreflect ssrfun seq ssrnat ssrbool eqtype.
From rlzrs Require Import all_mf choice_mf.
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

Lemma exists_listf (somea: A) (cnt: nat -> Q) (F: B ->> B'): cnt \is_surjective ->
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

Lemma queriesM_dom (psi: seq A * Q' -> seq Q + A'):
  dom (\F_(M psi)) \is_subset_of dom (\F_(queriesM psi)). 
Proof.
move => phi [Fphi FphiFphi].
suff ch: (forall q', exists L, exists n, queriesM psi n phi q' = Some L) by apply/(choice _ ch).
move => q'; have [n eq]:= FphiFphi q'.
exists (gather_queries psi n phi q').
exists n; move: eq; rewrite /M/queriesM.
by case: (M_rec psi n phi q').
Qed.

Lemma FM_cont (psi: seq A * Q' -> seq Q + A'):
  \F_(M psi) \is_continuous_operator.
Proof.
move => phi /queriesM_dom [mf mod].
by exists mf; apply/queriesM_mod.
Qed.

Lemma FM_val_cont (phi: B): (make_mf (fun psi (Fphi: B') => \F_(M psi) phi Fphi)) \is_continuous_operator.
Proof.
move => psi [Fphi prp].  
have /FM_val_spec FphiFphi: \F_(M psi) phi Fphi by trivial.
suff prp': forall q', exists L, cert (make_mf (fun psi0 => [eta \F_(M psi0) phi])) (L2SS L) psi q' (Fphi q').
- by have [mf cond]:= choice _ prp'; exists mf => q'; exists (Fphi q').
move => q'.
have [Qn com]:= FphiFphi q'.
exists (iseg (fun i => (map phi (flatten (drop i Qn)), q')) (size Qn).+1).
move => psi'/coin_spec coin Fphi' /= /FM_val_spec FphiFphi'.
have [Qn' [/=cns' val']]:= FphiFphi' q'.
have:= cmcn_unique com .
suff: (Qn, Fphi q') = (Qn', Fphi' q') by case.
apply/cmcn_unique.
- apply/com.
suff eq: Qn = Qn'.
- rewrite -eq.
  split => /=; first by apply com.1.
  rewrite eq.
  move: coin; rewrite coin_lstn => coin.
  rewrite coin // lstn_iseg.
  by exists 0; split => //; rewrite drop0 eq.            
case/orP: (leq_total (size Qn) (size Qn')) => ineq.
- by apply/cns_rec/cns'/com.1=>//; exact/com.2.
symmetry.
apply/cns_rec/com.1/cns' => //; try apply/val'.
apply/coin_sym.
apply/coin_subl/coin.
move => pr /lstn_iseg [n [ineq' eq]].
apply/lstn_iseg; exists (n + (size Qn - size Qn')).
rewrite -drop_drop.
split.
- rewrite -{2}(subnK ineq).
  rewrite [_ + size Qn']addnC -[X in _ < X]addSn.
  by rewrite ltn_add2r.
suff ->: drop (size Qn - size Qn') Qn = Qn' by trivial. 
apply/cns_eq/cns'; last first; last by rewrite size_drop subKn.
move => i.
rewrite size_drop subKn// => ils.
have [ | K [] ]//:= com.1 (i + size Qn - size Qn').
- rewrite /= -[X in _ < X](subnK ineq) [_ + size Qn']addnC -addnBA//.
  by rewrite ltn_add2r.
exists K.
rewrite !drop_drop addSn addnBA//; split => //.
move: coin; rewrite coin_lstn => coin; rewrite -coin//.
apply/lstn_iseg.
exists (i + size Qn - size Qn').+1.
split => //.
rewrite -addnBA // -[X in _ < X.+1](subnK ineq) addnC.
by have: (size Qn - size Qn' + i) < (size Qn - size Qn' + size Qn') by rewrite ltn_add2l.
apply/coin_sym/coin_subl/coin.
move => Kq' /lstn_iseg [k []].
rewrite size_drop subKn // => a <-.
apply/lstn_iseg.
exists (k.+1 + (size Qn - size Qn')).   
rewrite drop_drop; split => //.
rewrite addSn.
have: (size Qn - size Qn' + k) < (size Qn - size Qn' + size Qn') by rewrite ltn_add2l.
by rewrite subnK//addnC.
Qed.
End classical_machines.