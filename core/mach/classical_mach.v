From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mpf choice_mf.
Require Import all_cont classical_cont exec Mmach.
Require Import ClassicalChoice FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section COUNTABILITY.
Definition is_count Q :=
	exists cnt: nat -> option Q, cnt \is_surjective_function.
Notation "T '\is_countable'" := (is_count T) (at level 2).

Lemma classic_eqClass Q : exists P : Equality.class_of Q, True.
Proof.
have /choice[eq eqP]: forall q, exists b, (q.1 = q.2 :> Q) <-> (b = true).
  by move=> q; case: (classic (q.1 = q.2)) => ass; [exists true|exists false].
unshelve eexists (@Equality.Mixin _ (fun x y => eq (x, y)) _) => //.
by move=> x y; apply: (iffP idP) => [/eqP//|->]; apply/eqP.
Qed.

Lemma count_countMixin Q : Q \is_countable ->
  exists P : Countable.mixin_of Q, True.
Proof.
move => [cnt sur]; have [sec [issec min]] := minimal_section sur.
unshelve eexists (@Countable.Mixin _ (sec \o some) cnt _) => //.
by move=> x /=; rewrite issec.
Qed.

Lemma count_countClass Q  : Q \is_countable ->
  exists P : Countable.class_of Q, True.
Proof.
move=> /count_countMixin[cmQ _]; have [eqQ _] := classic_eqClass Q.
set QeqType := EqType Q eqQ.
set QchoiceType := ChoiceType QeqType (CountChoiceMixin cmQ).
by exists (Countable.class (CountType QchoiceType cmQ)).
Qed.

Lemma countMixin_count T : Countable.mixin_of T -> T \is_countable.
Proof.
move=> [pickle unpickle pickleK].
exists (fun n => if n isn't n.+1 then None else unpickle n).
move=> [x|]; last by exists 0.
by exists (pickle x).+1; rewrite pickleK.
Qed.

Lemma countType_count (T : countType) : T \is_countable.
Proof. by apply: countMixin_count; case: T => [?[]]. Qed.

Lemma nat_count: nat \is_countable.
Proof. exact: countType_count. Qed.

Lemma option_count T : T \is_countable -> (option T) \is_countable.
Proof.
move=> /count_countClass [cT _]; set T' : Type := Countable.Pack cT T.
by rewrite -[T]/T'; apply: countType_count.
Qed.

Lemma sum_count Q Q': Q \is_countable -> Q' \is_countable ->
  (Q + Q') \is_countable.
Proof.
move=> /count_countClass [cQ _]; set QC : Type := Countable.Pack cQ Q.
move=> /count_countClass [cQ' _]; set Q'C : Type := Countable.Pack cQ' Q'.
by rewrite -[Q]/QC -[Q']/Q'C; apply: countType_count.
Qed.

Lemma prod_count Q Q':
  Q \is_countable -> Q' \is_countable -> (Q * Q') \is_countable.
Proof.
move=> /count_countClass [cQ _]; set QC : Type := Countable.Pack cQ Q.
move=> /count_countClass [cQ' _]; set Q'C : Type := Countable.Pack cQ' Q'.
by rewrite -[Q]/QC -[Q']/Q'C; apply: countType_count.
Qed.

Lemma list_count Q: Q \is_countable -> (list Q) \is_countable.
Proof.
move=> /count_countClass [cQ _]; set QC : Type := Countable.Pack cQ Q.
by rewrite -[Q]/QC; apply: countType_count.
Qed.

Lemma count_sur Q: (exists cnt: nat -> Q, cnt \is_surjective_function) <-> inhabited Q /\ Q \is_countable.
Proof.
split => [ [cnt sur] | [[someq [cnt sur]]]].
	split; first exact (inhabits (cnt 0)).
	exists (fun n => match n with
		| 0 => None
		| S n' => Some (cnt n')
	end).
	move => q.
	case: q; last by exists 0.
	move => q.
	have [n val] := sur (q).
	by exists (S n); rewrite val.
exists (fun n => match cnt n with
	| None => someq
	| Some q => q
end) => q.
have [n val] := sur (some q).
by exists n; rewrite val.
Qed.
End COUNTABILITY.
Notation "T '\is_countable'" := (is_count T) (at level 2).

Section classical_machines.
Context (Q Q' A A': Type).
Notation B := (Q -> A).
Notation B' := (Q' -> A').

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
move => sur; have [sec min]:= minimal_section sur.
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
have [sec ms] := minimal_section sur.
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