From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mpf choice_mf.
Require Import all_cont choice iseg exec.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section universal_machine.
(* Q: Questions, A: Answers *)
Context (Q Q' A A' : Type).
(* B: Baire space *)
Notation B := (Q -> A).
Notation B' := (Q' -> A').
Notation "? K" := (@inl (list Q) A' K) (format "'?' K", at level 50).
Notation "! a'" := (@inr (list Q) A' a') (format "'!' a'", at level 50).

Definition M_step (psi: list A * Q' -> list Q + A') phi q' L :=
match psi (L, q') with
  | inr a' => inr a'
  | inl K => inl ((map phi K) ++ L)
end.

Fixpoint M_rec (psi: list A * Q' -> list Q + A') n phi q' :=
match n with
	|	0 => M_step psi phi q' nil
	|	S n' => match M_rec psi n' phi q' with
	  | inr a' => inr a'
		| inl L => M_step psi phi q' L
	end
end.

Definition M
	(psi: list A * Q' -> list Q + A')
	(n: nat)
	(phi: Q -> A)
	(q' : Q') :=
match M_rec psi n phi q' with
	| inr a' => Some a'
	| inl L => None
end.

Lemma M_mon psi:
	(M psi) \is_monotone.
Proof. by move => phi phifd q' n; rewrite/M/=; case E: (M_rec psi n phi q'). Qed.

Lemma M_rec_step n psi phi q':
	M_rec psi n.+1 phi q' = match M_rec psi n phi q' with
	  | inr a' => inr a'
		| inl L => M_step psi phi q' L
	end.
Proof. done. Qed.

Lemma M_rec_inl_spec psi n phi q' L:
	M_rec psi n phi q' =  inl L <-> exists (Ln: list (list A)),
		size Ln = n.+1 /\ L = flatten Ln /\
		forall i, i < n.+1 -> exists K,
			psi (flatten (drop i.+1 Ln), q') = ? K /\
			flatten (drop i Ln) = map phi K ++ flatten (drop i.+1 Ln).
Proof.
split.
	elim: n L => [L | /= n]; first rewrite /=/M_step.
		case E: (psi (nil, q')) => [K | ]//; rewrite cats0 => [[]] eq.
		exists [:: L]; split => //; split => [ | i ineq]; first by rewrite /= cats0.
		exists K; split => //; have /eqP ->: i == 0 by rewrite -leqn0.
		by rewrite /= eq.
	case E: (M_rec psi n phi q') => [L' | ] // ih L /=.
	have [ | Ln [sze [eq prp E']]]//:= ih L'.
	move: E'; rewrite /M_step; case val: (psi (L', q')) => [K | ]// [E'].
	exists (map phi K :: Ln); split => //=; first by rewrite sze.
	split; first by rewrite -eq E'.
	case => [_ | i ineq]; last exact/prp.
	by exists K; rewrite drop0 /=; split; first by rewrite -eq.
elim: n L => [_ [Ln [sze [-> prp]]]/= | /= n ih _ [Ln [sze [-> prp]]]].
	have [ | K [ ]]//:= prp 0; rewrite drop1 drop0.
	have -> /=: (behead Ln) = [::] by apply/size0nil; rewrite size_behead sze.
	by rewrite !cats0 /M_step => -> ->/=; rewrite cats0.
rewrite (ih (flatten (drop 1 Ln))); have [ | K [val ]]//:= prp 0.
	by rewrite drop0 /M_step val => ->.
move => eq; exists (drop 1 Ln); split; first by rewrite size_drop sze.
split => // i ineq; have [ | K']//:= prp i.+1 => [[val' eq']].
by exists K'; split; [rewrite drop_drop -val' addn1 | rewrite !drop_drop !addn1].
Qed.

Definition consistent (psi: _ -> _ + A') (phi: B) (q': Q') Ln := forall i, i < size Ln -> exists K,
			psi (flatten (drop i.+1 Ln), q') = ? K
			/\
			flatten (drop i Ln) = map phi K ++ flatten (drop i.+1 Ln).

Lemma rev_eq T (L L': seq T): rev L = rev L' <-> L = L'.
Proof. by split; first rewrite -{2}(revK L) -{2}(revK L'); move ->. Qed.

Lemma rcons_eq T L L' (a a': T): rcons L a = rcons L' a' <-> L = L' /\ a = a'.
Proof.
split; last by case => -> ->.
by rewrite -(revK (rcons L a)) -(revK (rcons L' a')) rev_eq !rev_rcons => [[-> /rev_eq ->]].
Qed.

Lemma cat_eq_right T (L L' K: seq T): L ++ K = L' ++ K <-> L = L'.
Proof.
elim: K L L' => [L L' | a K ih L L']; [rewrite !cats0 | split => [ | ->]] => //.
by rewrite -!cat_rcons (ih (rcons L a) (rcons L' a)) rcons_eq => [[->]].
Qed.

Lemma cns_eq psi phi q' Ln Ln': size Ln = size Ln' ->
	consistent psi phi q' Ln -> consistent psi phi q' Ln' -> Ln = Ln'.
Proof.
move: {2}(size Ln) (leqnn (size Ln)) => n.
elim: n Ln Ln' => [[[] | []] | n ih [[] | L Ln []]]// L' Ln' ineq [eq] cns cns'.
have eq': Ln = Ln' by rewrite (ih Ln Ln') => //[i ineq' | i ineq']; try exact/cns; try exact/cns'.
rewrite eq'; f_equal.
have [ | K []]//=:= cns 0; rewrite drop0 => val /cat_eq_right ->.
have [ | K' []]//=:= cns' 0; rewrite drop0 => val' /cat_eq_right ->.
by move: val val'; rewrite eq' => -> [->].
Qed.

Lemma cns_rec psi phi q' Ln Ln' a': psi (flatten Ln, q') = ! a' -> size Ln <= size Ln' ->
	consistent psi phi q' Ln -> consistent psi phi q' Ln' -> Ln = Ln'.
Proof.
move => val; elim: Ln' => [ | L' Ln' ih].
	by rewrite leqn0 => /eqP eq; rewrite (size0nil eq).
rewrite leq_eqVlt; case /orP => [/eqP eq | ineq cns cns'].
	by case: Ln eq ih val => // L Ln eq ih val cns cns'; exact/cns_eq/cns'/cns.
have [ | K [/=]]//:= cns' 0.
have <-: Ln = Ln' by apply/ih => // i ineq'; apply cns'.
by rewrite drop0 val.
Qed.

Definition communication psi (phi: B) := make_mf (fun (q': Q') Lna' =>
	let Ln:= Lna'.1 in let a':= Lna'.2 in consistent psi phi q' Ln /\ psi (flatten Ln, q') = !a').

Lemma cmcn_unique psi phi: (communication psi phi) \is_singlevalued.
Proof.
move => q' [Ln a'] [Ln' b'] [/=cns val] [cns' val'].
case/orP: (leq_total (size Ln) (size Ln')) => ineq.
	by move: val'; have <-:= cns_rec val ineq cns cns'; rewrite val => [[->]].
by move: val; have <-:= cns_rec val' ineq cns' cns; rewrite val' => [[->]].
Qed.

Lemma lstn_nth (L: seq A) Ln: List.In L Ln -> exists n, n < size Ln /\ L = nth nil Ln n.
Proof.
elim: Ln => // K Ln ih /=.
case => [-> | lstn]; first by exists 0.
by have [n []]:= ih lstn; exists n.+1.
Qed.

Lemma FM_val_spec psi phi Fphi: \F_(M psi) phi Fphi <->
	forall q', exists (Ln: list (list A)), communication psi phi q' (Ln, (Fphi q')).
Proof.
split => val q'.
	have [n]:= val q'.
	elim: n => [ | n ih /=]; rewrite /M/=/M_step.
		by case E: (psi (nil, q')) => [ | a']// [eq]; exists nil; rewrite E eq; split.
	case E: (M_rec psi n phi q') => [L | a']; last by move => eq; apply/ih; rewrite /M /= E eq.
	case E': (psi (L, q')) => [ | a']// [eq].
	have [Ln [<- [eq' prp]]]:= (M_rec_inl_spec psi n phi q' L).1 E.
	by exists Ln; split; last by rewrite -eq' E' eq.
have [Ln [eq prp]]:= val q'.
elim: Ln eq prp => [_ /= eq | L Ln ih prp eq/=]; first by exists 0; rewrite/M/=/M_step eq.
exists (size Ln).+1; rewrite /M/=/M_step.
suff ->: M_rec psi (size Ln) phi q' = inl (flatten (L :: Ln)) by rewrite eq.
by apply M_rec_inl_spec; exists (L :: Ln).
Qed.

(*
Lemma FM_dom_spec psi phi:
	phi \from dom \F_(M psi) <-> (communication psi phi) \is_total.
Proof.
split => [[Fphi /FM_val_spec FphiFphi] q' | tot].
	by have [Ln prp]:= FphiFphi q'; exists (Ln, (Fphi q')).
have [LnFphi prp]:= choice _ tot.
exists (fun q' => (LnFphi q').2); rewrite FM_val_spec => q'.
by exists (LnFphi q').1; exact/(prp q').
Qed.
*)

Definition dialogue psi phi := make_mf (fun q' a =>
	exists Lna', communication psi phi q' Lna' /\ List.In a (flatten Lna'.1)).

Lemma dlg_spec psi phi q' a: dialogue psi phi q' a -> 
	forall Ln a', communication psi phi q' (Ln, a') -> List.In a (flatten Ln).
Proof.
by move => [[Ln a'] [com lstn]] Ln' b' com'; have [<-]:= (cmcn_unique com com').
Qed.

End universal_machine.
Section psiF.
Context (Q: countType) (noq: Q) (noq_spec: pickle noq = 0) (Q': eqType) (A A': Type).
Notation B := (Q -> A).
Notation B' := (Q' -> A').
Context (listf: seq A -> B).
Context (mf: B -> Q' -> nat).
Context (FF: B -> B').
Notation init_seg := (iseg noq).
Notation segment :=(segment noq).

Definition psiF (Lq': seq A * Q') := let phi:= listf Lq'.1 in let n:= size Lq'.1 in let q' := Lq'.2 in
	if mf phi q' <= n then inr (FF phi q') else (inl (segment n (mf phi q').-1)).

Lemma psiF_size n phi q' L: M_rec psiF n phi q' = inl L -> n < size L.
Proof.
elim: n L => [L | n ih L /=].
	by rewrite /psiF/=/M_step/=; case E: (mf (listf nil) q') => [ | m /=]; last by move => [<-].
case E: (M_rec psiF n phi q') => [K | ]//.
rewrite /M_step/psiF /=.
case E': (mf (listf K) q' <= size K) => //.
move => [<-].
case eq': (mf (listf K) q') E' => [ | k] //= E'.
rewrite size_cat size_map size_seg subnK; last by rewrite leqW // leqNgt E'.
apply/leq_trans; first by have ineq': n.+1 < (size K).+1; [apply/ih | apply/ineq'].
by rewrite ltnNge E'.
Qed.

Lemma psiF_spec phi q':
	forall n,
		(exists k,
		mf (listf (map phi (init_seg k))) q' <= k
		/\
		M_rec psiF n phi q' = inr (FF (listf (map phi (init_seg k))) q'))
	\/
	forall m, m <= n -> exists k, M_rec psiF m phi q' = inl (map phi (init_seg k)).
Proof.
pose phin m := listf (map phi (init_seg m)).
elim => [ | n ih].
	rewrite /M_rec/M_step/psiF/=.
	case E: (mf (listf [::]) q' <= 0); first by left; exists 0; split.
	right => m; rewrite leqn0 => /eqP ->; rewrite E /=.
	by case S: (mf (listf nil) q') E => [ | n]// _; exists n.+1; rewrite cats0 iseg_seg.
case: ih => [[] m [] ineq | prp].
	by rewrite /M_rec; left; exists m; split; [apply ineq | rewrite /M_rec b].
have [ | k val]//:= prp n.
case E: (mf (listf (map phi (init_seg k))) q' <= k).
	by left; exists k; split =>//=; rewrite val /M_step /psiF/= size_map size_iseg E.
right => m; rewrite leq_eqVlt; case/orP => [/eqP -> /= | le]; last exact/prp.
rewrite val/M_step/psiF/= size_map size_iseg E.
exists (mf (listf [seq phi i | i <- init_seg k]) q').
f_equal; rewrite -map_cat; f_equal; case: k prp E val => [prp E val | k prp E val].
	by rewrite cats0; case: (mf (listf [seq phi i | i <- init_seg 0]) q') E => // h E; rewrite iseg_seg.
by rewrite iseg_cat_seg // ltnNge E.
Qed.

Definition mod_mod mf (phi: B):= continuity_modulus (F2MF mf) phi (fun (q': Q') => init_seg (mf phi q')).

Lemma MpsiF_spec (F: B ->> B'):
	(forall phi n, listf (map phi (init_seg n)) \from dom F) ->
	(forall phi n, (listf (map phi (init_seg n))) \and phi \coincide_on (init_seg n)) ->
	(forall phi q' n, mf (listf (map phi (init_seg n))) q' <= mf phi q') ->
	(forall phi, continuity_modulus F phi (fun q' => init_seg (mf phi q'))) ->
	FF \is_choice_for F ->
		(M psiF) \evaluates_to F.
Proof.
move => listfdom listfcoin listfmod mod icf.
have cont: F \is_continuous by move => phi; exists (fun q' => init_seg (mf phi q')).
apply/mon_eval; [ exact/M_mon | exact/cont_sing | ].
move => phi Fphi FphiFphi q'; pose phin n := (listf (map phi (init_seg n))).
have FFprop: forall n, mf (phin n) q' <= n -> FF (phin n) q' = Fphi q' => [n ineq | ].
	have [a' crt]:= mod (phin n) q'; have [Fphik FphikFphik]:= listfdom phi n.
	rewrite [RHS](crt phi) => //; first by rewrite (crt (phin n)) //; apply/icf/FphikFphik.
	exact/coin_spec/coin_subl/listfcoin/iseg_subl/ineq.
elim: {2}(mf phi q') (leqnn (mf phi q')) => [ | n ih]; last first.
	case: (psiF_spec phi q' n) => [[k [nlk eq]] | prp].
		by exists n.+1; rewrite /M/=eq; f_equal; exact/FFprop/nlk.
	rewrite leq_eqVlt => /orP [/eqP eq| ineq]; last exact/ih.
	have [ | k val]//:= prp n; exists n.+1; rewrite /M/=val/M_step/psiF/=size_map size_iseg.
	suff bnd: mf (listf [seq phi i | i <- init_seg k]) q' <= k by rewrite bnd; f_equal; apply/FFprop.
	apply/leq_trans; first exact/(listfmod phi q').
	by rewrite eq; have:= psiF_size val; rewrite size_map size_iseg.
move => ineq; exists 0; rewrite /M/psiF/=/M_step /=.
have eq': mf (listf nil) q' <= 0 by apply/leq_trans/ineq/leq_trans/(listfmod phi q' 0).
by rewrite eq'; f_equal; apply/(FFprop 0).
Qed.
End psiF.

Lemma U_universal (someq: Q) (somea : A) (somephi': B') (count: Q \is_countable):
	forall F, F \is_continuous -> exists psiF, (U psiF) \oracle_evaluates_to F.
Proof.
have [ | cnt sur]:= (count_sur Q).2.
	by split; [apply (inhabits someq) | apply count].
move => F Fcont.
have [Ff Fprop] := exists_choice F somephi'.
have [sec isminsec] := minimal_section sur.
have [mf [mprop minmod]] := exists_minmod isminsec sur Fcont.
have [listf listfprop] := exists_lstf F somea.
exists (psiF cnt mf listf Ff).
apply/U_psiF_cmpt_F => //.
exact: (minmod_compat isminsec).
Qed.

(* Lemma comp_cont:
  (exists psiF, (fun n phi q' => U n psiF phi q') \type_two_computes F) -> F \is_continuous.
Proof.
move => [] psiF comp phi q'.
case: (classic (phi \from_dom F)) => [] phifd.
move: (comp phi phifd) => [] [] psi ev prop.
move: (ev q') => [] n eq.
Admitted.
*)
End UNIVERSAL_MACHINE.
Notation L2MF L := (mf.Pack (fun q a => List.In (q, a) L)).