From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mpf choice_mf.
Require Import all_cont exec.
Require Import Psatz FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section UNIVERSAL_MACHINE.
(* Q: Questions, A: Answers *)
Context (Q Q': countType) (noq: Q) (noq': Q') (A A' : Type).
(* B: Baire space *)
Notation B := (Q -> A).
Notation B' := (Q' -> A').
Notation init_seg := (iseg noq).
Notation init_seg':= (iseg noq').
Notation "?" := (@inl (seq (Q * A)) A').
Notation "!" := (@inr (seq (Q * A)) A').

Definition U_step (psi : seq (Q * A) * Q' -> seq (Q * nat) + A') phi q' L :=
match psi (L, q') with
  | inr a' => inr a'
  | inl q => inl ((q, phi q) :: L)
end.

Fixpoint U_rec (psi: list (Q * A) * Q' -> Q + A') n phi q':=
match n with
	|	0 => U_step psi phi q' nil
	|	S n' => match U_rec psi n' phi q' with
	  | inr a' => inr a'
		| inl L => U_step psi phi q' L
	end
end.

(* This is the definition of the universal machine: *)
Definition U
	(psi: list (Q * A) * Q' -> Q + A')
	(n: nat)
	(phi: Q -> A)
	(q' : Q') :=
match U_rec psi n phi q' with
	| inr a' => Some a'
	| inl L => None
end.

Lemma U_mon psi: (U psi) \is_monotone.
Proof. by move => phi phifd q' n; rewrite /U/=; case E: (U_rec psi n phi q'). Qed.

Lemma U_rec_step psi n phi q':
	U_rec psi n.+1 phi q' = match U_rec psi n phi q' with
	  | inr a' => inr a'
		| inl L => U_step psi phi q' L
	end.
Proof. done. Qed.

Lemma U_rec_length psi n phi q' L:
	(U_rec psi n phi q') = inl L -> size L = n.+1.
Proof.
move: L.
elim: n => [/= L | n ih L /=]; first by rewrite /U_step; case: (psi ([::],q')) => // q [<-].
case: (U_rec psi n phi q') ih => [K | ] //; rewrite /U_step.
by case: (psi (K, q')) => // q ih [<-] /=; rewrite ih.
Qed.

(* List to multivalued function *)
Notation L2MF L := (make_mf (fun q a => List.In (q, a) L)).

Section FLST.
Context (phi: B).
Definition flst L:= zip L (map phi L).

Lemma flst_cons_elts qa L: List.In qa (flst L) -> phi (qa.1) = qa.2.
Proof. by case: qa => q a; elim: L => // p L ih [] // [<-]. Qed.

Lemma lstn_flst q L: (List.In q L -> List.In (q, phi q) (flst L)).
Proof. by elim: L => //= q' L ih [H|H]; [left; rewrite H | right; apply: ih]. Qed.

Lemma flst_lstn qa L:List.In qa (flst L) -> List.In qa.1 L.
Proof.
by case: qa => q a; elim: L => //= p L ih []; [case; left | right; apply: ih].
Qed.

Lemma icf_flst L:
	phi \is_choice_for (L2MF (flst L)).
Proof.
rewrite icf_F2MF_tight => q [a listin] .
split => [ |a' <-]; first by exists a; apply: flst_cons_elts listin.
by apply /lstn_flst/(flst_lstn listin).
Qed.

Lemma flst_sing L : (L2MF (flst L)) \is_singlevalued.
Proof.
by move=> s t1 t2 /flst_cons_elts /= <- /flst_cons_elts /= <-.
Qed.

Lemma coin_icf_flst psi L:
	psi \is_choice_for (L2MF (flst L))
	<->
	psi \and phi \coincide_on L.
Proof.
rewrite coin_lstn; split => [icf q lstn | prp q a /flst_lstn lstn].
	by rewrite (@flst_cons_elts (q, psi q) L); last by apply/icf/lstn_flst.
by rewrite prp; first apply /lstn_flst.
Qed.

Lemma icf_flst_coin psi L:
	psi \is_choice_for (L2MF(flst L)) <-> psi \and phi \coincide_on L.
Proof. exact: coin_icf_flst. Qed.

Lemma length_flst_in_seg n: size (flst (init_seg n)) = n.
Proof. by rewrite size_zip size_map size_iseg minnn. Qed.

Lemma extend_list (a: A):
	exists listf, forall (L: list (Q * A)), (listf L) \is_choice_for (L2MF L).
Proof.
pose R := (fun (L : list(Q * A)) (phi: Q -> A) => phi \is_choice_for (L2MF L)).
have [ | L]:= choice R; first by move => L; exact: exists_choice (L2MF L) a.
by exists L.
Qed.
End FLST.

Section MINIMAL_MODULI.
Context (F: B ->> B').

Definition listfprop listf :=
	listf \is_choice_for (make_mf (fun L phi => phi \from dom F /\ phi \is_choice_for (L2MF L))).

Lemma exists_lstf (a : A) :
	exists listf, listfprop listf.
Proof. exact: exists_choice. Qed.

Lemma phi'prop listf phi n:
	listfprop listf -> phi \from dom F ->
	(listf (flst phi (init_seg n))) \from dom F
	/\
	(listf (flst phi (init_seg n))) \is_choice_for (L2MF (flst phi (init_seg n))).
Proof.
move => listfprop phifd.
have prop: phi \from dom F/\ phi \is_choice_for (L2MF (flst phi (init_seg n))).
	by split; last exact: icf_flst.
by apply: (listfprop (flst phi (init_seg n)) phi).
Qed.
End MINIMAL_MODULI.

Section PSIF.
Notation init_seg := (iseg noq).
Context (F: B ->> B') (mf: B -> Q' -> nat) (listf: seq (Q * A) -> B) (Ff: B -> B').
Notation L phi m:= (flst phi (init_seg m)).
Notation inverse_pickle := (inverse_pickle noq).

Definition psiF (Lq': seq (Q * A) * Q') :=
	let phi := listf Lq'.1 in let n := size Lq'.1 in let q' := Lq'.2 in
	if (mf phi q' <= n)%N
	then
		(inr (Ff phi q'))
	else
		(inl (inverse_pickle n)).

Lemma psiFprop phi q':
	forall n,
		(exists m,
		mf (listf (flst phi (init_seg m))) q' <= m
		/\
		U_rec psiF n phi q' = inr (Ff (listf (flst phi (init_seg m))) q'))
	\/
	forall m, m <= n ->
	U_rec psiF m phi q' = inl (flst phi (init_seg (S m))).
Proof.
pose phin m := listf (L phi m).
elim => [ | n ih].
	rewrite /U_rec/U_step/psiF/=.
	case E: (mf (listf [::]) q' <= 0); first by left; exists 0; split.
	by right => m ineq; have /eqP ->: m == 0; [rewrite -leqn0 | rewrite E].
case: ih => [[] m [] ineq | eq].
	by rewrite /U_rec; left; exists m; split; [apply ineq | rewrite /U_rec b].
case E: (mf (listf (flst phi (init_seg n.+1), q').1) (flst phi (init_seg n.+1), q').2 <= n.+1).
	left; exists (n.+1);rewrite /U_rec in eq;rewrite /U_rec eq =>//.
	by rewrite /U_step/psiF length_flst_in_seg; split; last rewrite E.
right => m; rewrite  leq_eqVlt; case/orP => [/eqP nm | le]; last by rewrite -eq.
have eq': U_rec psiF n phi q' = inl (flst phi (init_seg n.+1)) by apply eq.
by rewrite /U_rec in eq'; rewrite /U_rec nm eq'/U_step/psiF length_flst_in_seg E.
Qed.

Definition Ff_mod phi q' :=
	forall m, mf (listf (L phi m)) q' <= m -> Ff (listf (L phi m)) q' = Ff phi q'.

Lemma Ffprop (icf: Ff \is_choice_for F) (lstprp: listfprop F listf) phi: phi \from dom F ->
	continuity_modulus F phi (fun q' => init_seg (mf phi q')) -> forall q', Ff_mod phi q'.
Proof.
move => [Fphi FphiFphi] mod q' m ineq.
have [ | [Flphi FlphiFlphi] /icf_flst_coin coin]:= @phi'prop _ _ phi m lstprp; first by exists Fphi.
have [a' crt]:= mod q'.
have crt': cert F (L2SS (init_seg (mf phi q'))) phi q' (Ff phi q').
	by apply/cert_icf/crt/icf/FphiFphi.
apply/crt'/icf/FlphiFlphi/coin_spec/coin_sym/coin_subl/coin/iseg_subl.
apply/leq_trans/ineq.

Admitted.

Lemma U_step_compat phi q' (cmpt: compat F cnt mf listf):
	phi \from dom F -> Ff_mod phi q' -> U_step psiF phi q' (L phi (mf phi q')) = inr (Ff phi q').
Proof.
move => phifd Ffprop.
rewrite /U_step/psiF/=length_flst_in_seg; case: ifP => [|/negP eq].
	by rewrite Ffprop; last by apply/cmpt.
by exfalso; apply eq; apply/cmpt.
Qed.

Lemma U_psiF_cmpt_F
	(sur: cnt \is_surjective_function)
	(icf: Ff \is_choice_for F)
	(mod: (fun phi q' => init_seg (mf phi q')) \is_modulus_of F)
	(lstprp: listfprop F listf)
	(cmpt: compat F cnt mf listf):
		(U psiF) \evaluates_to F.
Proof.
move => phi phifd.
pose phin m := listf (L phi m).
have phinprop m:= (phi'prop cnt m lstprp phifd).
have coin m: (phin m) \and phi \coincide_on (init_seg m) by apply/icf_flst_coin/(phinprop m).2.
pose phi' q' := phin (mf phi q').

have U_stops q': U psiF (mf phi q') phi q' = some (Ff phi q').
	rewrite /U.
	case: (psiFprop phi q'(mf phi q'))=> [ [] m []ineq eq | eq].
		by rewrite eq; congr some; rewrite (Ffprop).
	case E: (mf phi q') => [ | m].
		have eq': flst phi (init_seg (mf phi q')) = nil by rewrite E.
		by rewrite /= -eq' U_step_compat => //; apply/ Ffprop.
	have /eq eqn: m <= mf phi q' by rewrite E leqnSn.
	by rewrite /= eqn -E U_step_compat => //; apply/ Ffprop.

move: mod; rewrite mod_mf_mod => mod.
have [Fphi FphiFphi]:= phifd.
have eq' q': U psiF (mf phi q') phi q' = Some (Fphi q').
	rewrite U_stops; congr Some.
	by apply: (mod _ _ phifd).2; [ apply/icf/FphiFphi | apply/ coin_ref | ].
split => [|Mphi MphiMphi]; first by exists Fphi => q'; exists (mf phi q'); rewrite eq'.
have ->: Mphi = Fphi => //.
have U_sing: \F_(U psiF) \is_singlevalued by apply/mon_sing/U_mon.
by apply/U_sing => // q'; exists (mf phi q').
Qed.
End PSIF.

Lemma U_universal (someq: Q) (somea : A) (somephi': B') (count: Q \is_countable):
	forall F, F \is_continuous -> exists psiF, (U psiF) \evaluates_to F.
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
End UNIVERSAL_MACHINE.
Notation L2MF L := (mf.Pack (fun q a => List.In (q, a) L)).