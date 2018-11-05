From mathcomp Require Import all_ssreflect.
Require Import all_core classical_mach cs prod facts.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section cs_sum.
(* This is the sum of represented spaces. *)

Definition linc X Y (phi: names X) (p: questions X * questions Y) :=
@inl (answers X) (answers Y) (phi (p.1)).
Definition rinc X Y (psi: names Y) (p: questions X * questions Y) :=
@inr (answers X) (answers Y) (psi (p.2)).

Definition lslct X Y (phipsi: questions X * questions Y -> answers X + answers Y) :=
	fun q => match phipsi (q, someq Y) with
		| inl a => a
		| inr b => somea X
	end.

Definition rslct X Y (phipsi: questions X * questions Y -> answers X + answers Y) :=
	fun q => match phipsi (someq X, q) with
		| inl b => somea Y
		| inr b => b
	end.

Definition slct X Y (phi: questions X * questions Y -> answers X + answers Y) :=
	match phi (someq X, someq Y) with
		| inl a => inl (lslct phi)
		| inr b => inr (rslct phi)
	end.

Lemma lslct_linc (X Y: cs) (phi: names X):
	@lslct X Y (linc phi) =  phi.
Proof. by trivial. Qed.

Lemma rslct_rinc (X Y: cs) (psi: names Y):
	@rslct X Y (rinc psi) =  psi.
Proof. by trivial. Qed.

Definition sum_rep X Y :=
	make_mf (fun phipsi xpy => match xpy with
		| inl x => (exists a, phipsi (someq X, someq Y) = inl a)
			/\ rep X (lslct phipsi) x
		| inr y => (exists a, phipsi (someq X, someq Y) = inr a)
			/\ rep Y (rslct phipsi) y
	end).

Lemma sum_rep_sur (X Y: cs): (@sum_rep X Y) \is_cototal.
Proof.
move => [xy | xy]; have [phi phin]:= get_description xy.
	by exists (linc phi); split; first by exists (phi (someq X)).
by exists (rinc phi); split; first by exists (phi (someq Y)).
Qed.

Definition cs_sum_assembly_mixin (X Y: cs): interview_mixin.type
	(questions X * questions Y -> answers X + answers Y) (X + Y).
Proof. exists (@sum_rep X Y); exact/sum_rep_sur. Defined.

Lemma sum_rep_sing (X Y: cs): (@sum_rep X Y) \is_singlevalued.
Proof.
move => phi; rewrite /sum_rep.
case => [x | y].
	case => [x' | y'] => [[_ phinx] [_ phinx'] | [[a eq] _] [[b eq'] _]].
		by rewrite (rep_sing (lslct phi) x x').
	by rewrite eq in eq'.
case => [x' | y'] => [[[a eq] _] [[b eq'] _] | [_ phinx] [_ phinx']].
	by rewrite eq in eq'.
by rewrite (rep_sing (rslct phi) y y').
Qed.

Definition cs_sum_modest_set_mixin (X Y: cs): dictionary_mixin.type (interview.Pack (cs_sum_assembly_mixin X Y)).
Proof. split; exact/sum_rep_sing. Defined.

Canonical cs_sum X Y := @continuity_space.Pack
  (@questions X * @questions Y)
  (@answers X + @answers Y)
 	(someq X, someq Y)
  (inl (somea X))
  (prod_count (questions_countable X) (questions_countable Y))
  (sum_count (answers_countable X) (answers_countable Y))
	(dictionary.Pack (cs_sum_modest_set_mixin X Y)).
End cs_sum.

Section SUMLEMMAS.
(*
Lemma inl_rec_fun (X Y: cs):
	(@inl X Y) \is_recursive_function.
Proof.
by exists (@linc X Y); split; first by exists (phi (some_question X)).
Defined.

Lemma inl_rec (X Y: rep_space):
	(F2MF (@inl X Y)) \is_recursive.
Proof. exact/rec_fun_rec/inl_rec_fun. Defined.

Lemma inr_rec_fun (X Y: rep_space):
	(@inr X Y) \is_recursive_function.
Proof.
by exists (@rinc X Y); split; first by exists (phi (some_question Y)).
Defined.

Lemma inr_rec (X Y: rep_space):
	(F2MF (@inr X Y)) \is_recursive.
Proof. exact/rec_fun_rec/inr_rec_fun. Defined.
*)
Definition paib (X: Type):=
	fun (xx: X + X) => match xx with
		|	inl x => x
		| inr x => x
	end.

Definition paib_frlzr (X: cs) :=
	fun phi => @paib (names X) (slct phi).
(*
Lemma paib_frlzr_paib (X: cs):
	(@paib_frlzr X) \realizes (@paib X).
Proof.
by rewrite /paib_frlzr/paib/slct; move => phi x; case: x => x [[a ->] phinx].
Qed.

Lemma paib_rec_fun (X: rep_space):
	(@paib X) \is_recursive_function.
Proof. exists (@paib_frlzr X); apply paib_frlzr_paib. Defined.

Lemma paib_rec (X: rep_space):
	(F2MF (@paib X)) \is_recursive.
Proof. exact/rec_fun_rec/paib_rec_fun. Defined.

Lemma sum_assoc_rec_fun (X Y Z: rep_space):
	(fun xyz: X + (Y + Z) => match xyz with
		| inl x => inl (inl x)
		| inr yz => match yz with
			| inl y => inl (inr y)
			| inr z => inr z
		end
	end) \is_recursive_function.
Proof.
exists (fun phi (q: (questions X)* (questions Y) * (questions Z)) =>
	match slct phi with
	| inl psi => linc (linc psi) q
	| inr psi => match slct psi with
		| inl psi' => linc (rinc psi') q
		| inr psi' => rinc psi' q
	end
end).
move => phi x phinx /=.


case: (slct phi).
case: (phi (some_question _)).
		move => _ /=.
Admitted.

Lemma sum_assoc_rec (X Y Z: rep_space):
	(F2MF (fun x: X * (Y * Z) => (x.1, x.2.1,x.2.2))) \is_recursive.
Proof.
exact/rec_fun_rec/prod_assoc_rec_fun.
Defined.

Lemma prod_assoc_inv_rec_fun (X Y Z: rep_space):
	(fun x: X * Y * Z => (x.1.1, (x.1.2, x.2))) \is_recursive_function.
Proof.
exists (fun phi => name_pair (lprj (lprj phi)) (name_pair (rprj (lprj phi)) (rprj phi))).
by move => phi [[x y] z] [[phinx phiny] phinz].
Defined.

Lemma prod_assoc_inv_rec (X Y Z: rep_space):
	(F2MF (fun x: X * Y * Z => (x.1.1, (x.1.2, x.2)))) \is_recursive.
Proof.
exact/rec_fun_rec/prod_assoc_inv_rec_fun.
Defined.
*)

Lemma linc_cont X Y: (F2MF (@linc X Y)) \is_continuous_operator.
Proof.
by rewrite F2MF_cont => phi; exists (fun q => [:: q.1]) => psi /= q' [eq]; rewrite /linc eq.
Qed.

Lemma inl_hcr (X Y: cs): (F2MF (@inl X Y): _ ->> cs_sum _ _) \has_continuous_realizer.
Proof.
exists (F2MF (@linc X Y)); split; last exact: linc_cont.
by rewrite F2MF_rlzr_F2MF; split; first by exists (q (someq X)).
Qed.

Lemma inl_cont (X Y: cs): (@inl X Y: _ -> cs_sum _ _) \is_continuous.
Proof. exact/inl_hcr. Qed.

Lemma rinc_cont X Y: (F2MF (@rinc X Y)) \is_continuous_operator.
Proof.
by rewrite F2MF_cont => phi; exists (fun q => [:: q.2]) => psi /= q' [eq]; rewrite /rinc eq.
Qed.

Lemma inr_hcr (X Y: cs): (F2MF (@inr X Y): _ ->> cs_sum _ _) \has_continuous_realizer.
Proof.
exists (F2MF (@rinc X Y)); split; last exact: rinc_cont.
by rewrite F2MF_rlzr_F2MF; split; first by exists (q (someq Y)).
Qed.

Lemma inr_cont (X Y: cs): (@inr X Y: _ -> cs_sum _ _) \is_continuous.
Proof. exact/inr_hcr. Qed.

Definition mfssFG_rlzr (X Y X' Y': cs) (F: (names X) ->> (names Y)) (G: (names X') ->> (names Y')):=
	make_mf (fun (phi: names (cs_sum X X')) FGphi =>
		match phi (someq X, someq X') with
			| inl y => F (lslct phi) (lslct FGphi) /\ linc (lslct FGphi) = FGphi
			| inr y' => G (rslct phi) (rslct FGphi) /\ rinc (rslct FGphi) = FGphi
		end).

Definition mfssFG_frlzr X Y X' Y' (F: (names X) -> (names Y)) (G: (names X') -> (names Y')):=
	fun (phi: names (cs_sum X X')) =>
	match phi (someq X, someq X') with
		| inl y => linc (F (lslct phi))
		| inr y' => rinc (G (rslct phi))
	end.

(*
Lemma mfssFG_frlzr_rlzr (X Y X' Y': cs) (F: (names X) -> (names Y)) (G: (names X') -> (names Y')):
	F2MF (mfssFG_frlzr F G) =~= mfssFG_rlzr (F2MF F) (F2MF G).
Proof.
split; rewrite /F2MF/mfssFG_rlzr/mfssFG_frlzr.
	case: (s (someq X, someq X')) => _ <-.
by case (s (someq X, someq X')) => _ [->].
Qed.

Lemma mfssFG_rlzr_spec (X Y X' Y': cs) (f: X ->> Y) (g: X' ->> Y') F G:
	F \realizes f -> G \realizes g -> (mfssFG_rlzr F G) \realizes (f +s+ g: cs_sum _ _ ->> cs_sum _ _).
Proof.
move => Frf Grg phi [].
case => y [[]].
	case => [x [[[a eq] phinx] /= fxy] prp | x']; last by rewrite {1}/mfss/= => [][].
	have fd: (lslct phi) \from_dom (f o (delta (r:=X))).
		exists y; split; first by exists x.
		by move => b c; rewrite (rep_sing _ (lslct phi) b x) => //; exists y.
	have [[y' [[psi [Fphipsi psiny']]] prop cnd]]:= Frf (lslct phi) fd.
	split.
		exists (inl y');split.
			exists (linc psi); split; rewrite /mfssFG_rlzr; first by rewrite eq.
			by split; [exists (psi (some_question Y)) | rewrite lslct_linc].
		move => psi'; rewrite /mfssFG_rlzr eq => [[b c]].
		have [y'' name]:= prop (lslct psi') b; exists (inl y'').
		by split; first by exists (lslct psi' (some_question Y)); rewrite -c.
	case => y'' [[psi'' [val /= [[a' eq'] name]] cond]]; last first.
		move: val; rewrite /mfssFG_rlzr eq => [[val inc]].
		by rewrite -inc /linc/= in eq'.
	move: val; rewrite /mfssFG_rlzr eq => [[val inc]].
	split; last first.
		case => x'' [[a'' eq''] name']; last by rewrite eq'' in eq.
		rewrite (rep_sing _ (lslct phi) x'' x) => //.
		by exists (inl y).
	exists (inl x); split; first by split; first by exists a.
	have phiy'': (delta (r:=Y)) o F (lslct phi) y''.
		by split; first by exists (lslct psi'').
	have [[this [tmpnm con]]]:= cnd y'' phiy''.
	by rewrite (rep_sing X (lslct phi) x this).
case => [x' | x [[[a eq] phinx] /= fxy] prp]; first by rewrite {1}/mfss/= => [][].
have fd: (rslct phi) \from_dom (g o (delta (r:=X'))).
	exists y; split; first by exists x.
	by move => s b; rewrite (rep_sing _ (rslct phi) s x) => //; exists y.
have [[y' [[psi [Fphipsi psiny']]] prop cnd]]:= Grg (rslct phi) fd.
split.
	exists (inr y'); split.
		exists (rinc psi); split; rewrite /mfssFG_rlzr; first by rewrite eq.
		by split; [exists (psi (some_question Y')) | rewrite rslct_rinc].
	move => psi'; rewrite /mfssFG_rlzr eq => [[b c]].
	have [y'' name]:= prop (rslct psi') b; exists (inr y'').
	by split; first by exists (rslct psi' (some_question Y')); rewrite -c.
case => y'' [[psi'' [val /= [[a' eq'] name]] cond]].
	move: val; rewrite /mfssFG_rlzr eq => [[val inc]].
	by rewrite -inc /rinc/= in eq'.
move: val; rewrite /mfssFG_rlzr eq => [[val inc]].
split; last first.
	case => x'' [[a'' eq''] name']; first by rewrite eq'' in eq.
	rewrite (rep_sing _ (rslct phi) x'' x) => //.
	by exists (inr y).
exists (inr x).
split; first by split; first by exists a.
have phiy'': (delta (r:=Y')) o G (rslct phi) y''.
	by split; first by exists (rslct psi'').
have [[this [tmpnm con]]]:= cnd y'' phiy''.
by rewrite (rep_sing X' (rslct phi) x this).
Qed.

Lemma mfssFG_frlzr_spec (X Y X' Y': rep_space) (f: X -> Y) (g: X' -> Y') F G:
	F \is_realizer_function_for f -> G \is_realizer_function_for g -> (mfssFG_frlzr F G) \is_realizer_function_for (f +s+_f g).
Proof.
intros.
rewrite frlzr_rlzr mfssFG_frlzr_rlzr mfss_fun_mfss.
by apply mfssFG_rlzr_spec; rewrite -frlzr_rlzr.
Qed.

*)

Lemma sum_uprp_fun (X Y Z: cs) (f: X -> Z) (g: Y -> Z):
	exists! (F: X + Y -> Z),
		(forall x, F (inl x) = f x)
		/\
		(forall y, F (inr y) = g y).
Proof.
exists (fun xy => paib (fsum f g xy)); rewrite /paib.
by split => // F [eq eq']; apply functional_extensionality => [[x | y]].
Qed.
End SUMLEMMAS.