From mathcomp Require Import ssreflect ssrfun seq.
Require Import all_core cs.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section cs_sum.
(* This is the sum of represented spaces. *)

Definition linc Q A Q' A' (phi: Q -> A) (p: Q * Q') := @inl A A' (phi (p.1)).
Arguments linc {Q} {A} {Q'} {A'}.
Definition rinc Q A Q' A' (psi: Q' -> A') (p: Q * Q') := @inr A A' (psi (p.2)).
Arguments rinc {Q} {A} {Q'} {A'}.

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

Canonical cs_sum X Y := continuity_space.Pack
                          (someq X, someq Y)
                          (inl (somea X))
                          (prod_count (questions_countable X) (questions_countable Y))
                          (sum_count (answers_countable X) (answers_countable Y))
	                  (dictionary.Pack (cs_sum_modest_set_mixin X Y)).
End cs_sum.
Arguments linc {Q} {A} {Q'} {A'}.
Arguments rinc {Q} {A} {Q'} {A'}.
Notation "X \+_cs Y" := (cs_sum X Y) (at level 35).

Section SUMLEMMAS.
Definition inl_rlzr (X Y: cs) := F2MF (@linc (questions X) (answers X) (questions Y) (answers Y)).
Arguments inl_rlzr {X} {Y}.

Lemma inl_rlzr_spec (X Y: cs): inl_rlzr \realizes (F2MF inl: X ->> X \+_cs Y).
Proof. by rewrite F2MF_rlzr_F2MF => phi x phinx; split; first exists (phi (someq X)). Qed.

Lemma linc_cntop Q A Q' A': (F2MF (@linc Q A Q' A')) \is_continuous_operator.
Proof. by rewrite F2MF_cont => phi; rewrite /linc; exists (fun q => [:: q.1]) => psi q' [-> ]. Qed.

Lemma inl_cont (X Y: cs): (@inl X Y: _ -> cs_sum _ _) \is_continuous.
Proof. by exists inl_rlzr; split; [exact/inl_rlzr_spec | exact/linc_cntop]. Qed.

Definition inr_rlzr (X Y: cs) := F2MF (@rinc (questions X) (answers X) (questions Y) (answers Y)).
Arguments inr_rlzr {X} {Y}.

Lemma inr_rlzr_spec (X Y: cs): inr_rlzr \realizes (F2MF inr: Y ->> X \+_cs Y).
Proof. by rewrite F2MF_rlzr_F2MF => phi x phinx; split; first exists (phi (someq Y)). Qed.

Lemma rinc_cntop Q A Q' A': (F2MF (@rinc Q A Q' A')) \is_continuous_operator.
Proof. by rewrite F2MF_cont => phi; rewrite /rinc; exists (fun q => [:: q.2]) => psi q' [-> ]. Qed.

Lemma inr_cont (X Y: cs): (@inr X Y: _ -> cs_sum _ _) \is_continuous.
Proof. by exists inr_rlzr; split; [exact/inr_rlzr_spec | exact/rinc_cntop]. Qed.

Definition paib (X: Type):=
	fun (xx: X + X) => match xx with
		|	inl x => x
		| inr x => x
	end.

Definition paib_rlzr (X: cs) := F2MF (@paib (names X) \o_f (@slct X X)).

Lemma paib_rlzr_crct (X: cs): (paib_rlzr X) \realizes (F2MF (@paib X): X \+_cs X ->> X).
Proof.
by rewrite F2MF_rlzr_F2MF => phi [x [[a' eq] phinx] | x [[a' eq] phinx]]; rewrite /=/paib/slct eq.
Qed.

Lemma paib_rlzr_cntop (X: cs): (@paib_rlzr X) \is_continuous_operator.
Proof.
rewrite F2MF_cont => phi.
exists (fun q => [:: (someq X, someq X); (q, someq X); (someq X, q)]).
rewrite /paib/slct/=/lslct/rslct => psi q' [-> [eq [eq' _]]].
by case: (psi (someq X, someq X)); [rewrite eq | rewrite eq'].
Qed.


Lemma paib_cont (X: cs): (@paib X: _ \+_cs _ -> _) \is_continuous.
Proof. exists (paib_rlzr X); split; [exact/paib_rlzr_crct | exact/paib_rlzr_cntop]. Qed.

(*
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

Definition mfssFG_rlzr (X Y X' Y': cs) (F: (names X) ->> (names Y)) (G: (names X') ->> (names Y')):=
	make_mf (fun (phi: names (cs_sum X X')) FGphi =>
		match phi (someq X, someq X') with
			| inl y => F (lslct phi) (lslct FGphi) /\ linc (lslct FGphi) = FGphi
			| inr y' => G (rslct phi) (rslct FGphi) /\ rinc (rslct FGphi) = FGphi
		end).

Definition mfssFG_rlzrf X Y X' Y' (F: (names X) -> (names Y)) (G: (names X') -> (names Y')):=
	fun (phi: names (cs_sum X X')) =>
	match phi (someq X, someq X') with
		| inl y => linc (F (lslct phi))
		| inr y' => rinc (G (rslct phi))
	end.

Lemma mfssFG_rlzrf_spec (X Y X' Y': cs) (F: (names X) -> (names Y)) (G: (names X') -> (names Y')):
	F2MF (mfssFG_rlzrf F G) =~= mfssFG_rlzr (F2MF F) (F2MF G).
Proof.
split; rewrite /F2MF/mfssFG_rlzr/mfssFG_rlzrf /=.
- by case: (s (someq X, someq X')) => _ <-.
by case (s (someq X, someq X')) => _ [->].
Qed.

Lemma mfssFG_rlzr_spec (X Y X' Y': cs) (f: X ->> Y) (g: X' ->> Y') F G:
	F \realizes f -> G \realizes g -> (mfssFG_rlzr F G) \realizes (f +s+ g: cs_sum _ _ ->> cs_sum _ _).
Proof.
move => rlzr rlzr' /= phi [x [[a' eq] phinx] [[]// y fxy] | x [[a' eq] phinx] [[]// y fxy]].
- have [ | [Fphi FphiFphi] prp]//:= rlzr (lslct phi) x phinx; first by exists y.
  split => [ | Fphi' /=]; first by exists (linc Fphi); rewrite /= eq lslct_linc.
  rewrite eq /linc/lslct => [[val eq']]; have [fa []]:= prp (lslct Fphi') val.
  exists (inl fa); do 2 split => //.
  by rewrite -eq'; case: (Fphi' (someq Y, someq Y')) => [c | ]; [exists c | exists (somea Y)].
have [ | [Fphi FphiFphi] prp]//:= rlzr' (rslct phi) x phinx; first by exists y.
split => [ | Fphi' /=]; first by exists (rinc Fphi); rewrite /= eq rslct_rinc.
rewrite eq /rinc/rslct => [[val eq']]; have [fa []]:= prp (rslct Fphi') val.
exists (inr fa); do 2 split => //.
by rewrite -eq'; case: (Fphi' (someq Y, someq Y')) => [ | c]; [exists (somea Y') | exists c].
Qed.

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