From mathcomp Require Import all_ssreflect.
Require Import all_core cs.
Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section cs_product.
(* This is the product of continuity-spaces. *)
Definition lprj X Y (phipsi: questions X + questions Y -> (answers X) * (answers Y)) q := (phipsi (inl q)).1.
Definition rprj X Y (phipsi: questions X + questions Y -> (answers X) * (answers Y)) q := (phipsi (inr q)).2.

Definition name_pair X Y (phi: names X) (psi: names Y) :=
	fun c => match c with
		| inl s => (phi s, somea Y)
		| inr t => (somea X, psi t)
	end.

Definition prod_rep X Y :=
	make_mf (fun (phipsi : (questions X + questions Y -> answers X * answers Y)) xy =>
      (rep X ** rep Y) (lprj phipsi, rprj phipsi) xy).

Lemma prod_rep_sur (X Y: cs):
	(@prod_rep X Y) \is_cototal.
Proof.
move => x.
have [phi phinx1]:= (get_name x.1).
have [psi psinx2]:= (get_name x.2).
by exists (name_pair phi psi).
Qed.

Definition cs_prod_assembly_mixin (X Y: cs):
	interview_mixin.type (questions X + questions Y -> answers X * answers Y) (X * Y).
Proof. exists (prod_rep X Y); exact/prod_rep_sur. Defined.

Lemma prod_rep_sing (X Y: cs): (@prod_rep X Y) \is_singlevalued.
Proof.
move => phipsi x x' [phinx1 psinx2] [phinx'1 psinx'2].
apply: injective_projections.
	by apply/rep_sing; first apply phinx1.
by apply/rep_sing; first apply psinx2.
Qed.

Definition cs_prod_modest_set_mixin (X Y: cs):
 dictionary_mixin.type (interview.Pack (cs_prod_assembly_mixin X Y)).
Proof. by split; exact/prod_rep_sing. Defined.

Canonical cs_prod (X Y: cs) := @cs.Pack _ _ (inl (someq X)) (somea X, somea Y) (sum_count (cs.Qcount X) (cs.Qcount Y)) (prod_count (cs.Acount X) (cs.Acount Y)) (dictionary.Pack (cs_prod_modest_set_mixin X Y)).
End cs_product.
Notation "X \*_cs Y" := (cs_prod X Y) (at level 50).
Arguments lprj {X} {Y}.
Arguments rprj {X} {Y}.
(*
Class Uncurry T (f : T) src tgt := { prog : src -> tgt }.
Arguments prog {T} f {src tgt _}.

Instance Uncurry_base (A B : rep_space) f : @Uncurry (A -> B) f _ _ :=
  {| prog := f |}.
Instance Uncurry_step (A B : rep_space) C (f : A -> B -> C)
                       T (g : forall a, @Uncurry (B -> C) (f a) B T) :
                                          @Uncurry (A -> B -> C) f (rep_space_prod A B) T :=
  {| prog := (fun x : A * B => @prog _ _ _ _ (g (fst x)) (snd x)) |}.

Notation "f '\is_recursive_function'" := (@is_rec_fun _ _ (prog f)) (at level 2).
Notation "f '\is_computable_function'" := (@is_cmpt_fun _ _ (prog f)) (at level 2).
*)
Section products.
Lemma name_split X Y phi (x: cs_prod X Y):
	phi \is_name_of x <-> (lprj phi) \is_name_of (x.1) /\ (rprj phi) \is_name_of (x.2).
Proof. done. Qed.

Lemma lprj_rlzr_fst (X Y: cs):
	(F2MF lprj) \realizes (@mf_fst X Y: _ \*_cs _ ->> _).
Proof. by rewrite F2MF_rlzr_F2MF => phi x [phinx _]. Qed.

Lemma rprj_rlzr_snd (X Y: cs):
	(F2MF rprj) \realizes (@mf_snd X Y: _ \*_cs _ ->> _).
Proof. by rewrite F2MF_rlzr_F2MF => phi x [_ phinx]. Qed.

Lemma name_pair_rlzr_diag (X: cs):
	(F2MF (fun phi => @name_pair X X phi phi)) \realizes (@mf_diag X: _ ->> (_ \*_cs _)).
Proof. by rewrite F2MF_rlzr_F2MF. Qed.

Lemma lprj_pair (X Y: cs) (phi: names X) (psi: names Y):
	lprj (name_pair phi psi) =  phi.
Proof. by trivial. Qed.

Lemma rprj_pair (X Y: cs) (phi: names X) (psi: names Y):
	rprj (name_pair phi psi) =  psi.
Proof. by trivial. Qed.

Lemma lprj_cont X Y: (F2MF (@lprj X Y)) \is_pointwise_continuous.
Proof.
move => phi phifd q; exists ([::inl q]).
by split => // Fphi /= <- psi [eq _] Fpsi <-; rewrite /lprj eq.
Qed.

Lemma fst_hcr (X Y: cs):
	(@mf_fst X Y: _ \*_cs _ ->> _) \has_continuous_realizer.
Proof.
exists (F2MF (@lprj X Y)).
split; last exact/lprj_cont.
by rewrite F2MF_rlzr_F2MF => phi x [].
Qed.

Lemma rprj_cont X Y:
	(F2MF (@rprj X Y)) \is_pointwise_continuous.
Proof.
move => phi phifd q; exists ([::inr q]).
by split => // Fphi/= <- psi [eq _] Fpsi <-; rewrite /rprj eq.
Qed.

Lemma snd_hcr (X Y: cs):
	(@mf_snd X Y: _ \*_cs _ ->> _) \has_continuous_realizer.
Proof.
exists (F2MF (@rprj X Y)).
split; last exact/rprj_cont.
by rewrite F2MF_rlzr_F2MF => phi x [].
Qed.

Definition fprd_rlzr (X Y X' Y': cs) (F: (names X) ->> (names Y)) (G: (names X') ->> (names Y')):=
	make_mf (fun (phipsi: names (cs_prod X X')) FphiGpsi =>
		FphiGpsi = name_pair (lprj FphiGpsi) (rprj FphiGpsi)
		/\
		(F ** G) (lprj phipsi, rprj phipsi)	(lprj FphiGpsi, rprj FphiGpsi)).

Definition fprd_frlzr (X Y X' Y': cs) (F: (names X) -> (names Y)) (G: (names X') -> (names Y')):=
	(fun (phipsi: names (X \*_cs X')) => name_pair (F (lprj phipsi)) (G (rprj phipsi))).

Lemma	fprd_frlzr_rlzr (X Y X' Y': cs) (F: (names X) -> (names Y)) (G: (names X') -> (names Y')):
	F2MF (fprd_frlzr F G) =~= fprd_rlzr (F2MF F) (F2MF G).
Proof.
move => phi FGphi; rewrite {1}/F2MF.
by split => [<- | [np [/=vall valr]]]; last by rewrite np /fprd_frlzr vall valr.
Qed.

Lemma fprd_rlzr_spec (X Y X' Y': cs) (f: X ->> Y) (g: X' ->> Y') F G:
	F \realizes f -> G \realizes g -> (fprd_rlzr F G) \realizes (f ** g: _ \*_cs _ ->> (_ \*_cs _)).
Proof.
move => rlzr rlzr'; apply split_rlzr => phi x.
	rewrite name_split => [[phinx1 phinx2]].
	rewrite fprd_dom => [[fd1 fd2]].
	have [Fphi1 FphiFphi1]:= rlzr_dom rlzr phinx1 fd1.
	have [Fphi2 FphiFphi2]:= rlzr_dom rlzr' phinx2 fd2.
	exists (name_pair Fphi1 Fphi2).
	by rewrite /= lprj_pair rprj_pair.
move => FGphi; rewrite name_split => [[phinx1 phinx2]].
rewrite fprd_dom => [[fd1 fd2]] [eq [/= FphiFGphi GphiFGphi]].
have [y []]:= rlzr_val rlzr phinx1 fd1 FphiFGphi.
have [y' []]:= rlzr_val rlzr' phinx2 fd2 GphiFGphi.
by exists (y, y').
Qed.

Lemma fprd_rlzr_val_cont (X Y X' Y': cs) (F: (names X) ->> (names Y)) (G: (names X') ->> (names Y')):
	F \is_pointwise_continuous -> G \is_pointwise_continuous -> (fprd_rlzr F G) \is_pointwise_continuous.
Proof.
have mapl: forall K (q:questions X), List.In q K -> List.In ((@inl _ (questions X')) q) (map inl K).
	elim => // q K ih q' /=listin; by case: listin => ass; [left; rewrite -ass | right; apply ih].
have mapr: forall K (q:questions X'), List.In q K -> List.In ((@inr (questions X) _) q) (map inr K).
	elim => // q K ih q' /=listin; by case: listin => ass; [left; rewrite -ass | right; apply ih].
move => Fcont Gcont phi [FGphi [ np [/=FlphilFGphi GrphirFGphi]]] q.
case: q => q.
	have lphifd: (lprj phi) \from dom F by exists (lprj FGphi).
	have [L [/=phifd Lprop]] := (Fcont (lprj phi) lphifd q).
	exists (map inl L).
	split; first by exists FGphi; split.
	move => FGphi' [np' [/=vall valr]] psi coin Fpsi [ np'' [/=val'l val'r]].
	rewrite np' np''; apply injective_projections => //=.
	rewrite (ptw_cont_sing Fcont vall FlphilFGphi).
	apply/ Lprop; [ | | apply val'l ] => //=.
	rewrite /lprj coin_lstn => q' listin/=.
	rewrite ((@coin_lstn _ _ _ _ (map inl L)).1 coin (inl q')) => //.
	by apply (mapl L q').
have rphifd: (rprj phi) \from dom G by exists (rprj FGphi).
have [L [/=_ Lprop]] := (Gcont (rprj phi) rphifd q).
exists (map inr L); split; first by exists FGphi; split.
move => FGphi' [np' [/=vall valr]] psi coin Fpsi [ np'' [/=val'l val'r]].
rewrite np' np''; apply injective_projections => //=.
rewrite (ptw_cont_sing Gcont valr GrphirFGphi).
apply/ Lprop; [ | | apply val'r ] => //=.
rewrite /rprj coin_lstn => q' listin/=.
rewrite ((@coin_lstn _ _ _ _ (map inr L)).1 coin (inr q')) => //.
by apply (mapr L q').
Qed.

Lemma mfpp_hcr (X Y X' Y': cs) (f: X ->> Y) (g: X' ->> Y'):
	f \has_continuous_realizer -> g \has_continuous_realizer -> (f ** g: cs_prod _ _ ->> cs_prod _ _) \has_continuous_realizer.
Proof.
move => [F [Frf Fcont]] [G [Grg Gcont]].
exists (fprd_rlzr F G).
split; [exact: fprd_rlzr_spec | exact: fprd_rlzr_val_cont].
Qed.
End products.
Notation "X \*_cs Y" := (cs_prod X Y) (at level 50).