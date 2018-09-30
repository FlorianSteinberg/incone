From mathcomp Require Import all_ssreflect.
Require Import all_core cs_base.
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
rewrite cotot_spec => x.
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
Lemma lprj_rlzr_fst (X Y: cs):
	(F2MF lprj) \realizes (@mf_fst X Y: (cs_prod _ _) ->> _).
Proof. by rewrite F2MF_rlzr_F2MF => phi x [phinx _]. Qed.

Lemma rprj_rlzr_snd (X Y: cs):
	(F2MF rprj) \realizes (@mf_snd X Y: (cs_prod _ _) ->> _).
Proof. by rewrite F2MF_rlzr_F2MF => phi x [_ phinx]. Qed.

(*
Lemma fst_rec_fun (X Y: cs):
	(@fst X Y) \is_recursive_function.
Proof.
by exists (@lprj X Y); exact /lprj_rlzr_fst.
Defined.

Lemma snd_rec_fun (X Y: rep_space):
	(@snd X Y) \is_recursive_function.
Proof.
by exists (@rprj X Y); exact/rprj_rlzr_snd.
Defined.

Lemma rec_fun_rec (X Y: rep_space) (f: X -> Y):
	f \is_recursive_function -> (F2MF f) \is_recursive.
Proof.
by move => [M Mprop]; exists M; apply/ rrlzr_rlzr/ frlzr_rlzr.
Qed.

Lemma rec_rec_fun (X Y: rep_space) (f: X -> Y):
	(F2MF f) \is_recursive -> f \is_recursive_function.
Proof.
by move => [M Mprop] /=; exists M; apply/frlzr_rlzr/rrlzr_rlzr.
Qed.

Lemma fst_rec (X Y: rep_space):
	(F2MF (@fst X Y)) \is_recursive.
Proof. exact/rec_fun_rec/fst_rec_fun. Defined.

Lemma snd_rec (X Y: rep_space):
	(F2MF (@snd X Y)) \is_recursive.
Proof. exact/rec_fun_rec/snd_rec_fun. Defined.
*)

Lemma name_pair_rlzr_diag (X: cs):
	(F2MF (fun phi => @name_pair X X phi phi)) \realizes (@mf_diag X: _ ->> cs_prod _ _).
Proof. by rewrite F2MF_rlzr_F2MF. Qed.

(*
Lemma diag_rec_fun (X: rep_space):
	(@diag X) \is_recursive_function.
Proof. by exists (fun phi => name_pair phi phi). Defined.

Lemma diag_rec (X: rep_space):
	(F2MF (@diag X)) \is_recursive.
Proof. exact/rec_fun_rec/diag_rec_fun. Defined.

Lemma switch_rec_fun (X Y: rep_space):
	(@switch X Y) \is_recursive_function.
Proof. 
by exists (fun phi => name_pair (rprj phi) (lprj phi)); move => phi [x y] [phinx phiny].
Defined.

Lemma switch_rec (X Y: rep_space):
	(F2MF (@switch X Y)) \is_recursive.
Proof. exact/rec_fun_rec/switch_rec_fun. Defined.

Lemma prod_assoc_rec_fun (X Y Z: rep_space):
	(fun x: X * (Y * Z) => (x.1, x.2.1,x.2.2)) \is_recursive_function.
Proof.
exists (fun phi => name_pair (name_pair (lprj phi) (lprj (rprj phi))) (rprj (rprj phi))).
by move => phi [x [y z]] [phinx [phiny phinz]].
Defined.

Lemma prod_assoc_rec (X Y Z: rep_space):
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

Lemma prod_rec_elt (X Y: rep_space) (x: X) (y: Y):
	x \is_recursive_element -> y \is_recursive_element -> (x, y) \is_recursive_element.
Proof.
move => [phi phinx] [psi psiny].
by exists (name_pair phi psi).
Defined.
*)

Lemma lprj_pair (X Y: cs) (phi: names X) (psi: names Y):
	lprj (name_pair phi psi) =  phi.
Proof. by trivial. Qed.

Lemma rprj_pair (X Y: cs) (phi: names X) (psi: names Y):
	rprj (name_pair phi psi) =  psi.
Proof. by trivial. Qed.

(*
Lemma prod_cmpt_elt (X Y: cs) (x: X) (y: Y):
	x \is_computable_element -> y \is_computable_element -> (x, y) \is_computable_element.
Proof.
move => [phix phinx] [phiy phiny].
exists (fun n q => match q with
	| inl qx => match phix n qx with
		| Some a => Some (a, some_answer Y)
		| None => None
	end
	| inr qy => match phiy n qy with
		| Some a => Some (some_answer X, a)
		| None => None
	end
end).
have [psix [evalx psixnx]]:= phinx.
have [psiy [evaly psiyny]]:= phiny.
exists (name_pair psix psiy).
split.
	move => q a.
	split.
		case => n evl.
		case: q evl => [qx evl | qy evl]; case E: (_ n _) evl => [a' | ] // [<-].
			by rewrite -(evalx qx a').1; last exists n.
		by rewrite -(evaly qy a').1; last exists n.
	rewrite /F2MF; case: q => [qx /=eq| qy /=eq].
		by have []:= (evalx qx (psix qx)).2 => // n eq'; exists n; rewrite eq' eq.
	by have []:= (evaly qy (psiy qy)).2 => // n eq'; exists n; rewrite eq' eq.
by split; [rewrite /lprj | rewrite /rprj].
Defined.
*)

Lemma lprj_cont X Y:
	(F2MF (@lprj X Y)) \is_continuous.
Proof.
move => phi phifd q; exists ([::inl q]).
by split => // Fphi /= <- psi [eq _] Fpsi <-; rewrite /lprj eq.
Qed.

Lemma fst_hcr (X Y: cs):
	(@mf_fst X Y: cs_prod _ _ ->> _) \has_continuous_realizer.
Proof.
exists (F2MF (@lprj X Y)).
split; last exact/lprj_cont.
by rewrite F2MF_rlzr_F2MF => phi x [].
Qed.

Lemma rprj_cont X Y:
	(F2MF (@rprj X Y)) \is_continuous.
Proof.
move => phi phifd q; exists ([::inr q]).
by split => // Fphi/= <- psi [eq _] Fpsi <-; rewrite /rprj eq.
Qed.

Lemma snd_hcr (X Y: cs):
	(@mf_snd X Y: cs_prod _ _ ->> _) \has_continuous_realizer.
Proof.
exists (F2MF (@rprj X Y)).
split; last exact/rprj_cont.
by rewrite F2MF_rlzr_F2MF => phi x [].
Qed.

Definition mfppFG_rlzr (X Y X' Y': cs) (F: (names X) ->> (names Y)) (G: (names X') ->> (names Y')):=
	make_mf (fun (phipsi: names (cs_prod X X')) FphiGpsi =>
		FphiGpsi = name_pair (lprj FphiGpsi) (rprj FphiGpsi)
		/\
		(F ** G) (lprj phipsi, rprj phipsi)	(lprj FphiGpsi, rprj FphiGpsi)).

Definition mfppFG_frlzr (X Y X' Y': cs) (F: (names X) -> (names Y)) (G: (names X') -> (names Y')):=
	(fun (phipsi: names (cs_prod X X')) => name_pair (F (lprj phipsi)) (G (rprj phipsi))).

Lemma mfppFG_frlzr_rlzr (X Y X' Y': cs) (F: (names X) -> (names Y)) (G: (names X') -> (names Y')):
	F2MF (mfppFG_frlzr F G) =~= mfppFG_rlzr (F2MF F) (F2MF G).
Proof.
move => phi FGphi; rewrite {1}/F2MF.
by split => [<- | [np [/=vall valr]]]; last by rewrite np /mfppFG_frlzr vall valr.
Qed.

Lemma mfppFG_rlzr_spec (X Y X' Y': cs) (f: X ->> Y) (g: X' ->> Y') F G:
	F \realizes f -> G \realizes g -> (mfppFG_rlzr F G) \realizes (f ** g: cs_prod _ _ ->> cs_prod _ _).
Proof.
(*
move => Frf Grg phipsi [[y y']] [[[x x' [[/=phinx psinx'] [/= fxy gx'y']]]prop]].
have lprjfd: ((lprj phipsi) \from_dom (f o (delta (r:=X)))).
	exists y; split => [ | z phinz]; first by exists x.
	by rewrite (rep_sing X (lprj phipsi) z x); first exists y.
have [[z [[Fphi [FphiFphi Fphinz]]] propl]condl]:= Frf (lprj phipsi) lprjfd.
have rprjfd: ((rprj phipsi) \from_dom (g o (delta (r:=X')))).
	exists y'; split => [ | z' phinz']; first by exists x'.
	by rewrite (rep_sing X' (rprj phipsi) z' x'); first exists y'.
have [[z' [[Gpsi [GpsiGpsi Gpsinz']]] propr]condr]:= Grg (rprj phipsi) rprjfd.
split.
	exists (z, z'); split; first by exists (name_pair Fphi Gpsi).
	move => FphiGpsi [/= np [/=FphiFphi' GpsiGpsi']].
	have [l nl]:= (propl (lprj FphiGpsi) FphiFphi').
	have [k nk]:= (propr (rprj FphiGpsi) GpsiGpsi').
	by exists (l,k); split.
move => [l k] [[FphiGpsi [[ np [/=FphiFphi' GphiGphi']][/= Fphinl Gpsink]]] proplk].
have phipsil: ((delta (r:=Y)) o F (lprj phipsi) l).
	by split => //; exists (lprj FphiGpsi).
have [[x'' [phinx'' fx''l]] prpl]:= (condl l phipsil).
have phipsir: ((delta (r:=Y')) o G (rprj phipsi) k).
	by split => //; exists (rprj FphiGpsi).
have [[y'' [phiny'' gy''l]] prpr]:= (condr k phipsir).
split.
	exists (x, x'); split => //; split => /=.
		by rewrite (rep_sing X (lprj phipsi) x x'').
	by rewrite (rep_sing X' (rprj phipsi) x' y'').
move => [a b] [/=phina psinb].
have [this stuff]:= prpl a phina.
have [this' stuff']:= prpr b psinb.
by exists (this, this').
Qed. *)
Admitted.

(*
Lemma prod_rec_fun (X Y X' Y': cs) (f: X -> Y) (g: X' -> Y'):
	f \is_recursive_function -> g \is_recursive_function -> (f **_f g) \is_recursive_function.
Proof.
move => [M /= Mrf] [N /= Nrg].
exists (mfppFG_frlzr M N).
exact/ mfppFG_frlzr_spec.
Defined.

Lemma prod_rec (X Y X' Y': rep_space) (f: X ->> Y) (g: X' ->> Y'):
	f \is_recursive -> g \is_recursive -> (f ** g) \is_recursive.
Proof.
move => [M Mrf] [N Nrg].
exists (mfppFG_frlzr M N).
abstract by rewrite rrlzr_rlzr mfppFG_frlzr_rlzr; apply: mfppFG_rlzr_spec; rewrite -rrlzr_rlzr.
Defined.
*)

Lemma mfppFG_cont (X Y X' Y': cs) (F: (names X) ->> (names Y)) (G: (names X') ->> (names Y')):
	F \is_continuous -> G \is_continuous -> (mfppFG_rlzr F G) \is_continuous.
Proof.
have mapl: forall K (q:questions X), List.In q K -> List.In ((@inl _ (questions X')) q) (map inl K).
	elim => // q K ih q' /=listin; by case: listin => ass; [left; rewrite -ass | right; apply ih].
have mapr: forall K (q:questions X'), List.In q K -> List.In ((@inr (questions X) _) q) (map inr K).
	elim => // q K ih q' /=listin; by case: listin => ass; [left; rewrite -ass | right; apply ih].
move => Fcont Gcont phi [FGphi [ np [/=FlphilFGphi GrphirFGphi]]] q.
case: q => q.
	have lphifd: (lprj phi) \from_dom F by exists (lprj FGphi).
	have [L [/=phifd Lprop]] := (Fcont (lprj phi) lphifd q).
	exists (map inl L).
	split; first by exists FGphi; split.
	move => FGphi' [np' [/=vall valr]] psi coin Fpsi [ np'' [/=val'l val'r]].
	rewrite np' np''; apply injective_projections => //=.
	rewrite (cont_sing Fcont vall FlphilFGphi).
	apply/ Lprop; [ | | apply val'l ] => //=.
	rewrite /lprj coin_lstn => q' listin/=.
	rewrite ((@coin_lstn _ _ _ _ (map inl L)).1 coin (inl q')) => //.
	by apply (mapl L q').
have rphifd: (rprj phi) \from_dom G by exists (rprj FGphi).
have [L [/=_ Lprop]] := (Gcont (rprj phi) rphifd q).
exists (map inr L); split; first by exists FGphi; split.
move => FGphi' [np' [/=vall valr]] psi coin Fpsi [ np'' [/=val'l val'r]].
rewrite np' np''; apply injective_projections => //=.
rewrite (cont_sing Gcont valr GrphirFGphi).
apply/ Lprop; [ | | apply val'r ] => //=.
rewrite /rprj coin_lstn => q' listin/=.
rewrite ((@coin_lstn _ _ _ _ (map inr L)).1 coin (inr q')) => //.
by apply (mapr L q').
Qed.

Lemma mfpp_hcr (X Y X' Y': cs) (f: X ->> Y) (g: X' ->> Y'):
	f \has_continuous_realizer -> g \has_continuous_realizer -> (f ** g: cs_prod _ _ ->> cs_prod _ _) \has_continuous_realizer.
Proof.
move => [F [Frf Fcont]] [G [Grg Gcont]].
exists (mfppFG_rlzr F G).
split; [exact: mfppFG_rlzr_spec | exact: mfppFG_cont].
Qed.

Definition prod_uprp (X Y Z: cs) (f: Z -> X) (g: Z -> Y):
	exists! (F: Z -> X * Y),
	(forall z, (F z).1 = f z)
	/\
	(forall z, (F z).2 = g z).
Proof.
exists (fun z => fprd f g (diag z)); split => // F [lprp rprp]; rewrite /fprd/diag.
by apply functional_extensionality => z; rewrite -lprp -rprp -surjective_pairing.
Qed.

(*
Lemma rec_fun_comp (X Y Z: cs) (f: X -> Y) (g: Y -> Z):
	f \is_recursive_function -> g \is_recursive_function
	-> forall h, (forall x, h x = g (f x)) -> h \is_recursive_function.
Proof.
move => [M comp] [N comp'] h eq.
exists (fun phi => N (M phi)).
abstract by move => phi x phinx; rewrite/prog/= eq; apply comp'; apply comp.
Defined.

Lemma prod_uprp_rec_fun (X Y Z: rep_space) (f: Z -> X) (g: Z -> Y):
	f \is_recursive_function -> g \is_recursive_function ->
	exists! (F: Z -> X * Y), exists (P: F \is_recursive_function),
	(forall z, (F z).1 = f z)
	/\
	(forall z, (F z).2 = g z).
Proof.
intros; exists (fun x => (mfpp_fun f g (diag x))); split; last rewrite /diag.
	split; last	by split => // F [eq eq']; apply functional_extensionality => [[x | y]].
	by apply/ rec_fun_comp; [apply diag_rec_fun | apply: prod_rec_fun X0 X1 | ] => /=.
move => fg [fgrec [lfg rfg]].
by apply functional_extensionality => z; rewrite /mfpp_fun -lfg -rfg -surjective_pairing.
Qed.
*)
End products.
Notation "X \*_cs Y" := (cs_prod X Y) (at level 50).