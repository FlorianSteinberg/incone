From mathcomp Require Import ssreflect ssrfun seq.
From rlzrs Require Import all_rlzrs.
Require Import all_cont cs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section cs_product.
(* This is the product of continuity-spaces. *)
Definition lprj Q Q' A A' (phipsi: Q + Q' -> A * A') q := (phipsi (inl q)).1.
Definition rprj Q Q' A A' (phipsi: Q + Q' -> A * A') q := (phipsi (inr q)).2.

Definition prod_rep X Y :=
	make_mf (fun (phipsi : (queries X + queries Y -> answers X * answers Y)) xy =>
      (rep X ** rep Y) (lprj phipsi, rprj phipsi) xy).  

Definition name_pair X Y (phi: names X) (psi: names Y) :=
	fun c => match c with
		| inl s => (phi s, somea Y)
		| inr t => (somea X, psi t)
	end.

Lemma prod_rep_sur (X Y: cs):
	(@prod_rep X Y) \is_cototal.
Proof.
move => x.
have [phi phinx1]:= (get_description x.1).
have [psi psinx2]:= (get_description x.2).
by exists (name_pair phi psi).
Qed.

Lemma prod_rep_sing (X Y: cs): (@prod_rep X Y) \is_singlevalued.
Proof.
move => phipsi x x' [phinx1 psinx2] [phinx'1 psinx'2].
apply: injective_projections.
- by apply/rep_sing; first apply phinx1.
by apply/rep_sing; first apply psinx2.
Qed.

Canonical cs_prod_class (X Y: cs):=
  @continuity_space.Class _ _ _ (interview.Mixin (@prod_rep_sur X Y))
      (dictionary.Mixin (@prod_rep_sing X Y))
      (continuity_space.Mixin (inl (someq X))
                              (somea X, somea Y)
                              (sum_count (queries_countable X) (queries_countable Y))
                              (prod_count (answers_countable X) (answers_countable Y))).

Canonical cs_prod (X Y: cs) : cs:= continuity_space.Pack (cs_prod_class X Y).

End cs_product.
Arguments lprj {Q} {Q'} {A} {A'}.
Arguments rprj {Q} {Q'} {A} {A'}.
Notation "X \*_cs Y":= (cs_prod X Y) (at level 40).

Section products.
Lemma name_split X Y phi x:
	phi \describes x wrt (X \*_cs Y) <-> (lprj phi) \describes (x.1) wrt X /\ (rprj phi) \describes (x.2) wrt Y.
Proof. done. Qed.


Definition fst_rlzr (X Y: cs): questions (X \*_cs Y) ->> questions X := F2MF (@lprj (queries X) (queries Y) (answers X) (answers Y)).
Arguments fst_rlzr {X} {Y}.

Definition snd_rlzr (X Y: cs): questions (X \*_cs Y) ->> questions Y:= F2MF (@rprj (queries X) (queries Y) (answers X) (answers Y)).
Arguments snd_rlzr {X} {Y}.

Lemma fst_rlzr_spec (X Y: cs):
  (@fst_rlzr X Y) \realizes (@mf_fst X Y).
Proof. by rewrite F2MF_rlzr_F2MF => phi x [phinx _]. Qed.

Lemma snd_rlzr_spec (X Y: cs):
  (@snd_rlzr X Y) \realizes mf_snd.
Proof. by rewrite F2MF_rlzr_F2MF => phi x [_ phinx]. Qed.

Definition diag_rlzr (X: cs): questions X ->> questions (X \*_cs X):=
  F2MF (fun (phi: names X) => name_pair phi phi).
Arguments diag_rlzr {X}.

Lemma diag_rlzr_spec (X: cs):
  diag_rlzr \realizes (@mf_diag X: _ ->> (_ \*_cs _)).
Proof. by rewrite F2MF_rlzr_F2MF. Qed.

Lemma lprj_pair (X Y: cs) (phi: names X) (psi: names Y):
	lprj (name_pair phi psi) =  phi.
Proof. by trivial. Qed.

Lemma rprj_pair (X Y: cs) (phi: names X) (psi: names Y):
	rprj (name_pair phi psi) =  psi.
Proof. by trivial. Qed.

Lemma lprj_cntop Q Q' A A': (F2MF (@lprj Q Q' A A')) \is_continuous_operator.
Proof.
by rewrite cntop_F2MF => phi; exists (fun q => [:: inl q]) => psi q' [eq _]; rewrite /lprj eq.
Qed.

Lemma fst_hcr (X Y: cs): (@mf_fst X Y: _ * _ ->> _) \has_continuous_realizer.
Proof.
exists fst_rlzr.
split; last exact/lprj_cntop.
by rewrite F2MF_rlzr_F2MF => phi x [].
Qed.

Lemma fst_cont (X Y: cs): (@fst X Y: _ \*_cs _ -> _) \is_continuous.
Proof. exact/fst_hcr. Qed.
  
Lemma rprj_cntop Q Q' A A': (F2MF (@rprj Q Q' A A')) \is_continuous_operator.
Proof.
by rewrite cntop_F2MF => phi; exists (fun q => [:: inr q]) => psi q' [eq _]; rewrite /rprj eq.
Qed.

Lemma snd_hcr (X Y: cs): (@mf_snd X Y: _ \*_cs _ ->> _) \has_continuous_realizer.
Proof.
exists snd_rlzr; split; last exact/rprj_cntop.
by rewrite F2MF_rlzr_F2MF => phi x [].
Qed.

Lemma snd_cont (X Y: cs): (@snd X Y: _ \*_cs _ -> _) \is_continuous.
Proof. exact/snd_hcr. Qed.

Definition fprd_rlzr (X Y X' Y': cs) (F: (names X) ->> (names Y)) (G: (names X') ->> (names Y')):
  questions (X \*_cs X') ->> questions (Y \*_cs Y'):=
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
- rewrite name_split => [[phinx1 phinx2]].
  rewrite fprd_dom => [[fd1 fd2]].
  have [Fphi1 FphiFphi1]:= rlzr_dom rlzr phinx1 fd1.
  have [Fphi2 FphiFphi2]:= rlzr_dom rlzr' phinx2 fd2.
  exists (name_pair Fphi1 Fphi2).
  by rewrite /= lprj_pair rprj_pair.
rewrite name_split fprd_dom => [[phinx1 phinx2]] [fd1 fd2].
move => FGphi [-> [/=FphiFGphi GphiFGphi]].
have [y []]:= rlzr_val rlzr phinx1 fd1 FphiFGphi.
have [y' []]:= rlzr_val rlzr' phinx2 fd2 GphiFGphi.
by exists (y, y').
Qed.

Lemma fprd_rlzr_cntop (X Y X' Y': cs) (F: (names X) ->> (names Y))
	(G: (names X') ->> (names Y')): F \is_continuous_operator -> G \is_continuous_operator ->
	(fprd_rlzr F G) \is_continuous_operator.
Proof.
have mapl: forall K (q:queries X), List.In q K -> List.In ((@inl _ (queries X')) q) (map inl K).
	elim => // q K ih q' /=listin; by case: listin => ass; [left; rewrite -ass | right; apply ih].
have mapr: forall K (q:queries X'), List.In q K -> List.In ((@inr (queries X) _) q) (map inr K).
	elim => // q K ih q' /=listin; by case: listin => ass; [left; rewrite -ass | right; apply ih].
rewrite !cntop_spec => cont cont' phi [FGphi [np [/=FphiFGphi GphiFGphi]]].
have [ | Lf mod]:= cont (lprj phi); first by exists (lprj FGphi).
have [ | Lf' mod']:= cont' (rprj phi); first by exists (rprj FGphi).
exists (fun qq' => match qq' with
	| inl q => map inl (Lf q)
	| inr q' => map inr (Lf' q')
end) => [[q | q']].
- have [a' crt]:= mod q; exists (FGphi (inl q)).
  move => psi /coin_lstn coin Fpsi [ np' [/=val'l val'r]].
  rewrite np np'; apply injective_projections => //=.
  rewrite (crt (lprj phi) _ (lprj FGphi))//; last exact/coin_ref.
  rewrite (crt (lprj psi) _ (lprj Fpsi))// coin_lstn /lprj => q' lstn.
  by rewrite (coin (inl q')) //; apply (mapl (Lf q) q').
have [a' crt]:= mod' q'; exists (FGphi (inr q')).
move => psi /coin_lstn coin Fpsi [ np' [/=val'l val'r]].
rewrite np np'; apply injective_projections => //=.
rewrite (crt (rprj phi) _ (rprj FGphi))//; last exact/coin_ref.
rewrite (crt (rprj psi) _ (rprj Fpsi))// coin_lstn /rprj => q lstn.
by rewrite (coin (inr q)) //; apply (mapr (Lf' q') q).
Qed.

Lemma fprd_hcr (X Y X' Y': cs) (f: X ->> Y) (g: X' ->> Y'):
	f \has_continuous_realizer -> g \has_continuous_realizer -> (f ** g: cs_prod _ _ ->> cs_prod _ _) \has_continuous_realizer.
Proof.
move => [F [Frf Fcont]] [G [Grg Gcont]].
exists (fprd_rlzr F G).
split; [exact: fprd_rlzr_spec | exact: fprd_rlzr_cntop].
Qed.

Definition lcry_f S T R (f: S * T -> R) s t := f (s, t).

Definition lcry S T R (f: S * T ->> R) s :=
  make_mf (fun t fst => f (s,t) fst).

Lemma F2MF_lcry S T R (f: S * T -> R) s:
  F2MF (lcry_f f s) =~= lcry (F2MF f) s.
Proof. done. Qed.

Definition lcry_p S T R (f: S * T -> option R) s t := f (s, t).

Lemma PF2MF_lcry S T R (f: S * T -> option R) s:
  PF2MF (lcry_p f s) =~= lcry (PF2MF f) s.
Proof. done. Qed.

Definition lcry_rlzr (X Y Z: cs) (F: names (X \*_cs Y) ->> names Z) (phi: questions X):
  questions Y ->> questions Z:=
  (make_mf (fun psi Fphipsi => F (name_pair phi psi) Fphipsi)).

Lemma lcry_rlzr_spec (X Y Z: cs) F (f: X \*_cs Y ->> Z) phi x:
  F \realizes f -> phi \is_description_of x ->
  (lcry_rlzr F phi) \realizes (lcry f x).
Proof.
move => rlzr phinx psi y psiny xyfd.
by have []//:= rlzr (name_pair phi psi) (x, y).
Qed.

Fixpoint collect_right S T (L: seq (S + T)) := match L with
                      | nil => nil
                      | a :: L' => match a with
                                   | inr b => b :: (collect_right L')
                                   | inl _ => collect_right L'
                                   end
                      end.

Lemma lcry_rlzr_cntop (X Y Z: cs) (F: names (X \*_cs Y) ->> names Z) phi:
  F \is_continuous_operator -> (lcry_rlzr F phi) \is_continuous_operator.
Proof.
rewrite !cntop_spec => cont psi [Fphipsi /= val].
have [ | mf mod]:= cont (name_pair phi psi); first by exists Fphipsi.
exists (fun q => collect_right (mf q)) => q.
exists (Fphipsi q) => psi' coin Fphipsi' val'.
have [a' crt]:= mod q; apply/(crt_icf val crt)/val'.
by elim: (mf q) coin => // [[q' L ih /=/ih | q' L ih /= [-> /ih]]].
Qed.

Lemma lcry_hcr (X Y Z: cs) (f: X \*_cs Y ->> Z) x:
  f \has_continuous_realizer -> (lcry f x) \has_continuous_realizer.
Proof.
move => [F [rlzr cont]].
have [phi phinx]:= get_description x.  
exists (make_mf (fun psi Fphipsi => F (name_pair phi psi) Fphipsi)).
by split; [exact/lcry_rlzr_spec | exact/lcry_rlzr_cntop].
Qed.

Lemma lcry_cont (X Y Z: cs) (f: X * Y -> Z) x:
  f \is_continuous -> (lcry_f f x) \is_continuous.
Proof. by move => cont; rewrite /continuous F2MF_lcry; exact/lcry_hcr. Qed.

Definition rcry_f S T R (f: S * T -> R) t s := f (s, t).

Definition rcry S T R (f: S * T ->> R) t :=
  make_mf (fun s fst => f (s, t) fst).

Lemma F2MF_rcry S T R (f: S * T -> R) t:
  F2MF (rcry_f f t) =~= rcry (F2MF f) t.
Proof. done. Qed.

Definition rcry_p S T R (f: S * T -> option R) t s := f (s, t).

Lemma PF2MF_rcry S T R (f: S * T -> option R) t:
  PF2MF (rcry_p f t) =~= rcry (PF2MF f) t.
Proof. done. Qed.

Definition rcry_rlzr (X Y Z: cs) (F: names (X \*_cs Y) ->> names Z) (psi: questions Y):
  questions X ->> questions Z:=
  make_mf (fun phi Fphipsi => F (name_pair phi psi) Fphipsi).

Lemma rcry_rlzr_spec (X Y Z: cs) F (f: X \*_cs Y ->> Z) psi y:
  F \realizes f -> psi \is_description_of y ->
  (rcry_rlzr F psi) \realizes (rcry f y).
Proof.
move => rlzr psiny phi x phinx xyfd.
by have []//:= rlzr (name_pair phi psi) (x, y).
Qed.
  
Fixpoint collect_left S T (L: seq (S + T)) := match L with
                      | nil => nil
                      | a :: L' => match a with
                                   | inl b => b :: (collect_left L')
                                   | inr _ => collect_left L'
                                   end
                      end.

Lemma rcry_rlzr_cntop (X Y Z: cs) F psi:
  F \is_continuous_operator -> (@rcry_rlzr X Y Z F psi) \is_continuous_operator.
Proof.
  rewrite !cntop_spec => cont phi [Fphipsi /= val].
  have [ | mf mod]:= cont (name_pair phi psi); first by exists Fphipsi.
  exists (fun q => collect_left (mf q)) => q.
  exists (Fphipsi q) => psi' coin Fphipsi' val'.
  have [a' crt]:= mod q; apply/(crt_icf val crt)/val'.
  by elim: (mf q) coin => // [[q' L ih /= [-> /ih] | q' L ih /= /ih]].
Qed.

Lemma rcry_hcr (X Y Z: cs) (f: X * Y ->> Z) y:
  f \has_continuous_realizer -> (rcry f y) \has_continuous_realizer.
Proof.
move => [F [rlzr cont]].
have [psi psiny]:= get_description y.  
exists (rcry_rlzr F psi).
by split; [exact/rcry_rlzr_spec | exact/rcry_rlzr_cntop].
Qed.

Lemma rcry_cont (X Y Z: cs) (f: X * Y -> Z) y:
  f \is_continuous -> (rcry_f f y) \is_continuous.
Proof. by move => cont; rewrite /continuous F2MF_rcry; exact/rcry_hcr. Qed.
End products.

Lemma fprd_cont (X Y X' Y': cs) (f: X -> Y) (g: X' -> Y'):
  f \is_continuous -> g \is_continuous ->
  (f **_f g) \is_continuous.
Proof.
by move => cont cont' ; rewrite /continuous F2MF_fprd; apply/fprd_hcr.
Qed.
