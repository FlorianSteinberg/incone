From mathcomp Require Import ssreflect ssrfun seq.
From rlzrs Require Import all_rlzrs.
Require Import all_cont cs naming_spaces rs_names.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope cs_scope.
Section products.
  Lemma prod_rep_spec (X Y: cs) : prod_rep X Y =~= (rep X ** rep Y) \o delta.
  Proof.
    rewrite sing_rcmp; last exact/rep_sing.
    by rewrite prod_rep_spec => phi psi; split => [ | [_ [<-] []]] //; exists (lprj phi, rprj phi).
  Qed.

  Lemma name_split (X Y: rs) phi (xy: X * Y): phi \is_name_of xy <->
    (lprj phi) \is_name_of (xy.1) /\ (rprj phi) \is_name_of (xy.2).
  Proof. done. Qed.

  Lemma split_name (X Y: rs) phi psi (x: X) (y: Y): (pair (phi,psi)) \is_name_of (x,y) <->
                                                    phi \is_name_of x /\ psi \is_name_of y.
  Proof. done. Qed.
  
  Definition fst_rlzr (X Y: cs): name_space _ ->> name_space X :=
    F2MF (@lprj (name_space X) (name_space Y)).
  Local Arguments fst_rlzr {X} {Y}.

  Definition snd_rlzr (X Y: cs): name_space _ ->> name_space Y:=
    F2MF (@rprj (name_space X) (name_space Y)).
  Local Arguments snd_rlzr {X} {Y}.

  Lemma fst_rlzr_spec (X Y: cs): fst_rlzr \realizes (@mf_fst X Y).
  Proof. by rewrite F2MF_rlzr_F2MF => phi x [phinx _]. Qed.

  Lemma snd_rlzr_spec (X Y: cs): (@snd_rlzr X Y) \realizes mf_snd.
  Proof. by rewrite F2MF_rlzr_F2MF => phi x [_ phinx]. Qed.

  Definition diag_rlzr (X: cs): name_space X ->> name_space _:=
    F2MF (fun (phi: name_space X) => name_pair phi phi).
  Local Arguments diag_rlzr {X}.

  Lemma diag_rlzr_spec (X: cs):
    diag_rlzr \realizes (@mf_diag X: X ->> _).
  Proof. by rewrite F2MF_rlzr_F2MF. Qed.

  Lemma lprj_pair (X Y: cs) (phi: name_space X) (psi: name_space Y):
    lprj (name_pair phi psi) =  phi.
  Proof. by trivial. Qed.
  
  Lemma rprj_pair (X Y: cs) (phi: name_space X) (psi: name_space Y):
    rprj (name_pair phi psi) =  psi.
  Proof. by trivial. Qed.

  Lemma fst_hcr (X Y: rs): (@mf_fst X Y) \has_continuous_realizer.
  Proof.
    exists fst_rlzr.
    split; last exact/cont_F2MF/(@lprj_cont B B).
    by rewrite F2MF_rlzr_F2MF => phi x [].
  Qed.

  Lemma fst_cont (X Y: cs): (@fst X Y) \is_continuous.
  Proof. exact/fst_hcr. Qed.
  
  Lemma snd_hcr (X Y: cs): (@mf_snd X Y) \has_continuous_realizer.
  Proof.
    exists snd_rlzr; split; last exact/cont_F2MF/rprj_cont.
    by rewrite F2MF_rlzr_F2MF => phi x [].
  Qed.

  Lemma snd_cont (X Y: cs): (@snd X Y) \is_continuous.
  Proof. exact/snd_hcr. Qed.
  
  Definition fprd_frlzr (X Y X' Y': cs)
             (F: (name_space X) -> (name_space Y)) (G: (name_space X') -> (name_space Y'))
    phipsi:= pair (F (lprj phipsi),G (rprj phipsi)).

  Lemma	fprd_frlzr_rlzr (X Y X' Y': cs) (F: (name_space X) -> (name_space Y)) (G: (name_space X') -> (name_space Y')):
    F2MF (fprd_frlzr F G) =~= fprd_rlzr (F2MF F) (F2MF G).
  Proof.
    move => phi FGphi; rewrite {1}/F2MF.
    by split => [<- | [np [/=vall valr]]]; last by rewrite np /fprd_frlzr vall valr.
  Qed.
  
  Lemma fprd_rlzr_spec (X Y X' Y': cs) (f: X ->> Y) (g: X' ->> Y') F G:
    F \realizes f -> G \realizes g -> (fprd_rlzr F G) \realizes (f ** g).
  Proof.
    move => /rlzr_spec rlzr /rlzr_spec rlzr'.
    rewrite rlzr_spec/= !prod_rep_spec fprd_rlzr_comp -!comp_assoc.
    apply/tight_comp_l.
    rewrite (comp_assoc (_ ** _)) !rs_names.prod_rep_spec.    
    have /sec_cncl ->:= (@pairK (name_space Y) (name_space Y')).
    rewrite comp_id_r !fprd_comp.
    exact/fprd_tight.
  Qed.
  
  Lemma fprd_hcr (X Y X' Y': cs) (f: X ->> Y) (g: X' ->> Y'):
    f \has_continuous_realizer -> g \has_continuous_realizer -> (f ** g) \has_continuous_realizer.
  Proof.
    move => [F [Frf Fcont]] [G [Grg Gcont]]; exists (fprd_rlzr F G).
    by split; [exact: fprd_rlzr_spec | exact: fprd_cntop].
  Qed.
  
  Lemma fprd_cont (X Y X' Y': cs) (f: X -> Y) (g: X' -> Y'):
    f \is_continuous -> g \is_continuous -> (f **_f g) \is_continuous.
  Proof. by move => cont cont' ; rewrite /continuous F2MF_fprd; apply/fprd_hcr. Qed.
    
  Lemma lcry_rlzr_spec (X Y Z: cs) F (f: X * Y ->> Z) phi x:
    F \realizes f -> phi \is_name_of x -> (lcry_rlzr F phi) \realizes (lcry f x).
  Proof.
    move => rlzr phinx psi y psiny xyfd.
    by have []//:= rlzr (name_pair phi psi) (x, y).
  Qed.
  
  Lemma lcry_hcr (X Y Z: cs) (f: X * Y ->> Z) x:
    f \has_continuous_realizer -> (lcry f x) \has_continuous_realizer.
  Proof.
    move => [F [rlzr cont]].
    have [phi phinx]:= get_description x.  
    exists (lcry_rlzr F phi).
    by split; [exact/lcry_rlzr_spec | exact/lcry_cntop].
  Qed.

  Lemma lcry_cont (X Y Z: cs) (f: X * Y -> Z) x: f \is_continuous -> (lcry_f f x) \is_continuous.
  Proof. by move => cont; rewrite /continuous F2MF_lcry; exact/lcry_hcr. Qed.

  Lemma rcry_rlzr_spec (X Y Z: cs) F (f: X * Y ->> Z) psi y:
    F \realizes f -> psi \describes y \wrt Y ->
    (rcry_rlzr F psi) \realizes (rcry f y).
  Proof.
    move => rlzr psiny phi x phinx xyfd.
    by have []//:= rlzr (name_pair phi psi) (x, y).
  Qed.

  Lemma rcry_hcr (X Y Z: cs) (f: X * Y ->> Z) y:
    f \has_continuous_realizer -> (rcry f y) \has_continuous_realizer.
  Proof.
    move => [F [rlzr cont]].
    have [psi psiny]:= get_description y.  
    exists (rcry_rlzr F psi).
    by split; [exact/rcry_rlzr_spec | exact/rcry_cntop].
  Qed.

  Lemma rcry_cont (X Y Z: cs) (f: X * Y -> Z) y:
    f \is_continuous -> (rcry_f f y) \is_continuous.
  Proof. by move => cont; rewrite /continuous F2MF_rcry; exact/rcry_hcr. Qed.
End products.

Class Uncurry T (f : T) src tgt := { prog : src -> tgt}.
Arguments prog {T} f {src tgt _}.

Instance Uncurry_base (A B : cs) f : @Uncurry (A -> B) f _ _ :=
  {| prog := f |}.
Instance Uncurry_step (A B : cs) C (f : A -> B -> C)
                       T (g : forall a, @Uncurry (B -> C) (f a) B T) :
                                          @Uncurry (A -> B -> C) f (cs_prod A B) T :=
  {| prog := (fun x : A * B => @prog _ _ _ _ (g (fst x)) (snd x)) |}.
Notation "f '\is_continuous'" := (@continuous _ _ (prog f)) (at level 2): curry_scope.
Delimit Scope curry_scope with curry.