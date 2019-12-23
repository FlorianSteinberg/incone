From mathcomp Require Import ssreflect ssrfun seq.
From rlzrs Require Import all_rlzrs.
Require Import all_cont representations cs naming_spaces cs_names.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope cs_scope.
Section products.
  Lemma prod_rep_spec (X Y: cs) : delta_ (X \*_cs Y) =~= delta ** delta \o delta.
  Proof. by rewrite prod_rep_spec /= sing_rcmp; last exact/F2MF_sing. Qed.

  Lemma prod_name_spec (X Y: cs) phi (x: X) (y: Y):
    phi \is_name_of (x,y) <-> (lprj phi) \is_name_of x /\ (rprj phi) \is_name_of y.
  Proof. by split => [[[? ?] [<-]] | []] //; exists (lprj phi, rprj phi). Qed.
  
  Definition fst_rlzr (X Y: cs) := F2MF (@lprj (B_ X) (B_ Y)).
  Local Arguments fst_rlzr {X} {Y}.

  Definition snd_rlzr (X Y: cs):= F2MF (@rprj (B_ X) (B_ Y)).
  Local Arguments snd_rlzr {X} {Y}.

  Lemma fst_rlzr_spec (X Y: cs): fst_rlzr \realizes (@fst X Y).
  Proof. by rewrite F2MF_rlzr  => phi x /prod_name_spec []. Qed.

  Lemma snd_rlzr_spec (X Y: cs): (@snd_rlzr X Y) \realizes snd.
  Proof. by rewrite F2MF_rlzr => phi x /prod_name_spec []. Qed.

  Definition diag_rlzr (X: cs):=F2MF (fun (phi: B_ X) => pair (phi, phi)).
  Local Arguments diag_rlzr {X}.

  Lemma diag_rlzr_spec (X: cs):
    diag_rlzr \solves (@mf_diag X: X ->> _).
  Proof. by rewrite F2MF_rlzr => ? ? ?; apply/prod_name_spec. Qed.

  Lemma lprj_pair (X Y: cs) (phi: B_ X) (psi: B_ Y):
    lprj (pair (phi,psi)) =  phi.
  Proof. by trivial. Qed.
  
  Lemma rprj_pair (X Y: cs) (phi: B_ X) (psi: B_ Y):
    rprj (pair (phi, psi)) =  psi.
  Proof. by trivial. Qed.

  Lemma fst_hcs (X Y: cs): (@fst X Y) \is_continuous.
  Proof.
    apply/hcs_spec; exists fst_rlzr; split; first exact/cont_F2MF/lprj_cont.
    by rewrite F2MF_rlzr => phi x /prod_name_spec [].
  Qed.

  Lemma fst_cont (X Y: cs): (@fst X Y) \is_continuous.
  Proof. exact/fst_hcs. Qed.
  
  Lemma snd_hcs (X Y: cs): (@mf_snd X Y) \has_continuous_realizer.
  Proof.
    apply/hcs_spec; exists snd_rlzr; split; first exact/cont_F2MF/rprj_cont.
    by rewrite F2MF_rlzr => phi x /prod_name_spec [].
  Qed.

  Lemma snd_cont (X Y: cs): (@snd X Y) \is_continuous.
  Proof. exact/snd_hcs. Qed.
  
  Definition fprd_frlzr (X Y X' Y': cs)
             (F: (B_ X) -> (B_ Y)) (G: (B_ X') -> (B_ Y'))
    phipsi:= pair (F (lprj phipsi),G (rprj phipsi)).

  Lemma	fprd_frlzr_rlzr (X Y X' Y': cs) (F: (B_ X) -> (B_ Y)) (G: (B_ X') -> (B_ Y')):
    F2MF (fprd_frlzr F G) =~= fprd_rlzr (F2MF F) (F2MF G).
  Proof.
    move => phi FGphi; rewrite {1}/F2MF.
    by split => [<- | [np [/=vall valr]]]; last by rewrite np /fprd_frlzr vall valr.
  Qed.
  
  Lemma fprd_rlzr_spec (X Y X' Y': cs) (f: X ->> Y) (g: X' ->> Y') F G:
    F \solves f -> G \solves g -> (fprd_rlzr F G) \solves (f ** g).
  Proof.
    move => /rlzr_delta rlzr /rlzr_delta rlzr'.
    rewrite rlzr_delta prod_rep_spec (prod_rep_spec (X:= Y)) fprd_rlzr_comp -!comp_assoc.
    apply/tight_comp_l => /=.
    rewrite !fprd_id (comp_assoc (_ ** _)) rcmp_id_l.
    have /sec_cncl ->:= (@pairK (B_ Y) (B_ Y')).
    rewrite comp_id_r !fprd_comp.
    exact/fprd_tight.
  Qed.
  
  Lemma fprd_hcs (X Y X' Y': cs) (f: X ->> Y) (g: X' ->> Y'):
    f \has_continuous_realizer -> g \has_continuous_realizer -> (f ** g) \has_continuous_realizer.
  Proof.
    move => [F [Frf Fcont]] [G [Grg Gcont]]; exists (fprd_rlzr F G).
    by split; [exact/fprd_cntop | exact/fprd_rlzr_spec].
  Qed.
  
  Lemma fprd_cont (X Y X' Y': cs) (f: X -> Y) (g: X' -> Y'):
    f \is_continuous -> g \is_continuous -> (f **_f g) \is_continuous.
  Proof. by move => cont cont' ; rewrite /continuous F2MF_fprd; apply/fprd_hcs. Qed.
    
  Lemma lcry_rlzr_spec (X Y Z: cs) F (f: X * Y ->> Z) phi x:
    F \solves f -> phi \is_name_of x -> (lcry_rlzr F phi) \solves (lcry f x).
  Proof.
    move => rlzr phinx psi y psiny xyfd.
    have []//:= rlzr (pair (phi, psi)) (x, y).
    exact/prod_name_spec.
  Qed.
  
  Lemma lcry_hcr (X Y Z: cs) (f: X * Y ->> Z) x:
    f \has_continuous_realizer -> (lcry f x) \has_continuous_realizer.
  Proof.
    move => [F [rlzr cont]].
    have [phi phinx]:= get_description x.  
    exists (lcry_rlzr F phi).
    by split; [exact/lcry_cntop | exact/lcry_rlzr_spec].
  Qed.

  Lemma lcry_cont (X Y Z: cs) (f: X * Y -> Z) x: f \is_continuous -> (lcry_f f x) \is_continuous.
  Proof. by move => cont; rewrite /continuous F2MF_lcry; exact/lcry_hcr. Qed.

  Lemma rcry_rlzr_spec (X Y Z: cs) F (f: X * Y ->> Z) psi y:
    F \solves f -> psi \is_description_of y ->
    (rcry_rlzr F psi) \solves (rcry f y).
  Proof.
    move => rlzr psiny phi x phinx xyfd.
    have []//:= rlzr (pair (phi, psi)) (x, y).
    exact/prod_name_spec.
  Qed.

  Lemma rcry_hcr (X Y Z: cs) (f: X * Y ->> Z) y:
    f \has_continuous_realizer -> (rcry f y) \has_continuous_realizer.
  Proof.
    move => [F [rlzr cont]].
    have [psi psiny]:= get_description y.  
    exists (rcry_rlzr F psi).
    by split; [exact/rcry_cntop | exact/rcry_rlzr_spec].
  Qed.

  Lemma rcry_cont (X Y Z: cs) (f: X * Y -> Z) y:
    f \is_continuous -> (rcry_f f y) \is_continuous.
  Proof. by move => cont; rewrite /continuous F2MF_rcry; exact/rcry_hcr. Qed.

End products.

Class Uncurry T (f : T) src tgt := {prog : src -> tgt}.
Arguments prog {T} f {src tgt _}.

Instance Uncurry_base (X Y: cs) f: @Uncurry (X -> Y) f _ _ := {| prog := f |}.
Instance Uncurry_step (X Y: cs) Z (f : X -> Y -> Z)
                       T (g: forall a, @Uncurry (Y -> Z) (f a) Y T) :
                                          @Uncurry (X -> Y -> Z) f (cs_prod X Y) T :=
  {| prog := (fun x : X \*_cs Y => @prog _ _ _ _ (g (fst x)) (snd x)) |}.
Notation "f '\is_continuous'" := (@continuous _ _ (prog f)) (at level 2): curry_scope.
Delimit Scope curry_scope with curry.
Open Scope curry_scope.
