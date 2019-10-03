From mathcomp Require Import ssreflect ssrfun.
From rlzrs Require Import all_rlzrs dict.
Require Import all_cont naming_spaces representations.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope cs_scope with cs.
Local Open Scope cs_scope.

Structure continuity_space :=
  {
    space:> Type;
    name_space: naming_space;
    representation: name_space ->> space;
    represented: representation \is_representation;
  }.

Global Instance rep_rep (X: continuity_space): (representation X) \is_representation.
Proof. exact/represented. Qed.

Definition rep2cs X (delta: representation_of X): continuity_space.
  exists X (representations.name_space) delta.
  apply representations.representation.
Defined.

Definition get_representation_of (X: continuity_space): representation_of X.
  by exists (name_space X) (representation X); apply/represented.
Defined.

Notation rep := get_representation_of.
Notation "'delta_' X" := (get_representation_of X) (at level 30, format "'delta_' X").
Notation delta := (get_representation_of _).

Notation cs:= continuity_space.
Definition solution (X Y: cs) (f: X ->> Y) (F: name_space X ->> name_space Y):=
  realizer delta delta F f.
Notation queries X := (questions (name_space X)).
Notation replies X := (answers (name_space X)).
Notation "'Q_' X" := (queries X) (format "'Q_' X", at level 5): cs_scope.
Notation "'A_' X" := (replies X) (format "'A_' X", at level 5): cs_scope.
Notation "'B_' X" := (name_space X) (format "'B_' X", at level 5): cs_scope.
Notation "F \solves f" := (solution f F) (at level 30): cs_scope.
Notation "F \realizes f" := (F \solves (F2MF f)) (at level 30): cs_scope.
Notation "phi '\describes' x '\wrt' X" := ((representation X) phi x) (at level 30): cs_scope.
Notation "phi '\is_name_of' x" := (delta phi x) (at level 30): cs_scope.
Notation "phi '\is_description_of' x" := (delta phi x) (at level 30): cs_scope.
Definition descriptions_of (X: cs) (x: X) := (representation X)\^-1 x.
Notation names_of x := (descriptions_of x).
Notation some_query := (someq (name_space _)).

Section continuity_spaces.
  Lemma Q_count (X: cs): (queries X) \is_countable.
  Proof. exact/Q_count. Qed.

  Lemma Q_inh (X: cs): inhabited (queries X).
  Proof. exact/inhabits/default_question. Qed.

  Lemma A_count (X: cs): (replies X) \is_countable.
  Proof. exact/A_count. Qed.

  Lemma rep_sur (X: cs): (representation X) \is_cototal.
  Proof. exact/only_respond. Qed.

  Lemma rep_sing (X: cs): (representation X) \is_singlevalued.
  Proof. exact/answers_unique. Qed.

  Lemma split_slvs (X Y: cs) F (f: X ->> Y):
    (forall phi x, phi \is_name_of x -> x \from dom f -> phi \from dom F) ->
    (forall phi x, phi \is_name_of x -> x \from dom f -> forall Fphi, Fphi \from F phi -> exists fx, Fphi \is_name_of fx /\ fx \from f x) -> F \solves f.
  Proof. by move => dm val; apply/split_rlzr. Qed.

  Lemma slvs_comp (X Y Z: cs) F G (f: Y ->> Z) (g: X ->> Y):
    F \solves f -> G \solves g -> (F \o G) \solves (f \o g).
  Proof. exact/rlzr_comp. Qed.

  Lemma rlzr_comp (X Y Z: cs) F G (f: Y -> Z) (g: X -> Y):
    F \realizes f -> G \realizes g -> (F \o G) \realizes (f \o_f g).
  Proof. by rewrite /solution -F2MF_comp_F2MF; apply/slvs_comp. Qed.

  Lemma slvs_tight (X Y: cs) F (f g: X ->> Y):
    F \solves f -> f \tightens g -> F \solves g.
  Proof. exact/rlzr_tight. Qed.

  Definition rlzr_tight:= slvs_tight.

  Lemma tight_slvs (X Y: cs) F G (f: X ->> Y):
    F \solves f -> G \tightens F -> G \solves f.
  Proof. exact/tight_rlzr. Qed.

  Definition tight_rlzr:= tight_slvs.

  Lemma id_rlzr (X: cs): mf_id \realizes (@id X).
  Proof. exact/id_rlzr. Qed.

  Lemma cnst_rlzr (X Y: cs) phi (y: Y):
    phi \is_name_of y -> mf_cnst phi \realizes (@cnst X Y y).
  Proof. by move => phinx; apply/cnst_rlzr. Qed.

  Lemma slvs_delta (X Y: cs) F (f: X ->> Y): F \solves f <-> (delta \o F) \tightens (f \o delta).
  Proof. exact/rlzr_spec. Qed.

  Definition rlzr_delta:= slvs_delta.
  
  Lemma rlzr_F2MF_eq (X Y: cs) F (f g: X -> Y):
    F \realizes f -> F \realizes g -> f =1 g.
  Proof. exact/rlzr_F2MF_eq. Qed.
  
  Lemma slvs_val (X Y: cs) F (f: X ->> Y) phi Fphi x: F \solves f ->
    phi \is_name_of x -> x \from dom f -> Fphi \from F phi ->
    exists fx: f x, Fphi \is_name_of (sval fx).
  Proof.
    move => slvs phinx xfd val.
    have [fx [Fphinfx val']]:= rlzr_val slvs phinx xfd val.
    by exists (exist _ fx val').
  Qed.                                                      
  
  Lemma slvs_dom (X Y: cs) F (f: X ->> Y):
    F \solves f -> inv_img delta (dom f) \is_subset_of dom F.
  Proof. by move => rlzr phi [x [phinx xfd]]; apply/rlzr_dom/xfd/phinx/rlzr. Qed.
  
  Lemma slvs_dom_tot (X Y: cs) F (f: X ->> Y): f \is_total ->
    F \solves f -> dom delta \is_subset_of dom F.
  Proof. by move => tot rlzr phi [x phinx]; apply/rlzr_dom/tot/phinx/rlzr. Qed.

  Lemma rlzr_dom (X Y: cs) F (f: X -> Y): F \realizes f -> dom delta \is_subset_of dom F.
  Proof. exact/slvs_dom_tot/F2MF_tot. Qed.

  Lemma rlzr_val (X Y: cs) F (f: X -> Y) phi x:
    F \realizes f -> phi \is_name_of x -> F phi \is_subset_of names_of (f x).
  Proof.
    move => rlzr phinx Fphi val.
    by have [ | fx [vl ->]]:= rlzr_val rlzr phinx _ val; first exact/F2MF_tot.
  Qed.

  Lemma slvs_dep (X Y: cs) F (f: X ->> Y):
    F \solves f <-> forall (x: dom f) (phi: names_of (sval x)),
      (sval phi) \from dom F
      /\
      forall (Fphi: F (sval phi)), exists (fx: f (sval x)), (sval Fphi) \is_name_of (sval fx).
  Proof.
    split => [slvs [/=x xfd] [/=phi phinx] | slvs phi x phinx xfd]; last first.
    - have [dm vl]//:= slvs (exist _ _ xfd) (exist _ phi _).
      by split => // Fphi val; have [[fx]]:= vl (exist _ _ val); exists fx.
    have [dm vl]:= slvs phi x phinx xfd; split => //; case => Fphi val.
    by have [fx [Fphinfx val']]:= vl Fphi val; exists (exist _ _ val').
  Qed.

  Lemma rlzr_spec (X Y: cs) F (f: X -> Y): F \realizes f <->
    dom delta \is_subset_of (dom F)
    /\
    forall phi x, phi \describes x \wrt X -> F phi \is_subset_of names_of (f x).
  Proof.
    split => [rlzr | [dm vl]].
    - by split => [ | phi x]; [apply/rlzr_dom/rlzr | apply/rlzr_val/rlzr].
    apply/split_rlzr => phi x phinx _; first by apply/dm; exists x.
    by move => Fphi val; exists (f x); split => //; apply/vl/val.
  Qed.

  Lemma F2MF_slvs (X Y: cs) F (f: X ->> Y): F2MF F \solves f <->
    forall phi x, phi \is_name_of x -> x \from dom f -> exists fx, F phi \is_name_of fx /\ fx \from f x.
  Proof. exact/F2MF_rlzr. Qed.  

  Lemma F2MF_rlzr (X Y: cs) F (f: X -> Y):
    F2MF F \realizes f <-> forall phi x, phi \is_name_of x -> F phi \is_name_of f(x).
  Proof. exact/F2MF_rlzr_F2MF. Qed.
  
  Lemma sing_rlzr (X Y: cs) F (f: X -> Y): F \is_singlevalued ->
    F \realizes f <-> dom delta \is_subset_of dom F
                      /\
                      forall phi x, phi \is_name_of x -> F phi \is_subset_of names_of (f x).
  Proof.
    move => sing; rewrite /solution sing_rlzr_F2MF //.
    by split; case => subs val; split => // phi x a b; exact/val.
  Qed.

  Lemma PF2MF_rlzr (X Y: cs) F (f: X -> Y): (PF2MF F) \realizes f <->
    dom delta \is_subset_of dom F
    /\
    forall phi x, (sval phi) \is_name_of x -> (F phi) \is_name_of (f x).
  Proof. exact/PF2MF_rlzr_F2MF. Qed.
End continuity_spaces.  
Notation get_description:= rep_sur.
Notation get_name := rep_sur.

Section continuity.
  Definition has_continuous_realizer (X Y : cs) (f : X ->> Y) :=
    exists F, F \is_continuous_operator /\ F \solves f.
  Local Notation "f '\has_continuous_realizer'":= (has_continuous_realizer f) (at level 2).
  Local Notation hcr := has_continuous_realizer.
  Global Instance hcr_prpr (X Y: cs):
    Proper (@equiv X Y ==> iff) (@hcr X Y).
  Proof.
    move => f g feg.
    by split; move => [F [Frf Fcont]]; exists F; [rewrite /solution -feg | rewrite /solution feg].
  Qed.
  
  Lemma comp_hcr (X Y Z: cs) (f: X ->> Y) (g: Y ->> Z):
    f \has_continuous_realizer -> g \has_continuous_realizer -> (g \o f) \has_continuous_realizer.
  Proof.
    move => [F [Frf Fcont]] [G [Grg Gcont]].
    by exists (G \o F); split; [exact/cont_comp | exact/slvs_comp].
  Qed.
  
  Definition continuous (X Y: cs) (f: X -> Y):= (F2MF f) \has_continuous_realizer.
  Local Notation "f \is_continuous" := (continuous f) (at level 2).

  Global Instance cont_prpr (X Y: cs):
    Proper (@eqfun Y X ==> iff) (@continuous X Y).
  Proof. by move => f g /F2MF_eq eq; rewrite /continuous eq. Qed.

  Lemma cntop_cntf (B B': naming_space) (f: B -> B'):
    (F2MF f) \is_continuous_operator <-> f \is_continuous_functional.
  Proof. by rewrite cont_F2MF. Qed.

  Lemma cntop_comp (B B' B'': naming_space) (F: B' ->> B'') (G: B ->> B'):
    F \is_continuous_operator -> G \is_continuous_operator -> (F \o G) \is_continuous_operator.
  Proof. by move => cont cont'; apply/cont_comp. Qed.

  Lemma cont_comp (X Y Z: cs) (f: Y -> Z) (g: X -> Y):
    f \is_continuous -> g \is_continuous -> (f \o_f g) \is_continuous.
  Proof. by rewrite /continuous -F2MF_comp_F2MF => cont cont'; apply/comp_hcr. Qed.

  Lemma cont_spec (X Y: cs) (f: X -> Y): f \is_continuous <->
    exists F, F \is_continuous_operator
              /\
              F \realizes f.
  Proof. done. Qed.
    
  Lemma F2MF_cont (X Y: cs) (f: X -> Y):
  (exists F, F \is_continuous_functional /\ (F2MF F) \realizes f) -> f \is_continuous.
  Proof. by move => [F [cont rlzr]]; exists (F2MF F); split; try apply/cont_F2MF. Qed.  
End continuity.
Notation cntop_spec:= cont.cont_spec. 
Notation hcr := has_continuous_realizer.
Notation "f '\has_continuous_realizer'":= (hcr f) (at level 2): cs_scope.
Notation "f \is_continuous" := (continuous f) (at level 2): cs_scope.

Section products_and_sums.
  Context (X Y: cs).

  Definition product_representation:=
    representation X ** representation Y \o F2MF (@unpair (B_ X) (B_ Y)).

  Lemma prod_rep_sur: product_representation \is_cototal.
  Proof. exact/comp_cotot/F2MF_sur/unpair_sur/fprd_cotot/rep_sur/rep_sur/F2MF_sing. Qed.

  Lemma prod_rep_sing: product_representation \is_singlevalued.
  Proof. exact/comp_sing/F2MF_sing/fprd_sing/rep_sing/rep_sing. Qed.

  Canonical cs_prod: cs.
  exists (X * Y)%type (product_names (name_space X) (name_space Y)) product_representation.
  by split; [exact/prod_rep_sur | exact/prod_rep_sing].
  Defined.

  Definition sum_representation :=
    representation X +s+ representation Y \o (F2MF (@slct (name_space X) (name_space Y))).
  
  Lemma sum_rep_sur: sum_representation \is_cototal.
  Proof. exact/comp_cotot/F2MF_sur/slct_sur/fsum_cotot/rep_sur/rep_sur/F2MF_sing. Qed.
  
  Lemma sum_rep_sing: sum_representation \is_singlevalued.
  Proof. exact/comp_sing/F2MF_sing/fsum_sing/rep_sing/rep_sing. Qed.

  Canonical cs_sum: cs.
    exists (X + Y)%type (sum_names (name_space X) (name_space Y)) sum_representation.
    by split; [apply/sum_rep_sur | apply/sum_rep_sing].
  Defined.  
End products_and_sums.
Notation "X \*_cs Y":= (cs_prod X Y) (at level 30): cs_scope.
