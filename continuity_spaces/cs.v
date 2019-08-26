From mathcomp Require Import ssreflect ssrfun.
From rlzrs Require Import all_rlzrs dict.
Require Import all_names.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope cs_scope with cs.
Local Open Scope cs_scope.

Class is_representation (B: naming_space) (X: Type) (delta: B ->> X) :=
  {
    surjective: delta \is_cototal;
    deterministic: delta \is_singlevalued;
  }.

Global Instance R2D `{R: is_representation}: Dictionary delta.
  by split; first exact/surjective; exact/deterministic.
Defined.

Notation "delta \is_representation" := (is_representation delta) (at level 30).

Structure continuity_space :=
  {
    space: Type;
    names: naming_space;
    representation: names ->> space;
    represented: representation \is_representation;
  }.

Notation delta:= (representation _).
Coercion space: continuity_space >-> Sortclass.
Global Instance rep_rep (X: continuity_space): (representation X) \is_representation.
Proof. exact/represented. Qed.

Notation rs:= continuity_space.
Notation represented_space := continuity_space.
Notation cs:= continuity_space.
Notation name_space := names.
Notation queries X := (questions (names X)).
Notation answers X := (answers (name_space X)).
Notation B := (name_space _).
Notation "F \realizes f" := (realizer delta delta F f) (at level 30): cs_scope.
Notation rep X := (representation X).
Notation "phi '\describes' x '\wrt' X" := (rep X phi x) (at level 2): cs_scope.
Notation "phi '\is_name_of' x" := (delta phi x) (at level 2): cs_scope.
Notation "phi '\is_description_of' x" := (delta phi x) (at level 2): cs_scope.
Definition descriptions_of (X: cs) (x: X) := (rep X)\^-1 x.
Notation names_of x := (descriptions_of x).
Notation some_query := (someq B).

Section continuity_spaces.
  Lemma Q_count (X: rs): (queries X) \is_countable.
  Proof. exact/(Q_count B). Qed.

  Lemma Q_inh (X: cs): inhabited (queries X).
  Proof. exact/inhabits/(default_question B). Qed.

  Lemma A_count (X: cs): (answers X) \is_countable.
  Proof. exact/(A_count B). Qed.

  Lemma rep_sur (X: cs): (representation X) \is_cototal.
  Proof. exact/only_respond. Qed.

  Lemma rep_sing (X: cs): (representation X) \is_singlevalued.
  Proof. exact/answers_unique. Qed.

  Lemma split_rlzr (X Y: rs) F (f: X ->> Y):
    (forall phi x, phi \is_name_of x -> x \from dom f -> phi \from dom F) ->
    (forall phi x, phi \is_name_of x -> x \from dom f -> forall Fphi, Fphi \from F phi -> exists fx, Fphi \is_name_of fx /\ fx \from f x) -> F \realizes f.
  Proof. by move => dm val; apply/split_rlzr. Qed.

  Lemma rlzr_comp (X Y Z: rs) F G (f: Y ->> Z) (g: X ->> Y):
    F \realizes f -> G \realizes g -> (F \o G) \realizes (f \o g).
  Proof. exact/rlzr_comp. Qed.

  Lemma rlzr_tight (X Y: rs) F (f g: X ->> Y):
    F \realizes f -> f \tightens g -> F \realizes g.
  Proof. exact/rlzr_tight. Qed.

  Lemma tight_rlzr (X Y: rs) F G (f: X ->> Y):
    F \realizes f -> G \tightens F -> G \realizes f.
  Proof. exact/tight_rlzr. Qed.

  Lemma id_rlzr (X: rs): mf_id \realizes (@mf_id X).
  Proof. exact/id_rlzr. Qed.

  Lemma cnst_rlzr (X Y: rs) phi (y: Y): phi \is_name_of y -> mf_cnst phi \realizes (@mf_cnst X Y y).
  Proof. by move => phinx; apply/cnst_rlzr. Qed.

  Lemma rlzr_spec (X Y: rs) F (f: X ->> Y): F \realizes f <-> (delta \o F) \tightens (f \o delta).
  Proof. exact/rlzr_spec. Qed.
 
  Lemma rlzr_F2MF_eq (X Y: rs) F (f g: X -> Y):
    F \realizes (F2MF f) -> F \realizes (F2MF g) -> f =1 g.
  Proof. exact/rlzr_F2MF_eq. Qed.
  
  Lemma rlzr_dom_p (X Y: rs) F (f: X ->> Y):
    F \realizes f -> inv_img delta (dom f) \is_subset_of dom F.
  Proof. by move => rlzr phi [x [phinx xfd]]; apply/rlzr_dom/xfd/phinx/rlzr. Qed.
  
  Lemma rlzr_dom (X Y: rs) F (f: X ->> Y): f \is_total ->
    F \realizes f -> dom delta \is_subset_of dom F.
  Proof. by move => tot rlzr phi [x phinx]; apply/rlzr_dom/tot/phinx/rlzr. Qed.

  Lemma rlzr_val (X Y: rs) F (f: X -> Y) phi x:
    F \realizes (F2MF f) -> phi \is_name_of x -> F phi \is_subset_of names_of (f x).
  Proof.
    move => rlzr phinx Fphi val.
    by have [ | fx [vl ->]]:= rlzr_val rlzr phinx _ val; first exact/F2MF_tot.
  Qed.

  Lemma sing_rlzr_F2MF (X Y: rs) F (f: X -> Y): F \is_singlevalued ->
    F \realizes (F2MF f) <-> dom delta \is_subset_of dom F
                             /\
                             forall phi x, phi \is_name_of x -> F phi \is_subset_of names_of (f x).
  Proof.
    move => sing; rewrite sing_rlzr_F2MF //.
    by split; case => subs val; split => // phi x a b; exact/val.
  Qed.

  Lemma PF2MF_rlzr_F2MF (X Y: rs) F (f: X -> Y): (PF2MF F) \realizes (F2MF f) <->
    dom delta \is_subset_of dom F
    /\
    forall phi x, (sval phi) \is_name_of x -> (F phi) \is_name_of (f x).
  Proof. exact/PF2MF_rlzr_F2MF. Qed.
End continuity_spaces.  
Notation get_description:= rep_sur.
Notation get_name := rep_sur.
Notation "F \is_continuous_operator" := (continuous F) (at level 30): cs_scope.
Notation "f \is_continuous_functional" := (continuous_function f) (at level 30): cs_scope.

Section continuity.
  Definition has_continuous_realizer (X Y : cs) (f : X ->> Y) :=
    exists F, F \realizes f /\ F \is_continuous_operator.
  Local Notation "f '\has_continuous_realizer'":= (has_continuous_realizer f) (at level 2).
  Local Notation hcr := has_continuous_realizer.
  Global Instance hcr_prpr (X Y: cs):
    Proper (@equiv X Y ==> iff) (@hcr X Y).
  Proof.
    by move => f g feg; split; move => [F [Frf Fcont]]; exists F; [rewrite -feg | rewrite feg].
  Qed.
  
  Lemma comp_hcr (X Y Z: cs) (f: X ->> Y) (g: Y ->> Z):
    f \has_continuous_realizer -> g \has_continuous_realizer -> (g \o f) \has_continuous_realizer.
  Proof.
    move => [F [Frf Fcont]] [G [Grg Gcont]].
    by exists (G \o F); split; [exact/rlzr_comp | exact/cont_comp].
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

  Lemma cont_comp (X Y Z: rs) (f: Y -> Z) (g: X -> Y):
    f \is_continuous -> g \is_continuous -> (f \o_f g) \is_continuous.
  Proof. by rewrite /continuous -F2MF_comp_F2MF => cont cont'; apply/comp_hcr. Qed.

  Lemma cont_spec (X Y: rs) (f: X -> Y): f \is_continuous <->
    exists F, F \is_continuous_operator
              /\
              dom (rep X) \is_subset_of (dom F)
              /\
              forall (phi: name_space X) (x: X),
                phi \describes x \wrt X -> F phi \is_subset_of names_of (f x).
  Proof.    
    split => [[F [rlzr cont]] | [F [cont [dm val]]]]; exists F; split => //.
    - have /sing_rlzr_F2MF [ | dm val] := rlzr; first exact/cont_sing.
      split => [phi [x phinx] | phi x phinx Fphi]; last exact/val.
      by apply/dm; exists x.
    apply/sing_rlzr_F2MF; first exact/cont_sing.
    by split => [phi [x phinx] | phi x Fphi phinx]; [apply/dm; exists x | apply/val].
  Qed.
End continuity.
Notation cntop_spec:= cont.cont_spec. 
Notation hcr := has_continuous_realizer.
Notation "f '\has_continuous_realizer'":= (hcr f) (at level 2): cs_scope.
Notation "f \is_continuous" := (continuous f) (at level 2): cs_scope.

Section cs_product.
  
  Definition prod_rep X Y :=
    make_mf (fun (phipsi : product_names (name_space X) (name_space Y)) xy =>
               (rep X ** rep Y) (lprj phipsi, rprj phipsi) xy).  
    
  Definition name_pair X Y (phi: name_space X) (psi: name_space Y) := pair (phi,psi).

  Lemma prod_rep_sur (X Y: cs): (@prod_rep X Y) \is_cototal.
  Proof.
    move => [x y].
    have [phi phinx]:= rep_sur x.
    have [psi psiny]:= rep_sur y.
    exists (pair (phi, psi)) => /=.
    by rewrite lprj_pair rprj_pair.
  Qed.

  Lemma prod_rep_sing (X Y: cs): (@prod_rep X Y) \is_singlevalued.
  Proof.
    move => phipsi [x y] [x' y'] [/=phinx psiny] [phinx' psiny'].
    by rewrite (rep_sing phinx phinx') (rep_sing psiny psiny').
  Qed.

  Canonical cs_prod (X Y: rs): rs.
  exists (X * Y)%type (product_names (name_space X) (name_space Y)) (prod_rep X Y).
  by split; [exact/prod_rep_sur | exact/prod_rep_sing].
  Defined.
End cs_product.

Section cs_sum.
  Definition sum_rep (X Y: rs) :=
    ((rep X) +s+ (rep Y)) \o_R (F2MF (@slct (names X) (names Y))).
  
  Lemma sum_rep_sur (X Y: cs): (@sum_rep X Y) \is_cototal.
  Proof.
    apply/rcmp_cotot.
    - exact/fsum_cotot/rep_sur/rep_sur.
    by rewrite -F2MF_cotot; apply/slct_sur.
  Qed.                                     
  
  Lemma sum_rep_sing (X Y: cs): (@sum_rep X Y) \is_singlevalued.
  Proof. exact/rcmp_sing/F2MF_sing/fsum_sing/rep_sing/rep_sing. Qed.

  Canonical cs_sum (X Y: rs): rs.
    exists (X + Y)%type (sum_names (names X) (names Y)) (sum_rep X Y).
    by split; [apply/sum_rep_sur | apply/sum_rep_sing].
  Defined.  
End cs_sum.