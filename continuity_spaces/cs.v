From mathcomp Require Import ssreflect ssrfun.
From rlzrs Require Import all_mf all_rlzrs dict.
Require Import all_baire.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module continuity_space.
  Record mixin_of Q A :=
    Mixin {
        someq: Q;
        somea: A;
        Q_count: Q \is_countable;
        A_count: A \is_countable;
      }.
  
  Record class_of Q A X:=
    Class {
        I: interview.mixin_of (Q -> A) X;
        D: dictionary.mixin_of (conversation I);
        M: mixin_of Q A
      }.
        
  Structure type := Pack {X; Q; A; mixin: class_of Q A X}. 
End continuity_space.

Notation continuity_space := (continuity_space.type).
Delimit Scope cs_scope with cs.
Local Open Scope cs_scope.

Section continuity_spaces.
  Local Notation cs:= continuity_space.
  Local Coercion continuity_space.mixin: cs >-> continuity_space.class_of.
  Canonical space_class (X: cs) := (@dictionary.Class _ (interview.Struc (continuity_space.I X)) (continuity_space.D X)).
  Canonical space (X: cs) := dictionary.Pack (space_class X).
  Local Coercion space: cs >-> dictionary.
  Local Notation queries:= continuity_space.Q.
  Local Notation answers := continuity_space.A.
  
  Lemma Q_count (X: cs): (queries X) \is_countable.
  Proof. by case: X => X Q A [I D []]. Qed.

  Lemma Q_inh (X: cs): inhabited (queries X).
  Proof. by case: X => X Q A [I D []]. Qed.

  Lemma A_count (X: cs): (answers X) \is_countable.
  Proof. by case: X => X Q A [I D []]. Qed.

  Lemma A_inh (X: cs): inhabited (answers X).
  Proof. by case: X => X Q A [I D []]. Qed.
  
  Local Notation representation X:= (conversation X).

  Lemma rep_sur (X: cs): (representation X) \is_cototal.
  Proof. by case: X => X Q A [[]]. Qed.

  Lemma rep_sing (X: cs): (representation X) \is_singlevalued.
  Proof. by case : X => X Q A [I []]. Qed.

  Definition make_cs X
             Q A (q: Q) (a: A) (Qcnt: Q \is_countable) (Acnt: A \is_countable)
             (rep: (Q -> A) ->> X) (sur: rep \is_cototal) (sing: rep \is_singlevalued):=
    continuity_space.Pack (@continuity_space.Class _ _ _
                             (interview.Mixin sur) (dictionary.Mixin sing)
                             (continuity_space.Mixin q a Qcnt Acnt)).                      
End continuity_spaces.

Notation cs:= continuity_space.type.
Coercion space: cs >-> dictionary.
Coercion continuity_space.mixin: cs >-> continuity_space.class_of.
Coercion continuity_space.M: continuity_space.class_of >-> continuity_space.mixin_of.
Notation queries:= continuity_space.Q.
Notation answers := continuity_space.A.
Notation representation X:= (description X).
Notation rep X := (representation X).
Notation queries_countable := Q_count.
Notation answers_countable := A_count.
Notation name_functions X := (queries X -> answers X).
Notation names X := (questions X).
Notation delta phi x := (representation _ phi x).
Notation "phi '\describes' x '\wrt' X" := (representation (X: cs) phi x) (at level 2): cs_scope.
Notation "phi '\is_description_of' x" := (phi \describes x \wrt _) (at level 2): cs_scope.
Notation get_description:= rep_sur.
Notation someq:= continuity_space.someq.
Notation somea:= continuity_space.somea.
Notation "F \is_continuous_operator" := (continuous F) (at level 30): cs_scope.

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
    exists (G \o F); split; first by apply rlzr_comp.
    exact/cont_comp.
  Qed.

  Definition continuous (X Y: cs) (f: X -> Y):= (F2MF f) \has_continuous_realizer.
  Local Notation "f \is_continuous" := (continuous f) (at level 2).

  Global Instance cont_prpr (X Y: cs):
    Proper (@eqfun Y X ==> iff) (@continuous X Y).
  Proof.
      by move => f g /F2MF_eq eq; rewrite /continuous eq.
  Qed.

  Lemma cont_comp (X Y Z: cs) (f: Y -> Z) (g: X -> Y):
    f \is_continuous -> g \is_continuous -> (f \o_f g) \is_continuous.
  Proof.
    rewrite /funcomp /continuous => cont cont'.
    have ->: (F2MF (fun x => f (g x))) =~= (F2MF f) \o (F2MF g) by rewrite comp_F2MF.
    exact: comp_hcr.
  Qed.
End continuity.
Notation hcr:= has_continuous_realizer.
Notation "f '\has_continuous_realizer'":= (hcr f) (at level 2): cs_scope.
Notation "f \is_continuous" := (continuous f) (at level 2): cs_scope.