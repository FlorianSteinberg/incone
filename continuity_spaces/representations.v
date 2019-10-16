From mathcomp Require Import ssreflect ssrfun.
From rlzrs Require Import all_rlzrs dict.
Require Import all_cont naming_spaces.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope cs_scope with cs.
Local Open Scope cs_scope.

Notation "F \is_continuous_operator" := (continuous F) (at level 30): cs_scope.
Notation "f \is_continuous_functional" := (continuous_function f) (at level 30): cs_scope.
Section representations.
  Class is_representation (B: naming_space) X (delta: B ->> X) := dict:> Dictionary delta.

  Definition solution_wrt
             (B B': naming_space) X X' (delta: B ->> X) (delta': B' ->> X') (f: X ->> X') F:=
  realizer delta delta' F f.

  Definition has_continuous_solution_wrt
      (B B': naming_space) X X' (delta: B ->> X) (delta': B' ->> X') (f: X ->> X') :=
    exists F, F \is_continuous_operator /\ solution_wrt delta delta' f F. 

  Definition continuous_wrt (B B': naming_space) X X' (delta: B ->> X) (delta': B' ->> X') f :=
    has_continuous_solution_wrt delta delta' (F2MF f).
  
  Global Instance unpair_is_rep (B B': naming_space):
    is_representation (F2MF (@unpair B B')).
    split; [apply/unpair_sur | apply/F2MF_sing].
  Defined.

  Global Instance product_is_representation `{rep:is_representation} `{rep0:is_representation}:
    is_representation ((delta ** delta0) \o_R (F2MF (@unpair B B0))).
  exact combine_dictionaries.
  Defined.

  Global Instance slct_is_rep (B B': naming_space):
    is_representation (F2MF (@slct B B')).
  split; [apply/slct_sur | apply/F2MF_sing].
  Defined.
  
  Global Instance sum_is_representation `{is_representation} `{is_representation}:
    is_representation ((delta +s+ delta0) \o_R (F2MF (@slct B B0))).
  exact combine_dictionaries.
  Defined.
End representations.  
Notation "delta \is_representation" := (is_representation delta) (at level 30).

Section representations_of.
  Structure representation_of (X: Type) :=
    {
      name_space: naming_space;
      delta:> name_space ->> X;
      represented:> delta \is_representation;
    }.

  Canonical rep2repf (B: naming_space) X (delta: B ->> X)
            (representation: delta \is_representation):
    representation_of X.
  - exact/Build_representation_of.
  Defined.

  Local Notation "delta '\translatable_to' delta'" :=
    (continuous_wrt delta delta' id) (at level 35).

  Definition equivalent X (delta delta': representation_of X):=
    delta \translatable_to delta' /\  delta' \translatable_to delta.

  Canonical product_representation X Y (delta: representation_of X) (delta': representation_of Y):
    representation_of (X * Y).
  exists (product_names (name_space delta) (name_space delta'))
    ((delta ** delta') \o_R (F2MF (@unpair _ _))).
    by have := @product_is_representation _ _ _ (represented delta) _ _ _ (represented delta').
  Defined.

  Canonical sum_representation X Y (delta: representation_of X) (delta': representation_of Y):
    representation_of (X + Y).
  exists (sum_names (name_space delta) (name_space delta'))
  ((delta +s+ delta') \o_R (F2MF (@slct _ _))).
    by have := @sum_is_representation _ _ _ (represented delta) _ _ _ (represented delta').
  Defined.
End representations_of.
Notation "delta '\translatable_to' delta'" := (continuous_wrt delta delta' id) (at level 35).
Notation "delta '\equivalent_to' delta'" := (equivalent delta delta') (at level 30): cs_scope.
Notation "phi '\names' x '\wrt' delta" :=
  (delta (phi: name_space delta) x) (at level 30): cs_scope.
Notation "phi '\describes' x '\wrt' delta" :=
  (delta (phi: name_space delta) x) (at level 30): cs_scope.
