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
  Class is_representation (B: naming_space) X (delta: B ->> X) :=
    {
      surjective: delta \is_cototal;
      deterministic: delta \is_singlevalued;
    }.
  
  Global Instance R2D `{R: is_representation}: Dictionary delta.
    by split; first exact/surjective; exact/deterministic.
  Defined.

  Definition has_continuous_solution_wrt
      (B B': naming_space) (X X': Type) (delta: B ->> X) (delta': B' ->> X') (f: X ->> X') :=
    exists F, F \is_continuous_operator /\ realizer delta delta' F f. 
End representations.  
Notation "delta \is_representation" := (is_representation delta) (at level 30).

Section representations_of.
  Class representation_of (X: Type) :=
    {
      name_space: naming_space;
      delta: name_space ->> X;
      representation: delta \is_representation;
    }.

  Coercion delta: representation_of >-> multifunction.
  Notation hcr_wrt delta delta' f:= (has_continuous_solution_wrt delta delta' (F2MF f)).

  Definition equivalent X (delta delta': representation_of X):=
    hcr_wrt delta delta' id /\ hcr_wrt delta' delta id.
End representations_of.
Notation "delta '\equivalent_to' delta'" := (equivalent delta delta') (at level 30).
