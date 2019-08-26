From mathcomp Require Import ssreflect ssrfun seq ssrbool eqtype ssrnat.
From mf Require Import all_mf.
Require Import all_cont.
Require Import Morphisms.

Axiom functional_extensionality: forall Q A (f g: Q -> A), f =1 g -> f = g.
Local Notation funext:= functional_extensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section naming_spaces.
  Structure naming_space :=
    {
      Q: Type;
      A: Type;
      someq: Q;
      somea: A;
      Q_count: Q \is_countable;
      A_count: A \is_countable;
    }.
 End naming_spaces.