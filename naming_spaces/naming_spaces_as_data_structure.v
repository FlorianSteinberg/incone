From mathcomp Require Import ssreflect ssrfun seq .
From mf Require Import all_mf.
From rlzrs Require Import all_rlzrs.
Require Import all_cont naming_spaces.
Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope name_scope.

Definition name_pairs: pairs_data descriptions.
  exists (product_names) (unpair).
  apply unpair_sur.
Defined.

