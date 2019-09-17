From mathcomp Require Import ssreflect seq ssrnat ssrbool eqtype ssrfun.
From mf Require Import all_mf.
Require Import all_cont PhiN FMop Umach naming_spaces.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
  
Section CM2A.
  Context (Q: eqType) (someq: Q) ( Q' A A': Type).
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Local Open Scope name_scope.
  Context (M: B -> nat * Q' -> option A').
  Context (nu: B -> nat * Q' -> seq Q).
  Hypothesis mod: nu \modulus_function_for M.
  Hypothesis modmod: nu \modulus_function_for nu.

  Fixpoint count_someq (K: seq Q) :=
    match K with
    | nil => 0
    | q :: K' => if q == someq then (count_someq K').+1 else count_someq K'
    end.
End CM2A.

