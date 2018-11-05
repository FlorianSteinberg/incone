From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mpf choice_mf.
Require Import all_cont choice_cont exec Mmach.
Require Import ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section choice_machines.
Context (Q Q' A A': Type).
Notation B := (Q -> A).
Notation B' := (Q' -> A').

End choice_machines.