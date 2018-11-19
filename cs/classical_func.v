From mathcomp Require Import ssreflect ssrfun seq.
From rlzrs Require Import all_rlzrs choice_dict.
Require Import all_core cs prod sub func classical_cont classical_mach.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma ass_cont (X Y: cs) (f: X -> Y): f \from (codom (@associate X Y)) <-> f \is_continuous.
Proof.
split => [[psi /=rlzr] | [F [rlzr cont]]].
- exists \F_(M psi); split => //.
  admit.
have [psi val]:= (M_universal (someq X) (somea X) (fun _ => somea Y) (questions_countable X) cont).
by exists psi; exact/ntrvw.tight_rlzr/val.
Admitted.


Definition exist_c (X Y: cs) (f: X -> Y) (cont: f \is_continuous): (X c-> Y).
Proof. by exists f; apply/ass_cont. Defined.