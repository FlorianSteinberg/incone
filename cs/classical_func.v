From mathcomp Require Import ssreflect ssrfun seq.
From rlzrs Require Import all_rlzrs choice_dict.
Require Import all_core cs prod sub func classical_cont classical_mach.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma ass_cont (X Y: cs) (f: X -> Y): f \from (codom (@associate X Y)) <-> f \is_continuous.
Proof.
split => [[psi /=rlzr] | [F [rlzr cont]]]; first by exists \F_(M psi); split; last exact/FM_cont.
have [psi val]:= (M_universal (someq X) (somea X) (fun _ => somea Y) (questions_countable X) cont).
by exists psi; exact/ntrvw.tight_rlzr/val.
Qed.

Definition exist_c (X Y: cs) (f: X -> Y) (cont: f \is_continuous): (X c-> Y).
Proof. by exists f; apply/ass_cont. Defined.

Definition cs_comp (X Y Z: cs) (f: X c-> Y) (g: Y c-> Z): (X c-> Z).
Proof.
exists ((projT1 g) \o_f projT1 f); apply/ass_cont/cont_comp.
- exact/ass_cont/(projT2 g).
exact/ass_cont/(projT2 f).
Defined.

Notation "g \o_cs f" := (cs_comp f g) (at level 29).

Lemma cs_comp_spec (X Y Z: cs)(f: X c-> Y) (g: Y c-> Z): projT1 (g \o_cs f) =1 (projT1 g \o_f projT1 f).
Proof. done. Qed.