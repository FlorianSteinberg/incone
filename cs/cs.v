From mathcomp Require Import all_ssreflect.
Require Import all_core.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module cs.
Local Open Scope type_scope.
Structure type := Pack {
  Q: Type;
  A: Type;
  someq: Q;
	somea: A;
  Qcount: Q \is_countable;
  Acount: A \is_countable;
	X: dictionary.type (Q -> A)
}.
End cs.
Notation somea := cs.somea.
Notation someq := cs.someq.
Notation questions X:= (cs.Q X).
Notation answers X:= (cs.A X).
Notation names X := ((questions X) -> (answers X)).
Notation rep X := (conversation (cs.X X)).
Notation delta := (rep _).
Notation rep_sing := answer_unique.
Notation rep_sur := only_respond.
Notation get_name x:= (get_question x).
Notation "phi '\is_name_of' x" := (delta phi x) (at level 2).
Notation cs:= cs.type.
Coercion cs.X: cs.type >-> dictionary.type.

Section continuity.
Definition hcr (X Y : cs) (f : X ->> Y) :=
	exists F, F \realizes f /\ F \is_continuous.
Notation "f '\has_continuous_realizer'":= (hcr f) (at level 2).

Global Instance hcr_prpr (X Y: cs):
	Proper (@equiv X Y ==> iff) (@hcr X Y).
Proof.
by move => f g feg; split; move => [F [Frf Fcont]]; exists F; [rewrite -feg | rewrite feg].
Qed.

Lemma comp_hcr (X Y Z: cs) (f: X ->> Y) (g: Y ->> Z):
	f \has_continuous_realizer -> g \has_continuous_realizer -> (g o f) \has_continuous_realizer.
Proof.
move => [F [Frf Fcont]] [G [Grg Gcont]].
exists (G o F); split; first by apply rlzr_comp.
by apply/ cont_comp.
Qed.

Lemma comp_hcr_fun (X Y Z: cs) (f: X -> Y) (g: Y -> Z):
	(F2MF f) \has_continuous_realizer -> (F2MF g) \has_continuous_realizer -> (F2MF (fun x => g (f x))) \has_continuous_realizer.
Proof.
have ->: (F2MF (fun x => g (f x))) =~= (F2MF g) o (F2MF f) by rewrite comp_F2MF.
exact: comp_hcr.
Qed.
End continuity.
Notation "f '\has_continuous_realizer'":= (hcr f) (at level 2).