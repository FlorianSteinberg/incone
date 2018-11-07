From mathcomp Require Import ssreflect ssrfun.
From rlzrs Require Export all_mf all_rlzrs.
Require Import all_core.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module continuity_space.
Structure type := Pack {
  Q: Type;
  A: Type;
  someq: Q;
	somea: A;
  Qcount: Q \is_countable;
  Acount: A \is_countable;
	X:> dictionary.type (Q -> A)
}.
End continuity_space.
Notation somea := continuity_space.somea.
Notation someq := continuity_space.someq.
Notation questions X:= (continuity_space.Q X).
Notation questions_countable X := (continuity_space.Qcount X).
Notation answers X:= (continuity_space.A X).
Notation answers_countable X := (continuity_space.Acount X).
Notation names X := ((questions X) -> (answers X)).
Notation rep X := (conversation (continuity_space.X X)).
Notation delta := (rep _).
Notation rep_sing := answer_unique.
Notation rep_sur := only_respond.
Notation get_description x:= (get_question x).
Notation "phi '\is_description_of' x" := (x \is_response_to phi) (at level 2).
Notation cs:= continuity_space.type.
Coercion continuity_space.X: continuity_space.type >-> dictionary.type.

Section continuity.
Definition hcr (X Y : cs) (f : X ->> Y) :=
	exists F, F \realizes f /\ F \is_continuous_operator.
Notation "f '\has_continuous_realizer'":= (hcr f) (at level 2).

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
exact/cntop_comp.
Qed.

Definition continuous (X Y: cs) (f: X -> Y):= (F2MF f) \has_continuous_realizer.
Notation "f \is_continuous" := (continuous f) (at level 30).

Lemma cont_comp (X Y Z: cs) (f: Y -> Z) (g: X -> Y):
	f \is_continuous -> g \is_continuous -> (f \o_f g) \is_continuous.
Proof.
rewrite /funcomp /continuous => cont cont'.
have ->: (F2MF (fun x => f (g x))) =~= (F2MF f) \o (F2MF g) by rewrite comp_F2MF.
exact: comp_hcr.
Qed.
End continuity.
Notation "f '\has_continuous_realizer'":= (hcr f) (at level 2).
Notation "f \is_continuous" := (continuous f) (at level 30).