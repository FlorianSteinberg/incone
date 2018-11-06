From mathcomp Require Import all_ssreflect.
Require Import all_core cs func facts.
Require Import FunctionalExtensionality ClassicalFacts ClassicalChoice Psatz ProofIrrelevance.
Require Import RelationClasses.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section isomorphisms.
Definition isomorphism (X Y: cs) (f: X c-> Y) :=
	exists (g: Y c-> X), cancel (projT1 f) (projT1 g) /\ cancel (projT1 g) (projT1 f).

Definition isomorphic (X Y: cs):= exists f, @isomorphism X Y f.
Arguments isomorphic {X Y}.

Notation "X ~=~ Y" := (@isomorphic X Y) (at level 2).

Lemma iso_ref: Reflexive (@isomorphic).
Proof. by move => X; exists (exist_c (id_cont X)); exists (exist_c (id_cont X)). Qed.

Lemma iso_sym: Symmetric (@isomorphic).
Proof. by move => X Y [f [g [cncl cncl']]]; exists g; exists f. Qed.

Lemma iso_trans: Transitive (@isomorphic).
Proof.
move => X Y Z [f [g [cncl1 cncl2]]] [f' [g' [cncl1' cncl2']]].
exists (exist_c (cont_comp (projT2 f') (projT2 f))).
exists (exist_c (cont_comp (projT2 g) (projT2 g'))).
by rewrite /=; split; apply can_comp.
Qed.

Global Instance iso_equiv: Equivalence (@isomorphic).
Proof. split; [exact/iso_ref | exact/iso_sym | exact/iso_trans]. Qed.
End isomorphisms.
Notation "X ~=~ Y" := (@isomorphic X Y) (at level 2).
