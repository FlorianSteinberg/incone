From mathcomp Require Import all_ssreflect.
Require Import all_core cs func facts.
Require Import FunctionalExtensionality ClassicalFacts ClassicalChoice Psatz ProofIrrelevance.
Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ISOMORPHISMS.
Definition isomorphism (X Y: cs) (f: X c-> Y) :=
	exists (g: Y c-> X), cancel (projT1 f) (projT1 g) /\ cancel (projT1 g) (projT1 f).

Definition isomorphic (X Y: cs):= exists f, @isomorphism X Y f.
Arguments isomorphic {X Y}.

Notation "X ~=~ Y" := (@isomorphic X Y) (at level 2).

Lemma iso_ref X: X ~=~ X.
Proof. by exists (exist_c (id_cont X)); exists (exist_c (id_cont X)). Qed.

Lemma iso_sym X Y: X ~=~ Y -> Y ~=~ X.
Proof. by move => [f [g [cncl cncl']]]; exists g; exists f. Qed.

Lemma iso_trans X Y Z (someqx: questions X) (someqz: questions Z):
	X ~=~ Y -> Y ~=~ Z -> X ~=~ Z.
Proof.
move => [f [g [cncl1 cncl2]]] [f' [g' [cncl1' cncl2']]].
exists (exist_c (cont_comp (projT2 f') (projT2 f))).
exists (exist_c (cont_comp (projT2 g) (projT2 g'))).
by rewrite /=; split; apply can_comp.
Qed.
End ISOMORPHISMS.
Notation "X ~=~ Y" := (@isomorphic X Y) (at level 2).
