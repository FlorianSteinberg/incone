From mathcomp Require Import ssreflect ssrfun.
Require Import all_core cs.
Require Import ProofIrrelevance ProofIrrelevanceFacts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section cs_subspace.
Fact eq_sub T P (a b : {x : T | P x}) : a = b <-> projT1 a = projT1 b.
Proof.
split=> [->//|]; move: a b => [a Pa] [b Pb] /= eqab.
case: _ / eqab in Pb *; congr (exist _ _ _).
apply/proof_irrelevance.
Qed.

Definition rep_sub (X: cs) (P: mf_subset.type X):= 
	make_mf (fun phi (t: {x | P x}) => delta phi (sval t)).

Lemma rep_sub_sur (X: cs) P: (@rep_sub X P) \is_cototal.
Proof. by move => [s Ps]; have [phi phins]:= get_description s; exists phi. Qed.

Definition cs_sub_assembly_mixin (X: cs) (P: mf_subset.type X):
	interview_mixin.type (questions X -> answers X) {x | P x}.
Proof. exists (@rep_sub X P); exact/rep_sub_sur. Defined.

Lemma rep_sub_sing (X: cs) P: (@rep_sub X P) \is_singlevalued.
Proof.
move => phi [x Px] [y Py] rrdphix rrdphiy.
by apply eq_sub; apply (rep_sing phi x y).
Qed.

Definition cs_sub_modest_set_mixin X P:
	dictionary_mixin.type (interview.Pack (@cs_sub_assembly_mixin X P)).
Proof. split; exact/rep_sub_sing. Qed.

Definition cs_sub (X: cs) (P: mf_subset.type X) :=
  continuity_space.Pack
    (someq X)
    (somea X)
    (questions_countable X)
    (answers_countable X)
    (dictionary.Pack (@cs_sub_modest_set_mixin X P)).
End cs_subspace.