From mathcomp Require Import ssreflect ssrfun.
Require Import Classical ChoiceFacts count ProofIrrelevance.

Fact eq_sub T P (a b : {x : T | P x}) : a = b <-> projT1 a = projT1 b.
Proof.
  split=> [->//|]; move: a b => [a Pa] [b Pb] /= eqab.
  case: _ / eqab in Pb *; congr (exist _ _ _).
  exact/proof_irrelevance.
Qed.

Axiom functional_extensionality: forall Q A (f g: Q -> A), f =1 g -> f = g.
Notation fun_ext:= functional_extensionality.
Axiom full_choice: FunctionalChoice.
Arguments full_choice {A} {B}.
Axiom nat_choice: FunctionalCountableChoice.
Axiom countable_choice: forall T, T \is_countable -> forall T', FunctionalChoice_on T T'.
