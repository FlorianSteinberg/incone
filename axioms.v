From mathcomp Require Import ssrfun.
Require Import Classical ChoiceFacts count.

Axiom functional_extensionality: forall Q A (f g: Q -> A), f =1 g -> f = g.
Notation fun_ext:= functional_extensionality.
Axiom full_choice: FunctionalChoice.
Arguments full_choice {A} {B}.
Axiom nat_choice: FunctionalCountableChoice.
Axiom countable_choice: forall T, T \is_countable -> forall T', FunctionalChoice_on T T'.
