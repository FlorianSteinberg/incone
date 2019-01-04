From mathcomp Require Import ssreflect ssrfun.
From rlzrs Require Import all_rlzrs.
Require Import all_core cs.
Require Import ProofIrrelevance ProofIrrelevanceFacts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fact eq_sub T P (a b : {x : T | P x}) : a = b <-> projT1 a = projT1 b.
Proof.
  split=> [->//|]; move: a b => [a Pa] [b Pb] /= eqab.
  case: _ / eqab in Pb *; congr (exist _ _ _).
  exact/proof_irrelevance.
Qed.

Section subspace.

  Context (X: cs) (P: subset X).
  Definition rep_sub:=  make_mf (fun phi (t: {x | P x}) => rep X phi (sval t)).

  Lemma rep_sub_sur: rep_sub \is_cototal.
  Proof. by move => [s Ps]; have [phi phins]:= get_description s; exists phi. Qed.

  Lemma rep_sub_sing: rep_sub \is_singlevalued.
  Proof.
    move => phi [x Px] [y Py] rrdphix rrdphiy.
    by apply eq_sub; apply (@rep_sing X phi x y).
  Qed.

  Definition cs_sub_class:= @continuity_space.Class _ _ _
    (interview.Mixin rep_sub_sur) (dictionary.Mixin rep_sub_sing)
    (continuity_space.Mixin (someq X) (somea X) (Q_count X) (A_count X)).

  Canonical cs_sub := continuity_space.Pack cs_sub_class.
End subspace.

Section subspaces.
  Definition sub_fun S T (A: subset S) (f: S -> T) (a: A) := f (sval a).
  Arguments sub_fun {S} {T} (A).
  
  Definition sub_mf S T (A: subset S) (f: S ->> T) :=
    make_mf (fun (a: A) y => f (sval a) y).

  Lemma sub_F2MF S T (A: subset S) (f: S -> T):
    F2MF (sub_fun A f) =~= sub_mf A (F2MF f).
  Proof. done. Qed.
  
  Lemma sub_hcr (X Y: cs) (A: subset X) (f: X ->> Y):
    f \has_continuous_realizer -> (@sub_mf X Y A f) \has_continuous_realizer.
  Proof.
    move => [F [rlzr cont]].
    exists F; split => // phi x.
    exact/rlzr.
  Qed.
  
  Lemma sub_cont (X Y: cs) (A: subset X) (f: X -> Y):
    f \is_continuous -> (@sub_fun X Y A f) \is_continuous.
  Proof. exact/sub_hcr. Qed.
End subspaces.   