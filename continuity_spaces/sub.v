From mathcomp Require Import ssreflect ssrfun.
From rlzrs Require Import all_rlzrs.
From metric Require Import all_metric.
Require Import axioms all_names cs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

  Canonical cs_sub: cs.
    exists {x | x \from P} (name_space _) rep_sub.
    by split; [apply/rep_sub_sur | apply/rep_sub_sing].
  Defined.
End subspace.

Section subspaces.
  Local Open Scope cs_scope.  
  Lemma sub_hcr (X Y: cs) (A: subset X) (f: X ->> Y):
    f \has_continuous_realizer -> (@sub_mf X Y A f) \has_continuous_realizer.
  Proof. by move => [F [cont slvs]]; exists F; split => // phi x; apply/slvs. Qed.
  
  Lemma sub_cont (X Y: cs) (A: subset X) (f: X -> Y):
    f \is_continuous -> (@sub_fun X Y A f) \is_continuous.
  Proof. exact/sub_hcr. Qed.
End subspaces.