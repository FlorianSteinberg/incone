From mathcomp Require Import ssreflect ssrfun.
From rlzrs Require Import all_rlzrs.
From metric Require Import all_metric.
Require Import axioms all_names representations cs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope cs_scope.
Section subspace.
  Context (X: cs) (P: subset X).

  Local Notation rep_sub:= (make_mf (fun phi (t: {x | P x}) => phi \describes (sval t) \wrt X)).

  Lemma rep_sub_sur: rep_sub \is_cototal.
  Proof. by move => [s Ps]; have [phi phins]:= get_description s; exists phi. Qed.

  Lemma rep_sub_sing: rep_sub \is_singlevalued.
  Proof.
    move => phi [x Px] [y Py] rrdphix rrdphiy.
    by apply eq_sub; apply (@rep_sing X phi x y).
  Qed.

  Lemma rep_sub_rep: rep_sub \is_representation.
  Proof. by split; try apply/rep_sub_sing; try apply/rep_sub_sur. Qed.

  Definition sub_representation := Build_representation_of rep_sub_rep. 

  Canonical sub_space := rep2cs sub_representation.
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
