From mathcomp Require Import ssreflect ssrfun.
From rlzrs Require Import all_rlzrs.
From metric Require Import all_metric.
Require Import axioms all_names representations cs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope cs_scope.
Section subspace.
  Context (X: cs) (A: subset X).

  Local Notation rep_sub:= (make_mf (fun phi (t: A) => phi \describes (sval t) \wrt X)).

  Lemma rep_sub_rep: rep_sub \is_representation.
  Proof.
    split; first by move => [s Ps]; have [phi phins]:= get_description s; exists phi.
    by move => phi [x Px] [y Py] rrdphix rrdphiy; apply eq_sub; apply (@rep_sing X phi x y).
  Qed.

  Canonical sub_representation := Build_representation_of rep_sub_rep. 

  Canonical sub_space := repf2cs sub_representation.
End subspace.

Section subspaces.
  Local Open Scope cs_scope.  
  Lemma sub_hcs (X Y: cs) (A: subset X) (f: X ->> Y):
    f \has_continuous_solution -> (@sub_mf X Y A f) \has_continuous_solution.
  Proof. by move => [F [cont slvs]]; exists F; split => // phi x; apply/slvs. Qed.
  
  Lemma sub_cont (X Y: cs) (A: subset X) (f: X -> Y):
    f \is_continuous -> (@sub_fun X Y A f) \is_continuous.
  Proof. exact/sub_hcs. Qed.
End subspaces.
