From mathcomp Require Import ssreflect ssrfun.
From rlzrs Require Import all_rlzrs.
From metric Require Import all_metric.
Require Import axioms all_names representations cs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope cs_scope.
Section subspace.
  Context X (delta: representation_of X) (A: subset X).

  Local Notation rep_sub:= (make_mf (fun phi (t: A) =>
                                       phi \describes (sval t) \wrt delta)).

  Lemma rep_sub_rep: rep_sub \is_representation.
  Proof.
    have [sur sing]:= (represented delta).
    split => [[s Ps] | phi [x Px] [y Py]/= phinx phiny]; first by have [phi]:= sur s; exists phi.
    exact/eq_sub/sing/phiny/phinx.
  Qed.

  Canonical sub_representation := Build_representation_of rep_sub_rep. 
End subspace.

Canonical sub_space (X: cs) (A: subset X) := repf2cs (sub_representation (delta_ X) A).

Section subspaces.
  Local Open Scope cs_scope.  
  Lemma sub_hcs (X Y: cs) (A: subset X) (f: X ->> Y):
    f \has_continuous_solution -> (@sub_mf X Y A f) \has_continuous_solution.
  Proof. by move => [F [conjt slvs]]; exists F; split => // phi x; apply/slvs. Qed.
  
  Lemma sub_cont (X Y: cs) (A: subset X) (f: X -> Y):
    f \is_continuous -> (@sub_fun X Y A f) \is_continuous.
  Proof. exact/sub_hcs. Qed.
End subspaces.
