From mathcomp Require Import all_ssreflect.
Require Import all_core cs.
Require Import ProofIrrelevance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section cs_subspace.
Fact eq_sub T P (a b : {x : T | P x}) : a = b <-> projT1 a = projT1 b.
Proof.
split=> [->//|]; move: a b => [a Pa] [b Pb] /= eqab.
case: _ / eqab in Pb *; congr (exist _ _ _).
exact: Classical_Prop.proof_irrelevance.
Qed.

Definition rep_sub (X: cs) (P: mf_subset.type X):= 
	make_mf (fun phi (t: {x | P x}) => delta phi (sval t)).

Lemma rep_sub_sur (X: cs) P: (@rep_sub X P) \is_cototal.
Proof.
rewrite cotot_spec => [[s Ps]].
have [phi phins]:= get_name s.
by exists phi.
Qed.

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

Canonical cs_sub (X: cs) (P: mf_subset.type X) := @cs.Pack
	(cs.Q X)
	(cs.A X)
	(cs.someq X)
	(cs.somea X)
  (cs.Qcount X)
  (cs.Acount X)
  (dictionary.Pack (@cs_sub_modest_set_mixin X P)).

(*
Lemma sub_space_rec_fun (X Y: cs) (P: X -> Prop) (f: X -> Y):
	f \is_recursive_function -> (fun x: {x' | P x'} => f (projT1 x)) \is_recursive_function.
Proof. by move => [M Mprop]; exists M => phi x; apply Mprop. Qed.

Lemma sub_space_prec (X Y: rep_space) (P: X -> Prop) (f: X ->> Y):
	f \is_recursive -> (fun x: {x' | P x'} => f (projT1 x)) \is_recursive.
Proof.
move => [M Mprop'].
exists M.
move => phi x phinx [y /=fxy].
have xfd': (projT1 x) \from_dom f by exists y.
have phinx': (phi: names X) \is_name_of (projT1 x) by trivial.
by apply: Mprop' phi (projT1 x) phinx' xfd'.
Qed.
*)
End cs_subspace.