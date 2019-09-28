From mathcomp Require Import ssreflect ssrfun.
From rlzrs Require Import all_rlzrs.
Require Import all_names cs prod sum func classical_func.
Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope cs_scope.
Section isomorphisms.
Definition isomorphism (X Y: cs) (f: X c-> Y) :=
	exists (g: Y c-> X), cancel (projT1 f) (projT1 g) /\ cancel (projT1 g) (projT1 f).

Definition isomorphic (X Y: cs):= exists f, @isomorphism X Y f.
Arguments isomorphic {X Y}.

Notation "X ~=~ Y" := (@isomorphic X Y) (at level 2).

Lemma iso_ref: Reflexive (@isomorphic).
Proof. by move => X; exists (exist_c (id_cont X)); exists (exist_c (id_cont X)). Qed.

Lemma iso_sym: Symmetric (@isomorphic).
Proof. by move => X Y [f [g [cncl cncl']]]; exists g; exists f. Qed.

Lemma iso_trans: Transitive (@isomorphic).
Proof.
move => X Y Z [f [g [cncl1 cncl2]]] [f' [g' [cncl1' cncl2']]].  
exists (f' \o_cs f); exists (g \o_cs g').
by rewrite /=; split; apply can_comp.
Qed.

Global Instance iso_equiv: Equivalence (@isomorphic).
Proof. split; [exact/iso_ref | exact/iso_sym | exact/iso_trans]. Qed.
End isomorphisms.
Notation "X ~=~ Y" := (@isomorphic X Y) (at level 2).

Lemma iso_spec X Y: X ~=~ Y <->
  exists (f: X -> Y), f \is_continuous /\ exists g, g \is_continuous /\ cancel f g /\ cancel g f.
Proof.
  split => [[[f ?] [[g ? /=] [? ?]]] | [f [cont [g [cont' [? ?]]]]]].
  - by exists f; split; first exact/ass_cont; exists g; split; first exact/ass_cont.
  by exists (exist_c cont); exists (exist_c cont').
Qed.

Global Instance slvbl_prpr (X X' Y Y':cs):
  Proper ((@equiv B_(X) B_(Y)) ==> (@equiv X Y) ==> iff) (@realizer _ _ (rep X) _ _ (rep Y)).
Proof. by move => F G eq f g eq'; rewrite eq' eq. Qed.

Global Instance prod_prpr:
  Proper (isomorphic ==> isomorphic ==> isomorphic) cs_prod.
Proof.
  move => X X' [f [f' [cnclf cnclf']]] Y Y' [g [g' [cnclg cnclg']]].
  have fcont: (projT1 f) \is_continuous by apply/cfun_spec/(projT2 f).
  have gcont: (projT1 g) \is_continuous by apply/cfun_spec/(projT2 g).
  have f'cont: (projT1 f') \is_continuous by apply/cfun_spec/(projT2 f').
  have g'cont: (projT1 g') \is_continuous by apply/cfun_spec/(projT2 g').
  exists (exist_c (fprd_cont fcont gcont)).
  exists (exist_c (fprd_cont f'cont g'cont)).
  split; case => [x y /=]; rewrite /fprd /=.
  - by have /= ->:= cnclf x; have /= ->:= cnclg y.
  by have /= ->:= cnclf' x; have /= ->:= cnclg' y.
Qed.  

(*
Global Instance sum_prpr:
  Proper (isomorphic ==> isomorphic ==> isomorphic) cs_sum.
Proof.
  move => X X' [f [f' [cnclf cnclf']]] Y Y' [g [g' [cnclg cnclg']]].
  have fcont: (projT1 f) \is_continuous by apply/cfun_spec/(projT2 f).
  have gcont: (projT1 g) \is_continuous by apply/cfun_spec/(projT2 g).
  have f'cont: (projT1 f') \is_continuous by apply/cfun_spec/(projT2 f').
  have g'cont: (projT1 g') \is_continuous by apply/cfun_spec/(projT2 g').
  exists (exist_c (fsum_cont fcont gcont)).
  exists (exist_c (fsum_cont f'cont g'cont)).
  split; case => [x | y]; rewrite /fsum /=.
  - + * by have /= ->:= cnclf x.
  - + by have /= ->:= cnclg y.
  - by have /= ->:= cnclf' x.
  by have /= ->:= cnclg' y.
Qed.
*)