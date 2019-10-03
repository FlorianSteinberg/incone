From mathcomp Require Import ssreflect ssrfun.
From rlzrs Require Import all_rlzrs.
Require Import axioms all_names representations cs prod sum func classical_func.
Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope cs_scope.
Section equivalence.
  Context (T: Type).
  Lemma equiv_ref: Reflexive (@equivalent T).
  Proof. by move => delta; split; apply/(id_cont (rep2cs delta)). Qed.

  Lemma equiv_sym: Symmetric (@equivalent T).
  Proof. by move => ? ?; case. Qed.

  Lemma equiv_trans: Transitive (@equivalent T).
  Proof.
    move => delta delta' delta'' [hcr rch] [hcr' rch'].
    split.
    - have := (@comp_hcr (rep2cs delta) (rep2cs delta') (rep2cs delta'') mf_id mf_id hcr hcr').
      by rewrite comp_id_r.
    have := (@comp_hcr (rep2cs delta'') (rep2cs delta') (rep2cs delta) mf_id mf_id rch' rch).
    by rewrite comp_id_r.
  Qed.

  Global Instance equiv_equiv: Equivalence (@equivalent T).
  Proof. by split; try apply/equiv_ref; try apply/equiv_sym; try apply/equiv_trans. Qed.

  Global Instance hcr_prpr T' (f: T ->> T'):
    Proper ((@equivalent T) ==> (@equivalent T') ==> iff)
           (fun delta delta' => hcr (f: rep2cs delta ->> rep2cs delta')).
  Proof.
    move => deltaT delta'T [hcr rch] deltaT' delta'T' [hcr' rch'].
    split => cont.
    - rewrite -(comp_id_l f) -(comp_id_r f).
      exact/(comp_hcr (Y:= rep2cs deltaT'))/hcr'/(comp_hcr (Y := rep2cs deltaT))/cont/rch.
    rewrite -(comp_id_l f) -(comp_id_r f).
    exact/(comp_hcr (Y:= rep2cs delta'T'))/rch'/(comp_hcr (Y:= rep2cs delta'T))/cont/hcr.
  Qed.
End equivalence.

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
                      exists (f: X -> Y), f \is_continuous
                                          /\
                                          exists g, g \is_continuous
                                                    /\
                                                    cancel f g /\ cancel g f.
  Proof.
    split => [[[f ?] [[g ? /=] [? ?]]] | [f [cont [g [cont' [? ?]]]]]].
    - by exists f; split; first exact/ass_cont; exists g; split; first exact/ass_cont.
    by exists (exist_c cont); exists (exist_c cont').
  Qed.
  
  Definition rep2cs X (delta: representation_of X): cs.
    exists X (representations.name_space) delta.
    apply representations.representation.
  Defined.

  Global Instance rep2cs_prpr X:
    Proper (@equivalent X ==> isomorphic) (@rep2cs X).
  Proof.
    move => delta delta'; case; case => F [cont rlzr] [F' [cont' rlzr']].
    apply/iso_spec; exists id; split; first by exists F.
    by exists id; split; first by exists F'.
  Qed.

  Lemma equiv_iso X (delta delta': representation_of X):
    delta \equivalent_to delta' -> (rep2cs delta) ~=~ (rep2cs delta').
  Proof. exact/rep2cs_prpr. Qed.

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
