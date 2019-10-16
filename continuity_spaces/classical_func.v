From mathcomp Require Import ssreflect ssrfun seq.
From rlzrs Require Import all_rlzrs choice_dict.
Require Import axioms all_names cs smod prod sub func classical_cont classical_mach.
Require Import Classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope cs_scope.
Lemma ass_cont (X Y: cs) (f: X -> Y): f \from (codom (associate X Y)) -> f \is_continuous.
Proof. by move => [psi /= rlzr]; exists (\F_(U psi)); split; try apply/FU_cont. Qed.

Lemma cfun_spec (X Y: cs) (f: X -> Y): f \from (codom (associate X Y)) <-> f \is_continuous.
Proof.
  split => [ | [F [cont rlzr]]]; first exact/ass_cont.
  have [psi val]:= exists_associate (Q_count X) (A_count X) (Q_count Y) cont.
  by exists psi; apply/ntrvw.tight_rlzr/val.
Qed.

Definition exist_c (X Y: cs) (f: X -> Y) (cont: f \is_continuous): (X c-> Y).
Proof. by exists f; apply/cfun_spec. Defined.

Lemma prod_uprp_cont (X Y Z: cs) (f: Z c-> X) (g: Z c-> Y):
  exists! (F: Z c-> (cs_prod X Y)),
    (forall z, (projT1 F z).1 = (projT1 f) z)
    /\
    (forall z, (projT1 F z).2 = (projT1 g) z).
Proof.
  move: f g => [/=f /ass_cont fcont] [g /= /ass_cont gcont].
  set F :Z -> X * Y := (f **_f g) \o_f mf.diag.
  have Fcont: F \is_continuous.
  - apply/cont_comp; first exact/fprd_cont.
    exists (F2MF (fun phi => pair (phi, phi))).
    split; last by apply/F2MF_rlzr => phi x; rewrite prod_name_spec.
    apply/cont_F2MF => phi.
    exists (fun q' => match q' with inl q' => [:: q'; someq] | inr q' => [:: q'; someq] end).
    by case => q' psi /=[-> [->]].
  exists (exist_c Fcont); split => // G [] eq eq'.
  apply/eq_sub/functional_extensionality => z; symmetry.
  exact/injective_projections/eq'/eq.
Qed.

Definition cs_comp (X Y Z: cs) (f: X c-> Y) (g: Y c-> Z): (X c-> Z).
Proof.
  exists ((projT1 g) \o_f projT1 f); apply/cfun_spec/cont_comp.
  - exact/cfun_spec/(projT2 g).
  exact/cfun_spec/(projT2 f).
Defined.

Notation "g \o_cs f" := (cs_comp f g) (at level 29): cs_scope.

Lemma cs_comp_spec (X Y Z: cs)(f: X c-> Y) (g: Y c-> Z): projT1 (g \o_cs f) =1 (projT1 g \o_f projT1 f).
Proof. done. Qed.

Lemma id_cont (X: cs): (@id X) \is_continuous.
Proof.
  exists (\F_(U (@id_ass X))).
  split; last exact/id_ass_spec.
  exact/FU_cont.
Qed.

Lemma eval_cont (X Y: cs): (@evaluation X Y) \is_continuous.
Proof. by exists (eval_rlzr X Y); split; try exact/eval_rlzr_cntop; exact/eval_rlzr_crct. Qed.

Definition pt_eval (X Y: cs) (x: X) (f: X c-> Y):= evaluation (f, x).

Lemma ptvl_val_cont (X Y: cs) (x: X): (@pt_eval X Y x) \is_continuous.
Proof.
  have [phi phinx]:= get_description x.
  exists (\F_(U (D phi))).
  split => [ | psi f psinf]; try exact/FU_cont.
  have [ | [Fphi /D_spec val] prp]:= psinf phi x phinx; first exact/F2MF_dom.
  split => [ | Fphi' /D_spec val']; first by exists Fphi.
  by have [fa []]:= prp Fphi' val'; exists fa.
Qed.

Definition point_evaluation (X Y: cs) (x: X):= exist_c (@ptvl_val_cont X Y x).

Lemma ptvl_cont (X Y: cs): (@point_evaluation X Y) \is_continuous.
Proof.
  apply/hcs_spec; exists (F2MF (@D (queries X) (queries Y) (replies X) (replies Y))).
  rewrite F2MF_rlzr; split => [ | phi x phinx psi f psinf _].
  - rewrite cont_F2MF; exact/D_cont.
  have [ | [Fphi /D_spec val] prp]:= psinf phi x phinx; first exact/F2MF_dom.
  split => [ | Fphi' /D_spec val']; first by exists (Fphi).
  by have [fa []]:= prp Fphi' val'; exists fa.
Qed.
