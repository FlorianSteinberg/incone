From mathcomp Require Import ssreflect ssrfun seq.
From rlzrs Require Import all_rlzrs choice_dict.
Require Import axioms all_names cs smod prod sub func classical_cont classical_mach.
Require Import Classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope cs_scope.
Lemma ass_cont (X Y: cs) (f: X -> Y): f \from (codom (@associate F_U X Y)) -> f \is_continuous.
Proof.
  by move => [psi /=rlzr]; exists (F_U _ _ psi); split; first exact/FU_cont.
Qed.

Lemma cfun_spec (X Y: cs) (f: X -> Y): f \from (codom (@associate F_U X Y)) <-> f \is_continuous.
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
 
Local Open Scope name_scope.
Lemma eval_rlzr_cntop (X Y: cs):
  (eval_rlzr F_U X Y)|_(dom (rep (cs_prod (X c-> Y) X))) \is_continuous_operator.
Proof.
  (*
  rewrite !cntop_spec => psiphi [Fpsiphi [[[f x] [psinf phinx]] /eval_rlzr_val val]].
  rewrite /= in psinf phinx; have phifd: (rprj psiphi) \from dom (F_U _ _  (lprj psiphi)) by exists Fpsiphi.
  have [FqM [FsM prp]]:= @FM_cont_spec (queries X) (queries Y) (answers X) (answers Y).
  have [subs [subs' [c_prp _]]]:= prp (lprj psiphi) (rprj psiphi).
  have [qf qvl]:= subs (rprj psiphi) phifd.
  have [sf svl]:= subs' (rprj psiphi) phifd.
  move: subs subs' => _ _.
  have [qfmodF [qfmodqF _]]:= c_prp qf qvl.
  move: c_prp => _.
  exists (fun q' => map inl (sf q') ++ map inr (qf q')) => q'.
  exists (Fpsiphi q') => psi'phi' /coin_cat[coin coin'].
  have : (rprj psiphi) \and (rprj psi'phi') \coincide_on (qf q').
  - by elim: (qf q') coin' => // q K ih /= [eq /ih]; split; first rewrite /rprj /= eq.
  have: (lprj psiphi) \and (lprj psi'phi') \coincide_on (sf q').
  - by elim: (sf q') coin => // q K ih /= [eq /ih]; split; first rewrite /lprj /= eq.
  move: coin coin' => _ _ coin coin'.  
  apply det_restr => [[[f' x'] [/=psi'nf' phi'nx']]] Fpsi'phi'/eval_rlzr_val val'.
  rewrite /= in psi'nf' phi'nx'; pose psiphi':= name_pair (lprj psiphi) (rprj psi'phi').
  have psiphi'nfx': psiphi' \is_name_of (f, x') by trivial.
  have [Fpsiphi' val'']: psiphi' \from dom (eval_rlzr X Y).
  - by have []:= eval_rlzr_crct psiphi'nfx'; first exact/F2MF_dom.
  have crt := crt_icf val (qfmodF q') _.
  rewrite -(crt (rprj psi'phi') _ Fpsiphi' val''); last by apply/coin'.
  have [subs [subs' [cprp _]]]:= prp (lprj psiphi) (rprj psi'phi').
  have [ | qf' qvl']:= subs (rprj psi'phi'); first by exists Fpsiphi'.
  move: subs subs' => _ _.
  have [_ [_ qf'modsF]]:= cprp qf' qvl'.
  move: cprp => _.
  have mfeq: qf q' = qf' q'.  
  - have [a' crt'] := qfmodqF q'.
    suff ->: qf' q' = a' by apply/crt'; first apply/coin_ref.
    by apply/crt'; first apply/coin'.
  have [_ [subs' [_ vprp]]]:= prp (lprj psiphi) (rprj psi'phi').
  have [ | sf' svl']:= subs' (rprj psi'phi'); first by exists Fpsiphi'.
  have [sfmodF _]:= vprp sf' svl'.
  move: vprp prp => _ _.
  have eq: sf q' = sf' q'.
  - have [a' crt']:= qf'modsF q'.
    have ->: sf' q' = a' by apply/crt'; first by rewrite -mfeq; apply/coin_ref.
    by apply/crt'; first by rewrite -mfeq; apply/coin_sym/coin'.
  have [a' crt']:= sfmodF q'.
  have ->: Fpsi'phi' q' = a' by apply/crt'; first by rewrite -eq; apply/coin.
  by symmetry; apply/crt'; first by rewrite -eq; apply/coin_ref.
Qed.*)
Admitted.
Local Close Scope name_scope.

Lemma id_cont (X: cs): (@id X) \is_continuous.
Proof.
  exists (F_U _ _ (@id_ass X)).
  split; last exact/id_ass_spec.
  exact/FU_cont.
Qed.

Lemma eval_cont (X Y: cs): (@evaluation F_U X Y) \is_continuous.
Proof.
  exists (eval_rlzr F_U X Y)|_(dom delta).
  split; first exact/eval_rlzr_cntop.
  rewrite rlzr_F2MF => psiphi fx psiphinfx.
  have [ | [Fpsiphi val] prp]:= eval_rlzr_crct psiphinfx; first exact/F2MF_dom.
  split => [ | Fq [/=_ val']]; first by exists Fpsiphi; split; first by exists fx.
  by have [f'x' [nm ->]]:= prp Fq val'.                         
Qed.

Definition pt_eval (X Y: cs) (x: X) (f: X c-> Y):= evaluation (f, x).

Lemma ptvl_val_cont (X Y: cs) (x: X): (@pt_eval X Y x) \is_continuous.
Proof.
  have [phi phinx]:= get_description x.
  exists (F_U _ _ (D phi: function_names F_U (function_names F_U _ _) _)).
  rewrite rlzr_F2MF.
  split => [ | psi f psinf]; try exact/FU_cont.
  have [ | [Fphi /D_spec val] prp]:= psinf phi x phinx; first exact/F2MF_dom.
  split => [ | Fphi' /D_spec val']; first by exists Fphi.
  have [fa [Fphi'nfa]]:= prp Fphi' val'.
  by rewrite /pt_eval /evaluation =>/= ->.
Qed.

Definition point_evaluation (X Y: cs) (x: X):= exist_c (@ptvl_val_cont X Y x).

Lemma ptvl_cont (X Y: cs): (@point_evaluation X Y) \is_continuous.
Proof.
  exists (F2MF (@D (queries X) (queries Y) (replies X) (replies Y))).
  rewrite F2MF_rlzr_F2MF; split => [ | phi x phinx psi f psinf _].
  - rewrite cont_F2MF; exact/D_cont.
  have [ | [Fphi /D_spec val] prp]:= psinf phi x phinx; first exact/F2MF_dom.
  split => [ | Fphi' /D_spec val']; first by exists (Fphi).
  have [fa [Fphinfa]]:= prp Fphi' val'.
  rewrite /point_evaluation/pt_eval/evaluation/= => ->.
  by exists fa.      
Qed.
