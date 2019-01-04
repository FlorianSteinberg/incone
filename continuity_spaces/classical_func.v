From mathcomp Require Import ssreflect ssrfun seq.
From rlzrs Require Import all_rlzrs choice_dict.
Require Import facts all_core cs smod prod sub func classical_cont classical_mach Duop.
Require Import FunctionalExtensionality ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma ass_cont (X Y: cs) (f: X -> Y): f \from (codom (@associate X Y)) <-> f \is_continuous.
Proof.
split => [[psi /=rlzr] | [F [rlzr cont]]]; first by exists \F_(U psi); split; last exact/FM_cont.
have [psi val]:= (M_universal (someq X) (somea X) (fun _ => somea Y) (Q_count X) cont).
by exists psi; exact/ntrvw.tight_rlzr/val.
Qed.

Definition exist_c (X Y: cs) (f: X -> Y) (cont: f \is_continuous): (X c-> Y).
Proof. by exists f; apply/ass_cont. Defined.

Lemma prod_uprp_cont (X Y Z: cs) (f: Z c-> X) (g: Z c-> Y):
  exists! (F: Z c-> (cs_prod X Y)),
    (forall z, (projT1 F z).1 = (projT1 f) z)
    /\
    (forall z, (projT1 F z).2 = (projT1 g) z).
Proof.
set F :Z -> X \*_cs Y := (projT1 f **_f projT1 g) \o_f diag.
have Fcont: F \is_continuous.
- exact/(cont_comp _ (diag_cont Z))/fprd_cont/ass_cont/(projT2 g)/ass_cont/(projT2 f).
exists (exist_c Fcont); split => // G [] eq eq'.
apply/eq_sub/functional_extensionality => z; symmetry.
exact/injective_projections/eq'/eq.
Qed.

Definition cs_comp (X Y Z: cs) (f: X c-> Y) (g: Y c-> Z): (X c-> Z).
Proof.
exists ((projT1 g) \o_f projT1 f); apply/ass_cont/cont_comp.
- exact/ass_cont/(projT2 g).
exact/ass_cont/(projT2 f).
Defined.

Notation "g \o_cs f" := (cs_comp f g) (at level 29).

Lemma cs_comp_spec (X Y Z: cs)(f: X c-> Y) (g: Y c-> Z): projT1 (g \o_cs f) =1 (projT1 g \o_f projT1 f).
Proof. done. Qed.

Lemma eval_rlzr_cntop (X Y: cs):
  (@eval_rlzr (queries X) (queries Y) (answers X) (answers Y))|_(dom (rep (X c-> Y \*_cs X))) \is_continuous_operator.
Proof.
rewrite !cntop_spec => psiphi [Fpsiphi [[[f x] [psinf phinx]] /eval_rlzr_val val]].
rewrite /= in psinf phinx; have phifd: (rprj psiphi) \from dom \F_(U (lprj psiphi)) by exists Fpsiphi.
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
- by elim: (qf q') coin' => // q K ih /= [eq /ih]; split; first rewrite /rprj eq.
have: (lprj psiphi) \and (lprj psi'phi') \coincide_on (sf q').
- by elim: (sf q') coin => // q K ih /= [eq /ih]; split; first rewrite /lprj eq.
move: coin coin' => _ _ coin coin'.  
rewrite det_restr => [[[f' x'] [/=psi'nf' phi'nx']]] Fpsi'phi'/eval_rlzr_val val'.
rewrite /= in psi'nf' phi'nx'; pose psiphi':= name_pair (lprj psiphi) (rprj psi'phi').
have psiphi'nfx': psiphi' \describes (f, x') wrt (X c-> Y \*_cs X).
- by trivial.
have [Fpsiphi' val'']: psiphi' \from dom eval_rlzr.
- by have []:= eval_rlzr_crct psiphi'nfx'; first exact/F2MF_dom.
have [a' tempcrt]:= qfmodF q'. 
have crt := crt_icf val tempcrt _; move: a' tempcrt => _ _.
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
Qed.

Lemma eval_cont (X Y: cs): (@evaluation X Y) \is_continuous.
Proof.
exists (@eval_rlzr (queries X) (queries Y) (answers X) (answers Y))|_(dom (rep (X c-> Y \*_cs X))).
split; last exact/eval_rlzr_cntop.
rewrite rlzr_F2MF => psiphi fx psiphinfx.
have [ | [Fpsiphi val] prp]:= eval_rlzr_crct psiphinfx; first exact/F2MF_dom.
split => [ | Fq [_ val']]; first by exists Fpsiphi; split; first by exists fx.
by have [f'x' [nm ->]]:= prp Fq val'.                         
Qed.

Definition pt_eval (X Y: cs) (x: X) (f: X c-> Y):= evaluation (f, x).

Lemma ptvl_val_cont (X Y: cs) (x: X): (@pt_eval X Y x) \is_continuous.
Proof.
  have [phi phinx]:= get_description x.
  exists (\F_(U (D phi))).
  rewrite rlzr_F2MF.
  split => [psi f psinf | ]; last exact/FM_cont.
  have [ | [Fphi /D_spec val] prp]:= psinf phi x phinx; first exact/F2MF_dom.
  split => [ | Fphi' /D_spec val']; first by exists Fphi.
  have [fa [Fphi'nfa]]:= prp Fphi' val'.
  by rewrite /pt_eval /evaluation => ->.
Qed.

Definition point_evaluation (X Y: cs) (x: X):= exist_c (@ptvl_val_cont X Y x).

Lemma ptvl_cont (X Y: cs): (@point_evaluation X Y) \is_continuous.
Proof.
  exists (F2MF (@D (queries X) (queries Y) (answers X) (answers Y))).
  rewrite F2MF_rlzr_F2MF; split => [phi x phinx psi f psinf _| ]; last exact/D_cntop.
  have [ | [Fphi /D_spec val] prp]:= psinf phi x phinx; first exact/F2MF_dom.
  split => [ | Fphi' /D_spec val']; first by exists (Fphi).
  have [fa [Fphinfa]]:= prp Fphi' val'.
  rewrite /point_evaluation/pt_eval/evaluation/= => ->.
  by exists fa.      
Qed.
