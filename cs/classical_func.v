From mathcomp Require Import ssreflect ssrfun seq.
From rlzrs Require Import all_rlzrs choice_dict.
Require Import facts all_core cs prod sub func classical_cont classical_mach.
Require Import FunctionalExtensionality ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma ass_cont (X Y: cs) (f: X -> Y): f \from (codom (@associate X Y)) <-> f \is_continuous.
Proof.
split => [[psi /=rlzr] | [F [rlzr cont]]]; first by exists \F_(M psi); split; last exact/FM_cont.
have [psi val]:= (M_universal (someq X) (somea X) (fun _ => somea Y) (questions_countable X) cont).
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
  (@eval_rlzr (questions X) (questions Y) (answers X) (answers Y))|_(dom (rep (X c-> Y \*_cs X))) \is_continuous_operator.
Proof.
move => psiphi [Fpsiphi [[[f x] [psinf phinx]] /eval_rlzr_val val]].
rewrite /= in psinf phinx; have phifd: (rprj psiphi) \from dom \F_(M (lprj psiphi)) by exists Fpsiphi.
have [mf [Lf prp]]:= FM_ucont (lprj psiphi).
exists (fun q' => map inl (Lf (rprj psiphi) q') ++ map inr (mf (rprj psiphi) q')) => q'.
exists (Fpsiphi q') => psi'phi' /coin_agre/coin_cat[coin coin'].
have : (rprj psiphi) \and (rprj psi'phi') \coincide_on (mf (rprj psiphi) q').
- by elim: (mf (rprj psiphi) q') coin' => // q K ih /= [eq /ih]; split; first rewrite /rprj eq.
have: (lprj psiphi) \and (lprj psi'phi') \coincide_on (Lf (rprj psiphi) q').
- by elim: (Lf (rprj psiphi) q') coin => // q K ih /= [eq /ih]; split; first rewrite /lprj eq.
move: coin coin' => _ _ coin coin'.
rewrite det_restr => [[[f' x'] [psi'nf' phi'nx']]] Fpsi'phi'/eval_rlzr_val val'.
rewrite /= in psi'nf' phi'nx'; pose psiphi':= name_pair (lprj psiphi) (rprj psi'phi').
have psiphi'nfx': psiphi' \is_description_of ((f, x'): X c-> Y \*_cs X).
- by trivial.
have [Fpsiphi' val'']: psiphi' \from dom eval_rlzr.
- by have []:= eval_rlzr_crct psiphi'nfx'; first exact/F2MF_dom.
have [ | mod _]:= prp (rprj psiphi); first by exists Fpsiphi.
have [a' tempcrt]:= mod q'.  
have crt := cert_icf val tempcrt _; move: a' tempcrt => _ _.
rewrite -(crt (rprj psi'phi') _ Fpsiphi' val''); last first.
- apply/coin_agre/coin'.
have mfeq: mf (rprj psiphi) q' = mf (rprj psi'phi') q'.
- have [ | _ [mod' _]]:= prp (rprj psiphi); first by exists Fpsiphi.
  have [a' crt']:= mod' q'.
  suff ->: mf (rprj psi'phi') q' = a' by apply/crt'; [exact/agre_ref | split; first exists Fpsiphi].
  apply/crt'; first by apply/coin_agre/coin'.
  split => //; apply/rlzr_dom; first exact/ psinf.
  - apply/phi'nx'.
  exact/F2MF_tot.
have eq: Lf (rprj psiphi) q' = Lf (rprj psi'phi') q'.
- have [ | _ [_ [mod' _]]]:= prp (rprj psi'phi'); first by exists Fpsiphi'.
  have [a' crt']:= mod' q'.
  have ->: Lf (rprj psiphi) q' = a'.
  - by apply/crt'; first by apply/coin_agre; rewrite -mfeq; exact/coin_sym/coin'.
  symmetry.
  apply/crt'; first exact/agre_ref; split => //.
  apply/rlzr_dom; first exact/psinf; first exact/phi'nx'; exact/F2MF_tot.
have [ | _ [_ [_ mod']]] := prp (rprj psi'phi'); first by exists Fpsiphi'.
have [a' crt']:= mod' q'.
suff ->: Fpsi'phi' q' = a' by symmetry; apply/crt'; first exact/agre_ref.
by apply/crt'; first by apply/coin_agre; rewrite -eq; exact/coin.
Qed.

Lemma eval_cont (X Y: cs): (@evaluation X Y) \is_continuous.
Proof.
exists (@eval_rlzr (questions X) (questions Y) (answers X) (answers Y))|_(dom (rep (X c-> Y \*_cs X))).
split; last exact/eval_rlzr_cntop.
rewrite rlzr_F2MF => psiphi fx psiphinfx.
have [ | [Fpsiphi val] prp]:= eval_rlzr_crct psiphinfx; first exact/F2MF_dom.
split => [ | Fq [_ val']]; first by exists Fpsiphi; split; first by exists fx.
by have [f'x' [nm ->]]:= prp Fq val'.                         
Qed.