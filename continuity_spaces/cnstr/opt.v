From mathcomp Require Import ssreflect ssrfun seq.
From rlzrs Require Import all_rlzrs.
Require Import axioms all_cs_base classical_count classical_func cs dscrt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section OPTIONSPACES.
  Context (X: cs).
  Definition rep_opt:= make_mf (fun phi (ox: option X) =>
               match ox with
               | some x => exists psi, phi =1 Some \o_f psi /\ psi \describes x \wrt X
               | None => phi =1 cnst None
               end).

  Lemma rep_opt_sur: rep_opt \is_cototal.
  Proof.
    case => [x | ]; last by exists (cnst None).
    have [phi phinx]:= get_description x.
    by exists (Some \o_f phi); exists phi.
  Qed.

  Lemma rep_opt_sing: rep_opt \is_singlevalued.
  Proof.
    move => phi [x [y [psi [eq psinx]] [psi' [eq']] |]| [y | ]]//.
    - + suff <-: psi = psi' by move => psiny; f_equal; apply/answers_unique/psiny/psinx.
        apply/functional_extensionality => q.
        by have := eq q; rewrite (eq' q) /=; case.
    - move => [psi [eq psinx]] eq'.
      by have:= (eq' someq); rewrite eq.
    move => eq' [psi [eq psinx]].
    by have:= (eq' someq); rewrite eq.
  Qed.

  Canonical cs_opt: cs.
  exists (option X) (Build_naming_space someq (Q_count X) (option_count (A_count X))) rep_opt.
  by split; [apply/rep_opt_sur | apply/rep_opt_sing].
  Defined.

  Lemma Some_cont: (@Some X) \is_continuous.
  Proof.
    exists (F2MF (fun phi => Some \o_f phi)).
    split; try by rewrite F2MF_rlzr => phi; exists phi.
    by rewrite cont_F2MF => phi; exists (fun q => cons q nil) => q psi [/=<-].
  Qed.

  Lemma opt_rec_cont (Y: cs) (y: Y) (f: X -> Y):
    f \is_continuous -> (fun (ox: cs_opt) =>
                           match ox with
                           | None => y
                           | Some x => f x
                           end) \is_continuous.
  Proof.
    have [phiy phiny]:= get_description y.
    move => [F [cont /rlzr_F2MF rlzr]].
    exists (make_mf (fun phi Fphi =>
                       (exists psi, phi =1 Some \o_f psi /\ F psi Fphi)
                       \/
                       (phi =1 cnst None /\ Fphi =1 phiy))).
    split => [phi Fpsi [[psi [eq val]] | [eq val]] | ].
    - have [mf mod]:= cont psi Fpsi val.
      exists (fun q => someq :: mf q) => q' phi' /coin_agre coin Fpsi'.
      case => [[psi' [eq' val']] | [eq' val']]; last by have:= eq someq; rewrite coin; [rewrite eq' | left].
      apply/mod/val'/coin_agre => q /=lstn.
      by apply/Some_inj; have /= <-:= eq q; have /= <-:= eq' q; apply/coin; right.
    - exists (fun q => [:: someq]) => q' phi' [coin _] Fphi' /=.
      case => [[psi [eq'' val']] | [eq'' ->]]; last by rewrite val.
      by have /= := eq someq; rewrite coin val eq''.      
    move => phi [x [psi [eq psinx]] | phinN]; last first.
    - split => [ | Fphi [[psi [eq val]] | [/=eq val]]]; first by exists phiy; right.
      + by have:= eq someq; rewrite phinN.
      by exists y; have ->: Fphi = phiy by apply/functional_extensionality => q; rewrite val.
    have [[Fpsi FpsiFpsi] prp]:= rlzr psi x psinx.
    split; first by exists Fpsi; left; exists psi; split.
    move => Fpsi' /= [[psi' [eq' val']] | [eq'']]; last by have:= eq'' someq; rewrite eq.
    suff eq'': psi = psi' by exists (f x); split; first by apply/prp; rewrite ?eq''.
    by apply/fun_ext => q; have /= := eq' q; rewrite eq /=; case.
  Qed.

  (*
  Lemma opt_iso_sum: cs_opt ~=~ (cs_sum cs_unit X).
  Proof.
    have otscont: (fun (ox: cs_opt) => match ox with
                                         | None => inl tt
                                         | Some x => inr x: cs_sum cs_unit X
                                         end) \is_continuous.
    apply/opt_rec_cont/inr_cont.
    exists (exist_c otscont).
    have stocont: (fun (ttsx: cs_unit + X) => match ttsx with
                                                  | inl _ => (None: cs_opt)
                                                  | inr x => Some x
                                                  end) \is_continuous.
    - apply/sum_rec_cont/Some_cont.
      exists (mf_cnst (cnst None)).
      by split; [exact/cnst_rlzr | rewrite cont_F2MF; apply/cnst_cont].
    exists (exist_c stocont).
    by split; case => //; case.
  Qed.
  
  Lemma Some_inv_hcr:
    ((F2MF Some)\^-1: cs_opt ->> X) \has_continuous_realizer.
  Proof.
    exists (F2MF (fun phi q => match phi q with
                               | None => somea
                               | Some a => a
                               end)).
    split; last by apply/cont_F2MF => phi; exists (fun q => [:: q]) => q' phi' [ ->].
    rewrite F2MF_rlzr => phi [x [psi [eq psinx]] _ | phinN []] //.
    exists x; split => //.
    suff ->: (fun q => match phi q with | Some a => a | None => somea end) = psi by trivial.
    by apply/functional_extensionality => q; rewrite eq.
  Qed.  
*)
End OPTIONSPACES.
