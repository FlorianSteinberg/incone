From mathcomp Require Import ssreflect ssrfun seq.
From rlzrs Require Import all_rlzrs.
Require Import all_core all_cs_base classical_count classical_func cs dscrt.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section OPTIONSPACES.
  Context (X: cs).
  Definition rep_opt:= make_mf (fun phi (ox: option X) =>
               match ox with
               | some x => exists psi, phi =1 Some \o_f psi /\ psi \describes x wrt X
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
    - + suff <-: psi = psi' by move => psiny; rewrite (@answer_unique X psi x y).
        apply/functional_extensionality => q.
        by have := eq q; rewrite (eq' q) /=; case.
    - move => [psi [eq psinx]] eq'.
      by have:= (eq' (someq X)); rewrite eq.
    move => eq' [psi [eq psinx]].
    by have:= (eq' (someq X)); rewrite eq.
  Qed.

  Canonical cs_opt_class := @continuity_space.Class _ _ _
    (interview.Mixin rep_opt_sur) (dictionary.Mixin rep_opt_sing)
    (continuity_space.Mixin (someq X) None (Q_count X) (option_count (A_count X))).

  Canonical cs_opt := continuity_space.Pack cs_opt_class.
      
  Lemma Some_cont: (@Some X) \is_continuous.
  Proof.
    exists (F2MF (fun phi => Some \o_f phi)).
    split; first by rewrite F2MF_rlzr_F2MF => phi; exists phi.
    by rewrite cntop_F2MF => phi; exists (fun q => cons q nil) => q psi [/=<-].
  Qed.

  Lemma opt_rec_cont (Y: cs) (y: Y) (f: X -> Y):
    f \is_continuous -> (fun (ox: cs_opt) =>
                           match ox with
                           | None => y
                           | Some x => f x
                           end) \is_continuous.
  Proof.
    have [phiy phiny]:= get_description y.
    move => [F [/rlzr_F2MF rlzr cont]].
    exists (make_mf (fun phi Fphi =>
                       (exists psi, phi =1 Some \o_f psi /\ F psi Fphi)
                       \/
                       (phi =1 cnst None /\ Fphi =1 phiy))).
    split => [ | phi Fpsi [[psi [eq val]] | [eq val]]]; last first.
    - + exists (fun q => [:: someq X]) => q' phi' [coin _] Fphi'.
        case => [[psi [eq'' val']] | [eq'' ->]]; last by rewrite val.
        by have /= := eq (someq X); rewrite coin val eq''.
      have [mf mod]:= cont psi Fpsi val.
      exists (fun q => someq X :: mf q) => q' phi' /coin_lstn coin Fpsi'.
      case => [[psi' [eq' val']] | [eq' val']]; last by have:= eq (someq X); rewrite coin; [rewrite eq' | left].
      apply/mod/val'/coin_lstn => q /=lstn.
      by apply/Some_inj; have /= <-:= eq q; have /= <-:= eq' q; apply/coin; right.
    rewrite rlzr_F2MF => phi [x [psi [eq psinx]] | phinN]; last first.
    - split => [ | Fphi [[psi [eq val]] | [/=eq val]]]; first by exists phiy; right.
      + by have:= eq (someq X); rewrite phinN.
      by have ->: Fphi = phiy by apply/functional_extensionality => q; rewrite val.
    have [[Fpsi FpsiFpsi] prp]:= rlzr psi x psinx.
    split; first by exists Fpsi; left; exists psi; split.
    move => Fpsi' /= [[psi' [eq' val']] | [eq'']]; last by have:= eq'' (someq X ); rewrite eq.
    suff eq'': psi = psi' by apply/prp => //; rewrite eq''.
    apply/functional_extensionality => q.
    by have /= := eq' q; rewrite eq /=; case.
  Qed.

  Lemma opt_iso_sum: cs_opt ~=~ (cs_unit \+_cs X).
  Proof.
    have otscont: (fun (ox: cs_opt) => match ox with
                                         | None => inl tt
                                         | Some x => inr x: cs_unit \+_cs X
                                         end) \is_continuous.
    apply/opt_rec_cont/inr_cont.
    exists (exist_c otscont).
    have stocont: (fun (ttsx: cs_unit \+_cs X) => match ttsx with
                                                  | inl _ => (None: cs_opt)
                                                  | inr x => Some x
                                                  end) \is_continuous.
    - apply/sum_rec_cont/Some_cont.
      exists (mf_cnst (fun _ => None)).
      by split; [exact/cnst_rlzr | apply/cnst_cntop].
    exists (exist_c stocont).
    by split; case => //; case.
  Qed.

  Lemma Some_inv_hcr:
    ((F2MF Some)\^-1: cs_opt ->> X) \has_continuous_realizer.
  Proof.
    exists (F2MF (fun phi q => match phi q with
                               | None => somea X
                               | Some a => a
                               end)).
    split; last by apply/cntop_F2MF => phi; exists (fun q => [:: q]) => q' phi' [ ->].
    rewrite F2MF_rlzr => phi [x [psi [eq psinx]] _ | phinN []] //.
    exists x; split => //.
    suff ->: (fun q => match phi q with | Some a => a | None => somea X end) = psi by trivial.
    by apply/functional_extensionality => q; rewrite eq.
  Qed.  
End OPTIONSPACES.
