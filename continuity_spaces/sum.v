From mathcomp Require Import ssreflect ssrfun seq.
From rlzrs Require Import all_rlzrs.
Require Import all_names cs rs_names.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope cs_scope.  
Section sums.
  Definition inl_rlzr (X Y: cs) := F2MF (@linc (names X) (names Y)): _ ->> names (cs_sum _ _).
  Arguments inl_rlzr {X} {Y}.
  Arguments mf_inl {S} {T}.

  Lemma inl_rlzr_spec (X Y: cs): inl_rlzr \realizes (mf_inl: X ->> cs_sum X Y).
  Proof.
      by rewrite F2MF_rlzr_F2MF => phi x phinx; eexists; split; first exact/eq_refl. 
  Qed.
  
  Lemma inl_cont (X Y: cs): (@inl X Y: X -> cs_sum X Y) \is_continuous.
  Proof. by exists inl_rlzr; split; [exact/inl_rlzr_spec | apply/cntop_cntf/linc_cntf ]. Qed.
  
  Definition inr_rlzr (X Y: cs):= F2MF (@rinc (names X) (names Y)): _ ->> names (cs_sum _ _).
  Arguments inr_rlzr {X} {Y}.
  
  Lemma inr_rlzr_spec (X Y: cs): inr_rlzr \realizes (F2MF inr: Y ->> cs_sum X Y).
  Proof.
    rewrite F2MF_rlzr_F2MF => phi y phiny.
    by eexists; split; first exact/eq_refl.
  Qed.
  
  Lemma inr_cont (X Y: cs): (@inr X Y: _ -> cs_sum _ _) \is_continuous.
  Proof. by exists inr_rlzr; split; [exact/inr_rlzr_spec | exact/cntop_cntf/rinc_cntf]. Qed.

  Definition paib (T: Type) xx:= match (xx: T + T) with
		                 | inl x => x
		                 | inr x => x
	                         end.
  Arguments paib {T}.
  
  Definition paib_rlzr (X: cs):=
    F2MF (@paib (name_space X) \o_f (@slct (names X) (names X))): names (cs_sum _ _) ->> _.
  
  Lemma paib_rlzr_crct (X: cs): (paib_rlzr X) \realizes (F2MF paib: cs_sum X X ->> X).
  Proof.
    rewrite F2MF_rlzr_F2MF => phi.
    by case => x; case; by case => psi [eq psinx]//=; rewrite eq.
  Qed.

  Lemma paib_rlzr_cntop (X: cs): (@paib_rlzr X) \is_continuous_operator.
  Proof.
    rewrite cont_F2MF => phi.
    exists (fun q => [:: (someq, someq); (q, someq); (someq, q)]).
    rewrite /paib/slct/=/lslct/rslct => q' psi [-> [eq [eq' _]]].
    by case: (psi (someq, someq)); [rewrite eq | rewrite eq'].
  Qed.

  Lemma paib_cont (X: cs): (@paib X: cs_sum _ _ -> _) \is_continuous.
  Proof. exists (paib_rlzr X); split; [exact/paib_rlzr_crct | exact/paib_rlzr_cntop]. Qed.

  Lemma fsum_spec (X Y X' Y': cs) F G (f: X ->> Y) (g: X' ->> Y'):
    F \realizes f -> G \realizes g -> (fsum_rlzr F G) \realizes (f +s+ g).
  Proof.
    rewrite fsum_rlzr_comp sum_rep_spec.
    rewrite (@comp_rcmp _ _ _ (F2MF (@inc _ _))); last exact/F2MF_tot.
    rewrite comp_F2MF => rlzr rlzr' phi.
    case => x [].
    - case => [_ [<-] | _ [<-]].
      + case E: (slct phi) => [psi | psi] //.
        move => psinx [[]]//y val.
        have [| [Fpsi val'] prp]:= rlzr psi x psinx; first by exists y.
        split; first by exists (linc Fpsi); exists (inl Fpsi); split; first rewrite E.
        move => _ [[] Fphi [FpsiFpsi <-]]; last by rewrite E in FpsiFpsi.    
        have [ | _ prp']:= rlzr psi x psinx; first by exists y.
        have [ | fa []]//:= prp' Fphi; first by rewrite E in FpsiFpsi.
        by exists (inl fa); split; first exists (inl Fphi).
      case E: (slct phi) => [psi | psi]//.
      move => psinx [[]]//y val.
      have [| [Fpsi val'] prp]:= rlzr psi x psinx; first by exists y.
      split; first by exists (linc Fpsi); exists (inl Fpsi); split; first rewrite E.
      move => _ [[] Fphi [FpsiFpsi <-]]; last by rewrite E in FpsiFpsi.    
      have [ | _ prp']:= rlzr psi x psinx; first by exists y.
      have [ | fa []]//:= prp' Fphi; first by rewrite E in FpsiFpsi.
      by exists (inl fa); split; first exists (inl Fphi).
    case => [_ [<-] | _ [<-]].
    + case E: (slct phi) => [psi | psi]//.
      move => psinx [[]]//y val.
      have [| [Fpsi val'] prp]:= rlzr' psi x psinx; first by exists y.
      split; first by exists (rinc Fpsi); exists (inr Fpsi); split; first rewrite E.
      move => _ [[] Fphi [FpsiFpsi <-]]; first by rewrite E in FpsiFpsi.
      have [ | _ prp']:= rlzr' psi x psinx; first by exists y.
      have [ | fa []]//:= prp' Fphi; first by rewrite E in FpsiFpsi.
      by exists (inr fa); split; first exists (inr Fphi).
    case E: (slct phi) => [psi | psi]//.
    move => psinx [[]]//y val.
    have [| [Fpsi val'] prp]:= rlzr' psi x psinx; first by exists y.
    split; first by exists (rinc Fpsi); exists (inr Fpsi); split; first rewrite E.
    move => _ [[] Fphi [FpsiFpsi <-]]; first by rewrite E in FpsiFpsi.    
    have [ | _ prp']:= rlzr' psi x psinx; first by exists y.
    have [ | fa []]//:= prp' Fphi; first by rewrite E in FpsiFpsi.
    by exists (inr fa); split; first exists (inr Fphi).
  Qed. 

  (*
  Lemma fsum_hcr (X Y X' Y': cs) (f: X ->> Y) (g: X' ->> Y'):
    f \has_continuous_realizer -> g \has_continuous_realizer ->
    (f +s+ g) \has_continuous_realizer.
  Proof.                                  
    move => [F [rlzr cont]] [G [rlzr' cont']]; exists (fsum_rlzr F G).
    by split; [exact/fsum_spec | exact/fsum_rlzr_cntop ].
  Qed.

  Lemma fsum_cont (X Y X' Y': cs) (f: X -> Y) (g: X' -> Y'):
    f \is_continuous -> g \is_continuous ->
    (f +s+_f g) \is_continuous.
  Proof.
    by rewrite/continuous F2MF_fsum; apply/fsum_hcr.
  Qed.
*)
  Lemma sum_uprp_fun (X Y Z: cs) (f: X -> Z) (g: Y -> Z):
    exists! (F: X + Y -> Z),
      (forall x, F (inl x) = f x)
      /\
      (forall y, F (inr y) = g y).
  Proof.
    exists (fun xy => paib (fsum f g xy)); rewrite /paib.
    by split => // F [eq eq']; apply functional_extensionality => [[x | y]].
  Qed.
(*
  Lemma sum_rec_cont (X Y Z: cs) (f: X -> Z) (g: Y -> Z):
    f \is_continuous -> g \is_continuous ->
    (fun xsy => match xsy with
                | inl x => f x
                | inr y => g y
                end) \is_continuous.
  Proof.
    move => cont cont'.
    have [F [prp nque]]:= sum_uprp_fun f g; rewrite /continuous.
    have /F2MF_eq ->: (fun xsy => match xsy with
                                  | inl x => f x
                                  | inr y => g y
                                  end) =1 (@paib Z) \o_f (f +s+_f g).
    - by case.
    rewrite -F2MF_comp_F2MF F2MF_fsum.
    by have := comp_hcr (fsum_hcr cont cont') (paib_cont Z).
  Qed.*)
End sums.