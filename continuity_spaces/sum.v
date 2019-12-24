From mathcomp Require Import ssreflect ssrfun seq.
From rlzrs Require Import all_rlzrs.
Require Import axioms all_names representations cs cs_names.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope cs_scope.  
Section sums.
  Definition inl_rlzr (X Y: cs) := F2MF (@linc (B_ X) (B_ Y)): _ ->> B_ (_ \+_cs _).
  Arguments inl_rlzr {X} {Y}.
  Arguments mf_inl {S} {T}.

  Lemma inl_rlzr_spec (X Y: cs): inl_rlzr \realizes (inl: X -> cs_sum X Y).
  Proof. by rewrite F2MF_rlzr => phi x phinx; eexists; split; first exact/eq_refl. Qed.
  
  Lemma inl_cont (X Y: cs): (@inl X Y: X -> cs_sum X Y) \is_continuous.
  Proof. by exists inl_rlzr; split; last exact/inl_rlzr_spec; apply/cntop_cntf/linc_cntf. Qed.
  
  Definition inr_rlzr (X Y: cs):= F2MF (@rinc (B_ X) (B_ Y)): _ ->> B_ (cs_sum _ _).
  Arguments inr_rlzr {X} {Y}.
  
  Lemma inr_rlzr_spec (X Y: cs): inr_rlzr \realizes (inr: Y -> cs_sum X Y).
  Proof. by rewrite F2MF_rlzr => phi y phiny; eexists; split; first exact/eq_refl. Qed.
  
  Lemma inr_cont (X Y: cs): (@inr X Y: _ -> cs_sum _ _) \is_continuous.
  Proof. by exists inr_rlzr; split; last exact/inr_rlzr_spec; exact/cntop_cntf/rinc_cntf. Qed.

  Definition paib (T: Type) xx:= match (xx: T + T) with
		                 | inl x => x
		                 | inr x => x
	                         end.
  Arguments paib {T}.
  
  Definition paib_rlzr (X: cs):=
    F2MF (@paib (B_ X) \o_f (@slct (B_ X) (B_ X))): B_ (_ \+_cs _) ->> _.
  
  Lemma paib_rlzr_crct (X: cs): (paib_rlzr X) \realizes (paib: cs_sum X X -> X).
  Proof. by rewrite F2MF_rlzr => phi [] x [] [] psi [eq /= psinx]//=; rewrite eq.  Qed.

  Lemma paib_rlzr_cntop (X: cs): (@paib_rlzr X) \is_continuous_operator.
  Proof.
    rewrite cont_F2MF => phi.
    exists (fun q => [:: (someq, someq); (q, someq); (someq, q)]).
    rewrite /paib/slct/=/lslct/rslct => q' psi [-> [eq [eq' _]]].
    by case: (psi (someq, someq)); [rewrite eq | rewrite eq'].
  Qed.

  Lemma paib_cont (X: cs): (@paib X: cs_sum _ _ -> _) \is_continuous.
  Proof. exists (paib_rlzr X); split; last exact/paib_rlzr_crct; exact/paib_rlzr_cntop. Qed.

  Lemma fsum_comp S T R S' T' R' (f: S ->> T) (f': S' ->> T') (g: R ->> S) (g': R' ->> S'):
    (f +s+ f') \o (g +s+ g') =~= (f \o g) +s+ (f' \o g').
  Proof.
    move => [r [t | t'] | r' [t | t']]; split => //; try by move => [[[s | s'] []]] //.
    - move => [[[s | s'] [val val'] subs]]; split => //; first by exists s.
      by move => s' grs'; have [ | [t' | ]] //:= subs (inl s'); exists t'.
    - case => [[s [grs fst] subs]].
      split => [ | [s' grs'| ]//]; first by exists (inl s).
      by have [t' fs't']:= subs s' grs'; exists (inl t').
    - move => [[[s | s'] [val val'] subs]]; split => //; first by exists s'.
      by move => s grs; have [ | [ | t]] //:= subs (inr s); exists t.
    case => [[s [grs fst] subs]].
    split => [ | [| s' grs']//]; first by exists (inr s).
    by have [t fs't]:= subs s' grs'; exists (inr t).
  Qed.

  
  Lemma sum_rep_spec (X Y: cs) : delta_ (X \+_cs Y) =~= delta +s+ delta \o delta.
  Proof. by rewrite sum_rep_spec /= sing_rcmp; last exact/F2MF_sing. Qed.

  Lemma fsum_tight S T S' T' (f: S ->> T) (g: S' ->> T') (f': S ->> T) (g': S' ->> T'):
    f \tightens f' -> g \tightens g' -> (f +s+ g) \tightens (f' +s+ g').
  Proof.
    move => tight tight'; apply split_tight => [[s [[t /= prp | t']] | s' [[t | t' /= prp]]] | [s | s'] [[t p | t' p]] ] //.
    - case (tight s) => [|[t' /= t'prp ] _]; first by exists t.
      by exists (inl t').
    - case (tight' s') => [|[t2 /= t2prp ] _]; first by exists t'.
      by exists (inr t2).
    - case => [t' /= prp | t' prp] //.
      case (tight s) => [| /= H1 H2]; first by exists t.
      by apply (H2 t' prp).
    case => [t'' /= prp | t'' prp] //.
    case (tight' s') => [| /= H1 H2]; first by exists t'.
    by apply (H2 t'' prp).
  Qed.

  Lemma fsum_rlzr_spec (X Y X' Y': cs) (f: X ->> Y) (g: X' ->> Y') F G:
    F \solves f -> G \solves g -> (fsum_rlzr F G) \solves (f +s+ g).
  Proof.
    move => /rlzr_delta rlzr /rlzr_delta rlzr'.
    rewrite rlzr_delta sum_rep_spec (sum_rep_spec (X:= Y)) fsum_rlzr_comp -!comp_assoc.
    apply/tight_comp_l => /=.
    rewrite !fsum_id (comp_assoc (_ +s+ _)) rcmp_id_l.
    have /sec_cncl -> : (cancel (@inc B_ Y B_ Y')  (@slct B_ Y B_(Y'))).  
    - by rewrite /slct/inc/linc/rinc/lslct/rslct => [[x | x]] /= //.
    rewrite comp_id_r !fsum_comp.
    exact/fsum_tight.
  Qed.
  (* Lemma fsum_spec (X Y X' Y': cs) F G (f: X ->> Y) (g: X' ->> Y'): *)
  (*   F \solves f -> G \solves g -> (fsum_rlzr F G) \solves (f +s+ g). *)
  (* Proof. *)
  (*   rewrite (@comp_rcmp _ _ _ (F2MF (@inc _ _))); last exact/F2MF_tot. *)
  (*   rewrite comp_F2MF => rlzr rlzr' phi. *)
  (*   case => x []. *)
  (*   - case => [_ [<-] | _ [<-]]. *)
  (*     + case E: (slct phi) => [psi | psi] //. *)
  (*       move => psinx [[]]//y val. *)
  (*       have [| [Fpsi val'] prp]:= rlzr psi x psinx; first by exists y. *)
  (*       split; first by exists (linc Fpsi); exists (inl Fpsi); split; first rewrite E. *)
  (*       move => _ [[] Fphi [FpsiFpsi <-]]; last by rewrite E in FpsiFpsi.     *)
  (*       have [ | _ prp']:= rlzr psi x psinx; first by exists y. *)
  (*       have [ | fa []]//:= prp' Fphi; first by rewrite E in FpsiFpsi. *)
  (*       by exists (inl fa); split; first exists (inl Fphi). *)
  (*     case E: (slct phi) => [psi | psi]//. *)
  (*     move => psinx [[]]//y val. *)
  (*     have [| [Fpsi val'] prp]:= rlzr psi x psinx; first by exists y. *)
  (*     split; first by exists (linc Fpsi); exists (inl Fpsi); split; first rewrite E. *)
  (*     move => _ [[] Fphi [FpsiFpsi <-]]; last by rewrite E in FpsiFpsi.     *)
  (*     have [ | _ prp']:= rlzr psi x psinx; first by exists y. *)
  (*     have [ | fa []]//:= prp' Fphi; first by rewrite E in FpsiFpsi. *)
  (*     by exists (inl fa); split; first exists (inl Fphi). *)
  (*   case => [_ [<-] | _ [<-]]. *)
  (*   + case E: (slct phi) => [psi | psi]//. *)
  (*     move => psinx [[]]//y val. *)
  (*     have [| [Fpsi val'] prp]:= rlzr' psi x psinx; first by exists y. *)
  (*     split; first by exists (rinc Fpsi); exists (inr Fpsi); split; first rewrite E. *)
  (*     move => _ [[] Fphi [FpsiFpsi <-]]; first by rewrite E in FpsiFpsi. *)
  (*     have [ | _ prp']:= rlzr' psi x psinx; first by exists y. *)
  (*     have [ | fa []]//:= prp' Fphi; first by rewrite E in FpsiFpsi. *)
  (*     by exists (inr fa); split; first exists (inr Fphi). *)
  (*   case E: (slct phi) => [psi | psi]//. *)
  (*   move => psinx [[]]//y val. *)
  (*   have [| [Fpsi val'] prp]:= rlzr' psi x psinx; first by exists y. *)
  (*   split; first by exists (rinc Fpsi); exists (inr Fpsi); split; first rewrite E. *)
  (*   move => _ [[] Fphi [FpsiFpsi <-]]; first by rewrite E in FpsiFpsi.     *)
  (*   have [ | _ prp']:= rlzr' psi x psinx; first by exists y. *)
  (*   have [ | fa []]//:= prp' Fphi; first by rewrite E in FpsiFpsi. *)
  (*   by exists (inr fa); split; first exists (inr Fphi). *)
  (* Qed.  *)
  
  (* Lemma fsum_hcr (X Y X' Y': cs) (f: X ->> Y) (g: X' ->> Y'): *)
  (*   f \has_continuous_realizer -> g \has_continuous_realizer -> *)
  (*   (f +s+ g) \has_continuous_realizer. *)
  (* Proof.                                   *)
  (*   move => [F [rlzr cont]] [G [rlzr' cont']]; exists (fsum_rlzr F G). *)
  (*   by split; [exact/fsum_spec | exact/fsum_rlzr_cntop ]. *)
  (* Qed. *)

  (* Lemma fsum_cont (X Y X' Y': cs) (f: X -> Y) (g: X' -> Y'): *)
  (*   f \is_continuous -> g \is_continuous -> *)
  (*   (f +s+_f g) \is_continuous. *)
  (* Proof. *)
  (*   by rewrite/continuous F2MF_fsum; apply/fsum_hcr. *)
  (* Qed. *)

  (* Lemma sum_uprp_fun (X Y Z: cs) (f: X -> Z) (g: Y -> Z): *)
  (*   exists! (F: X + Y -> Z), *)
  (*     (forall x, F (inl x) = f x) *)
  (*     /\ *)
  (*     (forall y, F (inr y) = g y). *)
  (* Proof. *)
  (*   exists (fun xy => paib (fsum f g xy)); rewrite /paib. *)
  (*   by split => // F [eq eq']; apply fun_ext => [[x | y]]. *)
  (* Qed. *)
  
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
