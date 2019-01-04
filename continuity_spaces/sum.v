From mathcomp Require Import ssreflect ssrfun seq.
From rlzrs Require Import all_rlzrs.
Require Import all_core cs.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope cs_scope.
Section cs_sum.
  (* This is the sum of represented spaces. *)
  
  Definition linc Q A Q' A' phi := (@inl A A') \o_f phi \o_f (@fst Q Q').
  Arguments linc {Q} {A} {Q'} {A'}.

  Lemma linc_cntop Q A Q' A': (F2MF (@linc Q A Q' A')) \is_continuous_operator.
  Proof.
    rewrite cont_F2MF /linc => phi.
    by exists (fun q => [:: q.1]) => psi q' /=[->].  
  Qed.

  Definition rinc Q A Q' A' phi := (@inr A A') \o_f phi \o_f (@snd Q Q').
  Arguments rinc {Q} {A} {Q'} {A'}.

  Lemma rinc_cntop Q A Q' A': (F2MF (@rinc Q A Q' A')) \is_continuous_operator.
  Proof.
    rewrite cont_F2MF /rinc => phi.
    by exists (fun q => [:: q.2]) => psi q' /=[-> ].
  Qed.

  Definition inc Q A Q' A' (phi: (Q -> A) + (Q' -> A')):=
    match phi with
    | inl phi => linc phi
    | inr phi  => rinc phi
    end.

  Definition lslct Q A Q' A' somea (someq': Q') phipsi:=
    fun (q: Q) => match phipsi (q, someq'): A + A' with
	          | inl a => a
	          | inr _ => somea
	          end.

  Definition rslct Q A Q' A' (someq: Q) somea phipsi:=
    fun (q': Q') => match phipsi (someq, q'): A + A' with
		    | inl _ => somea
		    | inr b => b
	            end.
  
  Definition slct Q A Q' A' (someq: Q) somea (someq': Q') somea' phipsi:=
    match phipsi (someq, someq'): A + A' with
    | inl a => inl (lslct somea someq' phipsi)
    | inr b => inr (rslct someq somea' phipsi)
    end.
  
  Lemma lslct_linc Q A Q' A' somea someq' phi:
    @lslct Q A Q' A' somea someq' (linc phi) =  phi.
  Proof. by trivial. Qed.
  
  Lemma rslct_rinc Q A Q' A' someq somea' psi:
    @rslct Q A Q' A' someq somea' (rinc psi) =  psi.
  Proof. by trivial. Qed.
  
  Lemma slct_sur Q A Q' A' someq somea someq' somea':
    (@slct Q A Q' A' someq someq' somea somea') \is_surjective.
  Proof. by move => [phi | phi]; [exists (linc phi) | exists (rinc phi)]. Qed.
  
  Definition sum_rep (X Y: cs) :=
    ((rep X) +s+ (rep Y)) \o_R (F2MF (slct (someq X) (somea X) (someq Y) (somea Y))).
  
  Lemma sum_rep_sur (X Y: cs): (@sum_rep X Y) \is_cototal.
  Proof.
    apply/rcmp_cotot.
    - exact/fsum_cotot/rep_sur/rep_sur.
    by rewrite -F2MF_cotot; apply/slct_sur.
  Qed.                                     
  
  Lemma sum_rep_sing (X Y: cs): (@sum_rep X Y) \is_singlevalued.
  Proof. exact/rcmp_sing/F2MF_sing/fsum_sing/rep_sing/rep_sing. Qed.

  Canonical cs_sum_class (X Y: cs) := @continuity_space.Class _ _ _
    (interview.Mixin (@sum_rep_sur X Y)) (dictionary.Mixin (@sum_rep_sing X Y)) 
    (continuity_space.Mixin
       (someq X, someq Y) (inl (somea X))
       (prod_count (Q_count X) (Q_count Y))
       (sum_count (A_count X) (A_count Y))).
  Canonical cs_sum (X Y: cs) := continuity_space.Pack (@cs_sum_class X Y).

  Definition cs_lslct X Y : names (cs_sum X Y) -> names X:=
    lslct (somea X) (someq Y).
  
  Definition cs_rslct X Y: names (cs_sum X Y) -> names Y:=
    rslct (someq X) (somea Y).
  
  Definition cs_slct X Y: names (cs_sum X Y) -> names X + names Y:=
    slct (someq X) (somea X) (someq Y) (somea Y).
End cs_sum.
Arguments linc {Q} {A} {Q'} {A'}.
Arguments rinc {Q} {A} {Q'} {A'}.
Arguments inc {Q} {A} {Q'} {A'}.
Arguments cs_lslct {X} {Y}.
Arguments cs_rslct {X} {Y}.
Arguments cs_slct {X} {Y}.
Notation "X \+_cs Y" := (cs_sum X Y) (at level 35): cs_scope.

Section sums.
  Definition inl_rlzr (X Y: cs) : (questions X ->> questions (X \+_cs Y)) := F2MF linc.
  Arguments inl_rlzr {X} {Y}.
  Arguments mf_inl {S} {T}.

  Lemma inl_rlzr_spec (X Y: cs): inl_rlzr \realizes (mf_inl: X ->> X \+_cs Y).
  Proof.
      by rewrite F2MF_rlzr_F2MF => phi x phinx; eexists; split; first exact/eq_refl. 
  Qed.
  
  Lemma inl_cont (X Y: cs): (@inl X Y: _ -> _ \+_cs _) \is_continuous.
  Proof. by exists inl_rlzr; split; [exact/inl_rlzr_spec | exact/linc_cntop]. Qed.
  
  Definition inr_rlzr (X Y: cs): (questions Y ->> (questions (X \+_cs Y))):= F2MF rinc.
  Arguments inr_rlzr {X} {Y}.
  
  Lemma inr_rlzr_spec (X Y: cs): inr_rlzr \realizes (F2MF inr: Y ->> X \+_cs Y).
  Proof.
    rewrite F2MF_rlzr_F2MF => phi y phiny.
    by eexists; split; first exact/eq_refl.
  Qed.
  
  Lemma inr_cont (X Y: cs): (@inr X Y: _ -> cs_sum _ _) \is_continuous.
  Proof. by exists inr_rlzr; split; [exact/inr_rlzr_spec | exact/rinc_cntop]. Qed.

  Definition paib (T: Type) xx:= match (xx: T + T) with
		                 | inl x => x
		                 | inr x => x
	                         end.
  Arguments paib {T}.
  
  Definition paib_rlzr (X: cs): questions (X \+_cs X) ->> questions X:=
    F2MF (@paib (names X) \o_f (slct (someq X) (somea X) (someq X) (somea X))).
  
  Lemma paib_rlzr_crct (X: cs): (paib_rlzr X) \realizes (F2MF paib: X \+_cs X ->> X).
  Proof.
    rewrite F2MF_rlzr_F2MF => phi.
    by case => x; case; by case => psi [eq psinx]//=; rewrite eq.
  Qed.

  Lemma paib_rlzr_cntop (X: cs): (@paib_rlzr X) \is_continuous_operator.
  Proof.
    rewrite cont_F2MF => phi.
    exists (fun q => [:: (someq X, someq X); (q, someq X); (someq X, q)]).
    rewrite /paib/slct/=/lslct/rslct => q' psi [-> [eq [eq' _]]].
    by case: (psi (someq X, someq X)); [rewrite eq | rewrite eq'].
  Qed.

  Lemma paib_cont (X: cs): (@paib X: _ \+_cs _ -> _) \is_continuous.
  Proof. exists (paib_rlzr X); split; [exact/paib_rlzr_crct | exact/paib_rlzr_cntop]. Qed.

  Definition fsum_rlzr (X Y X' Y':cs) (F: (names X) ->> (names Y)) (G: (names X') ->> (names Y')):
    names (X \+_cs X') ->> questions (Y \+_cs Y'):=
    (F2MF inc) \o (F +s+ G) \o (F2MF cs_slct). 
  
  Lemma fsum_rlzr_spec (X Y X' Y': cs) F G (f: X ->> Y) (g: X' ->> Y'):
    F \realizes f -> G \realizes g ->
    (fsum_rlzr F G) \realizes (f +s+ g : cs_sum _ _ ->> cs_sum _ _).
  Proof.
    rewrite /fsum_rlzr (@comp_rcmp _ _ _ (F2MF inc)); last exact/F2MF_tot.
    rewrite comp_F2MF => rlzr rlzr' phi.
    case => x [].
    - case => [_ [<-] | _ [<-]].
      + case E: (cs_slct phi) => [psi | psi]; rewrite -/cs_slct E//.
        move => psinx [[]]//y val.
        have [| [Fpsi val'] prp]:= rlzr psi x psinx; first by exists y.
        split; first by exists (linc Fpsi); exists (inl Fpsi); split; first rewrite E.
        move => _ [[] Fphi [FpsiFpsi <-]]; last by rewrite E in FpsiFpsi.    
        have [ | _ prp']:= rlzr psi x psinx; first by exists y.
        have [ | fa []]//:= prp' Fphi; first by rewrite E in FpsiFpsi.
        by exists (inl fa); split; first exists (inl Fphi).
      case E: (cs_slct phi) => [psi | psi]; rewrite -/cs_slct E//.
      move => psinx [[]]//y val.
      have [| [Fpsi val'] prp]:= rlzr psi x psinx; first by exists y.
      split; first by exists (linc Fpsi); exists (inl Fpsi); split; first rewrite E.
      move => _ [[] Fphi [FpsiFpsi <-]]; last by rewrite E in FpsiFpsi.    
      have [ | _ prp']:= rlzr psi x psinx; first by exists y.
      have [ | fa []]//:= prp' Fphi; first by rewrite E in FpsiFpsi.
      by exists (inl fa); split; first exists (inl Fphi).
    case => [_ [<-] | _ [<-]].
    + case E: (cs_slct phi) => [psi | psi]; rewrite -/cs_slct E//.
      move => psinx [[]]//y val.
      have [| [Fpsi val'] prp]:= rlzr' psi x psinx; first by exists y.
      split; first by exists (rinc Fpsi); exists (inr Fpsi); split; first rewrite E.
      move => _ [[] Fphi [FpsiFpsi <-]]; first by rewrite E in FpsiFpsi.
      have [ | _ prp']:= rlzr' psi x psinx; first by exists y.
      have [ | fa []]//:= prp' Fphi; first by rewrite E in FpsiFpsi.
      by exists (inr fa); split; first exists (inr Fphi).
    case E: (cs_slct phi) => [psi | psi]; rewrite -/cs_slct E//.
    move => psinx [[]]//y val.
    have [| [Fpsi val'] prp]:= rlzr' psi x psinx; first by exists y.
    split; first by exists (rinc Fpsi); exists (inr Fpsi); split; first rewrite E.
    move => _ [[] Fphi [FpsiFpsi <-]]; first by rewrite E in FpsiFpsi.    
    have [ | _ prp']:= rlzr' psi x psinx; first by exists y.
    have [ | fa []]//:= prp' Fphi; first by rewrite E in FpsiFpsi.
    by exists (inr fa); split; first exists (inr Fphi).
  Qed. 

  Lemma fsum_rlzr_cntop X Y X' Y' F G:
    F \is_continuous_operator -> G \is_continuous_operator ->
    (@fsum_rlzr X Y X' Y' F G) \is_continuous_operator.
  Proof.
    rewrite /fsum_rlzr (@comp_rcmp _ _ _ (F2MF inc)); last exact/F2MF_tot.
    rewrite comp_F2MF => cont cont' phi Fphi.
    case E: (cs_slct phi) => [psi | psi].
    - move => [[] Fpsi []]; rewrite /= E // => val eq.
      have [mf mod]:= cont psi Fpsi val.
      exists (fun q => (someq X, someq X') :: (map (fun q' => (q', someq X')) (mf q.1))).
      move => q' phi' coin Fphi'.
      case E': (cs_slct phi') => [psi' |]; last first.
      * by move: E E'; rewrite /cs_slct/slct coin.1; case: (phi' (someq X, someq X')) => //.
      move => [[]Fpsi' [val' <-]]//; rewrite -eq/= /linc/=.
      f_equal; apply/mod/val'.
      elim: (mf q'.1) coin => // q K ih /= [equ [equ' coin]].
      split; last by apply/ih.
      move: E E'; rewrite /cs_slct/slct -equ.
      case: (phi (someq X, someq X')) => // _ [<-] [<-].
      by rewrite /lslct equ'.
    move => [[] Fpsi []]; rewrite /= E // => val eq.
    have [mf mod]:= cont' psi Fpsi val.
    exists (fun q => (someq X, someq X') :: (map (fun q' => (someq X, q')) (mf q.2))).
    move => q' phi' coin Fphi'.
    case E': (cs_slct phi') => [| psi'].
    - by move: E E'; rewrite /cs_slct/slct coin.1; case: (phi' (someq X, someq X')) => //.
    move => [[] Fpsi' [val' <-]]//; rewrite -eq/= /rinc/=.
    f_equal; apply/mod/val'.
    elim: (mf q'.2) coin => // q K ih /= [equ [equ' coin]].
    split; last by apply/ih.
    move: E E'; rewrite /cs_slct/slct -equ.
    case: (phi (someq X, someq X')) => // _ [<-] [<-].
    by rewrite /rslct equ'.
  Qed.

  Lemma fsum_hcr (X Y X' Y': cs) (f: X ->> Y) (g: X' ->> Y'):
    f \has_continuous_realizer -> g \has_continuous_realizer ->
    (f +s+ g: X \+_cs X' ->> Y \+_cs Y') \has_continuous_realizer.
  Proof.                                  
    move => [F [rlzr cont]] [G [rlzr' cont']]; exists (fsum_rlzr F G).
    by split; [exact/fsum_rlzr_spec | exact/fsum_rlzr_cntop ].
  Qed.

  Lemma fsum_cont (X Y X' Y': cs) (f: X -> Y) (g: X' -> Y'):
    f \is_continuous -> g \is_continuous ->
    (f +s+_f g:X \+_cs X' -> Y \+_cs Y') \is_continuous.
  Proof.
    by rewrite/continuous F2MF_fsum; apply/fsum_hcr.
  Qed.

  Lemma sum_uprp_fun (X Y Z: cs) (f: X -> Z) (g: Y -> Z):
    exists! (F: X + Y -> Z),
      (forall x, F (inl x) = f x)
      /\
      (forall y, F (inr y) = g y).
  Proof.
    exists (fun xy => paib (fsum f g xy)); rewrite /paib.
    by split => // F [eq eq']; apply functional_extensionality => [[x | y]].
  Qed.

  Lemma sum_rec_cont (X Y Z: cs) (f: X -> Z) (g: Y -> Z):
    f \is_continuous -> g \is_continuous ->
    (fun xsy => match (xsy: cs_sum _ _) with
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
  Qed.
End sums.