From mathcomp Require Import ssreflect ssrfun seq .
From mf Require Import all_mf.
From rlzrs Require Import all_rlzrs.
Require Import all_cont naming_spaces representations cs.
Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope cs_scope.
Global Instance id_name_is_rep (B: naming_space): (@mf_id B) \is_representation.
by split => [q | ]; last exact/F2MF_sing; exists q.
Qed.

Canonical name_rep (B: naming_space) := Build_representation_of (id_name_is_rep B).

Canonical cs_names B := repf2cs (name_rep B).

Coercion cs_names: naming_space >-> cs.

Lemma id_cntf (Q A: Type): (@id (Q -> A)) \is_continuous_functional.
Proof. by move => phi; exists (fun q => [::q]) => q' psi [->]. Qed.

Lemma rep_hcs (X: cs): (delta_ X) \has_continuous_solution.
Proof.
  exists mf_id.
  split => [ | /= phi _ <- [x /=] phinx]; first exact/cont_F2MF/id_cntf.
  by split => [| _ <-]; [exists phi | exists x].
Qed.

Lemma rep_inv_hcr (X: cs): (delta_ X\^-1) \has_continuous_realizer.
Proof.
  exists mf_id; split; first exact/cont_F2MF/id_cntf.
  by apply/slvs_delta; rewrite comp_id_r; apply/icf_spec/id_icf_inv.
Qed.

Lemma prod_rep_spec D D': delta =~= F2MF (@unpair D D').
Proof.
  by rewrite /= rcmp_F2MF => phipsi [phi psi] /=; split; case => // <- <-.
Qed.

Lemma sum_rep_spec D D': delta =~= F2MF (@slct D D').
Proof.
  move => phipsi [phi | psi]/=.
  split => [[[phi' [-> ->] | psi' []]]// | ->]; last by exists (inl phi).
  by split => [[[phi' []| psi' [-> ->]]] | ->]; last by exists (inr psi).
Qed.                                      
                                                               
Section baire_fprd.
  Lemma tight_F2MF S T (F: S ->> T) (f: S -> T):
    F \tightens (F2MF f) <-> F =~= F2MF f.
  Proof.
    split => [/tight_spec [subs prp s t] | ->]; last exact/tight_ref.
    split => [tfs | <-]//; first by apply/prp; split => //; exact/F2MF_tot.
    have [ | Fs val]:= subs s; first by exists (f s).
    by have ->//:= prp s Fs; split; first by exists (f s).
  Qed.
                                                    
  Lemma cntf_cont (B B': naming_space) (f: B -> B'):
    f \is_continuous_functional <-> f \is_continuous.
  Proof.
    split => [cntf | [F [cont /id_rlzr_tight /tight_F2MF]]]; last by rewrite -cntop_cntf => <-.
    by exists (F2MF f); split; last exact/id_rlzr_tight/tight_ref; apply/cont_F2MF.
  Qed.
      
  Lemma hcs_cntop (B B': naming_space) (F: B ->> B'):
    F \has_continuous_solution <-> exists G, G \tightens F /\ G \is_continuous_operator.
  Proof.
    by split => [[G [rlzr cont]] | [G [tight cont]]]; exists G; split; try apply/id_rlzr_tight.
  Qed.

  Lemma cntop_hcr (B B': naming_space) (F: B ->> B'):
    F \is_singlevalued -> F \has_continuous_realizer <-> F \is_continuous_operator.
  Proof.
    move => sing; split => [[G [cont /id_rlzr_tight rlzr]] |cont]; first exact/cont_exte/sing/cont.
    by apply/hcs_cntop; exists F; split; try apply/tight_ref.
  Qed.
        
  Context (B B' D D': naming_space).

  Definition fprd_rlzr (F: B ->> D) (G: B' ->> D'):=
    make_mf (fun phipsi FphiGpsi =>
	       FphiGpsi = pair (unpair FphiGpsi)
	       /\
	       (F ** G) (unpair phipsi) (unpair FphiGpsi)).

  Definition fprd_rlzr_comp F G: fprd_rlzr F G =~= (F2MF (@pair D D')) \o (F ** G) \o delta.
  Proof.
    rewrite prod_rep_spec comp_assoc comp_rcmp; last exact/F2MF_tot.
    rewrite comp_F2MF => phipsi FphiGpsi.
    by split => [[{2}-> val] | [[Fphi Gpsi] [val <-]]] //; exists (unpair FphiGpsi); split.
  Qed.
      
  Lemma fprd_rlzr_spec (F: B ->> D) (G: B' ->> D'): (fprd_rlzr F G) \solves (F ** G).
  Proof.
    rewrite rlzr_delta fprd_rlzr_comp -!comp_assoc !prod_rep_spec.
    by have /sec_cncl ->:= (@pairK D D'); rewrite comp_id_l; apply/tight_ref.
  Qed.

  Lemma map_inl T T' (L: seq T) t: t \from L -> (inl t:T + T') \from (map inl L).
  Proof.
    by elim: L t => // t L ih t' /=[-> | lstn]; [by left | right; apply/ih].
  Qed.

  Lemma map_inr T T' (L: seq T') t: t \from L -> (inr t:T + T') \from (map inr L).
  Proof.
    by elim: L t => // t L ih t' /=[-> | lstn]; [by left | right; apply/ih].
  Qed.

  Lemma fprd_cntop F G: F \is_continuous_operator -> G \is_continuous_operator ->
                       (fprd_rlzr F G) \is_continuous_operator.
  Proof.
    rewrite !cntop_spec => cont cont' phi [FGphi [np [/=FphiFGphi GphiFGphi]]].
    have [ | Lf mod]:= cont (lprj phi); first by exists (lprj FGphi).
    have [ | Lf' mod']:= cont' (rprj phi); first by exists (rprj FGphi).
    exists (fun qq' => match qq' with
	               | inl q => map inr (Lf' someq) ++ map inl (Lf q)
	               | inr q' => map inl (Lf someq) ++ map inr (Lf' q')
                       end) => [[q | q']].
    - have [psi' crt]:= mod q; have [Fpsi' crt']:= mod' (someq);  exists (FGphi (inl q)).
      move => psi /coin_cat[/coin_agre coin /coin_agre coin'] Fpsi [ np' [/=val'l val'r]].
      rewrite np np'; apply injective_projections => //=.
      - rewrite (crt (lprj phi) _ (lprj FGphi))//; last exact/coin_ref.
        rewrite (crt (lprj psi) _ (lprj Fpsi))// coin_agre /lprj => q' lstn.
        by rewrite /= (coin' (inl q')) //; apply/map_inl.
      rewrite (crt' (rprj phi) _ (rprj FGphi)) //; last exact/coin_ref.
      rewrite (crt' (rprj psi) _ (rprj Fpsi)) // coin_agre /rprj => q' lstn.
      by rewrite /= (coin (inr q')) //;apply/map_inr.      
    have [psi' crt]:= mod' q'; have [Fpsi' crt']:= mod someq; exists (FGphi (inr q')).
    move => psi /coin_cat[/coin_agre coin /coin_agre coin'] Fpsi [ np' [/=val'l val'r]].
    rewrite np np'; apply injective_projections => //=.
      rewrite (crt' (lprj phi) _ (lprj FGphi)) //; last exact/coin_ref.
      rewrite (crt' (lprj psi) _ (lprj Fpsi)) // coin_agre /lprj => q lstn.
      by rewrite /= (coin (inl q)) //;apply/map_inl.      
    rewrite (crt (rprj phi) _ (rprj FGphi))//; last exact/coin_ref.
    rewrite (crt (rprj psi) _ (rprj Fpsi))// coin_agre /rprj => q lstn.
    by rewrite /=(coin' (inr q)) //; apply/map_inr.
  Qed.

  Definition lcry_rlzr (F: _ ->> D) (phi: B): B' ->> D := make_mf (fun psi => F (pair (phi,psi))).
  
  Fixpoint collect_right S T (L: seq (S + T)) :=
    match L with
    | nil => nil
    | a :: L' => match a with
                 | inr b => b :: (collect_right L')
                 | inl _ => collect_right L'
                 end
    end.
  
  Lemma lcry_cntop F phi: F \is_continuous_operator -> (lcry_rlzr F phi) \is_continuous_operator.
  Proof.
    rewrite !cntop_spec => cont psi [Fphipsi /= val].
    have [ | mf mod]:= cont (pair (phi,psi)); first by exists Fphipsi.
    exists (fun q => someq :: collect_right (mf q)) => q.
    exists (Fphipsi q) => psi' coin Fphipsi' val'.
    apply/crt_icf/val'; first exact/val; first exact/mod.
    elim: (mf q) coin => //; case => q' L ih.
    - by case => /=eq coin; split; [rewrite eq | apply/ih].
    rewrite/=; case => eq [eq' coin].
    by split; [rewrite eq' | apply/ih].
  Qed.
  
  Definition rcry_rlzr (F: _ ->> D) (psi: B'): B ->> D:=
    make_mf (fun phi => F (pair (phi, psi))).
  
  Fixpoint collect_left S T (L: seq (S + T)) :=
    match L with
    | nil => nil
    | a :: L' => match a with
                 | inl b => b :: (collect_left L')
                 | inr _ => collect_left L'
                 end
    end.
  
  Lemma rcry_cntop F psi: F \is_continuous_operator -> (rcry_rlzr F psi) \is_continuous_operator.
  Proof.
    rewrite !cntop_spec => cont phi [Fphipsi /= val].
    have [ | mf mod]:= cont (pair (phi, psi)); first by exists Fphipsi.
    exists (fun q => someq :: collect_left (mf q)) => q.
    exists (Fphipsi q) => psi' coin Fphipsi' val'.
    apply/(crt_icf _)/val'; first exact/val; first exact/mod.
    elim: (mf q) coin => //; case => q' L ih.
    - rewrite/=; case => eq [eq' coin].
      by split; [rewrite eq' | apply/ih].
    by case => /=eq coin; split; [rewrite eq | apply/ih].
  Qed.

  Definition fsum_rlzr (F: B ->> D) (G: B' ->> D') :=
    make_mf (fun phipsi FphiGpsi =>
	       FphiGpsi = inc (slct FphiGpsi)
	       /\
	       (F +s+ G) (slct phipsi) (slct FphiGpsi)).

  Lemma fsum_rlzr_comp F G: fsum_rlzr F G =~= (F2MF (@inc D D')) \o (F +s+ G) \o delta. 
  Proof.
    rewrite sum_rep_spec comp_assoc comp_rcmp; last exact/F2MF_tot.
    rewrite comp_F2MF => phipsi FphiGpsi.
    by split => [[{2}-> val] | [[Fphi | Gpsi] [val <-]]] //; exists (slct FphiGpsi).
  Qed.
  (*
  Lemma fsum_rlzr_cntop F G:
    F \is_continuous_operator -> G \is_continuous_operator ->
    (fsum_rlzr F G) \is_continuous_operator.
  Proof.
    rewrite fsum_rlzr_comp sum_rep_spec.
    rewrite (@comp_rcmp _ _ _ (F2MF (inc (B' := D')))); last exact/F2MF_tot.
    rewrite comp_F2MF => cont cont' phi Fphi.
    case E: (slct phi) => [psi | psi].
    - move => [[] Fpsi []]; rewrite /= E // => val eq.
      have [mf mod]:= cont psi Fpsi val.
      exists (fun q => (someq, someq) :: (map (fun q' => (q', someq)) (mf q.1))).
      move => q' phi' coin Fphi'.
      case E': (slct phi') => [psi' |]; last first.
      * by move: E E'; rewrite /slct/slct coin.1; case: (phi' (someq, someq)) => //.
      move => [[]Fpsi' [val' <-]]//; rewrite -eq/= /linc/=.
      f_equal; apply/mod/val'.
      elim: (mf q'.1) coin => // q K ih /= [equ [equ' coin]].
      split; last by apply/ih.
      move: E E'; rewrite /slct/slct -equ.
      case: (phi (someq, someq)) => // _ [<-] [<-].
      by rewrite /lslct equ'.
    move => [[] Fpsi []]; rewrite /= E // => val eq.
    have [mf mod]:= cont' psi Fpsi val.
    exists (fun q => (someq, someq) :: (map (fun q' => (someq, q')) (mf q.2))).
    move => q' phi' coin Fphi'.
    case E': (slct phi') => [| psi'].
    - by move: E E'; rewrite /slct/slct coin.1; case: (phi' (someq, someq)) => //.
    move => [[] Fpsi' [val' <-]]//; rewrite -eq/= /rinc/=.
    f_equal; apply/mod/val'.
    elim: (mf q'.2) coin => // q K ih /= [equ [equ' coin]].
    split; last by apply/ih.
    move: E E'; rewrite /slct/slct -equ.
    case: (phi (someq, someq)) => // _ [<-] [<-].
    by rewrite /rslct equ'.
  Qed.*)
End baire_fprd.
