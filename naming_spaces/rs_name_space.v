From mathcomp Require Import ssreflect ssrfun seq .
From mf Require Import all_mf.
From rlzrs Require Import all_rlzrs.
Require Import all_cont naming_spaces cs.
Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope rs_scope.
Canonical rs_name_space (B: naming_space): represented_space.
  by exists B B mf_id; split => [q | ]; last exact/F2MF_sing; exists q.
Defined.

Lemma prod_rep_spec D D': delta =~= F2MF (@unpair D D').
  Proof. by move => phipsi [phi psi] /=; split; case => // <- <-. Qed.

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
    split => [cntf | [F [/id_rlzr_tight /tight_F2MF -> cont]]]; last exact/cntop_cntf.
    by exists (F2MF f); split; first exact/id_rlzr_tight/tight_ref; apply/cont_F2MF.
  Qed.
      
  Lemma hcr_cntop (B B': naming_space) (F: B ->> B'):
    F \has_continuous_realizer <-> exists G, G \tightens F /\ G \is_continuous_operator.
  Proof.
    by split => [[G [rlzr cont]] | [G [tight cont]]]; exists G; split; try apply/id_rlzr_tight.
  Qed.

  Lemma cntop_hcr (B B': naming_space) (F: B ->> B'):
    F \is_singlevalued -> F \has_continuous_realizer <-> F \is_continuous_operator.
  Proof.
    move => sing; split => [[G [/id_rlzr_tight rlzr cont]] |cont]; first exact/cont_exte/sing/cont.
    by apply/hcr_cntop; exists F; split; try apply/tight_ref.
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
      
  Lemma fprd_rlzr_spec (F: B ->> D) (G: B' ->> D'): (fprd_rlzr F G) \realizes (F ** G).
  Proof.
    rewrite rlzr_spec fprd_rlzr_comp -!comp_assoc !prod_rep_spec.
    have /sec_cncl ->:= (@pairK D D').
    rewrite comp_id_l; exact/tight_ref.
  Qed.

  Coercion L2SS: seq >-> subset.
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
	               | inl q => map inl (Lf q)
	               | inr q' => map inr (Lf' q')
                       end) => [[q | q']].
    - have [psi' crt]:= mod q; exists (FGphi (inl q)).
      move => psi /coin_agre coin Fpsi [ np' [/=val'l val'r]].
      rewrite np np'; apply injective_projections => //=.
      rewrite (crt (lprj phi) _ (lprj FGphi))//; last exact/coin_ref.
      rewrite (crt (lprj psi) _ (lprj Fpsi))// coin_agre /lprj => q' lstn.
      by rewrite (coin (inl q')) //; apply/map_inl.
    have [psi' crt]:= mod' q'; exists (FGphi (inr q')).
    move => psi /coin_agre coin Fpsi [ np' [/=val'l val'r]].
    rewrite np np'; apply injective_projections => //=.
    rewrite (crt (rprj phi) _ (rprj FGphi))//; last exact/coin_ref.
    rewrite (crt (rprj psi) _ (rprj Fpsi))// coin_agre /rprj => q lstn.
    by rewrite (coin (inr q)) //; apply/map_inr.
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
    exists (fun q => collect_right (mf q)) => q.
    exists (Fphipsi q) => psi' coin Fphipsi' val'.
    apply/crt_icf/val'; first exact/val; first exact/mod.
    by elim: (mf q) coin => // [[q' L ih /=/ih | q' L ih /= [-> /ih]]].
  Qed.
  
  Definition rcry (F: _ ->> D) (psi: B'): B ->> D:=
    make_mf (fun phi => F (pair (phi, psi))).
  
  Fixpoint collect_left S T (L: seq (S + T)) :=
    match L with
    | nil => nil
    | a :: L' => match a with
                 | inl b => b :: (collect_left L')
                 | inr _ => collect_left L'
                 end
    end.
  
  Lemma rcry_cntop F psi: F \is_continuous_operator -> (rcry F psi) \is_continuous_operator.
  Proof.
    rewrite !cntop_spec => cont phi [Fphipsi /= val].
    have [ | mf mod]:= cont (pair (phi, psi)); first by exists Fphipsi.
    exists (fun q => collect_left (mf q)) => q.
    exists (Fphipsi q) => psi' coin Fphipsi' val'.
    apply/(crt_icf _)/val'; first exact/val; first exact/mod.
    by elim: (mf q) coin => // [[q' L ih /= [-> /ih] | q' L ih /= /ih]].
  Qed.
End baire_fprd.