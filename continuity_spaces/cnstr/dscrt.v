From mathcomp Require Import ssreflect ssrfun seq choice.
From rlzrs Require Import all_rlzrs.
Require Import axioms all_cs_base func classical_func classical_cont.
Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section discreteness.
  Definition discrete (X: cs) := forall (Y: cs) (f: X -> Y), f \is_continuous.

  Lemma dscrt_prpr: Proper (isomorphic ==> iff) discrete.
  Proof.
    move => X Y [[g ass] [[h ass'] [/=/sec_cncl cncl /sec_cncl cncl']]].
    split => dscrt Z f.
    - rewrite /continuous -(comp_id_r (F2MF f)) /mf_id -cncl' -comp_assoc.
      apply/comp_hcr; first by apply/cfun_spec.
      by rewrite F2MF_comp_F2MF; apply/dscrt.
    rewrite /continuous -(comp_id_r (F2MF f)) /mf_id -cncl -comp_assoc.
    apply/comp_hcr; first by apply/cfun_spec.
    by rewrite F2MF_comp_F2MF; apply/dscrt.
  Qed.
End discreteness.
Notation "X \is_discrete" := (discrete X) (at level 40).

Section cs_dscrt.
  Context (S: Type).
  Definition discrete_representation:= make_mf (fun phi (s: S) => phi tt = s).

  Lemma dscrt_rep_sur: discrete_representation \is_cototal.
  Proof. by move => s; exists (fun str => s). Qed.
  
  Lemma dscrt_rep_sing: discrete_representation \is_singlevalued.
  Proof. by move => s t t' <- <-. Qed.

  Context (s: S) (S_count: S \is_countable).

  Definition discrete_space: cs.
    exists S (Build_naming_space tt unit_count S_count) discrete_representation.
    by split; [apply/dscrt_rep_sur | apply/dscrt_rep_sing].
  Defined.  

  Lemma dscrt_dscrt: discrete discrete_space.
  Proof.
    move => Y f.
    pose R phi psi := psi \describes (f (phi tt)) \wrt Y.
    have [ | | F icf]:= countable_choice _ _ _ R; try by move => phi; apply/rep_sur.
    - have [cnt [sing sur]]:= S_count.
      exists (make_mf (fun n f => cnt n (f tt))).
      split => [n g h /= val val' | g]; first by apply/fun_ext; case; apply/sing/val'/val.
      by have [n val]:= sur (g tt); exists n.
    exists (F2MF F); split; try by rewrite F2MF_rlzr_F2MF => fn n <-/=; apply/icf.
    rewrite cont_F2MF => phi; exists (fun _ => [:: tt]) => q' psi [eq _].
    by have ->: phi = psi by apply/fun_ext => str; elim str.    
  Qed.
End cs_dscrt.

Lemma dscrt_id (X: cs) (x: X) (Xcount: X \is_countable):
  X \is_discrete -> X ~=~ (discrete_space Xcount).
Proof.
  move => dscrt.
  exists (exist_c (dscrt (discrete_space Xcount) id)).
  by exists (exist_c (@dscrt_dscrt X Xcount X id)).
Qed.

Section TERMINAL.
  Canonical cs_unit := discrete_space unit_count.

  Lemma unit_dscrt: discrete cs_unit.
  Proof. exact/dscrt_dscrt. Qed.

  Definition unit_fun (X: cs) (x: X) := tt: cs_unit.

  Lemma trmnl_uprp_fun (X: cs): exists! f: X -> unit, True.
  Proof.
    by exists (@unit_fun X); split => // f _; apply functional_extensionality => x; elim (f x).
  Qed.

  Definition unit_fun_rlzr (X: cs): B_ X ->> B_ cs_unit
    := (F2MF (fun _ => (fun _ => tt))).

  Lemma unit_fun_rlzr_spec (X: cs) : (@unit_fun_rlzr X) \realizes (@unit_fun X).
  Proof. by rewrite F2MF_rlzr_F2MF. Qed.

  Lemma unit_fun_rlzr_cntop (X: cs): (@unit_fun_rlzr X) \is_continuous_operator.
  Proof. by rewrite cont_F2MF; exists (fun _ => nil). Qed.

  Lemma unit_fun_cont (X: cs): (@unit_fun X) \is_continuous.
  Proof.
      by exists (@unit_fun_rlzr X); split; try exact/unit_fun_rlzr_spec; exact/unit_fun_rlzr_cntop.
  Qed.

  Lemma unit_fun_hcr (X: cs): (F2MF (@unit_fun X): X ->> cs_unit) \has_continuous_realizer.
  Proof. exact/unit_fun_cont. Qed.

  Definition unit_fun_ass (X: cs) (KLq: seq (queries X * replies X) * queries cs_unit) :=
    inr tt : seq (queries X) + replies cs_unit.

  Lemma unit_fun_ass_eval (X: cs): F_U _ _ (@unit_fun_ass X) =~= unit_fun_rlzr X. 
  Proof.
    apply/eval_F2MF/mon_eval; first exact/U_mon; first exact/F2MF_sing.
    by move => phi _ <- q'; exists 2; rewrite /U/=.
  Qed.

  Lemma unit_fun_ass_spec (X: cs): associate F_U X cs_unit (@unit_fun_ass X) (@unit_fun X).
  Proof. exact/ntrvw.tight_rlzr/eval_F2MF/unit_fun_ass_eval/unit_fun_rlzr_spec. Qed.

  Lemma trmnl_uprp_cont (X: cs): exists! f: X c-> cs_unit, True.
  Proof.
    have cdom: (@unit_fun X) \from codom (associate F_U X cs_unit).
    - by exists (@unit_fun_ass X); apply/unit_fun_ass_spec.
    exists (exist (fun p => p \from codom (associate F_U X cs_unit)) _ cdom).
    split => // f' _.
    apply/eq_sub/functional_extensionality => x /=.
    by case: (sval f' x); case: (unit_fun x).
  Qed.
End TERMINAL.

Section BOOL.
  Canonical cs_bool:= discrete_space bool_count.

  Lemma bool_dscrt: discrete cs_bool.
  Proof. exact/dscrt_dscrt. Qed.
End BOOL.

Section NATURALS.
  Canonical cs_nat := discrete_space nat_count.

  Lemma S_cont: (S: cs_nat -> cs_nat) \is_continuous.
  Proof.
    exists (F2MF (fun phi q =>S (phi q))).
    split; try by rewrite F2MF_rlzr => phi n /= ->.
    by rewrite cont_F2MF => phi; exists (fun _ => [:: tt]) => str psi []; elim: str => ->.
  Qed.

  Lemma nat_dscrt (X: cs) (f: cs_nat -> X): f \is_continuous.
  Proof. exact/dscrt_dscrt. Qed.
  
  Lemma nat_nat_cont (f: nat -> nat -> nat):
    (fun (p: cs_nat * cs_nat) => f p.1 p.2: cs_nat) \is_continuous.
  Proof.
    exists (F2MF (fun phi q => f (phi (inl tt)).1 (phi (inr tt)).2)).
    split; try by rewrite F2MF_rlzr => phi [n m] /prod_name_spec [/= <- <-].
    by rewrite cont_F2MF => phi; exists (fun _ => [:: inl tt; inr tt]) => psi str [-> [->]].
  Qed.
End NATURALS.