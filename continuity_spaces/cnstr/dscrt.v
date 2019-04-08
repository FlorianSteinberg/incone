From mathcomp Require Import ssreflect ssrfun seq choice.
From rlzrs Require Import all_rlzrs.
Require Import all_cs_base func classical_func classical_cont.
Require Import Morphisms FunctionalExtensionality ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope cs_scope.
Section discreteness.
  Definition discrete (X: cs) := forall (Y: cs) (f: X -> Y), f \is_continuous.

  Lemma dscrt_prpr: Proper (isomorphic ==> iff) discrete.
  Proof.
    move => X Y [[g ass] [[h ass'] [/=/sec_cncl cncl /sec_cncl cncl']]].
    split => dscrt Z f.
    - rewrite /continuous -(comp_id_r (F2MF f)) /mf_id -cncl' -comp_assoc.
      apply/comp_hcr; first by apply/ass_cont.
      by rewrite F2MF_comp_F2MF; apply/dscrt.
    rewrite /continuous -(comp_id_r (F2MF f)) /mf_id -cncl -comp_assoc.
    apply/comp_hcr; first by apply/ass_cont.
    by rewrite F2MF_comp_F2MF; apply/dscrt.
  Qed.
End discreteness.
Notation "X \is_discrete" := (discrete X) (at level 40).

Section cs_id.
  Context (S: Type).
  Definition id_rep:= make_mf (fun phi (s: S) => phi tt = s).

  Lemma id_rep_sur: id_rep \is_cototal.
  Proof. by move => s; exists (fun str => s). Qed.
  
  Lemma id_rep_sing: id_rep \is_singlevalued.
  Proof. by move => s t t' <- <-. Qed.

  Context (s: S) (S_count: S \is_countable).
  Definition cs_id_class:= @continuity_space.Class _ _ _
    (interview.Mixin id_rep_sur) (dictionary.Mixin id_rep_sing)
    (continuity_space.Mixin tt s unit_count S_count).

  Definition cs_id:= continuity_space.Pack cs_id_class.
  
  Lemma cs_id_dscrt:
    discrete cs_id.
  Proof.
    move => Y f.
    pose R:= make_mf (fun phi psi => psi \describes (f (phi tt)) \wrt Y).
    have Rtot: R \is_total by move => phi; apply/rep_sur.
    have [F icf]:= choice _ Rtot.
    exists (F2MF F); split; first by rewrite F2MF_rlzr_F2MF => fn n <-/=; apply/icf.
    rewrite cont_F2MF F2MF_cont_choice => phi q'; exists [::tt] => psi [eq _].
    by have ->: phi = psi by apply functional_extensionality => str; elim str.
  Qed.
End cs_id.

Lemma dscrt_id (X: cs) (x: X) (Xcount: X \is_countable):
  X \is_discrete -> X ~=~ (cs_id x Xcount).
Proof.
  move => dscrt.
  exists (exist_c (dscrt (cs_id x Xcount) id)).
  by exists (exist_c (@cs_id_dscrt X x Xcount X id)).
Qed.

Section TERMINAL.
Canonical cs_unit_class:= cs_id_class tt unit_count.
Canonical cs_unit:= cs_id tt unit_count.

Lemma unit_dscrt: discrete cs_unit.
Proof. exact/cs_id_dscrt. Qed.

Definition unit_fun (X: cs) (x: X) := tt: cs_unit.

Lemma trmnl_uprp_fun (X: cs): exists! f: X -> unit, True.
Proof.
by exists (@unit_fun X); split => // f _; apply functional_extensionality => x; elim (f x).
Qed.

Definition unit_fun_rlzr (X: cs): questions X ->> questions cs_unit
  := (F2MF (fun (_: name_space X) (_: queries cs_unit) => tt: answers cs_unit)).

Lemma unit_fun_rlzr_spec (X: cs) : (@unit_fun_rlzr X) \realizes (F2MF (@unit_fun X)).
Proof. by rewrite F2MF_rlzr_F2MF. Qed.

Lemma unit_fun_rlzr_cntop (X: cs): (@unit_fun_rlzr X) \is_continuous_operator.
Proof. by rewrite cont_F2MF; exists (fun _ => nil). Qed.

Lemma unit_fun_cont (X: cs): (@unit_fun X) \is_continuous.
Proof.
by exists (@unit_fun_rlzr X); split; [exact/unit_fun_rlzr_spec | exact/unit_fun_rlzr_cntop].
Qed.

Lemma unit_fun_hcr (X: cs): (F2MF (@unit_fun X): X ->> cs_unit) \has_continuous_realizer.
Proof. exact/unit_fun_cont. Qed.

Definition unit_fun_ass (X: cs) (Lq: seq (answers X) * queries cs_unit) :=
  inr tt : seq (queries X) + answers cs_unit.

Lemma unit_fun_ass_eval (X: cs): (U (@unit_fun_ass X)) \evaluates_to (@unit_fun_rlzr X). 
Proof.
apply/mon_eval; first exact/U_mon; first exact/F2MF_sing.
by move => phi _ <- q'; exists 2; rewrite /U/=.
Qed.

Lemma unit_fun_ass_spec (X: cs): associate X cs_unit (@unit_fun_ass X) (@unit_fun X).
Proof. exact/ntrvw.tight_rlzr/unit_fun_ass_eval/unit_fun_rlzr_spec. Qed.

Lemma trmnl_uprp_cont (X: cs): exists! f: X c-> cs_unit, True.
Proof.
have cdom: (@unit_fun X) \from codom (associate X cs_unit) by exists (@unit_fun_ass X); exact/unit_fun_ass_spec.
exists (exist (fun p => p \from codom (associate X cs_unit)) _ cdom).
split => // f' _.
apply/eq_sub/functional_extensionality => x /=.
by case: (sval f' x); case: (unit_fun x).
Qed.
End TERMINAL.

Section BOOL.
  Canonical cs_bool_class:= cs_id_class true bool_count.
  Canonical cs_bool:= cs_id true bool_count.

  Lemma bool_dscrt: discrete cs_bool.
  Proof. exact/cs_id_dscrt. Qed.
End BOOL.

Section NATURALS.
  Canonical cs_nat_class := cs_id_class 0 nat_count.
  Canonical cs_nat := cs_id 0 nat_count.

  Lemma S_cont: (S: cs_nat -> cs_nat) \is_continuous.
  Proof.
    exists (F2MF (fun phi q =>S (phi q))).
    split; first by rewrite F2MF_rlzr => /= n phi -> [m]; by exists m.
    by rewrite cont_F2MF => phi; exists (fun _ => [:: tt]) => str psi []; elim: str => ->.
  Qed.

  Lemma nat_dscrt (X: cs) (f: cs_nat -> X): f \is_continuous.
  Proof. exact/cs_id_dscrt. Qed.
  
  Lemma nat_nat_cont (f: nat -> nat -> nat):
    (fun (p: cs_nat \*_cs cs_nat) => f p.1 p.2: cs_nat) \is_continuous.
  Proof.
    exists (F2MF (fun phi q => f (phi (inl tt)).1 (phi (inr tt)).2)).
    split; first by rewrite F2MF_rlzr_F2MF => phi [n m] [/= <- <-].
    by rewrite cont_F2MF => phi; exists (fun _ => [:: inl tt; inr tt]) => psi str [-> [->]].
  Qed.
End NATURALS.