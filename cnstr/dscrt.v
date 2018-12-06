From mathcomp Require Import ssreflect ssrfun seq choice.
Require Import all_core all_cs_base func classical_func classical_cont.
Require Import Morphisms FunctionalExtensionality ClassicalChoice.

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
  apply/comp_hcr; first by apply/ass_cont.
  rewrite F2MF_comp_F2MF; apply/dscrt.
rewrite /continuous -(comp_id_r (F2MF f)) /mf_id -cncl -comp_assoc.
apply/comp_hcr; first by apply/ass_cont.
rewrite F2MF_comp_F2MF; apply/dscrt.
Qed.

Definition id_rep S := make_mf (fun phi (s: S) => phi tt = s).

Lemma id_rep_sur S: (@id_rep S) \is_cototal.
Proof. by move => s; exists (fun str => s). Qed.

Definition cs_id_assembly_mixin S: interview_mixin.type (unit -> S) (S).
Proof. exists (@id_rep S); exact /id_rep_sur. Defined.

Lemma id_rep_sing S: (@id_rep S) \is_singlevalued.
Proof. by move => s t t' <- <-. Qed.

Definition cs_id_modest_set_mixin S:
	dictionary_mixin.type (interview.Pack (cs_id_assembly_mixin S)).
Proof. split; exact/id_rep_sing. Defined.

Definition cs_id_dict S:= dictionary.Pack (cs_id_modest_set_mixin S).

Lemma id_rep_dscrt S (count: S \is_countable) (somes: S):
  discrete (continuity_space.Pack tt somes unit_count count (cs_id_dict S)).
Proof.
move => Y f.
pose R:= make_mf (fun phi psi => psi \is_description_of (f (phi tt))).
have Rtot: R \is_total by move => phi; apply/rep_sur.
have [F icf]:= choice _ Rtot.
exists (F2MF F); split; first by rewrite F2MF_rlzr_F2MF => fn n <-/=; apply/icf.
rewrite F2MF_cont_choice => phi q'; exists [::tt] => psi [eq _].
by have ->: phi = psi by apply functional_extensionality => str; elim str.
Qed.
End discreteness.

Section TERMINAL.
Definition cs_unit := continuity_space.Pack tt tt unit_count unit_count
	(dictionary.Pack (cs_id_modest_set_mixin unit)).

Lemma unit_dscrt: discrete cs_unit.
Proof. exact/id_rep_dscrt. Qed.

Definition unit_fun (X: cs) (x: X) := tt: cs_unit.

Lemma trmnl_uprp_fun (X: cs): exists! f: X -> unit, True.
Proof.
by exists (@unit_fun X); split => // f _; apply functional_extensionality => x; elim (f x).
Qed.

Definition unit_fun_rlzr (X: cs) := (F2MF (fun (_: names X) (_: questions cs_unit) => tt: answers cs_unit)).

Lemma unit_fun_rlzr_spec (X: cs) : (@unit_fun_rlzr X) \realizes (F2MF (@unit_fun X)).
Proof. by rewrite F2MF_rlzr_F2MF. Qed.

Lemma unit_fun_rlzr_cntop (X: cs): (@unit_fun_rlzr X) \is_continuous_operator.
Proof. by rewrite -F2MF_cntop; exists (fun _ => nil). Qed.

Lemma unit_fun_cont (X: cs): (@unit_fun X) \is_continuous.
Proof.
by exists (@unit_fun_rlzr X); split; [exact/unit_fun_rlzr_spec | exact/unit_fun_rlzr_cntop].
Qed.

Lemma unit_fun_hcr (X: cs): (F2MF (@unit_fun X): X ->> cs_unit) \has_continuous_realizer.
Proof. exact/unit_fun_cont. Qed.

Definition unit_fun_ass (X: cs) (Lq: seq (answers X) * questions cs_unit) :=
  inr tt : seq (questions X) + answers cs_unit.

Lemma unit_fun_ass_eval (X: cs): (M (@unit_fun_ass X)) \evaluates_to (@unit_fun_rlzr X). 
Proof.
apply/mon_eval; first exact/M_mon; first exact/F2MF_sing.
by move => phi _ <- q'; exists 2; rewrite /M/=.
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
Canonical cs_bool := continuity_space.Pack tt false unit_count bool_count
	(cs_id_dict bool).

Lemma bool_dscrt: discrete cs_bool.
Proof. exact/id_rep_dscrt. Qed.
End BOOL.

Section NATURALS.

Canonical cs_nat := continuity_space.Pack
	tt
	0%nat
	unit_count
	nat_count
	(dictionary.Pack (cs_id_modest_set_mixin nat)).

Lemma S_rec_fun: (S: cs_nat -> cs_nat) \is_continuous.
Proof.
exists (F2MF (fun phi q =>S (phi q))).
split; first by rewrite F2MF_rlzr => /= n phi -> [m]; by exists m.
by rewrite -F2MF_cntop => phi; exists (fun _ => [:: tt]) => str psi []; elim: str => ->.
Qed.

Lemma nat_dscrt (X: cs) (f: cs_nat -> X): f \is_continuous.
Proof. exact/id_rep_dscrt. Qed.

Lemma nat_nat_cont (f: nat -> nat -> nat):
	(fun (p: cs_nat \*_cs cs_nat) => f p.1 p.2: cs_nat) \is_continuous.
Proof.
exists (F2MF (fun phi q => f (phi (inl tt)).1 (phi (inr tt)).2)).
split; first by rewrite F2MF_rlzr_F2MF => phi [n m] [/= <- <-].
by rewrite -F2MF_cntop => phi; exists (fun _ => [:: inl tt; inr tt]) => psi str [-> [->]].
Qed.
End NATURALS.

Require Import ZArith.
Definition cs_Z := continuity_space.Pack tt Z0 unit_count Z_count (dictionary.Pack (@cs_id_modest_set_mixin Z)).

Lemma Z_dscrt: discrete cs_Z.
Proof. exact/id_rep_dscrt. Qed.