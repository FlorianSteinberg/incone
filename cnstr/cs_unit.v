From mathcomp Require Import ssreflect ssrfun.
Require Import all_core all_cs_base.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TERMINAL.
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

Lemma unit_count: unit \is_countable.
Proof. by exists (fun _ => Some tt) => [[]]; exists 0. Qed.

Canonical cs_unit := continuity_space.Pack tt tt unit_count unit_count
	(dictionary.Pack (cs_id_modest_set_mixin unit)).

Definition unit_fun (X: cs) (x: X) := tt.

Lemma trmnl_uprp_fun (X: cs): exists! f: X -> unit, True.
Proof.
by exists (@unit_fun X); split => // f _; apply functional_extensionality => x; elim (f x).
Qed.

Lemma unit_fun_hcr (X: cs): (F2MF (@unit_fun X): X ->> cs_unit) \has_continuous_realizer.
Proof.
exists (F2MF (fun _ _ => tt)); split; first by rewrite F2MF_rlzr_F2MF.
by rewrite F2MF_cont; exists (fun _ => nil).
Qed.

Lemma unit_fun_cont (X: cs): (@unit_fun X: _ -> cs_unit) \is_continuous.
Proof. exact/unit_fun_hcr. Qed.

Definition unit_cfun X := exist_c (@unit_fun_hcr X) : (X c-> cs_unit).

Lemma trmnl_uprp_cont (X: cs): exists! f: X c-> cs_unit, True.
Proof.
exists (@unit_cfun X); split => // f _.
apply /eq_sub; apply functional_extensionality => x.
by case: (projT1 f x).
Qed.
End TERMINAL.