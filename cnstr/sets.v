From mathcomp Require Import all_ssreflect.
Require Import all_cs dscrt usig.
Require Import Classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SIERPINSKISPACE.
Inductive Sirp := top | bot.

Definition rep_Sirp := make_mf (fun phi s => (exists n:nat, phi n = true) <-> s = top).

Lemma rep_Sirp_sur: rep_Sirp \is_cototal.
Proof.
case; first by exists (fun _ => true); split => // _; exists 0.
by exists (fun _ => false); split => //; case.
Qed.

Definition Sirp_interview_mixin: interview_mixin.type (nat -> bool) Sirp.
Proof. exists rep_Sirp; exact/rep_Sirp_sur. Defined.

Definition Sirp_interview:= interview.Pack Sirp_interview_mixin.

Lemma rep_Sirp_sing: rep_Sirp \is_singlevalued.
Proof.
move => phi s s' [imp imp'] [pmi pmi'].
case: s imp imp' => [_ []// n val | prp _]; first by case: s' pmi pmi' => [_ []// | -> //]; exists n.
by case: s' pmi pmi' => // _[]// n val; apply prp; exists n.
Qed.

Definition Sirp_dictionary_mixin: dictionary_mixin.type Sirp_interview.
Proof. split; exact/rep_Sirp_sing. Defined.

Definition Sirp_dictionary:= dictionary.Pack Sirp_dictionary_mixin.

Canonical cs_Sirp := continuity_space.Pack 0%nat false nat_count bool_count Sirp_dictionary.
End SIERPINSKISPACE.

Section Kleeneans.
Inductive Kleeneans := false_K | true_K | bot_K.

Definition rep_K := make_mf (fun phi (t: Kleeneans) =>
	match t with
		| false_K => exists (n: nat), phi n = Some false /\ forall m, m < n -> phi m = None
		| true_K => exists (n: nat), phi n = Some true /\ forall m, m < n -> phi m = None
		| bot_K => forall n, phi n = None
	end).

Lemma rep_K_sur: rep_K \is_cototal.
Proof.
by case; [exists (fun _ => Some false) | exists (fun _ => Some true) | exists (fun _ => None)]; try exists 0.
Qed.

Definition Kleeneans_interview_mixin : interview_mixin.type (nat -> option bool) Kleeneans.
Proof. by exists rep_K; exact/rep_K_sur. Defined.

Definition Kleeneans_interview:= interview.Pack Kleeneans_interview_mixin.

Lemma rep_K_sing: rep_K \is_singlevalued.
Proof.
move => phi t t'.
case: t; case t' => //; try (move => [n [eq prp]] prp'; by rewrite prp' in eq);
  try (move => prp; case => n []; by rewrite prp); move => [n [eq prp]] [m []].
- case/orP: (leq_total m n) => ineq; rewrite leq_eqVlt in ineq.
  - by case/orP: ineq => [/eqP -> | ineq]; [rewrite eq | rewrite prp].
  by case/orP: ineq => [/eqP <- | ineq eq' prp']; [rewrite eq | rewrite prp' in eq].
case/orP: (leq_total m n) => ineq; rewrite leq_eqVlt in ineq.
- by case/orP: ineq => [/eqP -> | ineq]; [rewrite eq | rewrite prp].
by case/orP: ineq => [/eqP <- | ineq eq' prp']; [rewrite eq | rewrite prp' in eq].
Qed.

Definition Kleeneans_dictionary_mixin: dictionary_mixin.type Kleeneans_interview.
Proof. split; exact/rep_K_sing. Defined.

Definition Kleeneans_dictionary:= dictionary.Pack Kleeneans_dictionary_mixin.

Canonical cs_Kleeneans := continuity_space.Pack 0 None nat_count (option_count bool_count) Kleeneans_dictionary.
End Kleeneans.
