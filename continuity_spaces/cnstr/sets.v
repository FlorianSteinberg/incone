From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_rlzrs.
Require Import all_cs_base classical_func dscrt cprd.
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

Lemma rep_Sirp_sing: rep_Sirp \is_singlevalued.
Proof.
move => phi s s' [imp imp'] [pmi pmi'].
case: s imp imp' => [_ []// n val | prp _]; first by case: s' pmi pmi' => [_ []// | -> //]; exists n.
by case: s' pmi pmi' => // _[]// n val; apply prp; exists n.
Qed.

Canonical cs_Sirp_class:= @continuity_space.Class _ _ _
  (interview.Mixin rep_Sirp_sur) (dictionary.Mixin rep_Sirp_sing)
  (continuity_space.Mixin 0%nat false nat_count bool_count).

Canonical cs_Sirp:= continuity_space.Pack cs_Sirp_class.
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

Canonical cs_Kleeneans_class:= @continuity_space.Class _ _ _
  (interview.Mixin rep_K_sur) (dictionary.Mixin rep_K_sing)
  (continuity_space.Mixin 0%nat None nat_count (option_count bool_count)).
Canonical cs_Kleeneans:= continuity_space.Pack cs_Kleeneans_class.
End Kleeneans.

Section Opens.
Definition opens (X: cs):= X c-> cs_Sirp.
Notation "\O( X )" := (opens X) (at level 2, format "'\O(' X ')'").

Definition OO_fun (X: cs) (x: X) := (point_evaluation cs_Sirp x) : \O(\O(X)).

Lemma OO_fun_cont (X: cs): (@OO_fun X) \is_continuous.
Proof. exact/ptvl_cont. Qed.  

Definition admissible (X: cs) := F2MF (@OO_fun X)\^-1 \has_continuous_realizer.

End Opens.

Notation "\O( X )" := (opens X) (at level 2, format "'\O(' X ')'").
