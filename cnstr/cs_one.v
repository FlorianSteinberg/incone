From mathcomp Require Import all_ssreflect.
Require Import all_core all_cs_base.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TERMINAL.
Inductive one := star.

Definition id_rep S := make_mf (fun phi (s: S) => phi star = s).

Lemma id_rep_sur S: (@id_rep S) \is_cototal.
Proof. by rewrite cotot_spec => s; exists (fun str => s). Qed.

Definition cs_id_assembly_mixin S: interview_mixin.type (one -> S) (S).
Proof. exists (@id_rep S); exact /id_rep_sur. Defined.

Lemma id_rep_sing S: (@id_rep S) \is_singlevalued.
Proof. by move => s t t' <- <-. Qed.

Definition cs_id_modest_set_mixin S:
	dictionary_mixin.type (interview.Pack (cs_id_assembly_mixin S)).
Proof. split; exact/id_rep_sing. Defined.

Lemma one_count:
	one \is_countable.
Proof.
exists (fun n => match n with 0 => None | S n => Some star end) => q.
by case q => [str | ]; [exists 1; elim: str | exists 0].
Qed.

Canonical cs_one := @cs.Pack
	one
	one
	star
	star
	one_count
	one_count
	(dictionary.Pack (cs_id_modest_set_mixin one)).

Definition one_fun (X: cs) (x: X) := star.

Lemma trmnl_uprp_fun (X: cs):
	exists! f: X -> one, True.
Proof.
by exists (@one_fun X); split => // f _; apply functional_extensionality => x; elim (f x).
Qed.

(*
Lemma one_fun_rec_fun (X: rep_space):
	(@one_fun X) \is_recursive_function.
Proof. by exists (fun phi q => star). Qed.

Lemma term_uprp_rec_fun (X: rep_space):
	exists! f: X -> one, exists (P: f \is_recursive_function), True.
Proof.
exists (@one_fun X); split; first by exists (@one_fun_rec_fun X).
by move => f _; apply functional_extensionality => x; elim (f x).
Qed.
*)

Lemma one_fun_hcr (X: cs):
	(F2MF (@one_fun X): X ->> cs_one) \has_continuous_realizer.
Proof.
exists (F2MF (fun _ _ => star)) => /=.
split; first by rewrite F2MF_rlzr_F2MF.
intros; exists nil; split => //.
by move => Fphi/= -> psi _ Fpsi ->.
Qed.

Definition one_cfun X := exist_c (@one_fun_hcr X) : (X c-> cs_one).

Lemma trmnl_uprp_cont (X: cs):
	exists! f: X c-> cs_one, True.
Proof.
exists (@one_cfun X); split => // f _.
apply /eq_sub; apply functional_extensionality => x.
by case: (projT1 f x).
Qed.

(*
Lemma one_cfun_cmpt_elt (X: cs):
	(@one_cfun X) \is_recursive_element.
Proof.
exists (fun Lq => inr star).
rewrite /delta/=/is_fun_name/=.
suffices ->: (eval (U (fun Lq => inr star))) =~= F2MF (fun _ _ => star).
	by rewrite -frlzr_rlzr => phi x phinx.
move => T T0 T1 phi Fphi.
rewrite /F2MF/=.
split; last by by move <-; exists 1.
by move => evl; apply functional_extensionality => q; elim (Fphi q).
Qed.

Lemma trmnl_uprp_rec_elt (X: rep_space):
	exists! f: X c-> rep_space_one, exists (P: f \is_recursive_element), True.
Proof.
exists (@one_cfun X); split; first by exists (@one_cfun_cmpt_elt X).
move => f _; apply /eq_sub /functional_extensionality => x.
by case (projT1 f x).
Qed.
*)
End TERMINAL.