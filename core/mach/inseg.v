From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mpf.
Require Import baire cont.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section initial_segments.
Context (Q: countType) (someq: Q) (A: Type).
Notation B := (Q -> A).

Fixpoint iseg m := match m with
  | 0 => nil
  | S n => match pickle_inv Q n with
  	| None => (someq:: iseg n)
  	|	Some q => (q :: iseg n)
  end
end.

Lemma size_iseg n: size (iseg n) = n.
Proof. by elim: n => //n ih /=; case: (pickle_inv Q n) => [a | ]; rewrite /= ih. Qed.

Lemma iseg_subl n m:
	  n <= m -> (iseg n) \is_sublist_of (iseg m).
Proof.
elim: m => [ | m ih]; first by rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt; case/orP => [/eqP -> | ] //=.
by case: (pickle_inv Q m) => //; right; apply/ih.
Qed.

Lemma iseg_ex a n:
	 List.In a (iseg n) -> exists m, m < n /\ m = pickle a.
Proof.
elim: n => // n ih /=.
case E: (pickle_inv Q n) => [q | ] /= [<- | lstn].
by exists n; rewrite -(pickle_invK Q n) /oapp E.

case
by have [m [ineq eq]]:= ih lstn; exists m; split => //; apply leqW.
exists n.
by have [m [ineq eq]]:= ih lstn; exists m; split => //; apply leqW.
Qed.

Lemma iseg_base a: forall n, List.In a (iseg n) -> pickle a < n.
Proof.
move => n lstn; have [m [ineq eq]]:= iseg_ex lstn.
by apply/leq_trans/ineq; rewrite -(pickle_invK Q m) eq/=.
Qed.

Fixpoint max_elt K := match K with
  | nil => 0
  | cons q K' => maxn (pickle (q: Q)).+1 (max_elt K')
end.

Lemma melt_app L K:
	max_elt (L ++ K) = maxn (max_elt L) (max_elt K).
Proof. by elim: L K; [move => K; rewrite max0n | intros; rewrite /= (H K) maxnA]. Qed.

Lemma iseg_sec: forall a, List.In a (iseg (pickle a).+1).
Proof. by move => a /=; rewrite pickleK_inv; left. Qed.

Lemma list_melt K (phi psi: B):
	phi \and psi \coincide_on (iseg (max_elt K)) -> phi \and psi \coincide_on K.
Proof.
apply/coin_subl; elim: K => // q K subl q' /=[-> | lstn].
apply/iseg_subl/iseg_sec/leq_maxl.
apply/iseg_subl/subl/lstn/leq_maxr.
Qed.

Definition pickle_min:= forall n, max_elt (iseg n) <= n.

Lemma lstn_sec_melt K a: List.In a K -> pickle a < max_elt K.
Proof.
elim: K a => // a K ih a'/=.
by case => [<- | lstn]; apply/leq_trans; [|exact: leq_maxl|apply ih|exact: leq_maxr].
Qed.

Lemma melt_subl L K:
	L \is_sublist_of K -> max_elt L <= max_elt K.
Proof.
elim: L => //a L ih /=subl.
case/orP: (leq_total (pickle a).+1 (max_elt L)) => [/maxn_idPr -> | /maxn_idPl ->].
by apply/ih => q lstn; apply/subl; right.
apply/lstn_sec_melt.
Qed.

Lemma inseg_melt K: cnt \is_surjective_function -> is_min_sec cnt sec ->
	K \is_sublist_of (in_seg (max_elt K)).
Proof.
intros; apply/ (@inseg_subl (S (sec q)) (max_elt K)); last exact: inseg_sec.
move: H1; elim K => //=; intros; case: H2 => [-> | lstn]; first by apply leq_maxl.
by apply /leq_trans; [apply H1 | apply leq_maxr].
Qed.
End INITIAL_SEGMENTS.
Notation "L '\is_sublist_of' K" := (forall q, List.In q L -> List.In q K) (at level 2).
