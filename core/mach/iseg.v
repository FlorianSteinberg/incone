From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mpf.
Require Import baire cont.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section initial_segments.
Context (Q: countType) (noq: Q) (noq_spec: pickle noq = 0) (A: Type).
Notation B := (Q -> A).

Definition inverse_pickle n:= match pickle_inv Q n with
	| Some q => q
	| None => noq
end.

Fixpoint segment_rec n m {struct m} := match m with
	| 0 => [::]
	| S m' => [:: inverse_pickle (n + m') & segment_rec n m']
end.

Lemma size_seg_rec n m: size (segment_rec n m) = m.
Proof. by elim: m => // m /= ->. Qed.

Definition segment n m := segment_rec n (m.+1-n).

Lemma size_seg n m: size (segment n m) = m.+1-n.
Proof. by rewrite /segment; apply size_seg_rec. Qed.

Lemma seg_recr n m : n <= m.+1 ->
	segment n m.+1 = segment m.+1 m.+1 ++ segment n m.
Proof.
by move => ineq; rewrite /segment (@subSn (m.+1)) // subSn// subnn /= addn0 subnKC.
Qed.

Lemma seg_recl n m: n <= m ->
	segment n m = segment n.+1 m ++ segment n n.
Proof.
move => ineq; rewrite /segment subnS subSn//= subSn // subnn/= addn0.
by elim: (m - n) => [ | k ih]; [rewrite addn0 | rewrite /= ih addSn addnS].
Qed.

Lemma cat_seg n k m:
	segment (n + k).+1 ((n + k).+1 + m) ++ segment n (n + k)
		= segment n ((n + k).+1 + m).
Proof.
elim: k => [ | k /= ih].
	rewrite !addn0 (@seg_recl n (n.+1 + m)) //.
	by rewrite addSn; apply /leqW/leq_addr.
rewrite -addnS in ih; rewrite /=addSn (@seg_recr n (n + k.+1 + m)); last first.
	by apply/leqW; rewrite -addnA; apply/leq_addr.
rewrite -ih catA -(@seg_recr (n + k.+1) (n + k.+1 + m)); last first.
	by apply/leqW/leq_addr.
rewrite (@seg_recl (n + k.+1)); last by apply/leqW/leq_addr.
rewrite -catA addnS -(@seg_recr n)//; last by apply/leqW/leq_addr.
Qed.

Fixpoint iseg n:= match n with
	| 0 => nil
	| S n' => [:: inverse_pickle n' & iseg n']
end.

Lemma iseg_seg n: iseg n.+1 = segment 0 n.
Proof. by rewrite /segment; elim: n => // n; rewrite /= !add0n => ->. Qed.

Lemma iseg_cat_seg n k: n.+1 < k -> segment n.+1 k.-1 ++ iseg n.+1 = iseg k.
Proof.
case: k => //; case => //k ineq; rewrite iseg_seg.
have:= cat_seg 0 n (k - n); rewrite !add0n.
by rewrite addSn subnKC // iseg_seg.
Qed.

Lemma size_iseg n: size (iseg n) = n.
Proof. by elim: n => //n ih /=; case: (pickle_inv Q n) => [a | ]; rewrite /= ih. Qed.

Lemma iseg_subl n m:
	  n <= m -> (iseg n) \is_sublist_of (iseg m).
Proof.
elim: m => [ | m ih]; first by rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt; case/orP => [/eqP -> | ] //=.
by case: (pickle_inv Q m) => //; right; apply/ih.
Qed.

Lemma lstn_iseg: forall a, List.In a (iseg (pickle a).+1).
Proof. by move => a /=; rewrite /inverse_pickle pickleK_inv; left. Qed.

Lemma iseg_base a: forall n, List.In a (iseg n) -> pickle a < n.
Proof.
elim => // n ih/=; rewrite /inverse_pickle.
case E: (pickle_inv Q n) => [q | ] /=[<- | lstn]; try exact/leqW/ih; last by rewrite noq_spec.
by rewrite -(pickle_invK Q n) /oapp E.
Qed.

Lemma iseg_ex a n: List.In a (iseg n) -> exists m, m < n /\ m = pickle a.
Proof.
elim: n => // n ih /=; rewrite /inverse_pickle; case E: (pickle_inv Q n) => [q | ] /= [<- | lstn];
		try by have [m []]:= ih lstn; exists m; split; first exact/leqW.
	by exists n; split; last by rewrite -(pickle_invK Q n) /oapp E.
exists (0); split => //.
Qed.

Fixpoint max_elt K := match K with
  | nil => 0
  | cons q K' => maxn (pickle (q: Q)).+1 (max_elt K')
end.

Lemma melt_app L K:
	max_elt (L ++ K) = maxn (max_elt L) (max_elt K).
Proof. by elim: L K; [move => K; rewrite max0n | intros; rewrite /= (H K) maxnA]. Qed.

Lemma list_melt K (phi psi: B):
	phi \and psi \coincide_on (iseg (max_elt K)) -> phi \and psi \coincide_on K.
Proof.
apply/coin_subl; elim: K => // q K subl q' /=[-> | lstn].
	exact/iseg_subl/lstn_iseg/leq_maxl.
exact/iseg_subl/subl/lstn/leq_maxr.
Qed.

Definition pickle_min:= forall n, max_elt (iseg n) <= n.

Lemma lstn_melt K a: List.In a K -> pickle a < max_elt K.
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
by apply/lstn_melt/subl; left.
Qed.

Lemma melt_iseg n : max_elt (iseg n) <= n.
Proof.
elim: n => // n ih /=; rewrite /inverse_pickle.
case E: (pickle_inv Q n) => /= [q | ]; rewrite geq_max; apply/andP; split; try exact/leqW.
	by apply/iseg_base; rewrite -(pickle_invK Q n) /oapp E; apply/lstn_iseg.
by rewrite noq_spec.
Qed.

Lemma iseg_melt K: K \is_sublist_of (iseg (max_elt K)).
Proof.
by move => q lstn; apply/iseg_subl/lstn_iseg/lstn_melt.
Qed.
End initial_segments.