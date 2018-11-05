From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mpf.
Require Import baire cont.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section initial_segments.
Context (Q: Type) (cnt: nat -> Q).

Fixpoint segment_rec n m {struct m} := match m with
	| 0 => [::]
	| S m' => [:: cnt (n + m') & segment_rec n m']
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
	| S n' => [:: cnt n' & iseg n']
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
Proof. by elim: n => // n /= ->. Qed.

Lemma iseg_subl n m:
	  n <= m -> (iseg n) \is_sublist_of (iseg m).
Proof.
elim: m => [ | m ih]; first by rewrite leqn0 => /eqP ->.
by rewrite leq_eqVlt; case/orP => [/eqP -> | ] //=; right; apply/ih.
Qed.

Lemma iseg_ex a n: List.In a (iseg n) -> exists m, m < n /\ cnt m = a.
Proof.
elim: n => // n ih/=; case => [ | lstn]; first by exists n.
by have [m []]:= ih lstn; exists m; split => //; rewrite leqW.
Qed.

Lemma drop_iseg k m: drop k (iseg m) = iseg (m - k).
Proof.
move: {2}k (leqnn k) => l.
elim: l k m => [k m | n ih k m].
	by rewrite leqn0 => /eqP ->; rewrite drop0 subn0.
rewrite leq_eqVlt; case/orP => [/eqP ->| ]; last exact/ih.
rewrite -addn1 addnC -drop_drop.
rewrite ih//.
case: n ih => [ih | n ih]; last by rewrite ih // addSn add0n !subnS subn0.
by rewrite subn0 addn0; elim: (m) => //m' ihm /=; rewrite drop0 subn1.
Qed.

Lemma nth_iseg n m: nth (cnt 0) (iseg m) n = cnt (m - n).-1.
Proof. by rewrite -{1}(addn0 n) -nth_drop drop_iseg; elim: (m - n). Qed.

Context (sec: Q -> nat).
Fixpoint max_elt K := match K with
  | nil => 0
  | cons q K' => maxn (sec (q: Q)).+1 (max_elt K')
end.

Lemma melt_app L K:
	max_elt (L ++ K) = maxn (max_elt L) (max_elt K).
Proof. by elim: L K; [move => K; rewrite max0n | intros; rewrite /= (H K) maxnA]. Qed.

Definition pickle_min:= forall n, max_elt (iseg n) <= n.

Lemma lstn_melt K a: List.In a K -> sec a < max_elt K.
Proof.
elim: K a => // a K ih a'/=.
by case => [<- | lstn]; apply/leq_trans; [|exact: leq_maxl|apply ih|exact: leq_maxr].
Qed.

Lemma melt_subl L K:
	L \is_sublist_of K -> max_elt L <= max_elt K.
Proof.
elim: L => //a L ih /=subl.
case/orP: (leq_total (sec a).+1 (max_elt L)) => [/maxn_idPr -> | /maxn_idPl ->].
by apply/ih => q lstn; apply/subl; right.
by apply/lstn_melt/subl; left.
Qed.

Lemma lstn_iseg a: cancel sec cnt -> List.In a (iseg (sec a).+1).
Proof. by move => cncl; left. Qed.

Definition is_min_sec Q (cnt: nat -> Q) (sec : Q -> nat) :=
  cancel sec cnt /\ forall s,(forall m, cnt m = s -> sec s <= m).

Lemma iseg_base a n: is_min_sec cnt sec -> List.In a (iseg n) -> sec a < n.
Proof.
move => [cncl min]; elim: n => // n ih/=.
by case => [<- | lstn]; [apply/min | rewrite leqW//; apply/ih].
Qed.

Lemma melt_iseg n : is_min_sec cnt sec -> max_elt (iseg n) <= n.
Proof.
move => [cncl min]; elim: n => // n ih /=.
by rewrite geq_max; apply/andP; split; [apply/min | rewrite leqW].
Qed.

Lemma iseg_melt K: is_min_sec cnt sec -> K \is_sublist_of (iseg (max_elt K)).
Proof. by move => [cncl min] q lstn; apply/iseg_subl/lstn_iseg/cncl/lstn_melt. Qed.

Lemma list_melt A K (phi psi: Q -> A): cancel sec cnt ->
	phi \and psi \coincide_on (iseg (max_elt K)) -> phi \and psi \coincide_on K.
Proof.
move => cncl; apply/coin_subl; elim: K => // q K subl q' /=[-> | lstn].
	exact/iseg_subl/lstn_iseg/cncl/leq_maxl.
exact/iseg_subl/subl/lstn/leq_maxr.
Qed.
End initial_segments.

Section countTypes.
Context (Q: countType) (noq: Q) (noq_spec: pickle noq = 0).

Definition inverse_pickle n:= match pickle_inv Q n with
	| Some q => q
	| None => noq
end.

Lemma min_ip: is_min_sec inverse_pickle pickle.
Proof.
rewrite /inverse_pickle; split => [q | q n <-]; first by rewrite pickleK_inv.
case E: pickle_inv => [a  | ]; last by rewrite noq_spec.
by have := pickle_invK Q n; rewrite /oapp E => <-.
Qed.
End countTypes.