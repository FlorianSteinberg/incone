From mathcomp Require Import ssreflect seq ssrnat ssrbool eqtype ssrfun choice bigop.
From mf Require Import all_mf.
Require Import graphs.
Require Import Morphisms Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
   This file provides an interface for using an enumeration cnt: nat -> Q of a type Q to obtain
   a family of lists such that exhausts all the elements eventually if the enumeration is
   surjective. One could do this using the iota function from the standard library, i.e. by con-
   sidering the n-th initial-segment to be map cnt (iota 0 n), however for this the natural
   operation to append is rcons instead of cons. To get a more direct correspondence bewteen
   initial segments and potentially infinite lists in this file we consider the lists "backwards".
   For instance if cnt is chosen to be the identity function as enumeration of the natural numbers
   then iseg (@id nat) 5, i.e. initial segment of length 5, i.e. [:: 4, 3, 2, 1, 0] and the next
   the next initial segment can be obtained using cons. The file also provides a notion of
   segment i j, which is the list of elements with indices k such that i <= k <= j.
**)

Section initial_segments.
  Context (Q: Type) (cnt: nat -> Q).

  Fixpoint segment_rec n m {struct m} :=
    match m with
    | 0 => [::]
    | S m' => [:: cnt (n + m') & segment_rec n m']
    end.
  
  Lemma size_seg_rec n m: size (segment_rec n m) = m.
  Proof. by elim: m => // m /= ->. Qed.
  
  Definition segment n m := segment_rec n (m.+1-n).

  Lemma segnn i: segment i i = [:: cnt i].
  Proof. by rewrite /segment subSn // subnn /= addn0. Qed.
    
  Lemma seg_nil i j: (j < i)%nat -> segment i j = [::].
  Proof. by rewrite -subn_eq0 /segment => /eqP ->. Qed.

  Lemma size_seg n m: size (segment n m) = m.+1 - n.
  Proof. exact/size_seg_rec. Qed.
  
  Lemma seg_recr n m : n <= m.+1 ->
	               segment n m.+1 = segment m.+1 m.+1 ++ segment n m.
  Proof. by move => ineq; rewrite /segment (@subSn (m.+1)) // subSn// subnn /= addn0 subnKC. Qed.

  Lemma seg_recl n m: n <= m -> segment n m = segment n.+1 m ++ segment n n.
  Proof.
    move => ineq; rewrite /segment subnS subSn//= subSn // subnn/= addn0.
    by elim: (m - n) => [ | k ih]; [rewrite addn0 | rewrite /= ih addSn addnS].
  Qed.

  Lemma cat_seg n k m:
    segment (n + k).+1 ((n + k).+1 + m) ++ segment n (n + k)
    = segment n ((n + k).+1 + m).
  Proof.
    elim: k => [ | k /= ih].
    - rewrite !addn0 (@seg_recl n (n.+1 + m)) //.
      by rewrite addSn; apply /leqW/leq_addr.
      rewrite -addnS in ih; rewrite /=addSn (@seg_recr n (n + k.+1 + m)); last first.
    - by apply/leqW; rewrite -addnA; apply/leq_addr.
    rewrite -ih catA -(@seg_recr (n + k.+1) (n + k.+1 + m)); last first.
    - by apply/leqW/leq_addr.
    rewrite (@seg_recl (n + k.+1)); last by apply/leqW/leq_addr.
    by rewrite -catA addnS -(@seg_recr n)//; last by apply/leqW/leq_addr.
  Qed.
  
  Fixpoint iseg n:=
    match n with
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

  Lemma iseg_ex a n: a \from L2SS (iseg n) -> exists m, m < n /\ cnt m = a.
  Proof.
    elim: n => // n ih/=; case => [ | lstn]; first by exists n.
    by have [m []]:= ih lstn; exists m; split => //; rewrite leqW.
  Qed.

  Lemma drop_iseg k m: drop k (iseg m) = iseg (m - k).
  Proof.
    move: {2}k (leqnn k) => l.
    elim: l k m => [k m | n ih k m].
    - by rewrite leqn0 => /eqP ->; rewrite drop0 subn0.
    rewrite leq_eqVlt; case/orP => [/eqP ->| ]; last exact/ih.
    rewrite -addn1 addnC -drop_drop ih//.
    case: n ih => [ih | n ih]; last by rewrite ih // addSn add0n !subnS subn0.
    by rewrite subn0 addn0; elim: (m) => //m' ihm /=; rewrite drop0 subn1.
  Qed.

  Lemma nth_iseg n m: nth (cnt 0) (iseg m) n = cnt (m - n).-1.
  Proof. by rewrite -{1}(addn0 n) -nth_drop drop_iseg; elim: (m - n). Qed.

  Context (sec: Q -> nat).
  Fixpoint max_elt K :=
    match K with
    | nil => 0
    | cons q K' => maxn (sec (q: Q)).+1 (max_elt K')
    end.

  Lemma melt_app L K:
    max_elt (L ++ K) = maxn (max_elt L) (max_elt K).
  Proof. by elim: L K; [move => K; rewrite max0n | intros; rewrite /= (H K) maxnA]. Qed.

  Definition pickle_min:= forall n, max_elt (iseg n) <= n.
  
  Lemma L2SS_melt K a: a \from L2SS K -> sec a < max_elt K.
  Proof.
    elim: K a => // a K ih a'/=.
    by case => [<- | lstn]; apply/leq_trans; [|exact: leq_maxl|apply ih|exact: leq_maxr].
  Qed.

  Lemma melt_subl L K:
    L \is_sublist_of K -> max_elt L <= max_elt K.
  Proof.
    elim: L => //a L ih /=subl.
    case/orP: (leq_total (sec a).+1 (max_elt L)) => [/maxn_idPr -> | /maxn_idPl ->].
    - by apply/ih => q lstn; apply/subl; right.
    by apply/L2SS_melt/subl; left.
  Qed.

  Lemma L2SS_iseg_S a: cancel sec cnt -> a \from L2SS (iseg (sec a).+1).
  Proof. by move => cncl; left. Qed.

  Lemma L2SS_iseg q m:
    q \from L2SS (iseg m) <-> exists n, n < m /\ cnt n = q. 
  Proof.
    split => [ | [n []]]; first exact/iseg_ex; elim: m => // m ih.
    by rewrite leq_eqVlt; case/orP => [/eqP [<-]| ]; [left | right; apply/ih].
  Qed.

  Definition minimal_section:= make_mf (fun (cnt: nat -> Q) (sec : Q -> nat) =>
    cancel sec cnt /\ forall s,(forall m, cnt m = s -> sec s <= m)).
    
  Lemma iseg_base a n: sec \from minimal_section cnt -> a \from L2SS (iseg n) -> sec a < n.
  Proof.
    move => [cncl min]; elim: n => // n ih/=.
    by case => [<- | lstn]; [apply/min | rewrite leqW//; apply/ih].
  Qed.

  Lemma melt_iseg n : sec \from minimal_section cnt -> max_elt (iseg n) <= n.
  Proof.
    move => [cncl min]; elim: n => // n ih /=.
    by rewrite geq_max; apply/andP; split; [apply/min | rewrite leqW].
  Qed.

  Lemma iseg_melt K: sec \from minimal_section cnt -> K \is_sublist_of (iseg (max_elt K)).
  Proof. by move => [cncl min] q lstn; apply/iseg_subl/L2SS_iseg_S/cncl/L2SS_melt. Qed.
End initial_segments.

Lemma leqVlt i j: (i <= j \/ j < i)%nat.
Proof.
  case/orP: (leq_total i j); first by left.
  by rewrite leq_eqVlt; case/orP => [/eqP -> | ]; [left | right].
Qed.

Lemma seg_eq T (cnt cnt': _ -> T) i j:
  (forall k, i <= k <= j -> cnt k = cnt' k) -> segment cnt i j = segment cnt' i j.
Proof.
  case: (leqVlt i j) => [/subnK <- | ineq]; last by rewrite !seg_nil.
  elim: (j - i)%nat => [ass | n ih ass]; first by rewrite !add0n !segnn ass // add0n; apply/andP.
  have ineq: i <= (n + i).+1 by rewrite -addSn; apply/leq_addl.
  rewrite !addSn seg_recr // [RHS]seg_recr //.
  f_equal; last first.
  apply/ih => k /andP [ineq' ineq''].
  by apply/ass /andP; rewrite addSn; split => //; apply /leqW.
  by rewrite !segnn ass //; apply/andP.
Qed.

Local Open Scope name_scope.
Lemma coin_iseg Q A (phi psi: Q -> A) cnt n m:
  n <= m -> phi \coincides_with psi \on (iseg cnt m) -> phi \coincides_with psi \on (iseg cnt n).
Proof. by move => ineq; apply/coin_subl; first apply/iseg_subl/ineq. Qed.

Lemma list_melt Q A (cnt: nat -> Q) (sec: Q -> nat) K (phi psi: Q -> A):
  cancel sec cnt ->
  phi \coincides_with psi \on (iseg cnt (max_elt sec K)) -> phi \coincides_with psi \on K.
Proof.
  move => cncl; apply/coin_subl; elim: K => // q K subl q' /=[-> | lstn].
  - exact/iseg_subl/L2SS_iseg_S/cncl/leq_maxl.
  exact/iseg_subl/subl/lstn/leq_maxr.
Qed.
Local Close Scope name_scope.

Section naturals.
  Lemma seg_iota n k: segment id n (n + k) = rev (iota n k.+1).
  Proof.
    elim: k n => [n | k ih n]; first by rewrite addn0 /segment /= subSn // subnn /= addn0 /rev /=.
    rewrite seg_recl; last exact/leq_addr.
    have ->: rev (iota n k.+2) = rev (iota n.+1 k.+1) ++ [:: n] by rewrite /rev /= -catrev_catr /=.
    rewrite -ih addSn addnS; f_equal.
    by rewrite /segment subSn // subnn /= addn0.
  Qed.

  Lemma seg_map Q (cnt: nat -> Q) n k: segment cnt n (n + k) = map cnt (segment id n (n + k)).
  Proof.
    elim: k => [ | k].
    by rewrite /segment subSn addn0// subnn /=.
    rewrite addnS/segment => ih.
    rewrite subSn /=; first by f_equal; rewrite ih.
    rewrite -addnS.
    exact/leq_addr.
  Qed.

  Definition init_seg:= iseg id.

  Lemma iseg_iota n: init_seg n = rev (iota 0 n).
  Proof. by case: n => //n; rewrite /init_seg iseg_seg seg_iota. Qed.
    
  Lemma iseg_eq T (cnt cnt':nat -> T) n:
    iseg cnt n = iseg cnt' n <-> (forall i, i< n -> cnt i = cnt' i). 
  Proof.
    split.
    elim: n => // n ih /= [eq eq'] i.
      by rewrite leq_eqVlt; case/orP => [/eqP [->] | ]; last exact/ih.
    elim: n => // n ih prp /=.
    rewrite ih => [ | i ineq]; first f_equal; apply/prp => //.
    exact/leqW.
  Qed.

  Lemma leq_bigmax T (F: T -> nat) (K: seq T) i: i \from L2SS K -> (F i <= \max_(i <- K) F i)%nat.
  Proof.
    elim: K => // q K ih /=[-> | lstn]; rewrite big_cons; first exact/leq_maxl.
    exact/leq_trans/leq_maxr/ih.
  Qed.
End naturals.