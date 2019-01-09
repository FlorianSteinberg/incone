From mathcomp Require Import ssreflect seq ssrnat ssrbool eqtype ssrfun choice.
From rlzrs Require Import all_mf.
Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "L '\is_sublist_of' K" := (List.incl L K) (at level 2).

Section sublists.
Context (T: Type).

Lemma subl_refl: Reflexive (@List.incl T).
Proof. by move => L t. Qed.

Lemma subl_trans: Transitive (@List.incl T).
Proof. by move => L K M subl subl' t lstn; apply/subl'/subl. Qed.

Lemma subl0 (L: seq T): L \is_sublist_of [::] -> L = [::].
Proof. by elim: L => // t L ih subl; have []:= subl t; left. Qed.

Lemma drop_subl (L : seq T) n: (drop n L) \is_sublist_of L.
Proof.
elim: n => [ | n ih]; first by rewrite drop0.
rewrite -add1n -drop_drop drop1 => t lstn.
by apply/ih; case: (drop n L) lstn => //; right.
Qed.

Lemma lstn_app (L K: seq T)t: List.In t (L ++ K) <-> List.In t L \/ List.In t K.
Proof.
split; last by have:= List.in_or_app L K t.
elim: L => [ | l L ihL /= [eq | lstn]]; [ | left; left | ] => //.
- by elim: K => // l K ihK /= [eq | lstn]; [right; left | right; right].
by case: (ihL lstn); [ left; right | right ].
Qed.
End sublists.

Lemma lstn_flatten T (Ln: seq (seq T)) t:
  List.In t (flatten Ln) <-> exists L, List.In t L /\ List.In L Ln.
Proof.
split.
- elim: Ln => [| L Ln ih /=]// /lstn_app [lstn | lstn]; first by exists L; split => //; left.
  by have [K []] := ih lstn; exists K; split => //; right.
elim: Ln => [[L []] | L Ln ih [K [lstn /=[-> | lstn']]]]//; apply/lstn_app; first by left.
by right; apply/ih; exists K.
Qed.

Lemma flatten_subl T (Ln Kn: seq (seq T)):
  Ln \is_sublist_of Kn -> (flatten Ln) \is_sublist_of (flatten Kn).
Proof.
move => subl t /lstn_flatten [L [lstn lstn']].
by rewrite lstn_flatten; exists L; split; last apply subl.
Qed.


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

  Lemma size_seg n m: size (segment n m) = m.+1-n.
  Proof. by rewrite /segment; apply size_seg_rec. Qed.

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

  Lemma iseg_ex a n: List.In a (iseg n) -> exists m, m < n /\ cnt m = a.
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
    - by apply/ih => q lstn; apply/subl; right.
    by apply/lstn_melt/subl; left.
  Qed.

  Lemma lstn_iseg_S a: cancel sec cnt -> List.In a (iseg (sec a).+1).
  Proof. by move => cncl; left. Qed.

  Lemma lstn_iseg q m:
    List.In q (iseg m) <-> exists n, n < m /\ cnt n = q. 
  Proof.
    split => [ | [n []]]; first exact/iseg_ex; elim: m => // m ih.
    by rewrite leq_eqVlt; case/orP => [/eqP [<-]| ]; [left | right; apply/ih].
  Qed.

  Definition minimal_section Q (cnt: nat -> Q) (sec : Q -> nat) :=
    cancel sec cnt /\ forall s,(forall m, cnt m = s -> sec s <= m).

  Lemma iseg_base a n: minimal_section cnt sec -> List.In a (iseg n) -> sec a < n.
  Proof.
    move => [cncl min]; elim: n => // n ih/=.
    by case => [<- | lstn]; [apply/min | rewrite leqW//; apply/ih].
  Qed.

  Lemma melt_iseg n : minimal_section cnt sec -> max_elt (iseg n) <= n.
  Proof.
    move => [cncl min]; elim: n => // n ih /=.
    by rewrite geq_max; apply/andP; split; [apply/min | rewrite leqW].
  Qed.

  Lemma iseg_melt K: minimal_section cnt sec -> K \is_sublist_of (iseg (max_elt K)).
  Proof. by move => [cncl min] q lstn; apply/iseg_subl/lstn_iseg_S/cncl/lstn_melt. Qed.
End initial_segments.

Require Import Psatz.

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

  
  (* Most code from this section was provided by Vincent *)
  Context (p: nat -> bool).

  Let Fixpoint searchU m k : nat :=
    match k with
    | 0 => m
    | k'.+1 => let n := m - k in if p n then n else searchU m k'
    end.

  Lemma searchUS m k: k<= m ->
    searchU m.+1 k.+1 = if searchU m k != m then searchU m k else
                          if p m then m else m.+1.
  Proof.
    rewrite /= subSS.
    elim: k => [ | k ih klm]; first by rewrite /= subn0; have ->: m != m = false by apply/eqP.
    rewrite /=.
    case: ifP; first by case: ifP => // /eqP -> ->.
    rewrite subSS ih.
    case: ifP => //.
    by apply/leq_trans/klm.
  Qed.
    
  Let searchU_find m k: k <= m ->
    searchU m k = if has p (iota (m - k) k) then find p (iota (m - k) k) + (m - k) else m.
  Proof.
    elim: k => // k ih ineq.    
    rewrite [LHS]/= ih; last exact/leq_trans/ineq.
    case: ifP => [pmk | ].
    - case: ifP => [_ | ]//; first by rewrite /= pmk add0n.
      rewrite /= => /orP neg.
      by exfalso; apply/neg; left.
    move => pmk.
    rewrite /= subnSK //.
    case: ifP => hs.
    - case: ifP => [_ | /orP neg]; last by exfalso; apply/neg; right.
      by rewrite pmk addSn -addnS subnSK//.
    by case: ifP => // /orP; first by rewrite pmk; case.
  Qed.
    
  Let searchU_correct m k :
    p m -> p (searchU m k).
  Proof.
    move => hm.
    by elim: k => // n ih /=; case: ifP.
  Qed.
    
  Let searchU_le m k :
    searchU m k <= m.
  Proof.
    elim: k => // n ih /=; case: ifP => // _.
    rewrite /subn /subn_rec; apply /leP; lia.
  Qed.    
    
  Let searchU_minimal m k :
    (forall n, p n -> m - k <= n) -> forall n, p n -> searchU m k <= n.
  Proof.
    elim: k.
    - move => h n /=; rewrite -(subn0 m); exact: h.
      move => k ih h n /=; case: ifP.
    - move => _; exact: h.
      move => hk; apply: ih => i hi.
      case: (i =P m - k.+1).
      move => eq.
      rewrite -eq in hk.
      by rewrite hk in hi.
    move: (h i hi).
    by rewrite /subn /subn_rec => /leP prp cnd; apply/leP; lia.
  Qed.

  Let searchU_fail m k:
    (forall n, p n -> m < n) -> searchU m k = m.
  Proof.
    elim: k => //k ih prp /=.
    case: ifP => [pm | neg]; last exact/ih/prp.
    have:= prp (m-k.+1) pm.
    by rewrite ltn_subRL -{2}(add0n m) ltn_add2r.
  Qed.
    
  Definition search n := searchU n n.

  Lemma search_correct n: p n -> p (search n).
  Proof. exact: searchU_correct. Qed.
    
  Lemma search_le n: search n <= n.
  Proof. exact: searchU_le. Qed.

  Lemma search_min n m:	p m -> search n <= m.
  Proof.
    apply searchU_minimal => k pk.
    by rewrite /subn/subn_rec; apply/leP; lia.
  Qed.
    
  Lemma worder_nat:
    (exists n, p n) -> exists n, p n /\ forall m, p m -> n <= m.
  Proof.
    move => [m pm].
    exists (search m ).
    split; first exact: search_correct.
    exact: search_min.
  Qed.

  Lemma not_has_find T q (s: seq T): ~~ has q s -> find q s = size s.
  Proof.
    rewrite has_find => ass.
    suff /leP ineq: size s <= find q s by have /leP ineq':= find_size q s; lia.
    by rewrite leqNgt.
  Qed.

  Lemma search_find n: search n = find p (iota 0 n).
  Proof.
    rewrite /search searchU_find; last exact/leqnn.
    rewrite subnn addn0; case: ifP => //.
    elim: n => // n ih neg.    
    by rewrite not_has_find; [rewrite size_iota | rewrite neg].
  Qed.
    
  Lemma search_fail n: (forall m, p m -> n < m) -> search n = n.
  Proof. exact/searchU_fail. Qed.
    
  Lemma searchS n :
    search n.+1 = if search n != n then search n else if p n then n  else n.+1.
  Proof. by rewrite /search searchUS. Qed.
   
  Lemma search_inc n m: n <= m -> search n <= search m.
  Proof.
    elim: m => [ | m ih].
    by rewrite leqn0 => /eqP ->.
    rewrite leq_eqVlt; case/orP => [ /eqP -> | ineq]//.
    apply/leq_trans; first exact/ih.
    rewrite searchS.
    case: ifP => // /eqP ->.
    by case: ifP.
  Qed.

  Lemma search_eq m n: p m -> (m <= n)%nat -> search m = search n.
  Proof.
    move => pm ineq; apply/eqP; rewrite eqn_leq; apply/andP.
    by split; [apply/search_inc | apply/search_min/search_correct].
  Qed.

End naturals.

Lemma search_ext (p p': pred nat) n:
  (forall k, (k < n)%nat -> p k = p' k) -> search p n = search p' n.
Proof.
  rewrite !search_find => ass.
  apply/eq_in_find => k.
  rewrite mem_iota add0n => /andP [_ ineq].
  exact/ass.
Qed.

Section countTypes.
  Context (Q: countType) (noq: Q) (noq_spec: pickle noq = 0).

  Definition inverse_pickle n:= match pickle_inv Q n with
	                        | Some q => q
	                        | None => noq
                                end.

  Lemma min_ip: minimal_section inverse_pickle pickle.
  Proof.
    rewrite /inverse_pickle; split => [q | q n <-]; first by rewrite pickleK_inv.
    case E: pickle_inv => [a  | ]; last by rewrite noq_spec.
    by have := pickle_invK Q n; rewrite /oapp E => <-.
Qed.
End countTypes.