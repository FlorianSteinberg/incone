(**
   This file defines search functions that take a predicate (p: T -> bool) and given some
   additional information about how to search through the type produce the smallest value where
   the predicate is true. The additonal information can be provided in different ways. Either
   via an iteration procedure rec: T -> T and a starting value or via direct access to the n-th
   element cnt: nat -> T. The former is is called "increasing search", the latter "direct search"
   and its version where cnt may be partial is called "search". All of these are specified
   against the increasing search on naturals where rec is the successor and the start value is 0.
   This search is called "nat_search" and defined first (for historical reasons).

   As compared to the direct search, the increasing search avoids some recomputation when searching
   through a recursively defined sequence. While all of this looks similar to what is done in then
   mathcomp countTypes, no decidable equality is assumed anywhere. While it is still true that
   any increasing search can be expressed by a direct search, for the other direction decidable
   equality would be needed to either extend the rec function from the image of the enumeration to
   a total function or make it functional on a subtype.
**)

From mathcomp Require Import all_ssreflect.
From mf Require Import all_mf.
Require Import graphs iseg sets cont.
Require Import Psatz Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.  


  Lemma not_has_find T q (s: seq T): ~~ has q s -> find q s = size s.
  Proof.
    rewrite has_find => ass.
    suff /leP ineq: size s <= find q s by have /leP ineq':= find_size q s; lia.
    by rewrite leqNgt.
  Qed.

Section nat_search.
  (* Most code from this section was provided by Vincent *)
  Context (p: nat -> bool).

  Fixpoint nat_search_rec m k : nat :=
    match k with
    | 0 => m
    | k'.+1 => let n := m - k in if p n then n else nat_search_rec m k'
    end.

  Lemma nsrchrS m k: k <= m ->
    nat_search_rec m.+1 k.+1 = if nat_search_rec m k != m then nat_search_rec m k else
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
    
  Lemma nsrchr_find m k: k <= m ->
    nat_search_rec m k = if has p (iota (m - k) k) then find p (iota (m - k) k) + (m - k) else m.
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
    
  Lemma nsrchr_correct m k: p m -> p (nat_search_rec m k).
  Proof.
    move => hm.
    by elim: k => // n ih /=; case: ifP.
  Qed.
    
  Lemma nsrchr_le m k: nat_search_rec m k <= m.
  Proof.
    elim: k => // n ih /=; case: ifP => // _.
    rewrite /subn /subn_rec; apply /leP; lia.
  Qed.    

  Lemma nsrchr_ge m k: m - k <= nat_search_rec m k.
  Proof.
    elim: k => [ | k ih /=]; first by rewrite subn0.
    by case: ifP => // fls; apply/leq_trans/ih; rewrite subnS; case: (m - k).
  Qed.

  Lemma nsrchr_min m k :
    (forall n, p n -> m - k <= n) -> forall n, p n -> nat_search_rec m k <= n.
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

  Lemma nsrchr_fail m k:
    (forall n, p n -> m <= n) -> nat_search_rec m k = m.
  Proof.
    elim: k => //k ih prp /=; case: ifP => [pm | neg]; last exact/ih/prp.
    by apply/eqP; rewrite eqn_leq; apply/andP; split; [exact/leq_subr | exact/prp].
  Qed.

  Definition ord_search n := nat_search_rec n n.
    
  Definition nat_search n := nat_search_rec n.+1 n.+1.
  
  Lemma osrch_correct n: p n -> p (ord_search n).
  Proof. exact: nsrchr_correct. Qed.

  Lemma nsrch_correct n: p n -> p (nat_search n).
  Proof.
    move => pn; rewrite /nat_search nsrchrS //.
    by case: ifP => [_ |]; [apply/nsrchr_correct | rewrite pn].
  Qed.
    
  Lemma osrch_le n: ord_search n <= n.
  Proof. exact: nsrchr_le. Qed.

  Lemma nsrch_le n: nat_search n <= n.+1.
  Proof. exact: nsrchr_le. Qed.

  Lemma nsrch_fail n: (forall m, m <= n -> ~ p m) -> nat_search n = n.+1.
  Proof. 
    move => prp.
    apply/nsrchr_fail => k pk.
    rewrite ltnNge; apply/negP => ineq.
    exact/prp/pk.
  Qed.
  
  Lemma osrch_fail n: (forall m: 'I_n, ~ p m) -> ord_search n = n.
  Proof.
    move => prp.
    apply/nsrchr_fail => k pk.
    rewrite leqNgt; apply/negP => lt.
    exact/(prp (Ordinal lt)).
  Qed.

  Lemma osrch_min n m: p m -> ord_search n <= m.
  Proof.
    apply nsrchr_min => k pk.
    by rewrite /subn/subn_rec; apply/leP; lia.
  Qed.
  
  Lemma nsrch_min n m: p m -> nat_search n <= m.
  Proof.
    apply nsrchr_min => k pk.
    by rewrite /subn/subn_rec; apply/leP; lia.
  Qed.
  
  Lemma worder_nat:
    (exists n, p n) -> exists n, p n /\ forall m, p m -> n <= m.
  Proof.
    move => [m pm].
    exists (nat_search m ).
    split; first exact: nsrch_correct.
    exact: nsrch_min.
  Qed.

  Lemma osrch_find n: ord_search n = find p (iota 0 n).
  Proof.
    rewrite /ord_search nsrchr_find; last exact/leqnn.
    rewrite subnn addn0; case: ifP => //.
    elim: n => // n ih neg.    
    by rewrite not_has_find; [rewrite size_iota | rewrite neg].
  Qed.

  Lemma nsrch_find n: nat_search n = find p (iota 0 n.+1).
  Proof.
    rewrite /nat_search nsrchr_find; last exact/leqnn.
    rewrite subnn addn0; case: ifP => //.
    elim: n.+1 => // k ih neg.    
    by rewrite not_has_find; [rewrite size_iota | rewrite neg].
  Qed.

  Lemma osrch_ltP n: reflect (exists m: 'I_n, p m) (ord_search n < n).
  Proof.
    suff P: reflect (exists m, p m /\ m < n) (ord_search n < n).
    - by apply: (iffP idP) => [/P [m [pm lt]] | [[m lt] pm]]; [exists (Ordinal lt) | apply/P; exists m].
    apply: (iffP idP).
    rewrite osrch_find -{2}(size_iota 0 n) -has_find => /hasP [m] .
    by rewrite mem_iota add0n => /andP []; exists m.
    rewrite osrch_find -{3}(size_iota 0 n) -has_find => [[m [pm mln]]]. 
    by apply/hasP; exists m => //; rewrite mem_iota add0n; apply/andP.
  Qed.

  Lemma nsrch_leP n: reflect (exists m,  m <= n /\ p m) (nat_search n <= n).
  Proof.
    apply: (iffP idP) => [ineq | [m [ineq pm]]]; last exact/leq_trans/ineq/nsrch_min.
    have /osrch_ltP [[/=m lt] pm]: ord_search n.+1 < n.+1 by trivial.
    by exists m.
  Qed.

  Lemma osrch_eqP n: reflect (exists m: 'I_n, p m) (ord_search n != n).
  Proof.
    suff P: reflect (ord_search n < n) (ord_search n != n).
    - by apply/(iffP idP) => [/P /osrch_ltP | ex] //; apply/P/osrch_ltP.
    apply/(iffP idP) => [/negP neq | lt]; last by apply/negP => /eqP eq; rewrite eq ltnn in lt.
    rewrite ltnNge; apply/negP => leq.
    by apply/neq; rewrite eqn_leq; apply/andP; split; first exact/osrch_le.
  Qed.

  Lemma nsrch_eqP n: reflect (exists m, m <= n /\ p m) (nat_search n != n.+1).
  Proof.
    apply/(iffP idP) => [/osrch_eqP [[m ineq] pm] | [m [ineq pm]]]; first by exists m.
    by apply/osrch_eqP; suff lt: m < n.+1 by exists (Ordinal lt).
  Qed.

  Lemma osrch_neqS n :
    ord_search n.+1 = if ord_search n != n then ord_search n else if p n then n  else n.+1.
  Proof. by rewrite /ord_search nsrchrS. Qed.

  Lemma osrch_inc n m: n <= m -> ord_search n <= ord_search m.
  Proof.
    elim: m => [ | m ih].
    by rewrite leqn0 => /eqP ->.
    rewrite leq_eqVlt; case/orP => [ /eqP -> | ineq]//.
    apply/leq_trans; first exact/ih.
    rewrite osrch_neqS.
    case: ifP => // /eqP ->.
    by case: ifP.
  Qed.

  Lemma nsrch_inc n m: n <= m -> nat_search n <= nat_search m.
  Proof. by move => ineq; apply/osrch_inc. Qed.

  Lemma osrch_eq n m: p (ord_search n) -> n <= m -> ord_search n = ord_search m.
  Proof.
    move => pm ineq; apply/eqP; rewrite eqn_leq; apply/andP.
    by split; [apply/osrch_inc | apply/osrch_min].
  Qed.

  Lemma nsrch_eq n m: p (nat_search n) -> n <= m -> nat_search n = nat_search m.
  Proof. by move => pn ineq; exact/osrch_eq. Qed.

  Lemma osrch_osrch n: ord_search (ord_search n) = ord_search n.
  Proof.
    suff /negP/leP: ~ ord_search (ord_search n) < ord_search n.    
    - by have /leP:= osrch_le (ord_search n); lia.  
    move => /osrch_ltP [[/=m /leP ineq] pm].
    suff /leP: ord_search n <= m by lia.
    exact/osrch_min.
  Qed.

  Lemma nsrch_nsrch n: ord_search (ord_search n) = ord_search n.
  Proof. exact/osrch_osrch. Qed.

  Lemma osrch_correct_le n m: p n -> n <= m -> p (ord_search m).
  Proof. by move => pn ineq; rewrite -(osrch_eq _ ineq); apply/osrch_correct. Qed.
  
  Lemma nsrch_correct_le n m: p n -> n <= m -> p (nat_search m).
  Proof. by move => pn ineq; rewrite -(nsrch_eq _ ineq); apply/nsrch_correct. Qed.
  
  Lemma osrchP m: reflect (exists k, k <= m /\ p k) (p (ord_search m)).
  Proof.
    apply/(iffP idP) => [pm | [k [le pk]]]; last exact/osrch_correct_le/le.
    by exists (ord_search m); split; first exact/osrch_le.
  Qed.
    
  Lemma osrchS n: ord_search n.+1 = if p (ord_search n) then ord_search n else n.+1.
  Proof.
    rewrite osrch_neqS.
    case: ifP => [/osrch_eqP [[m ineq] pm] | /osrch_eqP fls].
    - by rewrite (osrch_correct_le pm) //; apply/leq_trans/ineq.
    case: ifP => [pn | npn].
    - by rewrite osrch_correct //; symmetry; apply/eqP/osrch_eqP.
    case: ifP => // /osrchP [k [kln pk]].
    exfalso; apply/fls.
    suff lt: k < n by exists (Ordinal lt).
    move: kln; rewrite leq_eqVlt; case/orP => // /eqP eq.
    by have: false by rewrite -npn -eq.
  Qed.    

  Lemma nsrchS n: nat_search n.+1 = if p (nat_search n) then nat_search n else n.+2.
  Proof. exact/osrchS. Qed.
End nat_search.

Section nat_search_lemmas.
  Lemma nsrchr_or p p' m k:
    nat_search_rec (fun k => p k || p' k) m k = minn (nat_search_rec p m k) (nat_search_rec p' m k).
  Proof.
    elim: k => [ | k /= ->]; first by rewrite minnn.
    case: ifP => [/orP | /negP/negP]; last first.
    - rewrite Bool.negb_orb => /andP [].
      by case: (p _) => // _; case: (p' _).
    case => [-> | ->].
    - case: ifP => _; first by rewrite minnn.
      symmetry; apply/minn_idPl.
      by apply/leq_trans/nsrchr_ge; rewrite subnS; case: (m - k).
    case: ifP => _; first by rewrite minnn.
    symmetry; apply/minn_idPr.
    by apply/leq_trans/nsrchr_ge; rewrite subnS; case: (m - k).
  Qed.

  Lemma osrch_cont p p' n:
    (forall k, k <= ord_search p n -> p k = p' k) -> ord_search p n = ord_search p' n.
  Proof.
    elim: n => [ | n ih prp] //.
    have eq: ord_search p n = ord_search p' n.
    - by apply/ih => k ineq; apply/prp/leq_trans/osrch_inc/leqW/leqnn.
    rewrite !osrch_neqS ih; last by move => k ineq; apply/prp/leq_trans/osrch_inc/leqW/leqnn.
    case: ifP => // /eqP eq'.
    rewrite prp // -{1}eq' -eq.
    exact/osrch_inc.
  Qed.

  Lemma nsrch_cont p p' n:
    (forall k, k <= nat_search p n -> p k = p' k) -> nat_search p n = nat_search p' n.
  Proof. exact/osrch_cont. Qed.

  Lemma osrch_ext (p p': pred nat) n:
    (forall k: 'I_n, p k = p' k) -> ord_search p n = ord_search p' n.
  Proof.
    rewrite !osrch_find => ass.
    apply/eq_in_find => k.
    rewrite mem_iota add0n => /andP [_ ineq].
    exact/(ass (Ordinal ineq)).
  Qed.

  Lemma nsrch_ext (p p': pred nat) n:
    (forall k, k <= n -> p k = p' k) -> nat_search p n = nat_search p' n.
  Proof.
    by move => prp; apply/osrch_ext; case => m ineq; apply/prp.
  Qed.

  Global Instance osrch_prpr: Proper (@eqfun bool nat ==> eq ==> eq) ord_search.
  Proof. by move => p p' eq n _ <-; apply/osrch_ext/eq. Qed.

  Global Instance nsrch_prpr: Proper (@eqfun bool nat ==> eq ==> eq) nat_search.
  Proof. by move => p p' eq n _ <-; apply/osrch_ext/eq. Qed.

  Lemma osrch_weaken (p p': pred nat) n:
    (forall n, p n -> p' n) -> ord_search p' n <= ord_search p n.
  Proof.
    move => imp.
    case pn: (p (ord_search p n)); first by apply/osrch_min/imp; rewrite pn.
    move: pn => /osrchP neq; rewrite leqNgt; apply/negP => lt.
    have/osrch_ltP [[k ineq] pk]: ord_search p n < n by apply/leq_trans/osrch_le; first exact/lt.
    by apply/neq; exists k; split => //; apply/leq_trans/ineq.
  Qed.

  Lemma nsrch_weaken (p p': pred nat) n:
    (forall n, p n -> p' n) -> nat_search p' n <= nat_search p n.
  Proof. exact/osrch_weaken. Qed.

  Lemma osrch_or p p' n:
    ord_search (fun k => p k || p' k) n = minn (ord_search p n) (ord_search p' n).
  Proof. exact/nsrchr_or. Qed.

  Lemma nsrch_or p p' n:
    nat_search (fun k => p k || p' k) n = minn (nat_search p n) (nat_search p' n).
  Proof. exact/nsrchr_or. Qed.

  Lemma osrch_orl (p p': pred nat) n:
    p (ord_search p' n) -> ord_search (fun k => p k || p' k) n = ord_search p n.
  Proof. by move => pn; rewrite osrch_or; apply/minn_idPl/osrch_min. Qed.

  Lemma nsrch_orl (p p': pred nat) n:
    p (nat_search p' n) -> nat_search (fun k => p k || p' k) n = nat_search p n.
  Proof. by move => pn; rewrite nsrch_or; apply/minn_idPl/nsrch_min. Qed.
End nat_search_lemmas.

Section increasing_search.
  Context T (step: T -> T). 
  Context (p: T -> bool).

  Fixpoint increasing_search start k :=
    match k with
    | 0 => start
    | k'.+1 => let t := start in if p t then t else increasing_search (step start) k'
    end.

  Fixpoint cnt start n:=
    match n with
    | 0 => start
    | S n' => step (cnt start n')
    end.

  Lemma cntr start n: step (cnt start n) = cnt (step start) n.
  Proof. by elim: n => //= n ->. Qed.
    
  Lemma cntS start n: step (cnt start n) = cnt start n.+1.
  Proof. by elim: n => //= n ->. Qed.
   
  Lemma isrch_nsrchr start m k: k <= m ->
    increasing_search (cnt start (m - k)) k = cnt start (nat_search_rec (fun n => p (cnt start n)) m k).
  Proof.
    elim: k start m => [start m | k ih /= start m klm]; first by rewrite subn0.
    by case: ifP => // fls; rewrite cntS -subSn // subSS ih //; apply/leq_trans/klm.
  Qed.

  Lemma isrch_osrch start k:
      increasing_search start k = cnt start (ord_search (fun n => p (cnt start n)) k).
  Proof. by rewrite /nat_search -isrch_nsrchr // subnn. Qed.  

  Lemma isrch_eq start n m:
    p (increasing_search start n) -> n <= m ->
    increasing_search start n = increasing_search start m.
  Proof. by rewrite !isrch_osrch => pn ineq; f_equal; apply/osrch_eq. Qed.  

  Lemma isrchS start n:
    increasing_search start n.+1 = if p (increasing_search start n)
                                   then increasing_search start n
                                   else cnt start n.+1.
  Proof. by rewrite !isrch_osrch osrchS; case: ifP. Qed.

  Lemma isrch_cnt start n:
    (forall m, p (cnt start m) -> n <= m) -> increasing_search start n = (cnt start n).
  Proof.
    rewrite isrch_osrch => prp; pose p' n := p (cnt start n).
    suff/osrch_eqP/eqP ->: ~ exists m: 'I_n, p' m by trivial.
    by move => [[/=m ineq] pm]; move: ineq; rewrite ltnNge => /negP fls; apply/fls/prp.
  Qed.

  Lemma isrch_correct start n: p (cnt start n) -> p (increasing_search start n).
  Proof. by rewrite isrch_osrch => pn; apply/(@osrch_correct (fun k => p (cnt start k))). Qed.

  Lemma isrch_correct_le start n m: p (cnt start n) -> n <= m -> p (increasing_search start m).
  Proof. by rewrite isrch_osrch => pn; apply/(@osrch_correct_le (fun k => p (cnt start k))). Qed.

  Lemma isrchP start n: reflect (exists m, p (cnt start m) /\ m <= n) (p (increasing_search start n)).
  Proof.
    apply/(iffP idP) => [pm | [m [pm ineq]]]; last exact/isrch_correct_le/ineq.
    by exists (ord_search (fun k => p (cnt start k)) n); split; [rewrite -isrch_osrch|apply/osrch_le].
  Qed.
End increasing_search.

Lemma osrch_isrch p k: ord_search p k = increasing_search S p 0 k.
Proof.
  have := isrch_nsrchr S p 0 (leqnn k).
  rewrite subnn /= => ->.
  suff eq: forall n, cnt S 0 n = n by rewrite eq; apply/osrch_ext; case => [k' ineq]; rewrite eq.
  by elim => // n /= ->.
Qed.

Lemma nsrch_isrch p k: nat_search p k = increasing_search S p 0 k.+1.
Proof. by rewrite -osrch_isrch. Qed.
  
Section direct_search.
  Context T (cnt: nat -> T).
  Context (p: T -> bool).

  Fixpoint direct_search_rec m k :=
    match k with
    | 0 => None
    | k'.+1 => let t := cnt (m - k) in if p t then Some t else direct_search_rec m k'
    end.

  Lemma dsrchr_nsrchr m k:
    direct_search_rec m.+1 k.+1 = let n := nat_search_rec (fun n => p (cnt n)) m k in
                            if  p (cnt n) then Some (cnt n) else None.
  Proof. by rewrite /= subSS; elim: k => /=[ | k ih]; [rewrite subn0 | case: ifP => // ->]. Qed.

  Definition direct_search k := direct_search_rec k.+1 k.+1.  

  Lemma dsrch_osrch k:
    direct_search k = let t := cnt (ord_search (p \o_f cnt) k) in
                      if p t then Some t else None.
  Proof. exact/dsrchr_nsrchr. Qed.
    
  Lemma dsrch_nsrch k:
    direct_search k = let n:= nat_search (p \o_f cnt) k in
                      if n == k.+1 then None else Some (cnt n).
  Proof.
    have ->: nat_search (p \o_f cnt) k = ord_search (p \o_f cnt) k.+1 by trivial.
    rewrite dsrch_osrch/= osrchS /= //; case: ifP => //; last by rewrite eq_refl.
    by case: ifP => // /eqP eq; have:= @osrch_le (p \o_f cnt) k; rewrite eq ltnn.
  Qed.

  Lemma dsrchS k: direct_search k.+1 =
                  if direct_search k is Some t
                  then Some t
                  else if p (cnt k.+1)
                       then Some (cnt k.+1)
                       else None.
  Proof.
    rewrite !dsrch_osrch osrchS /=.
    case: ifP; first by case: ifP => // _ ->.
    by case: ifP => [-> | _ ->]//.
  Qed.
  
  Lemma dsrch_correct k t: direct_search k = some t -> p t.
  Proof. by rewrite dsrch_osrch /=; case: ifP => // pk [<-]. Qed.
    
  Lemma dsrch_le k t: direct_search k = Some t -> exists l, l <= k /\ t = cnt l.
  Proof.
    rewrite dsrch_osrch /=; case: ifP => // pk [<-].
    by exists (ord_search (p \o_f cnt) k); split => //; apply/osrch_le.
  Qed.    

  Lemma dsrch_min k: p (cnt k) -> exists l, l <= k /\ direct_search k = Some (cnt l).
  Proof.
    rewrite dsrch_osrch /= => pt; exists (ord_search (fun k => p (cnt k)) k).
    by split; [apply/osrch_le | rewrite (@osrch_correct (fun k => p (cnt k)))].
  Qed.
    
  Lemma dsrch_someP k: reflect (exists l, l <= k /\ p (cnt l)) (direct_search k).
  Proof.
    by apply: (iffP idP); rewrite dsrch_osrch /=; case: ifP => // /(@osrchP (p \o_f cnt)).
  Qed.

  Lemma dsrch_val k l: l <= k -> p (cnt l) -> (forall m, p (cnt m) -> l <= m) ->
                       direct_search k = Some (cnt l).
  Proof.
    rewrite dsrch_osrch => ineq pl prp /=; case: ifP => [pk | npk]; last first.
    - by have: false by rewrite -npk; apply/(@osrch_correct_le (p \o_f cnt))/ineq.
    do 2 f_equal; have <-:= @osrch_eq (p \o_f cnt) _ _ _ ineq; last exact/osrch_correct.
    by apply/eqP/osrch_eqP => [[[m/=]]]; rewrite ltnNge => /negP fls pm; apply/fls/prp.
  Qed.  
    
  Lemma dsrch_failP k: reflect (forall m, p (cnt m) -> k < m) (~~ direct_search k).
  Proof.
    apply(iffP idP) => [/dsrch_someP nex m pm | prp].
    - by rewrite leqNgt; apply/negP => ineq; apply/nex; exists m.
    apply/dsrch_someP; case => l []; rewrite leqNgt => [/negP ineq pt].
    exact/ineq/prp.
  Qed.

  Lemma dsrch_None_spec k: (forall m, m <= k -> ~ p (cnt m)) <-> direct_search k = None.
  Proof.
    split => [ prp | eq m ineq pm]; last by have: @None T by rewrite -eq; apply/dsrch_someP; exists m.
    suff: ~~ direct_search k by case: direct_search => //.
    by apply/dsrch_someP; case => l [ineq pl]; apply/prp/pl.
  Qed.

  Lemma dsrch_noval k:
    (forall l, p (cnt l) -> k < l) -> direct_search k = None.
  Proof.
    move => prp; apply/dsrch_None_spec => m ineq pm.
    suff: k < m by rewrite ltnNge ineq.
    exact/prp/pm.
  Qed.
    
  Lemma dsrch_eqS k l: p (cnt k) -> k <= l -> direct_search k = direct_search l.
  Proof.
    rewrite !dsrch_osrch /= => pk ineq.
    rewrite (@osrch_eq (p \o_f cnt) _ _ _ ineq) //.
    exact/(@osrch_correct (p \o_f cnt)).
  Qed.

  Lemma dsrch_eq k l t: k <= l -> direct_search k = Some t -> direct_search l = Some t.
  Proof.
    move => ineq; rewrite !dsrch_osrch /=; case: ifP => // pk [<-].
    by rewrite -(@osrch_eq (p \o_f cnt) _ _ _ ineq) // pk.
  Qed.
End direct_search.  
Arguments dsrch_val: clear implicits.
Arguments dsrch_val {T} {cnt} {p} {k}.
    
Section search.
  Context T (cnt: nat -> option T).
  Context (p: T -> bool).

  Definition search k :=
    match direct_search cnt (fun ot => if ot is Some t then p t else false) k with
    | Some (Some t) => Some t
    | _ => None
    end. 

  Lemma dsrch_not_Some_None k:
    direct_search cnt (fun ot => if ot is Some t then p t else false) k <> Some None.
  Proof. by rewrite dsrch_osrch /=; case: ifP; first case: cnt. Qed.

  Lemma srchS k: search k.+1 =
                  if search k is Some t
                  then Some t
                  else if cnt k.+1 is Some t
                       then if p t then Some t else None
                       else None.
  Proof.
    rewrite /search dsrchS /=.
    case ds: direct_search => [ot | ]; first by case: ot ds => // /dsrch_not_Some_None //.
    by case eq: cnt => [t | ]//; case: ifP => //.
  Qed.
      
  Lemma srch_correct k t: search k = some t -> p t.
  Proof.
    rewrite /search; case ds: direct_search => [[ | ] | ]// => [[<-]].
    by have := dsrch_correct ds.
  Qed.
    
  Lemma srch_le k t: search k = Some t -> exists l, l <= k /\ cnt l = Some t /\ p t.
  Proof.
    rewrite /search; case ds: direct_search => [[ | ] | ]// => [[<-]].
    have pt := dsrch_correct ds.
    have [l [ineq eq]]:= dsrch_le ds.
    by exists l; split => //; split => //.
  Qed.

  Lemma srch_min k t: cnt k = Some t -> p t -> exists l, l <= k /\ search k = cnt l.
  Proof.
    move => eq pt.
    have [ | l [ineq ds]]:= @dsrch_min _ cnt (fun ot => if ot is some t then p t else false) k.
    - by rewrite eq pt.
    exists l; split => //.
    rewrite /search ds.
    have := dsrch_correct ds.
    by case: cnt.
  Qed.
      
  Lemma srch_eqS k l t: cnt k = Some t -> p t -> k <= l -> search k = search l.
  Proof. by move => eq pt ineq; rewrite /search (@dsrch_eqS _ _ _ _ l) // eq. Qed.

  Lemma srch_eq k l t: k <= l -> search k = Some t -> search l = Some t.
  Proof.
    move => ineq; rewrite /search.
    case ds: direct_search => [ot | ]//.
    by rewrite (dsrch_eq _ ds).
  Qed.    
End search.    

Section eqTypes.
  Lemma mem_segP (T: eqType) i j (Delta: _ -> T) x:
    reflect (exists k, i <= k <= j /\ x = Delta k) (x \in (segment Delta i j)).
  Proof.
    apply/(iffP idP) => [ | [k [/andP [ineq ineq'] eq]]].
    - case: (leqVlt i j) => [/subnK <- | ineq]; last by rewrite seg_nil.
      rewrite addnC seg_map seg_iota => /mapP [k].
      rewrite mem_rev mem_iota addnS => /andP [ineq ineq'] ->.
      by exists k; split; first apply/andP.
    have /subnK <-: (i <= j)%nat by apply/leq_trans/ineq'.
    rewrite addnC seg_map seg_iota; apply/mapP; exists k => //.
    rewrite mem_rev mem_iota; apply/andP; split => //.
    by rewrite addnS addnC; have /subnK ->: (i <= j)%nat by apply/leq_trans/ineq'.      
  Qed.
End eqTypes.

Section countTypes.
  Context (Q: countType) (noq: Q) (noq_spec: pickle noq = 0).

  Definition inverse_pickle n:= match @pickle_inv Q n with
	                        | Some q => q
	                        | None => noq
                                end.

  Lemma min_ip: pickle \from minimal_section Q inverse_pickle.
  Proof.
    rewrite /inverse_pickle; split => [q | q n <-]; first by rewrite pickleK_inv.
    case E: pickle_inv => [a  | ]; last by rewrite noq_spec.
    by have := @pickle_invK Q n; rewrite /oapp E => <-.
  Qed.
End countTypes.
