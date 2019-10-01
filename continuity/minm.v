From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq choice ssrfun.
From mf Require Import all_mf.
Require Import graphs iseg sets cont.
Require Import Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section search.
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

  Lemma searchP n: reflect (exists m, p m /\ m < n) (search n < n).
  Proof.
    apply: (iffP idP).
    rewrite search_find -{2}(size_iota 0 n) -has_find => /hasP [m] .
    by rewrite mem_iota add0n => /andP []; exists m.
    rewrite search_find -{3}(size_iota 0 n) -has_find => [[m [pm mln]]]. 
    by apply/hasP; exists m => //; rewrite mem_iota add0n; apply/andP.
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

  Lemma search_search n: search (search n) = search n.
  Proof.
    suff /negP/leP: ~ search (search n) < search n.    
    - by have /leP:= search_le (search n); lia.  
    move => /searchP [m [pm /leP ineq]].
    suff /leP: search n <= m by lia.
    exact/search_min.
  Qed.
End search.
  
Lemma search_ext (p p': pred nat) n:
  (forall k, (k < n)%nat -> p k = p' k) -> search p n = search p' n.
Proof.
  rewrite !search_find => ass.
  apply/eq_in_find => k.
  rewrite mem_iota add0n => /andP [_ ineq].
  exact/ass.
Qed.

Lemma search_cont p n p':
  (forall k, k <= search p n -> p k = p' k) -> search p n = search p' n.
  Proof.
  elim: n => [ | n ih prp] //.
  have eq: search p n = search p' n.
  - by apply/ih => k ineq; apply/prp/leq_trans/search_inc/leqW/leqnn.
  rewrite !searchS ih; last by move => k ineq; apply/prp/leq_trans/search_inc/leqW/leqnn.
  case: ifP => // /eqP eq'.
  rewrite prp // -{1}eq' -eq.
  exact/search_inc.
Qed.

Section eqTypes.
  Lemma mem_segP (T: eqType) i j (Delta: _ -> T) x:
    reflect (exists k, (i <= k <= j)%nat /\ x = Delta k) (x \in (segment Delta i j)).
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

  Definition inverse_pickle n:= match pickle_inv Q n with
	                        | Some q => q
	                        | None => noq
                                end.

  Lemma min_ip: pickle \from minimal_section Q inverse_pickle.
  Proof.
    rewrite /inverse_pickle; split => [q | q n <-]; first by rewrite pickleK_inv.
    case E: pickle_inv => [a  | ]; last by rewrite noq_spec.
    by have := pickle_invK Q n; rewrite /oapp E => <-.
  Qed.
End countTypes.

Local Open Scope name_scope.

Section minimal_modulus.
  Context (Q Q' A A': Type).
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Context (F: B ->> B').
  Context (cnt: nat -> Q).
  Context (sec: Q -> nat).
  Notation init_seg := (iseg cnt).
  Notation max_elt := (max_elt sec).

  Definition minimal_modulus S T (F: B ->> (S -> T)) := make_mf (fun phi mf =>
	((fun q' => init_seg (mf q')) \is_modulus_of F \on_input phi)
	/\
	forall L q', (exists a', certificate F L phi q' a') -> mf q' <= max_elt L).
  
  Lemma cntp_spec: continuity_points F === dom (continuity_modulus F)|_(dom F).
  Proof.
   by move => phi; split => [[] | [Fphi] []]; [rewrite dom_restr_spec | split; first by exists Fphi].
  Qed.
End minimal_modulus.

Section minimal_moduli.
  Context (Q': eqType) (Q A A': Type).
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Local Open Scope name_scope.
  Context (F: B ->> B'). 
  Context (cnt: nat -> Q).
  Context (sec: Q -> nat).
  Hypothesis (ms: minimal_section Q cnt sec).
  Notation init_seg := (iseg cnt).
  Notation max_elt := (max_elt sec).
  Notation minimal_modulus := (minimal_modulus cnt sec).

  Lemma mod_minm phi mf: (minimal_modulus F) phi mf ->
    (fun q' => init_seg (mf q')) \is_modulus_of (minimal_modulus F) \on_input phi.
  Proof.
    move => [mod min] q'.
    exists (mf q') => psi coin mf' [mod' min'].
    have ineq: mf' q' <= mf q'.
    - apply/leq_trans/melt_iseg/ms/min'; have [a' crt]:= mod q'.
      by exists a' => phi' coin'; apply/crt/coin_trans/coin'.
    apply/eqP; rewrite eqn_leq; apply/andP; split => //.
    apply/leq_trans/melt_iseg/ms/min.
    have [a' crt] := mod' q'; exists a' => phi' coin'.
    exact/crt/coin_trans/coin'/coin_subl/coin_sym/coin/iseg_subl.
  Qed.

  Lemma minm_cont: (minimal_modulus F) \is_continuous.
  Proof.
    move => phi mf mod; exists (fun q' => init_seg (mf q')) => q'.    
    exact/crt_icf/mod_minm.
  Qed.

  Lemma minm_modmod mu:
    (forall phi, phi \from dom F -> minimal_modulus F phi (mu phi)) ->
    ((F2MF (fun phi q' => init_seg (mu phi q')))|_(dom F)) \modulus_for (minimal_modulus F)|_(dom F).
  Proof.
    move => prp.
    split => [phi [mf [mod phifd]] | phi _ [phifd <-] q'].
    - by exists (fun q' => init_seg (mu phi q')).
    have [n crt]:= mod_minm (prp phi phifd) q'.
    exists n => psi coin Fpsi [psifd val]. 
    exact/crt/val.
  Qed.    
End minimal_moduli.