From mathcomp Require Import ssreflect ssrfun seq ssrnat ssrbool eqtype.
From mf Require Import all_mf classical_mf.
Require Import all_cont classical_count classical_cont minm PhiN FMop Umach Uuniv.
Require Import axioms Classical ChoiceFacts Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section classical_machines.
  Context (Q Q' A A': Type).
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Local Open Scope name_scope.
  
  Lemma sing_cmpt_elt M F n (phi: B) (Fphi: B') q' a': M \evaluates F -> F \is_singlevalued ->
    Fphi \from F phi -> M phi (n,q') = Some a' -> a' = Fphi q'.
  Proof.
    move => comp sing FphiFphi ev.
    have [ | [Mphi MphiFphi] prop]:= (comp phi _); first by exists Fphi.
    have eq: Mphi = Fphi by rewrite -(sing phi Fphi Mphi); last apply prop.
    move: Mphi eq MphiFphi => _ -> MphiFphi.
    pose Nphi := (fun q a => (q <> q' /\ Fphi q = a) \/ (q' = q /\ a' = a)).
    have [q | Mphi Mphiprop]:= @full_choice _ _ Nphi.
    - by case: (classic (q = q')) => ass; [exists a'; right | exists (Fphi q); left].
    have MphiMphi: (\F_M) phi Mphi => [q | ].
    - by case: (Mphiprop q) => [[_ <-] | [<- <-]]; [ | exists n].
    apply Some_inj; case: (Mphiprop q') => [[ctr] | [_ ->]] //.
    by have <-: Mphi = Fphi by apply/ sing; apply prop.
  Qed.

  Lemma exists_po (D: subset B): FunctionalChoice_on (seq (Q * A)) (option B) -> exists po,
        dom (pf2MF po) === dom (projection_on D) /\ (projection_on D) \extends pf2MF po.
  Proof.
    move => choice.
    have /choice [dp prp]: forall KL, exists ophi,
          (KL \from dom (projection_on D) <-> exists phi, ophi = some phi) /\
          forall phi, ophi = some phi -> (projection_on D) KL phi.
    - move => KL.
      case: (classic (KL \from dom (projection_on D))) => [[phi val] | nfd].
      - by exists (some phi); split => [ | phi' [<-]]; first by split; exists phi.
      by exists None; firstorder.
    exists dp.
    split => [KL | KL phi /= val]; last by apply (prp KL).2; case: (dp KL) val => // _ ->.
    rewrite (prp KL).1 /=.
    by split; case => phi eq; [exists phi; case: (dp KL) eq => // _ -> | exists phi; rewrite eq].
  Qed.
End classical_machines.

Section initial_segment_associate.
  Local Open Scope name_scope.
  Context (Q A Q' A': Type). 
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').    
  Context (F: B ->> B').
  Hypothesis F_cont: F \is_continuous.
  Context (dp: (seq (Q * A)) -> option B).
  Hypothesis dp_dom: dom (pf2MF dp) === dom (projection_on (dom F)).
  Hypothesis dp_spec: (projection_on (dom F)) \extends (pf2MF dp).
  Context (cnt: nat -> Q) (sec: Q -> nat).
  Hypothesis ms: minimal_section Q cnt sec.
  Notation minimal_modulus := (minimal_modulus cnt sec).    

  Lemma minm_melt phi mf q': minimal_modulus F phi mf ->
                             max_elt sec (iseg cnt (mf q')) = mf q'.
  Proof.
    move => [md mn].
    by have /leP := mn (iseg cnt (mf q')) q' (md q'); have /leP := melt_iseg (mf q') ms; lia.
  Qed.

  Lemma dp_val KL phi: dp KL = some phi -> phi \from dom F.
  Proof. by move => eq; have [ | ]:= @dp_spec KL phi; first by rewrite /= eq. Qed.

  Lemma dp_icf KL phi:
    dp KL = some phi -> phi \is_choice_for (GL2MF KL).
  Proof.
    by move => eq; have [ | ]:= @dp_spec KL phi; first by rewrite /= eq.
  Qed.

  Lemma dom_dp phi K:
    phi \from dom F -> (F2GL phi K) \from dom (pf2MF dp).
  Proof. by move => phifd; apply/dp_dom; exists phi; split; last apply/icf_GL2MF. Qed.

  Lemma exists_modf:
    FunctionalChoice_on (seq (Q * A)) (Q' -> nat) ->
    FunctionalChoice_on Q' nat ->
    exists Lf, forall KL phi, dp KL = some phi -> minimal_modulus F phi (Lf KL).
  Proof.
    move => choice choice'.
    suff /choice [Lf prp]:
      forall KL, exists Lf, forall phi, dp KL = some phi ->
            minimal_modulus F phi (Lf).
    - by exists Lf.
    move => KL.
    case E: (dp KL) => [phi | ]; last by exists (fun _ => 0).
    have [ | Lf mod]:= (dom_minmod ms F choice' phi).2.
    - by have /cont_spec cont := F_cont; apply/cont/(dp_val E).
    by exists Lf => _ [<-].
  Qed.

  Context (Lf: seq (Q * A) -> (Q' -> nat)).
  Hypothesis mod: forall KL phi, dp KL = some phi -> minimal_modulus F phi (Lf KL).

  Definition n_step phi q' n:=
    match dp (F2GL phi (iseg cnt n)) with
    | Some psi => maxn (Lf (F2GL psi (iseg cnt n)) q') n
    | None => n
    end.
    
  Fixpoint n_rec phi q' n :=
    match n with
    | 0 => 0
    | S n' => n_step phi q' (n_rec phi q' n')
    end.

  Lemma n_rec_dp phi q' n:
    phi \from dom F -> F2GL phi (iseg cnt (n_rec phi q' n)) \from dom (pf2MF dp).
  Proof.    
    move => /dom_dp prp.
    have [psi /= eq]:= prp (iseg cnt (n_rec phi q' n)).
    by exists psi; case E: (dp _) eq => // <-.
  Qed.

  Lemma n_step_le phi q' n:
        n_rec phi q' n <= n_step phi q' (n_rec phi q' n).
  Proof. by rewrite /n_step /=; case E: (dp _) => [psi | ]//; first exact/leq_maxr. Qed.
    
  Lemma n_rec_mon phi q' n: n_rec phi q' n <= n_rec phi q' n.+1.
  Proof. exact/n_step_le. Qed.

  Lemma n_rec_le phi q' n m: n <= m -> n_rec phi q' n <= n_rec phi q' m.
  Proof.
    move /subnK <-; elim: (m - n) => // k ih; rewrite addSn.
    exact/leq_trans/n_rec_mon.
  Qed.
  
  Lemma subl_cat T (K L L': seq T):
    K \is_sublist_of L \/ K \is_sublist_of L' -> K \is_sublist_of (L ++ L').
  Proof. by case => subl q lstn; rewrite L2SS_cat; [left | right]; apply/subl. Qed.

  Lemma n_rec_spec phi q': phi \from dom F -> FunctionalChoice_on Q' nat ->
    exists n, n_rec phi q' n.+1 <= n_rec phi q' n.
  Proof.
    move => phifd choice.
    pose phin:= dp (F2GL phi (iseg cnt (n_rec phi q' _))).
    have [ | Lf' [mod' min]]:= (dom_minmod ms F choice phi).2.
    - by have /cont_spec cont:= F_cont; apply/cont.
    case: (classic (exists n, Lf' q' <= n_rec phi q' n)) => [[n subl] |].
    - exists n; rewrite /= /n_step.
      have [/=]:= n_rec_dp q' n phifd.
      case eq: (dp _) => [psi | ] // _ _.
      rewrite geq_max; apply/andP; split => //.
      have [md mn]:= mod eq.
      apply/leq_trans/melt_iseg/ms.
      have /coin_GL2MF coin:= dp_icf eq.
      have /coin_F2GL -> := coin.
      apply/mn.
      have [a' crt]:= mod' q'.
      exists a' => phi' coin'.
      apply/crt/coin_trans/coin_subl/coin'/iseg_subl/subl.
      exact/coin_subl/coin_sym/coin/iseg_subl/subl.
    have eq: Lf' q' = max_elt sec (iseg cnt (Lf' q')).
    - have /leP := min (iseg cnt (Lf' q')) q' (mod' q').
      by have /leP := melt_iseg (Lf' q') ms; lia.
    move => /not_ex_all_not prp.
    have all: forall n, n_rec phi q' n <= Lf' q'.
    - move => n.
      have nd := prp n.
      rewrite leqNgt; apply/negP => ineq.
      exact/nd/leq_trans/ineq.
    apply/not_all_not_ex => prp'.
    suff ineq: Lf' q' <= n_rec phi q' (Lf' q').
    - by apply/(prp' (Lf' q'))/leq_trans; first exact/all.
    suff this: forall n, n <= n_rec phi q' n by apply/this.
    elim => // n ih.
    rewrite ltnNge; apply/negP => ineq.
    apply/(prp' n).
    exact/leq_trans/ih.
  Qed.

  Definition mod_M phi nq' :=
    let k := n_rec phi nq'.2 nq'.1 in
    if n_step phi nq'.2 k <= k
    then if dp (F2GL phi (iseg cnt k)) then Some (iseg cnt k) else None
    else None.
  
  Lemma M_mod: FunctionalChoice_on Q' nat -> \F_mod_M \modulus_for F.
  Proof.
    move => choice.
    split => [phi phifd | phi mf val q'].
    - apply/FM_dom => q'.
      have [ n ineq]:= n_rec_spec q' phifd choice.
      exists (iseg cnt (n_rec phi q' n)); exists n.
      rewrite /mod_M ineq.
      case: ifP => //=; case E: (dp _) => [ | ]//.
      have := (dp_dom (F2GL phi (iseg cnt (n_rec phi q' n)))).2.
      rewrite /= E => [] [] //.  
      move: phifd => [Fphi val].
      exists phi; split; first by exists Fphi.
      exact/coin_GL2MF/coin_ref.
    have [n]:= val q'.
    rewrite /mod_M /=.
    set K := iseg cnt (n_rec phi q' n).
    case: ifP => //= ineq.
    case: ifP => //; case eq: (dp _) => [psi | ]// _ [<-].
    have /dp_val [Fpsi val'] := eq.
    exists (Fpsi q') => phi' coin Fphi' val''.
    have [md min]:= mod eq.
    have [a' crt]:= md q'.
    have /coin_GL2MF coin':= dp_icf eq.
    have ->:= crt psi _ Fpsi val'; try by apply/coin_ref.
    apply/crt; last exact/val''.
    suff subl': (iseg cnt (Lf (F2GL phi K) q')) \is_sublist_of K.
    - by apply/coin_trans/coin_subl/coin; first apply/coin_subl/coin'.
    apply/iseg_subl/leq_trans/ineq.
    rewrite /n_step eq; have /coin_F2GL -> := coin'.
    exact/leq_maxl.
  Qed.

  Lemma mod_M_mon: mod_M \is_monotone.
  Proof.
    move => phi q' n.
    rewrite /mod_M /=.
    case: ifP => // ineq.
    case: ifP => // eq _.
    suff <-: n_rec phi q' n = n_step phi q' (n_rec phi q' n) by rewrite ineq eq.
    rewrite /n_step.
    case eq: (dp _) eq => [psi | ] // _.
    apply/eqP.
    rewrite eqn_leq; apply/andP; split; first exact/leq_maxr.
    rewrite geq_max; apply/andP; split => //.
    have [md mn]:= mod eq.
    apply/leq_trans/ineq.
    rewrite /n_step eq.
    exact/leq_maxl.
  Qed.

  Lemma exists_valf (somea': A'):
    FunctionalChoice_on (seq (Q * A)) B' ->
    FunctionalChoice_on Q' A' ->
    exists vf, forall KL phi, dp KL = some phi -> F phi (vf KL).
  Proof.
    move => choice choice'.
    suff /choice [Fphi prp]:
      forall KL, exists Fphi, forall phi, dp KL = some phi ->
            F phi Fphi.
    - by exists Fphi.
    move => KL.                
    case E: (dp KL) => [phi | ]; last by exists (fun _ => somea').
    have [Fphi val]: phi \from dom F by have //[]:= @dp_spec KL phi; first by rewrite /= E.
    by exists Fphi => phi' [<-].
  Qed.    

  Context (vf: seq (Q * A) -> B').
  Hypothesis (vl: forall KL phi, dp KL = some phi -> F phi (vf KL)).        

  Definition M phi nq' :=
    let k := n_rec phi nq'.2 nq'.1 in
    if n_step phi nq'.2 k <= k
    then if dp (F2GL phi (iseg cnt k)) then Some (vf (F2GL phi (iseg cnt k)) nq'.2) else None
    else None.

  Lemma M_spec: FunctionalChoice_on Q' nat -> M \evaluates F.
  Proof.
    move => choice phi phifd.
    split => [ | Fphi val].
    - apply/FM_dom => q'.
      have [ n ineq]:= n_rec_spec q' phifd choice.
      exists (vf (F2GL phi (iseg cnt (n_rec phi q' n))) q'); exists n.
      rewrite /M ineq.
      case: ifP => //=; case E: (dp _) => [ | ]// _.
      have := (dp_dom (F2GL phi (iseg cnt (n_rec phi q' n)))).2.
      rewrite /= E => [] [] //.  
      move: phifd => [Fphi val].
      exists phi; split; first by exists Fphi.
      exact/coin_GL2MF/coin_ref.
    move: phifd => [Fphi' val'].
    suff <-: Fphi' = Fphi by trivial.
    apply/functional_extensionality => q'.
    have [n]:= val q'.
    rewrite /M /=.
    set k := n_rec phi q' n.
    case: ifP => //= subl.
    case: ifP => //; case eq: (dp _) => [psi | ]// _ [<-].
    have [dm exte] := M_mod choice.
    have [ | mf md]:= dm phi; first by exists Fphi'.
    have [m eq']:= md q'.
    have eq'': mod_M phi (n, q') = Some (iseg cnt (n_rec phi q' n)) by rewrite /mod_M subl eq /=.
    have /mon_spec mn:= mod_M_mon.
    have eq''': mf q' = iseg cnt (n_rec phi q' n).
      apply/Some_inj.
      case/orP: (leq_total n m) => ineq.                               
      + by rewrite -(mn phi q' (iseg cnt (n_rec phi q' n)) n m ineq) //.
      by rewrite -(mn phi q' (mf q') m n ineq) //.
    move: md => /exte cmod.    
    have [a' crt]:= cmod q'.
    rewrite (crt phi (coin_ref _ _))//.
    symmetry.
    apply/crt/vl/eq; rewrite eq'''.
    by apply/coin_sym/coin_GL2MF/dp_icf.
  Qed.  
  
  Definition nu phi nq' := iseg cnt (n_rec phi nq'.2 nq'.1).

  Lemma n_rec_coin phi psi q' n:
    phi \coincides_with psi \on (iseg cnt (n_rec phi q' n)) -> n_rec phi q' n = n_rec psi q' n.
  Proof.
    elim: n => // n ih coin.
    have coin': phi \coincides_with psi \on (iseg cnt (n_rec phi q' n)).
    - by apply/coin_subl/coin/iseg_subl/n_rec_le.
    rewrite /= /n_step.
    have /coin_F2GL -> := coin'.
    by rewrite ih.    
  Qed.

  Lemma nu_mod_M: nu \modulus_function_for M.
  Proof.
    rewrite /nu /M => phi q' psi coin.
    rewrite /n_step.
    have /coin_F2GL -> := coin.
    by rewrite (n_rec_coin coin).
  Qed.

  Lemma nu_mod_nu: nu \modulus_function_for nu.
  Proof.
    rewrite /nu => phi q' psi coin.
    f_equal; exact/n_rec_coin.
  Qed.

  Lemma M_mon: M \is_monotone.
  Proof.
    move => phi q' n.
    rewrite /M /=.
    case: ifP => // ineq.
    case: ifP => // eq _.
    suff <-: n_rec phi q' n = n_step phi q' (n_rec phi q' n) by rewrite eq ineq.
    rewrite /n_step.
    case eq: (dp _) eq => [psi | ] // _.
    f_equal.
    apply/eqP.
    rewrite eqn_leq; apply/andP; split; first exact/leq_maxr.
    rewrite geq_max; apply/andP; split => //.
    have [md mn]:= mod eq.
    apply/leq_trans/ineq.
    rewrite /n_step eq.
    exact/leq_maxl.
  Qed.

  Lemma nu_mon: monotone_modulus nu.
  Proof. by move => phi q' n; apply/iseg_subl/n_step_le. Qed.

  Definition psi_iseg KLq':=
    let KL := KLq'.1 in let q' := KLq'.2 in
    if Lf KL q' <= size KL
    then inr (vf KL q')
    else inl (segment cnt (size KL) (Lf KL q').-1).

  Lemma map_iseg T T' (f: nat -> T) (g: T -> T') n: map g (iseg f n) = iseg (g \o_f f) n.
  Proof. by elim: n => // n /=<-. Qed.

  Lemma seg_cat_iseg T (cnt': nat -> T) (n k: nat):
    iseg cnt' (n + k.+1) = segment cnt' n (n + k) ++ iseg cnt' n.
  Proof.
    case: n => [ | n]; first by rewrite cats0 iseg_seg.
    rewrite (pred_Sn (n.+1 + k)).
    rewrite iseg_cat_seg // -addnS //.
    rewrite addnS -addSn; apply/leq_addr.
  Qed.

  Lemma iseg_cat_seg T (cnt': nat -> T) (n k: nat):
    n < k -> segment cnt' n k.-1 ++ iseg cnt' n = iseg cnt' k.
  Proof.
    case: n => [ | n]; last exact/iseg_cat_seg.
    by rewrite /=; case: k => // k _ /=; rewrite cats0; symmetry; apply/iseg_seg.
  Qed.

  Lemma zip_iseg (cnt': nat -> A) k:
    zip (iseg cnt k) (iseg cnt' k) = iseg (fun q' => (cnt q', cnt' q')) k.
  Proof. by elim: k => // k /= ->. Qed.

  Lemma size_F2GL (phi: B) K: size (F2GL phi K) = size K.
  Proof. by elim: K => //= q K ->. Qed.

  Lemma zip_F2GL_snd (phi: B) K:
    zip K (map snd (F2GL phi K)) = F2GL phi K.
  Proof. by elim: K => //= q K ->. Qed.

  Lemma gs_psig phi q' k: phi \from dom F ->
    gather_queries psi_iseg phi (k,q') = iseg cnt (n_rec phi q' k).
  Proof.
    move => phifd.
    elim: k => // k.
    rewrite /gather_queries /= /n_step => ih.
    have [ | phi' /=]:= (dp_dom (F2GL phi (iseg cnt (n_rec phi q' k)))).2.
    - by exists phi; split => //; apply/coin_GL2MF/coin_ref.
    case eq: (dp _) => [psi | ]// _.
    case E: (psi_iseg _) => [K | a']; move: E.
    rewrite {1}/psi_iseg /= size_F2GL ih; case: ifP => // ineq [<-].
    - rewrite size_iseg iseg_cat_seg; last first.
      + rewrite leqNgt; apply/negP => ineq'; suff: false by trivial.
        by rewrite -ineq size_iseg.
      f_equal.
      have [ | _ /coin_GL2MF/coin_F2GL ->] //:=
           @dp_spec (F2GL phi (iseg cnt (n_rec phi q' k))) psi; first by rewrite /= eq.
      symmetry; apply/maxn_idPl; rewrite leqNgt; apply/negP => ineq'; suff: false by trivial.
      by rewrite -ineq size_iseg; apply/leq_trans/ineq'.
    rewrite ih /psi_iseg; case: ifP => //=; rewrite size_F2GL size_iseg => ineq [eq'].
    f_equal; symmetry; apply/maxn_idPr.
    by have [ | _ /coin_GL2MF/coin_F2GL ->] //:=
         @dp_spec (F2GL phi (iseg cnt (n_rec phi q' k))) psi; first by rewrite /= eq.
  Qed.
    
  Lemma psi_iseg_spec: FunctionalChoice_on Q' nat -> (U psi_iseg) \evaluates F.
  Proof.
    move => choice phi [Fphi val].
    split => [ | Fphi' /FU_val_spec val']; last first.
    - suff ->: Fphi' = Fphi by trivial.
      apply/fun_ext => q'.
      have [n [/=cns]]:= val' q'.
      rewrite {1}/psi_iseg /=.
      have := gs_psig; rewrite /gather_queries size_F2GL => ->; last by exists Fphi.
      rewrite size_iseg; case: ifP => //.
      set KL := F2GL phi (iseg cnt (n_rec phi q' n)) => ineq [<-].
      have [ | phi' /=]:= (dp_dom KL).2.
      + by exists phi; split; [exists Fphi | apply/icf_GL2MF].
      case eq: (dp _) => [psi | ]// _.
      have [md mn]:= mod eq; have [a' crt]:= md q'.
      have -> //:= crt psi; last exact/vl; last exact/coin_ref.
      symmetry; apply/crt/val.
      have [ | _ /=]:= @dp_spec KL psi; first by rewrite /= eq.      
      rewrite {1}/KL => /coin_GL2MF coin.
      exact/coin_subl/coin/iseg_subl.      
    apply/FM_dom => q'.
    have [ | k ineq']:= @n_rec_spec phi q' _ choice; first by exists Fphi.
    set k' := search (fun k => n_rec phi q' k.+1 <= n_rec phi q' k) k.
    exists (Fphi q').
    exists k'.+1.
    have := @search_correct (fun k => n_rec phi q' k.+1 <= n_rec phi q' k) _ ineq'.
    rewrite -/k' => ineq.
    rewrite US.
    suff ->: U psi_iseg phi (k', q') = None.
    rewrite {1}/psi_iseg /= size_F2GL gs_psig; last by exists Fphi.
    rewrite size_iseg.
    set KL := F2GL phi (iseg cnt (n_rec phi q' k')).
    have [ | phi' /=]:= (dp_dom KL).2.
    - by exists phi; split; [exists Fphi | apply/icf_GL2MF].
    case eq: (dp _) => [psi | ]// _.
    have [md mn]:= mod eq; have [a' crt]:= md q'.
    suff le: Lf KL q' <= n_rec phi q' k'.
    - rewrite le; f_equal.      
      have -> //:= crt psi; last exact/vl; last exact/coin_ref.
      symmetry.
      apply/crt/val.
      have /= := @dp_spec KL psi.
      rewrite eq => [[]]// [Fpsi val'] /coin_GL2MF coin.
      exact/coin_subl/coin/iseg_subl.
    apply/leq_trans/ineq.
    rewrite /= /n_step eq.
    apply/leq_trans/leq_maxl.
    apply/leq_trans/melt_iseg/ms.
    apply/mn; exists a' => psi' coin.
    apply/crt/coin_subl/coin => q lstn.
    by have [ | _ /=/coin_GL2MF/coin_F2GL ->]:= @dp_spec KL psi; first by rewrite /= eq.
  move: {1 5}k' (leqnn k') ineq.
  elim => // m ih lt.
  rewrite US ih // => [ineq | | ]; last first; try by apply/leP; lia.
  - exact/(@search_correct (fun k => n_rec phi q' k.+1 <= n_rec phi q' k)).
  - by apply/leq_trans/lt.  
  rewrite {1}/psi_iseg /=.
  case: ifP => //.
  rewrite gs_psig; try by exists Fphi.
  rewrite size_F2GL size_iseg => le'.
  suff eq: n_rec phi q' m.+1 <= n_rec phi q' m.
  - have /leP:= (@search_min (fun k => n_rec phi q' k.+1 <= n_rec phi q' k)) k _ eq.
    by move/leP: lt; lia.
  rewrite /= /n_step.
  case E: dp => [psi | ]//.
  rewrite geq_max; apply/andP; split => //.
  have [ | _ /coin_GL2MF/coin_F2GL ->] //:= @dp_spec (F2GL phi (iseg cnt (n_rec phi q' m))) psi.
  by rewrite /= E.
Qed.
End initial_segment_associate.  

Section exists_associate.
  Local Open Scope name_scope.
  Context (Q A Q' A': Type).
  Hypothesis Qcount: Q \is_countable.
  Hypothesis Acount: A \is_countable.
  Hypothesis Q'count: Q' \is_countable.
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Context (F: B ->> B').

  Lemma exists_associate: F \is_continuous -> exists psi, (U psi) \evaluates F.
  Proof.
    move => cont.    
    case: (classic (inhabited Q')) => [[someq'] | nex]; last first.
    - exists (fun _ => inl nil) => phi [Fphi val]; split => [ | Fphi' val'].
      + by apply/FM_dom => q'; exfalso; apply/nex/inhabits/q'.
      suff ->: Fphi' = Fphi by trivial.
      by apply/functional_extensionality => q'; exfalso;apply/nex/inhabits/q'.
    case: (classic (inhabited A')) => [[somea'] | nex]; last first.
    - by exists (fun _ => inl nil) => phi [Fphi]; exfalso; apply/nex/inhabits/Fphi/someq'.
    case: (classic (inhabited Q)) => [[someq] | nex]; last first.
    - case: (classic (exists phi, phi \from dom F)) => [[phi [Fphi val]] | nex']; last first.
      + by exists (fun _ => inl nil) => phi phifd; exfalso; apply/nex'; exists phi.
      exists (fun Lq' => inr (Fphi Lq'.2)) => phi' [Fphi' val'].
      split; first by apply/FM_dom => q'; exists (Fphi q'); exists 1.
      move => Fphi'' val''.
      suff ->: Fphi'' = Fphi' by trivial.
      apply/functional_extensionality => q'.      
      have [n eq]:= val'' q'.
      have <-: Fphi q' = Fphi'' q'.
      - elim: n eq => // n ih.
        rewrite US; case E: (U _ _ _) => [b' | ]// []// eq.
        by apply/ih; rewrite -eq.
      have [Lf mod]:= cont phi Fphi val.
      symmetry; apply/mod/val'.
      by case (Lf q') => // q; exfalso; apply/nex/inhabits/q.
    have [ | dp [dp_dom dp_spec]]:= exists_po (dom F).
    - exact/countable_choice/list_count/prod_count/Acount/Qcount.
    have /count_enum/(enum_inh someq) [cnt sur] := Qcount.
    have [sec ms]:= exists_minsec sur.
    have [ | | Lf mod]:= exists_modf cont dp_spec ms.
    - exact/countable_choice/list_count/prod_count/Acount/Qcount.
    - exact/countable_choice.
    have [ | | | vf val]:= exists_valf dp_spec; first exact/somea'.
    - exact/countable_choice/list_count/prod_count/Acount/Qcount.
    - exact/countable_choice.
    exists (psi_iseg cnt Lf vf).
    apply/psi_iseg_spec; try exact/ms; move => //.
    exact/countable_choice.
  Qed. 

  Lemma exists_N: FunctionalChoice_on (seq (Q * A)) (option B) ->
                  exists N, \F_N \tightens (projection_on (dom F)).
  Proof.
    move => choice.
    have [dp [dp_dom dp_spec]]:= exists_po (dom F) choice.
    exists (fun KL nq => if dp KL is Some phi then Some (phi nq.2) else None).
    move => KL /dp_dom [/=]; case val: (dp KL) => [phi | ] // _ _.
    split => [ | phi' /= eq]; first by exists phi => q; exists 0.
    have [| fd icf] := dp_spec KL phi; first by rewrite /= val.
    by have ->: phi' = phi by apply/functional_extensionality => q; have [_ []]:= eq q.
  Qed.
End exists_associate.

(*
Section construct_associate.
  Local Open Scope name_scope.
  Context (Q: eqType) (Q' A A': Type) (somea: A) (someq: Q). 
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Context (M: B -> nat * Q' -> option A').
  Hypothesis M_mon: M \is_monotone.
  Context (mu: B -> nat * Q' -> seq Q).
  Hypothesis mu_mon: monotone_modulus mu.
  Hypothesis mod: mu \modulus_function_for M.
  Hypothesis modmod: mu \modulus_function_for mu.

  Fixpoint GL2LF (KL: seq (Q * A)) q :=
    match KL with
    | nil => nil
    | qa :: KL' => if qa.1 == q then qa.2::(GL2LF KL' q) else (GL2LF KL' q)
    end.

  Lemma filter_ntn (K K': seq Q):
    L2SS (filter (fun q => ~~ (q \in K')) K ++ K') === (L2SS K) \u (L2SS K').
  Proof.
    elim: K => [ | q K /= ih]; first by case: K' => [q /= | q' K' /= q /=]; firstorder.
    by case: ifP => /inP lstn q'; move: (ih q') => /=; firstorder; apply/H1; rewrite -H2.
  Qed.

  Definition Ks_step L nq' Ks :=
    if size (flatten Ks) <= size L
    then Ks
    else
      let KL := zip (flatten Ks) (drop (size L - size (flatten Ks)) L) in
      let K := mu (extend somea (GL2LF KL)) nq' in
      if K == nil then Ks else (K :: Ks).
    
  Fixpoint Ks_rec L nq' m:=
    match m with
    | 0 => nil
    | S m' => Ks_step L nq' (Ks_rec L nq' m')
    end.
  
  Definition get_K L nq' := flatten (Ks_rec L nq' (size L)).
    
  Definition pf_psi KLnq':=
    let KL:= KLnq'.1 in let nq' := KLnq'.2 in
    let K' := mu (extend somea (GL2LF KL)) nq' in
    if check_sublist K' (unzip1 KL)
    then inr (zip K' L)
    else inl K'.

  Fixpoint rm_qqs L :=
    match L with
    | q :: q' :: L' => if (q == someq) && (q' == someq)
                       then ((rm_qqs L').1, (rm_qqs L').2.+1)
                       else (q :: q' :: (rm_qqs L').1, (rm_qqs L').2)
    | L' => (L', 0)
    end.

  Lemma pf_psi_inl L q' K: pf_psi (L,q') = inl K -> K <> nil.
  Proof.
    rewrite /pf_psi; case: ifP =>//= /clP cl [<-].
    by elim: (mu _ _) cl => [subl | q K' ih /= subl]; first by exfalso; apply/subl => q.
  Qed.

  Lemma size_mpsi phi q' n:
    U pf_psi phi (n,q') = None -> n <= size (gather_queries pf_psi phi (n, q')).
  Proof. 
    elim: n => // n ih.
    rewrite US /gather_queries /=.
    case eq: (pf_psi _) => [K | K]; last by case: (U _ _ _).
    case E: (U _ _ _ ) => // _.
    move: eq => /pf_psi_inl.
    case: K => // q K _ /=.
    rewrite size_cat.
    suff: n <= size K + size (flatten (gather_shapes pf_psi phi q' n)) by trivial.
    exact/leq_trans/leq_addl/ih.
  Qed.    

  Lemma mu_nil phi' phi q' n m: n <= m ->
     mu phi' (m, q') = nil -> mu phi (n, q') = nil.
  Proof.
    move => ineq eq.
    have eq': mu phi (m, q') = nil by rewrite -eq; symmetry; apply/modmod; rewrite eq.
    have /monm_spec mon:= mu_mon.
    have := mon phi q' _ _ ineq.
    rewrite eq'.
    case: (mu phi (n, q')) => // q K subl.
    by case: (subl q); left.
  Qed.

  Lemma Ks_step_cat L' L q' Ks:
    size L = size (flatten Ks) ->
    Ks_step (L' ++ L) q' Ks = Ks_step L q' Ks.
  Proof.
    move => sze; rewrite /Ks_step.
    by rewrite size_cat sze leq_addl leqnn.
  Qed.

  Lemma Ks_rec_sze L q' n: Ks_rec L q' n = Ks_rec L q' (size (Ks_rec L q' n)).
  Proof.
    elim: n => // n ih /=.
    rewrite /Ks_step /=.    
    case: ifP => // ineq.
    case: ifP => // nl /=.
    by rewrite -ih /Ks_step ineq nl /=.
  Qed.

  Lemma Ks_rec_cat L q' n m: size L = size (flatten (Ks_rec L q' n)) -> n <= m ->
                             Ks_rec L q' n = Ks_rec L q' m.
  Proof.
    move => sze /subnK <-.
    elim: (m - n) => // k ih.
    by rewrite addSn /= -ih /Ks_step sze leqnn.
  Qed.    
End construct_associate.
*)
Section mathcomp.
  Context (Q Q' A: eqType) (A': Type).
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Local Open Scope name_scope.

  Lemma all_ovrt (P: subset B): countable Q -> countable A -> overt P.
  Proof.
    case: (classic (exists phi, phi \from P)) => [[sp spP] | nex]; last first.
    - by exists (fun _ => None); split => [phi [] | phi phiP]//; exfalso; apply/nex; exists phi.
    move => /prod_count prd {}/prd/list_count count.
    have choice: FunctionalChoice_on (seq (Q * A)) B.
    - by apply/count_eqT_choice; first exact/count; right; apply/inhabits/nil.
    move: count => /count_enum/(enum_inh nil) [cnt sur].
    have /choice [p prp]: forall KL, exists phi, phi \from P /\
          ((exists psi, psi \from P /\ psi \from cylinder KL) -> phi \from cylinder KL).
    - move => KL.
      case: (classic (exists phi, phi \from P /\ phi \is_choice_for (GL2MF KL))) => [ | nex].
      + by move => [phi [phifP icf ]]; exists phi.
      by exists sp.
    exists (Some \o_f p \o_f cnt).
    split => [phi [n /= <-] | phi phifP K]; first by have []:= prp (cnt n).
    exists (p (zip K (map phi K))).
    split; last by have [n /= <-]:= sur (zip K (map phi K)); exists n. 
    apply/coin_sym/coin_GL2MF; apply prp; exists phi; split => //.
    exact/coin_GL2MF/coin_ref.
  Qed.
  
  Lemma exists_dp_count_eqT (F: B ->> B'):
    Q \is_countable -> A \is_countable -> exists dp,
        dom (pf2MF dp) === dom (projection_on (dom F)) /\ (projection_on (dom F)) \extends pf2MF dp.
  Proof.
    move => count count'.
    apply/exists_po/count_eqT_choice; first exact/list_count/prod_count.
    by right; apply/inhabits/nil.
  Qed.
End mathcomp.