From mathcomp Require Import ssreflect ssrfun seq ssrnat ssrbool eqtype.
From mf Require Import all_mf choice_mf.
Require Import all_cont classical_count classical_cont FMop Umach Ucont Uuniv.
Require Import ClassicalChoice FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section classical_machines.
  Context (Q Q' A A': Type).
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Local Open Scope baire_scope.

  Lemma mach_choice M (phi: B):
	(forall (q': Q'), exists (a': A') n, M n phi q' = Some a') -> phi \from dom \F_M.
  Proof. by move => Rtot; have [Fphi FphiFphi]:= choice _ Rtot; exists Fphi. Qed.

  Lemma sing_cmpt_elt M F c (phi: B) (Fphi: B') q' a': M \evaluates_to F -> F \is_singlevalued ->
    F phi Fphi -> M c phi q' = Some a' -> a' = Fphi q'.
  Proof.
    move => comp sing FphiFphi ev.
    have [ | [Mphi MphiFphi] prop]:= (comp phi _); first by exists Fphi.
    have eq: Mphi = Fphi by rewrite -(sing phi Fphi Mphi); last apply prop.
    move: Mphi eq MphiFphi => _ -> MphiFphi.
    pose Nphi := (fun q a => (q <> q' /\ Fphi q = a) \/ (q' = q /\ a' = a)).
    have [q | Mphi Mphiprop]:= choice Nphi.
    - by case: (classic (q = q')) => ass; [exists a'; right | exists (Fphi q); left].
    have MphiMphi: (\F_M) phi Mphi => [q | ].
    - by case: (Mphiprop q) => [[_ <-] | [<- <-]]; [ | exists c].
    apply Some_inj; case: (Mphiprop q') => [[ctr] | [_ ->]] //.
    by have <-: Mphi = Fphi by apply/ sing; apply prop.
  Qed.

  Lemma FM_dom_spec (psi: seq A * Q' -> seq Q + A') (phi: B):
    phi \from dom \F_(U psi) <-> (communication psi phi) \is_total.
  Proof.
    split => [[Fphi /FU_spec FphiFphi] q' | tot].
    - by have [Ln prp]:= FphiFphi q'; exists (Ln, (Fphi q')).
    have [LnFphi prp]:= choice _ tot.
    exists (fun q' => (LnFphi q').2); rewrite FU_spec => q'.
    by exists (LnFphi q').1; exact/(prp q').
  Qed.

  Lemma exists_listf (somea: A) (cnt: nat -> Q) (F: B ->> B'): cnt \is_surjective ->
     exists listf, forall phi n, phi \from dom F ->
	listf (map phi (iseg cnt n)) \from dom F /\
	(listf (map phi (iseg cnt n))) \and phi \coincide_on (iseg cnt n).
  Proof.
    move => sur; have [sec min]:= exists_minsec sur.
    pose R := make_mf (fun L psiL =>
      (exists phi, phi \from dom F /\ map phi (iseg cnt (size L)) = L) ->
      (psiL \from dom F /\ map psiL (iseg cnt (size L)) = L)).
    have Rtot: R \is_total.
    move => L.
    case: (classic (exists phi, phi \from dom F /\
       (map phi (iseg cnt (size L)) = L))) => [[psil [fd eq]] | neg]; first by exists psil.
    - by exists (fun _ => somea) => cntr; exfalso; apply neg.
    have [listf listfprp]:= choice _ Rtot.
    exists listf => phi n phifd.
    have [ | fd eq]:= listfprp (map phi (iseg cnt n)).
    - by exists phi; split => //; rewrite !size_map !size_iseg.
    move: eq; rewrite size_map size_iseg; split => //; move: fd => _.
    rewrite coin_lstn => q lstn.
    have [m [ineq <-]]:= iseg_ex lstn.
    have: nth (phi (cnt 0)) ([seq listf [seq phi i | i <- iseg cnt n] i | i <- iseg cnt n]) (n - m).-1 =
	  nth (phi (cnt 0)) ([seq phi i | i <- iseg cnt n]) (n - m).-1.
      by rewrite eq.
    rewrite !(nth_map (cnt 0));
     try by case: (n) ineq =>// n' ineq; rewrite size_iseg subSn //=; have: n' - m <= n' by rewrite leq_subr.
    rewrite nth_iseg; suff ->: (n - (n - m).-1).-1 = m by trivial.
    case: n eq ineq lstn => //n eq ineq lstn.
    by rewrite !subSn //; [ rewrite subKn | rewrite leq_subr].
  Qed.

  Lemma M_universal (someq: Q) (somea : A) (somephi': B') (F: B ->> B'):
    Q \is_countable -> F \is_continuous -> exists psiF, (U psiF) \evaluates_to F.
  Proof.
    have [eqQ' _]:= classic_eqClass Q'.
    set Q'eqType:= EqType Q' eqQ'.
    move => [_ [/pfun_spec [pcnt <-] /PF2MF_cotot psur]] cont.
    have [ | | cnt sur]:= (@count_fun Q pcnt); first apply/inhabits/someq; first exact/psur.
    have [Ff Fprop] := exists_choice (F: _ ->>(Q'eqType -> _)) somephi'.
    have [sec ms] := exists_minsec sur.
    have [mf mfmod]:= exists_minmod ms (cont: (F: _ ->> (Q'eqType -> _)) \is_continuous).
    have [listf listfprop] := exists_listf somea (F: _ ->> (Q'eqType -> _)) sur.
    exists (psiF cnt listf mf Ff).
    rewrite mon_eval; last exact/cont_sing; last exact/U_mon.
    move => phi Fphi FphiFphi.
    have phifd: phi \from dom F by exists Fphi.
    apply/(MpsiF_spec phifd) => //; try by move => n; have []:= listfprop phi n phifd.
    - move => q' n ineq.
      have [a' crt]:= mod_minmod ms (mfmod phi phifd) q'.
      rewrite [mf phi q'](crt phi) //.
      have -> //:= crt (listf (map phi (iseg cnt n))) _ (mf (listf (map phi (iseg cnt n)))).
      + have [_ coin]:= listfprop phi n phifd.
        by apply/coin_sym/coin_subl/coin/iseg_subl.
      by apply/mfmod; have []:= listfprop phi n phifd.
    exact/coin_ref.
    exact/mfmod.
    by move => psi psifd; have [mod min]:= mfmod psi psifd.
  Qed.

  Lemma FqM_dom (psi: seq A * Q' -> seq Q + A'):
    dom (\F_(U psi)) === dom (\F_(queriesM psi)). 
  Proof.
    apply/split_set_eq => [phi [Fphi val] | phi [mf /FqM_spec val]].
    - suff ch: (forall q', exists L, exists n, queriesM psi n phi q' = Some L) by apply/(choice _ ch).
      move => q'; have [n eq]:= val q'.
      exists (gather_queries psi n phi q').
      exists n; move: eq; rewrite /U/queriesM.
      by case: (U_rec psi n phi q').
    rewrite FM_dom_spec => q'.  
    have [Qn [a' [com _]]]:= val q'.
    by exists (Qn, a').
  Qed.

  Lemma FsM_dom (psi: seq A * Q' -> seq Q + A'):
    dom (\F_(U psi)) === dom (\F_(shapesM psi)).
  Proof.
    apply/split_set_eq => [phi [Fphi FphiFphi] | phi [sf /FsM_spec val]].
    - suff ch: (forall q', exists L, exists n, shapesM psi n phi q' = Some L) by apply/(choice _ ch).
      move => q'; have [n eq]:= FphiFphi q'.
      exists (build_shapes psi n phi q').
      exists n; move: eq; rewrite /U/shapesM.
      by case: (U_rec psi n phi q').
    rewrite FM_dom_spec => q'.
    have [Qn [a' [com _]]] := val q'.
    by exists (Qn, a').
  Qed.

  Lemma FM_cont_spec:
    exists FqM FsM, forall (psi: seq A * Q' -> seq Q + A') phi,
        dom \F_(U psi) \is_subset_of dom (FqM psi)
        /\
        dom \F_(U psi) \is_subset_of dom (FsM psi)
        /\ (forall qf,
               FqM psi phi qf -> 
               continuity_modulus \F_(U psi) phi qf
               /\
               continuity_modulus (FqM psi) phi qf
               /\
               continuity_modulus (FsM psi) phi qf)
        /\ (forall sf,
               FsM psi phi sf ->
               continuity_modulus (make_mf (fun psi => \F_(U psi) phi)) psi sf
               /\
               continuity_modulus (make_mf (fun psi => (FqM psi) phi)) psi sf
               /\
               continuity_modulus (make_mf (fun psi => (FsM psi) phi)) psi sf).
  Proof.
    exists (fun psi => \F_(queriesM psi)); exists (fun psi => \F_(shapesM psi)) => psi phi.
    split; first by rewrite FqM_dom.
    split; first by rewrite FsM_dom.
    split => [qf mod | sf mod].
    - split; first exact/FqM_mod_FU.
      split; first exact/FqM_mod_FqM.
      exact/FqM_mod_FsM.
    split; first exact/FsM_mod_FU.
    split; first exact/FsM_mod_FqM.
    exact/FsM_mod_FsM.
  Qed.

  Lemma FM_cont (psi: seq A * Q' -> seq Q + A'): \F_(U psi) \is_continuous.
  Proof.
    rewrite cont_spec => phi /FqM_dom [mf mod].
    by exists mf; apply/FqM_mod_FU.
  Qed.

  Lemma FM_sing (psi: seq A * Q' -> seq Q + A'): \F_(U psi) \is_singlevalued.
  Proof. exact/cont_sing/FM_cont. Qed.

  Lemma FM_val_cont (phi: B): (make_mf (fun psi (Fphi: B') => \F_(U psi) phi Fphi)) \is_continuous.
  Proof.
    rewrite cont_spec => psi [Fphi val].
    have [ | sf val']:= (FsM_dom psi phi).1; first by exists Fphi.
    by exists sf; apply/FsM_mod_FU.
  Qed.
End classical_machines.