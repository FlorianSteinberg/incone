(**
   This file provides a definition of continuity for partial operators F:B -> B' where B = Q -> A
   and B' = Q' -> A' are spaces of functions between concrete types that are considered discrete
   (Q is for questions and A is for answers).
   Partiallity is handled via specification through relations, i.e. the notion is defined for
   a multivalued operator F: B ->> B' in such a way that it implies F to be singlevalued
   (see "cont_sing"). There are specifications of this notion for the more important special
   cases, i.e. if F = PF2MF f comes from a function f: {phi: B | phi \from domain f} -> B' that
   introduces partiality through dependent types (see cont_PF2MF) and if F = F2MF f comes from
   a function directly (see cont_F2MF).
**)
From mathcomp Require Import ssreflect ssrfun seq eqtype ssrnat ssrbool.
From mf Require Import all_mf.
Require Import sets iseg graphs smod.
Require Import Morphisms ChoiceFacts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope name_scope.
Notation determines:= determines.
Section continuity.
  Context (Q A Q' A' : Type).
  (* Q is for questions, A is for answers*)
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  (* B is for Baire space. *)

  Definition certificate (F: B ->> B') K phi := make_mf (fun q' a' =>
    forall psi, phi \and psi \coincide_on K -> determines F psi q' a').

  (**
     This means that the return-value F(phi)(q') is determined from the values of phi on the list
     K and should be read as follows:
   **)
  Local Notation "K '\is_certificate_that' F '\returns' a' '\on_inputs' phi '\and' q'" :=
    (certificate F K phi q' a') (at level 30).

  Context (F: B ->> B').

  (**
     The file "smod.v" introduces a more general concept for subsets instead of lists and names
     it "cert", the two notions are equivalent:
   **)
  Lemma crt_cert L phi: certificate F L phi =~= cert F (L2SS L) phi.
  Proof. by split => crt psi/coin_agre; apply/crt. Qed.

  Lemma crt_exte L K phi: L \is_sublist_of K -> certificate F K phi \extends certificate F L phi.
  Proof. by rewrite !crt_cert => subl; apply/cert_exte. Qed.

  Lemma crt_icf L phi Fphi: Fphi \from F phi -> Fphi \is_choice_for (certificate F L phi).
  Proof.
    move => val q' [a' /crt_cert crt].
    by rewrite crt_cert; apply/cert_icf => //; exists a'.
  Qed.

  (**
     A modulus of continuity of F should return on any inputs phi and q' a certificate, i.e. the
     specification of moduli of continuity of F is given by
   **)
  Definition continuity_modulus := make_mf (fun phi Lf =>
    forall q', exists a', certificate F (Lf q') phi q' a').

  (** 
      note that this specification has a domain that is in general strictly contained in the
      domain of F. Indeed, the domain of continuity modulus contains the domain of F if and only
      if F is continuous (see cont_spec below).
      An inclusion in the other direction is almost never given since an inspection of
      "certificate" shows that it is trivially true for elements outside of the domain of F.
   **)
  Lemma mod_cmod phi Lf:
    Lf \from continuity_modulus phi <-> (LF2MF Lf) \from modulus F phi.
  Proof. by split => mod q'; have [a' /crt_cert crt]:= mod q'; exists a'. Qed.

  Lemma cmod_frcs phi Fphi:
    Fphi \from F(phi) -> phi \from dom continuity_modulus -> forces F phi Fphi.
  Proof.
    move => val [mf].
    rewrite mod_cmod => mod.
    by apply/mod_frcs; try exists (LF2MF mf).
  Qed.

  Definition listfunctions:= make_subset (fun mf => exists Lf, mf = (@LF2MF Q' Q Lf)).

  Lemma cmod_spec:
    (modulus F)|^listfunctions =~= (F2MF (@LF2MF Q' Q)) \o continuity_modulus.
  Proof.
    move => phi mf; rewrite corestr_spec comp_rcmp; last exact/F2MF_tot.
    split => [[[Lf ->] /mod_cmod mod] | [Lf [/mod_cmod mod <-]]]; first by exists Lf.
    by split; first by exists Lf.
  Qed.

  Definition continuous := forall phi Fphi,
      Fphi \from F phi -> exists Lf, forall q', certificate F (Lf q') phi q' (Fphi q').

  Lemma cont_spec: continuous <->
                   dom F \is_subset_of (dom continuity_modulus).
  Proof.
    split => [cont phi [Fphi val] | cont phi Fphi val].
    - have [Lf mod]:= cont phi Fphi val.
      by exists Lf => q'; exists (Fphi q'); apply/mod.
      have [ | Lf mod]:= cont phi; first by exists Fphi.
    by exists Lf => q'; apply/crt_icf/mod.
  Qed.

  (**
     Since "certificate" is trivialy true whenever phi is outside of the domain of F,
     the definition of the set of continuity points of F takes the intersection of the
     domain of the specification of continuity moduli with the domain of F.
   **)
  Definition continuity_points := (dom continuity_modulus) \n (dom F).

  Lemma cont_dom: continuous -> dom F === continuity_points.
  Proof.
    move => /cont_spec cont phi.
    by split => [dm | ]; [split; first exact/cont | case].
  Qed.

  Lemma cont_cntp_spec: continuous <-> continuity_points === dom F.
  Proof. by split => [cont | eq]; [rewrite cont_dom | rewrite cont_spec -eq => phi []]. Qed.
    
  Definition modulus_for mu :=
    dom F \is_subset_of dom mu /\ continuity_modulus \extends mu.

End continuity.
Notation "Lf \is_modulus_of F \on_input phi" := (Lf \from continuity_modulus F phi) (at level 15): name_scope.
Notation "mu \modulus_for F" := (modulus_for F mu) (at level 30): name_scope.
Notation "F '\is_continuous'" := (continuous F) (at level 2): name_scope.

Section continuity_lemmas.
  Context (Q A Q' A' : Type).
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  
  Lemma cmod_F2MF phi Lf (f: B -> B'): Lf \is_modulus_of (F2MF f) \on_input phi <->
    forall q' psi, phi \and psi \coincide_on (Lf q') -> f phi q' = f psi q'.
  Proof.
    rewrite mod_cmod mod_F2MF.
    by split => mod psi q'; [rewrite coin_agre| rewrite -coin_agre]; apply/mod.
  Qed.

  Lemma cmod_exte (F G: B ->> B'):
    G \extends F -> continuity_modulus F \extends continuity_modulus G.
  Proof. by move => exte phi Lf; rewrite !mod_cmod; apply mod_exte. Qed.

  Global Instance cont_prpr: Proper (@equiv B B' ==> iff) (@continuous Q A Q' A').
  Proof.
    move => F F' eq.
    split => cont phi Fphi val.
    - have [ | Lf mod]:= cont phi Fphi; first exact/eq.
      by exists Lf => q' psi coin Fpsi val'; exact/mod/eq/val'.
    have [ | Lf mod] := cont phi Fphi; first exact/eq.
    by exists Lf => q' psi coin Fpsi val'; exact/mod/eq/val'.
  Qed.

  Lemma cont_choice (F: B ->> B'): FunctionalChoice_on Q' (seq Q) -> F \is_continuous <->
    forall phi Fphi, Fphi \from F phi -> forall q', exists L, certificate F L phi q' (Fphi q').
  Proof.
    move => choice; split => cont phi Fphi FphiFphi; first move => q'.
    - by have [Lf mod] := cont phi Fphi FphiFphi; exists (Lf q'); apply/mod.
    by have [Lf mod]:= choice _ (cont phi Fphi FphiFphi); exists Lf.
  Qed.

  Definition continuous_function (f: B -> B'):= forall phi, exists Lf,
        forall q' psi, phi \and psi \coincide_on (Lf q') -> f phi q' = f psi q'.
  Local Notation "f \is_continuous_function" := (continuous_function f) (at level 30): name_scope.

  Lemma cont_F2MF f: (F2MF f) \is_continuous <-> f \is_continuous_function.
  Proof.
    split => [cont phi | cont phi Fphi <-]; last first.
    - by have [Lf mod]:= cont phi; exists Lf => q' psi coin Fpsi <-; symmetry; apply/mod.
    have [ | Lf mod]//:= cont phi (f phi); exists Lf => q' psi coin.
    by symmetry; apply/mod; first exact/coin.
  Qed.

  Lemma cmod_tot (f: B -> B'):
    f \is_continuous_function <-> (continuity_modulus (F2MF f)) \is_total.
  Proof.
    split => [cont phi| tot phi]; last by have [Lf /cmod_F2MF]:= tot phi; exists Lf.
    by have [Lf mod]:= cont phi; exists Lf; apply/cmod_F2MF.
  Qed.
                
  Lemma restr_cont (F: B ->> B') P P':
    P \is_subset_of P' -> F|_P' \is_continuous -> F|_P \is_continuous.
  Proof.
    rewrite !cont_spec => subs cont phi phifd.
    exact/exte_dom/cont/dom_restr_subs/phifd/subs/cmod_exte/exte_restr.
  Qed.

  Lemma restr_cont_w (F: B ->> B') P: F \is_continuous -> F|_P \is_continuous.
  Proof. by move => cont; apply/restr_cont; first exact/subs_all; rewrite -restr_all. Qed.

  Lemma cmod_restr_cont (F: B ->> B'): F|_(dom (continuity_modulus F)) \is_continuous.
  Proof.
    rewrite cont_spec => phi [Fphi [[Lf mod] FphiFphi]].
    exists Lf => q'; have [a' crt]:= mod q'.
    by exists a' => psi coin Fpsi [_ FpsiFpsi]; rewrite (crt psi).
  Qed.

  Lemma restr_dom_cntop (F: B ->> B'): F|_(continuity_points F) \is_continuous.
  Proof. by apply/restr_cont/cmod_restr_cont; move => phi []. Qed.

  Lemma cont_sing (F: B ->> B'): F \is_continuous -> F \is_singlevalued.
  Proof.
    move => /cont_spec cont; apply/sing_spec_mod => phi phifd.
    by have [Lf]:= cont phi phifd; rewrite mod_cmod; exists (LF2MF Lf).
  Qed.

  Lemma cont_exte (F G: B ->> B'):
    G \tightens F -> G \is_continuous -> F \is_singlevalued -> F \is_continuous.
  Proof.
    rewrite !cont_spec => /sing_tight_exte exte cont sing phi phifd.
    exact/exte_dom/cont/exte_dom/phifd/exte/sing/cmod_exte/exte.
  Qed.

  Lemma cnst_cont (Fphi: B'): (cnst Fphi) \is_continuous_function.
  Proof. by move => phi; exists (cnst nil); rewrite /cnst. Qed.

  Lemma tot_tight_exte S T (f g: S ->> T):
    g \is_total -> f \tightens g -> g \extends f.
  Proof. by move => tot tight s t val; apply/(tight_val tight); first exact/tot. Qed.

  Lemma tot_exte_tight S T (f g: S ->> T):
    f \is_total -> g \extends f -> f \tightens g.
  Proof. by move => tot exte s sfd; split => [ | t val]; [exact/tot | exact/exte]. Qed.

  Lemma exte_tight_tot S T (f g: S ->> T):
    f \is_total -> g \is_total -> f \tightens g <-> g \extends f.
  Proof. by move => tot tot'; split; first exact/tot_tight_exte; exact/tot_exte_tight. Qed.

  Definition modulus_function mu (f: B -> B'):=
     forall phi q' psi, phi \and psi \coincide_on (mu phi q') -> f phi q' = f psi q'. 

  Local Notation "mu \modulus_function_for f" := (modulus_function mu f) (at level 30).

  Lemma modf_spec mu f: mu \modulus_function_for f <->
     forall phi, (mu phi) \is_modulus_of (F2MF f) \on_input phi.
  Proof.
    split => [mod phi q' | prp phi q' psi coin].
    - by exists (f phi q') => psi coin _ <-; symmetry; apply/mod.
    by have:= prp phi; rewrite cmod_F2MF => prp'; apply/prp'.
  Qed.
  
  Lemma modl_F2MF mu (f: B -> B'):
    mu \modulus_function_for f <-> (F2MF mu) \modulus_for (F2MF f).
  Proof.
    rewrite modf_spec; split => [mod | [_ mod] phi]; last exact/mod.
    by split => [phi _ | phi _ <-]; [apply/F2MF_tot | apply/mod].
  Qed.
    
  Lemma modf_cont mu (f: B -> B'):
    mu \modulus_function_for f -> f \is_continuous_function.
  Proof. by move => mod phi; exists (mu phi) => q' psi coin; apply/mod. Qed.
  
  Lemma cont_mod (F: B ->> B'): continuous F <-> exists mu, mu \modulus_for F.
  Proof.
    split => [cont | [mu [subs mod]]]; last by apply/cont_spec => phi fd; apply/exte_dom/subs/fd.
    by exists (continuity_modulus F); split; first exact/cont_spec; exact/exte_refl.
  Qed.
End continuity_lemmas.
Notation "f \is_continuous_function":= (continuous_function f) (at level 30): name_scope.
Notation "mu \modulus_function_for f" := (modulus_function mu f) (at level 30): name_scope.

Section composition.
  Context (Q A Q' A' Q'' A'': Type).
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Notation B'' := (Q'' -> A'').
  Context (F: B ->> B') (G: B' ->> B'').

  Fixpoint gather S T (Lf: S -> seq T) (K: seq S) :=
    match K with
    | nil => nil
    | cons q' K' => app (Lf q') (gather Lf K')
    end.
  
  Lemma gather_LF2MF R S T (Lf: S -> seq T) (Lg: R -> seq S):
    LF2MF ((gather Lf) \o_f Lg) =~= (LF2MF Lf) \o_R (LF2MF Lg).
  Proof.
    move => r t /=; elim: (Lg r) => [ | a L ih /=]; first by split => // [[s []]].
    rewrite List.in_app_iff ih; split; last by case => s [[<- | ]]; [left | right; exists s].
    by case => [lstn | [s []]]; [exists a | exists s]; split => //; [left | right].
  Qed.

  Lemma gather_LF2MF_eqfun R S T (Lf: S -> seq T) (Lg: R -> seq S) h:
    (h =1 (gather Lf) \o_f Lg) -> (LF2MF h) =~= (LF2MF Lf) \o_R (LF2MF Lg).
  Proof. by move => eq; rewrite -gather_LF2MF => r t /=; rewrite eq. Qed.

  Lemma cont_comp: F \is_continuous -> G \is_continuous -> (G \o F) \is_continuous.
  Proof.
    rewrite !cont_spec => cont cont' phi phifd.
    have [ | Lf /mod_cmod mod]:= cont phi; first exact/comp_dom/phifd.
    have [GFphi [[Fphi [FphiFphi GFphiGFphi]] _]] := phifd.
    have [ | Lf'/mod_cmod mod']:= cont' Fphi; first by exists GFphi.
    exists (fun q' => gather Lf (Lf' q')); rewrite mod_cmod; apply/mod_exte_mf.
    have/exte_equiv [this _]:= gather_LF2MF Lf Lf'; apply/this.
    exact/mod_comp/mod'.
  Qed.
End composition.

Section partial_functions.
  Context (Q A Q' A' : Type).
  (* Q is for questions, A is for answers*)
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  (* B is for Baire space. *)
  Context (f: partial_function B B').

  Lemma PF2MF_det psi q' a': determines f psi q' a'
                             <-> forall (P: psi \from domain f), f (exist _ psi P) q' = a'.
  Proof.
    split => [det P | eq Fpsi [P <-]]; last exact/eq.
    by apply/det; exists P.
  Qed.

  Lemma cont_PF2MF: f \is_continuous <->
                    forall (phi: domain f), exists Lf, forall q' (psi: domain f),
                          (sval phi) \and (sval psi) \coincide_on (Lf q') -> f psi q' = f phi q'.
  Proof.
    split => [cont phi | prp phi Fphi [phifd <-]].
    - have [ | Lf mod]:= cont (sval phi) (fun q' => f phi q').
      + by case: phi => [phi phifd]; exists phifd.
      exists Lf => q' psi coin.
      apply/mod; first exact/coin.
      by case: psi coin => [psi psifd] _; exists psifd.
    have [Lf mod]:= prp (exist _ phi phifd).
    exists Lf => q' psi coin Fpsi [psifd <-].
    exact/mod.
  Qed.
    
  Lemma cmod_PF2MF phi Lf: Lf \is_modulus_of f \on_input (sval phi) <->
    forall q' psi, (sval phi) \and (sval psi) \coincide_on (Lf q') -> f phi q' = f psi q'.
  Proof.
    rewrite mod_cmod mod_PF2MF.
    by split => mod psi q'; [rewrite coin_agre| rewrite -coin_agre]; apply/mod.
  Qed.
End partial_functions.

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