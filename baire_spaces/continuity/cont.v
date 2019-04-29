(* This file provides a definition of continuity of functions between spaces of the form
Q -> A for some arbitrary types Q and A. It also proves some basic Lemmas about this notion.*)
From mathcomp Require Import ssreflect ssrfun seq.
From mf Require Import all_mf.
Require Import baire iseg smod.
Require Import Morphisms FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope baire_scope.
Notation determines:= determines.
Section continuity.
  Context (Q A Q' A' : Type).
  (* Q is for questions, A is for answers*)
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  (* B is for Baire space. *)
  Context (F: B ->> B').

  Definition LF2MF S T (Lf: S -> seq T):= make_mf (fun s => L2SS (Lf s)).
  
  Definition certificate L phi := make_mf (fun q' a' =>
    forall psi, phi \and psi \coincide_on L -> determines F psi q' a').

  Lemma crt_cert L phi: certificate L phi =~= cert F (L2SS L) phi.
  Proof. by split => crt psi/coin_agre; apply/crt. Qed.

  Lemma crt_exte L K phi: L \is_sublist_of K -> certificate K phi \extends certificate L phi.
  Proof.
    by rewrite !crt_cert => subl; apply/cert_exte; rewrite -L2SS_subs.
  Qed.

  Lemma crt_icf L phi Fphi: F phi Fphi -> Fphi \is_choice_for (certificate L phi).
  Proof.
    move => val q' [a' /crt_cert crt].
    by rewrite crt_cert; apply/cert_icf => //; exists a'.
  Qed.

  Definition continuity_modulus := make_mf (fun phi Lf =>
    forall q', exists a', certificate (Lf q') phi q' a').
  
  Lemma mod_cmod phi Lf:
    continuity_modulus phi Lf <-> modulus F phi (LF2MF Lf).
  Proof. by split => mod q'; have [a' /crt_cert crt]:= mod q'; exists a'. Qed.

  Lemma cmod_frcs phi Fphi mf:
    F phi Fphi -> continuity_modulus phi mf -> forces F phi Fphi.
  Proof. rewrite mod_cmod; exact/mod_frcs. Qed.

  Definition listfunctions:= make_subset (fun mf => exists Lf, mf = (@LF2MF Q' Q Lf)).

  Lemma cmod_spec:
    (modulus F)|^listfunctions =~= (F2MF (@LF2MF Q' Q)) \o continuity_modulus.
  Proof.
    move => phi mf; rewrite corestr_spec comp_rcmp; last exact/F2MF_tot.
    split => [[[Lf ->] /mod_cmod mod] | [Lf [/mod_cmod mod <-]]]; first by exists Lf.
    by split; first by exists Lf.
  Qed.

  Definition continuous := forall phi Fphi,
      F phi Fphi -> exists Lf, forall q', certificate (Lf q') phi q' (Fphi q').

  Lemma cont_spec: continuous <->
                   dom F \is_subset_of (dom continuity_modulus).
  Proof.
    split => [cont phi [Fphi val] | cont phi Fphi val].
    - have [Lf mod]:= cont phi Fphi val.
      by exists Lf => q'; exists (Fphi q'); apply/mod.
      have [ | Lf mod]:= cont phi; first by exists Fphi.
    by exists Lf => q'; apply/crt_icf/mod.
  Qed.

  Definition continuity_points := intersection (dom continuity_modulus) (dom F).

  Lemma cont_dom : continuous -> dom F === continuity_points.
  Proof.
    move => /cont_spec cont phi.
    by split => [dm | ]; [split; first exact/cont | case].
  Qed.
End continuity.
Notation "Lf \is_modulus_of F \on_input phi" := (continuity_modulus F phi Lf) (at level 15): baire_scope.
Notation "F '\is_continuous'" := (continuous F) (at level 2): baire_scope.

Section continuity_lemmas.
  Context (Q A Q' A' : Type).
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  
  Lemma cmod_F2MF phi Lf (f: B -> B'): Lf \is_modulus_of (F2MF f) \on_input phi <->
    forall psi q', phi \and psi \coincide_on (Lf q') -> f phi q' = f psi q'.
  Proof.
    rewrite mod_cmod mod_F2MF.
    by split => mod psi q'; [rewrite coin_agre| rewrite -coin_agre]; apply/mod.
  Qed.

  Lemma cmod_exte (F G: B ->> B'):
    G \extends F -> continuity_modulus F \extends continuity_modulus G.
  Proof. by move => exte phi Lf; rewrite !mod_cmod; apply mod_exte. Qed.

  Global Instance cont_prpr:
    Proper (@equiv B B' ==> iff) (@continuous Q A Q' A').
  Proof.
    move => F F' eq.
    split => cont phi Fphi val.
    - have [ | Lf mod]:= cont phi Fphi; first exact/eq.
      by exists Lf => q' psi coin Fpsi val'; exact/mod/eq/val'.
    have [ | Lf mod] := cont phi Fphi; first exact/eq.
    by exists Lf => q' psi coin Fpsi val'; exact/mod/eq/val'.
  Qed.

  Definition continuous_f (f: B -> B'):= forall phi, exists Lf,
        forall q' psi, phi \and psi \coincide_on (Lf q') -> f phi q' = f psi q'.
  Local Notation "f \is_continuous_function" := (continuous_f f) (at level 30): baire_scope.
  
  Lemma cont_F2MF f: (F2MF f) \is_continuous <-> f \is_continuous_function.
  Proof.
    split => [cont phi | cont phi Fphi <-]; last first.
    - by have [Lf mod]:= cont phi; exists Lf => q' psi coin Fpsi <-; symmetry; apply/mod.
    have [ | Lf mod]//:= cont phi (f phi); exists Lf => q' psi coin.
    by symmetry; apply/mod; first exact/coin.
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

  Lemma restr_dom_cntop (F: B ->> B'):
    F|_(continuity_points F) \is_continuous.
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
End continuity_lemmas.
Notation "f \is_continuous_function":= (continuous_f f) (at level 30): baire_scope.

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