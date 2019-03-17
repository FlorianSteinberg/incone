(* This file provides a definition of continuity of functions between spaces of the form
Q -> A for some arbitrary types Q and A. It also proves some basic Lemmas about this notion.*)
From mathcomp Require Import ssreflect ssrfun seq.
From mf Require Import all_mf.
Require Import baire.
Require Import Morphisms FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section smodulus.
Context (Q A Q' A' : Type).
(* Q is for questions, A is for answers*)
Notation B := (Q -> A).
Notation B' := (Q' -> A').
(* B is for Baire space. *)
Context (F: B ->> B').

Definition determines phi := make_mf (fun q' a' =>
	forall Fphi, F phi Fphi -> Fphi q' = a').

Global Instance det_prpr: Proper (@eqfun A Q ==> @equiv Q' A') determines.
Proof.
move => phi psi eq q' a'.
by have ->: phi = psi by apply functional_extensionality => q; rewrite eq.
Qed.

Lemma det_val_sing phi: phi \from dom F -> (determines phi) \is_singlevalued.
Proof.
by move => [Fphi FphiFphi] q' a' b' detq'a' detq'b'; rewrite -(detq'a' Fphi) // -(detq'b' Fphi).
Qed.

Definition determined := make_subset (fun phi => (determines phi) \is_total).

Lemma det_eq phi:
	phi \from determined -> forall Fphi Fphi', F phi Fphi -> F phi Fphi' -> Fphi =1 Fphi'.
Proof.
move => det Fphi Fphi' FphiFphi FphiFphi' q'.
by have [a' dets]:= det q'; rewrite (dets Fphi) // (dets Fphi').
Qed.

Lemma eq_det phi:
	phi \from dom F /\ (forall Fphi Fphi', F phi Fphi -> F phi Fphi' -> Fphi =1 Fphi')
	-> determined phi.
Proof.
move => [[Fphi FphiFphi] eq] q'.
by exists (Fphi q') => Fphi' FphiFphi'; rewrite (eq Fphi Fphi').
Qed.

Lemma det_sing:
	(dom F \is_subset_of determined) <-> F \is_singlevalued.
Proof.
split => [detall | sing phi [Fphi FphiFphi] q']; last first.
	by exists (Fphi q') => Fphi' FphiFphi'; rewrite (sing phi Fphi Fphi').
move => phi Fphi Fphi' FphiFphi FphiFphi'; apply functional_extensionality => q'.
have [ | a' det] := (detall phi _ q'); first by exists Fphi.
by rewrite (det Fphi); first rewrite (det Fphi').
Qed.

Definition cert P phi := make_mf (fun q' a' =>
	forall psi, phi \agrees_with psi \on P -> determines psi q' a').
(* cert is for certificate and cert L phi q' a' means that the values of phi on the set P
is enough to determine the return value a' on input q'. *)

Global Instance crt_prpr: Proper (@set_equiv Q ==> @eqfun A Q ==> @equiv Q' A') cert.
Proof.
move => P P' eq phi phi' eq' q' a'; split => crt psi /agre_spec coin Fpsi FpsiFpsi.
- by apply/crt/FpsiFpsi; rewrite agre_spec eq -coin => q'' a'' /=; rewrite eq'.
by apply/crt/FpsiFpsi; rewrite agre_spec -eq -coin => q'' a'' /=; rewrite -eq'.
Qed.

Lemma cert_all phi: cert All phi =~= determines phi.
Proof.
move => q' a'; split => [crt Fphi FphiFphi | det psi coin]; first by apply/crt/FphiFphi.
by have <- : phi = psi by apply/functional_extensionality => q; apply coin.
Qed.

Lemma cert_icf L phi Fphi: F phi Fphi -> Fphi \is_choice_for (cert L phi).
Proof.
move => FphiFphi q' a' crt psi coin Fpsi FpsiFpsi.
rewrite (crt psi coin Fpsi) // (crt phi _ Fphi)//; exact/coin_ref.
Qed.

Lemma cert_exte L K phi: L \is_subset_of K -> cert K phi \extends cert L phi.
Proof.
move => subs q' a' crt psi /agre_spec coin.
exact/crt/agre_spec/restr_equiv/coin.
Qed.

Lemma cert_coin P phi psi:
  phi \agrees_with psi \on P -> cert P phi =~= cert P psi.
Proof.
move => coin; rewrite exte_equiv; split => q' a' crt psi' coin'; apply/crt.
- by rewrite -coin -coin'.
by rewrite coin coin'.
Qed.

Definition modulus := make_mf (fun phi (mf: Q' ->> Q) =>
	forall q', exists a', cert (mf q') phi q' a').

Lemma mod_prpr phi: Proper (@equiv Q' Q ==> iff) (modulus phi).
Proof.
move => f g eq; split => mod q'; have [a' crt]:= mod q'; exists a' => psi.
- by move => /agre_spec eq'; apply crt; rewrite agre_spec (eq q').
by move  => /agre_spec eq'; apply crt; rewrite agre_spec -(eq q').
Qed.

Lemma mod_frcs phi Fphi mf: F phi Fphi -> modulus phi mf -> forces F phi Fphi.
Proof.
move => FphiFphi mod Fphi' FphiFphi'.
apply functional_extensionality => q'; have [a' crt]:= mod q'.
by rewrite (crt phi) //; symmetry; apply/crt/FphiFphi.
Qed.

Lemma sing_spec_mod: F \is_singlevalued <->
	             dom F \is_subset_of dom modulus.
Proof.
rewrite sing_spec; split => [sing phi [Fphi FphiFphi]| cont phi [Fphi FphiFphi]]; last first.
	by have [ | mf mod]:= cont phi; [exists Fphi | exists Fphi; apply/mod_frcs/mod].
exists (make_mf (fun q => All)) => q'; exists (Fphi q'); rewrite cert_all => Fphi' FphiFphi'.
by have [ | Fphi'' frcs]:= sing phi; [exists Fphi | rewrite (frcs Fphi)//(frcs Fphi')].
Qed.
End smodulus.

Section smodulus_lemmas.
Context (Q A Q' A' : Type).
Notation B := (Q -> A).
Notation B' := (Q' -> A').

Lemma det_F2MF (f: B -> B') phi q': determines (F2MF f) phi q' (f phi q').
Proof. by move => _ <-. Qed.

Lemma det_exte (F G: B ->> B') phi:
	G \extends F -> determines F phi \extends determines G phi.
Proof. by move => GeF q' a' det Fpsi FpsiFpsi; exact/det/GeF. Qed.

Lemma det_restr P (F: B ->> B') phi q' a':
	determines (F \restricted_to P) phi q' a' <-> (P phi -> determines F phi q' a').
Proof. by split => [det Pphi Fphi val | prop Fphi [] Pphi]; [apply/det | apply/prop]. Qed.

Lemma cert_F2MF (f: B -> B') P phi q' a': cert (F2MF f) P phi q' a' <->
       forall psi, phi \agrees_with psi \on P -> f psi q' = a'.
Proof. by split => cert psi coin; last move => _ <-; apply/(cert psi coin). Qed.

Lemma cert_exte_exte (F G: B ->> B') P phi:
	G \extends F -> cert F P phi \extends cert G P phi.
Proof. by move => GeF q' a' certi psi coin; apply/det_exte; [apply GeF | apply certi]. Qed.

Lemma mod_F2MF phi mf (f: B -> B'): modulus (F2MF f) phi mf <->
  forall psi q', phi \agrees_with psi \on (mf q') -> f phi q' = f psi q'.
Proof.
split => [mod psi q' coin| prp]; first by have [a' crt]:= mod q'; rewrite (crt phi) // (crt psi).
by move => q'; exists (f phi q'); rewrite cert_F2MF; symmetry; apply/prp.
Qed.

Lemma mod_exte (F G: B ->> B'): G \extends F -> modulus F \extends modulus G.
Proof.
by move => exte phi Lf mod q'; have [a' crt] := mod q'; exists a'; apply/cert_exte_exte/crt.
Qed.

Lemma mod_exte_mf (F: B ->> B') mf mg phi:
	mg \extends mf -> modulus F phi mf -> modulus F phi mg.
Proof. by move => exte mod q'; have [a' crt]:= mod q'; exists a'; apply/cert_exte/crt. Qed.

Lemma mod_restr_sing (F: B ->> B'): F|_(dom (modulus F)) \is_singlevalued.
Proof.
apply/det_sing => phi [Fphi [[mf mod] FphiFphi]] q'.
by have [a' crt]:= mod q'; exists a'; rewrite det_restr => phifd; apply/crt.
Qed.
End smodulus_lemmas.

Section composition.
Context (Q A Q' A' Q'' A'': Type).
Notation B := (Q -> A).
Notation B' := (Q' -> A').
Notation B'' := (Q'' -> A'').
Context (F: B ->> B') (G: B' ->> B'').

Lemma det_comp phi Fphi:
	(forall Fphi', F phi Fphi' -> Fphi =1 Fphi') ->
	F phi Fphi -> determines (G \o F) phi \extends determines G Fphi.
Proof.
move => det FphiFphi q'' a'' detG GFphi [[Fphi' [FphiFphi' GFphi'GFphi]] subs].
apply/detG; suff ->: Fphi = Fphi' by trivial.
by apply functional_extensionality => q'; apply det.
Qed.

Lemma mod_comp mf mg phi Fphi: F phi Fphi ->
 modulus F phi mf -> modulus G Fphi mg -> modulus (G \o F) phi (mf \o_R mg).
Proof.
move => FphiFphi mod mod' q''; have [a'' crt']:= mod' q''; exists a''.
move => psi /agre_spec coin GFpsi [[Fpsi [FpsiFpsi GFpsiGFpsi]] subs]; rewrite (crt' Fpsi) => //.
move => q' a' /=; have [b' crt] := mod q'.
by rewrite (crt phi)//(crt psi)//; apply/agre_spec/restr_rcmp_equiv/coin.
Qed.
End composition.