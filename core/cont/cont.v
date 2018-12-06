(* This file provides a definition of continuity of functions between spaces of the form
Q -> A for some arbitrary types Q and A. It also proves some basic Lemmas about this notion.*)
From mathcomp Require Import ssreflect ssrfun seq.
From rlzrs Require Import all_mf.
Require Import baire.
Require Import Morphisms FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section continuity.
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

Definition LF2MF S T (Lf: S -> seq T):= make_mf (fun s => L2SS (Lf s)).

Definition certificate L phi := make_mf (fun q' a' =>
	forall psi, phi \and psi \coincide_on L -> determines psi q' a').

Lemma crt_cert L phi: certificate L phi =~= cert (L2SS L) phi.
Proof. by split => crt psi/coin_agre; apply/crt. Qed.

Lemma crt_icf L phi Fphi: F phi Fphi -> Fphi \is_choice_for (certificate L phi).
Proof.
by move => val q' a'/crt_cert crt; rewrite crt_cert; apply/cert_icf/crt. 
Qed.

Definition continuity_modulus := make_mf (fun phi Lf =>
	forall q', exists a', certificate (Lf q') phi q' a').

Lemma mod_cmod phi Lf:
	continuity_modulus phi Lf <-> modulus phi (LF2MF Lf).
Proof. by split => mod q'; have [a' /crt_cert crt]:= mod q'; exists a'. Qed.

Lemma cmod_frcs phi Fphi mf:
	F phi Fphi -> continuity_modulus phi mf -> forces F phi Fphi.
Proof. rewrite mod_cmod; exact/mod_frcs. Qed.

Definition listfunctions:= make_subset (fun mf => exists Lf, mf = (@LF2MF Q' Q Lf)).

Lemma cmod_spec:
	modulus|^listfunctions =~= (F2MF (@LF2MF Q' Q)) \o continuity_modulus.
Proof.
move => phi mf; rewrite corestr_spec comp_rcmp; last exact/F2MF_tot.
split => [[[Lf ->] /mod_cmod mod] | [Lf [/mod_cmod mod <-]]]; first by exists Lf.
by split; first by exists Lf.
Qed.

Definition continuous_operator := forall phi Fphi,
  F phi Fphi -> exists Lf, forall q', certificate (Lf q') phi q' (Fphi q').

Lemma cntop_spec: continuous_operator <->
                  dom F \is_subset_of (dom continuity_modulus).
Proof.
split => [cont phi [Fphi val] | cont phi Fphi val].
- have [Lf mod]:= cont phi Fphi val.
  by exists Lf => q'; exists (Fphi q'); apply/mod.
have [ | Lf mod]:= cont phi; first by exists Fphi.
exists Lf => q'; have [a' crt]:= mod q'.
exact/crt_cert/cert_icf/crt_cert/crt.
Qed.

Definition continuity_points := intersection (dom continuity_modulus) (dom F).

Lemma cntop_dom : continuous_operator -> dom F === continuity_points.
Proof.
move => /cntop_spec cont phi.
by split => [dm | ]; [split; first exact/cont | case].
Qed.

End continuity.
Notation "F '\is_continuous_operator'" := (continuous_operator F) (at level 2).

Section continuity_lemmas.
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

Lemma smod_F2MF phi mf (f: B -> B'): modulus (F2MF f) phi mf <->
  forall psi q', phi \agrees_with psi \on (mf q') -> f phi q' = f psi q'.
Proof.
split => [mod psi q' coin| prp]; first by have [a' crt]:= mod q'; rewrite (crt phi) // (crt psi).
by move => q'; exists (f phi q'); rewrite cert_F2MF; symmetry; apply/prp.
Qed.

Lemma mod_F2MF phi Lf (f: B -> B'): continuity_modulus (F2MF f) phi Lf <->
  forall psi q', phi \and psi \coincide_on (Lf q') -> f phi q' = f psi q'.
Proof.
rewrite mod_cmod smod_F2MF.
by split => mod psi q'; [rewrite coin_agre| rewrite -coin_agre]; apply/mod.
Qed.

Lemma smod_exte (F G: B ->> B'):
  G \extends F -> modulus F \extends modulus G.
Proof.
by move => exte phi Lf mod q'; have [a' crt] := mod q'; exists a'; apply/cert_exte_exte/crt.
Qed.

Lemma mod_exte (F G: B ->> B'):
  G \extends F -> continuity_modulus F \extends continuity_modulus G.
Proof. by move => exte phi Lf; rewrite !mod_cmod; apply smod_exte. Qed.

Lemma smod_exte_mf (F: B ->> B') mf mg phi:
	mg \extends mf -> modulus F phi mf -> modulus F phi mg.
Proof. by move => exte mod q'; have [a' crt]:= mod q'; exists a'; apply/cert_exte/crt. Qed.

Global Instance cntop_prpr:
	Proper (@equiv B B' ==> iff) (@continuous_operator Q A Q' A').
Proof.
move => F F' eq.
split => cont phi Fphi val.
- have [ | Lf mod]:= cont phi Fphi; first exact/eq.
  by exists Lf => q' psi coin Fpsi val'; exact/mod/eq/val'.
have [ | Lf mod] := cont phi Fphi; first exact/eq.
by exists Lf => q' psi coin Fpsi val'; exact/mod/eq/val'.
Qed.

Definition continuous_operator_f (f: B -> B'):= forall phi, exists Lf,
   forall q' psi, phi \and psi \coincide_on (Lf q') -> f phi q' = f psi q'.

Lemma F2MF_cntop f: continuous_operator_f f <-> continuous_operator (F2MF f).
Proof.
split => [cont phi Fphi <-| cont phi].
- by have [Lf mod]:= cont phi; exists Lf => q' psi coin Fpsi <-; symmetry; apply/mod.
have [ | Lf mod]//:= cont phi (f phi); exists Lf => q' psi coin.
by symmetry; apply/mod; first exact/coin.
Qed.

Lemma restr_cont (F: B ->> B') P P':
  P \is_subset_of P' -> F|_P' \is_continuous_operator -> F|_P \is_continuous_operator.
Proof.
rewrite !cntop_spec => subs cont phi phifd.
exact/exte_dom/cont/dom_restr_subs/phifd/subs/mod_exte/exte_restr.
Qed.

Lemma restr_cont_w (F: B ->> B') P: F \is_continuous_operator ->
	                            F|_P \is_continuous_operator.
Proof. by move => cont; apply/restr_cont; first exact/subs_all; rewrite -restr_all. Qed.

Lemma mod_restr_cont (F: B ->> B'):
  F|_(dom (continuity_modulus F)) \is_continuous_operator.
Proof.
rewrite cntop_spec => phi [Fphi [[Lf mod] FphiFphi]].
exists Lf => q'; have [a' crt]:= mod q'.
by exists a' => psi coin Fpsi [_ FpsiFpsi]; rewrite (crt psi).
Qed.

Lemma restr_dom_cont (F: B ->> B'):
	F|_(continuity_points F) \is_continuous_operator.
Proof. by apply/restr_cont/mod_restr_cont; move => phi []. Qed.

Lemma mod_restr_sing (F: B ->> B'): F|_(dom (modulus F)) \is_singlevalued.
Proof.
apply/det_sing => phi [Fphi [[mf mod] FphiFphi]] q'.
by have [a' crt]:= mod q'; exists a'; rewrite det_restr => phifd; apply/crt.
Qed.

Lemma cont_sing (F: B ->> B'): F \is_continuous_operator -> F \is_singlevalued.
Proof.
move => /cntop_spec cont; apply/sing_spec_mod => phi phifd.
by have [Lf]:= cont phi phifd; rewrite mod_cmod; exists (LF2MF Lf).
Qed.

Lemma exte_dom S T (f g: S ->> T): f \extends g -> dom g \is_subset_of dom f.
Proof. by move => exte s [gs gsgs]; exists gs; apply/exte. Qed.

Lemma cont_exte (F G: B ->> B'):
	G \tightens F -> G \is_continuous_operator -> F \is_singlevalued ->
	F \is_continuous_operator.
Proof.
rewrite !cntop_spec => /sing_tight_exte exte cont sing phi phifd.
exact/exte_dom/cont/exte_dom/phifd/exte/sing/mod_exte/exte.
Qed.

Lemma cnst_cont (Fphi: B'):
	(F2MF (fun phi: B => Fphi)) \is_continuous_operator.
Proof. by rewrite cntop_spec => phi/= _; exists (cnst nil) => q'; exists (Fphi q') => psi _ _ <-. Qed.
End continuity_lemmas.

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

Lemma restr_rcmp_equiv S T S' T' (f f': S ->> T) (g: S' ->> S) (g': T' ->> S') (q: T') a:
	g' q a -> f|_(g \o_R g' q) =~= f'|_(g \o_R g' q) -> f|_(g a) =~= f'|_(g a).
Proof.
move => gqa eq s t.
split => [[gas fst] | [gas f'st]]; first by split => //; apply (eq s t).1; split; first by exists a.
by split => //; apply (eq s t).2; split; first by exists a.
Qed.

Lemma mod_comp mf mg phi Fphi: F phi Fphi ->
 modulus F phi mf -> modulus G Fphi mg -> modulus (G \o F) phi (mf \o_R mg).
Proof.
move => FphiFphi mod mod' q''; have [a'' crt']:= mod' q''; exists a''.
move => psi /agre_spec coin GFpsi [[Fpsi [FpsiFpsi GFpsiGFpsi]] subs]; rewrite (crt' Fpsi) => //.
move => q' a' /=; have [b' crt] := mod q'.
by rewrite (crt phi)//(crt psi)//; apply/agre_spec/restr_rcmp_equiv/coin.
Qed.

Lemma comp_rcmp_corestr R S T (f: R ->> S) (g: S ->> T):
  g \o_R f =~= g \o f|^(dom g).
Proof.
move => r t; split => [[s [frs gst]] | [[s [[]]]]]; last by exists s.
by split => [ | s' []]//; exists s; split => //; split => //; exists t.
Qed.

Fixpoint gather S T (Lf: S -> seq T) (K: seq S) := match K with
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
Proof.
by move => eq; rewrite -gather_LF2MF => r t /=; rewrite eq.
Qed.

Lemma exte_ref S T (f: S ->> T): f \extends f.
Proof. by move => s t fst. Qed.

Lemma cntop_comp: F \is_continuous_operator -> G \is_continuous_operator ->
	(G \o F) \is_continuous_operator.
Proof.
rewrite !cntop_spec => cont cont' phi phifd.
have [ | Lf /mod_cmod mod]:= cont phi; first exact/comp_dom/phifd.
have [GFphi [[Fphi [FphiFphi GFphiGFphi]] _]] := phifd.
have [ | Lf'/mod_cmod mod']:= cont' Fphi; first by exists GFphi.
exists (fun q' => gather Lf (Lf' q')); rewrite mod_cmod; apply/smod_exte_mf.
have/exte_equiv [this _]:= gather_LF2MF Lf Lf'; apply/this.
exact/mod_comp/mod'.
Qed.
End composition.