(* This file provides a definition of continuity of functions between spaces of the form
Q -> A for some arbitrary types Q and A. It also proves some basic Lemmas about this notion.*)
From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mpf.
Require Import baire.
Require Import FunctionalExtensionality.
Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section continuity.
Context (Q A Q' A' : Type).
(* Q is for questions, A is for answers*)
Notation B := (Q ->> A).
Notation B' := (Q' ->> A').
(* B is for Baire space. *)
Context (F: B ->> B').

Definition determines phi:= make_mf (fun q' a' =>
	forall Fphi, F phi Fphi -> forces Fphi q' a').

Definition cert L phi :=make_mf (fun q' a' =>
	forall psi, phi|_L =~= psi|_L -> determines psi q' a').
(* cert is for certificate and cert L phi q' a' means that the values of phi on the list L
is enough to determine the return value a' on input q'. *)

Definition modulus := make_mf (fun phi Lf => forall q', exists a', cert (Lf q') phi q' a').

Definition continuous := dom F \is_subset_of dom modulus.
Definition continuity_points := intersection (dom modulus) (dom F).

Lemma cont_dom : continuous -> dom F === continuity_points.
Proof. by move => cont phi; split => [dm | ]; [split; first exact/cont | case]. Qed.

Lemma cert_subs L K phi:
	L \is_subset_of K -> cert K phi \extends cert L phi.
Proof.
Admitted.

Lemma cert_coin L phi psi:
	phi|_L  =~= psi|_L -> cert L phi =~= cert L psi.
Proof.
Admitted.
End continuity.

Section composition.
Context (Q A Q' A' Q'' A'': Type).
Notation B := (Q ->> A).
Notation B' := (Q' ->> A').
Notation B'' := (Q'' ->> A'').
Context (F: B ->> B') (G: B' ->> B'').

Lemma det_comp phi Fphi:
	(forall Fphi', F phi Fphi' -> Fphi =~= Fphi') ->
	F phi Fphi -> determines (G o F) phi \extends determines G Fphi.
Proof.
move => det FphiFphi q'' a'' detG GFphi [[Fphi' [FphiFphi' GFphi'GFphi]] subs].
apply/detG; suff eq: Fphi =~= Fphi'.
	admit.
exact/det.

Qed.

Fixpoint gather S T (Lf: S -> seq T) (K: seq S) := match K with
	| nil => nil
	| cons q' K' => app (Lf q') (gather Lf K')
end.

Definition LF2MF S T (Lf: S -> seq T):= make_mf (fun s => L2SS (Lf s)).

Lemma gather_LF2MF R S T (Lf: S -> seq T) (Lg: R -> seq S):
	LF2MF (fun r => (gather Lf (Lg r))) =~= (LF2MF Lf) o_R (LF2MF Lg).
Proof.
move => r t /=; elim: (Lg r) => [ | a L ih /=]; first by split => // [[s []]].
rewrite List.in_app_iff ih; split; last by case => s [[<- | ]]; [left | right; exists s].
by case => [lstn | [s []]]; [exists a | exists s]; split => //; [left | right].
Qed.

Lemma mod_comp Lf Lg phi Fphi: F phi Fphi ->
	modulus F phi Lf -> modulus G Fphi Lg -> modulus (G o F) phi (fun q'' => gather Lf (Lg q'')).
Proof.
move => FphiFphi mod mod' q''; have [a'' crt']:= mod' q''; exists a''.
move => psi coin GFpsi [[Fpsi [FpsiFpsi GFpsiGFpsi]] subs]; rewrite (crt' Fpsi) => //.
elim: (Lg q'') coin => // q' L ih coin.
have [coin1 coin2]:= ((coin_app phi psi (Lf q') (gather Lf L)).1 coin).
split; last exact/ih; have [a' crt]:= mod q'.
by rewrite (crt phi) //; try apply coin_ref; rewrite (crt psi).
Qed.

Lemma cont_comp: F \is_continuous -> G \is_continuous -> (G o F) \is_continuous.
Proof.
move => cont cont' phi phifd.
have [ | Lf mod]:= cont phi; first exact/comp_dom/phifd.
have [GFphi [[Fphi [FphiFphi GFphiGFphi]] _]] := phifd.
have [ | Lf' mod']:= cont' Fphi; first by exists GFphi.
exists (fun q' => gather Lf (Lf' q')).
exact/mod_comp/mod'.
Qed.
End composition.
(*
Definition eligible phi q' a' := exists Fphi, F phi Fphi /\ a' = Fphi q'.

Lemma dom_elig:
	F \is_total -> forall phi q', exists a', eligible phi q' a'.
Proof.
move => tot phi q'; have [Fphi FphiFphi]:= tot phi.
by exists (Fphi q'); exists Fphi.
Qed.

Lemma elig_dom:
	inhabited Q' -> F \is_total <-> forall phi q', exists a', eligible phi q' a'.
Proof.
move => [q']; split; first exact dom_elig; move => eligall phi.
by have [_ [Fphi [FphiFphi _]]]:= eligall phi q'; exists Fphi.
Qed.*)
End continuity.
Notation "F '\is_continuous'" := (continuous F) (at level 2).

Section continuity_lemmas.
Context (Q A Q' A' : Type).
Notation B := (Q ->> A).
Notation B' := (Q' ->> A').

Lemma det_exte (F G: B ->> B') phi:
	G \extends F -> determines F phi \extends determines G phi.
Proof. by move => GeF q' a' det Fpsi FpsiFpsi; exact/det/GeF. Qed.

Lemma det_restr P (F: B ->> B') phi q' a':
	determines (F \restricted_to P) phi q' a' <-> (P phi -> determines F phi q' a').
Proof.
split; first by move => det Pphi Fphi val; apply det.
by move => prop Fphi [] Pphi; apply: (prop Pphi).
Qed.

Lemma cert_F2MF (f: B -> B') L phi q' a':
	cert (F2MF f) L phi q' a' <-> forall psi, phi|_L =~= psi|_L -> determines (F2MF f) psi q' a'.
Proof. by split => cert psi coin; last move => _ <-; apply/(cert psi coin). Qed.

Lemma cert_exte (F G: B ->> B') L phi:
	G \extends F -> cert F L phi \extends cert G L phi.
Proof. by move => GeF q' a' certi psi coin; apply/det_exte; [apply GeF | apply certi]. Qed.

(*
Lemma elig_exte (F G: B ->> B') phi q' a':
	F \extends G -> eligible G phi q' a' -> eligible F phi q' a'.
Proof. by move => GeF [] Gphi [] GphiGphi eq; exists Gphi; split => //; apply/ GeF. Qed.

Lemma elig_restr P (F: B ->> B') phi q' a':
	eligible (F \restricted_to P) phi q' a' -> P phi /\ eligible F phi q' a'.
Proof. by move => [] Fphi [] []; split => //; exists Fphi. Qed.

Lemma restr_elig (P: mf_subset.type B) (F: B ->> B') phi q' a':
	P phi -> eligible F phi q' a' -> eligible (F \restricted_to P) phi q' a'.
Proof. by move => Pphi [] Fphi []; exists Fphi. Qed.
*)

Lemma mod_exte (F G: B ->> B'):
	G \extends F -> modulus F \extends modulus G.
Proof.
by move => exte phi Lf mod q'; have [a' crt] := mod q'; exists a'; apply/cert_exte/crt.
Qed.

Lemma mod_subl (F: B ->> B') Lf Kf phi:
	(forall q', (Lf q') \is_subset_of (Kf q')) -> modulus F phi Lf -> modulus F phi Kf.
Proof. by move => subl mod q'; have [a' crt]:= mod q'; exists a'; apply/cert_subs/crt. Qed.

Global Instance cont_prpr:
	Proper (@equiv B B' ==> iff) (@continuous Q A Q' A').
Proof.
move => f f' eq.
split => cont phi phifd.
	have [ | Lf mod] := cont phi; first by rewrite eq.
	exists Lf => q'; have [a' crt]:= mod q'.
	by exists a' => psi coin Fpsi; rewrite -eq; apply crt.
have [ | Lf mod] := cont phi; first by rewrite -eq.
exists Lf => q'; have [a' crt]:= mod q'.
by exists a' => psi coin Fpsi; rewrite eq; apply crt.
Qed.

Lemma restr_cont (F: B ->> B') P P':
	P \is_subset_of P' -> F|_P' \is_continuous -> F|_P \is_continuous.
Proof.
move => subs cont phi phifd.
exact/exte_dom/cont/dom_restr_subs/phifd/subs/mod_exte/exte_restr.
Qed.

Lemma restr_cont_w (F: B ->> B') P: F \is_continuous -> F|_P \is_continuous.
Proof. by move => cont; apply/restr_cont; first exact/subs_all; rewrite -restr_all. Qed.

Lemma mod_restr_cont (F: B ->> B'): F|_(dom (modulus F)) \is_continuous.
Proof.
move => phi [Fphi [[Lf mod] FphiFphi]].
exists Lf => q'; have [a' crt]:= mod q'.
by exists a' => psi coin Fpsi [_ FpsiFpsi]; apply/crt.
Qed.

Lemma restr_dom_cont (F: B ->> B'): F|_(continuity_points F) \is_continuous.
Proof. by apply/restr_cont/mod_restr_cont; move => phi []. Qed.

(*
Lemma mod_restr_sing (F: B ->> B'): F|_(dom (modulus F)) \is_singlevalued.
Proof.
apply/det_sing => phi [Fphi [[mf mod] FphiFphi]] q'.
by have [a' crt]:= mod q'; exists a'; rewrite det_restr => phifd; apply/crt/coin_ref.
Qed.
*)

(*
Lemma cont_sing (F: B ->> B'): F \is_continuous -> F \is_singlevalued.
Proof. by move => cont; rewrite -(restr_dom F); apply/restr_sing/mod_restr_sing. Qed.
*)

Lemma exte_dom S T (f g: S ->> T): f \extends g -> dom g \is_subset_of dom f.
Proof. by move => exte s [gs gsgs]; exists gs; apply/exte. Qed.

Lemma cont_exte (F G: B ->> B'):
	G \tightens F -> G \is_continuous -> F \is_singlevalued -> F \is_continuous.
Proof.
move => /sing_tight_exte exte cont sing phi phifd.
exact/exte_dom/cont/exte_dom/phifd/exte/sing/mod_exte/exte.
Qed.

Lemma cnst_cont (Fphi: Q' -> A'):
	(F2MF (fun phi: B => F2MF Fphi)) \is_continuous.
Proof.
move => phi/= _; exists (make_mf (fun q' a' => False)) => q'.
by exists (Fphi q') => psi _ _ <- S <-.
Qed.
End continuity_lemmas.

Section composition.
Context (Q A Q' A' Q'' A'': Type).
Notation B := (Q ->> A).
Notation B' := (Q' ->> A').
Notation B'' := (Q'' ->> A'').
Context (F: B ->> B') (G: B' ->> B'').

Lemma det_comp phi Fphi:
	(forall Fphi', F phi (F2MF Fphi') -> Fphi =1 Fphi') ->
	F phi (F2MF Fphi) -> determines (G o F) phi \extends determines G (F2MF Fphi).
Proof.
Admitted.

Lemma cont_comp: F \is_continuous -> G \is_continuous -> (G o F) \is_continuous.
Proof.
move => cont cont' phi phifd.
have [ | Lf mod]:= cont phi; first exact/comp_dom/phifd.
set gather := fix gather K := match K with
	| nil => nil
	| cons q' K' => app (Lf q') (gather K')
end.
have [GFphi [[Fphi [FphiFphi GFphiGFphi]] _]] := phifd.
have [ | Lf' mod']:= cont' Fphi; first by exists GFphi.
exists (fun q' => gather (Lf' q')) => q''; exists (GFphi q'') => psi coin.
move => GFpsi [[Fpsi [FpsiFpsi GFpsiGFpsi]] subs]; have [a'' crt']:= mod' q''.
rewrite (crt' Fpsi) => //; first by rewrite (crt' Fphi); try apply/coin_ref.
elim: (Lf' q'') coin => // q' L ih coin.
have [coin1 coin2]:= ((coin_app phi psi (Lf q') (gather L)).1 coin).
split; last exact/ih; have [a' crt]:= mod q'.
by rewrite (crt phi) //; try apply coin_ref; rewrite (crt psi).
Qed.
End composition.