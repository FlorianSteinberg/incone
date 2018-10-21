From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mpf.
Require Import baire cont.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section pointwise_continuity.
Context (Q A Q' A' : Type).
(* Q is for questions, A is for answers*)
Notation B := (Q -> A).
Notation B' := (Q' -> A').
(* B is for Baire space. *)
Context (F: B ->> B').

Definition mf_mod := make_mf (fun phiq L => phiq.1 \from dom F /\ forall Fphi, F phiq.1 Fphi -> cert F L phiq.1 phiq.2 (Fphi phiq.2)).

Lemma mod_mf_mod mf:
	mf \is_modulus_of F <-> forall phi q', phi \from dom F -> mf_mod (phi, q') (mf phi q').
Proof.
split => [ | mod phi Fphi FphiFphi q']; first by move => prop; split => //=; intros; apply prop.
by have phifd: phi \from dom F; [exists Fphi | apply (mod phi q' phifd).2].
Qed.

Definition cont_xtndbl_to phi := forall q', (phi, q') \from dom mf_mod.
Definition continuous_in phi := phi \from dom F /\ cont_xtndbl_to phi.
Definition ptw_continuous := forall phi, phi \from dom F -> cont_xtndbl_to phi.

Lemma ptw_continuous_spec:
	ptw_continuous <-> forall phi, phi \from (dom F) -> continuous_in phi.
Proof.
split => cont phi phifd; first by split => // q'; apply/cont.
by have []:= cont phi phifd.
Qed.

Lemma cont_ptw_cont: F \is_continuous -> ptw_continuous.
Proof.
by move => [mf /mod_mf_mod mod] phi phifd q'; exists (mf phi q'); apply /mod.
Qed.

Lemma ptw_cont_sing: ptw_continuous -> F \is_singlevalued.
Proof.
rewrite -det_sing => cont phi [Fphi FphiFphi] q'.
exists (Fphi q'); have [ | L [_ Lprop]]:= cont phi _ q'; first by exists Fphi.
exact/Lprop/coin_ref.
Qed.

Lemma mod_elig_cert phiq L:
	mf_mod phiq L <-> phiq.1 \from dom F /\ forall a', eligible F phiq.1 phiq.2 a' -> cert F L phiq.1 phiq.2 a'.
Proof.
split => [[phifd mod] | ]; first by split => // a' [Fphi [FphiFphi ->]]; apply/ mod.
by move => [phifd eligcert]; split => // Fphi FphiFphi; apply eligcert; exists Fphi.
Qed.

Lemma mod_subl phiq L K:
	L \is_sublist_of K -> mf_mod phiq L -> mf_mod phiq K.
Proof. by move => sl [phifd mod]; split => //; intros; apply/(cert_subl sl)/mod. Qed.

Definition dom_cont :=
	make_subset (fun phi => (forall q', (phi, q') \from dom mf_mod)).

Lemma dom_domc:
	ptw_continuous <-> forall phi, phi \from dom F -> phi \from dom_cont.
Proof. by split => cont phi phifd; last move => q'; apply cont. Qed.
End pointwise_continuity.
Notation "F \is_pointwise_continuous" := (ptw_continuous F) (at level 20).

Section composition.
Context (Q A : Type).
Notation B := (Q -> A).
Context (Q' A': Type).
Notation B':= (Q' -> A').
Context (F: B ->> B').

Lemma ptw_cont_domc: (F|_(dom_cont F)) \is_pointwise_continuous.
Proof.
move => phi [Fphi [domc FphiFphi]] q'.
have [L [/= phifd Lprop]]:= domc q'; exists L; split; first by exists Fphi.
move => Fphi' [/= _ val] psi coin.
by apply/ det_restr => domcpsi; apply/ Lprop.
Qed.

Lemma ptw_cont_comp Q'' A'' (G: B' ->> (Q'' -> A'')):
	F \is_continuous -> G \is_pointwise_continuous ->
		(G o F) \is_pointwise_continuous.
Proof.
move => [mf mod] cont phi phifd q''.
set gather := fix gather K := match K with
	| nil => nil
	| cons q' K' => app (mf phi q') (gather K')
end.
have [GFphi [[Fphi [FphiFphi GFphiGFphi]] _]] := phifd.
have [ | L [_ Lprop]]:= cont Fphi _ q''; first by exists GFphi.
exists (gather L); split => //.
move => GFphi' [[/=Fphi' [FphiFphi' GFphiGFphi']] _] psi coin'.
move => GFpsi [[Fpsi [FpsiFpsi GFpsiGFpsi]] subs].
have Gsing: G \is_singlevalued by apply ptw_cont_sing.
have Fsing: F \is_singlevalued by apply cont_sing; exists mf.
rewrite (Fsing phi Fphi' Fphi) in GFphiGFphi' => //.
rewrite (Gsing Fphi GFphi' GFphi) => //.
suffices gprop:
	forall K, phi \and psi \coincide_on (gather K) -> Fphi \and Fpsi \coincide_on K.
	by apply/Lprop/GFpsiGFpsi/gprop.
elim => // a K ih coin; have [coin1 coin2]:= ((coin_app phi psi (mf phi a) (gather K)).1 coin).
by split; [apply/mod/FpsiFpsi/coin1 | apply/ih].
Qed.
End composition.