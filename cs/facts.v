From mathcomp Require Import ssreflect seq.
From rlzrs Require Import all_mf.
Require Import cont cs prod.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section BASIC_LEMMAS.

Lemma id_hcr (X: cs): (@mf_id X) \has_continuous_realizer.
Proof.
exists mf_id; split; first by rewrite F2MF_rlzr_F2MF.
by apply F2MF_cont => phi; exists (fun q => [:: q]) => psi q' [-> ].
Qed.

Lemma id_cont (X: cs): (@id X) \is_continuous.
Proof. exact/id_hcr. Qed.

Lemma diag_hcr (X: cs):
	(mf_diag: X ->> cs_prod _ _) \has_continuous_realizer.
Proof.
exists (F2MF (fun phi => name_pair phi phi)); split; first by rewrite F2MF_rlzr_F2MF.
apply F2MF_cont => phi.
exists (fun qq' => match qq' with | inl q => [:: q] | inr q' => [:: q'] end) => psi [q | q'] [];
by rewrite /name_pair => ->.
Qed.
End BASIC_LEMMAS.