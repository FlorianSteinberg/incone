From mathcomp Require Import all_ssreflect.
Require Import all_core cs prod.
Require Import FunctionalExtensionality ClassicalFacts ClassicalChoice Psatz.
Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section BASIC_LEMMAS.

Lemma id_hcr (X: cs): (@mf_id X) \has_continuous_realizer.
Proof.
exists mf_id; split => [ | phi phifd q']; first by rewrite F2MF_rlzr_F2MF.
by exists [ ::q']; split => // Fphi /= <- psi coin Fpsi <-; apply coin.1.
Qed.

Lemma diag_hcr (X: cs):
	(mf_diag: X ->> cs_prod _ _) \has_continuous_realizer.
Proof.
exists (F2MF (fun phi => name_pair phi phi)).
split => [ | phi phifd q]; first by rewrite F2MF_rlzr_F2MF.
case: q => q; by exists [:: q]; split => // Fphi/= <- psi [eq _] Fpsi <-; rewrite /name_pair eq.
Qed.
End BASIC_LEMMAS.