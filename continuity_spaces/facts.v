From mathcomp Require Import ssreflect seq.
From rlzrs Require Import all_rlzrs.
Require Import cont cs prod.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope cs_scope.
Section facts.
  Lemma id_hcr (X: cs): (@mf_id X) \has_continuous_realizer.
  Proof.
    exists mf_id; split; first by rewrite F2MF_rlzr_F2MF.
    by apply cont_F2MF => phi; exists (fun q => [:: q]) => psi q' [-> ].
  Qed.

  Lemma id_cont (X: cs): (@id X) \is_continuous.
  Proof. exact/id_hcr. Qed.

  Lemma diag_hcr (X: cs):
    (mf_diag: X ->> _) \has_continuous_realizer.
  Proof.
    exists (F2MF (fun phi => name_pair phi phi)); split; first by rewrite F2MF_rlzr_F2MF.
    exact/cntop_cntf/naming_spaces.diag_cont.
  Qed.

  Lemma diag_cont (X: cs): (@diag X) \is_continuous.
  Proof. exact/diag_hcr. Qed.
End facts.