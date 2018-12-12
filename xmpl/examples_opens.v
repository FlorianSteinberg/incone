From Coq.micromega Require Import Psatz.
From mathcomp Require Import all_ssreflect.
Require Import all_cs sets classical_cont classical_func.
Require Import ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section opens.
Lemma ON_iso_Sirpw : \O(cs_nat) ~=~ (cs_Sirp\^w).
Proof. by rewrite/opens sig_iso_fun; apply iso_ref. Qed.

Definition O2SS X (f: \O(X)) := make_subset (fun x => projT1 f x = top).

Lemma all_open X: exists (O: \O(X)), (O2SS O) === All.
Proof.
suff cont: (fun (_: X) => top: cs_Sirp) \is_continuous by exists (exist_c cont).
exists (F2MF (fun phi q => true)).  
by split; [apply/F2MF_rlzr_F2MF; split => //; exists 0 | apply cnst_cntop].
Qed.

Lemma empty_open X: exists (O: \O(X)), (O2SS O) === empty.
Proof.
suff cont: (fun (_: X) => bot: cs_Sirp) \is_continuous by exists (exist_c cont).
exists (F2MF (fun phi q => false)).  
by split; [apply/F2MF_rlzr_F2MF; split => [[] | ] | apply cnst_cntop].
Qed.
  
Notation "\A( X )" := (opens X) (at level 2, format "'\A(' X ')'").

Definition A2SS X (f: \A(X)) := make_subset (fun x => projT1 f x = bot).

Definition nonempty X := make_subset (fun (f: \O(X)) => exists x, projT1 f x = top).

Lemma all_closed X: exists (A: \A(X)), (A2SS A) === All.
Proof.
have [A eq]:= empty_open X.
exists A => x; split => // _ /=.
have /=:= eq x; move: eq => _.
by case: (sval A x) => // [[]].
Qed.

Lemma empty_closed X: exists (A: \A(X)), (A2SS A) === empty.
Proof.
have [A eq]:= all_open X.
exists A => x; split => //=.
have /=:= eq x; move: eq => _.
by case: (sval A x) => // [[]] _ {1}->.
Qed.

Definition CN:= (make_mf (fun (chi: \O(cs_nat)) (n: cs_nat) => (projT1 chi n) = bot))|_(nonempty cs_nat).

(*
Lemma CN_not_cont: ~ CN \has_continuous_realizer.
Proof.
move => [F [rlzr cont]].
*)

End opens.