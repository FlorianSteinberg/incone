From mathcomp Require Import ssreflect seq ssrnat ssrbool eqtype ssrfun.
From rlzrs Require Import all_mf.
Require Import all_cont FMop Umach Ucont Uuniv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section duality_operator.
(* Q: Questions, A: Answers *)
Context (Q Q' A A' : Type).
(* B: Baire space *)
Notation B := (Q -> A).
Notation B' := (Q' -> A').
Notation "? K" := (@inl (list Q) A' K) (format "'?' K", at level 50).
Notation "! a'" := (@inr (list Q) A' a') (format "'!' a'", at level 50).

Fixpoint collect_left (Ka's: seq (seq Q + A')) : seq Q :=
  match Ka's with
  | nil => nil
  | cons Ka' Ka's' => match Ka' with
                      | inl K => K ++ collect_left Ka's'
                      | inr a' => nil
                      end
  end.

                                             
Fixpoint D (phi: B) (Ka'sq': seq (seq Q + A') * Q') : seq (seq A * Q') + A' :=
  match Ka'sq'.1 with
    | nil => inl [::(nil, Ka'sq'.2)]
    | Ka' :: Ka's => match Ka' with
                    | inl K => inl [::(map phi (collect_left Ka'sq'.1), Ka'sq'.2)]
                    | inr a' => inr a'
                    end
  end.

Lemma D_spec psi phi:
  \F_(U (D phi)) psi === \F_(U psi) phi.
Proof.
move => Fphi.
split => /FU_spec evl q'; last first.
have [Qn [/=cns val]]:= evl q'.
exists (size Qn).+2.
rewrite /U unfold_U_rec.
case: (U_rec_spec (D phi) (size Qn).+1 psi q') => [-> | ].
rewrite /U_step.
Admitted.
End duality_operator.