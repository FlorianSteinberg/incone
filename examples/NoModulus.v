(* This file contains a formalization of an old result by Kreisel that was formally written down by
   Trolestra. It says that no modulus of continuity exists. The proof is taken from a previous
   formalization in minlog done by Helmut Schwichtenberg which was in turn motivated by one
   done in Agda by Chuangji Xu.*)
From mathcomp Require Import all_ssreflect.

Definition is_modulus (M: ((nat -> nat) -> nat) -> nat):=
  forall G h,
    (forall i, i < M G -> h i = 0) ->
    G (fun _ => 0) = G h.

Lemma no_mod : ~ exists M, is_modulus M.
Proof.
  move => [M mod].
  pose G h := M (fun g => h (g (M (fun _ => 0)))).
  pose h n := if n < (M G).+1 then 0 else 1.
  pose g n := if n < M (fun _ => 0) then 0 else (M G).+1.
  have eq: G h = M (fun _ => 0).
    by rewrite -mod /h // => i /leqW ->.
  have: h 0 = h (g (M (fun _ => 0))).
  - apply/(mod (fun g => h (g (M (fun _ => 0))))) => // i.
    by rewrite /G in eq; rewrite eq /g => ->.
  by rewrite /h/= /g !ltnn.
Qed.