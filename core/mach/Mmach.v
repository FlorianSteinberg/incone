From mathcomp Require Import ssreflect seq ssrnat ssrbool eqtype ssrfun.
From rlzrs Require Import all_mf.
Require Import all_cont exec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section M_machine.
(* Q: Questions, A: Answers *)
Context (Q Q' A A' : Type).
(* B: Baire space *)
Notation B := (Q -> A).
Notation B' := (Q' -> A').
Notation "? K" := (@inl (list Q) A' K) (format "'?' K", at level 50).
Notation "! a'" := (@inr (list Q) A' a') (format "'!' a'", at level 50).

Definition M_step (psi: list A * Q' -> list Q + A') phi q' K :=
  match psi (map phi K, q') with
  | inr a' => inr a'
  | inl K' => inl (K' ++ K)
  end.

Fixpoint M_rec (psi: list A * Q' -> list Q + A') n phi q' :=
  match n with
  | 0 => inl nil
  | S n' => match M_rec psi n' phi q' with
	    | inr a' => inr a'
	    | inl K => M_step psi phi q' K
	    end
  end.

Definition M (psi: list A * Q' -> list Q + A')
           (n: nat) (phi: Q -> A) (q' : Q') :=
  match M_rec psi n phi q' with
  | inr a' => Some a'
  | inl L => None
  end.

Lemma M_mon psi: (M psi) \is_monotone.
Proof. by move => phi phifd q' n; rewrite/M/=; case E: (M_rec psi n phi q'). Qed.

Lemma M_rec_step n psi phi q':
  M_rec psi n.+1 phi q' = match M_rec psi n phi q' with
	                  | inr a' => inr a'
		          | inl K => M_step psi phi q' K
	                  end.
Proof. done. Qed.

Definition consistent (psi: _ -> _ + A') (phi: B) (q': Q') Qn :=
  forall i, i < size Qn -> exists K,
      psi (map phi (flatten (drop i.+1 Qn)), q') = ? K
      /\
      flatten (drop i Qn) = K ++ flatten (drop i.+1 Qn).

Lemma cns_drop psi phi q' Kn n:
  consistent psi phi q' Kn -> consistent psi phi q' (drop n Kn).
Proof.
move => cns i; rewrite size_drop => ils.
have [ | K []]:= cns (i + n); first by rewrite addnC -ltn_subRL.
by exists K; rewrite !drop_drop addSn.
Qed.

Lemma cns_cons psi phi q' K Kn:
  consistent psi phi q' (K::Kn) -> consistent psi phi q' Kn.
Proof. by move => cns i ineq; apply/cns. Qed.

Lemma M_rec_inl_spec psi n phi q' K:
  M_rec psi n phi q' =  inl K <-> exists (Qn: list (list Q)),
    size Qn = n /\ K = flatten Qn /\ consistent psi phi q' Qn.
Proof.
split.
- elim: n K => [K []| /= n]; first by rewrite /=/M_step; exists nil.
case E: (M_rec psi n phi q') => [K' | ] // ih K /=.
- have [ | Qn [sze [eq prp E']]]//:= ih K'.
  move: E'; rewrite /M_step; case val: (psi (map phi K', q')) => [K'' | ]// [E'].
  exists ( K'' :: Qn); split => //=; first by rewrite sze.
  split; first by rewrite -eq E'.
  case => [_ | i ineq]; last exact/prp.
  by exists K''; rewrite drop1/= -eq.
elim: n K => [_ [Ln [sze [-> cns]]]/= | /= n ih _ [Ln [sze [-> cns]]]].
- by rewrite (size0nil sze).
rewrite (ih (flatten (drop 1 Ln))).
  have [ | K [val ]]//:= cns 0; first by rewrite sze.
  by rewrite drop0 /M_step val => ->.
exists (drop 1 Ln); split => //; first by rewrite size_drop sze subnS.
by split; last exact/cns_drop.
Qed.

Lemma M_rec_inr_spec psi phi q' Qn a':
  consistent psi phi q' Qn -> M_rec psi (size Qn).+1 phi q' = inr a' <-> psi (map phi (flatten Qn), q') = inr a'.
Proof.
rewrite /= => cns.
rewrite (M_rec_inl_spec psi (size Qn) phi q' (flatten Qn)).2; last by exists Qn.
by rewrite /M_step; case: (psi (map phi (flatten Qn),q')).
Qed.

Definition communication psi (phi: B) := make_mf (fun (q': Q') Kna' =>
	let Kn:= Kna'.1 in let a':= Kna'.2 in consistent psi phi q' Kn /\ psi (map phi (flatten Kn), q') = !a').

Lemma FM_spec psi phi Fphi: \F_(M psi) phi Fphi <->
	forall q', exists Qn, communication psi phi q' (Qn, (Fphi q')).
Proof.
split => val q'.
- have [n]:= val q'.
  elim: n => [ | n ih /=]; rewrite /M/=/M_step.
    by case E: (psi (nil, q')) => [ | a']// [eq]; exists nil; rewrite E eq; split.
  case E: (M_rec psi n phi q') => [K | a']; last by move => eq; apply/ih; rewrite /M /= E eq.
  case E': (psi (map phi K, q')) => [ | a']// [eq].
  have [Kn [sze [eq']]]:= (M_rec_inl_spec psi n phi q' K).1 E.
  by exists Kn; split; last by rewrite -eq' E' eq.
have [Ln [/=eq prp]]:= val q'; exists (size Ln).+1.
rewrite /M/=/M_step (M_rec_inl_spec psi (size Ln) phi q' (flatten Ln)).2.
- by rewrite prp.
by exists Ln.
Qed.
End M_machine.