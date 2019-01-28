From mathcomp Require Import ssreflect seq ssrnat ssrbool eqtype ssrfun.
From rlzrs Require Import all_mf.
Require Import all_cont FMop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section U_machine.
(* Q: Questions, A: Answers *)
Context (Q Q' A A' : Type).
(* B: Baire space *)
Notation B := (Q -> A).
Notation B' := (Q' -> A').
Notation "? K" := (@inl (list Q) A' K) (format "'?' K", at level 50).
Notation "! a'" := (@inr (list Q) A' a') (format "'!' a'", at level 50).

Definition U_step (psi: list A * Q' -> list Q + A') phi q' K :=
  match psi (map phi K, q') with
  | inr a' => inr a'
  | inl K' => inl (K' ++ K)
  end.

Fixpoint U_rec (psi: list A * Q' -> list Q + A') n phi q' :=
  match n with
  | 0 => inl nil
  | S n' => match U_rec psi n' phi q' with
	    | inr a' => inr a'
	    | inl K => U_step psi phi q' K
	    end
  end.

Definition U (psi: list A * Q' -> list Q + A')
           (n: nat) (phi: Q -> A) (q' : Q') :=
  match U_rec psi n phi q' with
  | inr a' => Some a'
  | inl L => None
  end.

Lemma U_mon psi: (U psi) \is_monotone.
Proof. by move => phi phifd q' n; rewrite/U/=; case E: (U_rec psi n phi q'). Qed.

Lemma unfold_U_rec n psi phi q':
  U_rec psi n.+1 phi q' = match U_rec psi n phi q' with
	                  | inr a' => inr a'
		          | inl K => U_step psi phi q' K
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

Lemma rev_eq T (L L': seq T): rev L = rev L' <-> L = L'.
Proof. by split; first rewrite -{2}(revK L) -{2}(revK L'); move ->. Qed.

Lemma rcons_eq T L L' (a a': T): rcons L a = rcons L' a' <-> L = L' /\ a = a'.
Proof.
split; last by case => -> ->.
by rewrite -(revK (rcons L a)) -(revK (rcons L' a')) rev_eq !rev_rcons => [[-> /rev_eq ->]].
Qed.

Lemma cat_eq_r T (L L' K: seq T): L ++ K = L' ++ K <-> L = L'.
Proof.
elim: K L L' => [L L' | a K ih L L']; [rewrite !cats0 | split => [ | ->]] => //.
by rewrite -!cat_rcons (ih (rcons L a) (rcons L' a)) rcons_eq => [[->]].
Qed.

Lemma cns_eq (psi: seq A * Q' -> seq Q + A') phi q' Kn Kn': size Kn = size Kn' ->
	consistent psi phi q' Kn -> consistent psi phi q' Kn' -> Kn = Kn'.
Proof.
move: {2}(size Kn) (leqnn (size Kn)) => n.
elim: n Kn Kn' => [[[] | []] | n ih [[] | K Kn []]]// K' Kn' ineq [sze] cns cns'.
have eq: Kn = Kn' by apply/ih/cns_cons/cns'/cns_cons/cns/sze/ineq.
rewrite eq; f_equal.
have [ | K'' []]//=:= cns 0; rewrite drop0 => val /cat_eq_r ->.
have [ | K''' []]//=:= cns' 0; rewrite drop0 => val' /cat_eq_r ->.
by move: val val'; rewrite eq => -> [->].
Qed.

Lemma cns_val_eq (psi: seq A * Q' -> seq Q + A') phi q' Kn Kn' a':
  psi (map phi (flatten Kn), q') = ! a' -> size Kn <= size Kn' ->
	consistent psi phi q' Kn -> consistent psi phi q' Kn' -> Kn = Kn'.
Proof.
move => val; elim: Kn' => [ | K' Kn' ih]; first by rewrite leqn0 => /eqP eq; rewrite (size0nil eq).
rewrite leq_eqVlt; case /orP => [/eqP eq | ineq cns cns'].
- by case: Kn eq ih val => // K Kn [sze] ih val; apply/cns_eq; rewrite /= sze.
have [ | K ]//:= cns' 0; have <-: Kn = Kn' by apply/ih/cns_cons/cns'.
by rewrite drop1 /= val; case.
Qed.

Lemma U_rec_inl_spec psi n phi q' K: U_rec psi n phi q' =  inl K <->
  exists (Qn: list (list Q)), size Qn = n /\ K = flatten Qn /\ consistent psi phi q' Qn.
Proof.
split.
- elim: n K => [K []| /= n]; first by rewrite /=/U_step; exists nil.
case E: (U_rec psi n phi q') => [K' | ] // ih K /=.
- have [ | Qn [sze [eq prp E']]]//:= ih K'.
  move: E'; rewrite /U_step; case val: (psi (map phi K', q')) => [K'' | ]// [E'].
  exists ( K'' :: Qn); split => //=; first by rewrite sze.
  split; first by rewrite -eq E'.
  case => [_ | i ineq]; last exact/prp.
  by exists K''; rewrite drop1/= -eq.
elim: n K => [_ [Ln [sze [-> cns]]]/= | /= n ih _ [Ln [sze [-> cns]]]].
- by rewrite (size0nil sze).
rewrite (ih (flatten (drop 1 Ln))).
  have [ | K [val ]]//:= cns 0; first by rewrite sze.
  by rewrite drop0 /U_step val => ->.
exists (drop 1 Ln); split => //; first by rewrite size_drop sze subnS.
by split; last exact/cns_drop.
Qed.

Lemma U_rec_inr_spec psi phi q' Qn a':
  consistent psi phi q' Qn -> U_rec psi (size Qn).+1 phi q' = inr a' <-> psi (map phi (flatten Qn), q') = inr a'.
Proof.
rewrite /= => cns.
rewrite (U_rec_inl_spec psi (size Qn) phi q' (flatten Qn)).2; last by exists Qn.
by rewrite /U_step; case: (psi (map phi (flatten Qn),q')).
Qed.

Definition communication psi (phi: B) := make_mf (fun (q': Q') Kna' =>
	let Kn:= Kna'.1 in let a':= Kna'.2 in consistent psi phi q' Kn /\ psi (map phi (flatten Kn), q') = !a').

Lemma cmcn_sing (psi: seq A * Q' -> seq Q + A') phi: (communication psi phi) \is_singlevalued.
Proof.
move => q' [Ln a'] [Ln' b'] [/=cns val] [cns' val'].
case/orP: (leq_total (size Ln) (size Ln')) => ineq.
- move: val'; have <-: Ln = Ln' by apply/cns_val_eq/cns'/cns/ineq/val.
  by rewrite val => [[->]].
move: val; have <-: Ln' = Ln by apply/cns_val_eq/cns/cns'/ineq/val'.
by rewrite val' => [[->]].
Qed.

Lemma FU_spec psi phi Fphi: \F_(U psi) phi Fphi <->
	forall q', exists Qn, communication psi phi q' (Qn, (Fphi q')).
Proof.
split => val q'.
- have [n]:= val q'.
  elim: n => [ | n ih /=]; rewrite /U/=/U_step.
    by case E: (psi (nil, q')) => [ | a']// [eq]; exists nil; rewrite E eq; split.
  case E: (U_rec psi n phi q') => [K | a']; last by move => eq; apply/ih; rewrite /U /= E eq.
  case E': (psi (map phi K, q')) => [ | a']// [eq].
  have [Kn [sze [eq']]]:= (U_rec_inl_spec psi n phi q' K).1 E.
  by exists Kn; split; last by rewrite -eq' E' eq.
have [Ln [/=eq prp]]:= val q'; exists (size Ln).+1.
rewrite /U/=/U_step (U_rec_inl_spec psi (size Ln) phi q' (flatten Ln)).2.
- by rewrite prp.
by exists Ln.
Qed.
End U_machine.