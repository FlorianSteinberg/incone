From mathcomp Require Import ssreflect seq ssrnat ssrbool eqtype ssrfun.
From rlzrs Require Import all_mf.
Require Import all_cont FMop Umach.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section queries.
(* Q: Questions, A: Answers *)
Context (Q Q' A A' : Type).
(* B: Baire space *)
Notation B := (Q -> A).
Notation B' := (Q' -> A').
Notation "? K" := (@inl (seq Q) A' K) (format "'?' K", at level 50).
Notation "! a'" := (@inr (seq Q) A' a') (format "'!' a'", at level 50).

Fixpoint gather_queries (psi: seq A * Q' -> seq Q + A') n phi q':=
  match U_rec psi n phi q' with
  | inr a' => match n with
              | 0 => nil
              | S n' => gather_queries psi n' phi q'
              end
  | inl K => K
  end.

Definition queriesM psi n phi q' :=
  match U_rec psi n phi q' with
  | inl K => None
  | inr a' => Some (gather_queries psi n phi q')
  end.

Lemma unfold_gq psi n phi q': gather_queries psi n phi q' =
  match U_rec psi n phi q' with
  | inr a' => match n with
              | 0 => nil
              | S n' => gather_queries psi n' phi q'
              end
  |inl K => K
  end.
Proof. by case: n. Qed.

Lemma gq_mon psi n phi q':
  (gather_queries psi n phi q') \is_sublist_of (gather_queries psi n.+1 phi q').
Proof.
move => q/=; rewrite unfold_gq.
case E: (U_rec psi n phi q') => [K | a'] //; rewrite /U_step.
by case: (psi (map phi K, q')) => // K' lstn; apply/lstn_app; right.
Qed.

Lemma gq_subl psi n m phi q': n <= m ->
  (gather_queries psi n phi q') \is_sublist_of (gather_queries psi m phi q').
Proof.  
elim: m n => [n | m ih n]; first by rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt; case/orP => [/eqP -> | ineq]//.  
exact/subl_trans/gq_mon/ih.
Qed.

Lemma U_rec_spec psi n phi q':
  U_rec psi n phi q' = ?(gather_queries psi n phi q') \/ exists a', U_rec psi n phi q' = !a'.
Proof.
elim: n => [ | n [/= -> | [a' eq]]]; [left | | right; exists a' => /=; rewrite eq] => //.
by case E: (U_step psi phi q' (gather_queries psi n phi q')) => [K | a']; [left | right; exists a'].
Qed.

Lemma gq_cns psi phi q' Qn: consistent psi phi q' Qn ->
  gather_queries psi (size Qn) phi q' = flatten Qn.
Proof.
elim: Qn => // K Qn ih cns /=; have [ | K' []]//:= cns 0.
rewrite (U_rec_inl_spec psi (size Qn) phi q' (flatten Qn)).2.
- by rewrite /= drop0 /U_step => ->.
by exists Qn; split; last split; last exact/cns_cons/cns.
Qed.

Lemma cns_gq psi n phi q':
exists Qn, size Qn <= n /\ consistent psi phi q' Qn /\ gather_queries psi n phi q' = flatten Qn.
Proof.
elim: n => [ | n [Qn [sze [cns/= eq]]]]; first by exists nil.
have:= eq; rewrite unfold_gq.
case E: (U_rec psi n phi q') => [K | a'] => [ | ->]; last by exists Qn; rewrite leqW.
rewrite /U_step/=; case val: (psi (map phi K, q')) => [K' | ]// ->.
+ exists (K':: Qn); split => //; split => // [[ | i ineq]]; last exact/cns.
  by exists K'; rewrite drop1/=; split => //; rewrite -eq unfold_gq E.
by exists Qn; split; first exact/leqW; split => //; rewrite -eq unfold_gq E.
Qed.

Lemma gq_spec psi phi q' K : (exists n, gather_queries psi n phi q' = K) <->
      exists Qn, consistent psi phi q' Qn /\ K = flatten Qn.
Proof.
split => [[n <-] | [Qn [sze cns]]]; last by exists (size Qn); rewrite gq_cns.
by have [Qn [_ []]]:= cns_gq psi n phi q'; exists Qn.
Qed.

Lemma gq_cmcn psi n phi q' Qn a':
  communication psi phi q' (Qn, a') -> size Qn <= n ->
  gather_queries psi n phi q' = flatten Qn.
Proof.                                
move => [/=cns val] ineq; rewrite -(subnK ineq).
elim: (n-size Qn) => [ | k gq]; first exact/gq_cns.
rewrite -gq addSn /= unfold_gq /U_step.
case: (U_rec_spec psi (k + size Qn) phi q') => [-> | [_ ->]] //.
case E: (psi (map phi (gather_queries psi (k + size Qn) phi q'), q')) => [K |] //.
by rewrite gq val in E.
Qed.

Lemma cmcn_gq psi n phi q' Qn a':
  U_rec psi n phi q' = !a' -> consistent psi phi q' Qn -> gather_queries psi n phi q' = flatten Qn -> communication psi phi q' (Qn, a').
Proof.
move => val cns eq; split => //=.
have sze: size Qn <= n.
  - rewrite leqNgt; apply /negP => lt.
    case E: (size Qn) => [ | k]; first by rewrite E in lt.
    have [ | K [vl eq']]:= cns (k - n); first by rewrite E; apply/leq_subr.
    rewrite (U_rec_inl_spec psi n phi q' (flatten (drop (k.+1-n) Qn))).2 in val => //.
    exists (drop (k.+1 - n) Qn); split; last split => //; last by apply/cns_drop.
    by rewrite size_drop E subKn // -E; apply/leq_trans/lt.  
  have prp: forall K, psi (map phi (flatten Qn), q') = ? K -> K = nil.
  - rewrite -eq => K; move: val eq; rewrite -(subnK sze).
    elim (n - size Qn) => [ | k ih]; last rewrite addSn /=.
    - rewrite (U_rec_inl_spec psi (size Qn) phi q' (flatten Qn)).2 //.
      by exists Qn.
    case: (U_rec_spec psi (k + size Qn) phi q') => [-> | [b' eq]]; last first.
    - by rewrite eq => eq' gq ps; apply/ih => //; first by rewrite -eq'.
    rewrite /U_step.
    case E: (psi (map phi (gather_queries psi (k + size Qn) phi q'), q')) => [ | b'] // eq'.
    by rewrite E.
  have prp': forall k, gather_queries psi (k + size Qn) phi q' = flatten Qn.
  - elim => [ | k ih]; [by rewrite add0n; apply/gq_cns | rewrite addSn /=].
    case: (U_rec_spec psi (k + size Qn) phi q') => [-> | [_ ->]]//.
    rewrite /U_step ih; case E: (psi (map phi (flatten Qn), q')) => [K' | ]//.
    by rewrite (prp K') //.
  move: val; rewrite -(subnK sze).
  elim: (n - size Qn) => [ | k ih]; last rewrite addSn/=.
  - rewrite add0n (U_rec_inl_spec psi (size Qn) phi q' (flatten Qn)).2 //.
    by exists Qn.
  case: (U_rec_spec psi (k + size Qn) phi q') => [E | [b' eq']].
    rewrite E /U_step.
    case E': (psi (map phi (gather_queries psi (k + size Qn) phi q'), q')) => [K | b'] // <- //.
  + by rewrite prp' in E'. 
  by rewrite eq' => eq''; apply ih; rewrite -eq''.
Qed.

Lemma qM_mon psi: (queriesM psi) \is_monotone.
Proof.
by move => phi phifd q' n; rewrite /queriesM /=; case: (U_rec psi n phi q').
Qed.
  
Lemma FqM_spec psi phi mf: \F_(queriesM psi) phi mf <->
  forall q', exists Qn a', communication psi phi q' (Qn, a')
                           /\
                           mf (q') = flatten Qn.
Proof.
split => [mod q' | prp q'].
- have [n]:= mod q'; rewrite /queriesM.
  case val: (U_rec psi n phi q') => [ | a'] // [eq].
  have [ | Qn [cns flt]]:= (gq_spec psi phi q' (mf q')).1; try by exists n.
  exists Qn; exists a'; split => //; split => //.
  rewrite flt in eq; move: flt => _ /=.
  by have []:= cmcn_gq val cns eq.
have [Qn [a' [[cns val] gq]]]:= prp q'; exists (size Qn).+1.
rewrite /queriesM /=/U_step (U_rec_inl_spec psi (size Qn) phi q' (flatten Qn)).2; last by exists Qn.
by rewrite val (gq_cns cns); f_equal.
Qed.
End queries.

Section shapes.
(* Q: Questions, A: Answers *)
Context (Q Q' A A' : Type).
(* B: Baire space *)
Notation B := (Q -> A).
Notation B' := (Q' -> A').
Notation "? K" := (@inl (seq Q) A' K) (format "'?' K", at level 50).
Notation "! a'" := (@inr (seq Q) A' a') (format "'!' a'", at level 50).

Fixpoint build_shapes (psi: seq A * Q' -> seq Q + A') n phi q':=
  match U_rec psi n phi q' with
  | inr a' => match n with
              | 0 => [:: (nil, q')]
              | S n => build_shapes psi n phi q'
              end
  | inl K => iseg (fun i => (map phi (gather_queries psi i phi q'), q')) n.+1
  end.

Definition shapesM psi n phi q' :=
  match U_rec psi n phi q' with
  | inl K => None
  | inr a' => Some (build_shapes psi n phi q')
  end.

Lemma unfold_bs psi n phi q':
  build_shapes psi n phi q' =
  match U_rec psi n phi q' with
  | inr a' => match n with
              | 0 => [:: (nil, q')]
              | S n => build_shapes psi n phi q'
              end
  | inl K => iseg (fun i => (map phi (gather_queries psi i phi q'), q')) n.+1
  end.
Proof. by case: n. Qed.

Lemma bs_mon psi n phi q':
  (build_shapes psi n phi q') \is_sublist_of (build_shapes psi n.+1 phi q').
Proof.
move => q.
rewrite/=.
case E: (U_rec psi n phi q') => [K | a'] //; rewrite /U_step.
case E': (psi (map phi K, q')) => [K' | b'] //=.
by rewrite unfold_bs E; right.
Qed.

Lemma bs_subl psi n m phi q': n <= m ->
  (build_shapes psi n phi q') \is_sublist_of (build_shapes psi m phi q').
Proof.  
elim: m n => [n | m ih n]; first by rewrite leqn0 => /eqP ->.
by rewrite leq_eqVlt; case/orP => [/eqP -> | ineq]//; apply/subl_trans/bs_mon/ih.
Qed.

Lemma size_bs_leq psi phi q' n: size (build_shapes psi n phi q') <= n.+1.
Proof.
elim: n => [ | n ih]; first by rewrite /=; case: (U_step psi phi q' [::]).
rewrite unfold_bs.
by case: (U_rec psi n.+1 phi q') => [K | a']; [rewrite size_iseg | exact/leqW].
Qed.

Lemma bs_cns psi phi q' Qn: consistent psi phi q' Qn ->
  build_shapes psi (size Qn) phi q' =  iseg (fun i => (map phi (gather_queries psi i phi q'), q')) (size Qn).+1.
Proof.
elim: Qn => // K Qn ih cns /=.
rewrite (U_rec_inl_spec psi (size Qn) phi q' (flatten Qn)).2; last first.
  by exists Qn; split; last split; last exact/cns_cons/cns.
have [ | K' []] //:= cns 0.
by rewrite /= drop0 /U_step => -> . 
Qed.

Lemma bs_cmcn psi n phi q' Qn a': communication psi phi q' (Qn, a') ->
                                  size Qn <= n -> build_shapes psi n phi q' = iseg (fun i => (map phi (flatten (drop (size Qn - i) Qn)), q')) (size Qn).+1.
Proof.    
move => [/=cns val] ineq; rewrite -(subnK ineq).
elim: (n - size Qn) => [ | k bs].
- rewrite bs_cns //; apply/iseg_eq => i ineq'.
  by rewrite -(gq_cns (cns_drop cns)) size_drop subKn.
rewrite -bs addSn /= unfold_bs /U_step.
case: (U_rec_spec psi (k + size Qn) phi q') => [-> | [_ ->]] //.
case E: (psi (map phi (gather_queries psi (k + size Qn) phi q'), q')) => [K |] //.
have com: communication psi phi q' (Qn, a') by trivial.
have prp:= (gq_cmcn com).
rewrite (prp (k + size Qn)) in E; [rewrite val// in E | exact/leq_addl].
Qed.

Lemma FsM_spec psi phi sf: \F_(shapesM psi) phi sf <->
  forall q', exists Qn a', communication psi phi q' (Qn, a') /\ sf q' = iseg (fun i => (map phi (flatten (drop ((size Qn) - i) Qn)), q')) (size Qn).+1.
Proof.
split => [sM q' | prp q' ]; last first.
- have [Qn [a' [com ->]]] := prp q'; exists (size Qn).+1.
  by rewrite /shapesM ((M_rec_inr_spec a' com.1).2 com.2) (bs_cmcn com).
have [n]:= sM q'; rewrite /shapesM.
case: (U_rec_spec psi n phi q') => [eq | [a' eq]];rewrite eq//; case => <-.
have [Qn [sze [cns gq]]]:= cns_gq psi n phi q'.
by exists Qn; exists a'; have com:= cmcn_gq eq cns gq; rewrite (bs_cmcn com). 
Qed.
End shapes.

Section continuity.
(* Q: Questions, A: Answers *)
Context (Q Q' A A' : Type).
(* B: Baire space *)
Notation B := (Q -> A).
Notation B' := (Q' -> A').
Notation "? K" := (@inl (seq Q) A' K) (format "'?' K", at level 50).
Notation "! a'" := (@inr (seq Q) A' a') (format "'!' a'", at level 50).

Lemma cns_cont (psi: seq A * Q' -> seq Q + A') phi phi' q' Qn:
  phi \and phi' \coincide_on (gather_queries psi (size Qn) phi q') ->
    consistent psi phi q' Qn -> consistent psi phi' q' Qn.
Proof.
elim: Qn => // K Qn ih /= coin cns; move: coin.
have rec:= (U_rec_inl_spec psi (size Qn) phi q' (flatten Qn)).2.
rewrite rec/U_step; last by exists Qn; do 2 split => //; apply/cns_cons/cns.
case val: (psi (map phi (flatten Qn), q')) => [K' | a']; last first.
- by have [ | K'' [/=]]//:= cns 0; rewrite drop0 val.
rewrite coin_cat => [[coin coin']] [_/= | i].
- rewrite drop0 -(coin_map coin').
  by have prp:= cns 0; rewrite /= drop0 in prp; apply/prp.
apply/ih=>//; [rewrite unfold_gq rec// | exact/cns_cons/cns].
by exists Qn; do 2 split => //; apply/cns_cons/cns.
Qed.

Lemma FqM_mod_FM (psi: seq A * Q' -> seq Q + A') phi mf:
  \F_(queriesM psi) phi mf -> continuity_modulus \F_(U psi) phi mf.
Proof.
move => /FqM_spec mod q'.
have [Qn [a' [[/=cns val] gq]]]:= mod q'.  
exists a' => phi' coin Fphi' /FU_spec Fphi'Fphi'.
have [Qn' com]:= Fphi'Fphi' q'.
suff com': communication psi phi' q' (Qn, a') by have [_ ->]:= (cmcn_sing com com').
split; last by rewrite -gq -(coin_map coin) gq.
by apply/cns_cont/cns; rewrite (gq_cns cns) // -gq.
Qed.

Lemma FqM_mod_FqM (psi: seq A * Q' -> seq Q + A') phi mf:
  \F_(queriesM psi) phi mf -> continuity_modulus \F_(queriesM psi) phi mf.
Proof.
move => /FqM_spec val q'; have [Qn [a' [com eq]]]:= val q'.  
exists (flatten Qn) => phi' coin mf' /FqM_spec mf'val.
have [Qn' [b' [com' eq']]]:= mf'val q'; move: mf'val => _.
rewrite eq'; f_equal.
suff prp: communication psi phi' q' (Qn, a') by have []:= cmcn_sing com' prp.
split; first by apply/cns_cont/com.1; rewrite (gq_cns com.1) -eq.
by rewrite -eq -(coin_map coin) eq com.2.
Qed.

Lemma FqM_mod_FsM (psi: seq A * Q' -> seq Q + A') phi mf:
  \F_(queriesM psi) phi mf -> continuity_modulus \F_(shapesM psi) phi mf.
Proof.
move => /FqM_spec val q'.
have [Qn [a' [com ->]]]:= val q'.
exists (build_shapes psi (size Qn) phi q').
rewrite (bs_cmcn com) // => phi' coin sf /FsM_spec val'.
have [Qn' [b' [com' ->]]]:= val' q'.
have com'': communication psi phi' q' (Qn, a').
- split; first by apply/cns_cont/com.1; rewrite (gq_cns com.1).
  by rewrite -(coin_map coin); exact/com.2.
have [-> _]:= (cmcn_sing com' com'') => //.
apply/iseg_eq => i ineq; have ->// :=@coin_map _ _ phi' phi.
exact/coin_subl/coin_sym/coin/flatten_subl/drop_subl.
Qed.

Lemma cns_val_cont (psi psi': seq A * Q' -> seq Q + A') phi q' Qn:
  psi \and psi' \coincide_on (build_shapes psi (size Qn) phi q') ->
  consistent psi phi q' Qn -> consistent psi' phi q' Qn.
Proof.
elim: Qn => // K Qn ih /coin_lstn coin cns i ineq.
rewrite -coin; first exact/cns.  
rewrite bs_cns // lstn_iseg; exists (size Qn - i).
split; last by rewrite -(gq_cns (cns_drop cns)) size_drop /= subSS.
by rewrite -subSn //;apply/leq_trans; first apply/leq_subr.
Qed.

Lemma FsM_mod_FM (psi: seq A * Q' -> seq Q + A') phi sf: \F_(shapesM psi) phi sf ->
  continuity_modulus (make_mf (fun psi => \F_(U psi) phi)) psi sf.
Proof.
move => /FsM_spec val q'; have [Qn [a' [com ->]]]:= val q'.
exists a' => psi' coin Fpsiphi /FU_spec val'.
have [Qn' com']:= val' q'.
suff com'': communication psi' phi q' (Qn, a') by have []:= (cmcn_sing com' com'').
split.
- apply/cns_val_cont/com.1; rewrite (bs_cns com.1).
  apply/coin_subl/coin => q /lstn_iseg [n [ineq eq]]; apply/lstn_iseg.
  by exists n; rewrite -(gq_cns (cns_drop com.1)) size_drop subKn.
move/coin_lstn: coin => <-; first exact/com.2.
by apply/lstn_iseg; exists (size Qn); rewrite subnn drop0.
Qed.

Lemma FsM_mod_FqM (psi: seq A * Q' -> seq Q + A') phi sf: \F_(shapesM psi) phi sf ->
  continuity_modulus (make_mf (fun psi => \F_(queriesM psi) phi)) psi sf.
Proof.
move => /FsM_spec val q'.
have [Qn [a' [com ->]]]:= val q'.
exists (flatten Qn) => psi' coin mf /FqM_spec val'.
have [Qn' [b' [com' ->]]]:= val' q'.
f_equal.
suff com'': communication psi' phi q' (Qn, a') by have [->]:= (cmcn_sing com' com'').
split.
apply/cns_val_cont/com.1; rewrite (bs_cns com.1).
- apply/coin_subl/coin => q /lstn_iseg [n [ineq eq]]; apply/lstn_iseg.
  by exists n; rewrite -(gq_cns (cns_drop com.1)) size_drop subKn.
move/coin_lstn: coin => <-; first exact/com.2.
by apply/lstn_iseg; exists (size Qn); rewrite subnn drop0.
Qed.

Lemma FsM_mod_FsM (psi: seq A * Q' -> seq Q + A') phi sf: \F_(shapesM psi) phi sf ->
  continuity_modulus (make_mf (fun psi => \F_(shapesM psi) phi)) psi sf.
Proof.
move => /FsM_spec val q'; have [Qn [a' [com ->]]]:= val q'.
exists (iseg (fun i => (map phi (flatten (drop ((size Qn) - i) Qn)), q')) (size Qn).+1).
move => psi' coin sf' /FsM_spec val'.
have [Qn' [b' [com' ->]]]:= val' q'.
suff com'': communication psi' phi q' (Qn, a') by have [->]:= (cmcn_sing com' com'').
split.
- apply/cns_val_cont/com.1/coin_subl/coin.
  rewrite (bs_cns com.1) => q /lstn_iseg [n [ineq eq]]; apply/lstn_iseg.
  by exists n; rewrite -(gq_cns (cns_drop com.1)) size_drop subKn.
move/coin_lstn: coin => <-; first exact/com.2.
by apply/lstn_iseg; exists (size Qn); rewrite subnn drop0.
Qed.
End continuity.
