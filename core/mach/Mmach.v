From mathcomp Require Import ssreflect seq ssrnat ssrbool eqtype ssrfun.
From rlzrs Require Import all_mf.
Require Import all_cont exec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section universal_machine.
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

Lemma cns0 psi phi q': consistent psi phi q' nil.
Proof. done. Qed.

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

Lemma rev_eq T (L L': seq T): rev L = rev L' <-> L = L'.
Proof. by split; first rewrite -{2}(revK L) -{2}(revK L'); move ->. Qed.

Lemma rcons_eq T L L' (a a': T): rcons L a = rcons L' a' <-> L = L' /\ a = a'.
Proof.
split; last by case => -> ->.
by rewrite -(revK (rcons L a)) -(revK (rcons L' a')) rev_eq !rev_rcons => [[-> /rev_eq ->]].
Qed.

Lemma cat_eq_right T (L L' K: seq T): L ++ K = L' ++ K <-> L = L'.
Proof.
elim: K L L' => [L L' | a K ih L L']; [rewrite !cats0 | split => [ | ->]] => //.
by rewrite -!cat_rcons (ih (rcons L a) (rcons L' a)) rcons_eq => [[->]].
Qed.

Lemma lstn_iseg T (cnt: nat -> T) q m:
  List.In q (iseg cnt m) <-> exists n, n < m /\ cnt n = q. 
Proof.
split => [ | [n []]]; first exact/iseg_ex; elim: m => // m ih.
by rewrite leq_eqVlt; case/orP => [/eqP [<-]| ]; [left | right; apply/ih].
Qed.

Lemma coin_cns psi psi' phi q' Kn:
  psi \and psi' \coincide_on (iseg (fun i => (map phi (flatten (drop i.+1 Kn)), q')) (size Kn)) ->
  consistent psi phi q' Kn -> consistent psi' phi q' Kn.
Proof.
elim: Kn => // K Kn ih /coin_lstn coin cns i ineq.
rewrite -coin; first exact/cns.  
by rewrite lstn_iseg; exists i.
Qed.

Lemma cns_eq psi psi' phi q' Kn Kn': size Kn = size Kn' ->
   psi \and psi' \coincide_on (iseg (fun i => (map phi (flatten (drop i.+1 Kn)), q')) (size Kn)) ->
	consistent psi phi q' Kn -> consistent psi phi q' Kn' -> Kn = Kn'.
Proof.
move: {2}(size Kn) (leqnn (size Kn)) => n.
elim: n Kn Kn' => [[[] | []] | n ih [[] | K Kn []]]// K' Kn' ineq [eq] /coin_lstn coin cns cns'.
have eq': Kn = Kn'.
- rewrite (ih Kn Kn') => //[ | i ineq' | i ineq']; try exact/cns; try exact/cns'.
  apply/coin_lstn => q.
  rewrite lstn_iseg => [[k [ineq' <-]]].
  apply/coin; rewrite lstn_iseg.
  by exists k.+1; rewrite -addn1 -drop_drop drop1 /= addn1.
rewrite eq'; f_equal.
have [ | K'' []]//=:= cns 0; rewrite drop0 => val /cat_eq_right ->.
have [ | K''' []]//=:= cns' 0; rewrite drop0 => val' /cat_eq_right ->.
by move: val val'; rewrite eq' => -> [->].
Qed.

Lemma cns_rec psi psi' phi q' Kn Kn' a': psi (map phi (flatten Kn), q') = ! a' ->
  size Kn <= size Kn' ->
  psi \and psi' \coincide_on (iseg (fun i => (map phi (flatten (drop i Kn)), q')) (size Kn).+1) -> 
	consistent psi phi q' Kn -> consistent psi' phi q' Kn' -> Kn = Kn'.
Proof.
move => val; elim: Kn' => [ | K' Kn' ih].
  by rewrite leqn0 => /eqP eq; rewrite (size0nil eq).
rewrite leq_eqVlt; case /orP => [/eqP eq | ineq /coin_lstn coin cns cns'].
- case: Kn eq ih val => // K Kn [sze] ih val /coin_lstn coin cns cns'.
  have cns'': consistent psi' phi q' (K :: Kn).
  - apply/coin_cns/cns/coin_lstn => q /lstn_iseg [k [ineq eq]].
    by apply/coin/lstn_iseg; exists k.+1.
  apply/cns_eq/cns'/cns''/coin_sym; first by rewrite /= sze.
  exact/coin_ref.
have [ | K ]//:= cns' 0.
have eq: Kn = Kn'.
- by apply/ih => //; [ apply/coin_lstn/coin | apply/cns_cons/cns'].
rewrite -coin; last by apply/lstn_iseg; exists 0; rewrite drop1 drop0 /= eq.
by rewrite drop1 /= -eq val; case.
Qed.

Definition communication psi (phi: B) := make_mf (fun (q': Q') Kna' =>
	let Kn:= Kna'.1 in let a':= Kna'.2 in consistent psi phi q' Kn /\ psi (map phi (flatten Kn), q') = !a').

Lemma cmcn_unique psi phi: (communication psi phi) \is_singlevalued.
Proof.
move => q' [Ln a'] [Ln' b'] [/=cns val] [cns' val'].
case/orP: (leq_total (size Ln) (size Ln')) => ineq.
- move: val'; have <-: Ln = Ln' by apply/cns_rec/cns'/cns/coin_ref/ineq/val.
  by rewrite val => [[->]].
move: val; have <-: Ln' = Ln by apply/cns_rec/cns/cns'/coin_ref/ineq/val'.
by rewrite val' => [[->]].
Qed.

Lemma FM_val_spec psi phi Fphi: \F_(M psi) phi Fphi <->
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
have [Ln [/=eq prp]]:= val q'.
exists (size Ln).+1.
rewrite /M/=/M_step.
rewrite (M_rec_inl_spec psi (size Ln) phi q' (flatten Ln)).2.
- by rewrite prp.
by exists Ln.
Qed.

Fixpoint gather_queries psi n phi q':=
  match M_rec psi n phi q' with
  | inr a' => match n with
              | 0 => nil
              | S n' => gather_queries psi n' phi q'
              end
  | inl K => K
  end.

Lemma unfold_gq psi n phi q': gather_queries psi n phi q' =
  match M_rec psi n phi q' with
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
case E: (M_rec psi n phi q') => [K | a'] //; rewrite /M_step.
by case: (psi (map phi K, q')) => // K' lstn; apply/lstn_app; right.
Qed.

Lemma gq_subl psi n m phi q': n <= m ->
  (gather_queries psi n phi q') \is_sublist_of (gather_queries psi m phi q').
Proof.  
elim: m n => [n | m ih n]; first by rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt; case/orP => [/eqP -> | ineq]//.  
exact/subl_trans/gq_mon/ih.
Qed.

Lemma M_rec_spec psi n phi q':
  M_rec psi n phi q' = ?(gather_queries psi n phi q') \/ exists a', M_rec psi n phi q' = !a'.
Proof.
elim: n => [ | n [/= -> | [a' eq]]]; [left | | right; exists a' => /=; rewrite eq] => //.
by case E: (M_step psi phi q' (gather_queries psi n phi q')) => [K | a']; [left | right; exists a'].
Qed.

Lemma gq_cns psi phi q' Qn: consistent psi phi q' Qn ->
  gather_queries psi (size Qn) phi q' = flatten Qn.
Proof.
elim: Qn => // K Qn ih cns /=.
rewrite ih; last exact/cns_cons/cns.
have [ | K' [/=val eq]]//:= cns 0.
rewrite (M_rec_inl_spec psi (size Qn) phi q' (flatten Qn)).2.
- by rewrite drop0 in val; rewrite /M_step val eq drop0.
by exists Qn; do 2 split => //; apply/cns_cons/cns.
Qed.

Lemma gq_size psi phi q' Qn n: Qn <> nil ->
  (exists a', communication psi phi q' (Qn, a')) -> gather_queries psi n phi q' = flatten Qn -> n = size Qn.
Proof.
case: Qn => // K Qn _ prp eq.

- rewrite -gq in val; have [ | K'[]]//:= cns 0.
  rewrite /= drop0; suff ->: flatten Qn = nil by rewrite val.
  by elim: (K) gq => //.
have [ | K']//:= cns 0.    
rewrite /=.
rewrite /M_step.
case: (M_rec_spec psi n phi q') => [-> | ].
  case: Qn cns val => // K Qn cns /= val eq.
suff eq': flatten Qn = nil.
rewrite eq' cats0 in eq.
have [ | K' []]//:= cns 0.
by rewrite -eq /= in val; rewrite /= drop0 val.

Lemma gq_spec psi phi q' K:
  (exists n, gather_queries psi n phi q' = K) <->
      exists Qn, consistent psi phi q' Qn /\ K = flatten Qn.
Proof.
split => [[n] | [Qn [cns eq]]]; last by exists (size Qn); rewrite eq gq_cns.
rewrite unfold_gq.
elim: n K => [K | n /=ih K]; first by rewrite /= => <-; exists nil.
case E: (M_rec psi n phi q') ih => [K' | a'] => [ ih | ih gq].
- rewrite /M_step/=; case val: (psi (map phi K', q')) => [K'' | ]// eq.
  - have [ | Qn [cns eq']]//:= ih K'.
    exists (K'' :: Qn); split; last by rewrite -eq /= -eq'.
    case => [ | i ineq]; last by apply/cns.
    by exists K''; rewrite drop1/=; split; first by rewrite -eq'.
  by apply/ih; rewrite unfold_gq E in eq.
apply/ih; case: (n) gq E => [ | k].
- by rewrite /M_step/=; case: (psi (nil, q')).
rewrite /= unfold_gq; case: (M_rec psi k phi q') => [K' | b'] //.
by case: (M_step psi phi q' K') => //.
Qed.

Lemma coin_map (phi phi': B) K:
  phi \and phi' \coincide_on K -> map phi K = map phi' K.
Proof. by elim: K => // q K ih /=[-> coin]; rewrite ih. Qed.

Lemma M_rec_cont psi n phi phi' q':
  phi \and phi' \coincide_on (gather_queries psi n phi q') ->
    M_rec psi n phi q' = M_rec psi n phi' q'.
Proof.
elim: n => // n ih /=.
case: (M_rec_spec psi n phi q') => [eq | [a' val]]; last first.
- by rewrite val => coin; rewrite -ih//val.
rewrite eq /M_step.
case val: (psi (map phi (gather_queries psi n phi q'), q')) => [K' | a'].
- rewrite coin_cat; case => coin coin'.
  by rewrite -ih // eq -(coin_map coin') val.
by move => coin; rewrite -ih// eq -(coin_map coin) val.
Qed.

Lemma cns_cont psi phi phi' q' Qn: consistent psi phi q' Qn ->
  phi \and phi' \coincide_on (gather_queries psi (size Qn) phi q') ->
    consistent psi phi' q' Qn.
Proof.
elim: Qn => // K Qn ih cns /=.
have rec:= (M_rec_inl_spec psi (size Qn) phi q' (flatten Qn)).2.
rewrite rec/M_step; last by exists Qn; do 2 split => //; apply/cns_cons/cns.
case val: (psi (map phi (flatten Qn), q')) => [K' | a']; last first.
- by have [ | K'' [/=]]//:= cns 0; rewrite drop0 val.
rewrite coin_cat => [[coin coin']] [_/= | i].
- rewrite drop0 -(coin_map coin').
  by have prp:= cns 0; rewrite /= drop0 in prp; apply/prp.
apply/ih=>//; [by apply/cns_cons/cns | rewrite unfold_gq rec//].
by exists Qn; do 2 split => //; apply/cns_cons/cns.
Qed.

Lemma cmcn_cont psi phi phi' q' Qn a':
  phi \and phi' \coincide_on (gather_queries psi (size Qn) phi q') ->
  communication psi phi q' (Qn, a') -> communication psi phi' q' (Qn, a').
Proof.
move => coin [cns val]; split; first exact/cns_cont/coin/cns.
by rewrite -(gq_cns cns) -(coin_map coin) gq_cns.
Qed.

Definition queriesM psi n phi q' :=
  match M_rec psi n phi q' with
  | inl K => None
  | inr a' => Some (gather_queries psi n phi q')
  end.

Lemma qM_mon psi: (queriesM psi) \is_monotone.
Proof.
by move => phi phifd q' n; rewrite /queriesM /=; case: (M_rec psi n phi q').
Qed.

Lemma qM_spec psi phi mf: \F_(queriesM psi) phi mf <->
  forall q', exists Qn a', communication psi phi q' (Qn, a')
                           /\
                           gather_queries psi (size Qn) phi q' = mf (q').
Proof.
split => [mod q' | prp q'].
- have [n]:= mod q'; rewrite /queriesM.
  case val: (M_rec psi n phi q') => [ | a'] // [eq].
  have [ | Qn [cns flt]]:= (gq_spec psi phi q' (mf q')).1; try by exists n.
  have sze: size Qn <= n.
  - rewrite leqNgt; apply /negP => lt.
    case E: (size Qn) => [ | k]; first by rewrite E in lt.
    have [ | K [vl eq']]:= cns (k - n); first by rewrite E; apply/leq_subr.
    rewrite (M_rec_inl_spec psi n phi q' (flatten (drop (k.+1-n) Qn))).2 in val => //.
    exists (drop (k.+1 - n) Qn); split; last split => //; last by apply/cns_drop.
    by rewrite size_drop E subKn // -E; apply/leq_trans/lt.  
  exists Qn; exists a'; split; first split => //; last by rewrite gq_cns.
  rewrite flt in eq; move: flt => _ /=; rewrite -eq.
  have prp: forall K, psi (map phi (flatten Qn), q') = ? K -> K = nil.
  - rewrite -eq => K; move: val eq; rewrite -(subnK sze).
    elim (n - size Qn) => [ | k ih]; last rewrite addSn /=.
    - rewrite (M_rec_inl_spec psi (size Qn) phi q' (flatten Qn)).2 //.
      by exists Qn.
    case: (M_rec_spec psi (k + size Qn) phi q') => [-> | [b' eq]]; last first.
    - by rewrite eq => eq' gq ps; apply/ih => //; first by rewrite -eq'.
    rewrite /M_step.
    case E: (psi (map phi (gather_queries psi (k + size Qn) phi q'), q')) => [ | b'] // eq'.
    by rewrite E.
  have prp': forall k, gather_queries psi (k + size Qn) phi q' = flatten Qn.
  - elim => [ | k ih]; [by rewrite add0n; apply/gq_cns | rewrite addSn /=].
    case: (M_rec_spec psi (k + size Qn) phi q') => [-> | [_ ->]]//.
    rewrite /M_step ih; case E: (psi (map phi (flatten Qn), q')) => [K' | ]//.
    by rewrite (prp K') //.
  move: val; rewrite -(subnK sze).
  elim: (n - size Qn) => [ | k ih]; last rewrite addSn/=.
  - rewrite add0n (M_rec_inl_spec psi (size Qn) phi q' (flatten Qn)).2 //.
    by exists Qn.
  case: (M_rec_spec psi (k + size Qn) phi q') => [E | [b' eq']].
    rewrite E /M_step.
    case E': (psi (map phi (gather_queries psi (k + size Qn) phi q'), q')) => [K | b'] // <- //.
  by rewrite eq' => eq''; apply ih; rewrite -eq''.
have [Qn [a' [[com val] gq]]]:= prp q'; exists (size Qn).+1.
rewrite /queriesM /=/M_step.
rewrite (M_rec_inl_spec psi (size Qn) phi q' (flatten Qn)).2.
- by rewrite val; f_equal.
by exists Qn.
Qed.

Lemma qM_mod_FM psi phi mf:
  \F_(queriesM psi) phi mf -> continuity_modulus \F_(M psi) phi mf.
Proof.
move => /qM_spec mod q'.
have [Qn [a' [[/=cns val] gq]]]:= mod q'.  
exists a' => phi'/coin_agre coin Fphi' /FM_val_spec Fphi'Fphi'.
have [Qn' com]:= Fphi'Fphi' q'.
suff com': communication psi phi' q' (Qn, a') by have [_ ->]:= (cmcn_unique com com').
split; first by apply/cns_cont; [exact/cns | rewrite gq].    
by rewrite -(gq_cns cns) gq -(coin_map coin) -gq (gq_cns cns).
Qed.

Lemma qM_mod_qM (psi: seq A * Q' -> seq Q + A') phi mf:
  \F_(queriesM psi) phi mf -> continuity_modulus \F_(queriesM psi) phi mf.
Proof.
move => /qM_spec val q'; have [Qn [a' [com eq]]]:= val q'.  
exists (gather_queries psi (size Qn) phi q') => phi' /coin_agre coin mf' /qM_spec mf'val.
have [Qn' [b' [com' eq']]]:= mf'val q'; move: mf'val => _.
rewrite -eq' (gq_cns com'.1) (gq_cns com.1) /=; f_equal.
suff prp: communication psi phi' q' (Qn, a') by have []:= cmcn_unique com' prp.
split; first by apply/cns_cont; [exact/com.1 | rewrite eq].
by rewrite -(gq_cns com.1) eq -(coin_map coin)-eq (gq_cns com.1) com.2.
Qed.

Fixpoint build_shapes psi n phi q':=
  match M_rec psi n phi q' with
  | inr a' => match n with
              | 0 => nil
              | S n => build_shapes psi n phi q'
              end
  | inl K => iseg (fun i => (map phi (gather_queries psi i phi q'), q')) n
  end.

Lemma unfold_bs psi n phi q': build_shapes psi n phi q' =
  match M_rec psi n phi q' with
  | inr a' => match n with
              | 0 => nil
              | S n => build_shapes psi n phi q'
              end
  | inl K => iseg (fun i => (map phi (gather_queries psi i phi q'), q')) n
  end.
Proof. by case: n. Qed.

Lemma bs_mon psi n phi q':
  (build_shapes psi n phi q') \is_sublist_of (build_shapes psi n.+1 phi q').
Proof.
move => q/=; rewrite unfold_bs.
case E: (M_rec psi n phi q') => [K | a'] //; rewrite /M_step.
by case: (psi (map phi K, q')) => // K' lstn; right.
Qed.

Lemma bs_subl psi n m phi q': n <= m ->
  (build_shapes psi n phi q') \is_sublist_of (build_shapes psi m phi q').
Proof.  
elim: m n => [n | m ih n]; first by rewrite leqn0 => /eqP ->.
by rewrite leq_eqVlt; case/orP => [/eqP -> | ineq]//; apply/subl_trans/bs_mon/ih.
Qed.

Lemma bs_cns psi phi q' Qn: consistent psi phi q' Qn ->
  build_shapes psi (size Qn) phi q' =  iseg (fun i => (map phi (gather_queries psi i phi q'), q')) (size Qn).
Proof.
elim: Qn => // K Qn ih cns /=.
rewrite ih; last exact/cns_cons/cns.
have [ | K' [/=val eq]]//:= cns 0.
rewrite (M_rec_inl_spec psi (size Qn) phi q' (flatten Qn)).2.
- by rewrite /M_step -(drop0 Qn) val.
by exists Qn; do 2 split => //; apply/cns_cons/cns.
Qed.

Require Import FunctionalExtensionality.

Lemma bs_spec psi phi q' Ln: build_shapes psi (size Ln) phi q' = Ln <->
   exists Qn, consistent psi phi q' Qn /\ Ln = iseg (fun i => (map phi (gather_queries psi i phi q'), q')) (size Qn).
Proof.
split => [[] | [Qn [cns ->]]]; last by rewrite size_iseg (bs_cns cns).
rewrite unfold_bs.
case: (M_rec_spec psi (size Ln) phi q') => [E | [a' E]]; rewrite E => <-.
have[ | Qn [cns val]]:= (gq_spec psi phi q' (gather_queries psi (size Ln) phi q')).1; first by exists (size Ln).
exists Qn; split => //; f_equal.

rewrite E.
have:= gq_spec.

case E: (M_rec psi (size Ln) phi q') => [K' | a'] => [ ih | ih gq].
- rewrite /M_step/=; case val: (psi (map phi K', q')) => [K'' | ]// eq.
  - have [ | Qn [cns eq']]//:= ih K'.
    exists (K'' :: Qn); split; last by rewrite -eq /= -eq'.
    case => [ | i ineq]; last by apply/cns.
    by exists K''; rewrite drop1/=; split; first by rewrite -eq'.
  by apply/ih; rewrite unfold_gq E in eq.
apply/ih; case: (n) gq E => [ | k].
- by rewrite /M_step/=; case: (psi (nil, q')).
rewrite /= unfold_gq; case: (M_rec psi k phi q') => [K' | b'] //.
by case: (M_step psi phi q' K') => //.
Qed.

Lemma size_bs psi phi q' n: size (build_shapes psi n phi q') <= n.
Proof.
elim: n => // n ih /=.
case: (M_rec psi n phi q') => [K | a']; last exact/leqW.
case: (M_step psi phi q' K) => [K' | a'] /=; last exact/leqW.
by rewrite size_iseg.
Qed.

Proof.
elim: Ln => [ | L Ln ih /=]; first by split; first by exists nil.
case: (M_rec_spec psi (size Ln) phi q') => [eq | [a' eq]]; rewrite eq.
case: (M_step psi phi q' (gather_queries psi (size Ln) phi q')) => [K | a'] //; last first.
rewrite -ih.2 //.

rewrite unfold_bs eq; case => <- eq'.


exists (gather_queries psi (size Ln) phi q' :: Qn

  Definition shapesM psi n phi q' :=
  match M_rec psi n phi q' with
  | inl K => None
  | inr a' => Some (build_shapes psi n phi q')
  end.

Lemma sM_spec psi phi sf: \F_(shapesM psi) phi sf <->
  forall q', exists Qn a', communication psi phi q' (Qn, a') /\ sf q' = iseg (fun i => (map phi (flatten (drop i Qn)), q')) (size Qn).+1.
Proof.
split => [val q' | ].
have [n]:= val q'.
rewrite /shapesM.
case: (M_rec_spec psi n phi q') => [eq | [a' eq]]; rewrite eq//; case.
case: n eq => // n /=.
case: (M_rec psi n phi q') => [_ -> | _ _] // eq.
exists (iseg (fun i => gather_queries psi i phi q') n); exists a'.
split.
- rewrite /shapesM /=; split.
  have:= gq_spec psi phi q'.
  
Require Import FunctionalExtensionality.

Lemma qM_mod_shps psi phi mf:
  \F_(queriesM psi) phi mf -> continuity_modulus (shapes psi) phi mf.
Proof.
move => /qM_spec mod q'; have [Qn [a' [com eq]]]:= mod q'; move: mod => _.
exists (iseg (fun i => (map phi (flatten (drop i Qn)), q')) (size Qn).+1).
move => phi' /coin_agre coin lf val.
have [Qn' [b' [com' ->]]] := val q'.
have com'': communication psi phi' q' (Qn, a') by apply/cmcn_cont/com; rewrite eq.
have [-> _]:= cmcn_unique com' com''.
f_equal; apply/functional_extensionality => i; f_equal.
rewrite -eq gq_cns in coin; last exact/com.1.
exact/coin_map/coin_subl/coin_sym/coin/flatten_subl/drop_subl.
Qed.

Lemma shps_mod_FM psi phi sf: shapes psi phi sf ->
  continuity_modulus (make_mf (fun psi => \F_(M psi) phi)) psi sf.
Proof.
move => shps q'; have [Qn [a' [com eq]]]:= shps q'.  
exists a' => psi' /coin_agre coin Fpsiphi /FM_val_spec val.
have [Qn' com']:= val q'.
have com'': communication psi phi q' (Qn', Fpsiphi q').
apply cmcn_val_cont.


Lemma FM_ucont: exists (Mf Lf: _ -> _ -> _ -> Prop), forall (psi: seq A * Q' -> seq Q + A') phi mf lf,
      phi \from dom \F_(M psi) -> Mf psi phi mf -> Lf psi phi lf ->
               continuity_modulus \F_(M psi) phi mf /\
               continuity_modulus (make_mf (Mf psi)) phi mf /\
               continuity_modulus (make_mf (Lf psi)) phi mf /\
               continuity_modulus (make_mf (fun psi => \F_(M psi) phi)) psi lf /\
               continuity_modulus (make_mf (fun psi => Mf psi phi)) psi lf /\
               continuity_modulus (make_mf (fun psi => Lf psi phi)) psi lf.
Proof.
exists (fun psi phi mf => \F_(queriesM psi) phi mf).
exists (fun psi phi lf => forall Qn a' q', communication psi phi q' (Qn, a') -> lf q' = iseg (fun i => (map phi (flatten (drop i Qn)), q')) (size Qn).+1).
move => psi phi mf lf [Fpsiphi /FM_val_spec val] /queriesM_spec mod mod'.
split.
- apply/queriesM_mod; rewrite queriesM_spec => q'.
  have [Qn com]:= val q'; have [Qn'' [a' [com'' eq]]]:= mod q'.
  exists Qn; exists (Fpsiphi q'); split => //.
  by have [-> _]: (Qn, Fpsiphi q') = (Qn'', a') by apply/cmcn_unique/com''/com.
split; last split; last split; last split;
  move => q'; have [Qn com] := val q'; have [Qn'' [a' [com'' eq]]]:= mod q'.
- exists (gather_queries psi (size Qn) phi q') => phi' /coin_agre coin mf' /queriesM_spec mf'val.
  have [Qn' [b' [com' eq']]]:= mf'val q'; move: mf'val => _.
  rewrite -eq' (gather_queries_cns com'.1) (gather_queries_cns com.1) /=; f_equal.
  suff prp: communication psi phi' q' (Qn, a') by have []:= cmcn_unique com' prp.
  have [-> _]:= cmcn_unique com com''.
  split; first by apply/cns_cont; [exact/com''.1 | rewrite eq].
  rewrite -(gather_queries_cns com''.1) eq -(coin_map coin).
  by rewrite -eq (gather_queries_cns com''.1) com''.2.
- exists (lf q') => phi' /coin_agre coin lf' lf'val.
  rewrite (lf'val Qn (Fpsiphi q')) //.
  rewrite (mod' Qn (Fpsiphi q')) //.
  + f_equal; apply functional_extensionality => i; f_equal.
    apply/coin_map/coin_subl/coin_sym/coin.
    rewrite -eq (gather_queries_cns com''.1) (cmcn_unique com'' com).
    exact/flatten_subl/drop_subl.
  rewrite (cmcn_unique com com'').
  split; first by apply/cns_cont; [exact/com''.1 | rewrite eq].
  rewrite -(gather_queries_cns com''.1) eq -(coin_map coin).
  by rewrite -eq (gather_queries_cns com''.1) com''.2.
- exists (Fpsiphi q') => psi' /coin_agre coin Fpsiphi' /FM_val_spec val'.
  have [eqQ eq']: (Qn'', a') = (Qn, Fpsiphi q') by apply/cmcn_unique/com/com''.
  rewrite eqQ in eq; move: a' eqQ eq' com'' => _ _ _ _.
  have [Qn' com']:= val' q'; move: coin; rewrite (mod' Qn (Fpsiphi q')) // => /coin_lstn coin.
  suff prp: communication psi phi q' (Qn, Fpsiphi' q') by have []:= cmcn_unique com prp.
  split; first exact/com.1.
  rewrite coin; last by apply/lstn_iseg; exists 0; rewrite drop0.
  rewrite -com'.2 /=; do 4 f_equal.
  case/orP: (leq_total (size Qn) (size Qn')) => ineq.
  + by apply/cns_rec/com'.1/com.1/coin_lstn/coin; first exact/com.2. 
  admit.
- exists (mf q').
  admit.
- exists (lf q').
  admit.
Admitted.

End universal_machine.

Section psiF.
Context (Q Q' A A': Type).
Notation B := (Q -> A).
Notation B' := (Q' -> A').
Context (cnt: nat -> Q).
Notation init_seg := (iseg cnt).
Notation segment :=(segment cnt).
Context (listf: seq A -> B).
Context (mf: B -> Q' -> nat).
Context (FF: B -> B').

Definition psiF (Lq': seq A * Q') :=
  let phi:= listf Lq'.1 in let n:= size Lq'.1 in let q' := Lq'.2 in
	if mf phi q' <= n then inr (FF phi q') else (inl (segment n (mf phi q').-1)).

Lemma psiF_size n phi q' L: M_rec psiF n phi q' = inl L -> n <= size L.
Proof.
elim: n L => [L | n ih L /=] //.
case E: (M_rec psiF n phi q') => [K | ]//.
rewrite /M_step/psiF /=.
case E': (mf (listf (map phi K)) q' <= size (map phi K)) => //.
move => [<-]; case eq': (mf (listf (map phi K)) q') E' => [ | k] //= E'.
rewrite size_map in eq' E'.
rewrite size_cat size_map size_seg subnK; last by rewrite leqW // leqNgt E'.
apply/leq_trans; first by have ineq': n.+1 <= (size K).+1; [apply/ih | apply/ineq'].
by rewrite ltnNge E'.
Qed.

Lemma psiF_spec phi q' n:
		(exists k,
		mf (listf (map phi (init_seg k))) q' <= k
		/\
		M_rec psiF n phi q' = inr (FF (listf (map phi (init_seg k))) q'))
	\/
	forall m, m <= n -> exists k, M_rec psiF m phi q' = inl (init_seg k).
Proof.  
elim: n => [ | n ih]; first by right => m; rewrite leqn0 => /eqP ->; exists 0.
case: ih => [[] m [] ineq | prp].
  by rewrite /M_rec; left; exists m; split; [apply ineq | rewrite /M_rec b].
have [ | k val]//:= prp n.
case E: (mf (listf (map phi (init_seg k))) q' <= k).
  by left; exists k; split =>//=; rewrite val /M_step /psiF/= size_map size_iseg E.
right => m; rewrite leq_eqVlt; case/orP => [/eqP -> /= | le]; last exact/prp.
rewrite val/M_step/psiF/= size_map size_iseg E.
exists (mf (listf [seq phi i | i <- init_seg k]) q').
f_equal; case: k prp E val => [prp E val | k prp E val].
  by rewrite cats0; case: (mf (listf [seq phi i | i <- init_seg 0]) q') E => // h E; rewrite iseg_seg.
by rewrite iseg_cat_seg // ltnNge E.
Qed.

Lemma MpsiF_spec (F: B ->> B') phi: phi \from dom F ->
	(forall n, listf (map phi (init_seg n)) \from dom F) ->
	(forall n, (listf (map phi (init_seg n))) \and phi \coincide_on (init_seg n)) ->
	(forall q' n, mf phi q' <= n -> mf (listf (map phi (init_seg n))) q' <= mf phi q') ->
	(forall psi, psi \from dom F -> continuity_modulus F psi (fun q' => init_seg (mf psi q'))) ->
	FF \is_choice_for F -> forall Fphi, F phi Fphi -> \F_(M psiF) phi Fphi.
Proof.
move => phifd listfdom listfcoin listfmod mod icf Fphi FphiFphi q'.
pose phin n := (listf (map phi (init_seg n))).
have FFprop: forall n, mf (phin n) q' <= n -> FF (phin n) q' = Fphi q' => [n ineq | ].
- have [ | a' crt]:= mod (phin n) _ q'; first exact/listfdom; have [Fphik FphikFphik]:= listfdom n.
  rewrite [RHS](crt phi) => //; first by rewrite (crt (phin n)) //; apply/icf/FphikFphik.
  exact/coin_agre/coin_subl/listfcoin/iseg_subl/ineq.
elim: {2}(mf phi q') (leqnn (mf phi q')) => [ineq | n ih].
- exists 1; rewrite /M/=/M_step/=/psiF /=.
  have eq': mf (listf nil) q' <= 0 by apply/leq_trans/ineq/leq_trans/(listfmod q' 0).
  by rewrite eq'; f_equal; apply/(FFprop 0).
case: (psiF_spec phi q' n.+1) => [[k [nlk eq]] | prp].
  by exists n.+1; rewrite /M eq; f_equal; exact/FFprop/nlk.
rewrite leq_eqVlt => /orP [/eqP eq| ineq]; last exact/ih.
have [ | k val]//:= prp n.+1.
exists n.+2; have:= val; rewrite /M/= =>  ->; rewrite /M_step/psiF/=size_map size_iseg.
suff bnd: mf (listf [seq phi i | i <- init_seg k]) q' <= k by rewrite bnd; f_equal; apply/FFprop.
apply/leq_trans; first apply/(listfmod q'); rewrite eq.
- by have:= psiF_size val; rewrite size_iseg.
by have:= psiF_size val; rewrite size_iseg.
Qed.
End psiF.