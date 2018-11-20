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
  | 0 => M_step psi phi q' nil
  | S n' => match M_rec psi n' phi q' with
	   | inr a' => inr a'
	   | inl K => M_step psi phi q' K
	   end
  end.

Definition M
	   (psi: list A * Q' -> list Q + A')
	   (n: nat)
	   (phi: Q -> A)
	   (q' : Q') :=
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

Lemma M_rec_inl_spec psi n phi q' K:
  M_rec psi n phi q' =  inl K <-> exists (Qn: list (list Q)),
    size Qn = n.+1 /\ K = flatten Qn /\ consistent psi phi q' Qn.
Proof.
split.
- elim: n K => [K | /= n]; first rewrite /=/M_step.
  case E: (psi (nil, q')) => [K' | ]//; rewrite cats0 => [[]] eq.
  exists [:: K]; split => //; split => [ | i ineq]; first by rewrite /= cats0.
  exists K'; split => //; have /eqP ->: i == 0 by rewrite -leqn0.
  by rewrite /= eq.
case E: (M_rec psi n phi q') => [K' | ] // ih K /=.
- have [ | Qn [sze [eq prp E']]]//:= ih K'.
  move: E'; rewrite /M_step; case val: (psi (map phi K', q')) => [K'' | ]// [E'].
  exists ( K'' :: Qn); split => //=; first by rewrite sze.
  split; first by rewrite -eq E'.
  case => [_ | i ineq]; last exact/prp.
  by exists K''; rewrite drop1/= -eq.
elim: n K => [_ [Ln [sze [-> cns]]]/= | /= n ih _ [Ln [sze [-> cns]]]].
- have [ | K [ ]]//:= cns 0; first by rewrite sze.
  rewrite drop1 drop0.
  have -> /=: (behead Ln) = [::] by apply/size0nil; rewrite size_behead sze.
  by rewrite !cats0 /M_step => -> ->/=; rewrite cats0.
rewrite (ih (flatten (drop 1 Ln))).
  have [ | K [val ]]//:= cns 0; first by rewrite sze.
  by rewrite drop0 /M_step val => ->.
exists (drop 1 Ln); split; first by rewrite size_drop sze.
split => // i; rewrite size_drop sze subnS subn0/= => ineq. 
have [ | K' []]:= cns i.+1; first by rewrite sze.
by exists K'; split; [rewrite drop_drop addn1| rewrite !drop_drop !addn1].
Qed.

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
Proof.
by move => cns i ineq; apply/cns.
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

Lemma lstn_nseg n m: List.In n (iseg id m) <-> n < m.
Proof.
elim: m => // m ih.
rewrite leq_eqVlt /=.
split => [[-> | /ih ineq] |/orP [/eqP [->] | ineq]].
- - - by apply/orP; left.
- - by apply/orP; right.
- by left.
by right; apply/ih.
Qed.

Lemma lstn_iseg T (cnt: nat -> T) q m: List.In q (iseg cnt m) <-> exists n, n < m /\ cnt n = q. 
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

Lemma cns_rec psi psi' phi q' Kn Kn' a': psi (map phi (flatten Kn), q') = ! a' -> size Kn <= size Kn' ->
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
  case E: (M_rec psi n phi q') => [L | a']; last by move => eq; apply/ih; rewrite /M /= E eq.
  case E': (psi (map phi L, q')) => [ | a']// [eq].
  have [Ln [<- [eq' prp]]]:= (M_rec_inl_spec psi n phi q' L).1 E.
  by exists Ln; split; last by rewrite -eq' E' eq.
have [Ln [eq prp]]:= val q'.
elim: Ln eq prp => [_ /= eq | L Ln ih prp eq/=]; first by exists 0; rewrite/M/=/M_step eq.
exists (size Ln).+1; rewrite /M/=/M_step.
suff ->: M_rec psi (size Ln) phi q' = inl (flatten (L :: Ln)) by rewrite eq.
by apply M_rec_inl_spec; exists (L :: Ln).
Qed.

Definition mf_dialogue psi phi := make_mf (fun q' a =>
	exists Ln, consistent psi phi q' Ln /\ List.In a (flatten Ln)).

Lemma dlg_com psi phi q' a: mf_dialogue psi phi q' a -> 
	forall Ln a', communication psi phi q' (Ln, a') -> List.In a (flatten Ln).
Proof.
move => [Ln [cns lstn]] Ln' a' [/=cns' eq].
case/orP: (leq_total (size Ln') (size Ln)) => ineq; first by rewrite (cns_rec eq ineq cns').
have sze: size Ln = size (drop (size Ln' - size Ln) Ln') by rewrite size_drop subKn.
move: lstn; rewrite (cns_eq sze cns); last exact/cns_drop.
exact/flatten_subl/drop_subl.
Qed.

Definition mf_queries psi phi:= make_mf(fun q' q =>
  exists Ln, consistent psi phi q' Ln /\ (exists K, psi (flatten Ln, q') = inl K /\ List.In q K)).

Fixpoint gather_queries (psi: seq A * Q' -> seq Q + A') n (phi: B) q' :=
  match n with
  | 0 => nil
  | S n' => let K' := gather_queries psi n' phi q' in
            match psi (map phi K', q') with
            | inr a => K'
            | inl K => K ++ K'
            end
  end.

Definition queriesM psi n phi q' :=
  match M_rec psi n phi q' with

Lemma mf_queries_spec psi phi q' q: mf_queries psi phi q' q <->
       exists n, List.In q (gather_queries psi n phi q').

communication psi phi q' (Ln, a') -> {qL | mf_queries psi phi q' === L2SS qL}.
Proof.
elim: Ln => [comm | L Ln ih comm].
- exists nil.
  rewrite /queries.
  move => [Fphi /FM_val_spec val].
have [Ln]:= val q'.
elim => [ | n ih eq].
rewrite /M/=/M_step; case E: (psi (nil, q')) => [ | a']// eq.
exists nil => a /=; split => // [[n [L] []]].
elim: n => [/= | n ihn eq' lstn]; first by rewrite /= /M_step E => [[]].
apply/ihn => //.
move: eq' => /=.
case: (M_rec psi n phi q') => //.

Lemma dialogue_queries psi phi q' a:
  mf_dialogue psi phi q' a <-> exists q, mf_queries psi phi q' q /\ phi q = a.
Proof.


Lemma queries psi phi: phi*)
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

Lemma psiF_size n phi q' L: M_rec psiF n phi q' = inl L -> n < size L.
Proof.
elim: n L => [L | n ih L /=].
  by rewrite /psiF/=/M_step/=; case E: (mf (listf nil) q') => [ | m /=]; last by move => [<-].
case E: (M_rec psiF n phi q') => [K | ]//.
rewrite /M_step/psiF /=.
case E': (mf (listf K) q' <= size K) => //.
move => [<-]; case eq': (mf (listf K) q') E' => [ | k] //= E'.
rewrite size_cat size_map size_seg subnK; last by rewrite leqW // leqNgt E'.
apply/leq_trans; first by have ineq': n.+1 < (size K).+1; [apply/ih | apply/ineq'].
by rewrite ltnNge E'.
Qed.

Lemma psiF_spec phi q' n:
		(exists k,
		mf (listf (map phi (init_seg k))) q' <= k
		/\
		M_rec psiF n phi q' = inr (FF (listf (map phi (init_seg k))) q'))
	\/
	forall m, m <= n -> exists k, M_rec psiF m phi q' = inl (map phi (init_seg k)).
Proof.
pose phin m := listf (map phi (init_seg m)).
elim: n => [ | n ih].
- rewrite /M_rec/M_step/psiF/=.
  case E: (mf (listf [::]) q' <= 0); first by left; exists 0; split.
  right => m; rewrite leqn0 => /eqP ->; rewrite E /=.
  by case S: (mf (listf nil) q') E => [ | n]// _; exists n.+1; rewrite cats0 iseg_seg.
case: ih => [[] m [] ineq | prp].
  by rewrite /M_rec; left; exists m; split; [apply ineq | rewrite /M_rec b].
have [ | k val]//:= prp n.
case E: (mf (listf (map phi (init_seg k))) q' <= k).
  by left; exists k; split =>//=; rewrite val /M_step /psiF/= size_map size_iseg E.
right => m; rewrite leq_eqVlt; case/orP => [/eqP -> /= | le]; last exact/prp.
rewrite val/M_step/psiF/= size_map size_iseg E.
exists (mf (listf [seq phi i | i <- init_seg k]) q').
f_equal; rewrite -map_cat; f_equal; case: k prp E val => [prp E val | k prp E val].
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
  exact/coin_spec/coin_subl/listfcoin/iseg_subl/ineq.
elim: {2}(mf phi q') (leqnn (mf phi q')) => [ineq | n ih].
- exists 0; rewrite /M/psiF/=/M_step /=.
  have eq': mf (listf nil) q' <= 0 by apply/leq_trans/ineq/leq_trans/(listfmod q' 0).
  by rewrite eq'; f_equal; apply/(FFprop 0).
case: (psiF_spec phi q' n) => [[k [nlk eq]] | prp].
  by exists n.+1; rewrite /M/=eq; f_equal; exact/FFprop/nlk.
rewrite leq_eqVlt => /orP [/eqP eq| ineq]; last exact/ih.
have [ | k val]//:= prp n; exists n.+1; rewrite /M/=val/M_step/psiF/=size_map size_iseg.
suff bnd: mf (listf [seq phi i | i <- init_seg k]) q' <= k by rewrite bnd; f_equal; apply/FFprop.
by apply/leq_trans; first apply/(listfmod q');
rewrite eq; have:= psiF_size val; rewrite size_map size_iseg.
Qed.
End psiF.