From mathcomp Require Import ssreflect seq ssrnat ssrbool eqtype ssrfun.
From mf Require Import all_mf.
Require Import all_cont FMop PhiN Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section U_machine.
  (* Q: Questions, A: Answers *)
  Context (Q Q' A A' : Type).
  (* B: Baire space *)
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Context (psi: seq (Q * A) * Q' -> seq Q + A').

  (* Construct a partial function F from B to B' by iterating a function psi of the type as above.
     That is: Start with L =[::] and while psi(L,q') returns something of the form inl K repeat 
     doing L:= map phi K ++ L and calling psi on the updated list and q'. If psi returns inr a'
     at some point, then interpret a' as the return-value of F(phi) on input q'.
     Note that this means that the list L is partial information about the functional input of F.
     Since this chunk of information is finite, the produced operator is always continuous. All
     continuous operators are produced in this way (the proof of this is in the file Ucont.v).
     Since F is partial, it is not defined directly. Instead we first define a U that takes psi
     to something that can be interpreted through the operator assignment from FMop.v. *)
  
  Definition U_step phi q' L :=
    match psi (L, q') with
    | inr a' => inr a'
    | inl K => inl (F2GL phi K ++ L)
    end.

  Fixpoint U_rec phi q' n :=
    match n with
    | 0 => inl nil
    | S n' =>
      match U_rec phi q' n' with
      | inr a' => inr a'
      | inl L => U_step phi q' L
      end
    end.

  Lemma U_recS phi q' n: U_rec phi q' n.+1 =
                         match U_rec phi q' n with
                         | inr a' => inr a'
                         | inl L => U_step phi q' L
                         end.
  Proof. done. Qed.

  Definition U (phi: Q -> A) (nq' : nat * Q') :=
    match U_rec phi nq'.2 nq'.1 with
    | inl _ => None
    | inr a' => Some a'
    end.

  Lemma U_mon: U \is_monotone.
  Proof. by rewrite /U => phi q' n /=; case: (U_rec phi q' n). Qed.

  Definition F_U := get_pf U.
  Context (phi: Q -> A).

  Fixpoint consistent q' Ks :=
    match Ks with
    | nil => True
    | K :: Ks' => psi (F2GL phi (flatten Ks'), q') = inl K /\ consistent q' Ks'  end.
  
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

  Lemma cns_cons q' K Ks:
    consistent q' (K::Ks) -> consistent q' Ks.
  Proof. by case. Qed.

  Lemma cns_spec q' Ks:
    consistent q' Ks <->
    forall i, i < size Ks -> exists K,
        psi (F2GL phi (flatten (drop i.+1 Ks)), q') = inl K
        /\
        flatten (drop i Ks) = K ++ flatten (drop i.+1 Ks).
  Proof.
    elim: Ks => // K Ks ih.
    split => [[val /ih cns] | prp]; first by case; last exact/cns; exists K; rewrite /= drop0.
    split; first by have [ | K' [ ]]//=:= prp 0; rewrite drop0 => -> /cat_eq_r ->.
    by apply/ih => i ineq; apply/prp.
  Qed.

  Lemma cns_drop q' n Ks: consistent q' Ks -> consistent q' (drop n Ks).
  Proof.
    move => /cns_spec cns; apply/cns_spec => i; rewrite size_drop => ils.
    have [ | K []]:= cns (i + n); first by rewrite addnC -ltn_subRL.
    by exists K; rewrite !drop_drop addSn.
  Qed.

  Lemma cns_eq q' Ks Ks': size Ks = size Ks' ->
	                  consistent q' Ks -> consistent q' Ks' -> Ks = Ks'.
  Proof.  
    move: {2}(size Ks) (leqnn (size Ks)) => n.
    elim: n Ks Ks' => [[[]|[]] | n ih [[] | K Ks []]]// K' Ks' ineq [sze] /=[val cns] [val' cns'].
    by move: val'; rewrite -(ih Ks Ks') // val; case => ->.
  Qed.

  Lemma cns_val_eq q' Ks Ks' a':
    psi (F2GL phi (flatten Ks), q') = inr a' -> size Ks <= size Ks' ->
    consistent q' Ks -> consistent q' Ks' -> Ks = Ks'.
  Proof.
    move => val; elim: Ks' => [ | K' Kn' ih].
    - by rewrite leqn0 => /eqP eq; rewrite (size0nil eq).
    rewrite leq_eqVlt; case /orP => [/eqP eq | ineq cns /cns_spec cns'].
    - by case: Ks eq ih val => // K Kn [sze] ih val; apply/cns_eq; rewrite /= sze.
    have [ | K ]//:= cns' 0.
    have <-: Ks = Kn' by apply/ih/cns_cons/cns_spec/cns'.
    by rewrite drop1 /= val; case.
  Qed.

  Lemma F2GL_cat K K': F2GL phi (K ++ K') = F2GL phi K ++ F2GL phi K'. 
  Proof. by rewrite /F2GL map_cat zip_cat // size_map. Qed.

  Lemma cns_U_rec q' Ks: consistent q' Ks -> U_rec phi q' (size Ks) = inl (F2GL phi (flatten Ks)).
  Proof.
    elim: Ks => // K Ks ih /cns_spec cns /=.
    rewrite /U_step ih; last exact/cns_cons/cns_spec/cns.
    have [ | K' /= []]//:= cns 0.
    by rewrite drop0 F2GL_cat  => -> /cat_eq_r ->.
  Qed.

  (* The function gather_shapes gathers the values that psi requires the values of phi on and will
     ultimately be used to define a modulus of continuity for the operator F produced from psi or
     more precisley for U psi, from which a modulus of F = \F_(U psi) can be found. *)

  Fixpoint gather_shapes q' n:=
    match n with
    | 0 => nil
    | S n' => let Ks := gather_shapes q' n' in
              match psi (F2GL phi (flatten Ks), q') with
              | inl K => K:: Ks
              | inr a' => Ks
              end
    end.

  Lemma gs_mon q' n: (gather_shapes q' n) \is_sublist_of (gather_shapes q' n.+1).
  Proof.
    by move => K/=; case: (psi _) => //; right.
  Qed.

  Lemma gs_subl q' n m:
    n <= m -> (gather_shapes q' n) \is_sublist_of (gather_shapes q' m).
  Proof. by move => /subnK <-; elim: (m - n) => // k ih; apply/subs_trans/gs_mon/ih. Qed.
  
  Lemma gs_cns q' n: consistent q' (gather_shapes q' n).
  Proof. by elim: n => // n ih /=; case E: (psi _) => [K | a']; last exact/ih. Qed.

  Lemma cns_gs q' Ks: consistent q' Ks -> gather_shapes q' (size Ks) = Ks.
  Proof. by elim: Ks => // K Ks ih /= [val cns]; rewrite ih // val. Qed.
  
  Lemma size_gs q' n: size (gather_shapes q' n) <= n.
  Proof. by elim: n => // n ih /=; case: (psi _) => // _; apply/leq_trans/leqnSn. Qed.  

  Lemma gs_gs q' n: gather_shapes q' n = gather_shapes q' (size (gather_shapes q' n)).
  Proof. by elim: n => // n ih /=; case E: (psi _) => [K | a'] //=; rewrite -ih E. Qed.

  Lemma gs_eqP q' n m: reflect
                       (gather_shapes q' n = gather_shapes q' m)
                       (size (gather_shapes q' n) == size (gather_shapes q' m)).
  Proof. by apply/(iffP idP) => [ sze | ->] //; apply/cns_eq/gs_cns/gs_cns/eqP. Qed.  

  Definition gather_queries nq' := flatten (gather_shapes nq'.2 nq'.1).

  Lemma gq_mon q' n: (gather_queries (n,q')) \is_sublist_of (gather_queries (n.+1, q')).
  Proof. exact/flatten_subl/gs_mon. Qed.

  Lemma gq_subl q' n m: n <= m ->
                        (gather_queries (n,q')) \is_sublist_of (gather_queries (m,q')).
  Proof. by move => ineq; apply/flatten_subl/gs_subl. Qed.

  Lemma gq_spec_ex q' K: (exists n, gather_queries (n,q') = K) <->
                         exists Ks, consistent q' Ks /\ K = flatten Ks.
  Proof.
    split => [[n <-] | [Ks [/cns_gs <- ->]]]; last by exists (size Ks).
    by exists (gather_shapes q' n); split; first exact/gs_cns.
  Qed.

  Lemma U_rec_if q' n: U_rec phi q' n =
                       if n == 0 then inl nil
                       else if psi (F2GL phi (gather_queries (n.-1, q')), q') is inr a' then inr a'
                            else inl (F2GL phi (gather_queries (n, q'))).
  Proof.
    elim: n => //= n ->.
    rewrite /U_step /gather_queries /=.
    case: ifP => [/eqP->/=|/eqP neq]; first by case: (psi _) => [K | ]//=; rewrite F2GL_cat.
    case E: (psi _) => [K | a'] //.
    - by case E': (psi _) => [K' | b']//=; rewrite F2GL_cat.
    by case: n neq E => // n _ /= eq; do 2 rewrite eq.
  Qed.  

  Lemma flatten_cat_eq T (K: seq T) Ks: 0 < size Ks ->
        flatten Ks = K ++ flatten (drop 1 Ks) -> Ks = K :: (drop 1 Ks).
  Proof. by case: Ks => //= K' Ks _; rewrite drop0 => /cat_eq_r ->. Qed.

  Definition communication:= make_mf (fun (q': Q') Ksa' =>
	     consistent q' Ksa'.1 /\ psi (F2GL phi (flatten Ksa'.1), q') = inr Ksa'.2).

  Lemma cmcn_sing: communication \is_singlevalued.
  Proof.
    move => q' [Ln a'] [Ln' b'] [/=cns val] [cns' val'].
    case/orP: (leq_total (size Ln) (size Ln')) => ineq.
    - move: val'; have <-: Ln = Ln' by apply/cns_val_eq/cns'/cns/ineq/val.
      by rewrite val => [[->]].
    move: val; have <-: Ln' = Ln by apply/cns_val_eq/cns/cns'/ineq/val'.
    by rewrite val' => [[->]].
  Qed.

  Lemma US q' n:
    U phi (n.+1, q') = match U phi (n, q') with
                       | Some a' => Some a'
                       | None => if psi (F2GL phi (gather_queries (n, q')), q') is inr a'
                                 then Some a'
                                 else None
                       end.
  Proof.
    rewrite /U U_rec_if /=.
    case: n => [/= | n]; first by rewrite /F2GL /=; case (psi (nil, q')).
    rewrite U_rec_if; have -> /=: n.+1 == 0 = false by trivial.
    rewrite /gather_queries /=.
    by case E: (psi (_ phi (gather_queries (n, _)), _)) => [K|]//; [case: (psi _) | rewrite E].
  Qed.

  Lemma cmcn_spec q' Ks a': communication q' (Ks,a') <->
                            Ks = gather_shapes q' (size Ks) /\ U phi ((size Ks).+1, q') = Some a'.
  Proof.
    split => [[/=cns val] | [-> val]].
    - split; first by symmetry; apply/cns_gs.
      by rewrite US /gather_queries (cns_gs cns) val /U cns_U_rec.
    split; simpl; first exact/gs_cns.
    move: val; rewrite US /U cns_U_rec; last exact/gs_cns.
    by case E: (psi _) => [| b'] // [<-]; rewrite gs_gs.
  Qed.

  Lemma gsS q' n: gather_shapes q' n.+1 =
                  match U phi (n.+1, q') with
                  | None => gather_shapes q' n.+1
                  | Some a' => gather_shapes q' n
                  end.
  Proof.
    elim: n => [ | n]; first by rewrite US /= /U_step /=; case: (psi (nil, q')).
    rewrite (US _ n.+1); case E: (U phi _) => [a' | ] => [/= | _].
    - by case E': (psi _) => [K | b'] => [eq | ]; first rewrite eq; rewrite E'.
    rewrite /U_step /= /gather_queries /=.
    by case E': (psi _) => [K | b']; case: (psi _).
  Qed.

  Lemma gqS q' n: gather_queries (n.+1,q') =
                  match U phi (n.+1, q') with
                  | None => gather_queries (n.+1,q')
                  | Some a' => gather_queries (n,q')
                  end.
  Proof. by rewrite [LHS]/gather_queries gsS; case: (U phi _). Qed.

  Lemma gs_rec_size q' n: U phi (n, q') = None -> size (gather_shapes q' n) = n.
  Proof.
    elim: n => // n ih; rewrite /= US /U_step.
    case: (psi _) => [K | a']//; first by case E: (U phi _) => //= _; rewrite (ih E).
    by case: (U phi _).
  Qed.
  
  Lemma U_size_gs q' n a':
    U phi (n,q') = some a' -> U phi ((size (gather_shapes q' n.-1)).+1, q') = some a'.
  Proof.
    elim: n => // n ih /=; rewrite US.
    case E: (U phi _) => [b' | ] => [eq |]; last by have ->:= gs_rec_size E; rewrite US E.
    rewrite eq in E.
    have := ih E; case: (n) E => // n' sm.
    by rewrite gsS sm /=.  
  Qed.

  Lemma U_val_spec q' n a':
    U phi (n.+1,q') = Some a'
    <->
    communication q' (gather_shapes q' n, a').
  Proof.
    split => [/U_size_gs /= val | /cmcn_spec [_ val]]; first by apply/cmcn_spec; rewrite -gs_gs.
    have /subnK {1}<-:= size_gs q' n; elim: (n - size _) val => // k ih val.
    by rewrite addSn US ih.
  Qed.  
  
  Lemma FU_val_spec Fphi: Fphi \from \F_U phi <->
	                  forall q', exists n, communication q' (gather_shapes q' n, (Fphi q')).
  Proof.
    split => [val q' | prp q'].
    - by have [n]:= val q'; case: n => //n /U_val_spec; exists n.
    by have [n /U_val_spec val]:= prp q'; exists n.+1.
  Qed.

  Lemma FU_dom_spec: phi \from dom \F_U <-> communication \is_total.
  Proof.
    split => [[Fphi /FU_val_spec tot q'] | tot].
    - by have [n val] := tot q'; exists (gather_shapes q' n, (Fphi q')).
    apply/FM_dom => q'.
    have [[Ks a'] [/=cns val]]:= tot q'; exists a'; exists ((size Ks).+1).
    by rewrite US /U cns_U_rec // /gather_queries cns_gs // val.
  Qed.

  
End U_machine.

Section moduli.
  (* Q: Questions, A: Answers *)
  Context (Q Q' A A' : Type).
  (* B: Baire space *)
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Notation "? K" := (@inl (list Q) A' K) (format "'?' K", at level 50).
  Notation "! a'" := (@inr (list Q) A' a') (format "'!' a'", at level 50).
  Context (psi: seq (Q * A) * Q' -> seq Q + A').

  Local Open Scope name_scope.
  Lemma gq_modf_gs:
    gather_queries psi \modulus_function_for (fun phi nq' => gather_shapes psi phi nq'.2 nq'.1).
  Proof.
    rewrite /gather_queries => phi [n q'] phi'.
    elim: n => // n ih coin /=.
    have coin': phi \coincides_with phi' \on (flatten (gather_shapes psi phi q' n)).
    - exact/coin_subl/coin/gq_mon.
    by rewrite -ih //= /F2GL -(coin_map coin').
  Qed.
    
  Lemma gq_modf_gq:
    gather_queries psi \modulus_function_for gather_queries psi.
  Proof. by move => phi nq' phi' coin; rewrite /gather_queries (gq_modf_gs coin). Qed.

  Lemma gq_modf_U:
    gather_queries psi \modulus_function_for U psi.
  Proof.
    move => phi [n q'] phi' coin.
    elim: n coin => //n ih coin.
    have coin': phi \coincides_with phi' \on (gather_queries psi phi (n,q')).
    - exact/coin_subl/coin/gq_mon.
    rewrite !US -ih // /U_step /F2GL -(gq_modf_gq coin') (coin_map coin').
    by case: (U psi phi _) => //; case: (psi _).
  Qed.

  Lemma U_cntf: (U psi) \is_continuous_function.
  Proof. exact/modf_cont/gq_modf_U. Qed.

  Lemma FU_cont: (\F_(U psi)) \is_continuous.
  Proof.
    rewrite FMop.sing_sfrst; first exact/sfrst_cntf_cont/U_cntf.
    exact/FMop.mon_sing/U_mon.
  Qed.

  Lemma FU_sing: (\F_(U psi)) \is_singlevalued.
  Proof. exact/cont_sing/FU_cont. Qed.

  Lemma FU_spec: (F_U psi) =~= \F_(U psi).
  Proof. by rewrite gtpf_spec -FMop.sing_sfrst//; apply/FU_sing. Qed.

  Lemma gq_monm: monotone_modulus (gather_queries psi).
  Proof. by move => phi q' n; apply/gq_mon. Qed.
End moduli.

Section duality_operator.
  (* Q: Questions, A: Answers *)
  Context (Q Q' A A' : Type).
  (* B: Baire space *)
  Local Notation B := (Q -> A).
  Local Notation B' := (Q' -> A').
  Local Open Scope name_scope.

  (* The duality operator is a special case of currying that does not need products for its
     specification. The operator D allows to exchange the arguments psi and phi. *)
  
  Fixpoint collect_left (Ka's: seq (seq Q + A')) : seq Q :=
    match Ka's with
    | nil => nil
    | cons Ka' Ka's' => match Ka' with
                        | inl K => K ++ collect_left Ka's'
                        | inr a' => nil
                        end
    end.

  Fixpoint D (phi: B) (Ka'sq': seq (seq (Q * A) * Q' * (seq Q + A')) * Q') : seq (seq (Q * A) * Q') + A' :=
    if map snd Ka'sq'.1 is inr a' :: _ then inr a'
    else inl [::(F2GL phi (collect_left (map snd Ka'sq'.1)), Ka'sq'.2)].
  
  Lemma D_cont: D \is_continuous_function.
  Proof.
    exists (fun Ka'sq' => match map snd Ka'sq'.1 with
                          | inl K :: Ka's => collect_left (map snd Ka'sq'.1)
                          | _ => nil
                          end).
    move => [Ka's q'] psi coin.
    rewrite /D /=; case: Ka's coin => // [[_ []]]//= K Ka's coin.
    by f_equal; f_equal; rewrite /F2GL (coin_map coin).
  Qed.

  Lemma U_rec_D psi phi q' n:
    U_rec (D phi) psi q' n =
    if n == 0 then inl nil
    else if U_rec psi phi q' n.-1 is inr a' then inr a'
         else inl (iseg (fun i =>
                           ((F2GL phi (gather_queries psi phi (i, q')),
                             q'),
                            psi (F2GL phi (gather_queries psi phi (i,q')), q'))) n).
  Proof.
    elim: n => // n.
    rewrite [RHS]/= U_recS => ->; rewrite !U_rec_if.
    case: n => // n; have ->: n.+1 == 0 = false by trivial.
    case: n => [ | n].
    - rewrite eq_refl; have ->: 2 == 0 = false by trivial.
      rewrite /U_step /= /gather_queries/=.
        by case E: (psi (nil, q')) => [K | ].
    rewrite /= /U_step /= /gather_queries /=.
    case E: (psi _) => [K | a']//; last by rewrite E.
    case E': (psi _) => [K' | a'] //=.
    do 8 f_equal.
    - move: E' => _.
      elim: n K E => // k ih K /=.
      case val: (psi (F2GL phi (flatten (gather_shapes psi phi q' k)), q')) => [L | a'] // E.
      + by rewrite (ih L).
      by rewrite E in val.
    move: E' => _.
    elim: n K E => // k ih K /=.
    case val: (psi (F2GL phi (flatten (gather_shapes psi phi q' k)), q')) => [L | a'] // E.
    - by rewrite (ih L).
    by rewrite E in val.    
  Qed.

  Lemma U_D_val psi phi q' n: U psi phi (n,q') = U (D phi) psi (n.+1, q').
  Proof. by rewrite /U U_rec_D /=; case: (U_rec _ _ _ _). Qed.

  Lemma D_spec psi phi: \F_(U (D phi)) psi === \F_(U psi) phi.
  Proof.
    move => Fphi.
    split => val q'; have [n eq]:= val q'.
    - exists n.-1; move: eq; rewrite /U U_rec_D.
      by case: (U_rec _ _ _); do 2 case: n => //.
    exists n.+1; move: eq; rewrite /U U_rec_D.
    by case eq: (U_rec _ _ _) => //.
  Qed.
End duality_operator.