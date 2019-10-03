From mathcomp Require Import ssreflect ssrfun seq ssrnat ssrbool.
From rlzrs Require Import all_rlzrs.
Require Import  axioms classical_count classical_cont classical_mach classical_func.
Require Import all_names all_cs_base dscrt seq_cont.
From metric Require Import pointwise.
Require Import ChoiceFacts Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section sequence_space.
  Context (X: cs) (I: Type) (somei: I) (I_count: I \is_countable).

  Definition Iprod_names : naming_space.
    exists (I * (queries X))%type (replies X).
    - exact/(somei,someq).
    - exact/prod_count/Q_count/I_count.
    exact/A_count.
  Defined.

  Local Notation rep_Iprod := (make_mf (fun (phi: Iprod_names) (xn: I -> space X) =>
    forall i, (fun p => (phi (i,p))) \describes (xn i) \wrt X)).
  
  Lemma rep_Iprod_sur: rep_Iprod \is_cototal.
  Proof.
    move => xn.
    pose R n phi:= phi \describes (xn n) \wrt X.
    have [ | phi phiprp]:= countable_choice I I_count _ R; last by exists (fun p => phi p.1 p.2).
    by move => n; have [phi phinx]:= (get_description (xn n)); exists phi.
  Qed.

  Lemma rep_Iprod_sing: rep_Iprod \is_singlevalued.
  Proof.
    move => phi xn yn phinxn phinyn.
    apply/fun_ext => n.
    by apply/ (rep_sing); [apply phinxn | apply phinyn ].
  Qed.
  
  Lemma rep_Iprod_rep: rep_Iprod \is_representation.
  Proof. by split; try apply/rep_Iprod_sing; try apply/rep_Iprod_sur. Qed.

  Definition sequence_representation:= Build_representation_of rep_Iprod_rep.

    Canonical cs_Iprod: cs.
    exists (I -> X) Iprod_names rep_Iprod.
    by split; [apply/rep_Iprod_sur | apply/rep_Iprod_sing].
  Defined.
  
  Lemma Iprd_base (an: cs_Iprod) (phi: name_space cs_Iprod):
    phi \describes an \wrt cs_Iprod <-> forall i, (fun q => phi (i,q)) \describes (an i) \wrt X.
  Proof. done. Qed.

  Lemma cprd_rlzr (Z: cs) (f: I -> Z -> X) F:
    (forall i, (F i) \realizes (f i)) ->
    (make_mf (fun phi psi => forall i, F i phi (fun q => (psi (i, q)))):_ ->> name_space cs_Iprod)
      \realizes
      (fun z => f^~ z).
  Proof.
    move => rlzr; apply/rlzr_F2MF => /= phi z phinz.
    split => [ | Fphi val i]; last first.
    - by have /rlzr_F2MF rlzr':= rlzr i; have [_ prp]:= rlzr' _ _ phinz; apply/prp/val.
    suff /full_choice [tphi_i tphi_ic] :
      forall i, exists phi_i, phi_i \describes ((f i) z) \wrt X /\ F i phi phi_i.
    - by exists (fun nq => tphi_i nq.1 nq.2) => n; have []:= tphi_ic n.
    move => i; have /rlzr_F2MF rlzr':= (rlzr i).
    have [[phi_i val] prp]:= rlzr' _ _ phinz.
    by exists phi_i; split; first apply/prp.            
  Qed.

  Lemma cprd_uprp_cont (Z : cs) (f : I -> Z c-> X):
    exists (F : Z c-> cs_Iprod), forall z i, sval F z i = sval (f i) z.
  Proof.
    suff fcont: continuous ((fun z => (fun n => sval (f n) z)) : (Z -> cs_Iprod)).
    - by exists (exist_c fcont).
    have /full_choice [F Fprp]: forall i, (sval (f i)) \is_continuous.
    - by move => i; apply/cfun_spec; case: (f i).
    have rlzr: forall i, (F i) \realizes (sval (f i)) by apply Fprp.
    have cont: forall i, (F i) \is_continuous_operator by apply Fprp.
    exists (make_mf (fun phi psi => forall i, (F i) phi (fun q => (psi (i,q))))).
    split => [ phi Fphi val /= |]; try exact/cprd_rlzr.
    have /full_choice[tLf mod]:
      forall i, exists Lf, forall Fphi,
            (F i) phi Fphi -> forall q', certificate (F i) (Lf q') phi q' (Fphi q').
    - move => i; have [Lf mod]:= cont i phi (fun q => Fphi (i, q)) (val i).
      exists Lf => Fphi' val' q'.
      suff <-: (fun q => Fphi (i, q)) = Fphi' by apply/mod.
      exact/cont_sing/val'/val/cont.
    exists (fun iq => tLf iq.1 iq.2) => [[i q] psi coin Fpsi val'].
    by have := mod i (fun q => Fphi (i,q)) (val i) q psi coin (fun q => Fpsi (i, q)) (val' i).
  Qed.
End sequence_space.
Notation "X '\^w'" :=
  (cs_Iprod X 0 nat_count) (at level 7, format "X '\^w'").    

Section isomorphisms.
  Context (I: Type) (somei: I) (I_count: I \is_countable).
  Notation cs_I:= (discrete_space I_count).
  Notation "X '\^I'" := (cs_Iprod X somei I_count) (at level 7, format "X '\^I'").
    
  Context (X: cs).
  Definition sig2fun (f: X\^I) := exist_c (dscrt_dscrt f): cs_I c-> X.

  Definition sig2fun_rlzrf (phi: (I * queries X -> replies X)) KLq' :=
    match KLq'.1 with
    | nil => inl [:: tt]
    | (ttn :: L) => inr (phi (@snd unit I ttn, KLq'.2))
    end.

  Definition sig2fun_rlzr: B_ (X\^I) ->> B_ (cs_I c-> X) := F2MF sig2fun_rlzrf.

  Lemma sig2fun_rlzr_spec: sig2fun_rlzr \realizes sig2fun.
  Proof.
    rewrite F2MF_rlzr => phi xn phinxn.
    rewrite /= => nf /= n eq.
    split => [ | psi val].
    - by exists (fun q => phi (n, q)) => q'; exists 2; rewrite /Umach.U/= eq.
    suff <-: (fun q => phi (n, q)) = psi by exists (xn n); split; first apply/phinxn.
    apply/fun_ext => q.
    have [m eq']:= val q; case: m eq' => //m; case: m => //m.
    have ->: Umach.U (sig2fun_rlzrf phi) nf (m.+2,q) = Umach.U (sig2fun_rlzrf phi) nf (2,q).
    - elim: m => // m; rewrite -addn1 -addn1 /Umach.U /=.
      by case: (U_rec (sig2fun_rlzrf phi) nf q).
    by rewrite /Umach.U/= eq => [[]].
  Qed.

  Lemma sig2fun_rlzr_cntop: sig2fun_rlzr \is_continuous_operator.
  Proof.
    rewrite cont_F2MF.
    apply/F2MF_cont_choice => [ | phi Lq']; first exact/countable_choice/Q_count.
    case E: Lq'.1 => [ | n L]; first by exists [::] => psi _; rewrite /sig2fun_rlzrf E.
    by exists ([:: (n.2, Lq'.2)]); rewrite /sig2fun_rlzrf E => psi [->].
  Qed.

  Lemma sig2fun_cont: sig2fun \is_continuous.
  Proof.
    by exists sig2fun_rlzr; split; try exact/sig2fun_rlzr_spec; apply/sig2fun_rlzr_cntop.
  Qed.

  Definition fun2sig_rlzr: B_ (cs_I c-> X) ->> B_ (X\^I):=
    make_mf (fun (psi: name_space cs_I c-> X) phi =>
	       forall n, \F_(U psi) (fun _ => n) (fun q => phi (n, q))).

  Lemma fun2sig_rlzr_spec: fun2sig_rlzr \realizes (sval: _ c-> _ -> _).
  Proof.
    rewrite /solution rlzr_F2MF => psi xn /rlzr_F2MF rlzr.
    split => [ | phin Fpsiphi n].
    - have prp: forall (i: I), exists phi: queries X -> replies X, forall q,
      exists c : nat, U psi (fun _ : unit => i) (c,q) = Some (phi q).
      + move => n.
        have [ | [phi val prp]]//:= rlzr (fun _ => n) n.
        by exists phi => q; apply/val.
      have [phin nm]:= full_choice _ prp.
      by exists (fun nq => phin nq.1 nq.2) => n q /=; apply nm.
    have [ | [phi val prp]]//:= rlzr (fun _ => n) n.
    apply/prp => q.
    exact/Fpsiphi.
  Qed.

  Lemma fun2sig_rlzr_cntop: fun2sig_rlzr \is_continuous_operator.
  Proof.
    move => phi Fphi val.
    suff /full_choice: forall nq', exists L, certificate fun2sig_rlzr L phi nq' (Fphi nq') by trivial.
    move => [n q'].
    have [ | mf mod]:= @FU_cont _ _ _ _ (D (fun _ => n)) phi (fun q => Fphi (n, q)).
    - by rewrite D_spec; apply/val.
    exists (mf q') => psi coin Fpsi val'.
    apply/(mod q' psi coin (fun q => Fpsi (n, q))).
    by rewrite D_spec; apply/val'.
  Qed.

  Lemma fun2sig_cont: (sval: cs_I c-> X -> X\^I) \is_continuous.
  Proof. by exists fun2sig_rlzr; split; try exact/fun2sig_rlzr_spec; exact/fun2sig_rlzr_cntop. Qed.

  Lemma sig_iso_fun: X\^I ~=~ (cs_I c-> X).
  Proof.
    exists (exist_c sig2fun_cont).
    exists (exist_c fun2sig_cont).
    by split => [f | f]; last apply/eq_sub; apply fun_ext => n /=.
  Qed.

  Context (Y: cs).
  
  Definition cs_zip (xnyn: X\^I * Y\^I): (X \*_cs Y)\^I:= (fun i => (xnyn.1 i, xnyn.2 i)).

  Lemma cs_zip_spec (xn: X\^I) (yn: Y\^I) i: cs_zip (xn, yn) i = (xn i, yn i).
  Proof. done. Qed.

  Definition zip_rlzr Q A Q' A' (phipsi: _ -> A * A') (iqq': I* (Q + Q')):=
    match iqq'.2 with
    | inl q => phipsi (inl (iqq'.1, q))
    | inr q' => phipsi (inr (iqq'.1, q'))
    end.
  Arguments zip_rlzr {Q} {A} {Q'} {A'}.
  
  Local Open Scope name_scope.
  Lemma zip_rlzr_cntf Q A Q' A': (@zip_rlzr Q A Q' A') \is_continuous_function.
  Proof.
    move => phi.
    exists (fun iqq' => [::match iqq'.2 with | inl q => inl (iqq'.1,q) | inr q' => inr (iqq'.1, q') end]).
    by rewrite /zip_rlzr; move => [i [q | q']] psi [/= ->].
  Qed.
  Local Close Scope name_scope.
    
  Lemma zip_rlzr_spec: (F2MF zip_rlzr) \realizes cs_zip.
  Proof.
    rewrite /solution rlzr_F2MF => phipsi [xn yn] /prod_name_spec [nm nm'].
    split => [ | _ <- i]; first exact/F2MF_dom.
    by apply/prod_name_spec; split; [apply/nm | apply/nm'].
  Qed.

  Lemma zip_cont: cs_zip \is_continuous.
  Proof.
    by apply/F2MF_cont; exists zip_rlzr; split; try apply/zip_rlzr_spec; apply/zip_rlzr_cntf.
  Qed.
              
  Definition cs_unzip (xyn: (cs_prod X Y)\^I): X\^I * Y\^I:=
    (fun i => (xyn i).1, fun i => (xyn i).2).
  
  Definition nzip_rlzrf X Y (phipsi: _ -> replies X * replies Y) (iqiq': queries (X\^I) + queries (Y\^I)):=
    match iqiq' with
    | inl iq => phipsi (iq.1, inl iq.2)
    | inr iq' => phipsi (iq'.1, inr iq'.2)
    end.

  Local Open Scope name_scope.
  Lemma nzip_rlzr_cntop:
    (@nzip_rlzrf X Y) \is_continuous_function.
  Proof.
    move => phi.
    exists (fun iqiq' => [::match iqiq' with | inl iq => (iq.1, inl iq.2) | inr iq' => (iq'.1, inr iq'.2) end]).
    by rewrite /nzip_rlzrf; move => [iq | iq'] psi [/= ->].
  Qed.
  Local Close Scope name_scope.

  Definition nzip_rlzr: B_ ((cs_prod X Y)\^I) ->> B_ (cs_prod (X\^I) (Y\^I)):=
    F2MF (@nzip_rlzrf X Y).
  
  Lemma nzip_rlzr_spec: nzip_rlzr \realizes cs_unzip.
  Proof.
    rewrite F2MF_rlzr => phipsi xyn nm.
    by apply/prod_name_spec; split => i; move: (nm i) => /prod_name_spec [].
  Qed.

  Lemma nzip_cont: cs_unzip \is_continuous.
  Proof.
    by exists nzip_rlzr; split; try exact/nzip_rlzr_spec; exact/cont_F2MF/nzip_rlzr_cntop.
  Qed.

  Lemma cprd_prd: (X\^I) \*_cs (Y\^I) ~=~ (X \*_cs Y)\^I.
  Proof.
    exists (exist_c zip_cont).
    exists (exist_c nzip_cont).
    split => [[xn yn] | xyn] //.
    apply/fun_ext => i.
    by rewrite /cs_unzip/cs_zip/=; case: (xyn i).
  Qed.
End isomorphisms.

Section pointwise.  
  Context I (somei: I) (I_count: I \is_countable).
  
  Notation "X '\^I'" := (cs_Iprod X somei I_count) (at level 2, format "X '\^I'").

  Definition ptw_rlzr Q A Q' A' (F: (Q -> A) ->> (Q' -> A')) :=
    make_mf (fun phin Fphin =>
               forall (i: I), F (fun q => phin (i, q)) (fun q' => Fphin (i, q'))).

  Lemma ptw_rlzr_cntop Q A Q' A' (F: (Q -> A) ->> (Q' -> A')):
    F \is_continuous_operator -> (ptw_rlzr F) \is_continuous_operator.
  Proof.
    move => cont => phin Fphin val.
    have /full_choice [Lf mod]//:
         forall i, exists Lf, forall q',
               certificate F (Lf q') (fun  q => phin (i, q)) q' (Fphin (i, q')).
    - by move => i; apply/cont/val.
    exists (fun iq => [seq (iq.1, L) | L <- Lf iq.1 iq.2]).
    move => [i q'] psin coin Fpsin val'.
    apply/(mod i q' _ _ (fun q => Fpsin (i, q)))/val'.
    by elim: (Lf i q') coin => //= q L ih []; split => //; apply/ih.
  Qed.

  Lemma ptw_rlzr_spec (X Y: cs) (f: X ->> Y) F:
    F \solves f -> (ptw_rlzr F:B_ (X\^I) ->> B_ (Y\^I)) \solves (mf_ptw I f). 
  Proof.
    move => slvs phin xs phinxs [ys val].
    split => [ | Fphi val'].
    - suff /full_choice [Fphi prp]: forall i, exists Fphi, F (fun q => phin (i, q)) Fphi.
      - by exists (fun iq => Fphi iq.1 iq.2).
      move => i; have []//:= slvs (fun q => phin (i, q)) (xs i); first exact/phinxs.
      by exists (ys i); apply/val.
    suff /full_choice [fa prp] i: exists fai,
                    (fun q' => Fphi (i, q')) \describes fai \wrt Y
                    /\
                    f (xs i) fai. 
    - by exists fa; split => i; have []:= prp i.
    have [ | [fx ]]:= slvs_val slvs (phinxs i) _ (val' i); first by exists (ys i); apply/ val.
    by exists fx.
  Qed.

  Lemma ptw_hcr (X Y: cs) (f: X ->> Y): f \has_continuous_realizer ->
             (mf_ptw I f : X\^I ->> Y\^I) \has_continuous_realizer.
  Proof.
    move => [F [rlzr cont]].
    by exists (ptw_rlzr F); split; try exact/ptw_rlzr_spec; exact/ptw_rlzr_cntop.
  Qed.

  Definition ptw R T (f: R -> T) (rs: I -> R) i := f (rs i).
  
  Lemma ptw_comp R T (f: R -> T) rs: (ptw f rs) =1 f \o_f rs.
  Proof. done. Qed.

  Lemma F2MF_ptw R T (f: R -> T):
    mf_ptw I (F2MF f) =~= F2MF (ptw f).
  Proof.
    move => rs ts /=; split => [prp | <-]//.
    exact/fun_ext.
  Qed.

  Lemma ptw_cont (X Y: cs) (f: X -> Y):
    f \is_continuous -> (ptw f: X\^I -> Y\^I) \is_continuous.
  Proof.
    move => cont.
    rewrite /continuous -F2MF_ptw.
    exact/ptw_hcr.
  Qed.
  
  Definition cptw_op (X Y Z: cs) (op: X * Y -> Z): X\^I * Y\^I -> Z\^I :=
    curry (ptw_op (uncurry op)).

  Lemma cptw_ptw (X Y Z: cs) (op: X * Y -> Z):
    (cptw_op op) = (@ptw (X * Y) Z op) \o_f (@cs_zip I somei I_count _ _).
  Proof. done. Qed.
  
  Lemma cptw_cont X (op: cs_prod X X -> X): op \is_continuous -> (cptw_op op) \is_continuous.
  Proof.
    move => [F [Fcont /rlzr_F2MF Frop]].
    pose np := (@pair B_ X B_ X: _ -> B_(X \*_cs X)).
    exists (make_mf (fun (phi: B_ (_\^I \*_cs _\^I)) psi => forall n,
	 F (np (fun q => lprj phi (n, q), fun q => rprj phi (n, q))) (fun q => psi (n, q)))).
    rewrite /solution rlzr_F2MF; split => [ | phi [xn yn] /prod_name_spec [phinxn phinyn]].
    - apply cont_choice => [ | phi Fphi /=FphiFphi [n q]].
      + exact/countable_choice/prod_count/Q_count.
      pose phin:= np (fun q => lprj phi (n, q), fun q => rprj phi (n, q)).
      have [ | Lf mod]:= Fcont phin (fun q' => Fphi (n, q')); first exact/FphiFphi.
      exists ([:: inr (n, someq); inl (n, someq)] ++
                                  map (fun q' => match q' with
	                                         | inl q'' => inl (n, q'')
	                                         | inr q'' => inr (n, q'')
	                                         end) (Lf q)) => psi /coin_agre coin Fpsi eq.
      apply/(mod q (np (_, _)) _ (fun q => Fpsi (n, q)))/eq.
      apply/coin_agre => [[q' | q'] lstn].
      - rewrite /phin/lprj/rprj /= -(coin (inr (n, someq))); last by left.
        rewrite -(coin (inl (n,q'))) //; right; right.
        by elim: (Lf q) lstn => // a L ih /= [ -> | ]; [left | right; apply/ih].
      rewrite /phin/lprj/rprj/= -(coin (inl (n,someq))); last by right; left.
      rewrite -(coin (inr (n, q'))) //; right; right.
      by elim: (Lf q) lstn => // a L ih /= [ -> | ]; [left | right; apply/ih].
    have nms n: (np (fun q : queries X => lprj phi (n, q), fun q : queries X => rprj phi (n, q)))
                    \is_name_of (xn n, yn n).
    - by apply/prod_name_spec; split; [apply/phinxn | apply/phinyn].
    split => [ | psi FpsiFpsi n].
    - have fd n:= (Frop (np (fun q => lprj phi (n, q), fun q => rprj phi (n, q))) (xn n, yn n) (nms n)).1.
      have [Fphi Fphiprp]:= countable_choice I I_count _ _ fd.
      by exists (fun nq => Fphi nq.1 nq.2) => n /=; apply Fphiprp.
    have val n:= (Frop (np (fun q => lprj phi (n, q), fun q => rprj phi (n, q)))
                         (xn n, yn n) (nms n)).2.
    by rewrite /ptw/=; apply/val/FpsiFpsi.
  Qed.
End pointwise.
  
Notation cptwn_op := (@cptw_op nat 0%nat nat_count).
Notation ptwn_op := (@ptw_op nat).
Notation ptwn := (@ptw nat).

Section limits.
  Definition limit X: X\^w ->> X:= make_mf (fun xn x =>
    exists phin phi,
      phin \describes xn \wrt (X\^w)
      /\
      phi \describes x \wrt X
      /\
      (phi \is_limit_of (uncurry phin))%name).
  Arguments limit {X}.
  Local Notation "x \is_limit_of xn" := (limit xn x).

  (*
  Lemma lim_prd (X Y: cs) xn (x: X) yn (y: Y):
    (x, y) \is_limit_of (@cs_zip nat 0 nat_count _ _ (xn, yn))
    <->
    x \is_limit_of xn /\ y \is_limit_of yn.
  Proof.
    split => [[phipsin [phipsi [nm [[lnm rnm] lmt]]]] |].
    - split.
      + exists (lprj (nzip_rlzrf phipsin)); exists (lprj phipsi).
        split => [i | ]; [by have []:= nm i | split => // q].
        have [N prp]:= lmt (inl q).
        exists N => m ineq /=; have := prp m ineq.
        by rewrite /lprj /= => ->.
      exists (rprj (nzip_rlzrf phipsin)); exists (rprj phipsi).
      split => [i | ]; [by have []:= nm i | split => // q].
      have [N prp]:= lmt (inr q).
      exists N => m ineq /=; have := prp m ineq.
      by rewrite /rprj /= => ->.
    move => [[phin [phi [phinxn [phinx lmt]]]] [psin [psi [psinxn [psinx lmt']]]]].
    exists (fun iqq' => match iqq'.2 with
                        | inl q => (phin (iqq'.1, q), somea)
                        | inr q' => (somea, psin (iqq'.1, q'))
                        end).
    exists (name_pair phi psi).
    split => [i | ]; first by split; rewrite /lprj/rprj/=; [apply/phinxn | apply/psinxn].
    split => //; apply/lim_coin.
    elim => [ | [q | q'] L [N ih]]; first by exists 0.
    - have [N' coin]:= lmt q.
      exists (maxn N N') => m ineq.
      split; last exact/ih/leq_trans/ineq/leq_maxl.
      rewrite /uncurry/=.
      by have -> //:= coin m; apply/leq_trans/ineq/leq_maxr.
    have [N' coin]:= lmt' q'.
    exists (maxn N N') => m ineq.
    split; last exact/ih/leq_trans/ineq/leq_maxl.
    rewrite /uncurry/=.
    by have ->//:= coin m; first by apply/leq_trans/ineq/leq_maxr.
  Qed.
   *)
   
  Definition sequential_continuity_point (X Y: cs) (f: X -> Y) x:=
    forall xn, x \is_limit_of xn -> (f x) \is_limit_of (ptw f xn).
  Local Notation "f \is_sequentially_continuous_in x" := (sequential_continuity_point f x).
  
  Definition sequential_continuity_points (X Y: cs) (f: X -> Y):=
    make_subset (fun x => sequential_continuity_point f x).
  
  Definition sequentially_continuous (X Y: cs) (f : X -> Y):=
    forall x, sequential_continuity_point f x.
  Local Notation "f \is_sequentially_continuous" := (sequentially_continuous f).
  Local Notation "F \is_sequentially_continuous_operator":= (seq_cont.sequentially_continuous F) (at level 30).
  
  Lemma rlzr_scnt (X Y: cs) (f: X -> Y) F:
    FunctionalCountableChoice_on (B_ Y) ->
    F \realizes f -> F \is_sequentially_continuous_operator ->
    f \is_sequentially_continuous.
  Proof.
    move => choice /rlzr_F2MF rlzr cont x xn [phin [phi [phinxn [phinx lmt]]]].
    have [[Fphi val] prp]:= rlzr _ _ phinx.
    have /choice [Fphin vals]: forall n, exists Fphin, F (fun q => phin (n, q)) Fphin.
    - move => n; have [[Fphin vals] _]:= rlzr _ _ (phinxn n).
      by exists Fphin; apply/vals.               
    exists (curry Fphin); exists Fphi; split.
      move => n; have [_ prps]:= rlzr _ _ (phinxn n).
      exact/prps/vals.
    split; first exact/prp.
    exact/cont/val/vals/lmt.
  Qed.

  Lemma cont_scnt_choice (X Y: cs) (f: X -> Y):
    FunctionalCountableChoice_on (B_ Y) -> f \is_continuous -> sequentially_continuous f.
  Proof. move => choice [F [/cont_scnt cont rlzr]]; exact/rlzr_scnt/cont. Qed.
End limits.
Arguments limit {X}.
Notation "x \is_limit_of xn" := (limit xn x): cs_scope.
Notation "f \is_sequentially_continuous_in x" := (sequential_continuity_point f x): cs_scope.
Notation "f \is_sequentially_continuous" := (sequentially_continuous f): cs_scope.
Notation "F \is_sequentially_continuous_operator":= (seq_cont.sequentially_continuous F) (at level 2): cs_scope.

Section cs_names.
  Lemma BequivB (B: naming_space):
    delta_(B) \equivalent_to
          (sequence_representation (discrete_space (A_count B)) (default_question B) (Q_count B)).
  Proof.
    split.
    - apply/F2MF_cont; exists (fun phi ntt => phi (ntt.1)).
      by split; try apply/F2MF_rlzr => ? _ <- //; exists (fun ntt => [:: ntt.1]) => ntt psi [<-].
    apply/F2MF_cont; exists (fun phi n => phi (n,tt)).
    split; first by exists (fun n => [:: (n, tt)]) => ? ? [].
    by apply/F2MF_rlzr => /= phi x eq; apply/fun_ext/eq.
  Qed.
    
  Lemma BisoB (B: naming_space):
    B ~=~ (discrete_space (Q_count B)) c-> (discrete_space (A_count B)).
  Proof. by rewrite -sig_iso_fun; apply/(equiv_iso (BequivB B)). Qed.
End cs_names.

Lemma cont_scnt (X Y: cs) (f: X -> Y):
  f \is_continuous -> f \is_sequentially_continuous.
Proof. exact/cont_scnt_choice/countable_choice/nat_count. Qed.
