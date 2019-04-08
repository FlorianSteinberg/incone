From mathcomp Require Import ssreflect ssrfun seq ssrnat ssrbool.
From rlzrs Require Import all_rlzrs.
Require Import classical_count classical_cont classical_mach classical_func all_cs_base dscrt seq_cont sub.
From metric Require Import pointwise.
Require Import FunctionalExtensionality ClassicalChoice ChoiceFacts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section USIGPROD.
  Context (X: cs) (I: Type).
  Hypothesis choice: forall A, FunctionalChoice_on I A.
  Definition rep_Iprod := make_mf (fun phi (xn: I -> X) =>
    forall i, (fun p => (phi (i,p))) \describes (xn i) \wrt X).
  
  Lemma rep_Iprod_sur: rep_Iprod \is_cototal.
  Proof.
    move => xn.
    pose R n phi:= phi \describes (xn n) \wrt X.
    have [ | phi phiprp]:= @choice _ R; last by exists (fun p => phi p.1 p.2).
    by move => n; have [phi phinx]:= (get_description (xn n)); exists phi.
  Qed.

  Lemma rep_Iprod_sing: rep_Iprod \is_singlevalued.
  Proof.
    move => phi xn yn phinxn phinyn.
    apply functional_extensionality => n.
    by apply/ (rep_sing); [apply phinxn | apply phinyn ].
  Qed.

  Context (somei: I) (I_count: I \is_countable).
  Canonical cs_Iprod_class := @continuity_space.Class _ _ _
    (interview.Mixin rep_Iprod_sur) (dictionary.Mixin rep_Iprod_sing)
    (continuity_space.Mixin
       (somei, someq X) (somea X) (prod_count I_count (Q_count X)) (A_count X)).
  Canonical cs_Iprod := continuity_space.Pack cs_Iprod_class.
                  
  Lemma Iprd_base (an: cs_Iprod) (phi: name_space cs_Iprod):
    phi \describes an \wrt cs_Iprod <-> forall i, (fun q => phi (i,q)) \describes (an i) \wrt X.
  Proof. done. Qed.

  Lemma cprd_rlzr (Z: cs) (f: I -> Z -> X) F:
    (forall i, (F i) \realizes (F2MF (f i))) ->
    (make_mf (fun phi psi => forall i, F i phi (fun q => (psi (i, q)))):_ ->> name_space cs_Iprod)
      \realizes
      (F2MF (fun z => f^~ z)).
  Proof.
    move => rlzr; apply/rlzr_F2MF => /= phi z phinz.
    split => [ | Fphi val i]; last first.
    - by have /rlzr_F2MF rlzr':= rlzr i; have [_ prp]:= rlzr' _ _ phinz; apply/prp/val.
    suff /choice [tphi_i tphi_ic] :
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
    have /choice [F Fprp]: forall i, (sval (f i)) \is_continuous.
    - by move => i; apply/ass_cont; case: (f i).
    have rlzr: forall i, (F i) \realizes (F2MF (sval (f i))) by apply Fprp.
    have cont: forall i, (F i) \is_continuous_operator by apply Fprp.
    exists (make_mf (fun phi psi => forall i, (F i) phi (fun q => (psi (i,q))))).
    split => [ | phi Fphi val /=]; first exact/cprd_rlzr.
    have /choice[tLf mod]:
      forall i, exists Lf, forall Fphi,
            (F i) phi Fphi -> forall q', certificate (F i) (Lf q') phi q' (Fphi q').
    - move => i; have [Lf mod]:= cont i phi (fun q => Fphi (i, q)) (val i).
      exists Lf => Fphi' val' q'.
      suff <-: (fun q => Fphi (i, q)) = Fphi' by apply/mod.
      exact/cont_sing/val'/val/cont.
    exists (fun iq => tLf iq.1 iq.2) => [[i q] psi coin Fpsi val'].
    by have := mod i (fun q => Fphi (i,q)) (val i) q psi coin (fun q => Fpsi (i, q)) (val' i).
 Qed.
End USIGPROD.
Notation "X '\^w'" :=
  (cs_Iprod X countable_choice 0 nat_count) (at level 35, format "X '\^w'").    

Section isomorphisms.
  Context (I: Type) (somei: I) (I_count: I \is_countable).
  Hypothesis choice: forall A, FunctionalChoice_on I A.
  Notation cs_I:= (@cs_id I somei I_count).
  Notation "X '\^I'" := (cs_Iprod X choice somei I_count) (at level 30, format "X '\^I'").
  Context (X: cs).
  Definition sig2fun (f: X\^I) := exist_c (@cs_id_dscrt I somei I_count X f): cs_I c-> X.

  Definition sig2fun_rlzrf (phi: name_space (X\^I)) Lq' :=
    match Lq'.1 with
    | nil => inl [:: tt]
    | (n :: L) => inr (phi (n, Lq'.2))
    end.
  
  Definition sig2fun_rlzr: questions (X\^I) ->> questions (cs_I c-> X) := F2MF sig2fun_rlzrf.

  Lemma sig2fun_rlzr_spec: sig2fun_rlzr \realizes (F2MF sig2fun).
  Proof.
    rewrite F2MF_rlzr_F2MF => phi xn phinxn.
    rewrite /= rlzr_F2MF => nf /= n eq.
    split => [ | psi val]; first by exists (fun q => phi (n, q)) => q'; exists 2; rewrite /U/= eq.
    suff <-: (fun q => phi (n, q)) = psi by apply/phinxn.
    apply/functional_extensionality => q.
    have [m eq']:= val q; case: m eq' => //m; case: m => //m.
    have ->: U (sig2fun_rlzrf phi) m.+2 nf q = U (sig2fun_rlzrf phi) 2 nf q.
    - elim: m => // m; rewrite -addn1 -addn1 /U /=.
      by case: (U_rec (sig2fun_rlzrf phi) (m + 1 + 1) nf q).
    by rewrite /U/= eq => [[]].
  Qed.

  Lemma sig2fun_rlzr_cntop: sig2fun_rlzr \is_continuous_operator.
  Proof.
    rewrite cont_F2MF F2MF_cont_choice => phi Lq'.
    case E: Lq'.1 => [ | n L]; first by exists [::] => psi _; rewrite /sig2fun_rlzrf E.
    by exists ([:: (n, Lq'.2)]); rewrite /sig2fun_rlzrf E => psi [->].
  Qed.

  Lemma sig2fun_cont: sig2fun \is_continuous.
  Proof.
    by exists sig2fun_rlzr; split; [apply/sig2fun_rlzr_spec | apply/sig2fun_rlzr_cntop].
  Qed.

  Definition fun2sig_rlzr: questions (cs_I c-> X) ->> questions (X\^I):=
    make_mf (fun (psi: name_space cs_I c-> X) phi =>
	       forall n, \F_(U psi) (fun _ => n) (fun q => phi (n, q))).

  Lemma fun2sig_rlzr_spec: fun2sig_rlzr \realizes (F2MF sval).
  Proof.
    rewrite rlzr_F2MF => psi xn /rlzr_F2MF rlzr.
    split => [ | phin Fpsiphi n].
    - have prp: forall (i: I), exists phi: queries X -> answers X, forall q,
      exists c : nat, U psi c (fun _ : unit => i) q = Some (phi q).
      + move => n.
        have [ | [phi val prp]]//:= rlzr (fun _ => n) n.
        by exists phi => q; apply/val.
      have [phin nm]:= choice prp.
      by exists (fun nq => phin nq.1 nq.2) => n q /=; apply nm.
    have [ | [phi val prp]]//:= rlzr (fun _ => n) n.
    apply/prp => q.
    exact/Fpsiphi.
  Qed.

  Lemma fun2sig_rlzr_cntop: fun2sig_rlzr \is_continuous_operator.
  Proof.
    apply/cont_choice.
    rewrite /fun2sig_rlzr => psi phi Fpsiphi [n q'].
    have [ | mf mod]:= @FM_val_cont _ _ _ _ (fun _ => n) psi (fun q => phi (n, q)); first exact/(Fpsiphi n).
    exists (mf q') => psi' coin Fpsi' val.
    exact/(mod q' psi' coin (fun q => Fpsi' (n, q)))/val.
  Qed.

  Lemma fun2sig_cont: (sval: cs_I c-> X -> X\^I) \is_continuous.
  Proof.
    exists fun2sig_rlzr; split; [exact/fun2sig_rlzr_spec | exact/fun2sig_rlzr_cntop].
  Qed.

  Lemma sig_iso_fun: X\^I ~=~ (cs_I c-> X).
  Proof.
    exists (exist_c sig2fun_cont).
    exists (exist_c fun2sig_cont).
    by split => [f | f]; last apply/eq_sub; apply functional_extensionality => n /=.
  Qed.

  Context (Y: cs).
  
  Definition cs_zip (xnyn: X\^I \*_cs Y\^I): (X \*_cs Y)\^I :=
    (fun i => (xnyn.1 i, xnyn.2 i)).

  Lemma cs_zip_spec (xn: X\^I) (yn: Y\^I) i:
    cs_zip (xn, yn) i = (xn i, yn i).
  Proof. done. Qed.

  Definition zip_rlzrf Q A Q' A' (phipsi: _ -> A * A') (iqq': I* (Q + Q')):=
    match iqq'.2 with
    | inl q => phipsi (inl (iqq'.1, q))
    | inr q' => phipsi (inr (iqq'.1, q'))
    end.

  Local Open Scope baire_scope.
  Lemma zip_rlzr_cntop Q A Q' A':
    (@zip_rlzrf Q A Q' A') \is_continuous_function.
  Proof.
    move => phi.
    exists (fun iqq' => [::match iqq'.2 with | inl q => inl (iqq'.1,q) | inr q' => inr (iqq'.1, q') end]).
    by rewrite /zip_rlzrf; move => [i [q | q']] psi [/= ->].
  Qed.
  Local Close Scope baire_scope.
  
  Definition zip_rlzr: questions (X\^I \*_cs Y\^I) ->> questions ((X \*_cs Y)\^I):=
    F2MF (@zip_rlzrf _ _ _ _).
  
  Lemma zip_rlzr_spec: zip_rlzr \realizes (F2MF cs_zip).
  Proof.
    rewrite rlzr_F2MF => phipsi [xn yn] [nm nm'].
    split => [ | _ <- i]; first exact/F2MF_dom.
    rewrite /zip_rlzrf/=/lprj/rprj /=.
    by split; [apply/nm | apply/nm'].
  Qed.

  Lemma zip_cont: cs_zip \is_continuous.
  Proof.
    by exists zip_rlzr; split; [exact/zip_rlzr_spec | exact/cont_F2MF/zip_rlzr_cntop].
  Qed.
              
  Definition cs_unzip (xyn: (X \*_cs Y)\^I): X\^I \*_cs Y\^I:=
    (fun i => (xyn i).1, fun i => (xyn i).2).
  
  Definition nzip_rlzrf Q A Q' A' (phipsi: _ -> A * A') (iqiq': I * Q + I * Q'):=
    match iqiq' with
    | inl iq => phipsi (iq.1, inl iq.2)
    | inr iq' => phipsi (iq'.1, inr iq'.2)
    end.

  Local Open Scope baire_scope.
  Lemma nzip_rlzr_cntop Q A Q' A':
    (@nzip_rlzrf Q A Q' A') \is_continuous_function.
  Proof.
    move => phi.
    exists (fun iqiq' => [::match iqiq' with | inl iq => (iq.1, inl iq.2) | inr iq' => (iq'.1, inr iq'.2) end]).
    by rewrite /nzip_rlzrf; move => [iq | iq'] psi [/= ->].
  Qed.
  Local Close Scope baire_scope.

  Definition nzip_rlzr: questions ((X \*_cs Y)\^I) ->> questions (X\^I \*_cs Y\^I):=
    F2MF (@nzip_rlzrf _ _ _ _).
  
  Lemma nzip_rlzr_spec: nzip_rlzr \realizes (F2MF cs_unzip).
  Proof.
    rewrite rlzr_F2MF => phipsi xyn nm.
    split => [ | _ <-]; first exact/F2MF_dom.
    by split => i; have []:= nm i.
  Qed.

  Lemma nzip_cont: cs_unzip \is_continuous.
  Proof.
    by exists nzip_rlzr; split; [exact/nzip_rlzr_spec | exact/cont_F2MF/nzip_rlzr_cntop].
  Qed.

  Lemma cprd_prd: (X\^I \*_cs Y\^I) ~=~ ((X \*_cs Y)\^I).
  Proof.
    exists (exist_c zip_cont).
    exists (exist_c nzip_cont).
    split => [[xn yn] | xyn] //.
    apply/functional_extensionality => i.
    by rewrite /cs_unzip/cs_zip/=; case: (xyn i).
  Qed.
End isomorphisms.

Section pointwise.  
  Context I (somei: I) (I_count: I \is_countable).
  Hypothesis choice: forall A, FunctionalChoice_on I A.
  
  Notation "X '\^I'" := (cs_Iprod X choice somei I_count) (at level 2, format "X '\^I'").

  Definition ptw_rlzr Q A Q' A' (F: (Q -> A) ->> (Q' -> A')) :=
    make_mf (fun phin Fphin =>
               forall (i: I), F (fun q => phin (i, q)) (fun q' => Fphin (i, q'))).

  Lemma ptw_rlzr_cntop Q A Q' A' (F: (Q -> A) ->> (Q' -> A')):
    F \is_continuous_operator -> (ptw_rlzr F) \is_continuous_operator.
  Proof.
    move => cont => phin Fphin val.
    have /choice [Lf mod]//: forall i, exists Lf, forall q', certificate F (Lf q') (fun  q => phin (i, q)) q' (Fphin (i, q')).
    - by move => i; apply/cont.    
    exists (fun iq => [seq (iq.1, L) | L <- Lf iq.1 iq.2]).
    move => [i q'] psin coin Fpsin val'.
    apply/(mod i q' _ _ (fun q => Fpsin (i, q)))/val'.
    by elim: (Lf i q') coin => //= q L ih []; split => //; apply/ih.
  Qed.

  Lemma ptw_rlzr_spec (X Y: cs) (f: X ->> Y) F:
    F \realizes f -> (ptw_rlzr F:questions (X\^I) ->> questions (Y\^I)) \realizes (mf_ptw I f). 
  Proof.
    move => rlzr phin xs phinxs [ys val].
    split => [ | Fphi val'].
    - suff /choice [Fphi prp]: forall i, exists Fphi,
            F (fun q => phin (i, q)) Fphi.
      - by exists (fun iq => Fphi iq.1 iq.2).
      move => i.
      by have []//:= rlzr (fun q => phin (i, q)) (xs i); first by exists (ys i).
    suff /choice [fa prp]: forall i, exists fai,
                    (fun q' => Fphi (i, q')) \describes fai \wrt Y
                    /\
                    f (xs i) fai. 
    - by exists fa; split => i; have []:= prp i.
    move => i.
    have [ | | _ prp]//:= rlzr (fun q => (phin (i, q))) (xs i); first by exists (ys i).
    have [ | fa]//:= prp (fun q' => Fphi (i, q')).
    by exists fa.
  Qed.

  Lemma ptw_hcr (X Y: cs) (f: X ->> Y): f \has_continuous_realizer ->
             (mf_ptw I f : X\^I ->> Y\^I) \has_continuous_realizer.
  Proof.
    move => [F [rlzr cont]].
    exists (ptw_rlzr F); split.
    - exact/ptw_rlzr_spec.
    exact/ptw_rlzr_cntop.
  Qed.

  Definition ptw R T (f: R -> T) (rs: I -> R) i := f (rs i).
  
  Lemma ptw_comp R T (f: R -> T) rs: (ptw f rs) =1 f \o_f rs.
  Proof. done. Qed.

  Lemma F2MF_ptw R T (f: R -> T):
    mf_ptw I (F2MF f) =~= F2MF (ptw f).
  Proof.
    move => rs ts /=; split => [prp | <-]//.
    exact/functional_extensionality.
  Qed.

  Lemma ptw_cont (X Y: cs) (f: X -> Y):
    f \is_continuous -> (ptw f: X\^I -> Y\^I) \is_continuous.
  Proof.
    move => cont.
    rewrite /continuous -F2MF_ptw.
    exact/ptw_hcr.
  Qed.
    
  Definition curry R S T (f: R -> S -> T) rs := f rs.1 rs.2.

  Definition cptw_op (X Y Z: cs) (op: X \*_cs Y -> Z): X\^I \*_cs Y\^I -> Z\^I :=
    curry (ptw_op (uncurry op)).

  Lemma cptw_ptw (X Y Z: cs) (op: X \*_cs Y -> Z):
    (cptw_op op) = (@ptw (X \*_cs Y) Z op) \o_f (@cs_zip I somei I_count choice _ _).
  Proof. done. Qed.
  
  Lemma cptw_cont X (op: X \*_cs X -> X):
    op \is_continuous -> (cptw_op op) \is_continuous.
  Proof.
    move => [F [/rlzr_F2MF Frop Fcont]].
    pose np := (@name_pair X X: name_space X -> name_space X -> name_space (X \*_cs X)).
    exists (make_mf (fun (phi: name_space (_\^I \*_cs (_\^I))) psi => forall n,
	                 F (np (fun q => lprj phi (n, q)) (fun q => rprj phi (n, q))) (fun q => psi (n, q)))).
    rewrite rlzr_F2MF; split => [phi [xn yn] [/= phinxn phinyn] | ].
    - have nms n: (np (fun q : queries X => lprj phi (n, q))
		      (fun q : queries X => rprj phi (n, q)))
                    \describes (xn n, yn n) \wrt (X \*_cs X).
      + by split => /=; [apply/phinxn | apply/phinyn].
      split => [ | psi FpsiFpsi n].
      + have fd n:= (Frop (np (fun q => lprj phi (n, q))
			      (fun q => rprj phi (n, q))) (xn n, yn n) (nms n)).1.
        have [Fphi Fphiprp]:= choice fd.
        by exists (fun nq => Fphi nq.1 nq.2) => n /=; apply Fphiprp.
      have val n:= (Frop (np (fun q => lprj phi (n, q))
		             (fun q => rprj phi (n, q)))
                         (xn n, yn n) (nms n)).2.
      by rewrite /ptw/=; apply/val.
    apply cont_choice => phi Fphi /=FphiFphi [n q].
    pose phin:= np (fun q => lprj phi (n, q)) (fun q => rprj phi (n, q)).
    have [ | Lf mod]:= Fcont phin (fun q' => Fphi (n, q')); first exact/FphiFphi.
    exists (map (fun q' => match q' with
	                   | inl q'' => inl (n, q'')
	                   | inr q'' => inr (n, q'')
	                   end) (Lf q)) => psi /coin_lstn coin Fpsi eq.
    apply/(mod q (fun q' => match q' with
	                    | inl q'' => ((psi (inl (n, q''))).1, somea _)
	                    | inr q'' => (somea _, (psi (inr (n, q''))).2)
                            end) _ (fun q => Fpsi (n, q))); last by apply eq.
    apply/coin_lstn => [[q' | q'] lstn].
    + rewrite /phin/= -(coin (inl (n,q'))) /lprj//.
      by elim: (Lf q) lstn => // a L ih /= [ -> | ]; [left | right; apply/ih].
    rewrite /phin/= -(coin (inr (n,q'))) /rprj//.
    by elim: (Lf q) lstn => // a L ih /= [ -> | ]; [left | right; apply/ih].
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
      (phi \is_limit_of (uncurry phin))%baire).
  Arguments limit {X}.
  Local Notation "x \is_limit_of xn" := (limit xn x).

  Lemma lim_prd (X Y: cs) xn (x: X) yn (y: Y):
    (x, y) \is_limit_of (cs_zip (xn, yn))
    <->
    x \is_limit_of xn /\ y \is_limit_of yn.
  Proof.
    split => [[phipsin [phipsi [nm [[lnm rnm] lmt]]]] |].
    - split.
      + exists (lprj (nzip_rlzrf phipsin)); exists (lprj phipsi).
        split => [i | ]; [by have []:= nm i | split => // L].
        have [N prp]:= lmt (map inl L).
        exists N => m ineq /=; have := prp m ineq.
        elim L => // q K ih [coin prp']; split; last exact/ih/prp'.
        by rewrite /lprj coin.
      exists (rprj (nzip_rlzrf phipsin)); exists (rprj phipsi).
      split => [i | ]; [by have []:= nm i | split => // L].
      have [N prp]:= lmt (map inr L).
      exists N => m ineq /=; have := prp m ineq.
      elim L => // q K ih [coin prp']; split; last exact/ih/prp'.
      by rewrite /rprj coin.
    move => [[phin [phi [phinxn [phinx lmt]]]] [psin [psi [psinxn [psinx lmt']]]]].
    exists (fun iqq' => match iqq'.2 with
                        | inl q => (phin (iqq'.1, q), somea Y)
                        | inr q' => (somea X, psin (iqq'.1, q'))
                        end).
    exists (name_pair phi psi).
    split => [i | ]; first by split; rewrite /lprj/rprj/=.
    split => //.
    elim => [ | [q | q'] L [N ih]]; first by exists 0.
    - have [N' coin]:= lmt [::q].
      exists (maxn N N') => m ineq.
      split; last exact/ih/leq_trans/ineq/leq_maxl.
      rewrite /uncurry/=.
      by have [ | ->]:= coin m; first by apply/leq_trans/ineq/leq_maxr.
    have [N' coin]:= lmt' [::q'].
    exists (maxn N N') => m ineq.
    split; last exact/ih/leq_trans/ineq/leq_maxl.
    rewrite /uncurry/=.
    by have [ | ->]:= coin m; first by apply/leq_trans/ineq/leq_maxr.
  Qed.

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
    FunctionalCountableChoice_on (questions Y) ->
    F \realizes (F2MF f) -> F \is_sequentially_continuous_operator ->
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

  Lemma cont_scnt (X Y: cs) (f: X -> Y):
    FunctionalCountableChoice_on (questions Y) -> f \is_continuous -> sequentially_continuous f.
  Proof. move => choice [F [rlzr /cont_scnt cont]]; exact/rlzr_scnt/cont. Qed.
End limits.
Arguments limit {X}.
Notation "x \is_limit_of xn" := (limit xn x): cs_scope.
Notation "f \is_sequentially_continuous_in x" := (sequential_continuity_point f x): cs_scope.
Notation "f \is_sequentially_continuous" := (sequentially_continuous f): cs_scope.
Notation "F \is_sequentially_continuous_operator":= (seq_cont.sequentially_continuous F) (at level 2): cs_scope.
