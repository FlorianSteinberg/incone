From mathcomp Require Import ssreflect seq ssrfun ssrbool ssrnat eqtype bigop.
From rlzrs Require Import all_rlzrs.
From metric Require Import all_metric reals standard Qmetric.
Require Import axioms all_cs cs_mtrc baire_metric hyper_spaces.
Require Import Qreals Reals Psatz ClassicalChoice FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import QArith.

Local Open Scope R_scope.
Notation "'\|' x '|'" := (Rabs x) (at level 30).

Section reals_via_rational_approximations.
  Coercion Q2R: Q >-> R.
  (*
    One way to encode real numbers is to use functions phi: Q -> Q on the rationals that
    return approximations when given an accuracy requirement "eps", i.e. such that
    forall eps > 0, |x - phi(eps)| <= eps. This representation is very straight forward to
    specify by a relation. This relation should be marked as a specification of a function,
    which in particularly means that the arguments should not be treated interchangably.
    This is done by constructing a multifunction (mf) from the relation.
   *)
  
  Definition rep_RQ := make_mf (fun (phi: Q -> Q) x =>
                       forall (eps: Q), 0 < eps -> \|x - phi eps| <= eps).

  (*
    The first thing to check is that this relation is deterministic so that it uniquely specifies
    a partial function. For multivalued functions this property is called being "singlevalued".
   *)
  Lemma rep_RQ_sing: rep_RQ \is_singlevalued.
  Proof.
    move => phi x x' phinx phinx'.
    apply/(cond_eq_f accf_Q2R_0) => eps eg0.
    set r := Q2R (phi (eps/(1 + 1))%Q); rewrite /R_dist.
    have ->: (x-x') = ((x-r) + (r-x')) by field.
    apply/Rle_trans/Rle_trans; first exact/Rabs_triang.
    - apply /Rplus_le_compat; last rewrite Rabs_minus_sym; [apply phinx | apply phinx'];
      rewrite Q2R_div; try lra; rewrite {2}/Q2R/=; lra.
    by rewrite Q2R_div; try lra; rewrite {2 4}/Q2R/=; lra.
  Qed.

  (*
    To prove that the specified function is a representation, it remains to prove that each real
    number is assigned a name. For a function this property is called "surjective", for single-
    valued multifunctions this is equivalent to the dual notion of totality, so it is called and
    thus called being "cototal".
   *)
  Check pf2MF_cotot.

  Lemma rep_RQ_sur: rep_RQ \is_cototal.
  Proof.
    move => x; pose aprx (eps: Q) := (inject_Z (Int_part (x/eps)) * eps)%Q.
    exists aprx => eps eg0.
    have ->: (x - aprx eps) = (x/eps - Int_part (x/eps)) * eps.
    - by rewrite Q2R_mult {1}/Q2R/=; field; lra.
    have []:= base_Int_part (x/eps); intros.
    rewrite Rabs_mult !Rabs_pos_eq; try lra.
    by rewrite -[X in _ <= X]Rmult_1_l; apply/Rmult_le_compat; lra.
  Qed.

  (*
    To define a represented space, we first bundle the information that justifies that Q can be
    used as discrete data, namly that it is an inhabited and countable type. The bundle we name
    B_RQ, where "B" is for Baire space and "RQ" is for "reals encoded by rationals".
   *)
  Definition B_RQ: naming_space.
    by exists Q Q; try exact/count.Q_count; exact/0%Q.
  Defined.

  (**
     And afterwards define a represented space ("continuity_space" or for short "cs" in incone)
     of Cauchy real numbers. We use "Canonical" instead of "Definition" so that the additional
     Structure that we added will be automatically found by Coq whenever it is needed (or at
     least in most cases).
   **)
  Canonical RQ: continuity_space.
    by exists R B_RQ rep_RQ; split; [apply/rep_RQ_sur | apply/rep_RQ_sing].
  Defined.
End reals_via_rational_approximations.
  
Section addition.
  (**
     For functions between continuity spaces, there is a natural notion of continuity.
   **)
  Check cont_spec.
  (**
     Where continuity on Baire space is defined as the return value being determined by
     the return values of the functional input on a finite list of inputs. The statment is
     a little easier for partial functions (PF2MF is the name of the function that takes a
     partial function to the corresponding multi-function). The notion for multifunctions
     is such that it implies singlevaluedness and incone provides a proof that the metric
     notion of continuity is actually captured.
   **)
  Check cont_PF2MF.
  Check cont_f_cont.
  (**
     And where being a realizer means to translate names of the input to names of the output:
   **)
  Check F2MF_rlzr.
  (**
     For instance the function that modifies the return-value of a name to be the negative
     is a realizer of the function x |-> -x and since it only needs to evaluate the name for one
     precision it is continuous.
   **)
  
  Definition Ropp_rlzrf phi (eps: Q) := Qopp (phi eps).

  (**
     Note that this defines a proper function, to prove correctness we cast this function to
     its specification which is done by the function F2MF (for "function to multi-function").
   **)
  Lemma Ropp_rlzr_spec: (F2MF Ropp_rlzrf: B_RQ ->> B_RQ) \realizes (Ropp: RQ -> RQ).
  Proof.
    rewrite F2MF_rlzr_F2MF => phi x phinx eps epsg0 /=.
    by rewrite Q2R_opp; move: (phinx eps epsg0); split_Rabs; lra.
  Qed.

  (**
     We may do the same for continuity and prove "F2MF Ropp_rlzrf \is_continuous_operator".
     Alternatively, we can use a simplified definition for functions.
   **)
  Lemma Ropp_rlzr_cntf: Ropp_rlzrf \is_continuous_functional.
  Proof.
    by rewrite /Ropp_rlzrf => phi; exists (fun eps => [:: eps]) => psi q' [<-].
  Qed.

  Lemma Ropp_cont: (Ropp: RQ -> RQ) \is_continuous.
  Proof.
    by exists (F2MF Ropp_rlzrf); split; try exact/Ropp_rlzr_spec; apply/cntop_cntf/Ropp_rlzr_cntf.
  Qed.

  (**
     The same can be done for the other arithmetic operations. For the binary operations, the
     product of representes spacs can be used.
   **)
  Definition Rplus_rlzrf (phi: B_RQ \*_ns B_RQ) (eps: Q) :=
    (lprj phi (eps/(1+1)) + rprj phi (Qdiv eps (1+1)))%Q.

  Definition Rplus_rlzr: B_(RQ \*_cs RQ) ->> B_RQ:= F2MF Rplus_rlzrf.

  (**
     Note that the type of Rplus is R -> R -> R, so to make the function a function between
     represented spaces it needs to first be curried to have type R * R.
   **)
  Lemma Rplus_rlzr_spec:
    Rplus_rlzr \realizes (curry Rplus: RQ \*_cs RQ -> RQ).
  Proof.
    apply/F2MF_rlzr => phi x /prod_name_spec phinx eps eg0.
    rewrite /Rplus_rlzr Q2R_plus.
    set r := Q2R (lprj phi (Qdiv eps (1 + 1))).
    set q := Q2R (rprj phi (Qdiv eps (1 + 1))).
    have ->: (x.1 + x.2 - (r + q)) = (x.1 - r + (x.2 - q)) by field.
    apply/Rle_trans; first exact/Rabs_triang; rewrite -(eps2 (Q2R eps)).
    have eq: Q2R eps * / 2 = Q2R (eps / (1 + 1)).
    - by symmetry; rewrite Q2R_div; first rewrite {2}/Q2R/=; lra.
    by rewrite eq; apply: Rplus_le_compat; apply phinx; lra.
  Qed.

  Lemma Rplus_rlzr_cntop: Rplus_rlzr \is_continuous_operator.
  Proof.
    rewrite cont_F2MF => phi.
    exists (fun eps => [:: inl (Qdiv eps (1 + 1)); inr (Qdiv eps (1 + 1))]).
    by rewrite /Rplus_rlzrf/lprj/rprj => psi q' /= [-> [->]].
  Qed.

  Lemma Rplus_cont: (curry Rplus) \is_continuous.
  Proof.
    by exists Rplus_rlzr; split; try exact/Rplus_rlzr_spec; apply/Rplus_rlzr_cntop.
  Qed.
End addition.

  Definition Qabs r := Zabs (Qnum r) # (Qden r).

  Lemma Qabs_Rabs r: Q2R (Qabs r) = \|r|.
  Proof.
    rewrite /Qabs/Q2R/= -Rabs_Zabs -{1}(Rabs_pos_eq (/QDen r)).
    - by symmetry; apply/Rabs_mult.
    by apply/Rlt_le/Rinv_0_lt_compat; have /IZR_lt:= Pos2Z.is_pos (Qden r).
  Qed.

Section multiplication.
  (**
     Multiplication is more involved as the precision of approximations that have to be used
     depends on the size of the inputs. Roughly one would proceeds as follows: given phi and
     psi that are Cauchy names of x and y make the Ansatz that there is a name of x * y that
     can be written as eps |-> phi(delta) * psi(delta), where delta should be chosen
     appropriatelly depending on eps. A triangle argument gives
     |x * y - phi(delta) * psi(delta)| <= |x - phi(delta)| * |y| + |y - psi(delta)| * |phi(delta)|,
     and thus delta should be chosen small enough to make both terms small. One may do this by
     using by first getting an upper bounds of a x and y from phi and psi as follows: 
   **)      
  Definition get_ub phi := ((upQ (Qabs (phi (1#2)))#1) + 1)%Q.

  (**
     We gather some lemmas about this function that we will need for the proof of conrrectness
     of the multiplication.
   **)

  Lemma gub_Q2R phi: Q2R (get_ub phi) = upQ (Qabs (phi (1#2))) + 1.
  Proof. by rewrite Q2R_plus /Q2R /= Rinv_1 !Rmult_1_r. Qed.

  Lemma gub_pos phi: 1 <= Q2R (get_ub phi).
  Proof.
    suff: 0 <= upQ (Qabs (phi (1#2))) by rewrite gub_Q2R; lra.
    apply/Rlt_le/Rle_lt_trans/(archimedQ (Qabs (phi (1#2)))).1.
    by rewrite Qabs_Rabs; apply/Rabs_pos.
  Qed.

  Lemma gub_spec phi (x: RQ): phi \is_name_of x -> \|x| + /2 <= Q2R (get_ub phi).
  Proof.
    rewrite gub_Q2R => phinx. 
    apply/Rle_trans/Rplus_le_compat_r/Rlt_le/Rle_lt_trans/(archimedQ _).1.
    - have {1}->: (x = phi (1 # 2) + (x - phi (1 # 2)))%R by lra.    
      apply/Rle_trans; first exact/Rplus_le_compat_r/Rabs_triang.
      rewrite Rplus_assoc; apply/Rplus_le_compat; first exact/Rle_refl.
      by apply/Rle_trans; first apply/Rplus_le_compat_r; first apply/phinx; rewrite /Q2R /=; lra.
    by rewrite Qabs_Rabs; split_Rabs; lra.
  Qed.

  (**
     Finally, to guarantee that our upper bound to x is also an upper bound to phi(elta), we will
     guarantee that delta is always smaller than one by simly truncating it.
   **)
  
  Definition trunc eps:Q := if Qlt_le_dec eps 1 then eps else 1%Q.
  
  Lemma trunc_le eps: Q2R (trunc eps) <= Q2R eps.
  Proof. by rewrite /trunc; case: (Qlt_le_dec eps 1) => ass /=; [lra | apply Qle_Rle]. Qed.

  Lemma truncI eps: 0 < Q2R eps -> 0 < trunc eps <= 1.
  Proof.
    by rewrite /trunc; case: (Qlt_le_dec eps 1) => /=[/Qlt_Rlt | /Qle_Rle]; lra.
  Qed.

  (**
     Which leaves us with the following algorithm for multiplication:
   **)
  Definition Rmult_rlzrf (phi: B_RQ \*_ns B_RQ) (eps: Q) :=
    (lprj phi (trunc eps / (1 + 1)/(get_ub (rprj phi)))
     *
     (rprj phi (eps / (1 + 1)/(get_ub (lprj phi)))))%Q.

  Definition Rmult_rlzr : B_(RQ \*_cs RQ) ->> B_RQ:= F2MF Rmult_rlzrf.

  (**
     The proof of correctness is now pretty straight forward.
   **)
  Lemma Rmult_rlzr_spec:
    Rmult_rlzr \realizes (curry Rmult: RQ \*_cs RQ -> RQ).
  Proof.
    rewrite F2MF_rlzr => phi [x y] /prod_name_spec [phinx psiny] eps eg0 /=.
    rewrite Q2R_mult; have eq: eps * /2 = (eps/(1 + 1))%Q by rewrite Q2R_div /Q2R /=; try lra.
    set r := Q2R (lprj phi (trunc eps / (1 + 1) / get_ub (rprj phi))%Q).
    set q := Q2R (rprj phi (eps / (1 + 1) / get_ub (lprj phi))%Q).
    have g0: 0 < Q2R (eps / (1 + 1)) by rewrite Q2R_div; first rewrite {2}/Q2R/=; lra.
    rewrite -(eps2 eps); have ->: (x * y - r * q) = ((x - r) * y + r * (y - q)) by field.
    apply/Rle_trans/Rplus_le_compat; first exact/Rabs_triang; rewrite Rabs_mult.
    - have gub_ineq: \|y| <= get_ub (rprj phi) by have := gub_spec psiny; lra.
      have gub_pos:= gub_pos (rprj phi); apply/Rle_trans.
      + apply/Rmult_le_compat; try exact/Rabs_pos; last exact/gub_ineq.
        apply/phinx; rewrite Q2R_div => [ | /Qeq_eqR]; try lra.
        apply/Rdiv_lt_0_compat; first rewrite Q2R_div; try lra.
        suff ?: 0</(1 + 1)%Q by have [? _]:= truncI eg0; rewrite /Rdiv; try nra.
        by apply/Rinv_0_lt_compat; rewrite /Q2R /=; lra.
      rewrite Q2R_div => [ | /Qeq_eqR]; try lra.
      rewrite Rmult_assoc Rinv_l; first rewrite Q2R_div; try lra.
      by have := trunc_le eps; rewrite /Q2R /=; try lra.
    suff r_ineq: \|r| <= get_ub(lprj phi).
    - have gub_pos:= gub_pos (lprj phi).
      apply/Rle_trans;first apply/Rmult_le_compat/psiny; try exact/Rabs_pos; first exact/r_ineq.
      + rewrite Q2R_div => [ | /Qeq_eqR]; try lra.
        by rewrite -eq; apply/Rdiv_lt_0_compat; lra.
      rewrite Q2R_div => [ | /Qeq_eqR]; try lra.
      by rewrite -Rmult_assoc Rmult_comm -Rmult_assoc Rinv_l; try lra.
    have ->: r = r - x + x by ring.
    apply/Rle_trans; first exact/Rabs_triang.
    apply/Rle_trans/gub_spec/phinx; rewrite Rabs_minus_sym [X in _ <= X]Rplus_comm.
    apply/Rplus_le_compat_r/Rle_trans; first apply/phinx; last first.
    - rewrite !Q2R_div => [ | | /Qeq_eqR]; try by have := gub_pos (rprj phi); lra.
      have [pos ineq]:= truncI eg0.
      rewrite {2}/Q2R /= Rinv_1 Rmult_1_r /Rdiv.
      have gl1: /get_ub (rprj phi) <= 1 by rewrite -Rinv_1; apply/Rinv_le_contravar/gub_pos; lra.
      rewrite -{2}(Rmult_1_l (/2)) -[X in _ <= X]Rmult_1_r.
      apply/Rmult_le_compat => //; try lra.
      apply/Rlt_le/Rinv_0_lt_compat.
      by have ps:= gub_pos (rprj phi); apply/Rlt_le_trans/ps; lra.
    have gub_pos:= gub_pos (rprj phi).
    rewrite Q2R_div => [ | /Qeq_eqR]; try lra.
    rewrite Q2R_div; try lra.
    rewrite {2}/Q2R/= Rinv_1 Rmult_1_r /Rdiv; have := truncI eg0.
    have zlg: 0 < / get_ub (rprj phi) by apply/Rinv_0_lt_compat; lra.
    by intros; apply/Rmult_lt_0_compat/zlg; try lra.
  Qed.

  Lemma Rmult_rlzr_cntop: Rmult_rlzr \is_continuous_operator.
  Proof.
    apply/cont_F2MF => phi; rewrite /Rmult_rlzrf /=.
    exists (fun eps => [:: inl (1 # 2); inr (1 # 2);
                        inl (trunc eps / (1 + 1) / get_ub (rprj phi))%Q;
                        inr (eps / (1 + 1) / get_ub (lprj phi))%Q]).
      by rewrite /get_ub/lprj/rprj => eps psi /= [-> [-> [-> [->]]]].
  Qed.  

  Lemma Rmult_cont: (fun (xy: cs_prod RQ RQ) => xy.1 * xy.2: RQ) \is_continuous.
  Proof. by exists Rmult_rlzr; split; try exact/Rmult_rlzr_spec; apply/Rmult_rlzr_cntop. Qed.
End multiplication.    
    
Section limit.
  (**
     A function that works on slightly more complicated spaces than finite products of real numbers
     is the limite function. I.e. the partial function lim: R^N -> R that takes a sequence of
     real numbers to the limit of this sequence if it exists. A definition of this function using
     The Metric notions of a limit can be found in the standard library and the metric lirary
     has a version that is proven identical to that from the standard library but also works for
     psuedo-metric spaces.
   **)
  Notation lim:= metric_limit.

  (**
     This function is discontinuous, and it is thus impossible to implement. We would like to give
     A proof that this is so. For this we need names for rational numbers and sequences when
     considered as sequences of real numbers.
   **)
  
  Lemma cnst_name q: (cnst q) \describes (Q2R q) \wrt RQ.
  Proof. by rewrite /cnst => eps; split_Rabs; lra. Qed.
  
  Lemma cnst_sqnc_name q: (cnst q) \describes (cnst (Q2R q)) \wrt (RQ\^w).
  Proof. by rewrite /cnst => n eps ineq; split_Rabs; lra. Qed.
  
  Lemma Q_sqnc_name qn:
    (fun neps => qn neps.1) \describes (fun n => Q2R (qn n)) \wrt (RQ\^w).
  Proof. by move => n eps ineq /=; split_Rabs; lra. Qed.

  Lemma leq_bigmax T (F: T -> nat) (K: seq T) i:
    i \from K -> (F i <= \max_(i <- K) F i)%nat.
  Proof.
    elim: K => // q K ih /=[-> | lstn]; rewrite big_cons; first exact/leq_maxl.
    exact/leq_trans/leq_maxr/ih.
  Qed.
  
  Lemma lim_not_cont: ~ (lim: RQ\^w ->> RQ) \has_continuous_realizer.
  Proof.
    move => [/= F [/cntop_spec cont rlzr]].
    pose xn := cnst (Q2R 0): RQ\^w.
    have limxn0: lim (xn: nat -> M2PM metric_R) (Q2R 0).
    - by exists 0%nat; rewrite /xn/cnst/distance/=/R_dist; split_Rabs; lra.
    have qnfdF: cnst 0%Q \from dom F.
    - by apply/(ntrvw.rlzr_dom rlzr); [exact/cnst_sqnc_name | exists (Q2R 0)].
    have [Lf Lmod]:= cont (cnst 0%Q) qnfdF.
    pose m:= \max_(i <- Lf 1%Q) i.1.
    have mprop n eps: (n, eps) \from (Lf 1%Q) -> (n <= m)%nat by move => /(leq_bigmax fst) /=.
    pose yn:= (fun n => Q2R (if (n <= m)%nat then 0%Q else 3#1)): RQ\^w.
    pose rn (p: nat * Q) := if (p.1 <= m)%nat then 0%Q else 3#1.
    have rnyn: rn \describes yn \wrt (RQ\^w) by apply/Q_sqnc_name.
    have limyn3: lim (yn: nat -> M2PM metric_R) 3.
    - exists (S m) => n /leP ineq; rewrite /yn.
      by case: ifP => [/leP ineq' | ]; [lia | rewrite /distance/=; split_Rabs; lra].
    have [phi Frnphi]: rn \from dom F by apply /(ntrvw.rlzr_dom rlzr); first exact/rnyn; exists 3.
    have coin: (cnst 0%Q) \and rn \coincide_on (Lf 1%Q).
    - apply /coin_agre => [[n eps] listin].
      rewrite /cnst /rn; case: ifP => // /= /leP ineq.
      by exfalso; apply/ineq/leP/mprop/listin.
    have [psi Fqnpsi]:= qnfdF.
    have eq: psi 1%Q == phi 1%Q.
    - have [a' crt]:= Lmod 1%Q; rewrite (crt rn coin phi)// (crt (cnst 0%Q) _ psi) //.
      exact/coin_ref.
    have := Qeq_eqR (psi 1%Q) (phi 1%Q) eq.
    have psin0: psi \describes 0 \wrt ( RQ).
    - apply /(rlzr_val_sing _ rlzr)/Fqnpsi/lim_cnst; first exact/metric_spaces.lim_sing.
      by rewrite /cnst/=/Q2R /=; split_Rabs; lra.
    have phin3: phi \describes 3 \wrt RQ.
    - by apply/(rlzr_val_sing _ rlzr)/Frnphi/limyn3; first exact/metric_spaces.lim_sing.
    have l01: 0 < Q2R 1 by rewrite /Q2R/=; lra.
    have:= psin0 1%Q l01; have:= phin3 1%Q l01.
    by rewrite {2 4}/Q2R/=; split_Rabs; lra.
  Qed.

  (**
     To get an implementable version of the limit operator, we can restrict its domain to only
     reach over those sequences that converge efficiently.
   **)
  Check lim_eff_spec.
  Print fast_Cauchy_sequence.
  Notation lim_eff:= (efficient_limit: RQ\^w ->> RQ).

  (**
     For a fast converging Cauchy sequence an eps-approximation to the limit can be produced
     by first geting some n such that /2^n <= eps and then using an eps/2 approximation of the
     n+1-st element of the sequence. An appropriate n can for instance be found by using the
     number of bits of the denominator of eps.     
   **)

  Definition lim_eff_rlzrf phin eps :=
      phin ((Pos_size (Qden eps)).+1, (eps/(1 + 1))%Q): Q.
    
  Definition lim_eff_rlzr : name_space (RQ\^w) ->> name_space RQ := F2MF lim_eff_rlzrf.
    
  Lemma lim_eff_rlzr_spec:
    lim_eff_rlzr \solves lim_eff.
  Proof.
    rewrite F2MF_slvs => psi xn psinxn [x lim].
    exists x; split => // eps epsg0.
    set N:= (Pos_size (Qden eps)); set y:= Q2R (lim_eff_rlzrf psi eps).
    have ->: x - y = x - xn N.+1 + (xn N.+1 - y) by lra.
    rewrite /y /lim_eff_rlzrf -/N.
    apply/Rle_trans/Rle_trans; first exact/Rabs_triang.
    - apply/Rplus_le_compat; first exact/lim.
      by apply psinxn; rewrite Q2R_mult {2}/Q2R/=; lra. 
    have lt1:= pow_lt 2 (Pos_size (Qden eps)); have lt2:= size_Qden epsg0.
    by rewrite Q2R_mult {2}/Q2R /= /N Rinv_mult_distr; lra.
  Qed.

  Lemma lim_eff_rlzr_cntop : lim_eff_rlzr \is_continuous_operator.
  Proof.
    apply/cont_F2MF => phi; rewrite /lim_eff_rlzrf.
    by exists (fun eps => [:: ((Pos_size (Qden eps)).+1, (eps * (1#2))%Q)]) => eps psi [].
  Qed.

  Lemma lim_eff_hcr: lim_eff \has_continuous_realizer.
  Proof.
    by exists lim_eff_rlzr; split; try exact/lim_eff_rlzr_spec; apply/lim_eff_rlzr_cntop.
  Qed.
End limit.

Section metric_Qreals.
  Definition Rm: cs := metric_cs count.Q_count Q_dense.
  Definition Rm2RQ_rlzrf (phi: B_(Rm)) eps := phi (Pos_size (Qden eps)).

  Lemma Rm2RQ_rlzr_cntop: Rm2RQ_rlzrf \is_continuous_functional.
  Proof.
    move => phi; exists (fun eps => [:: Pos_size (Qden eps)]).
    by rewrite /Rm2RQ_rlzrf => eps psi [->].
  Qed.

  Lemma Rm2RQ_rlzrf_spec:
    (F2MF Rm2RQ_rlzrf: B_(Rm) ->> B_RQ) \realizes id.
  Proof.
    apply/F2MF_rlzr_F2MF => phi x phinx eps eg0.
    rewrite /Rm2RQ_rlzrf.
    apply/Rle_trans; first exact/phinx.
    exact/size_Qden.
  Qed.

  Lemma Rm2RQ_cont:
    (id: Rm -> RQ) \is_continuous.
  Proof.
    exists (F2MF Rm2RQ_rlzrf).
    split; try exact Rm2RQ_rlzrf_spec.
    exact/cont_F2MF/Rm2RQ_rlzr_cntop.
  Qed.

  Definition RQ2Rm_rlzrf (phi: B_RQ) n := phi (Qpower (1 + 1) (-Z.of_nat n)).

  Lemma Qpower_spec r n: ~ r == 0 -> Q2R (r^(Z.of_nat n))%Q = (Q2R r) ^ n.
  Proof.
    case: n => [ | n neq]; first by rewrite /Q2R /= Rinv_1; lra.
    symmetry; rewrite /= /Qpower_positive.
    elim: n => [/= | n ih]; first by rewrite Rmult_1_r; lra.
    have /= /Qeq_eqR ->:= pow_pos_succ Q_Setoid Qmult_comp Qmult_assoc r (Pos.of_succ_nat n).
    by rewrite Q2R_mult ih.
  Qed.

  Lemma Qpower_minus r z: Q2R (Qpower r z) = Q2R (Qpower (Qinv r) (Zopp z)).
  Proof.
    apply/Qeq_eqR.
    suff eq q p: q^ (Z.pos p) == (/q)^(-Zpos p).
    - case: z => // p.
      by rewrite -Pos2Z.opp_pos Zopp_involutive -{1}(Qinv_involutive r); symmetry; apply/eq.
    rewrite -positive_nat_Z.
    case: (Pos.to_nat p) => //.
    elim => [ | n /=]; first by rewrite /= Qinv_involutive.
    rewrite /Qpower_positive => ih.
    have ->:= pow_pos_succ Q_Setoid Qmult_comp Qmult_assoc q (Pos.of_succ_nat n).
    have ->:= pow_pos_succ Q_Setoid Qmult_comp Qmult_assoc (Qinv q) (Pos.of_succ_nat n).
    by rewrite ih Qinv_mult_distr Qinv_involutive.
  Qed.

  Lemma tpmn_Q n: /2^n = ((/(1 + 1)) ^ (Z.of_nat n))%Q.
  Proof.
    rewrite Rinv_pow; try lra.
    suff -> : /2 = Q2R (/(1 + 1)) by rewrite -Qpower_spec.
    rewrite /Q2R /=; lra.
  Qed.

  Lemma RQ2Rm_rlzrf_spec: (F2MF RQ2Rm_rlzrf: B_RQ ->> B_(Rm)) \realizes id.
  Proof.
    apply/F2MF_rlzr.
    move => phi x phinx n /=.
    rewrite /id.
    suff eq: /2^n = ((1 + 1)^(- Z.of_nat n))%Q.
    - by apply/Rle_trans; first apply/phinx; rewrite -eq; try lra; apply/tpmn_lt.
    suff ->: /2 ^ n = ((/ /(1 + 1))^(-Z.of_nat n))%Q by apply/Qeq_eqR; rewrite Qinv_involutive.
    rewrite -Qpower_minus.
    by rewrite Qpower_spec; [rewrite /Q2R /= Rmult_1_l Rinv_pow | rewrite /Qinv /=]; lra.
  Qed.

  Lemma RQ2Rm_cont: (id: RQ -> Rm) \is_continuous.
  Proof.
    exists (F2MF RQ2Rm_rlzrf); split; try exact RQ2Rm_rlzrf_spec.
    apply/cont_F2MF => phi; rewrite /RQ2Rm_rlzrf.
    by exists (fun n => [::Qpower (1 + 1) (-Z.of_nat n)]) => n psi [->].
  Qed.

  Lemma iso_RQ_Rm: RQ ~=~ Rm.
  Proof.
    apply/iso_spec; exists id; split; first exact/RQ2Rm_cont.
    by exists id; split; first exact/Rm2RQ_cont.
  Qed.

  Lemma RQ_Rm_lim: @limit RQ =~= @limit Rm.
  Proof.
    move => xn x.
    split => lim.
    - have /cont_scnt cont:= RQ2Rm_cont.
      by have := cont x xn lim.
    have /cont_scnt cont:= Rm2RQ_cont.
    by have := cont x xn lim.
  Qed.
    
  Lemma RQ_Rm_cont (f: R -> R): (f: RQ -> RQ) \is_continuous <-> (f: Rm -> Rm) \is_continuous.
  Proof.
    split => cont.    
    - have ->: f = (id:RQ -> Rm) \o_f f \o_f (id: Rm -> RQ) by trivial.
      exact/cont_comp/Rm2RQ_cont/cont_comp/cont/RQ2Rm_cont.
    have ->: f = ((id:Rm -> RQ) \o_f f) \o_f (id: RQ -> Rm) by trivial.
    exact/(cont_comp Rm2RQ_cont)/(cont_comp _ RQ2Rm_cont).
  Qed.
End metric_Qreals.

Section inversion.
  Definition inversion := make_mf (fun x y => x * y = 1).

  Lemma dom_inv: dom inversion === make_subset(fun x => x <> 0).
  Proof.
    move => x; split => [[y/= eq eq'] | /= neq]; first by rewrite eq' in eq; lra.
    by exists (Rinv x); rewrite Rinv_r.
  Qed.

  Lemma Rinv_spec: (fun x => Rinv x) \is_choice_for inversion.
  Proof.
    by move => x [y /=]; case: (total_order_T x 0) => [[?|{1 2}->]|?]; try rewrite Rinv_r; lra.
  Qed.

  Lemma Rabs_le_up x: \|x| <= \|up(x)| + 1.
  Proof. by have := archimed x; split_Rabs; lra. Qed.
  
  Lemma Rinv_not_cont: ~ (Rinv: RQ -> RQ) \is_continuous.
  Proof.
    move => /cont_scnt cont.
    have lim : limit (fun n => /2^n) 0.
    - apply/RQ_Rm_lim/lim_mlim/lim_tpmn => n; exists n => m ineq /=.
      by rewrite Rminus_0_l Rabs_Ropp Rabs_pos_eq; [apply/tpmnP | apply/tpmn_pos].
    move: lim => /cont/RQ_Rm_lim/lim_mlim/lim_tpmn lim.
    have [N Nprp]:= lim (0%nat); move: lim => _.
    set M := (Z_size (Z.abs (up (/0))))%nat.
    have := Nprp (maxn N M.+1).+1.
    rewrite /ptw /= Rinv_1 Rinv_involutive => [ineq | ]; last by have:=pow_lt 2 (maxn N M.+1); lra.
    suff: 1 < \| /0 - 2 ^ (maxn N M.+1).+1| by apply/Rle_not_lt/ineq/leqW/leq_maxl.
    rewrite -Rabs_Ropp Ropp_minus_distr.
    apply/Rlt_le_trans/Rabs_triang_inv.
    rewrite Rabs_pos_eq; last by apply/pow_le; lra.
    suff: 1 + \| /0 | < 2^(maxn N M.+1).+1 by have := pow_le 2 (maxn N M).+1; lra.
    rewrite -tech_pow_Rmult double.
    apply/Rplus_le_lt_compat; first by apply/pow_R1_Rle; lra.
    apply/Rle_lt_trans; first exact/Rabs_le_up.
    rewrite Rabs_Zabs.
    apply/Rlt_le_trans.
    apply/Rplus_lt_le_compat/Rle_refl/Z_size_lt.
    apply/Rle_trans/Rle_pow/leP/leq_maxr; try lra.
    rewrite -tech_pow_Rmult double.
    by apply/Rplus_le_compat/pow_R1_Rle; first exact/Rle_refl; lra.
  Qed.

  Definition Qmin r r':=
    match Qlt_le_dec r r' with
    | left _ => r
    | right _ => r'
    end.

  Definition RQinv_M phi neps :=
    let n := neps.1 in
    let eps := neps.2 in
    let tpmn := ((/(1 + 1)) ^ (Z.of_nat n))%Q in
    let del := (Qabs (phi tpmn) - tpmn)%Q in
    if Qle_bool eps 0
    then Some 0%Q
    else if Qle_bool (Qabs (phi tpmn)) tpmn
         then None
         else Some (/(phi (Qmin (del/(1+1)) (eps * del^2/(1 + 1)))))%Q.

  Lemma Rabs0_dec x: decidable (0 < \|x|).
  Proof.
    case: (total_order_T x 0) => [[ | ->] | ]; try by left; split_Rabs; lra.
    right; split_Rabs; lra.
  Qed.

  Lemma QleP r q: reflect (Qle r q) (Qle_bool r q).
  Proof. by apply/(iffP idP) => /Qle_bool_iff //. Qed.
    
  Lemma inv_M_spec: (\F_(RQinv_M):B_RQ ->> B_RQ) \solves inversion.
  Proof.
    move => phi x phinx /dom_inv neq; rewrite /= in neq; split => [ | Fphi val].
    - apply/FM_dom => eps.
      case eq: (Qle_bool eps 0).
      + by exists 0%Q; exists 0%nat; rewrite /RQinv_M; case: ifP => //=; rewrite eq //.
      have ineq: (0 < eps)%Q by apply Qnot_le_lt => /Qle_bool_iff; rewrite eq.
      case: (Rabs0_dec x) => xineq; last by split_Rabs; lra.
      have [n nineq]:= dns0_tpmn xineq.
      exists (
          let tpmn := ((/(1 + 1)) ^ (Z.of_nat n.+1))%Q in
          let del := (Qabs (phi tpmn) - tpmn)%Q in
          (/(phi (Qmin (del/(1+1)) (eps * del^2/(1 + 1)))))%Q).
      exists n.+1.
      rewrite /RQinv_M.
      have prp: ~ / (1 + 1) == 0 by move => /Qeq_eqR; rewrite /Q2R /=; lra.
      case: ifP => [ | _]; first by rewrite eq.
      case: ifP => // /QleP/Qle_Rle/Rle_not_lt fls; exfalso; apply/fls.
      rewrite Qabs_Rabs Qpower_spec // {1}/Q2R /= Rmult_1_l -Rinv_pow; try lra.
      apply/Rle_lt_trans.
      + by apply/Rmult_le_compat_l/Rlt_le/nineq/Rlt_le/Rinv_0_lt_compat; lra.
      set del:= Qpower_positive (/(1+1)) (Pos.of_succ_nat n).
      have ->: Q2R (phi del) = x - (x - phi del) by ring.
      apply/Rlt_le_trans/Rabs_triang_inv.
      suff: \|x - phi del| < /2 * \|x| by split_Rabs; lra.
      apply/Rle_lt_trans; first apply/phinx; have /= ->:= @Qpower_spec (/(1 + 1))%Q n.+1 => //.
      + apply/Rmult_lt_0_compat; rewrite /Q2R /=; try lra.
        by rewrite Rmult_1_l -Rinv_pow; try lra; exact/tpmn_lt.
      by rewrite /Q2R /= Rmult_1_l -Rinv_pow; try lra.
    case: (Rabs0_dec x) => [/dns0_tpmn [n ineq] | ]; last by split_Rabs; lra.
    exists (Rinv x); split => [eps eg0 | ]; last by rewrite /= Rinv_r; split_Rabs; lra.
    have [m /=]:= val eps; rewrite /RQinv_M; case: ifP => [/QleP /Qle_Rle /= | _]; try lra.
    set tpmm := ((/(1+1))^Z.of_nat m)%Q.
    set del := (Qabs (phi tpmm) - tpmm)%Q.
    case: ifP => //= /QleP tmp.
    have ineq': tpmm < \|phi tpmm|.
    - by rewrite -Qabs_Rabs; apply/Rnot_le_lt => tmp'; apply/tmp/Rle_Qle.
    move: tmp => _ [<-].    
    set r := (phi(Qmin (del /(1 + 1)) (eps * (del * del) / (1 + 1))))%Q.
    have neq' : 0 <> r by admit.      
    rewrite Q2R_inv; last by move => /Qeq_eqR; lra.
    have ->: /x - /r = (r - x)/(x * r) by field; lra.
    rewrite Rabs_mult.
    apply/Rle_trans.
    - apply/Rmult_le_compat_r; try exact/Rabs_pos.
      rewrite Rabs_minus_sym; apply/phinx; rewrite /Qmin.
      have del_pos: 0 < del by rewrite /del Q2R_minus Qabs_Rabs; lra.
      case : Qlt_le_dec => _.
      - by rewrite Q2R_div //; apply/Rdiv_lt_0_compat; last by rewrite /Q2R /=; lra.
      rewrite Q2R_div //; apply/Rdiv_lt_0_compat; last by rewrite /Q2R/=; lra.
      by rewrite !Q2R_mult; apply/Rmult_lt_0_compat/Rmult_lt_0_compat.
    rewrite /Qmin; case: Qlt_le_dec => le; last first.
    apply/Rle_trans; first by apply/Rmult_le_compat_r; [apply/Rabs_pos | apply/Qle_Rle/le].
    
    
  Admitted.
  
  Lemma M_cont: RQinv_M \is_continuous_functional.
  Proof.
    move => phi.
    exists (fun neps =>
              let tpmn := Qpower (/(1 + 1)) (Z.of_nat neps.1) in
              let delta := (Qabs (phi tpmn) - tpmn)%Q in
              [:: tpmn; Qmin (delta/(1+1)) (neps.2 * delta^2/(1 + 1))]%Q).
    by rewrite /RQinv_M => eps psi [-> [->]].
  Qed.

  Lemma inv_cont: inversion \has_continuous_realizer.
  Proof.
    exists (\F_(FMop.use_first RQinv_M)); split; try exact/sfrst_cntf_cont/M_cont.
    exact/tight_slvs/FMop.sfrst_spec/inv_M_spec.
  Qed.
End inversion.
