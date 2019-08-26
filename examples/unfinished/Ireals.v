From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_rlzrs.
From metric Require Import reals.
Require Import all_cs_base classical_mach.
Require Import Reals Psatz FunctionalExtensionality ClassicalChoice.
From Interval Require Import Interval_specific_ops Interval_bigint_carrier Interval_stdz_carrier.
From Interval Require Import Interval_interval_float_full Interval_interval.
From Interval Require Import Interval_xreal.
Import BigN BigZ.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.
Import QArith.
Local Open Scope R_scope.

Module SFBI2 := SpecificFloat BigIntRadix2.
Module SF2 := SpecificFloat StdZRadix2.
Module I := FloatIntervalFull SFBI2.
Module IZ := FloatIntervalFull SF2.

Notation D:= SFBI2.type.
Notation Dz:= SF2.type.
Notation mant := BigIntRadix2.smantissa_type.
Notation xpnt := BigIntRadix2.exponent_type.
Notation ID := (Interval_interval_float.f_interval SFBI2.type).
Notation IDZ := (Interval_interval_float.f_interval SF2.type).

Notation "x '\contained_in' I" := (Interval_interval.contains (I.convert I) (Xreal x)) (at level 2).
Coercion I.convert: ID >-> Interval_interval.interval.
Notation D2R := I.T.toR.
Coercion I.T.toR: D >-> R.
Notation lower := I.lower.
Notation upper := I.upper.
Notation diam I := (I.upper I - I.lower I).
Notation bounded := I.bounded.
Notation I0 := (I.fromZ 0).

Lemma add_correct_R prec x y I J:
	x \contained_in I -> y \contained_in J -> (x + y) \contained_in (I.add prec I J).
Proof.
intros.
replace (Xreal (x + y)) with (Xadd (Xreal x) (Xreal y)) by trivial.
by apply I.add_correct.
Qed.

Lemma mul_correct_R prec x y I J:
	x \contained_in I -> y \contained_in J -> (x * y) \contained_in (I.mul prec I J).
Proof.
intros.
replace (Xreal (x * y)) with (Xmul (Xreal x) (Xreal y)) by trivial.
by apply I.mul_correct.
Qed.

Definition rep_R : (nat -> ID) ->> R:= make_mf (
  fun I x => (forall n,  x \contained_in (I n))
  /\
  forall n, exists N, forall k, (N <= k)%nat -> bounded (I k)
                                                /\
                                                diam (I k) <= /2 ^ n).

Lemma D2R_SFBI2toX m e: SFBI2.toX (Float m e) = Xreal (D2R (Float m e)).
Proof.
rewrite /D2R/proj_val/=/SFBI2.toX/=/Interval_definitions.FtoX/=.
by case: BigIntRadix2.mantissa_sign (Float m e) => //.
Qed.

Lemma D2R_Float (m e: bigZ):
  D2R (Float m e) = IZR [m]%bigZ * powerRZ 2 [e]%bigZ.
Proof.
rewrite /D2R /SFBI2.toX /SFBI2.toF/=.
case: (BigIntRadix2.mantissa_sign m) (BigIntRadix2.mantissa_sign_correct m);
  rewrite /BigIntRadix2.MtoZ /=.
	by move => ->; lra.
move => s p' [-> [p]].
rewrite /BigIntRadix2.EtoZ /BigIntRadix2.MtoP => -> {p'}.
move: [e]%bigZ => {e} [ | e | e ] /=;
  rewrite ?Z.pow_pos_fold ?mult_IZR ?pow_IZR ?positive_nat_Z;
  case: s => //;
  lra.
Qed.

Lemma powerRZ2_neg_pos n: powerRZ 2 (-Z.of_nat n) = /2^n.
Proof.
by rewrite powerRZ_neg; try lra; rewrite Interval_missing.pow_powerRZ powerRZ_inv.
Qed.

Lemma rep_R_sur: rep_R \is_cototal.
Proof.
move => x.
exists (fun n => I.bnd 
	(Float (BigZ.BigZ.of_Z (Int_part (x * (2 ^ n)))) (BigZ.BigZ.of_Z (-Z.of_nat n)))
	(Float (BigZ.BigZ.of_Z (up (x * (2 ^ n)))) (BigZ.BigZ.of_Z (-Z.of_nat n)))).
split => n/=.
	have bi:= base_Int_part (x * 2^n); have lt:= pow_lt 2 n; have arc:= archimed (x * 2 ^ n).
	rewrite !D2R_SFBI2toX;	split; rewrite D2R_Float !BigZ.spec_of_Z powerRZ2_neg_pos.
		by apply (Rmult_le_reg_r (2 ^ n)); try lra; rewrite Rmult_assoc Rinv_l; lra.
	by apply (Rmult_le_reg_r (2 ^ n)); try lra; rewrite Rmult_assoc Rinv_l; lra.
exists n.+1 => k ineq; split => //.
have bi:= base_Int_part (x * 2^k); have ltn1:= pow_lt 2 n.+1; have arc:= archimed (x * 2 ^ k).
have ltk:= pow_lt 2 k; have ltn2:= pow_lt 2 n; have eq: 2 ^ k * /2 ^k = 1 by rewrite Rinv_r; lra.
have /=exp: /2 ^ k <= /2 ^ n.+1.
	apply Rinv_le_contravar; try lra.
	by apply Rle_pow; try lra; apply /leP.
rewrite !D2R_Float !BigZ.spec_of_Z powerRZ2_neg_pos.
rewrite -Raux.Rmult_minus_distr_r.
rewrite -[/2 ^ n]Rmult_1_l -(Rinv_r 2); try lra.
rewrite Rmult_assoc -Rinv_mult_distr; try lra.
apply Rmult_le_compat; try lra.
by apply /Rlt_le/Rinv_0_lt_compat; lra.
Qed.

Lemma Float_to_R m e:
	D2R (Float (BigZ.of_Z m) (BigZ.of_Z e)) = IZR m * powerRZ 2 e.
Proof. by rewrite D2R_Float !BigZ.spec_of_Z. Qed.

Lemma nFnan eps: 0 < D2R eps -> ~ eps = Fnan.
Proof. by case: eps; first by rewrite /D2R/=; lra. Qed.

Lemma rep_R_sing: rep_R \is_singlevalued.
Proof.
move => In x x' [xeIn convIn] [x'eIn _].
apply cond_eq => e eg0.
have [n [_ ineq]]:= accf_tpmn eg0.
have [N prop]:= convIn n.
have ineq': (N <= N)%nat by trivial.
have [Ibnd dI]:= (prop N ineq').
move: xeIn (xeIn N) => _ xeIn.
move: x'eIn (x'eIn N) => _ x'eIn.
apply/ Rle_lt_trans; last by apply ineq.
case: (In N) Ibnd dI xeIn x'eIn => // l u/=.
case: u; first by case: l.
by case: l => // um ue lm le; rewrite !D2R_SFBI2toX; split_Rabs; lra.
Qed.

Lemma countable_comp Q Q': Q \is_countable -> (exists cnt : (Q -> Q'), cnt \is_surjective) -> Q' \is_countable .
Proof.
  move => [cnt [H1 H2]].
  case => cnt' p1.
  exists ((F2MF cnt') \o cnt).
  split; first by apply comp_sing; by [apply F2MF_sing | ].
  apply comp_cotot; by [| |].
Qed.

Definition join_t (n : nat) (t1 t2 : (BigN.dom_t n)) : ((BigN.dom_t n.+1)) := (BigN.succ_t n (WW t1 t2)).

Fixpoint generate_t (h n : nat) : (BigN.dom_t h) := match h with
                                      | 0%nat => (match (@unpickle (prod_countType nat_countType nat_countType) n) with
                                               | (Some (n1,n2)) => match n1 with
                                                                  | 0%nat => (phi_inv (Z.of_nat n2))                             
                                                                  | _ => (phi_inv ((-1)*(Z.of_nat n2))%Z)
                                                                  end
                                               | _ => (phi_inv 0)
                                               end)
                                      | h'.+1 => match (unpickle  n) with
                                                | (Some (n1,n2)%nat) => (@join_t h' (generate_t h' n1) (generate_t h' n2))
                                                | _ => (BigN.succ_t h' W0)
                                              end
                                      end.
Lemma generate_cnt : forall h, forall (t : BigN.dom_t h), exists n, (generate_t h n) = t.
Proof.
  elim => [t |  h' IH t //=].
  - set z := (phi t).
    have : (t = (phi_inv z)) by rewrite Cyclic31.phi_inv_phi.
    case z eqn:zp => tinv.
    +exists (pickle (0,0)%nat).
     by rewrite tinv.
    +exists (pickle (0%nat,(Z.abs_nat z))%nat); by rewrite //= pickleK Zabs2Nat.id_abs /Z.abs zp tinv.
    +exists (pickle (1%nat,(Z.abs_nat z))%nat); by rewrite //= pickleK Zabs2Nat.id_abs /Z.abs zp tinv.
  - destruct h'; [| destruct h'; [| destruct h'; [| destruct h'; [| destruct h'; [| destruct h']]]]].
    all: try by (case t => [| t0 t1]; [ exists 2%nat | case (IH t1) => n1 n1p; case (IH t0) => n0 n0p; exists (pickle (n0,n1)); rewrite /generate_t pickleK; rewrite <- n0p, <- n1p]).
  - have ts: forall m,(BigN.succ_t m.+2.+4 W0) = W0 by elim => [| m Ihm]; by [].
    elim t; first by exists 2%nat; apply ts.
    move : IH.
    elim h' => [IH t0 t1| h'' _ IH t0 t1]; case (IH t1) => n1 n1p; case (IH t0) => n0 n0p; exists (pickle (n0,n1)); rewrite pickleK; by rewrite <-n0p, <- n1p.
Qed.

Lemma generate_cnt2 : forall N : bigN, exists h n, (BigN.mk_t h (generate_t h n)) = N.
Proof.
  elim => t.
  - case (@generate_cnt 0 t) => n P; by exists 0%nat, n;rewrite P.
  - case (@generate_cnt 1 t) => n P; by exists 1%nat, n;rewrite P.
  - case (@generate_cnt 2 t) => n P; by exists 2%nat, n;rewrite P.
  - case (@generate_cnt 3 t) => n P; by exists 3%nat, n;rewrite P.
  - case (@generate_cnt 4 t) => n P; by exists 4%nat, n;rewrite P.
  - case (@generate_cnt 5 t) => n P; by exists 5%nat, n;rewrite P.
  - case (@generate_cnt 6 t) => n P; by exists 6%nat, n;rewrite P.
  -
    elim t => [w|h' IH' w].
    + case (@generate_cnt 7 w) => n P; by exists 7%nat, n;rewrite P.
    + case (@generate_cnt h'.+2.+4.+2 w) => n P;by exists h'.+2.+4.+2, n;rewrite P.
Qed.

Lemma BigInt_count : bigN \is_countable.
Proof.
   apply (countable_comp (prod_count nat_count nat_count)).
   exists (fun n => (BigN.mk_t n.1 (generate_t n.1 n.2))) => N. 
   case (generate_cnt2 N) => h.
   case => n P.
   by exists (h,n).
Qed.

Lemma BigZ_count : bigZ \is_countable.
Proof.
   apply (countable_comp (prod_count bool_count (prod_count nat_count nat_count))).
   exists (fun n => match n.1 with
              | true  => (BigZ.Pos (BigN.mk_t n.2.1 (generate_t n.2.1 n.2.2)))
              | false => (BigZ.Neg (BigN.mk_t n.2.1 (generate_t n.2.1 n.2.2)))
             end) => Z.
   case Z => N;case (generate_cnt2 N) => h; case => n P.
   - by (exists (true, (h,n)));rewrite P.
   - by (exists (false, (h,n)));rewrite P.
Qed.     

Lemma D_count : D \is_countable.
Proof.
  have [p [p1 p2]]:= ((prod_count (option_count BigZ_count) BigZ_count)).
  pose cnt (z : (option bigZ*bigZ)) :=  (match z.1 with
             | None => Fnan
             | (Some z') => (Float (z') ((z.2)))
            end) : D.
  exists ((F2MF cnt) \o p).
  - split; first by apply comp_sing; [apply F2MF_sing |].
    apply comp_cotot; try by [].
    rewrite <- F2MF_cotot.
    move => d.
    case d eqn:eq; first by exists (None,0%bigZ).
    by exists (Some s, e).
Qed.
  
Lemma ID_count: ID \is_countable.
Proof.
  have [p [p1 p2]]:= (option_count (prod_count D_count D_count)).
  
  set cnt := (F2MF (fun (z :(option (D*D))) => match z with
                                            | None => Interval_interval_float.Inan
                                            | (Some z') => (I.bnd z'.1 z'.2)
             end)).
  exists (cnt \o p).
  split; first by apply comp_sing; [apply F2MF_sing |] .
  apply comp_cotot; try by [].
  rewrite /cnt.
  rewrite <- F2MF_cotot.
  case => [| l u]; first by exists None.
  by exists (Some (l,u)).
Qed.

Definition Iall:= @Interval_interval_float.Ibnd D Fnan Fnan. 

Definition IR:= make_cs 0%nat Iall nat_count ID_count rep_R_sur rep_R_sing.

Definition nat2p n := SFBI2.PtoP (Pos.of_nat n).

Lemma SFBI2_add_correct: forall (mode: Interval_definitions.rounding_mode) (p: xpnt) (e e':xpnt) (m m':mant),
    D2R (SFBI2.add mode p (Float m e) (Float m' e')) = Interval_definitions.round SFBI2.radix mode (SFBI2.prec p) (D2R (Float m e) + (D2R (Float m' e'))).
Proof.
move => mode p e e' m m'.
have := SFBI2.add_correct mode p (Float m e) (Float m' e').
rewrite !D2R_SFBI2toX.
rewrite /Xadd/Interval_definitions.Xround/Xbind/SFBI2.toX.
rewrite /Interval_definitions.FtoX.
by case E: (SFBI2.toF (SFBI2.add mode p (Float m e) (Float m' e'))) => //; move =>  [<-]; rewrite /D2R/proj_val/SFBI2.toX/Interval_definitions.FtoX E.
Qed.



Lemma mantissa_digits_shl m d p : (BigIntRadix2.valid_mantissa m) -> (BigIntRadix2.EtoZ d) = (Z.pos p) -> ((BigIntRadix2.EtoZ (BigIntRadix2.mantissa_digits (BigIntRadix2.mantissa_shl m d))) = ((BigIntRadix2.EtoZ (BigIntRadix2.mantissa_digits m))+(Z.pos p))%Z).
Proof.
  move => H1 H2.
  have [c1 c2] := (BigIntRadix2.mantissa_shl_correct p m d H1 H2).
  rewrite !BigIntRadix2.mantissa_digits_correct; try by [].
  rewrite <- !Interval_generic_proof.digits_conversion.
  rewrite c1.
  rewrite Interval_generic_proof.shift_correct Z.pow_pos_fold Digits.Zdigits_mult_Zpower; by [].
Qed.

Definition decrease_exp' p (e e':xpnt) :=
  match BigIntRadix2.exponent_cmp e e' with
        | Eq | Lt => p
        | Gt =>  (BigIntRadix2.mantissa_shl p (BigIntRadix2.exponent_sub e e'))
  end.

Definition decrease_exp (m : mant) e e' := match (BigIntRadix2.mantissa_sign m) with
                                   | Interval_specific_sig.Mzero  => m
                                   | (Interval_specific_sig.Mnumber s p)  => (if s then BigZ.Neg else BigZ.Pos) (decrease_exp' p e e')
                       end.

Definition exponent_min e e' :=
  match BigIntRadix2.exponent_cmp e e' with
        | Eq | Lt => e
        | Gt => e'
  end.

Definition exponent_max e e' :=
  match BigIntRadix2.exponent_cmp e e' with
        | Lt => e'
        | _ => e
  end.
Lemma exponent_min_lt e e' : ((exponent_min e e') <= e)%bigZ /\ ((exponent_min e e') <= e')%bigZ.
Proof.
  rewrite /exponent_min.
  case cmp : (BigIntRadix2.exponent_cmp e e').
  - have := cmp.
    rewrite BigZ.compare_eq_iff => cmp'.
    by rewrite cmp' /BigZ.le;lia.
  - have := cmp.
    rewrite BigZ.compare_lt_iff => cmp'.
    apply BigZ.lt_le_incl in cmp'.
    split; by [apply BigZ.le_refl | ].
  have := cmp.
  rewrite BigZ.compare_gt_iff => cmp'.
  apply BigZ.lt_le_incl in cmp'.
  split; by [apply BigZ.le_refl | ].
Qed.

Lemma decrease_correct (m:mant) e e' : (D2R (Float (decrease_exp m e e') (exponent_min e e'))) = (D2R (Float m e)).
Proof.
  rewrite /decrease_exp /exponent_min.
    rewrite !D2R_Float.
  case ms: (m =? 0)%bigZ.
  - rewrite /BigIntRadix2.mantissa_sign.
    rewrite ms.
    suff : (m == 0)%bigZ.
    - move => H.
      rewrite /BigZ.eq in H.
      rewrite BigZ.spec_0 in H.
      by rewrite H;lra.
    by apply BigZ.eqb_eq. 
  rewrite /BigIntRadix2.mantissa_sign.
  rewrite ms.
  have P0 x: (IZR [decrease_exp' x e e']%bigN)*(powerRZ 2 [(exponent_min e e')]%bigZ) = (IZR [x]%bigN * (powerRZ 2 [e]%bigZ)).
  - rewrite /decrease_exp'/exponent_min.
    case cmp : (BigIntRadix2.exponent_cmp e e'); try by [].
    have := cmp.
    rewrite BigZ.compare_gt_iff => cmp'.
    have gt : (0 < e-e')%bigZ by apply BigZ.lt_0_sub.
    rewrite /BigZ.lt BigZ.spec_0 in gt.
    rewrite /BigIntRadix2.exponent_sub.
    rewrite /BigIntRadix2.mantissa_shl //=.
    rewrite BigN.spec_shiftl_pow2.
    move : gt.
    case e'': ([e-e']%bigZ) => [| p|]; try by auto.
    move => _.
    rewrite spec_to_Z_pos /Z.pow e''.
    rewrite !mult_IZR Zpower_pos_powerRZ.
    rewrite <- e''.
    rewrite BigZ.spec_sub powerRZ_add;last by [].
    rewrite !Rmult_assoc.
    rewrite <- powerRZ_add;last by [].
    rewrite Z.add_opp_diag_l //=.
    by lra.
    by [].
  case m => t; try by apply P0.
  - rewrite !opp_IZR; rewrite <- !Ropp_mult_distr_l; apply Ropp_eq_compat.
    by apply P0.
Qed.

Lemma decrease_exp_spec m e e' : [(decrease_exp m e e')]%bigZ = ([m]%bigZ * 2^[e-(exponent_min e e')]%bigZ)%Z.
Proof.
  rewrite /decrease_exp /exponent_min/BigIntRadix2.mantissa_sign.
  case ms: (m =? 0)%bigZ.
  - suff : (m == 0)%bigZ.
    - move => H.
      rewrite /BigZ.eq in H.
      rewrite BigZ.spec_0 in H.
      by rewrite H //=;lra.
    by apply BigZ.eqb_eq. 
  have P0 x: ([decrease_exp' x e e']%bigN = ([x]%bigN * 2^[e-(exponent_min e e')]%bigZ))%Z.
  - rewrite /decrease_exp'/exponent_min BigZ.spec_sub/BigIntRadix2.exponent_sub.
    rewrite /Z.pow.
    case cmp : (BigIntRadix2.exponent_cmp e e'); try by rewrite Z.sub_diag;lia.
    have := cmp.
    rewrite BigZ.compare_gt_iff => cmp'.
    have gt : (0 < e-e')%bigZ by apply BigZ.lt_0_sub.
    rewrite /BigZ.lt BigZ.spec_0 in gt.
    have := gt.
    case e'': ([e-e']%bigZ) => [| p|]; try by auto.
    rewrite BigZ.spec_sub in e''.
    rewrite e''.
    move => _.
    rewrite /BigIntRadix2.mantissa_shl.
    case m => t //=; rewrite BigN.spec_shiftl_pow2; try rewrite !opp_IZR; (rewrite  spec_to_Z_pos;last by apply Z.lt_le_incl);rewrite BigZ.spec_sub.
    - by rewrite e''.
    by rewrite e'' Z.pow_pos_fold;lia.
  case m => t; try by apply P0.
    - rewrite /BigZ.to_Z.
      rewrite <- !Zopp_mult_distr_l.
      Search _ (- _ = - _)%Z.
      apply Z.opp_inj_wd.
      by apply P0.
Qed.


Lemma exponent_min_sym e e' : [(exponent_min e e')]%bigZ = [(exponent_min e' e)]%bigZ.
Proof.
  rewrite /exponent_min.
  case cmp : (BigIntRadix2.exponent_cmp e e').
  - have := cmp;rewrite BigZ.compare_eq_iff => cmp0.
    have cmp' : (BigIntRadix2.exponent_cmp e' e) = Eq by  rewrite BigZ.compare_eq_iff.
    by rewrite cmp'.
  - have := cmp;rewrite BigZ.compare_lt_iff => cmp0.
    have cmp' : (BigIntRadix2.exponent_cmp e' e) = Gt by  rewrite BigZ.compare_gt_iff.
    by rewrite cmp'.
  have := cmp;rewrite BigZ.compare_gt_iff => cmp0.
  have cmp' : (BigIntRadix2.exponent_cmp e' e) = Lt by  rewrite BigZ.compare_lt_iff.
  by rewrite cmp'.
Qed.

Lemma exponent_max_sym e e' : [(exponent_max e e')]%bigZ = [(exponent_max e' e)]%bigZ.
Proof.
  rewrite /exponent_max.
  case cmp : (BigIntRadix2.exponent_cmp e e').
  - have := cmp;rewrite BigZ.compare_eq_iff => cmp0.
    have cmp' : (BigIntRadix2.exponent_cmp e' e) = Eq by  rewrite BigZ.compare_eq_iff.
    by rewrite cmp'.
  - have := cmp;rewrite BigZ.compare_lt_iff => cmp0.
    have cmp' : (BigIntRadix2.exponent_cmp e' e) = Gt by  rewrite BigZ.compare_gt_iff.
    by rewrite cmp'.
  have := cmp;rewrite BigZ.compare_gt_iff => cmp0.
  have cmp' : (BigIntRadix2.exponent_cmp e' e) = Lt by  rewrite BigZ.compare_lt_iff.
  by rewrite cmp'.
Qed.

Lemma add_float m e m' e' : (D2R (Float m e)+(D2R (Float m' e'))) = (D2R (Float ((decrease_exp m e e')+(decrease_exp m' e' e))%bigZ (exponent_min e e'))).
Proof.
  rewrite !D2R_Float !BigZ.spec_add !decrease_exp_spec !plus_IZR !mult_IZR.
  have pos e1 e2 :  (0 <= [e1-(exponent_min e1 e2)]%bigZ)%Z.
  - rewrite BigZ.spec_sub.
    suff : ([exponent_min e1 e2]%bigZ <= [e1]%bigZ)%Z by lia.
    by apply (exponent_min_lt e1 e2).
  rewrite !(Raux.IZR_Zpower SFBI2.radix _ (pos e e')).
  rewrite !(Raux.IZR_Zpower SFBI2.radix _ (pos e' e)).
  rewrite !(Raux.bpow_powerRZ SFBI2.radix) //=.
  rewrite Rmult_plus_distr_r !BigZ.spec_sub.
  rewrite !Rmult_assoc.
  rewrite <- !powerRZ_add;try by lra.
  rewrite (exponent_min_sym e' e).
  by rewrite !Z.sub_add.
Qed.

Lemma round_IZR : forall (mode: Interval_definitions.rounding_mode) n, (Interval_definitions.rnd_of_mode mode (IZR n)) = n.
Proof.
  move => mode n.
  elim mode;simpl.
  -  apply Raux.Zceil_IZR.
  - apply Raux.Zfloor_IZR.
  - apply Raux.Ztrunc_IZR.
  case (Generic_fmt.Znearest_DN_or_UP (fun x => ~~ Z.even x) (IZR n)) => H; rewrite H.
  - apply Raux.Zfloor_IZR.
  apply Raux.Zceil_IZR.
Qed.

Lemma mantissa_digits_gt1 m : (BigIntRadix2.valid_mantissa m) -> (1 <= (BigIntRadix2.mantissa_digits m))%bigZ.
Proof.
  move => H.
  have crc := (BigIntRadix2.mantissa_digits_correct m H).
  rewrite /BigIntRadix2.EtoZ in crc.
  rewrite /BigZ.le crc.
  suff t : (0 < (Z.pos (Interval_definitions.count_digits BigIntRadix2.radix (BigIntRadix2.MtoP m))))%Z.
  - have eq1 : ([1]%bigZ = 1)%Z by [].
    by rewrite eq1; lia.
  by apply Pos2Z.is_pos.
Qed.


Lemma generic_format_mantissa_length : forall (e:xpnt) (m:bigZ) p, (BigIntRadix2.valid_mantissa (BigZ.to_N m)) -> ((BigIntRadix2.mantissa_digits (BigZ.to_N m)) <= p)%bigZ -> (Generic_fmt.generic_format SFBI2.radix (FLX.FLX_exp (Z.pos (SFBI2.prec p))) (IZR [m]%bigZ * powerRZ 2 [e]%bigZ)).
Proof. 
  move => e m p V1 V2.
  have P1 : (1 <= p)%bigZ.
  - have := (mantissa_digits_gt1 V1).
    rewrite /BigZ.le => gt.
    by apply (Zle_trans _ _ _ gt).
  have helper1 z: (1 <= [z]%bigZ)%Z -> (Z.pos (SFBI2.prec z))=[z]%bigZ.
  - rewrite /SFBI2.prec/BigIntRadix2.EtoZ.
    case M : [z]%bigZ => [|z'|z']; try by lia; try by rewrite /BigZ.lt M //=.
  apply FLX.generic_format_FLX.
  apply (FLX.FLX_spec SFBI2.radix (Z.pos (SFBI2.prec p)) (IZR [m]%bigZ * powerRZ 2 [e]%bigZ) (Defs.Float SFBI2.radix [m]%bigZ [e]%bigZ)); first by rewrite /Defs.F2R Raux.bpow_powerRZ //=.
    simpl.
    suff H: ((Z.abs [m]%bigZ) < Z.pow_pos 2 (SFBI2.prec (BigIntRadix2.mantissa_digits (BigZ.to_N m))))%Z.
    + apply /Zlt_le_trans.
      apply H.
      apply le_IZR.
      rewrite !Zpower_pos_powerRZ.
      rewrite !powerRZ_Rpower; try by lra.
      apply Rle_Rpower; try by lra.
      rewrite helper1; last by apply mantissa_digits_gt1.
      rewrite helper1; last by apply P1.
      by apply IZR_le.
    rewrite /SFBI2.prec BigIntRadix2.mantissa_digits_correct; last by apply V1.
    rewrite Z.pow_pos_fold.
    rewrite <- Interval_generic_proof.digits_conversion.
    have P : (Z.pos (BigIntRadix2.MtoP (BigZ.to_N m))) = (Z.abs [m]%bigZ).
    + case V1 => m' m'p.
      rewrite spec_to_N.
      rewrite /BigIntRadix2.MtoP m'p Z.abs_mul //=.
      suff zabs_sgn : ((Z.abs (Z.sgn [m]%bigZ)) = 1)%Z by rewrite zabs_sgn;lia.
      suff : ([m]%bigZ <> 0)%Z by lia.
      suff: ([m]%bigZ = 0)%Z -> False by [].
      move => m0; move : m'p.
      by rewrite spec_to_Z m0 //=.
    rewrite P Digits.Zdigits_abs.
    have [_ D] := (Digits.Zdigits_correct BigIntRadix2.radix [m]%bigZ).
    rewrite /BigIntRadix2.MtoP.
    move : D.
    by case M: [m]%bigZ => [| | p']; try by auto.
Qed.

Lemma round_no_error : forall (mode: Interval_definitions.rounding_mode) (e:xpnt) (m:bigZ) p, (BigIntRadix2.valid_mantissa (BigZ.to_N m)) -> ((BigIntRadix2.mantissa_digits (BigZ.to_N m)) <= p)%bigZ -> Interval_definitions.round SFBI2.radix mode (SFBI2.prec p) (D2R (Float m e)) = (D2R (Float m e)).
Proof. 
  move => mode e m p V1 V2.
  rewrite /Interval_definitions.round/Generic_fmt.round.
  rewrite /Defs.F2R//=.
  rewrite D2R_Float.
  have helper: (Generic_fmt.generic_format SFBI2.radix
    (FLX.FLX_exp (Z.pos (SFBI2.prec p)))
    (IZR [m]%bigZ * powerRZ 2 [e]%bigZ)) by apply generic_format_mantissa_length.
  rewrite Generic_fmt.scaled_mantissa_generic; by [rewrite round_IZR//= | apply helper].
Qed.


Definition mantissa_digits (m : mant) := match (BigIntRadix2.mantissa_sign m) with
                                   | Interval_specific_sig.Mzero  => 0%bigZ
                                   | (Interval_specific_sig.Mnumber s p)  => (BigIntRadix2.mantissa_digits p)
                                end.

Definition valid_mantissa (m : mant) := match m with
                                  | (BigZ.Pos t) => BigIntRadix2.valid_mantissa t
                                  | (BigZ.Neg t) => BigIntRadix2.valid_mantissa t
                                end.

Definition Dmantissa_digits (d :D) := match d with
                                   | Fnan => 0%bigZ 
                                   | (Float m e) => (mantissa_digits m)
                                end.

Lemma ms_decrease_exp m e e' : (BigIntRadix2.mantissa_sign (decrease_exp m e e')) = Interval_specific_sig.Mzero <-> (BigIntRadix2.mantissa_sign m) = Interval_specific_sig.Mzero.
Proof.
  split => H; last by rewrite /decrease_exp H.
  move : H.
  rewrite /BigIntRadix2.mantissa_sign.
  case mz : (decrease_exp m e e' =? 0)%bigZ.
  - suff m0 : (m == 0)%bigZ by rewrite <- BigZ.eqb_eq in m0;rewrite m0.
    move : mz.
    rewrite BigZ.eqb_eq /BigZ.eq decrease_exp_spec.
    rewrite BigZ.spec_0.
    apply Zmult_integral_l.
    apply Z.pow_nonzero; try by lia.
    suff H : (exponent_min e e' <= e)%bigZ.
      -by rewrite BigZ.spec_sub; rewrite /BigZ.le in H; lia.
    by apply exponent_min_lt.
  case (decrease_exp m e e') => t; try by [].
Qed.
Lemma ms_decrease_exp' m e e' : ((decrease_exp m e e') =? 0)%bigZ = (m =? 0)%bigZ.
Proof.
  case mz : (decrease_exp m e e' =? 0)%bigZ.
  - suff m0 : (m == 0)%bigZ by rewrite <- BigZ.eqb_eq in m0;rewrite m0.
    move : mz.
    rewrite BigZ.eqb_eq /BigZ.eq decrease_exp_spec.
    rewrite BigZ.spec_0.
    apply Zmult_integral_l.
    apply Z.pow_nonzero; try by lia.
    suff H : (exponent_min e e' <= e)%bigZ.
      -by rewrite BigZ.spec_sub; rewrite /BigZ.le in H; lia.
    by apply exponent_min_lt.
    move : mz; rewrite /decrease_exp/BigIntRadix2.mantissa_sign.
    case mz0 : (m =? 0)%bigZ; try by rewrite mz0.
    - case m => t; by [].
Qed.
Lemma valid_mantissa_bigN t: ([t]%bigN <> 0)%Z -> (BigIntRadix2.valid_mantissa t).
  - move => tp.
    case t0: [t]%bigN => [| p |p]; first by [].
      * by exists p.
      have  := (BigN.spec_pos t).
      by rewrite t0.
Qed.

Lemma decrease_exp_mantissa_digits_lt m e e' : (e' < e)%bigZ -> ((BigIntRadix2.EtoZ (mantissa_digits (decrease_exp m e e'))) <= (BigIntRadix2.EtoZ ((Dmantissa_digits (Float m e))+(e-e'))%bigZ))%Z.
Proof.
  move => H //=.
  case mz: (m =? 0)%bigZ.
  - rewrite /mantissa_digits/BigIntRadix2.mantissa_sign.
    rewrite ms_decrease_exp' mz.
    rewrite /BigIntRadix2.EtoZ BigZ.spec_add BigZ.spec_0 //= BigZ.spec_sub.
      by rewrite /BigZ.lt in H;lia.
  apply Zeq_le.
  rewrite /mantissa_digits/decrease_exp/BigIntRadix2.mantissa_sign.
  rewrite ms_decrease_exp' mz.
  move : mz.
 have pos: (BigIntRadix2.EtoZ (BigIntRadix2.exponent_sub e e')) = (Z.pos (Z.to_pos (BigIntRadix2.EtoZ (BigIntRadix2.exponent_sub e e')))).
  - rewrite Z2Pos.id; first by [].
    rewrite /BigIntRadix2.EtoZ /BigIntRadix2.exponent_sub BigZ.spec_sub.
    by rewrite /BigZ.lt in H;lia.
  have cmp : (BigIntRadix2.exponent_cmp e e') = Gt by rewrite BigZ.compare_gt_iff.
  case m => t mz; move : mz;rewrite BigZ.eqb_neq /BigZ.eq /BigZ.to_Z BigN.spec_0 => mz.
  - rewrite /decrease_exp' /mantissa_digits.
    rewrite cmp.
    have vm := (valid_mantissa_bigN  mz).
    rewrite (mantissa_digits_shl vm pos).
    rewrite Z2Pos.id;last by suff : ([e']%bigZ < [e]%bigZ)%Z by lia. 
    rewrite /BigIntRadix2.exponent_sub.
    rewrite !/BigIntRadix2.EtoZ.
    by rewrite BigZ.spec_add.
  rewrite /decrease_exp' /mantissa_digits cmp.
  have mz' : ([t]%bigN <> 0)%Z by lia.
  have vm := (valid_mantissa_bigN mz').
  rewrite (mantissa_digits_shl vm pos).
  rewrite Z2Pos.id;last by suff : ([e']%bigZ < [e]%bigZ)%Z by lia. 
  rewrite /BigIntRadix2.exponent_sub.
  rewrite !/BigIntRadix2.EtoZ.
  by rewrite BigZ.spec_add.
Qed.


Definition Dexp (d :D) := match d with
                                   | Fnan => 0%bigZ 
                                   | (Float m e) => e
                                end.

Definition Imantissa_digits (I : ID) := match I with
                                | Interval_interval_float.Inan => 0%bigZ
                                | (Interval_interval_float.Ibnd l r) => (BigZ.max (Dmantissa_digits l) (Dmantissa_digits r))
                                end.

Definition Iexp_max (I : ID) := match I with
                                | Interval_interval_float.Inan => 0%bigZ
                                | (Interval_interval_float.Ibnd l r) => (BigZ.max (Dexp l) (Dexp r))
                                end.

Lemma add_mantissa_digits_helper m1 m2: (BigIntRadix2.valid_mantissa m1) -> (BigIntRadix2.valid_mantissa m2) -> ((BigIntRadix2.EtoZ (BigIntRadix2.mantissa_digits (m1+m2)%bigN)) <= (Z.max (BigIntRadix2.EtoZ (BigIntRadix2.mantissa_digits m1)) (BigIntRadix2.EtoZ (BigIntRadix2.mantissa_digits m2)))+1)%Z. 
Proof.
  Compute (BigIntRadix2.EtoZ (BigIntRadix2.mantissa_digits 0%bigN)).
  move => H1 H2.
  have [H3 V] := (BigIntRadix2.mantissa_add_correct m1 m2 H1 H2).
  rewrite /BigIntRadix2.mantissa_add in H3,V.
  rewrite !BigIntRadix2.mantissa_digits_correct; try by [].
  rewrite H3.
  rewrite <- !Interval_generic_proof.digits_conversion.
  suff Zdigits_add p1 p2 : ((Digits.Zdigits BigIntRadix2.radix (p1+p2)%Z) <= (Z.max (Digits.Zdigits BigIntRadix2.radix p1) (Digits.Zdigits BigIntRadix2.radix p2))+1)%Z by rewrite Pos2Z.inj_add.
  rewrite <- Digits.Zdigits_abs.
  rewrite <- (Digits.Zdigits_abs _ p1).
  rewrite <- (Digits.Zdigits_abs _ p2).
  have lt : ((Z.abs (p1+p2))%Z <= 2*(Z.max (Z.abs p1) (Z.abs p2)))%Z.
  - apply /Zle_trans.
    apply Z.abs_triangle.
    rewrite <- Z.add_diag.
    by apply Z.add_le_mono; by [apply Z.le_max_l |apply Z.le_max_r].
  apply /Zle_trans.
  apply Digits.Zdigits_le; first by apply Z.abs_nonneg.
  apply lt.
  have Zdigits_mult_lt p : ((Digits.Zdigits BigIntRadix2.radix (2*p)) <= (Digits.Zdigits BigIntRadix2.radix p)+1)%Z.
  - rewrite <- Digits.Zdigits_abs.
    rewrite <- (Digits.Zdigits_abs _ p).
    have t : ((Z.abs (2*p)) = (Z.abs p)*2)%Z by lia.
    rewrite t.
    by case p => [| p' | p']; try by [];apply Zeq_le; rewrite (Digits.Zdigits_mult_Zpower BigIntRadix2.radix _ 1); try by lia.
  apply /Zle_trans.
  apply Zdigits_mult_lt.
  suff: (Digits.Zdigits BigIntRadix2.radix (Z.max (Z.abs p1) (Z.abs p2)) <=  Z.max (Digits.Zdigits BigIntRadix2.radix (Z.abs p1)) (Digits.Zdigits BigIntRadix2.radix (Z.abs p2)))%Z by lia.
 have P0 u v : ((Z.abs u) <= (Z.abs v))%Z -> ((Z.max (Digits.Zdigits BigIntRadix2.radix (Z.abs u))
     (Digits.Zdigits BigIntRadix2.radix (Z.abs v))) = (Digits.Zdigits BigIntRadix2.radix (Z.abs v))).
 - move => H.
   rewrite Z.max_r; first by [].
    by apply Digits.Zdigits_le; [lia |].
  case e: ((Z.abs p1) <=? (Z.abs p2))%Z.
  - apply Z.leb_le in e.
    rewrite Z.max_r; last by [].
    rewrite P0; last by [].
    by lia.
  apply Z.leb_gt in e.
  apply Z.lt_le_incl in e.
  rewrite Z.max_l; last by [].
  rewrite Z.max_comm.
  rewrite P0; last by [].
  by lia.
Qed.


Lemma mantissa_digits_pos m : (0 <= (mantissa_digits m))%bigZ.
Proof.
  rewrite /mantissa_digits/BigIntRadix2.mantissa_sign.
  case (m =? 0)%bigZ; first by [].
  case m => t; by rewrite /BigIntRadix2.mantissa_digits /BigZ.le BigZ.spec_0 /BigZ.to_Z;apply BigN.spec_pos.
Qed.

Lemma mantissa_digits_val m m' : (m == m')%bigZ -> (mantissa_digits m == mantissa_digits m')%bigZ.
Proof.
  move => H.
  rewrite /BigZ.eq in H.
  rewrite /mantissa_digits/BigIntRadix2.mantissa_sign.
  rewrite !BigZ.spec_eqb.
  case e : ([m]%bigZ =? [0]%bigZ)%Z.
  - move : e.
    rewrite Z.eqb_eq => e.
    rewrite e in H.
    symmetry in H.
    by rewrite H BigZ.spec_0.
  rewrite <- H.
  rewrite e.
  move : H e.
  rewrite /BigZ.to_Z.
  have crc := BigIntRadix2.mantissa_digits_correct.
  rewrite /BigIntRadix2.EtoZ in crc.
  case m => t;case m' => t' H;rewrite BigN.spec_0;rewrite Z.eqb_neq => e; rewrite /BigZ.eq.
  - rewrite !crc; try by apply valid_mantissa_bigN; try rewrite <- H.
    by rewrite /BigIntRadix2.MtoP H.
  - have lt := (BigN.spec_pos t').
    have lt' := (BigN.spec_pos t).
    have tp : ((- [t']%bigN) < 0)%Z by lia.
    by rewrite H in lt';lia.   
  - have lt := (BigN.spec_pos t').
    have lt' := (BigN.spec_pos t).
    have tp : ((- [t]%bigN) < 0)%Z by lia.
    by rewrite <- H in lt;lia.   
    have H' : ([t]%bigN = [t']%bigN)%Z by lia.
    have e' : ([t]%bigN <> 0)%Z by lia.
    rewrite !crc; try by apply valid_mantissa_bigN; try rewrite <- H'.
    by rewrite /BigIntRadix2.MtoP H'.
Qed.

Lemma mantissa_digits_inv m : ((mantissa_digits m) == (mantissa_digits (-m)%bigZ))%bigZ.
Proof.
  rewrite /mantissa_digits/ BigIntRadix2.mantissa_sign.
  case e : ([m]%bigZ =? 0)%Z;rewrite !BigZ.spec_eqb !BigZ.spec_opp.
  - have e' : ((-[m]%bigZ =? 0)%Z = true) by move:e; rewrite !Z.eqb_eq;lia.
    by rewrite e e'.
  have e' : ((-[m]%bigZ =? 0)%Z = false) by move:e; rewrite !Z.eqb_neq;lia.
  rewrite e e'.
  by case m => p //=.
Qed.

Lemma mantissa_digits_lt m1 m2 : (BigIntRadix2.valid_mantissa m1) -> (BigIntRadix2.valid_mantissa m2) -> (m1 <= m2)%bigN -> ((BigIntRadix2.mantissa_digits m1) <= (BigIntRadix2.mantissa_digits m2))%bigZ.
Proof.
  move => H1 H2 le.
  have c := BigIntRadix2.mantissa_digits_correct.
  rewrite /BigIntRadix2.EtoZ in c.
  rewrite /BigZ.le !c; try by [].
  rewrite <- !Interval_generic_proof.digits_conversion.
  apply Digits.Zdigits_le; try by [].
  rewrite /BigN.le in le.
  move : le.
  rewrite /BigIntRadix2.MtoP.
  case [m1]%bigN => [| p | p]; case [m2]%bigN => p'; try by lia.
Qed.


Lemma mantissa_digits_abs m : ((mantissa_digits m) == (mantissa_digits (BigZ.abs m)))%bigZ.
Proof.
  case (BigZ.abs_eq_or_opp m) => H; by [apply mantissa_digits_val| rewrite (mantissa_digits_inv m); apply mantissa_digits_val].
Qed.

Lemma add_mantissa_digits1 m1 m2 : (m1 != 0)%bigZ -> (m2 != 0)%bigZ -> ([(mantissa_digits (m1+m2))]%bigZ <= (Z.max [(mantissa_digits m1)]%bigZ [(mantissa_digits m2)]%bigZ)+1)%Z.
Proof.
  move => H1 H2.
  have [H1' H2'] : (m1 =? 0)%bigZ=false /\ (m2 =? 0)%bigZ=false by split;apply BigZ.eqb_neq.
  case H3' : ((m1+m2)%bigZ =? 0)%bigZ.
  - rewrite [mantissa_digits (m1+m2)%bigZ]/mantissa_digits /BigIntRadix2.mantissa_sign H3' BigZ.spec_0.
    apply /Zle_trans.
    apply (@mantissa_digits_pos m1).
    apply /Zle_trans.
    apply (Z.le_max_l [mantissa_digits m1]%bigZ [mantissa_digits m2]%bigZ).
    by lia.
   have abs0 m : ((m =? 0)%bigZ = false) -> ((BigZ.abs m =? 0)%bigZ = false) by rewrite !BigZ.eqb_neq /BigZ.eq BigZ.spec_abs BigZ.spec_0;lia.
   apply abs0 in H1'.
   apply abs0 in H2'.
   have := H3'.
   rewrite BigZ.eqb_neq /BigZ.eq BigZ.spec_0 => H4'.
   apply abs0 in H3'.
   suff : ([mantissa_digits (BigZ.abs (m1+m2))]%bigZ <= (Z.max [(mantissa_digits (BigZ.abs m1))]%bigZ [(mantissa_digits (BigZ.abs m2))]%bigZ)+1)%Z by rewrite <- !mantissa_digits_abs.
  rewrite /mantissa_digits/BigIntRadix2.mantissa_sign H1' H2' H3' /BigZ.abs.
  have neqneq x: ([x]%bigZ <> 0)%Z -> ([BigZ.to_N x]%bigN <> 0)%Z by case x => p; try rewrite /BigZ.to_Z/BigZ.to_N;lia.
  have [V1 [V2 V3]] : (BigIntRadix2.valid_mantissa (BigZ.to_N m1)) /\ (BigIntRadix2.valid_mantissa (BigZ.to_N m2)) /\ (BigIntRadix2.valid_mantissa (BigZ.to_N (m1+m2))) by split; [|split]; by apply valid_mantissa_bigN; apply neqneq.
  have V4 : (BigIntRadix2.valid_mantissa ((BigZ.to_N m1) + (BigZ.to_N m2))).
  - apply valid_mantissa_bigN.
    rewrite BigN.spec_add.
    have lt0 m: (m != 0)%bigZ -> (0 < [BigZ.to_N m]%bigN)%Z.
     + have lt1 := (BigN.spec_pos (BigZ.to_N m)).
       move => H0.
       suff : ([BigZ.to_N m]%bigN <> 0)%Z by lia.
       by apply neqneq.
    have lt0' := (lt0 m1 H1).
    have lt0'' := (lt0 m2 H2).
    by lia.
  apply /Zle_trans.
  apply (@mantissa_digits_lt _ ((BigZ.to_N (m1))+(BigZ.to_N m2))); try by [].
  - suff : (BigZ.abs (m1+m2) <= (BigZ.abs m1)+(BigZ.abs m2))%bigZ by rewrite /BigZ.abs/BigZ.le/BigZ.to_Z //=.
    by apply BigZ.abs_triangle.
  apply add_mantissa_digits_helper; try by [].
Qed.  

Lemma add_mantissa_digits0 m1 m2 : (m2 == 0)%bigZ -> ((mantissa_digits (m1+m2)) == (mantissa_digits m1))%bigZ.
Proof.
  move => H.
  suff : (m1+m2 == m1)%bigZ by apply mantissa_digits_val.
  rewrite H.
  by apply BigZ.add_0_r.
Qed.


Lemma add_mantissa_digits2 m1 m2 : ([(mantissa_digits (m1+m2))]%bigZ <= (Z.max [(mantissa_digits m1)]%bigZ [(mantissa_digits m2)]%bigZ)+1)%Z.
Proof.
  have add_mant_digits_sym m m' : ((mantissa_digits (m+m')) == (mantissa_digits (m'+m)))%bigZ.
  - suff : (m+m' == m'+m)%bigZ by apply mantissa_digits_val.
    by rewrite /BigZ.eq !BigZ.spec_add;lia.
  case m1eq0 : (m1 =? 0)%bigZ; first by rewrite add_mant_digits_sym add_mantissa_digits0; [lia|  move :m1eq0; rewrite BigZ.eqb_eq].
  case m2eq0 : (m2 =? 0)%bigZ; first by rewrite add_mantissa_digits0; [lia|  move :m2eq0; rewrite BigZ.eqb_eq].
  by apply add_mantissa_digits1; rewrite <- BigZ.eqb_neq.
Qed.

Lemma mantissa_digits_ub m : (Rabs (IZR [m]%bigZ)) <= (powerRZ 2 [mantissa_digits m]%bigZ).
Proof.
  rewrite /mantissa_digits/BigIntRadix2.mantissa_sign.
  case e : (m =? 0)%bigZ.
  - rewrite BigZ.spec_0 /powerRZ.
    move : e.
    rewrite BigZ.eqb_eq/BigZ.eq BigZ.spec_0 => e.
    by rewrite e Rabs_R0 //=;lra.
  have helper : exists p, ([p]%bigN <> 0)%Z /\ (m = (BigZ.Pos p) \/ (m = (BigZ.Neg p))).
    - move : e.
      case m => p;rewrite BigZ.eqb_neq /BigZ.eq BigZ.spec_0 /BigZ.to_Z; exists p; split; try by lia.
      + by apply or_introl.
      + by apply or_intror.
  have posMtoP p : ([p]%bigN <> 0)%Z -> [BigZ.Pos p]%bigZ = (Z.pos (BigIntRadix2.MtoP p)).
  - move => pneg0.
    rewrite /BigIntRadix2.MtoP //=.
    case p' : [p]%bigN => [| a | a]; try by []; try by have ps := (BigN.spec_pos p);lia.
  have c:= BigIntRadix2.mantissa_digits_correct; rewrite /BigIntRadix2.EtoZ in c.
  rewrite Rabs_Zabs.
  have bign_prop p : ([p]%bigN <> 0)%Z -> (IZR (Z.abs [BigZ.Pos p]%bigZ) <= powerRZ 2 [BigIntRadix2.mantissa_digits p]%bigZ).
  - move => pneg0.
    rewrite c;try rewrite <- Interval_generic_proof.digits_conversion; try apply valid_mantissa_bigN; try by [].
    have [_ crc] := (Digits.Zdigits_correct BigIntRadix2.radix [BigZ.Pos p]%bigZ).
    apply IZR_lt in crc.
    apply /Rlt_le.
    apply /Rlt_le_trans.
    apply crc.
    rewrite Raux.IZR_Zpower; last by apply Digits.Zdigits_ge_0.
    have r : (Zaux.radix_val BigIntRadix2.radix) = 2%Z by [].
    rewrite <- r.
    rewrite <- Raux.bpow_powerRZ.
    rewrite posMtoP; last by [].
    by lra.
  case helper => p [p_pos pm]; move : pm; case => pm; rewrite pm.
  - apply bign_prop; last by [].
    have zabs_neg : (Z.abs [BigZ.Neg p]%bigZ) = (Z.abs [BigZ.Pos p]%bigZ) by rewrite /BigZ.to_Z; lia.
    rewrite zabs_neg.
    by apply bign_prop.
Qed.

Lemma bigZ_abs_pos z: (z != 0)%bigZ -> exists p, [(BigZ.abs z)]%bigZ = (Z.pos p).
Proof.
  have rw n: ([n]%bigN <> 0)%Z -> exists p, ([n]%bigN = (Z.pos p)).
  - have  := (BigN.spec_pos n).
    case e: [n]%bigN => [| p | p]; try by lia.
    by exists p.
  case z => n; by rewrite /BigZ.eq /BigZ.to_Z BigN.spec_0 => H;  apply rw;rewrite /BigZ.to_N;lia.
Qed.

Lemma round_error : forall (mode: Interval_definitions.rounding_mode) (e:xpnt) (m:mant) p, (1 < p <= (mantissa_digits m))%bigZ -> (Rabs ((Interval_definitions.round SFBI2.radix mode (SFBI2.prec p) (D2R (Float m e))) - (D2R (Float m e)))) <= (powerRZ 2 ([mantissa_digits m]%bigZ+[e]%bigZ+1-[p]%bigZ)).
Proof.
  move => mode e m p [P1 P2].
  rewrite /Interval_definitions.round.
  apply /Rle_trans.
  apply Ulp.error_le_ulp; by [apply FLX.FLX_exp_valid; [] | apply Interval_definitions.valid_rnd_of_mode].
  apply /Rle_trans.
  apply FLX.ulp_FLX_le; by [].
  rewrite D2R_Float Raux.bpow_powerRZ Rabs_mult //=.
  rewrite (Rabs_right (powerRZ _ _)); last by apply Rle_ge; apply powerRZ_le;lra.
  rewrite Rmult_assoc.
  rewrite <- powerRZ_add; last by lra.
  have helper1 : (Z.pos (SFBI2.prec p))=[p]%bigZ.
  - rewrite /SFBI2.prec/BigIntRadix2.EtoZ.
    move : P1.
    case M : [p]%bigZ => [|p'|p']; try by rewrite /BigZ.lt M //=.
  have helper2 : (1 < (Z.pos (SFBI2.prec p)))%Z by rewrite helper1.
  have R : ((Z.pos_sub 1 (SFBI2.prec p)) = 1-[p]%bigZ)%Z.
  - rewrite <- Z.pos_sub_opp.
    rewrite Z.pos_sub_gt; last by apply helper2.
    rewrite Pos2Z.inj_sub; last by apply helper2.
    by rewrite helper1;lia.
  rewrite R.
  suff pwr : (Rabs (IZR [m]%bigZ)) <= (powerRZ 2 [mantissa_digits m]%bigZ).
  - apply /Rle_trans.
    have rm := (Rmult_le_compat_r (powerRZ 2 ([e]%bigZ + (1 - [p]%bigZ))) _ _ _ pwr).
    apply rm; first by apply powerRZ_le; lra.
    rewrite <- powerRZ_add; last by lra.
    apply Req_le.
    by rewrite !Z.add_assoc.
  by apply mantissa_digits_ub.
Qed.

Lemma mantissa_digits0 m: (m != 0)%bigZ -> ((mantissa_digits m) == (BigIntRadix2.mantissa_digits (BigZ.to_N m)))%bigZ.
Proof.
  move => H.
  have abs_neq0 : (((BigZ.abs m) =? 0)%bigZ = false).
  - move :H.
    rewrite BigZ.eqb_neq /BigZ.eq BigZ.spec_abs BigZ.spec_0.
    by lia.   
  by rewrite /BigZ.eq mantissa_digits_abs /BigZ.abs /mantissa_digits /BigIntRadix2.mantissa_sign abs_neq0.
Qed.

Lemma round_no_error2 : forall (mode: Interval_definitions.rounding_mode) (e:xpnt) (m:mant) p, ((mantissa_digits m) <= p)%bigZ -> (Interval_definitions.round SFBI2.radix mode (SFBI2.prec p) (D2R (Float m e)) = (D2R (Float m e))).
Proof.
  move => mode e m p.
  case M: (m =? 0)%bigZ.
  - rewrite /mantissa_digits /BigIntRadix2.mantissa_sign M.
    move : M.
    rewrite BigZ.eqb_eq /BigZ.eq BigZ.spec_0 => M H.
    by rewrite D2R_Float M Rmult_0_l /Interval_definitions.round Generic_fmt.round_0.
  have mp : (m != 0)%bigZ by rewrite <- BigZ.eqb_neq.
  rewrite mantissa_digits0; last by [].
  apply round_no_error.
  apply valid_mantissa_bigN.
  move : mp.
  rewrite /BigZ.eq BigZ.spec_to_N.
  by apply Z.neq_mul_0.
Qed.

Lemma round_error2 : forall (mode: Interval_definitions.rounding_mode) (e:xpnt) (m:mant) p, (1 < p)%bigZ -> (Rabs ((Interval_definitions.round SFBI2.radix mode (SFBI2.prec p) (D2R (Float m e))) - (D2R (Float m e)))) <= (powerRZ 2 ([mantissa_digits m]%bigZ+[e]%bigZ+1-[p]%bigZ)).
Proof.
  move => mode e m p P1.
  case P2: (p <=? (mantissa_digits m))%bigZ.
  - by apply round_error; split; [ | rewrite <- BigZ.leb_le].
  rewrite round_no_error2  //=; first by rewrite Rcomplements.Rminus_eq_0 Rabs_R0; apply powerRZ_le;lra.
  apply BigZ.lt_le_incl.
  by rewrite <- BigZ.leb_gt.
Qed.

Lemma exponent_max_spec e e' : (exponent_max e e') = (BigZ.max e e').
Proof.
  by rewrite /exponent_max/BigZ.max/BigIntRadix2.exponent_cmp.
Qed.

Lemma dexp2 e1 e2 mant : (e1 < e2)%bigZ -> (decrease_exp mant e1 e2) = mant.
Proof.
  move => H.
  rewrite /decrease_exp/BigIntRadix2.mantissa_sign.
  case (mant =? 0)%bigZ; first by [].
  suff dexp2' p : (decrease_exp' p e1 e2) = p by case mant => p; by rewrite dexp2'.
  rewrite /decrease_exp'.
  rewrite BigIntRadix2.exponent_cmp_correct /BigIntRadix2.MtoZ.
    rewrite /BigZ.lt in H.
    apply Z.compare_lt_iff in H.
    by rewrite H.
Qed.

Lemma dexp2' e1 e2 mant : (e1 <= e2)%bigZ -> (decrease_exp mant e1 e2) = mant.
Proof.
  move => H.
  apply BigZ.lt_eq_cases in H.
  case H => H'; first by rewrite dexp2.
  rewrite /decrease_exp/BigIntRadix2.mantissa_sign.
  case (mant =? 0)%bigZ; first by [].
  suff dexp2' p : (decrease_exp' p e1 e2) = p by case mant => p; by rewrite dexp2'.
  rewrite /decrease_exp'/BigIntRadix2.exponent_cmp.
  have H'' := H'.
  apply BigZ.compare_eq_iff in H''.
  by rewrite H''.
Qed.

Lemma digits_dec_exp m e m' e' : ((Z.max [mantissa_digits (decrease_exp m e e')]%bigZ [mantissa_digits (decrease_exp m' e' e)]%bigZ) <= (Z.max [mantissa_digits m]%bigZ [mantissa_digits m']%bigZ)+[(exponent_max e e')]%bigZ-[(exponent_min e e')]%bigZ)%Z.
Proof.
  have dexp:= decrease_exp_mantissa_digits_lt.
  rewrite /BigIntRadix2.EtoZ in dexp.
  have expmax e1 e2 : (e1 < e2)%bigZ -> (exponent_max e1 e2) = e2.
  - move => H.
    rewrite /exponent_max.
    rewrite BigIntRadix2.exponent_cmp_correct /BigIntRadix2.MtoZ.
    rewrite /BigZ.lt in H.
    apply Z.compare_lt_iff in H.
    by rewrite H.
  have expmax' e1 e2 : (e1 <= e2)%bigZ -> [(exponent_max e1 e2)]%bigZ = [e2]%bigZ.
  - move => H.
    apply BigZ.lt_eq_cases in H.
    case H => H'; first by rewrite expmax.
    rewrite /exponent_max /BigIntRadix2.exponent_cmp //=.
    have H'' := H'.
    apply BigZ.compare_eq_iff in H''.
    rewrite H''.
    by rewrite /BigZ.eq in H'.
  have expmin e1 e2 : (e1 < e2)%bigZ -> (exponent_min e1 e2) = e1.
  - move => H.
    rewrite /exponent_min.
    rewrite BigIntRadix2.exponent_cmp_correct /BigIntRadix2.MtoZ.
    rewrite /BigZ.lt in H.
    apply Z.compare_lt_iff in H.
    by rewrite H.
  have expmin' e1 e2 : (e1 <= e2)%bigZ -> [(exponent_min e1 e2)]%bigZ = [e1]%bigZ.
  - move => H.
    apply BigZ.lt_eq_cases in H.
    case H => H'; first by rewrite expmin.
    rewrite /exponent_min /BigIntRadix2.exponent_cmp //=.
    have H'' := H'.
    apply BigZ.compare_eq_iff in H''.
    rewrite H''.
    by rewrite /BigZ.eq in H'.
  case C0 : (e' <? e)%bigZ.
  have le := (Z.max_le_compat_r [mantissa_digits (decrease_exp m e e')]%bigZ ([Dmantissa_digits (Float m e) + (e - e')]%bigZ)).
  - apply /Zle_trans.
    apply le.
    apply dexp; last by apply BigZ.ltb_lt.
    rewrite /Dmantissa_digits.
    rewrite (@dexp2 e' e m'); last by apply BigZ.ltb_lt.
    rewrite exponent_min_sym exponent_max_sym.
    rewrite (expmin e' e); last by apply BigZ.ltb_lt.
    rewrite (expmax e' e); last by apply BigZ.ltb_lt.
    rewrite BigZ.spec_add BigZ.spec_sub.
    apply BigZ.ltb_lt in C0.
    by rewrite /BigZ.lt in C0; lia.
  apply BigZ.ltb_ge in C0.
  rewrite dexp2'; last by [].
  rewrite expmax'; try by [].
  rewrite expmin'; try by [].
  apply BigZ.lt_eq_cases in C0.
  case C0 => H.
  have le := (Z.max_le_compat_l [mantissa_digits (decrease_exp m' e' e)]%bigZ ([Dmantissa_digits (Float m' e') + (e' - e)]%bigZ)).
  apply /Zle_trans.
  apply le.
  apply dexp; last by [].
  rewrite /Dmantissa_digits.
  - rewrite BigZ.spec_add BigZ.spec_sub.
    by rewrite /BigZ.lt in H; lia.
  rewrite /BigZ.eq in H.
  rewrite dexp2'; last by rewrite /BigZ.le;lia.
  by lia.
Qed.

Lemma add_error I J n m p:
  (1 < p)%bigZ ->
  bounded I -> diam I <= /2^n -> bounded J -> diam J <= /2^m ->
  bounded (I.add p I J)
  /\
  diam (I.add p I J) <= /2 ^ n + /2 ^ m + (powerRZ 2 (Z.max [(Imantissa_digits I)]%bigZ [(Imantissa_digits J)]%bigZ+(Z.max [Iexp_max I]%bigZ [Iexp_max J]%bigZ)-[p]%bigZ + 3)).
Proof.
  move => pgt.
  case: I => //; case => //lIm lIe; case => //uIm uIe _ ineq; rewrite /= in ineq.
  case: J => //; case => //lJm lJe; case => //uJm uJe _ ineq'; rewrite /= in ineq'.
  set  M := (Z.max [(Imantissa_digits (Interval_interval_float.Ibnd (Float lIm lIe) (Float uIm uIe)))]%bigZ [(Imantissa_digits (Interval_interval_float.Ibnd (Float lJm lJe) (Float uJm uJe)))]%bigZ).
  set  E := (Z.max [(Iexp_max (Interval_interval_float.Ibnd (Float lIm lIe) (Float uIm uIe)))]%bigZ [(Iexp_max (Interval_interval_float.Ibnd (Float lJm lJe) (Float uJm uJe)))]%bigZ).
  split.
  - rewrite /I.add /bounded !SFBI2.real_correct !SFBI2.add_correct.
    rewrite /Xadd.
    by rewrite !D2R_SFBI2toX.
  rewrite /I.add.
  rewrite !SFBI2_add_correct.
  have t1 :  (Interval_definitions.round SFBI2.radix Interval_definitions.rnd_UP (SFBI2.prec p) ((D2R (Float uIm uIe))+(D2R (Float uJm uJe)))) <= ((D2R (Float uIm uIe))+(D2R (Float uJm uJe)))+(powerRZ 2 ((Z.max [mantissa_digits uIm]%bigZ [mantissa_digits uJm]%bigZ)+[exponent_max uJe uIe]%bigZ-[p]%bigZ+2)).
  - rewrite add_float.
    apply (Rcomplements.Rabs_le_between').
    apply /Rle_trans.
    apply round_error2; last by [].
    rewrite !powerRZ_Rpower; try by lra.
    apply Rle_Rpower; try by lra.
    apply IZR_le.
    suff: ([mantissa_digits (decrease_exp uIm uIe uJe + decrease_exp uJm uJe uIe)]%bigZ <=   (Z.max [mantissa_digits uIm]%bigZ [mantissa_digits uJm]%bigZ) + [exponent_max uJe uIe]%bigZ - [exponent_min uIe uJe]%bigZ +1)%Z by lia.
    apply /Zle_trans.
    apply add_mantissa_digits2.
    suff : ((Z.max [mantissa_digits (decrease_exp uIm uIe uJe)]%bigZ [mantissa_digits (decrease_exp uJm uJe uIe)]%bigZ) <= (Z.max [mantissa_digits uIm]%bigZ [mantissa_digits uJm]%bigZ) + [exponent_max uJe uIe]%bigZ - [exponent_min uIe uJe]%bigZ)%Z by lia.
    apply /Zle_trans.
    apply digits_dec_exp.
    by rewrite exponent_max_sym;lia.
  have t1' : (Interval_definitions.round SFBI2.radix Interval_definitions.rnd_UP (SFBI2.prec p) ((D2R (Float uIm uIe))+(D2R (Float uJm uJe)))) <= ((D2R (Float uIm uIe))+(D2R (Float uJm uJe)))+(powerRZ 2 (M+E-[p]%bigZ+2)%Z).
  - apply /Rle_trans.
    apply t1.
    suff : (powerRZ 2 (Z.max [mantissa_digits uIm]%bigZ [mantissa_digits uJm]%bigZ + [exponent_max uJe uIe]%bigZ - [p]%bigZ + 2)) <= (powerRZ 2 (M + E - [p]%bigZ + 2)) by lra.
    rewrite !powerRZ_Rpower; try by lra.
    apply Rle_Rpower; try by lra.
    apply IZR_le.
    suff [B1 B2] : ((Z.max [mantissa_digits uIm]%bigZ [mantissa_digits uJm]%bigZ) <= M)%Z /\ ([exponent_max uJe uIe]%bigZ <= E)%Z by lia.
   split.
   + by rewrite /M/Imantissa_digits/Dmantissa_digits !BigZ.spec_max //=; lia.
     by rewrite /E /Iexp_max/Dexp/exponent_max_spec !BigZ.spec_max //=; lia.
  have t2 :   ((D2R (Float lIm lIe))+(D2R (Float lJm lJe))) <= (Interval_definitions.round SFBI2.radix Interval_definitions.rnd_DN (SFBI2.prec p) ((D2R (Float lIm lIe))+(D2R (Float lJm lJe))))+ (powerRZ 2 ((Z.max [mantissa_digits lIm]%bigZ [mantissa_digits lJm]%bigZ)+[exponent_max lJe lIe]%bigZ-[p]%bigZ+2)) .
  - rewrite add_float.
    apply (Rcomplements.Rabs_le_between').
    rewrite Rabs_minus_sym.
    apply /Rle_trans.
    apply round_error2; last by [].
    rewrite !powerRZ_Rpower; try by lra.
    apply Rle_Rpower; try by lra.
    apply IZR_le.
    suff: ([mantissa_digits (decrease_exp lIm lIe lJe + decrease_exp lJm lJe lIe)]%bigZ <=   (Z.max [mantissa_digits lIm]%bigZ [mantissa_digits lJm]%bigZ) + [exponent_max lJe lIe]%bigZ - [exponent_min lIe lJe]%bigZ +1)%Z by lia.
    apply /Zle_trans.
    apply add_mantissa_digits2.
    suff : ((Z.max [mantissa_digits (decrease_exp lIm lIe lJe)]%bigZ [mantissa_digits (decrease_exp lJm lJe lIe)]%bigZ) <= (Z.max [mantissa_digits lIm]%bigZ [mantissa_digits lJm]%bigZ) + [exponent_max lJe lIe]%bigZ - [exponent_min lIe lJe]%bigZ)%Z by lia.
    apply /Zle_trans.
    apply digits_dec_exp.
    by rewrite exponent_max_sym;lia.
  have t2' : ((D2R (Float lIm lIe))+(D2R (Float lJm lJe))) <= (Interval_definitions.round SFBI2.radix Interval_definitions.rnd_DN (SFBI2.prec p) ((D2R (Float lIm lIe))+(D2R (Float lJm lJe))))+ (powerRZ 2 ((M+E-[p]%bigZ+2)%Z)) .
  - apply /Rle_trans.
    apply t2.
    suff : (powerRZ 2 (Z.max [mantissa_digits lIm]%bigZ [mantissa_digits lJm]%bigZ + [exponent_max lJe lIe]%bigZ - [p]%bigZ + 2)) <= (powerRZ 2 (M + E - [p]%bigZ + 2)) by lra.
    rewrite !powerRZ_Rpower; try by lra.
    apply Rle_Rpower; try by lra.
    apply IZR_le.
    suff [B1 B2] : ((Z.max [mantissa_digits lIm]%bigZ [mantissa_digits lJm]%bigZ) <= M)%Z /\ ([exponent_max lJe lIe]%bigZ <= E)%Z by lia.
   split.
   + by rewrite /M/Imantissa_digits/Dmantissa_digits !BigZ.spec_max //=; lia.
     by rewrite /E /Iexp_max/Dexp/exponent_max_spec !BigZ.spec_max //=; lia.
  rewrite Rcomplements.Rle_minus_l.
  apply /Rle_trans.
  apply t1'.
  have pwr : (powerRZ 2 (M+E - [p]%bigZ + 3)) = (2 * powerRZ 2 (M+E - [p]%bigZ + 2)) by rewrite !(powerRZ_add);try by simpl;lra.
  rewrite pwr.
  suff :  (D2R (Float uIm uIe)) + (D2R (Float uJm uJe)) - (/ 2 ^ n) - (/ 2 ^ m) <= (Interval_definitions.round SFBI2.radix Interval_definitions.rnd_DN (SFBI2.prec p) ((D2R (Float lIm lIe)) + (D2R (Float lJm lJe)))) + (powerRZ 2 (M + E - [p]%bigZ + 2)) by lra.
  have T:= (Rle_trans ((D2R (Float uIm uIe)) + (D2R (Float uJm uJe)) - (/ 2 ^ n) - (/ 2 ^ m))  _ _ _ t2').
  by apply T; lra.
Qed.

Lemma mantissa_digits0' m: ((m == 0)%bigZ /\ ([(mantissa_digits m)]%bigZ =0)%Z) \/ (((BigIntRadix2.valid_mantissa (BigZ.to_N m)) /\ mantissa_digits m == (BigIntRadix2.mantissa_digits (BigZ.to_N m)))%bigZ).
Proof.
  case e : (m =? 0)%bigZ.
  - apply or_introl.
    rewrite <- BigZ.eqb_eq.
    by rewrite /mantissa_digits /BigIntRadix2.mantissa_sign e.
  apply or_intror; split; last by apply mantissa_digits0; rewrite <- BigZ.eqb_neq.
  apply valid_mantissa_bigN.
  move : e.
  rewrite BigZ.eqb_neq /BigZ.eq BigZ.spec_0 /BigZ.to_N /BigZ.to_Z.
  case m => p; by [|lia].
Qed.

Lemma mantissa_digits_lb m : (m != 0)%bigZ -> (powerRZ 2 ([(mantissa_digits m)]%bigZ-1)) <= (Rabs (IZR [m]%bigZ)).
Proof.
case (mantissa_digits0' m) => [[Meq0 P] | [V P]] H; first by [].
  rewrite P.
  have c := BigIntRadix2.mantissa_digits_correct.
  rewrite /BigIntRadix2.EtoZ in c.
  rewrite c; last by [].
  rewrite <- Interval_generic_proof.digits_conversion.
  have [crc _] := (Digits.Zdigits_correct BigIntRadix2.radix (Z.pos (BigIntRadix2.MtoP (BigZ.to_N m)))).
  have r : (Zaux.radix_val BigIntRadix2.radix) = 2%Z by [].
  rewrite <- r.
  rewrite <- Raux.bpow_powerRZ.
  apply IZR_le in crc.
  rewrite abs_IZR Raux.IZR_Zpower in crc; last first.
  - suff: (0 < (Digits.Zdigits BigIntRadix2.radix (Z.pos (BigIntRadix2.MtoP (BigZ.to_N m)))))%Z by lia.
    by apply Digits.Zdigits_gt_0.
  suff: (Rabs (IZR (Z.pos (BigIntRadix2.MtoP (BigZ.to_N m))))) = (Rabs (IZR [m]%bigZ)) by move => <-.
  rewrite !Rabs_Zabs.
  apply IZR_eq.
  move : H.
  case m => n; by rewrite /BigZ.eq BigZ.spec_0 /BigIntRadix2.MtoP  /BigZ.to_Z /BigZ.to_N; have := (BigN.spec_pos n);case [n]%bigN => [| p |p]; try by []; try by lia.
Qed.
Lemma exp_lt m e N : (m != 0)%bigZ -> (Rabs (D2R (Float m e))) <= (powerRZ 2 N) ->  ([e]%bigZ <= N)%Z.
Proof.
  move => H0.
  rewrite D2R_Float Rabs_mult.
  Abort.
Lemma float_lt m e N : (m != 0)%bigZ -> (Rabs (D2R (Float m e))) <= (powerRZ 2 N) -> ((powerRZ 2 [(mantissa_digits m)]%bigZ) <= (powerRZ 2 (N - [e]%bigZ+1))).
Proof.
  move => H0.
  rewrite D2R_Float Rabs_mult.
  rewrite [(Rabs (powerRZ _ _))]Rabs_right; last by apply Rle_ge, powerRZ_le;lra.
  rewrite Rcomplements.Rle_div_r /Rdiv; last by apply Rlt_gt, powerRZ_lt;lra.
  rewrite <- powerRZ_inv, <-powerRZ_neg, <-powerRZ_add, Z.add_opp_r; try by lra.
  move => H.
  suff : (powerRZ 2 ([(mantissa_digits m)]%bigZ-1)) <= (powerRZ 2 (N-[e]%bigZ)) by rewrite !powerRZ_add //=;lra.
  apply /Rle_trans.
  apply mantissa_digits_lb; try by [].
  by [].
 Qed.

Lemma round_error3 : forall (mode: Interval_definitions.rounding_mode) (e:xpnt) (m:mant) p N, (1 < p)%bigZ -> (Rabs (D2R (Float m e))) <= (powerRZ 2 N) -> (Rabs ((Interval_definitions.round SFBI2.radix mode (SFBI2.prec p) (D2R (Float m e))) - (D2R (Float m e)))) <= (powerRZ 2 (N+2-[p]%bigZ)).
Proof.
  move => mode e m p N P1 Lt.
  case P2: (m =? 0)%bigZ; move : P2; [rewrite BigZ.eqb_eq | rewrite BigZ.eqb_neq] => P2.
  - rewrite D2R_Float P2 BigZ.spec_0 Rmult_0_l Rminus_0_r /Interval_definitions.round Generic_fmt.round_0 Rabs_R0.
    apply powerRZ_le;lra.
    apply /Rle_trans.
    by apply round_error2;  [].
  rewrite !powerRZ_add; try by lra.
  apply Rmult_le_compat_r; first by apply powerRZ_le;lra.
  suff : (powerRZ 2 [mantissa_digits m]%bigZ)*(powerRZ 2 ([e]%bigZ-1)) <= (powerRZ 2 N) by rewrite powerRZ_add; simpl;lra.
  rewrite Rcomplements.Rle_div_r /Rdiv; last by apply Rlt_gt, powerRZ_lt;lra.
  rewrite <- powerRZ_inv, <-powerRZ_neg, <-powerRZ_add, Z.add_opp_r, Z.sub_sub_distr; try by lra.
  by apply float_lt.
Qed.
Lemma ID_bound_abs (I : ID) : (bounded I) ->   forall x, x \contained_in I -> (Rabs x) <= (Rabs (lower I))+(diam I).
Proof.
  rewrite /lower/upper.
  case: I => //; case => //lIm lIe; case => //uIm uIe _ x xc.
  have [Lb Ub] := (contains_le (SFBI2.toX (Float lIm lIe)) (SFBI2.toX (Float uIm uIe)) (Xreal x) xc).
  rewrite /le_upper D2R_SFBI2toX in Ub.
  rewrite  D2R_SFBI2toX/le_lower/le_upper//= in Lb.
  case (Rcase_abs x) => x0; [rewrite Rabs_left | rewrite Rabs_right]; by [|case (Rcase_abs (D2R (Float lIm lIe))) => Ip; [rewrite Rabs_left | rewrite Rabs_right]; by [|lra]].
Qed.

Lemma ID_bound_simpl (I : ID) n N : (0 <= N)%Z -> (bounded I) -> (diam I ) <= /2^n -> (exists x, x \contained_in I) -> (Rabs (lower I)) <= (powerRZ 2 N) -> (Rabs (upper I)) <= (powerRZ 2 (N+1)).
Proof.
  move => Ngt.
  rewrite /upper/lower.
  case: I => //; case => //lIm lIe; case => //uIm uIe BI DI nonempty LB.
  apply /Rle_trans.
  apply (ID_bound_abs BI).
  case nonempty => x xp.
  have c := (contains_upper (SFBI2.toX (Float lIm lIe)) (D2R (Float uIm uIe)) (Xreal x)).
  rewrite //= !D2R_SFBI2toX in c,xp.
  rewrite //=!D2R_SFBI2toX.  
  apply c; apply xp.
  simpl. 
  apply /Rle_trans.
  apply Rplus_le_compat_l.
  apply DI.
  apply /Rle_trans.
  apply Rplus_le_compat_r.
  apply LB.
  rewrite powerRZ_add;simpl;last by lra.
  suff : (/ 2 ^ n) <=(powerRZ 2 N) by lra.
  suff K : (/ 2 ^ n) <= 1.
  - apply /Rle_trans.
    apply K.
    rewrite powerRZ_Rpower; try by lra.
    rewrite <- (Rpower_O 2); try by lra.
    apply (Rle_Rpower 2 0 (IZR N)); by [lra | apply IZR_le].
    rewrite Rinv_pow; last by lra.
    case (Nat.eq_0_gt_0_cases n) => H;first by rewrite H //=;lra.
    apply Rlt_le.
    apply pow_lt_1_compat; by [lra|].
Qed.
Lemma ID_bound_dist I x y : (bounded I) -> (x \contained_in I) -> (y \contained_in I) -> (Rabs (x-y)) <= (diam I).  
  case: I => //; case => //lIm lIe; case => //uIm uIe _.
  rewrite //=!D2R_SFBI2toX.  
  move => H1 H2.
  by apply Rcomplements.Rabs_le_between';lra.
Qed.

Lemma upper_lower_contained I : (bounded I)-> (not_empty (I.convert I))-> ((upper I) \contained_in I) /\ ((lower I) \contained_in I).
Proof.
  case: I => //; case => //lIm lIe; case => //uIm uIe BI ne.
  case ne => x xp.
  have u := (contains_upper (SFBI2.toX (Float lIm lIe)) (D2R (Float uIm uIe)) (Xreal x)).
  have l := (contains_lower (D2R (Float lIm lIe)) (SFBI2.toX (Float uIm uIe)) (Xreal x)).
  rewrite //= !D2R_SFBI2toX.
  rewrite //= !D2R_SFBI2toX in u,l,xp.
  by lra.
Qed.

Lemma ID_bound_simpl2 (I : ID) n x N : (0 <= N)%Z -> (bounded I) -> (diam I ) <= /2^n ->  x \contained_in I -> (Rabs x) <= (powerRZ 2 N) -> (Rabs (upper I)) <= (powerRZ 2 (N+1)) /\ (Rabs (lower I)) <= (powerRZ 2 (N+1)).
Proof.
  move => Ngt.
  move => BI DI xc LB.
  have Rabs_bnd a b c : (Rabs (a-b)) <= c -> (Rabs a <= ((Rabs b) + c)).
    move => H.
    suff : (Rabs a - Rabs b <= c) by lra.
    apply /Rle_trans.
    by apply Rabs_triang_inv.
    by [].
  have ne : (not_empty (I.convert I)) by exists x.
  have [U L]  := (upper_lower_contained BI ne).
  have := (ID_bound_dist BI U xc).
  have := (ID_bound_dist BI L xc).
  move : U L BI DI xc LB ne.
  rewrite /upper/lower.
  case: I => //; case => //lIm lIe; case => //uIm uIe _ _ _ D _ xB _ lB uB.
  have lb' : (Rabs ((D2R (Float lIm lIe))-x)) <= (/ 2 ^ n) by lra.
  have ub' : (Rabs ((D2R (Float uIm uIe))-x)) <= (/ 2 ^ n) by lra.
  apply Rabs_bnd in lb'.
  apply Rabs_bnd in ub'.
  have helper0 : (/ 2 ^ n) <= 1.
  - rewrite Rinv_pow; last by lra.
    case (Nat.eq_0_gt_0_cases n) => H;first by rewrite H //=;lra.
    apply Rlt_le.
    by apply pow_lt_1_compat; by [lra|].
  have helper1 : (/ 2 ^ n) <=(powerRZ 2 N).
  - apply /Rle_trans.
    apply helper0.
    rewrite powerRZ_Rpower; try by lra.
    rewrite <- (Rpower_O 2); try by lra.
    by apply (Rle_Rpower 2 0 (IZR N)); by [lra | apply IZR_le].
  by have UB := (Rabs x)+(/ 2 ^ n) <=(powerRZ 2 (N+1));rewrite powerRZ_add /=;lra.
Qed.      

Lemma add_error' I J n m p x y N:
  (1 < p)%bigZ ->
  (0 <= N)%Z ->
  bounded I -> diam I <= /2^n -> bounded J -> diam J <= /2^m ->
  (x \contained_in I) ->
  (y \contained_in J) ->
  (Rabs x) <=  (powerRZ 2 N) -> (Rabs y) <= (powerRZ 2 N) ->
  bounded (I.add p I J)
  /\
  diam (I.add p I J) <= /2 ^ n + /2 ^ m + (powerRZ 2 (N+5-[p]%bigZ)).
Proof.
  move => pgt Ngt.
  move => BI DI BJ DJ xc yc Bx By.
  have [B1 B2] := (ID_bound_simpl2 Ngt BI DI xc Bx). 
  have [B1' B2'] := (ID_bound_simpl2 Ngt BJ DJ yc By). 
  move : BI DI BJ DJ xc yc Bx By B1 B2 B1' B2'.
  rewrite /upper/lower.
  case: I => //; case => //lIm lIe; case => //uIm uIe _ ineq; rewrite /= in ineq.
  case: J => //; case => //lJm lJe; case => //uJm uJe _ ineq' _ _ P1 P2 BIu BIl BJu BJl; rewrite /= in ineq'.
  split.
  - rewrite /I.add /bounded !SFBI2.real_correct !SFBI2.add_correct.
    rewrite /Xadd.
    by rewrite !D2R_SFBI2toX.
  rewrite /I.add.
  rewrite !SFBI2_add_correct.
  have [BP1 BP2] : (Rabs ((D2R (Float uIm uIe))+(D2R (Float uJm uJe)))) <= (powerRZ 2 (N+2)) /\ (Rabs ((D2R (Float lIm lIe))+(D2R (Float lJm lJe)))) <= (powerRZ 2 (N+2)).
  - suff: ((N+2) = (N+1+1))%Z ; last by lia.
    move ->.
    split.
    + apply /Rle_trans.
      apply Rabs_triang.
      by rewrite powerRZ_add //=;lra.
    apply /Rle_trans.
    apply Rabs_triang.
    by rewrite powerRZ_add //=;lra.
  have t1 :  (Interval_definitions.round SFBI2.radix Interval_definitions.rnd_UP (SFBI2.prec p) ((D2R (Float uIm uIe))+(D2R (Float uJm uJe)))) <= ((D2R (Float uIm uIe))+(D2R (Float uJm uJe)))+(powerRZ 2 ((N+4-[p]%bigZ))).
  - rewrite add_float in BP1.
    rewrite add_float.
    apply (Rcomplements.Rabs_le_between').
    apply /Rle_trans.
    apply (round_error3 _ pgt BP1); try by [].
    suff : ((N + 2 + 2 -[p]%bigZ) = (N + 4 - [p]%bigZ))%Z by move => ->;apply Req_le.
    by lia.
  have t2 :   ((D2R (Float lIm lIe))+(D2R (Float lJm lJe))) <= (Interval_definitions.round SFBI2.radix Interval_definitions.rnd_DN (SFBI2.prec p) ((D2R (Float lIm lIe))+(D2R (Float lJm lJe))))+ (powerRZ 2 ((N+4-[p]%bigZ))).
  - rewrite add_float in BP2.
    rewrite add_float.
    apply (Rcomplements.Rabs_le_between').
    rewrite Rabs_minus_sym.
    apply /Rle_trans.
    apply (round_error3 _ pgt BP2); try by [].
    suff : ((N + 2 + 2 -[p]%bigZ) = (N + 4 - [p]%bigZ))%Z by move => ->;apply Req_le.
    by lia.
  rewrite Rcomplements.Rle_minus_l.
  apply /Rle_trans.
  apply t1.
  have pwr : (powerRZ 2 (N+5 - [p]%bigZ)) = (2*powerRZ 2 (N+4- [p]%bigZ)) by rewrite !(powerRZ_add);try by simpl;lra.
  rewrite pwr.
  suff :  (D2R (Float uIm uIe)) + (D2R (Float uJm uJe)) - (/ 2 ^ n) - (/ 2 ^ m) <= (Interval_definitions.round SFBI2.radix Interval_definitions.rnd_DN (SFBI2.prec p) ((D2R (Float lIm lIe)) + (D2R (Float lJm lJe)))) + (powerRZ 2 (N + 4 - [p]%bigZ)) by lra.
  have T:= (Rle_trans ((D2R (Float uIm uIe)) + (D2R (Float uJm uJe)) - (/ 2 ^ n) - (/ 2 ^ m))  _ _ _ t2).
  by apply T; lra.
Qed.


Definition Rplus_rlzrf (phi: questions (IR \*_cs IR)) (n: queries IR):= I.add (nat2p n) (lprj phi n) (rprj phi n).
Definition Rplus_rlzr: questions (IR \*_cs IR) ->> questions IR := F2MF Rplus_rlzrf.

Lemma powerRZ2_bound x y : exists K, (1 <= K)%nat /\ ((Rabs x) <= (powerRZ 2 (Z.of_nat K))) /\ ((Rabs y) <= (powerRZ 2 (Z.of_nat K))).
Proof.
  have tp2_upper t: exists K, (0 <= K)%Z /\ (Rabs t) <= (powerRZ 2 K).
  - have [A _] := (archimed (Rabs t)).
    have A' : (Rabs t) <= (IZR (up (Rabs t))) by lra.
    case e : ((up (Rabs t)) <=? 1)%Z; move : e; [rewrite Z.leb_le | rewrite Z.leb_gt]=>e.
    + exists 1%Z; split; first by lia.
      apply /Rle_trans.
      apply A'.
      apply /Rle_trans.
      apply (IZR_le _ _ e).
      by simpl;lra.
    exists (Z.log2_up (up (Rabs t))); split; first by apply Z.log2_up_nonneg.
    have [_ lt] := (Z.log2_up_spec (up (Rabs t)) e).
    apply /Rle_trans.
    apply A'.
    apply /Rle_trans.
    apply (IZR_le _ _ lt).
    rewrite (Raux.IZR_Zpower SFBI2.radix); last by apply Z.log2_up_nonneg.
    by rewrite <- (Raux.bpow_powerRZ SFBI2.radix);lra.
  case (tp2_upper x) => Ux [Uxge0 Uxp]; case (tp2_upper y) => Uy [Uyge0 Uyp].
  have [T1 T2] : ((Z.to_nat Ux) <= (maxn 1 (maxn (Z.to_nat Ux) (Z.to_nat Uy))))%nat /\ ((Z.to_nat Uy) <= (maxn 1 (maxn (Z.to_nat Ux) (Z.to_nat Uy))))%nat.
  - split.
    apply /leP /Nat.le_trans.
    apply /leP; apply (leq_maxl (Z.to_nat Ux) (Z.to_nat Uy)).
    by apply /leP; apply leq_maxr.
    apply /leP /Nat.le_trans.
    apply /leP; apply (leq_maxr (Z.to_nat Ux) (Z.to_nat Uy)).
    by apply /leP; apply leq_maxr.
    exists (maxn 1 (maxn (Z.to_nat Ux) (Z.to_nat Uy))); split; first exact: (leq_maxl 1 _).
    split.
    + apply /Rle_trans.
      apply Uxp.
      rewrite !powerRZ_Rpower; try by lra.
      apply Rle_Rpower; try by lra.
      apply IZR_le.
      apply Z2Nat.inj_le; [by [] | by apply Zle_0_nat | ].
      rewrite Nat2Z.id.
      by apply /leP.
    apply /Rle_trans.
    apply Uyp.
    rewrite !powerRZ_Rpower; try by lra.
    apply Rle_Rpower; try by lra.
    apply IZR_le.
    apply Z2Nat.inj_le; [by [] | by apply Zle_0_nat | ].
    rewrite Nat2Z.id.
    by apply /leP.
Qed.
Lemma Rplus_rlzr_spec : Rplus_rlzr \realizes (F2MF (fun xy => Rplus xy.1 xy.2)).
Proof.
  rewrite F2MF_rlzr_F2MF => phi [x y] [/=[xephin convx] [yephin convy]].
  split => n; first by apply/add_correct_R; [apply xephin | apply yephin].
  case (powerRZ2_bound x y) => K [Kprp1 [Kprp2 Kprp3]].
  have [N Nprp]:= convx n.+2.
  have [M Mprp]:= convy n.+2.
  exists (maxn ((K+n.+1).+3.+2)%nat (maxn M N)) => k ineq.
  have [ | bndl dml]:= Nprp k.
	- apply/leq_trans; first exact: (leq_maxr M N).
  	by apply/leq_trans; first exact: (leq_maxr ((K+n.+1).+3.+2)%nat (maxn M N)).
  have [ | bndr dmr]:= Mprp k.
	- apply/leq_trans; first exact: (leq_maxl M N).
	  by apply/leq_trans; first exact: (leq_maxr ((K+n.+1).+3.+2)%nat (maxn M N)).
  have t : ((Int31.phi 1) = 1)%Z by [].
  have kgel : ((K+n.+1)%coq_nat.+3.+2 <= k)%coq_nat.
  - by apply (Nat.le_trans ((K+n.+1).+3.+2) (maxn ((K+n.+1).+3.+2) (maxn M N)) k);apply /leP; by [apply (leq_maxl ((K+n.+1).+3.+2) (maxn M N))|].
  have lt: (1 < nat2p k)%bigZ.
  - suff : (1 < k)%coq_nat.
    rewrite /nat2p/SFBI2.PtoP/BigZ.lt //=.   
    rewrite BigN.spec_of_pos.
    rewrite t.
    rewrite Nat2Z.inj_lt //=.
    case  k => [|p]; by [lia |rewrite /Z.of_nat Pos.of_nat_succ].
    by suff : ((K+n.+1).+3.+2 <= k)%coq_nat by lia.
  have lt' : (0 <= Z.of_nat K)%Z by lia. 
  have [bnd err] := (add_error' lt lt' bndl dml bndr dmr (xephin k) (yephin k) Kprp2 Kprp3).
  split; first by apply bnd.
  apply /Rle_trans.
  apply err.
  suff H : (powerRZ 2 ((Z.of_nat K)+5 - [nat2p k]%bigZ)) <= (/ 2 ^ n.+1).
  - apply /Rle_trans.
    apply Rplus_le_compat_l.
    apply H.
    by rewrite <- !tpmn_half;lra.
  rewrite <- powerRZ2_neg_pos.
  rewrite !powerRZ_Rpower;try by lra.
  apply Rle_Rpower; try by lra.
  move : lt.
  rewrite /nat2p /SFBI2.PtoP/BigIntRadix2.ZtoE/BigZ.lt !BigIntRadix2.ZtoE_correct.
  move => lt.
  have zp : (Z.pos (Pos.of_nat k)) = (Z.of_nat k).
  - move :lt.
    case k => [| p H] ; try by simpl; [].
    by rewrite <- Pos.of_nat_succ, Zpos_P_of_succ_nat;lia.
  rewrite zp.
  by apply IZR_le;lia.
Qed.

Lemma mul_float m1 e1 m2 e2 : (D2R (Float m1 e1)*(D2R (Float m2 e2))) = (D2R (Float (m1*m2)%bigZ (e1+e2)%bigZ)).
Proof.
  rewrite !D2R_Float.
  have comm u v w t : u*v*(w*t) = (u*w*(v*t)) by lra.
  rewrite comm.
  rewrite <- powerRZ_add; try by [].
  by rewrite <- BigZ.spec_add,<- mult_IZR,<-BigZ.spec_mul.
Qed.
Lemma round_error_mul p rnd m1 e1 m2 e2 M: (1 < p)%bigZ -> (Rabs (D2R (Float m1 e1))) <= (powerRZ 2 M) -> (Rabs (D2R (Float m2 e2))) <= (powerRZ 2 M) -> (D2R (Float m1 e1))*(D2R (Float m2 e2)) - (powerRZ 2 (2*M+2-[p]%bigZ)%Z) <= (Interval_definitions.round SFBI2.radix rnd (SFBI2.prec p) ((D2R (Float m1 e1))*(D2R (Float m2 e2)))) <= (D2R (Float m1 e1))*(D2R (Float m2 e2)) + (powerRZ 2 (2*M+2-[p]%bigZ)%Z).
Proof.
  move => pgt H1 H2.
  rewrite !mul_float.
  have lt : (Rabs (D2R (Float (m1*m2)%bigZ (e1+e2)%bigZ))) <= (powerRZ 2 (2*M)).
  - rewrite <- mul_float.
    rewrite Rabs_mult.
    rewrite <-Z.add_diag, powerRZ_add; last by lra.
    by apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | |].
  apply Rcomplements.Rabs_le_between'.
  apply round_error3; by [].
Qed.

Lemma non_empty_diam_pos I x: (bounded I) -> (x \contained_in I) -> (0 <= (upper I - lower I)).
Proof.
  move => H1 H2.
  have Rabs_0 : (Rabs (x-x)) = 0 by rewrite Rcomplements.Rminus_eq_0 Rabs_R0.
  rewrite <- Rabs_0.
  apply ID_bound_dist; by [].
Qed.

Lemma mul_error I J n m p x y N:
  (1 < p)%bigZ ->
  (0 <= N)%Z ->
  bounded I -> diam I <= /2^n -> bounded J -> diam J <= /2^m ->
  (x \contained_in I) ->
  (y \contained_in J) ->
  (Rabs x) <=  (powerRZ 2 N) -> (Rabs y) <= (powerRZ 2 N) ->
  bounded (I.mul p I J)
  /\
  diam (I.mul p I J) <= (powerRZ 2 (N+1-(Z.of_nat n)))+ (powerRZ 2 (N+1-(Z.of_nat m))) + (powerRZ 2 (2*N+5-[p]%bigZ)).
Proof.
  move => pgt Ngt.
  move => BI DI BJ DJ xc yc Bx By.
  have [B1 B2] := (ID_bound_simpl2 Ngt BI DI xc Bx). 
  have [B1' B2'] := (ID_bound_simpl2 Ngt BJ DJ yc By). 
  have [diam_abs_diamI diam_abs_diamJ] : (diam I) = (Rabs (diam I)) /\ (diam J) = (Rabs (diam J)).
  - rewrite !Rabs_right; by [|  apply Rle_ge; apply (non_empty_diam_pos BJ yc)| apply Rle_ge; apply (non_empty_diam_pos BI xc)].
  move : BI DI BJ DJ xc yc Bx By B1 B2 B1' B2' diam_abs_diamJ diam_abs_diamI.
  have sub_simplification a b a' b': (a <= a') -> (b' <= b) -> (a-b <= a' - b') by lra.
  have mul_sub_err u u' v v' n1 n2: (Rabs (u-u')) <= (/ 2 ^ n1) -> (Rabs (v - v')) <= (/2 ^ n2) -> (Rabs (u*v-u'*v')) <= (Rabs v)*(/2 ^ n1) + (Rabs u')*(/2 ^ n2).
  - move => H1 H2.
   have s : (u*v - u'*v') = v*(u-u') + u'*(v-v') by lra.
   rewrite s.
   apply /Rle_trans.
   apply Rabs_triang.
   rewrite !Rabs_mult.
   apply Rplus_le_compat.
   - by apply Rmult_le_compat_l; [apply Rabs_pos | apply H1].
   by apply Rmult_le_compat_l; [apply Rabs_pos | apply H2].
  have mul_sub_err' u u' v v' n1 n2 M: (Rabs (u-u')) <= (/ 2 ^ n1) -> (Rabs (v - v')) <= (/2 ^ n2) -> (Rabs v) <= (powerRZ 2 M) -> (Rabs u') <= (powerRZ 2 M) -> (Rabs (u*v-u'*v')) <= (powerRZ 2 (M-(Z.of_nat n1))) + (powerRZ 2 (M-(Z.of_nat n2))).
  - move => H1 H2 H3 H4.
    apply /Rle_trans.
    apply (mul_sub_err _ _ _ _ n1 n2); try by [].
    rewrite !powerRZ_add;try by lra.
    rewrite !powerRZ2_neg_pos.
    apply Rplus_le_compat; by apply Rmult_le_compat_r; [apply tpmn_pos | ].
  have round_sub_simplification M rnd rnd' m1 m2 m3 m4 e1 e2 e3 e4: ((Rabs (D2R (Float m1 e1))) <= (powerRZ 2 M)) -> ((Rabs (D2R (Float m2 e2))) <= (powerRZ 2 M)) -> ((Rabs (D2R (Float m3 e3))) <= (powerRZ 2 M)) -> ((Rabs (D2R (Float m4 e4))) <= (powerRZ 2 M)) -> (SFBI2.mul rnd p (Float m1 e1) (Float m2 e2)) - (SFBI2.mul rnd' p (Float m3 e3) (Float m4 e4)) <= (D2R (Float m1 e1))*(D2R (Float m2 e2)) + (powerRZ 2 (2*M+2-[p]%bigZ)%Z) - ((D2R (Float m3 e3))*(D2R (Float m4 e4)) - (powerRZ 2 (2*M+2-[p]%bigZ)%Z)).
  - move => B1 B2 B3 B4.
    rewrite /D2R !SFBI2.mul_correct /Xmul !D2R_SFBI2toX //=.
     by apply sub_simplification;apply round_error_mul; try by [].
  rewrite /upper/lower.
  case: I => //; case => //lIm lIe; case => //uIm uIe  _ ineq; rewrite /= in ineq.
  case: J => //; case => //lJm lJe; case => //uJm uJe _ ineq'  _ _  P1 P2 BIu BIl BJu BJl diam_absJ diam_absI; rewrite /= in ineq'.
  split.
  - rewrite /bounded /I.mul.
    case : (I.sign_large_ (Float lIm lIe) (Float uIm uIe));case : (I.sign_large_ (Float lJm lJe) (Float uJm uJe)); try by []; try by rewrite /I.mul !SFBI2.real_correct !SFBI2.mul_correct /Xmul !D2R_SFBI2toX.
    rewrite !SFBI2.real_correct !SFBI2.max_correct !SFBI2.min_correct !SFBI2.mul_correct /Xmul.
    by rewrite /Xmin /Xmax !D2R_SFBI2toX.
    rewrite /I.mul.
    have helper u v u' v' : (u*v + (powerRZ 2 (2*(N+1)+2-[p]%bigZ)))-(u'*v' - (powerRZ 2 (2*(N+1)+2-[p]%bigZ))) = (u*v - u'*v')+(powerRZ 2 (2*N+5-[p]%bigZ)).
    - suff :  (powerRZ 2 1)*(powerRZ 2 (2 * (N + 1) + 2 - [p]%bigZ))  =  (powerRZ 2 (2*N + 5 - [p]%bigZ)) by simpl;lra.
      rewrite <- powerRZ_add; try by lra.
      suff H0 :((1 + (2 * (N + 1) + 2 - [p]%bigZ)) =  (2 * N + 5 - [p]%bigZ))%Z by rewrite H0.
      by lia.
    rewrite diam_absI in ineq.
    rewrite diam_absJ in ineq'.
    have ineq_rev := ineq.
    have ineq'_rev := ineq'.
    have ineq_triv z k: (Rabs (z - z) <= / 2 ^ k) by rewrite Rcomplements.Rminus_eq_0 Rabs_R0;apply tpmn_pos.
    rewrite Rabs_minus_sym in ineq_rev.
    rewrite Rabs_minus_sym in ineq'_rev.
    have case_helper rnd rnd' m1 e1 m2 e2 m1' e1' m2' e2' : (Rabs (D2R (Float m1 e1))) <= (powerRZ 2 (N+1)) -> (Rabs (D2R (Float m1' e1'))) <= (powerRZ 2 (N+1)) -> (Rabs (D2R (Float m2 e2))) <= (powerRZ 2 (N+1)) -> (Rabs (D2R (Float m2' e2'))) <= (powerRZ 2 (N+1)) ->  (Rabs ((D2R (Float m1 e1)) - (D2R (Float m1' e1')))) <= / 2 ^ n -> (Rabs ((D2R (Float m2 e2)) - (D2R (Float m2' e2')))) <= / 2 ^ m -> (SFBI2.mul rnd p (Float m1 e1) (Float m2 e2)) - (SFBI2.mul  rnd' p (Float m1' e1') (Float m2' e2')) <= (powerRZ 2 (N+1-(Z.of_nat n)))+(powerRZ 2 (N+1-(Z.of_nat m)))+(powerRZ 2 (2*N + 5 - [p]%bigZ)).
    move => H1 H2 H3 H4 H5 H6.
    apply /Rle_trans.
    apply (round_sub_simplification (N+1)%Z); try by [].
    rewrite helper.
    apply Rplus_le_compat_r.
    apply /Rle_trans.
    apply Rle_abs.
    by apply mul_sub_err'; by [].
  have case_helper2 : (D2R (SFBI2.zero) - (D2R SFBI2.zero)) <=
  powerRZ 2 (N + 1 - Z.of_nat n) + powerRZ 2 (N + 1 - Z.of_nat m) +
  powerRZ 2 (2 * N + 5 - [p]%bigZ).
  - rewrite /D2R SFBI2.zero_correct Rminus_0_r //=.
    apply Rplus_le_le_0_compat; [apply Rplus_le_le_0_compat |]; by apply powerRZ_le;lra.
  case : (I.sign_large_ (Float lIm lIe) (Float uIm uIe));case : (I.sign_large_ (Float lJm lJe) (Float uJm uJe)); try by (try apply case_helper2; try by (apply case_helper; by [])).
  have := (case_helper Interval_definitions.rnd_UP Interval_definitions.rnd_DN lIm lIe lJm lJe lIm lIe uJm uJe).
  have := (case_helper Interval_definitions.rnd_UP Interval_definitions.rnd_DN lIm lIe lJm lJe uIm uIe lJm lJe).
  have := (case_helper Interval_definitions.rnd_UP Interval_definitions.rnd_DN uIm uIe uJm uJe lIm lIe uJm uJe).
  have := (case_helper Interval_definitions.rnd_UP Interval_definitions.rnd_DN uIm uIe uJm uJe uIm uIe lJm lJe).
  rewrite /D2R !SFBI2.max_correct !SFBI2.min_correct /Xmin /Xmax !SFBI2.mul_correct /Xmul  !D2R_SFBI2toX //= .
  apply Rmax_case;apply Rmin_case; try by auto.
Qed.
Definition Rmult_rlzrf (phi: questions (IR \*_cs IR)) (n: queries IR):= I.mul (nat2p n) (lprj phi n) (rprj phi n).
Definition Rmult_rlzr: questions (IR \*_cs IR) ->> questions IR := F2MF Rmult_rlzrf.
Lemma maxN3 x y z B: ((maxn x (maxn  y z)) <= B)%nat -> (x <= B /\ y <= B /\ z <= B)%nat.
Proof.
  split; first by apply (leq_trans (leq_maxl x (maxn y z)) H).
  split.
  - apply /leq_trans.
    apply (leq_maxl y z).
    apply /leq_trans.
    apply (leq_maxr x (maxn y z)).
    by apply H.
  apply /leq_trans.
  apply (leq_maxr y z).
  apply /leq_trans.
  apply (leq_maxr x (maxn y z)).
  by apply H.
Qed.
Lemma Rmult_rlzr_spec : Rmult_rlzr \realizes (F2MF (fun xy => Rmult xy.1 xy.2)).
Proof.
  rewrite F2MF_rlzr_F2MF => phi [x y] [/=[xephin convx] [yephin convy]].
  split => n; first by apply/mul_correct_R; [apply xephin | apply yephin].
  case (powerRZ2_bound x y) => K [Kprp1 [Kprp2 Kprp3]].
  have [N Nprp]:= convx (K+n.+3)%nat.
  have [M Mprp]:= convy (K+n.+3)%nat.
  exists (maxn ((2*K+n.+1).+3.+2)%nat (maxn M N)) => k ineq.
  have [Kp1 [Kp2 Kp3]] := (maxN3 ineq).
  have [ | bndl dml]:= Nprp k; first by [].
  have [ | bndr dmr]:= Mprp k; first by [].
  have t : ((Int31.phi 1) = 1)%Z by [].
  have lt: (1 < nat2p k)%bigZ.
  - suff : (1 < k)%coq_nat.
    rewrite /nat2p/SFBI2.PtoP/BigZ.lt //=.   
    rewrite BigN.spec_of_pos.
    rewrite t.
    rewrite Nat2Z.inj_lt //=.
    case  k => [|p]; by [lia |rewrite /Z.of_nat Pos.of_nat_succ].
    suff : ((2*K+n.+1).+3.+2 <= k)%coq_nat by lia.
    by apply /ltP.
  have lt' : (0 <= Z.of_nat K)%Z by lia. 
  have := (mul_error lt lt' bndl dml bndr dmr (xephin k) (yephin k) Kprp2 Kprp3).
  suff : ((((Z.of_nat K)+1)%Z-(Z.of_nat (K+ (n.+3))%nat)) = -(Z.of_nat (n.+2)))%Z; last by rewrite Nat2Z.inj_add;lia.
  move => -> [bnd err].
  split; first by apply bnd. 
  apply /Rle_trans.
  apply err.
  rewrite powerRZ2_neg_pos.
  suff H : (powerRZ 2 (2*(Z.of_nat K)+5 - [nat2p k]%bigZ)) <= (/ 2 ^ n.+1).
  - apply /Rle_trans.
    apply Rplus_le_compat_l.
    apply H.
    by rewrite <- !tpmn_half;lra.
  rewrite <- powerRZ2_neg_pos.
  rewrite !powerRZ_Rpower;try by lra.
  apply Rle_Rpower; try by lra.
  move : lt.
  rewrite /nat2p /SFBI2.PtoP/BigIntRadix2.ZtoE/BigZ.lt !BigIntRadix2.ZtoE_correct.
  move => lt.
  have zp : (Z.pos (Pos.of_nat k)) = (Z.of_nat k).
  - move :lt.
    case k => [| p H] ; try by simpl; [].
    by rewrite <- Pos.of_nat_succ, Zpos_P_of_succ_nat;lia.
  rewrite zp.
  apply IZR_le.
  suff : ((((Z.of_nat 2)*Z.of_nat K)+(Z.of_nat n.+1))+(Z.of_nat 4) < (Z.of_nat k))%Z by lia.
  rewrite <- Nat2Z.inj_mul,<- !Nat2Z.inj_add.
  apply inj_lt.
  have p a : (a+4)%coq_nat = (a.+4) by lia.
  rewrite p.
  suff : ((((2*K)+(n.+1)).+4) < k)%nat by apply /ltP.
  by apply Kp1.
Qed.

Definition ZtoIR z : (questions IR):= (fun p:nat => (I.fromZ z)).
Definition FloattoIR m e : (questions IR):= (fun p:nat => (I.bnd (Float (BigZ.of_Z m) (BigZ.of_Z e)) (Float (BigZ.of_Z m) (BigZ.of_Z e)))).

Definition to_pair (d : D) := match d with
                         | Fnan => (0%Z, 1%Z)
                         | (Float m e) => ([m]%bigZ, [e]%bigZ)
                                end.
                          
 Definition plus_float m1 e1 m2 e2 (n:nat) := (to_pair (I.midpoint (Rplus_rlzrf (name_pair (FloattoIR m1 e1) (FloattoIR m2 e2)) n))).

 Compute (plus_float 12 2 3 2 50).
 Fixpoint times_with_plus m e N : (name_space IR)  := match N with
                                       | 0%nat => (FloattoIR 0 0)
                                       | 1%nat => (FloattoIR m e)
                                       | M.+1 => (Rplus_rlzrf (name_pair (FloattoIR m e) (times_with_plus m e M)))
                                       end.

 Fixpoint power_with_mult m e N : (name_space IR)  := match N with
                                       | 0%nat => (FloattoIR 1 0)
                                       | M.+1 => (Rmult_rlzrf (name_pair (FloattoIR m e) (power_with_mult m e M)))
                                       end.
 
 Fixpoint logistic_map phi rm re N : (name_space IR)  := match N with
                                       | 0%nat => phi
                                       | M.+1 => let P := (logistic_map phi rm re M) in (Rmult_rlzrf (name_pair (FloattoIR rm re) (Rmult_rlzrf (name_pair P (Rplus_rlzrf (name_pair (FloattoIR 1 0) (Rmult_rlzrf (name_pair (FloattoIR (-1) 0) P))))))))
                                       end.
  Compute (logistic_map (FloattoIR 1 (-1)) 120 (-5) 15 400%nat).

Require Import Q_reals.
  Definition Q2RQ (q:Q) := (fun (eps :Q) => q). 
 Fixpoint logistic_map_RQ x0 r N : (name_space RQ)  := match N with
                                       | 0%nat => (Q2RQ x0)
                                       | M.+1 => let P := (logistic_map_RQ x0 r M) in (Rmult_rlzrf (name_pair (Q2RQ r) (Rmult_rlzrf (name_pair P (Rplus_rlzrf (name_pair (Q2RQ (1)%Q) (Rmult_rlzrf (name_pair (Q2RQ (-1%Q)) P))))))))
                                       end.

 Fixpoint logistic_map_rlzrf x0 r N n : ID := match N with
                                       | 0%nat => x0
                                       | M.+1 => let P := (logistic_map_rlzrf x0 r M n) in (I.mul n r (I.mul n P (I.add n (I.fromZ 1) (I.neg P))))
                                       end.
 Fixpoint logistic_map_rlzrfZ x0 r N n : IDZ := match N with
                                       | 0%nat => x0
                                       | M.+1 => let P := (logistic_map_rlzrfZ x0 r M n) in (IZ.mul n r (IZ.mul n P (IZ.add n (IZ.fromZ 1) (IZ.neg P))))
                                       end.
 Fixpoint logistic_map_Q x0 r (N:nat) : Q := match N with
                                             | 0%nat => x0
                                             | M.+1 => let P := (logistic_map_Q x0 r M) in
                                                      (r*P*(1-P))%Q
                                        end.

                                              
                                                        
                                                
  Definition logistic_map_mp x0m x0e rm re (N :nat) (n :nat):= (to_pair (I.midpoint (logistic_map (FloattoIR x0m x0e) rm re N n))).
  Definition logistic_map_mp_rlzr (N :nat) (n :Z):= (to_pair (I.midpoint (logistic_map_rlzrf (I.bnd (Float 1%bigZ (-1)%bigZ) (Float (1%bigZ) (-1)%bigZ)) (I.bnd (Float 15%bigZ (-2)%bigZ) (Float 15%bigZ (-2)%bigZ)) N (BigZ.of_Z n)))).
Definition to_pairZ (d : Dz) := match d with
                         | Fnan => (0%Z, 1%Z)
                         | (Float m e) => (m, e)
                                end.
Search _ (Dz -> Dz ->Dz).
Definition midpoint_err I := (to_pairZ(IZ.midpoint I), to_pairZ(SF2.sub Interval_definitions.rnd_UP 1%Z (IZ.upper I) (IZ.lower I))).
Definition midpoint_errI I := (to_pair(I.midpoint I), to_pair(SFBI2.sub Interval_definitions.rnd_UP 1%bigZ (I.upper I) (I.lower I))).
  Definition logistic_map_mp_rlzrZ (N :nat) (n :Z):= (midpoint_err (logistic_map_rlzrfZ (IZ.bnd (Float 1%Z (-1)%Z) (Float 1%Z (-1)%Z)) (IZ.bnd (Float 15%Z (-2)%Z) (Float 15%Z (-2)%Z)) N n)).
  Compute (logistic_map_mp 1 (-1) 120 (-5) 5 10%nat).
  Compute (logistic_map_mp_rlzr 100 100).
  Compute (logistic_map_mp_rlzrZ 81 200).
  Require Extraction.

  Require ExtrHaskellBasic.
  Require ExtrHaskellZInteger.
  Require ExtrHaskellNatInteger.
  Extraction Language Haskell.
  Definition log_map_Q N :=(logistic_map_Q (1#2) (15#4) N).
  Extraction "logisticZ" logistic_map_mp_rlzrZ.
  Definition sine_rlzrf (phi: (questions IR)) (n: queries IR) := I.sin (nat2p n) (phi n).
  Definition Pi (n : (queries IR)) : (answers IR)  := (I.pi (nat2p n)).
  Compute (midpoint_errI (sine_rlzrf (Top.Rmult_rlzrf (name_pair (ZtoIR 5001) (Top.Rmult_rlzrf (name_pair Pi (FloattoIR 1%Z (-2)%Z))))) 300%nat)).
Search _ (Z->Z->Z*Z).
Print Zaux.div_fast
Print positive.
Search _ "log".
Print Z.shiftl.
Search _ (Z -> positive -> Z).
Print Z.pow_pos.
Print Pos.iter.
Check Z.of_N.
Print Z.
 Compute (plus_float 3%Z 2%Z (-3)%Z 10%Z 10%nat).
Compute ((Rplus_rlzrf (name_pair (ZtoIR (Z.pow 4 4000000)) (ZtoIR 4))) 2%nat).
200u
