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

Module SF2 := SpecificFloat StdZRadix2.
Module I := FloatIntervalFull SF2.

Notation D:= SF2.type.
Notation mant := StdZRadix2.smantissa_type.
Notation xpnt := StdZRadix2.exponent_type.
Notation ID := (Interval_interval_float.f_interval SF2.type).

Notation "x '\contained_in' I" := (Interval_interval.contains (I.convert I) (Xreal x)) (at level 2).
Coercion I.convert: ID >-> Interval_interval.interval.
Notation D2R := I.T.toR.
Coercion I.T.toR: D >-> R.
Notation lower := I.lower.
Notation upper := I.upper.
Notation diam I := (I.upper I - I.lower I).
Notation bounded := I.bounded.
Notation I0 := (I.fromZ 0).

Lemma Rabs_bnd a b c : (Rabs (a-b)) <= c -> (Rabs a <= ((Rabs b) + c)).
    move => H.
    suff : (Rabs a - Rabs b <= c) by lra.
    apply /Rle_trans.
    by apply Rabs_triang_inv.
    by [].
Qed.

Lemma Rabs_bnd' a b c : (Rabs (a-b)) <= c -> ( ((Rabs b) - c) <= (Rabs a)).
    move => H.
    suff : (Rabs b - Rabs a <= c) by lra.
    apply /Rle_trans.
    by apply Rabs_triang_inv.
    by rewrite Rabs_minus_sym.
Qed.

Lemma powerRZ_bound t :  exists K, (0 <= K)%Z /\ (Rabs t) <= (powerRZ 2 K).
  have [A _] := (archimed (Rabs t)).
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
    rewrite (Raux.IZR_Zpower SF2.radix); last by apply Z.log2_up_nonneg.
    by rewrite <- (Raux.bpow_powerRZ SF2.radix);lra.
Qed.

Lemma powerRZ2_bound x y : exists K, (1 <= K)%nat /\ ((Rabs x) <= (powerRZ 2 (Z.of_nat K))) /\ ((Rabs y) <= (powerRZ 2 (Z.of_nat K))).
Proof.
  case (powerRZ_bound x) => Ux [Uxge0 Uxp]; case (powerRZ_bound y) => Uy [Uyge0 Uyp].
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

Lemma powerRZ2_neg_pos n: powerRZ 2 (-Z.of_nat n) = /2^n.
Proof.
by rewrite powerRZ_neg; try lra; rewrite Interval_missing.pow_powerRZ powerRZ_inv.
Qed.

Lemma SF2_Z p: (1 < p)%Z -> (Z.pos (SF2.prec p))=p.
 move => pgt.
  - rewrite /SF2.prec/StdZRadix2.EtoZ.
    move : pgt.
    case M : p => [|p'|p']; try by lia.
Qed.

Definition nat2p n := SF2.PtoP (Pos.of_nat n).
Lemma nFnan eps: 0 < D2R eps -> ~ eps = Fnan.

Proof. by case: eps; first by rewrite /D2R/=; lra. Qed.
(* convert float to Xreal *)
Lemma D2R_SF2toX m e: SF2.toX (Float m e) = Xreal (D2R (Float m e)).
Proof.
rewrite /D2R/proj_val/=/SF2.toX/=/Interval_definitions.FtoX/=.
by case: StdZRadix2.mantissa_sign (Float m e) => //.
Qed.

(* convert float to real *)
Lemma D2R_Float (m e: Z):
  D2R (Float m e) = IZR m * powerRZ 2 e.
Proof.
rewrite /D2R /SF2.toX /SF2.toF/=.
case: (StdZRadix2.mantissa_sign m) (StdZRadix2.mantissa_sign_correct m);
  rewrite /StdZRadix2.MtoZ /=.
	by move => ->; lra.
  move => s p'.
  case s. 
  move => [-> p2].
  by rewrite Interval_definitions.FtoR_split /Defs.F2R Raux.bpow_powerRZ.
  move => [-> p2].
  by rewrite Interval_definitions.FtoR_split /Defs.F2R Raux.bpow_powerRZ.
Qed.

(* error bounds *)
Section Interval_error_bounds.

Lemma ID_bound_dist I x y : (bounded I) -> (x \contained_in I) -> (y \contained_in I) -> (Rabs (x-y)) <= (diam I).  
  case: I => //; case => //lIm lIe; case => //uIm uIe _.
  rewrite //=!D2R_SF2toX.  
  move => H1 H2.
  by apply Rcomplements.Rabs_le_between';lra.
Qed.

Lemma upper_lower_contained I : (bounded I)-> (not_empty (I.convert I))-> ((upper I) \contained_in I) /\ ((lower I) \contained_in I).
Proof.
  case: I => //; case => //lIm lIe; case => //uIm uIe BI ne.
  case ne => x xp.
  have u := (contains_upper (SF2.toX (Float lIm lIe)) (D2R (Float uIm uIe)) (Xreal x)).
  have l := (contains_lower (D2R (Float lIm lIe)) (SF2.toX (Float uIm uIe)) (Xreal x)).
  rewrite //= !D2R_SF2toX.
  rewrite //= !D2R_SF2toX in u,l,xp.
  by lra.
Qed.

Lemma non_empty_diam_pos I x: (bounded I) -> (x \contained_in I) -> (0 <= (upper I - lower I)).
Proof.
  move => H1 H2.
  have Rabs_0 : (Rabs (x-x)) = 0 by rewrite Rcomplements.Rminus_eq_0 Rabs_R0.
  rewrite <- Rabs_0.
  apply ID_bound_dist; by [].
Qed.

Lemma tpmn_bound n :  (/ 2 ^ n) <= 1.
Proof.
 rewrite Rinv_pow; last by lra.
 case (Nat.eq_0_gt_0_cases n) => H;first by rewrite H //=;lra.
 apply Rlt_le.
 by apply pow_lt_1_compat; by [lra|].
Qed.

Lemma ID_bound_simpl (I : ID) n x N : (N+1 <= (Z.of_nat n))%Z -> (bounded I) -> (diam I ) <= /2^n ->  x \contained_in I ->  (powerRZ 2 (-N)%Z) <= (Rabs x) ->  (powerRZ 2 (-(N+1))%Z) <= (Rabs (upper I))/\  (powerRZ 2 (-(N+1))%Z) <= (Rabs (lower I)).
  move => Ngt.
  move => BI DI xc LB.
  have ne : (not_empty (I.convert I)) by exists x.
  have [U L]  := (upper_lower_contained BI ne).
  have := (ID_bound_dist BI U xc).
  have := (ID_bound_dist BI L xc).
  move : U L BI DI xc LB ne.
  rewrite /upper/lower.
  case: I => //; case => //lIm lIe; case => //uIm uIe _ _ _ D _ xB _ lB uB.
  have lb' : (Rabs ((D2R (Float lIm lIe))-x)) <= (/ 2 ^ n) by lra.
  have ub' : (Rabs ((D2R (Float uIm uIe))-x)) <= (/ 2 ^ n) by lra.
  apply Rabs_bnd' in lb'.
  apply Rabs_bnd' in ub'.
  suff : (powerRZ 2 (- (N + 1))%Z) <= (Rabs x) - (/ 2 ^ n) by lra.  
  have helper1 : (/ 2 ^ n) <= (powerRZ 2 (- (N+1))).
  - rewrite <- powerRZ2_neg_pos, !powerRZ_Rpower; try by lra.
    apply Rle_Rpower; try by lra.
    by apply IZR_le;lia.
  suff : (powerRZ 2 (- (N + 1))%Z) + (powerRZ 2 (-(N+1))%Z)  = (powerRZ 2 (-N)%Z) by lra. 
  have -> : (- (N+1))%Z = (-N + -1)%Z by lia.
  rewrite powerRZ_add //=; by lra.
Qed.

Lemma ID_bound_simpl2 (I : ID) n x N : (0 <= N)%Z -> (bounded I) -> (diam I ) <= /2^n ->  x \contained_in I -> (Rabs x) <= (powerRZ 2 N) -> (Rabs (upper I)) <= (powerRZ 2 (N+1)) /\ (Rabs (lower I)) <= (powerRZ 2 (N+1)).

Proof.
  move => Ngt.
  move => BI DI xc LB.
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
  have helper1 : (/ 2 ^ n) <=(powerRZ 2 N).
  - apply /Rle_trans.
    apply tpmn_bound.
    rewrite powerRZ_Rpower; try by lra.
    rewrite <- (Rpower_O 2); try by lra.
    by apply (Rle_Rpower 2 0 (IZR N)); by [lra | apply IZR_le].
  by rewrite powerRZ_add /=;lra.
Qed.      

Lemma round_error : forall (mode: Interval_definitions.rounding_mode) x N p, (1 < p)%Z -> (Rabs x <= powerRZ 2 N) -> (Rabs ((Interval_definitions.round SF2.radix mode (SF2.prec p) x) - x)) <= (powerRZ 2 (N+1-p)%Z).
Proof.
  move => mode x N p [pgt B].
  have helper2 : (1 < (Z.pos (SF2.prec p)))%Z by rewrite SF2_Z.
  rewrite /Interval_definitions.round.
  apply /Rle_trans.
  apply Ulp.error_le_ulp; by [apply FLX.FLX_exp_valid; [] | apply Interval_definitions.valid_rnd_of_mode].
  apply /Rle_trans.
  apply FLX.ulp_FLX_le; by [].
  rewrite Raux.bpow_powerRZ //=.
  rewrite <- Z.pos_sub_opp, <-Z.add_sub_assoc, Z.pos_sub_gt, Pos2Z.inj_sub, Z.opp_sub_distr; try by [].
  rewrite Z.add_comm Z.add_opp_r.
  rewrite powerRZ_add;last by lra.
  rewrite SF2_Z; last by [].
  apply Rmult_le_compat_r; last by [].
  by apply powerRZ_le; lra.
Qed.
End Interval_error_bounds.

Section addition.
Lemma add_correct_R prec x y I J:
	x \contained_in I -> y \contained_in J -> (x + y) \contained_in (I.add prec I J).
Proof.
intros.
replace (Xreal (x + y)) with (Xadd (Xreal x) (Xreal y)) by trivial.
by apply I.add_correct.
Qed.

Lemma SF2_add_correct: forall (mode: Interval_definitions.rounding_mode) (p: xpnt) (e e':xpnt) (m m':mant),
    D2R (SF2.add mode p (Float m e) (Float m' e')) = Interval_definitions.round SF2.radix mode (SF2.prec p) (D2R (Float m e) + (D2R (Float m' e'))).
Proof.
move => mode p e e' m m'.
have := SF2.add_correct mode p (Float m e) (Float m' e').
rewrite !D2R_SF2toX.
rewrite /Xadd/Interval_definitions.Xround/Xbind/SF2.toX.
rewrite /Interval_definitions.FtoX.
by case E: (SF2.toF (SF2.add mode p (Float m e) (Float m' e'))) => //; move =>  [<-]; rewrite /D2R/proj_val/SF2.toX/Interval_definitions.FtoX E.
Qed.

Lemma add_error I J n m p x y N:
  (1 < p)%Z ->
  (0 <= N)%Z ->
  bounded I -> diam I <= /2^n -> bounded J -> diam J <= /2^m ->
  (x \contained_in I) ->
  (y \contained_in J) ->
  (Rabs x) <=  (powerRZ 2 N) -> (Rabs y) <= (powerRZ 2 N) ->
  bounded (I.add p I J)
  /\
  diam (I.add p I J) <= /2 ^ n + /2 ^ m + (powerRZ 2 (N+4-p)%Z).
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
  - rewrite /I.add /bounded !SF2.real_correct !SF2.add_correct.
    rewrite /Xadd.
    by rewrite !D2R_SF2toX.
  rewrite /I.add.
  rewrite !SF2_add_correct.
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
  have t1 :  (Interval_definitions.round SF2.radix Interval_definitions.rnd_UP (SF2.prec p) ((D2R (Float uIm uIe))+(D2R (Float uJm uJe)))) <= ((D2R (Float uIm uIe))+(D2R (Float uJm uJe)))+(powerRZ 2 ((N+3-p)%Z)).
  -  
    apply (Rcomplements.Rabs_le_between').
    apply /Rle_trans.
    apply (round_error _ pgt BP1).
    suff : ((N + 2 + 1 -p)%Z = (N + 3 - p))%Z by move => ->;apply Req_le.
    by lia.
  have t2 :   ((D2R (Float lIm lIe))+(D2R (Float lJm lJe))) <= (Interval_definitions.round SF2.radix Interval_definitions.rnd_DN (SF2.prec p) ((D2R (Float lIm lIe))+(D2R (Float lJm lJe))))+ (powerRZ 2 ((N+3-p)%Z)).
  - apply (Rcomplements.Rabs_le_between').
    rewrite Rabs_minus_sym.
    apply /Rle_trans.
    apply (round_error _ pgt BP2); try by [].
    suff : ((N + 2 + 1 -p) = (N + 3 - p))%Z by move => ->;apply Req_le.
    by lia.
  rewrite Rcomplements.Rle_minus_l.
  apply /Rle_trans.
  apply t1.
  have pwr : (powerRZ 2 (N+4 - p)) = (2*powerRZ 2 (N+3- p)) by rewrite !(powerRZ_add);try by simpl;lra.
  rewrite pwr.
  suff :  (D2R (Float uIm uIe)) + (D2R (Float uJm uJe)) - (/ 2 ^ n) - (/ 2 ^ m) <= (Interval_definitions.round SF2.radix Interval_definitions.rnd_DN (SF2.prec p) ((D2R (Float lIm lIe)) + (D2R (Float lJm lJe)))) + (powerRZ 2 (N + 3 - p)%Z) by lra.
  have T:= (Rle_trans ((D2R (Float uIm uIe)) + (D2R (Float uJm uJe)) - (/ 2 ^ n) - (/ 2 ^ m))  _ _ _ t2).
  by apply T; lra.
Qed.
End addition.

Section multiplication.
Lemma mul_correct_R prec x y I J:
	x \contained_in I -> y \contained_in J -> (x * y) \contained_in (I.mul prec I J).
Proof.
intros.
replace (Xreal (x * y)) with (Xmul (Xreal x) (Xreal y)) by trivial.
by apply I.mul_correct.
Qed.

Lemma mul_float m1 e1 m2 e2 : (D2R (Float m1 e1)*(D2R (Float m2 e2))) = (D2R (Float (m1*m2)%Z (e1+e2)%Z)).
Proof.
  rewrite !D2R_Float.
  have comm u v w t : u*v*(w*t) = (u*w*(v*t)) by lra.
  rewrite comm.
  rewrite <- powerRZ_add; try by [].
  by rewrite  <- mult_IZR.
Qed.

Lemma round_error_mul p rnd x y M: (1 < p)%Z -> (Rabs x) <= (powerRZ 2 M) -> (Rabs y) <= (powerRZ 2 M) -> x*y - (powerRZ 2 (2*M+1-p)%Z) <= (Interval_definitions.round SF2.radix rnd (SF2.prec p) (x*y)) <= x*y + (powerRZ 2 (2*M+1-p)%Z).
Proof.
  move => pgt H1 H2.
  have lt : (Rabs (x*y)) <= (powerRZ 2 (2*M)).
  - rewrite Rabs_mult.
    rewrite <-Z.add_diag, powerRZ_add; last by lra.
    by apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | |].
  apply Rcomplements.Rabs_le_between'.
  apply round_error; by [].
Qed.

Lemma powerRZ_sub_helper u v N p : (u + (powerRZ 2 (2*(N+1)+1-p))%Z)-(v - (powerRZ 2 (2*(N+1)+1-p)%Z)) = (u - v)+(powerRZ 2 (2*N+4-p)%Z).
Proof.
   suff :  (powerRZ 2 1)*(powerRZ 2 (2 * (N + 1) + 1 - p)%Z)  =  (powerRZ 2 (2*N + 4 - p)%Z) by simpl;lra.
 rewrite <- powerRZ_add; try by lra.
  suff H0 :((1 + (2 * (N + 1) + 1 - p)%Z) =  (2 * N + 4 - p))%Z by rewrite H0.
  by lia.
Qed. 

Lemma mul_sub_err u u' v v' n1 n2: (Rabs (u-u')) <= (/ 2 ^ n1) -> (Rabs (v - v')) <= (/2 ^ n2) -> (Rabs (u*v-u'*v')) <= (Rabs v)*(/2 ^ n1) + (Rabs u')*(/2 ^ n2).
Proof.
  move => H1 H2.
  have s : (u*v - u'*v') = v*(u-u') + u'*(v-v') by lra.
  rewrite s.
  apply /Rle_trans.
  apply Rabs_triang.
  rewrite !Rabs_mult.
  apply Rplus_le_compat.
  - by apply Rmult_le_compat_l; [apply Rabs_pos | apply H1].
  by apply Rmult_le_compat_l; [apply Rabs_pos | apply H2].
Qed.

Lemma mul_sub_err' u u' v v' n1 n2 M: (Rabs (u-u')) <= (/ 2 ^ n1) -> (Rabs (v - v')) <= (/2 ^ n2) -> (Rabs v) <= (powerRZ 2 M) -> (Rabs u') <= (powerRZ 2 M) -> (Rabs (u*v-u'*v')) <= (powerRZ 2 (M-(Z.of_nat n1))) + (powerRZ 2 (M-(Z.of_nat n2))).
Proof.
  move => H1 H2 H3 H4.
  apply /Rle_trans.
  apply (@mul_sub_err _ _ _ _ n1 n2); try by [].
  rewrite !powerRZ_add;try by lra.
  rewrite !powerRZ2_neg_pos.
  apply Rplus_le_compat; by apply Rmult_le_compat_r; [apply tpmn_pos | ].
Qed.

Lemma mul_error I J n m p x y N:
  (1 < p)%Z ->
  (0 <= N)%Z ->
  bounded I -> diam I <= /2^n -> bounded J -> diam J <= /2^m ->
  (x \contained_in I) ->
  (y \contained_in J) ->
  (Rabs x) <=  (powerRZ 2 N) -> (Rabs y) <= (powerRZ 2 N) ->
  bounded (I.mul p I J)
  /\
  diam (I.mul p I J) <= (powerRZ 2 (N+1-(Z.of_nat n)))+ (powerRZ 2 (N+1-(Z.of_nat m))) + (powerRZ 2 (2*N+4-p)%Z).
Proof.
  move => pgt Ngt.
  move => BI DI BJ DJ xc yc Bx By.
  have [B1 B2] := (ID_bound_simpl2 Ngt BI DI xc Bx). 
  have [B1' B2'] := (ID_bound_simpl2 Ngt BJ DJ yc By). 
  have [diam_abs_diamI diam_abs_diamJ] : (diam I) = (Rabs (diam I)) /\ (diam J) = (Rabs (diam J)).
  - rewrite !Rabs_right; by [|  apply Rle_ge; apply (non_empty_diam_pos BJ yc)| apply Rle_ge; apply (non_empty_diam_pos BI xc)].
  move : BI DI BJ DJ xc yc Bx By B1 B2 B1' B2' diam_abs_diamJ diam_abs_diamI.
  have sub_simplification a b a' b': (a <= a') -> (b' <= b) -> (a-b <= a' - b') by lra.
  have round_sub_simplification M rnd rnd' m1 m2 m3 m4 e1 e2 e3 e4: ((Rabs (D2R (Float m1 e1))) <= (powerRZ 2 M)) -> ((Rabs (D2R (Float m2 e2))) <= (powerRZ 2 M)) -> ((Rabs (D2R (Float m3 e3))) <= (powerRZ 2 M)) -> ((Rabs (D2R (Float m4 e4))) <= (powerRZ 2 M)) -> (SF2.mul rnd p (Float m1 e1) (Float m2 e2)) - (SF2.mul rnd' p (Float m3 e3) (Float m4 e4)) <= (D2R (Float m1 e1))*(D2R (Float m2 e2)) + (powerRZ 2 (2*M+1-p)%Z) - ((D2R (Float m3 e3))*(D2R (Float m4 e4)) - (powerRZ 2 (2*M+1-p)%Z)).
  - move => B1 B2 B3 B4.
    rewrite /D2R !SF2.mul_correct /Xmul !D2R_SF2toX //=.
     by apply sub_simplification;apply round_error_mul; try by [].
  rewrite /upper/lower.
  case: I => //; case => //lIm lIe; case => //uIm uIe  _ ineq; rewrite /= in ineq.
  case: J => //; case => //lJm lJe; case => //uJm uJe _ ineq'  _ _  P1 P2 BIu BIl BJu BJl diam_absJ diam_absI; rewrite /= in ineq'.
  split.
  - rewrite /bounded /I.mul.
    case : (I.sign_large_ (Float lIm lIe) (Float uIm uIe));case : (I.sign_large_ (Float lJm lJe) (Float uJm uJe)); try by []; try by rewrite /I.mul !SF2.real_correct !SF2.mul_correct !D2R_SF2toX /Xmul //=.
    rewrite !SF2.real_correct !SF2.max_correct !SF2.min_correct !SF2.mul_correct /Xmul.
    by rewrite /Xmin /Xmax !D2R_SF2toX /I.mul //=.
  rewrite /I.mul.
  have helper u v u' v' := (powerRZ_sub_helper (u*v) (u'*v') N p).
  rewrite diam_absI in ineq.
  rewrite diam_absJ in ineq'.
    have ineq_rev := ineq.
    have ineq'_rev := ineq'.
    have ineq_triv z k: (Rabs (z - z) <= / 2 ^ k) by rewrite Rcomplements.Rminus_eq_0 Rabs_R0;apply tpmn_pos.
    rewrite Rabs_minus_sym in ineq_rev.
    rewrite Rabs_minus_sym in ineq'_rev.

    have case_helper rnd rnd' m1 e1 m2 e2 m1' e1' m2' e2' : (Rabs (D2R (Float m1 e1))) <= (powerRZ 2 (N+1)) -> (Rabs (D2R (Float m1' e1'))) <= (powerRZ 2 (N+1)) -> (Rabs (D2R (Float m2 e2))) <= (powerRZ 2 (N+1)) -> (Rabs (D2R (Float m2' e2'))) <= (powerRZ 2 (N+1)) ->  (Rabs ((D2R (Float m1 e1)) - (D2R (Float m1' e1')))) <= / 2 ^ n -> (Rabs ((D2R (Float m2 e2)) - (D2R (Float m2' e2')))) <= / 2 ^ m -> (SF2.mul rnd p (Float m1 e1) (Float m2 e2)) - (SF2.mul  rnd' p (Float m1' e1') (Float m2' e2')) <= (powerRZ 2 (N+1-(Z.of_nat n)))+(powerRZ 2 (N+1-(Z.of_nat m)))+(powerRZ 2 (2*N + 4 - p)%Z).
    move => H1 H2 H3 H4 H5 H6.
    apply /Rle_trans.
    apply (round_sub_simplification (N+1)%Z); try by [].
    rewrite helper.
    apply Rplus_le_compat_r.
    apply /Rle_trans.
    apply Rle_abs.
    by apply mul_sub_err'; by [].
  have case_helper2 : (D2R (SF2.zero) - (D2R SF2.zero)) <=
  powerRZ 2 (N + 1 - Z.of_nat n) + powerRZ 2 (N + 1 - Z.of_nat m) +
  powerRZ 2 (2 * N + 4 - p)%Z.
  - rewrite /D2R SF2.zero_correct Rminus_0_r //=.
    apply Rplus_le_le_0_compat; [apply Rplus_le_le_0_compat |]; by apply powerRZ_le;lra.
  case : (I.sign_large_ (Float lIm lIe) (Float uIm uIe));case : (I.sign_large_ (Float lJm lJe) (Float uJm uJe)); try by (try apply case_helper2; try by (apply case_helper; by [])).
  have := (case_helper Interval_definitions.rnd_UP Interval_definitions.rnd_DN lIm lIe lJm lJe lIm lIe uJm uJe).
  have := (case_helper Interval_definitions.rnd_UP Interval_definitions.rnd_DN lIm lIe lJm lJe uIm uIe lJm lJe).
  have := (case_helper Interval_definitions.rnd_UP Interval_definitions.rnd_DN uIm uIe uJm uJe lIm lIe uJm uJe).
  have := (case_helper Interval_definitions.rnd_UP Interval_definitions.rnd_DN uIm uIe uJm uJe uIm uIe lJm lJe).
  rewrite /D2R !SF2.max_correct !SF2.min_correct /Xmin /Xmax !SF2.mul_correct /Xmul !D2R_SF2toX //=.
    apply Rmax_case;apply Rmin_case; by auto.
Qed.
End multiplication.
Section division.
Lemma powerRZ_lt_neq0 y M: (powerRZ 2 M) <= (Rabs y) -> (y <> 0). 
Proof.
  split_Rabs.
  - suff : (0 < -y) by lra.
    apply /Rlt_le_trans.
    apply (powerRZ_lt 2 M); lra.
    by apply H.
  - suff : (0 < y) by lra.
    apply /Rlt_le_trans.
    apply (powerRZ_lt 2 M); by lra.
    by apply H.
Qed.

Lemma div_correct_R prec x y I J:
	(y <> 0) -> x \contained_in I -> y \contained_in J -> (x / y) \contained_in (I.div prec I J).
Proof.
intros.
  have neq0 : (is_zero y) = false by apply Raux.Req_bool_false.
  replace (Xreal (x / y)) with (Xdiv (Xreal x) (Xreal y)); last by rewrite /Xdiv/Xdiv' neq0.
  by apply I.div_correct.
Qed.

Lemma div_bound x y M : (Rabs x) <= (powerRZ 2 M) ->  (powerRZ 2 (-M)%Z) <= (Rabs y) -> ((Rabs (x/y)) <= (powerRZ 2 (2*M))).
Proof.
  move => H1 H2.
  rewrite Rabs_mult.
  rewrite <-Z.add_diag, powerRZ_add; last by lra.
  suff H0 : (Rabs (/ y) <= (powerRZ 2 M)) by apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | |].
  rewrite Rabs_Rinv; last by apply (powerRZ_lt_neq0 H2).
  rewrite powerRZ_Rpower; try by lra.
  have -> : (IZR M) = (- (IZR (- M))) by rewrite opp_IZR;lra.
  rewrite Rpower_Ropp.
  rewrite <- powerRZ_Rpower.
  apply Raux.Rinv_le; by [(apply powerRZ_lt;lra) | apply H2 ].
  by lra.
Qed.
Lemma dist_lower_bound v v'  M : (powerRZ 2 (-M)%Z) <= (Rabs v) -> (Rabs (v - v')) <= (powerRZ 2 (-(M+1))%Z) ->  (powerRZ 2 (-(M+1))%Z) <= (Rabs v').
Proof.
  move => H1 H2.
  have pwrRZ2_minus : (powerRZ 2 (- (M + 1))%Z) = (powerRZ 2 (- M)%Z) - (powerRZ 2 (- (M + 1))). 
  - suff : (powerRZ 2 (- (M + 1))%Z) + (powerRZ 2 (- (M + 1)))= (powerRZ 2 (- M)%Z) by lra.
    ring_simplify.
    have {1}-> : 2 = (powerRZ 2 1%Z) by simpl;lra.
    rewrite <- powerRZ_add; last by lra.
    by have -> : (1 + - (M +1) = (-M))%Z by lia.
  rewrite pwrRZ2_minus.
  apply /Rle_trans.
  apply Rplus_le_compat.
  apply H1.
  apply Ropp_le_contravar.
  apply H2.
  apply /Rle_trans.
  apply Rabs_triang_inv.
  have -> : (v - (v - v')) = v' by lra.
  by lra.
Qed.

Lemma inv_prod_bound v v' M : (powerRZ 2 (-M)%Z) <= (Rabs v) -> (Rabs (v - v')) <= (powerRZ 2 (-(M+1))%Z) -> (Rabs (/(v'*v))) <= (powerRZ 2 (2*M + 1)%Z).
Proof.
  move => H1 H2.
  have v'bound := (dist_lower_bound H1 H2).
  rewrite Rabs_Rinv; last by apply Rmult_integral_contrapositive_currified; [apply (powerRZ_lt_neq0 v'bound) | apply (powerRZ_lt_neq0 H1)].
  have -> : (2*M + 1 = ((- (- 2*M - 1))))%Z by lia.
  rewrite powerRZ_neg; last by lra.
  rewrite powerRZ_inv; last by lra.
  apply Raux.Rinv_le; first by apply powerRZ_lt;lra.
  rewrite Rabs_mult.
  have -> : (powerRZ 2 (-2 *M - 1)) = (powerRZ 2 (- (M + 1)))*(powerRZ 2 (- M)).
  - rewrite <- powerRZ_add; last by lra.
    by have -> : ((-2*M -1) = (- (M+1) + - M))%Z by lia.
  apply Rmult_le_compat; try by apply powerRZ_le; lra.
  by apply v'bound.
  by apply H1.
Qed.

Lemma inv_dist_bound v v' M n :   (M+1 <= (Z.of_nat n))%Z -> (powerRZ 2 (-M)%Z) <= (Rabs v) -> (Rabs (v - v')) <= (/ 2 ^ n) -> (Rabs (/v' - /v)) <= (powerRZ 2 (2*M + 1 - (Z.of_nat n))%Z).
Proof.
  rewrite <- powerRZ2_neg_pos.
  move => H1 H2 H3.
  have B1 : (Rabs (v - v')) <= (powerRZ 2 (-(M+1))%Z).
  - apply /Rle_trans.
    apply H3.
    rewrite !powerRZ_Rpower; try by lra.
    apply Rle_Rpower; first by lra.
    by apply IZR_le;lia.
  have v'bound := (dist_lower_bound H2 B1).
  have neq0 : (v <> 0 /\ v' <> 0) by split; [  apply (powerRZ_lt_neq0 H2) | apply (powerRZ_lt_neq0 v'bound)].
  have -> : (/v' - /v) =  ((v - v')/(v'*v)) by field_simplify; try by lra.
  rewrite Rabs_mult.
  rewrite powerRZ_add; last by lra.
  rewrite Rmult_comm.
  apply Rmult_le_compat; try by apply Rabs_pos.
  - by apply inv_prod_bound.
  apply H3. 
Qed.

Lemma div_sub_err' u u' v v' n1 n2 M: (M+1 <= (Z.of_nat n2))%Z -> (Rabs (u-u')) <= (/ 2 ^ n1) -> (Rabs (v - v')) <= (/2 ^ n2) ->  (powerRZ 2 (-M)) <= (Rabs v) -> (Rabs u') <= (powerRZ 2 M) -> (Rabs ((u/v)-(u'/v'))) <= (powerRZ 2 (M-(Z.of_nat n1))) + (powerRZ 2 (3*M+1-(Z.of_nat n2))).
Proof.
  move => Mb H1 H2 H3 H4.
  rewrite /Rdiv.
  have vb : (Rabs (/ v) <= (powerRZ 2 M)).
  - rewrite Rabs_Rinv; last by apply (powerRZ_lt_neq0 H3).
    have -> :(M = (- (- M)))%Z by lia.
    rewrite powerRZ_neg; last by lra.
    rewrite powerRZ_inv;last by lra.
    apply Raux.Rinv_le; try by lra.
    by apply powerRZ_lt; last by lra.
  have -> : (u/v - u'/v') = (u-u')*/v + u'*(/v-/v') by lra.
  apply /Rle_trans.
  apply Rabs_triang.
  rewrite !Rabs_mult.
  have -> : (3*M+1 - (Z.of_nat n2) = (2*M+1 - (Z.of_nat n2) + M))%Z by lia.
  apply Rplus_le_compat; rewrite powerRZ_add; try by lra.
  - rewrite Rmult_comm; apply Rmult_le_compat; try by apply Rabs_pos. 
    apply vb.  
    by rewrite powerRZ2_neg_pos.
 rewrite Rmult_comm; apply Rmult_le_compat; try by apply Rabs_pos.
 - rewrite Rabs_minus_sym; apply inv_dist_bound; by auto.
 by apply H4.
Qed.    

Lemma round_error_div p rnd x y M: (1 < p)%Z -> (Rabs x) <= (powerRZ 2 M) ->  (powerRZ 2 (-M)%Z) <= (Rabs y) -> x/y - (powerRZ 2 (2*M+1-p)%Z) <= (Interval_definitions.round SF2.radix rnd (SF2.prec p) (x/y)) <= x/y + (powerRZ 2 (2*M+1-p)%Z).
Proof.
  move => pgt H1 H2.
  apply Rcomplements.Rabs_le_between'.
  apply round_error; by [| apply div_bound].
Qed.

Lemma div_error I J n m p x y N:
  (1 < p)%Z ->
  (0 <= N)%Z ->
  (N+2 <= (Z.of_nat m))%Z ->
  bounded I -> diam I <= /2^n -> bounded J -> diam J <= /2^m ->
  (x \contained_in I) ->
  (y \contained_in J) ->
  (Rabs x) <=  (powerRZ 2 N) ->  (powerRZ 2 (- N)) <= (Rabs y) ->
  bounded (I.div p I J)
  /\
  diam (I.div p I J) <= (powerRZ 2 (N+1-(Z.of_nat n)))+ (powerRZ 2 (3*N+4-(Z.of_nat m))) + (powerRZ 2 (2*N+4-p)%Z).
Proof.
  move => pgt Nle Ngt H3 H4 H5 H6 H7 H8 H10 H11.
  have yneq0 := (powerRZ_lt_neq0 H11).
  have [diam_abs_diamI diam_abs_diamJ] : (diam I) = (Rabs (diam I)) /\ (diam J) = (Rabs (diam J)).
  - rewrite !Rabs_right; by [|  apply Rle_ge; apply (non_empty_diam_pos H5 H8)| apply Rle_ge; apply (non_empty_diam_pos H3 H7)].
  move : diam_abs_diamI H3 H4 H5 diam_abs_diamJ  H6 H7 H8 H10 H11.
  case: I => //; case => //lIm lIe; case => //uIm uIe diam_abs_diamI  BI ineq; rewrite /= in ineq.
  case: J => //; case => //lJm lJe; case => //uJm uJe BJ diam_abs_diamJ ineq'  xcont ycont P1 P2; rewrite /= in ineq'.
  have Ngt' : (N+1 <= (Z.of_nat m))%Z by lia.
  set lJ := (Float lJm lJe).
  set uJ := (Float uJm uJe).
  set lI := (Float lIm lIe).
  set uI := (Float uIm uIe).
  have notcont0: (not 0 \contained_in (I.bnd (Float lJm lJe) (Float uJm uJe))).
  - move => cnt0.
    have [e1 e2] := (contains_le _ _ _ cnt0 ).
    rewrite /le_lower/le_upper !D2R_SF2toX /Xneg in e1 e2.
    have [bnd1 bnd2] := (ID_bound_simpl Ngt' BJ ineq' ycont P2).    
    apply Raux.Rabs_ge_inv in bnd2.
    case : bnd2 => b.
    + apply Rlt_not_le in e2.
      apply e2.
      apply Rcomplements.Rle_minus_l in ineq'.
      apply /Rle_lt_trans.
      apply ineq'.
      suff : (D2R (Float lJm lJe))  < - (/ 2 ^ m)  by lra.
      suff b' : (/ 2 ^ m) < (powerRZ 2 (- (N+1))) by apply (Rle_lt_trans _ _ _ b);lra.
      rewrite <- powerRZ2_neg_pos.
      rewrite !powerRZ_Rpower;try by lra.
      apply Rpower_lt; try by lra.
      by apply IZR_lt;lia.
    apply Rlt_not_le in e1.
    apply e1.
    apply Ropp_lt_contravar.
    apply /Rlt_le_trans.
    apply (powerRZ_lt 2 (- (N + 1))); try by lra.
    by apply b.
  have [lneq0 uneq0] : (is_zero (D2R lJ)) = false /\ (is_zero (D2R uJ)) = false.
  - have C := (upper_lower_contained BJ).
    split; apply Raux.Req_bool_false => H; apply notcont0; rewrite <- H; apply C; by exists y.
  split.
  - rewrite /bounded /I.div/I.Fdivz.
    have := (I.sign_strict_correct_ _ _ _ ycont).
    case : (I.sign_strict_ lJ uJ); try by lra.
    case : (I.sign_strict_ lI uI); try by []; move => [ylt _]; try rewrite !SF2.real_correct; try rewrite !SF2.div_correct; try rewrite  !D2R_SF2toX /Xdiv' //=; try rewrite lneq0; try rewrite uneq0; try by [].
    + by case : (I.sign_strict_ lI uI); try rewrite !SF2.real_correct;try rewrite !SF2.div_correct;try rewrite  !D2R_SF2toX /Xdiv' //=;try rewrite lneq0; try rewrite uneq0; try by [].
    case : (I.sign_strict_ lI uI);try rewrite  !D2R_SF2toX; apply or_to_imply;apply or_introl => H;apply notcont0;apply le_contains; rewrite !D2R_SF2toX /le_lower/le_upper //=;by lra.
  rewrite /I.div.
  have [B1 B2] := (ID_bound_simpl2 Nle BI  ineq xcont P1 ).
  have [B1' B2'] := (ID_bound_simpl Ngt' BJ  ineq' ycont P2 ). 
  rewrite diam_abs_diamI in ineq.
  rewrite diam_abs_diamJ in ineq'.
  rewrite /upper/lower/I.Fdivz.
  rewrite !SF2.real_correct !D2R_SF2toX /D2R.
  have case_helper rnd rnd' x1 x2 y1 y2: (x1 = lI /\ x2 = uI \/ x1 = uI /\ x2 = lI ) -> (y1 = lJ \/ y1 = uJ) -> (y2 = lJ \/ y2 = uJ) -> (proj_val (SF2.toX (SF2.div rnd p x1 y2))) - proj_val (SF2.toX (SF2.div rnd' p x2 y1)) <=  powerRZ 2 (N + 1 - Z.of_nat n) + powerRZ 2 (3 * N + 4 - Z.of_nat m) +
  powerRZ 2 (2 * N + 4 - p).
  - move => H1 H2 H3.
    have : ((is_zero (D2R y1)) = false) /\ (is_zero (D2R y2) = false).
    + case H2 => H11; case H3 => H12; rewrite H11 H12; split; try by auto.
    have : exists m1 e1 m2 e2, (x1 = (Float m1 e1)) /\ (x2 = (Float m2 e2)). 
    + case H1;move => [H11 H12];[exists lIm; exists lIe; exists uIm; exists uIe | exists uIm; exists uIe; exists lIm; exists lIe]; by rewrite H11 H12.
    have : exists m1 e1 m2 e2, (y1 = (Float m1 e1)) /\ (y2 = (Float m2 e2)). 
    + case H2 => H11; [exists lJm; exists lJe | exists uJm; exists uJe].
      case H3 => H12; [exists lJm; exists lJe | exists uJm; exists uJe]; by rewrite H11 H12.
      case H3 => H12; [exists lJm; exists lJe | exists uJm; exists uJe]; by rewrite H11 H12.
    case => m1; case => e1; case => m2; case => e2 [ep1 ep2].
    case => m1'; case => e1'; case => m2'; case => e2' [ep1' ep2'].
    rewrite ep1 ep2 ep1' ep2'.
    move => [nz0 nz1].
    rewrite !SF2.div_correct/Interval_definitions.Xround /Xdiv/Xdiv' !D2R_SF2toX nz0 nz1.
    rewrite <-ep1, <-ep2, <-ep1',<-ep2'.
    have [b1 b2] : (Rabs (D2R x1)) <= (powerRZ 2 (N+1)) /\ (Rabs (D2R x2)) <= (powerRZ 2 (N+1)).
    + case H1; move => [H11 H12]; rewrite H11 H12; by auto.
    have [b1' b2'] :(powerRZ 2 (-(N+1))%Z) <= (Rabs (D2R y1)) /\ (powerRZ 2 (-(N+1))%Z) <= (Rabs (D2R y2)).
    + case H2=> H11; case H3 => H12; rewrite H11 H12; by auto.
    have ineq1 : (Rabs ((D2R x1) - (D2R x2))) <= (/ 2 ^ n).
    + case H1; move => [H11 H12]; rewrite H11 H12; try by [rewrite Rabs_minus_sym |].
    have ineq2 : (Rabs ((D2R y2) - (D2R y1))) <= (/ 2 ^ m).
    + case H2 => H11; case H3 => H12; rewrite H11 H12; try by rewrite Rcomplements.Rminus_eq_0 Rabs_R0;apply tpmn_pos.
      by auto.
      by rewrite Rabs_minus_sym.
    have r1  := (round_error_div  _ pgt b1 b2').
    have r2  := (round_error_div _  pgt b2 b1').
    have sub_simplification a b a' b': (a <= a') -> (b' <= b) -> (a-b <= a' - b') by lra.
    apply /Rle_trans.
    apply sub_simplification.
    apply r1 .
    apply r2.
    have -> :((2*N + 4 - p) = ((2*(N+1)+1-p)+1))%Z by lia.
    rewrite powerRZ_add //=.
    apply ->Rcomplements.Rle_minus_l.
    ring_simplify.
    rewrite Rabs_minus_sym in ineq.
    have t : ((N+1)+1 <= (Z.of_nat m))%Z by lia.
    have -> : ((3*N+4) = (3*(N+1)+1))%Z by lia.
    apply /Rle_trans.
    apply Rle_abs.
    apply div_sub_err'; try by auto.
  have case_helper2 a b c: (0 <= (powerRZ 2 a) + (powerRZ 2 b) + (powerRZ 2 c)).
  - suff : (0 <= (powerRZ 2 a)) /\ (0 <= (powerRZ 2 b)) /\ (0 <= (powerRZ 2 c)) by lra.
    by split; [|split]; try by apply powerRZ_le; lra.
  by case : (I.sign_strict_ lI uI);case : (I.sign_strict_ lJ uJ);(try rewrite //= Rcomplements.Rminus_eq_0; try apply case_helper2); (try apply case_helper; auto).
Qed.

End division.
