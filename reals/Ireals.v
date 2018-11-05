From mathcomp Require Import all_ssreflect.
Require Import all_cs_base classical_mach reals.
Require Import Reals Psatz FunctionalExtensionality ClassicalChoice.
From Interval Require Import Interval_specific_ops Interval_bigint_carrier.
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
Module I := FloatIntervalFull SFBI2.

Notation D:= SFBI2.type.
Notation mant := BigIntRadix2.smantissa_type.
Notation xpnt := BigIntRadix2.exponent_type.
Notation ID := (Interval_interval_float.f_interval SFBI2.type).
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
	forall n, exists N, forall k, (N <= k)%nat -> bounded (I k) /\ diam (I k) <= /2 ^ n).

Lemma D2R_SFBI2toX m e:
	SFBI2.toX (Float m e) = Xreal (D2R (Float m e)).
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

Definition IR_interview_mixin : interview_mixin.type (nat -> ID) R.
Proof. exists rep_R; exact/rep_R_sur. Defined.

Definition IR_interview := interview.Pack IR_interview_mixin.

Lemma Float_to_R m e:
	D2R (Float (BigZ.of_Z m) (BigZ.of_Z e)) = IZR m * powerRZ 2 e.
Proof. by rewrite D2R_Float !BigZ.spec_of_Z. Qed.

Lemma nFnan eps: 0 < D2R eps -> ~ eps = Fnan.
Proof. by case: eps; first by rewrite /D2R/=; lra. Qed.

Lemma rep_R_sing: rep_R \is_singlevalued.
Proof.
move => In x x' [xeIn convIn] [x'eIn _].
apply cond_eq => e eg0.
have [n [_ ineq]]:= accf_2pown eg0.
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

Definition IR_dictionary_mixin: dictionary_mixin.type IR_interview.
Proof. split; exact/rep_R_sing. Qed.

Definition IR := dictionary.Pack IR_dictionary_mixin.

Lemma Intervals_countable: ID \is_countable.
Proof.
Admitted.

Canonical IR_cs := cs.Pack
	0%nat
	I0
	nat_count
	Intervals_countable
	IR.

Definition nat2p n := SFBI2.PtoP (Pos.of_nat n).
Lemma add_error I J n m p:
	bounded I -> diam I <= /2^n -> bounded J -> diam J <= /2^m ->
		diam (I.add (nat2p p) I J) <= /2 ^ n + /2 ^ m + /2 ^ p.
Proof.
Admitted.

Definition Rplus_frlzr (phi: names (cs_prod IR_cs IR_cs)) (n: questions IR_cs):=
	I.add (nat2p n) (lprj phi n) (rprj phi n).

Definition Rplus_rlzr := F2MF Rplus_frlzr.

Lemma Rplus_rlzr_spec : Rplus_rlzr \realizes (F2MF (fun xy => Rplus xy.1 xy.2): IR_cs \*_cs IR_cs ->> IR_cs).
Proof.
rewrite F2MF_rlzr_F2MF => phi [x y] [/=[xephin convx] [yephin convy]].
split => n; first by apply/add_correct_R; [apply xephin | apply yephin].
have [N Nprp]:= convx n.+2.
have [M Mprp]:= convy n.+2.
exists (maxn n.+1 (maxn M N)) => k ineq.
have [ | bndl dml]:= Nprp k.
	apply/leq_trans; first exact: (leq_maxr M N).
	by apply/leq_trans; first exact: (leq_maxr n.+1 (maxn M N)).
have [ | bndr dmr]:= Mprp k.
	apply/leq_trans; first exact: (leq_maxl M N).
	by apply/leq_trans; first exact: (leq_maxr n.+1 (maxn M N)).
rewrite /Rplus_rlzr; split.
	admit.
have npg0: 0 < 2 ^ n.+1.
	admit.
have /=exp: /2 ^ k <= /2 * /2 ^ n.
	admit.
apply /Rle_trans; first by apply (@add_error (lprj phi k) (rprj phi k) n.+2 n.+2 k).
have ng0: 0 < 2^n by apply pow_lt; lra.
by rewrite /= !Rinv_mult_distr; try lra.
Admitted.