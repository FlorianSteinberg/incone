From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_rlzrs.
From metric Require Import reals.
Require Import all_cs_base classical_mach.
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
Print word.
Print zn2z.
Print BigN.dom_t.
Compute (word BigN.w6 2).
Check BigN.mk_t.
Compute (((WW (WW (WW (phi_inv 2) (phi_inv 2)) W0) (WW W0 W0)))).
Compute (BigN.mk_t 0 ((phi_inv 2))).
Compute (BigN.mk_t 1 (WW (phi_inv 0) (phi_inv 2))).
Compute (BigN.mk_t 2 ((WW W0 ( WW (phi_inv 0) (phi_inv 2))))).

Lemma bigN_dom : forall n, (BigN.dom_t n.+1) = (zn2z (BigN.dom_t n)).
Proof.
elim.
done.
move => n H.
simpl.
case n; first by [].
do 5! (case; try by []).
Qed.
Search _ BigN.dom_t.
Check BigN.succ_t.

Search _ countable.
Locate prod_count.
Definition join_t (n : nat) (t1 t2 : (BigN.dom_t n)) : ((BigN.dom_t n.+1)) := (BigN.succ_t n (WW t1 t2)).
Search _ nat_countType.
Search _ Countable.sort.
Search _ (nat -> Z).
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
Compute (generate_t 8 0).

Print BigN.succ_t.
Search _ BigN.dom_t.
Print BigN.View_t.
Search _ bigN.
Print BigN.reduce.
Lemma generate_cnt : forall h, forall (t : BigN.dom_t h), exists n, (generate_t h n) = t.
Proof.
  elim => [ | h' IH].
  - move => t.
    set z := (phi t).
     have : (t = (phi_inv z)).
     * by rewrite Cyclic31.phi_inv_phi.
       simpl.
    case z eqn:zp => tinv.
    +exists (pickle (0,0)%nat).
     simpl.
     rewrite /On.
     by rewrite tinv.
    +exists (pickle (0%nat,(Z.abs_nat z))%nat).
     rewrite pickleK.
     rewrite Zabs2Nat.id_abs.
     rewrite /Z.abs.
     rewrite zp.
     by rewrite tinv.
    +exists (pickle (1%nat,(Z.abs_nat z))%nat).
     rewrite pickleK.
     rewrite Zabs2Nat.id_abs.
     rewrite /Z.abs.
     rewrite zp.
     by rewrite tinv.
     simpl.
  - 
    destruct h'.
    move => t.
    case t eqn: tp; first by exists 2%nat.
    have := (IH t1).
    case => n1 n1p.
    have := (IH t0).
    case => n0 n0p.
    exists (pickle (n0,n1)).
    rewrite /generate_t.
    rewrite pickleK.
    rewrite <- n0p.
    rewrite <- n1p.
    by [].
  - move => t.
    destruct h'.
    case t; first by exists 2%nat.
    move => t0 t1.
    have := (IH t1).
    case => n1 n1p.
    have := (IH t0).
    case => n0 n0p.
    exists (pickle (n0,n1)).
    rewrite /generate_t.
    rewrite pickleK.
    rewrite <- n0p.
    rewrite <- n1p.
    by [].
  - 
    destruct h'.
    case t; first by exists 2%nat.
    move => t0 t1.
    have := (IH t1).
    case => n1 n1p.
    have := (IH t0).
    case => n0 n0p.
    exists (pickle (n0,n1)).
    rewrite /generate_t.
    rewrite pickleK.
    rewrite <- n0p.
    rewrite <- n1p.
    by [].
  - 
    destruct h'.
    case t; first by exists 2%nat.
    move => t0 t1.
    have := (IH t1).
    case => n1 n1p.
    have := (IH t0).
    case => n0 n0p.
    exists (pickle (n0,n1)).
    rewrite /generate_t.
    rewrite pickleK.
    rewrite <- n0p.
    rewrite <- n1p.
    by [].
  - 
    destruct h'.
    case t; first by exists 2%nat.
    move => t0 t1.
    have := (IH t1).
    case => n1 n1p.
    have := (IH t0).
    case => n0 n0p.
    exists (pickle (n0,n1)).
    rewrite /generate_t.
    rewrite pickleK.
    rewrite <- n0p.
    rewrite <- n1p.
    by [].
  - 
    destruct h'.
    case t; first by exists 2%nat.
    move => t0 t1.
    have := (IH t1).
    case => n1 n1p.
    have := (IH t0).
    case => n0 n0p.
    exists (pickle (n0,n1)).
    rewrite /generate_t.
    rewrite pickleK.
    rewrite <- n0p.
    rewrite <- n1p.
    by [].
  - 
    have ts: forall m,(BigN.succ_t m.+2.+4 W0) = W0 by elim => [| m Ihm]; by [].
    elim t; first by exists 2%nat; apply ts.
    move : IH.
    elim h' => [| h'' IH'].
    move =>IH t0 t1.
    have := (IH t1).
    case => n1 n1p.
    have := (IH t0).
    case => n0 n0p.
    exists (pickle (n0,n1)).
    rewrite pickleK.
    rewrite <- n0p.
    rewrite <- n1p.
    by [].
    move => IH t0 t1.
    have := (IH t1).
    case => n1 n1p.
    have := (IH t0).
    case => n0 n0p.
    exists (pickle (n0,n1)).
    rewrite pickleK.
    rewrite <- n0p.
    rewrite <- n1p.
    by [].
Qed.

Lemma generate_cnt2 : forall N : bigN, exists h n, (BigN.mk_t h (generate_t h n)) = N.
Proof.
  elim => t.
  - case (@generate_cnt 0 t).
    move => n P.
    by exists 0%nat, n;rewrite P.
  - case (@generate_cnt 1 t).
    move => n P.
    by exists 1%nat, n;rewrite P.
  - case (@generate_cnt 2 t).
    move => n P.
    by exists 2%nat, n;rewrite P.
  - case (@generate_cnt 3 t).
    move => n P.
    by exists 3%nat, n;rewrite P.
  - case (@generate_cnt 4 t).
    move => n P.
    by exists 4%nat, n;rewrite P.
  - case (@generate_cnt 5 t).
    move => n P.
    by exists 5%nat, n;rewrite P.
  - case (@generate_cnt 6 t).
    move => n P.
    by exists 6%nat, n;rewrite P.
  -
    elim t => [| h' IH'].
    move => w.
    case (@generate_cnt 7 w).
    move => n P.
    by exists 7%nat, n;rewrite P.
    move => w.
    case (@generate_cnt h'.+2.+4.+2 w).
    move => n P.
    by exists h'.+2.+4.+2, n;rewrite P.
Qed.

Lemma BigInt_count : bigN \is_countable.
Proof.
   apply (countable_comp (prod_count nat_count nat_count)).
   exists (fun n => (BigN.mk_t n.1 (generate_t n.1 n.2))).
   move => N. 
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
             end).
   move => Z.
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
    D2R (SFBI2.add mode p (Float e m) (Float e' m')) = Interval_definitions.round SFBI2.radix mode (SFBI2.prec p) (D2R (Float e m) + (D2R (Float e' m'))).
Proof.
move => mode p e e' m m'.
have := SFBI2.add_correct mode p (Float e m) (Float e' m').
rewrite !D2R_SFBI2toX.
rewrite /Xadd/Interval_definitions.Xround/Xbind/SFBI2.toX.
rewrite /Interval_definitions.FtoX.
by case E: (SFBI2.toF (SFBI2.add mode p (Float e m) (Float e' m'))) => //; move =>  [<-]; rewrite /D2R/proj_val/SFBI2.toX/Interval_definitions.FtoX E.
Qed.

Lemma add_error I J n m p:
  bounded I -> diam I <= /2^n -> bounded J -> diam J <= /2^m ->
  bounded (I.add (nat2p p) I J)
  /\
  diam (I.add (nat2p p) I J) <= /2 ^ n + /2 ^ m + /2 ^ p.
Proof.
case: I => //; case => //lIe lIm; case => //uIe uIm _ ineq; rewrite /= in ineq.
case: J => //; case => //lJe lJm; case => //uJe uJm _ ineq'; rewrite /= in ineq'.
split; first admit.
rewrite /upper /lower !SFBI2_add_correct /=.
Admitted.

Definition Rplus_rlzrf (phi: names (IR \*_cs IR)) (n: queries IR):= I.add (nat2p n) (lprj phi n) (rprj phi n).

Definition Rplus_rlzr: questions (IR \*_cs IR) ->> questions IR := F2MF Rplus_rlzrf.

Lemma Rplus_rlzr_spec : Rplus_rlzr \realizes (F2MF (fun xy => Rplus xy.1 xy.2)).
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
rewrite /Rplus_rlzr/Rplus_rlzrf; split.
admit.
have npg0: 0 < 2 ^ n.+1.
	admit.
have /=exp: /2 ^ k <= /2 * /2 ^ n.
	admit.
apply /Rle_trans; first by apply (@add_error (lprj phi k) (rprj phi k) n.+2 n.+2 k).
have ng0: 0 < 2^n by apply pow_lt; lra.
by rewrite /= !Rinv_mult_distr; try lra.
Admitted.
