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
Check I.add.

Print I.extension_2.
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

Lemma Rabs_bnd a b c : (Rabs (a-b)) <= c -> (Rabs a <= ((Rabs b) + c)).
    move => H.
    suff : (Rabs a - Rabs b <= c) by lra.
    apply /Rle_trans.
    by apply Rabs_triang_inv.
    by [].
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

Lemma SFBI2_BigZ p: (1 < p)%bigZ -> (Z.pos (SFBI2.prec p))=[p]%bigZ.
 move => pgt.
  - rewrite /SFBI2.prec/BigIntRadix2.EtoZ.
    move : pgt.
    case M : [p]%bigZ => [|p'|p']; try by rewrite /BigZ.lt M //=.
Qed.

Lemma round_error : forall (mode: Interval_definitions.rounding_mode) x N p, (1 < p)%bigZ -> (Rabs x <= powerRZ 2 N) -> (Rabs ((Interval_definitions.round SFBI2.radix mode (SFBI2.prec p) x) - x)) <= (powerRZ 2 (N+1-[p]%bigZ)).
Proof.
  move => mode x N p [pgt B].
  have helper2 : (1 < (Z.pos (SFBI2.prec p)))%Z by rewrite SFBI2_BigZ.
  rewrite /Interval_definitions.round.
  apply /Rle_trans.
  apply Ulp.error_le_ulp; by [apply FLX.FLX_exp_valid; [] | apply Interval_definitions.valid_rnd_of_mode].
  apply /Rle_trans.
  apply FLX.ulp_FLX_le; by [].
  rewrite Raux.bpow_powerRZ //=.
  rewrite <- Z.pos_sub_opp, <-Z.add_sub_assoc, Z.pos_sub_gt, Pos2Z.inj_sub, Z.opp_sub_distr; try by [].
  rewrite Z.add_comm Z.add_opp_r.
  rewrite powerRZ_add;last by lra.
  rewrite SFBI2_BigZ; last by [].
  apply Rmult_le_compat_r; last by [].
  by apply powerRZ_le; lra.
Qed.

Lemma add_error I J n m p x y N:
  (1 < p)%bigZ ->
  (0 <= N)%Z ->
  bounded I -> diam I <= /2^n -> bounded J -> diam J <= /2^m ->
  (x \contained_in I) ->
  (y \contained_in J) ->
  (Rabs x) <=  (powerRZ 2 N) -> (Rabs y) <= (powerRZ 2 N) ->
  bounded (I.add p I J)
  /\
  diam (I.add p I J) <= /2 ^ n + /2 ^ m + (powerRZ 2 (N+4-[p]%bigZ)).
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
  have t1 :  (Interval_definitions.round SFBI2.radix Interval_definitions.rnd_UP (SFBI2.prec p) ((D2R (Float uIm uIe))+(D2R (Float uJm uJe)))) <= ((D2R (Float uIm uIe))+(D2R (Float uJm uJe)))+(powerRZ 2 ((N+3-[p]%bigZ))).
  -  
    apply (Rcomplements.Rabs_le_between').
    apply /Rle_trans.
    apply (round_error _ pgt BP1).
    suff : ((N + 2 + 1 -[p]%bigZ) = (N + 3 - [p]%bigZ))%Z by move => ->;apply Req_le.
    by lia.
  have t2 :   ((D2R (Float lIm lIe))+(D2R (Float lJm lJe))) <= (Interval_definitions.round SFBI2.radix Interval_definitions.rnd_DN (SFBI2.prec p) ((D2R (Float lIm lIe))+(D2R (Float lJm lJe))))+ (powerRZ 2 ((N+3-[p]%bigZ))).
  - apply (Rcomplements.Rabs_le_between').
    rewrite Rabs_minus_sym.
    apply /Rle_trans.
    apply (round_error _ pgt BP2); try by [].
    suff : ((N + 2 + 1 -[p]%bigZ) = (N + 3 - [p]%bigZ))%Z by move => ->;apply Req_le.
    by lia.
  rewrite Rcomplements.Rle_minus_l.
  apply /Rle_trans.
  apply t1.
  have pwr : (powerRZ 2 (N+4 - [p]%bigZ)) = (2*powerRZ 2 (N+3- [p]%bigZ)) by rewrite !(powerRZ_add);try by simpl;lra.
  rewrite pwr.
  suff :  (D2R (Float uIm uIe)) + (D2R (Float uJm uJe)) - (/ 2 ^ n) - (/ 2 ^ m) <= (Interval_definitions.round SFBI2.radix Interval_definitions.rnd_DN (SFBI2.prec p) ((D2R (Float lIm lIe)) + (D2R (Float lJm lJe)))) + (powerRZ 2 (N + 3 - [p]%bigZ)) by lra.
  have T:= (Rle_trans ((D2R (Float uIm uIe)) + (D2R (Float uJm uJe)) - (/ 2 ^ n) - (/ 2 ^ m))  _ _ _ t2).
  by apply T; lra.
Qed.




Definition Rplus_rlzrf (phi: questions (IR \*_cs IR)) (n: queries IR):= I.add (nat2p n) (lprj phi n) (rprj phi n).
Definition Rplus_rlzr: questions (IR \*_cs IR) ->> questions IR := F2MF Rplus_rlzrf.


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
    rewrite (Raux.IZR_Zpower SFBI2.radix); last by apply Z.log2_up_nonneg.
    by rewrite <- (Raux.bpow_powerRZ SFBI2.radix);lra.
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
  have [bnd err] := (add_error lt lt' bndl dml bndr dmr (xephin k) (yephin k) Kprp2 Kprp3).
  split; first by apply bnd.
  apply /Rle_trans.
  apply err.
  suff H : (powerRZ 2 ((Z.of_nat K)+4 - [nat2p k]%bigZ)) <= (/ 2 ^ n.+1).
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
Lemma round_error_mul p rnd x y M: (1 < p)%bigZ -> (Rabs x) <= (powerRZ 2 M) -> (Rabs y) <= (powerRZ 2 M) -> x*y - (powerRZ 2 (2*M+1-[p]%bigZ)%Z) <= (Interval_definitions.round SFBI2.radix rnd (SFBI2.prec p) (x*y)) <= x*y + (powerRZ 2 (2*M+1-[p]%bigZ)%Z).
Proof.
  move => pgt H1 H2.
  have lt : (Rabs (x*y)) <= (powerRZ 2 (2*M)).
  - rewrite Rabs_mult.
    rewrite <-Z.add_diag, powerRZ_add; last by lra.
    by apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | |].
  apply Rcomplements.Rabs_le_between'.
  apply round_error; by [].
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
  diam (I.mul p I J) <= (powerRZ 2 (N+1-(Z.of_nat n)))+ (powerRZ 2 (N+1-(Z.of_nat m))) + (powerRZ 2 (2*N+4-[p]%bigZ)).
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
  have round_sub_simplification M rnd rnd' m1 m2 m3 m4 e1 e2 e3 e4: ((Rabs (D2R (Float m1 e1))) <= (powerRZ 2 M)) -> ((Rabs (D2R (Float m2 e2))) <= (powerRZ 2 M)) -> ((Rabs (D2R (Float m3 e3))) <= (powerRZ 2 M)) -> ((Rabs (D2R (Float m4 e4))) <= (powerRZ 2 M)) -> (SFBI2.mul rnd p (Float m1 e1) (Float m2 e2)) - (SFBI2.mul rnd' p (Float m3 e3) (Float m4 e4)) <= (D2R (Float m1 e1))*(D2R (Float m2 e2)) + (powerRZ 2 (2*M+1-[p]%bigZ)%Z) - ((D2R (Float m3 e3))*(D2R (Float m4 e4)) - (powerRZ 2 (2*M+1-[p]%bigZ)%Z)).
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
    have helper u v u' v' : (u*v + (powerRZ 2 (2*(N+1)+1-[p]%bigZ)))-(u'*v' - (powerRZ 2 (2*(N+1)+1-[p]%bigZ))) = (u*v - u'*v')+(powerRZ 2 (2*N+4-[p]%bigZ)).
    - suff :  (powerRZ 2 1)*(powerRZ 2 (2 * (N + 1) + 1 - [p]%bigZ))  =  (powerRZ 2 (2*N + 4 - [p]%bigZ)) by simpl;lra.
      rewrite <- powerRZ_add; try by lra.
      suff H0 :((1 + (2 * (N + 1) + 1 - [p]%bigZ)) =  (2 * N + 4 - [p]%bigZ))%Z by rewrite H0.
      by lia.
    rewrite diam_absI in ineq.
    rewrite diam_absJ in ineq'.
    have ineq_rev := ineq.
    have ineq'_rev := ineq'.
    have ineq_triv z k: (Rabs (z - z) <= / 2 ^ k) by rewrite Rcomplements.Rminus_eq_0 Rabs_R0;apply tpmn_pos.
    rewrite Rabs_minus_sym in ineq_rev.
    rewrite Rabs_minus_sym in ineq'_rev.
    have case_helper rnd rnd' m1 e1 m2 e2 m1' e1' m2' e2' : (Rabs (D2R (Float m1 e1))) <= (powerRZ 2 (N+1)) -> (Rabs (D2R (Float m1' e1'))) <= (powerRZ 2 (N+1)) -> (Rabs (D2R (Float m2 e2))) <= (powerRZ 2 (N+1)) -> (Rabs (D2R (Float m2' e2'))) <= (powerRZ 2 (N+1)) ->  (Rabs ((D2R (Float m1 e1)) - (D2R (Float m1' e1')))) <= / 2 ^ n -> (Rabs ((D2R (Float m2 e2)) - (D2R (Float m2' e2')))) <= / 2 ^ m -> (SFBI2.mul rnd p (Float m1 e1) (Float m2 e2)) - (SFBI2.mul  rnd' p (Float m1' e1') (Float m2' e2')) <= (powerRZ 2 (N+1-(Z.of_nat n)))+(powerRZ 2 (N+1-(Z.of_nat m)))+(powerRZ 2 (2*N + 4 - [p]%bigZ)).
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
  powerRZ 2 (2 * N + 4 - [p]%bigZ).
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
  suff H : (powerRZ 2 (2*(Z.of_nat K)+4 - [nat2p k]%bigZ)) <= (/ 2 ^ n.+1).
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
(*******************************************************************)
Definition to_pair (d : D) := match d with
                         | Fnan => (0%Z, 1%Z)
                         | (Float m e) => ([m]%bigZ, [e]%bigZ)
                                end.
                          
 Fixpoint logistic_map phi rm re N : (name_space IR)  := match N with
                                       | 0%nat => phi
                                       | M.+1 => let P := (logistic_map phi rm re M) in (Rmult_rlzrf (name_pair (FloattoIR rm re) (Rmult_rlzrf (name_pair P (Rplus_rlzrf (name_pair (FloattoIR 1 0) (Rmult_rlzrf (name_pair (FloattoIR (-1) 0) P))))))))
                                       end.
(*******************************************************************)

Definition QtoIR p q := match q with 
                        (a#b) => (I.div p  (I.fromZ a) (I.fromZ (Z.pos b)))
                        end.
Require Import Qreals.
Require Import Q_reals.

Lemma QtoIR_correct p q :  (Q2R q) \contained_in (QtoIR p q).
Proof.
  case q => a b.
  suff -> : (Xreal (Q2R (a # b))) = (Xdiv (Xreal (IZR a)) (Xreal (IZR (Z.pos b)))).
  - by apply I.div_correct; apply I.fromZ_correct.
  rewrite /Xdiv' /is_zero//=.
  have -> // : (Raux.Req_bool (IZR (Z.pos b)) 0) = false.
  exact /Raux.Req_bool_false/IZR_nz.
Qed.

Lemma sign_strict_pos b : (I.sign_strict_ (SFBI2.fromZ (Z.pos b)) (SFBI2.fromZ (Z.pos b))) = Xgt.
Proof.
  have blt: (0 < IZR (Z.pos b)) by rewrite /IZR;rewrite <- INR_IPR;apply pos_INR_nat_of_P.
 have  := (I.sign_strict_correct_ _ _ _ (I.fromZ_correct (Z.pos b))).
  case e :(I.sign_strict_ (SFBI2.fromZ (Z.pos b)) (SFBI2.fromZ (Z.pos b))); try by [];try by lra.
 rewrite /SFBI2.toX !SFBI2.fromZ_correct.
 by lra.
Qed.     

Lemma div_real a b r p : SFBI2.real (SFBI2.div r p (SFBI2.fromZ a) (SFBI2.fromZ (Z.pos b))).
Proof.
  rewrite SFBI2.real_correct SFBI2.div_correct /SFBI2.toX !SFBI2.fromZ_correct //= /Xdiv'.
  by have -> : (is_zero (IZR (Z.pos b))) = false by apply Raux.Req_bool_false.
Qed.

Lemma QtoIR_bounded q p : bounded (QtoIR p q).
Proof.
  case q => a b.
  rewrite /QtoIR /SFBI2.fromZ/I.fromZ /I.div /I.Fdivz/bounded sign_strict_pos.
  by case : (I.sign_strict_ (SFBI2.fromZ a) (SFBI2.fromZ a)); try by rewrite !div_real.
Qed.

Notation "'\|' x '|' " := (Rabs x) (format "'\|' x '|' ").

Lemma QtoIR_diam (q:Q) N p: (1 < p)%bigZ -> \|q| <= powerRZ 2 N ->  diam (QtoIR p q) <= powerRZ 2 (N+2-[p]%bigZ).
Proof. 
  case q => a b pgt qlt.
  suff rnd_error rnd rnd': (SFBI2.div rnd p (SFBI2.fromZ a) (SFBI2.fromZ (Z.pos b))) - (SFBI2.div rnd' p (SFBI2.fromZ a) (SFBI2.fromZ (Z.pos b))) <= powerRZ 2 (N + 2 - [p]%bigZ).
  - rewrite /QtoIR /I.fromZ /I.div /I.Fdivz !sign_strict_pos [SFBI2.real (SFBI2.fromZ _)]//=.
    by case:I.sign_strict_; try exact/rnd_error; rewrite /D2R Rminus_0_r;apply powerRZ_le;lra.
  rewrite /D2R !SFBI2.div_correct.
  rewrite /SFBI2.toX !SFBI2.fromZ_correct /Xdiv' //=.
  rewrite /is_zero Raux.Req_bool_false; last exact: IZR_nz.
  apply Rcomplements.Rabs_le_between.
  have -> : forall (u v : R), u - v = (u - (a#b)) +  ((a#b) - v) by intros; lra.
  apply /Rle_trans; first exact/Rabs_triang.
  have -> : forall k, (N+2 - k = (N+1)-k+1)%Z by intros;lia.
  rewrite powerRZ_add ; last by lra.
  rewrite /=Rmult_comm Rmult_1_r double.
  by apply Rplus_le_compat; last rewrite <- Rabs_minus_sym; apply round_error.
Qed.

Definition extend J p := (I.add (nat2p p) J (I.bnd (Float (-1)%bigZ (-(BigZ.of_Z (Z.of_nat p)))%bigZ) (Float (1)%bigZ (-(BigZ.of_Z (Z.of_nat p)))%bigZ))).

Lemma extend_diam_lb J p x y: (x \contained_in J) -> (Rabs (y-x)) <= (/ 2 ^ p) -> (y \contained_in (extend J p)). 
Proof.
  move => xc dist.
  set K := (I.bnd (Float (-1)%bigZ (-(BigZ.of_Z (Z.of_nat p)))%bigZ) (Float (1)%bigZ (-(BigZ.of_Z (Z.of_nat p)))%bigZ)).
  have -> : y = (x + (y-x)) by lra. 
  suff cnt : ((y-x) \contained_in K) by apply (add_correct_R (nat2p p) xc cnt).
  rewrite //= !Interval_definitions.FtoR_split Float_prop.F2R_Zopp !Float_prop.F2R_bpow.
  rewrite !Raux.bpow_powerRZ/BigIntRadix2.EtoZ BigZ.spec_opp //=.
  apply Rcomplements.Rabs_le_between.
  by rewrite BigIntRadix2.ZtoE_correct powerRZ2_neg_pos.
Qed.

Lemma extend_diam_ub J p n x N: (1 < p)%nat -> (0 <= N)%Z ->
 (bounded J) -> (diam J <= (/ 2 ^ n)) -> (x \contained_in J) -> ((Rabs x) <= (powerRZ 2 N)) -> (diam (extend J p)) <= (/ 2 ^ n)+(/ 2 ^ (p.-1)) + (powerRZ 2 (N + 4 - [nat2p p]%bigZ)).
Proof.
  move => plt Nlt B dJ xc xb.
  set K := (I.bnd (Float (-1)%bigZ (-(BigZ.of_Z (Z.of_nat p)))%bigZ) (Float (1)%bigZ (-(BigZ.of_Z (Z.of_nat p)))%bigZ)).
  have plt' : (1 < (nat2p p))%bigZ.
  - rewrite /nat2p.
    rewrite /SFBI2.PtoP /BigZ.lt //=.
    rewrite BigN.spec_of_pos.
    have -> : (p = ((p.-2).+1).+1) by move /leP : plt;lia.
    have -> : (((phi 1)) = 1)%Z by [].
    case (p.-2) => [| m]; rewrite //=;lia.
  have [Bk dK] : (bounded K) /\ ((diam K) <= (/ 2 ^ (p.-1))).
  - split; first by [].
    rewrite !D2R_Float //=.
    have -> : (IZR (phi 1)) = 1 by [].
    ring_simplify.
    rewrite BigZ.spec_opp BigIntRadix2.ZtoE_correct powerRZ2_neg_pos//=.
    have {1}-> : (p = ((p.-1).+1))%nat.
    + rewrite Nat.succ_pred_pos; first by [].
      move /leP : plt.
      by lia.
    rewrite double.
    rewrite <- tpmn_half.
    by lra.
  have c0 : (0 \contained_in K).
  - rewrite //= !Interval_definitions.FtoR_split Float_prop.F2R_Zopp !Float_prop.F2R_bpow.
    rewrite !Raux.bpow_powerRZ/BigIntRadix2.EtoZ BigZ.spec_opp //=.
    apply Rcomplements.Rabs_le_between.
    rewrite Rabs_R0.
    by apply powerRZ_le; lra.
  apply (add_error plt' Nlt B dJ Bk dK xc c0 xb).
  by rewrite Rabs_R0; apply powerRZ_le;lra.
Qed.
Definition QRtoIR (phi : (Q -> Q)) := (fun p:nat => (extend (QtoIR (nat2p p) (phi (/ (inject_Z (Z.pow 2 (Z.of_nat p))))%Q)) p)).

Lemma eps_simplify p : (Q2R (/ (inject_Z (Z.pow 2 (Z.of_nat p))))%Q) = (/ 2 ^ p).
Proof.
  rewrite Q2R_inv.
  - field_simplify_eq; first by rewrite pow_IZR/inject_Z/Q2R //=;lra. 
    split; first by apply pow_nonzero;lra.
    rewrite /inject_Z/Q2R //=.
    suff: (IZR (2 ^ (Z.of_nat p))) <> (IZR 0) by lra.
    apply IZR_neq.
    by apply Z.pow_nonzero; lia.
  apply Qnot_eq_sym.
  apply Qlt_not_eq.
  rewrite /inject_Z //=.
  apply Rlt_Qlt.
  rewrite /Q2R //=.
  suff : (IZR 0) < (IZR (2 ^ (Z.of_nat p))) by lra.
  apply IZR_lt.
  apply Z.pow_pos_nonneg; by lia.
Qed.

Lemma QRtoIR_contains phi x : (phi \describes x \wrt RQ) -> (forall p, (x \contained_in (QRtoIR phi p))).
  move => //=phin p.
  rewrite /QRtoIR.
  set eps := (/ (inject_Z (Z.pow 2 (Z.of_nat p))))%Q.
  have c := (QtoIR_correct (nat2p p) (phi eps)).
  apply (extend_diam_lb c).
  suff <- : (Q2R eps) = (/ 2 ^ p).
  - apply (phin eps).
    have -> : (0 = Q2R 0) by lra.
    apply Qlt_Rlt.
    apply Qinv_lt_0_compat.
    have -> : (0%Q = (inject_Z 0)) by compute.
    rewrite <- Zlt_Qlt.
    apply Z.pow_pos_nonneg; by lia.
 rewrite /eps.
 apply eps_simplify.
Qed.

Lemma extend_bounded J p : (bounded J) -> (bounded (extend J p)).
Proof.
  rewrite /extend.
  rewrite /I.add //=.
  case J => [| u l]; first by [].
  rewrite /bounded !SFBI2.real_correct //=.
  case u => [|m e]; case l => [|m' e']; try by [].
  - by rewrite andb_false_r.
 move => _.
 rewrite !SFBI2.add_correct.
 by rewrite !D2R_SFBI2toX.
Qed.

Definition RQ_IR_id_rlzr: questions RQ ->> questions IR := F2MF QRtoIR.
Lemma RQ_IR_id_rlzr_cont : RQ_IR_id_rlzr \is_continuous_operator.
Proof.
  rewrite cont_F2MF => phi.
  rewrite /QRtoIR //=.
  by exists (fun n => [:: (/ inject_Z (2 ^ Z.of_nat n))%Q]) => n psi [] ->.
Qed.

Definition RQ_IR_id_rlzr_spec : RQ_IR_id_rlzr \realizes (F2MF (fun x => x)).
Proof.     
  rewrite F2MF_rlzr_F2MF => phi x //= phinx.
  split; first by apply QRtoIR_contains.
  case (powerRZ_bound x) => K [Kprp1 Kprp2].
  move => n.
  exists (((Z.to_nat K)+n).+4.+3)%nat => k kprp.
  rewrite /QRtoIR.
  have klt' : (1 < k)%nat.
    apply /leP.
    move /leP : kprp.
    by lia.
  have klt : (1 < (nat2p k))%bigZ.
  - suff : (1 < k)%coq_nat; last by apply /leP.
    rewrite /nat2p/SFBI2.PtoP/BigZ.lt //=.   
    rewrite BigN.spec_of_pos.
    rewrite Nat2Z.inj_lt //=.
    case  k => [|p]; by [lia |rewrite /Z.of_nat Pos.of_nat_succ].
  set eps := (/ inject_Z (2 ^ Z.of_nat k))%Q.
  have epsgt0 : (0 < eps) by rewrite eps_simplify;apply tpmn_lt.
  have lt' : (Rabs (phi eps)) <= (powerRZ 2 (K+1)).
  - rewrite powerRZ_add; last by lra.
    simpl;ring_simplify.
    rewrite double.
    suff : (Rabs (phi eps))  <= (Rabs x)+(powerRZ 2 K) by lra.
    apply Rabs_bnd.
    rewrite Rabs_minus_sym.
    apply /Rle_trans.
    apply (phinx eps); first by [].
    rewrite eps_simplify.
    rewrite Interval_missing.pow_powerRZ.
    rewrite !powerRZ_Rpower; try by lra.
    rewrite <-Rpower_Ropp.
    apply Rle_Rpower; first by lra.
    rewrite <- opp_IZR.
    apply IZR_le.
    by lia.
  have diam1 := (QtoIR_diam klt lt' ).
  have zp : ((Z.pos (Pos.of_nat k)) = (Z.of_nat k)).
  - move : kprp.
    case k => [|k' H]; first by rewrite ltn0.
    rewrite Nat2Pos.inj_succ //=; last by move /leP : H;lia.
    rewrite Pos.succ_of_nat; last by move /leP : H;lia.
    by [].
  have simp_exp : (K+1+2- [nat2p k]%bigZ)%Z = (-Z.of_nat (k - (Z.to_nat K)-3 ))%Z.
  -  rewrite //= BigN.spec_of_pos.
     have -> : (3%nat = (Z.to_nat 3%Z))%nat by auto.
     have -> : (k = (Z.to_nat (Z.of_nat k)))%nat by rewrite Nat2Z.id.
     rewrite <- !Z2Nat.inj_sub; try by lia.
     rewrite Z2Nat.id; last first.
     + suff : ((K+3) < (Z.of_nat k))%Z by lia.
       suff :((Z.to_nat K) + 3 < k)%coq_nat.
       * have -> : (3%Z = (Z.of_nat 3%nat))%nat by auto.
         have {2}-> : (K = (Z.of_nat (Z.to_nat K)))%nat by rewrite Z2Nat.id.
         rewrite <- Nat2Z.inj_add; try by lia.
         by apply inj_lt.
       rewrite /addn/addn_rec.
       move /ltP : kprp.
       rewrite /addn/addn_rec.
       by lia.
       rewrite Nat2Z.id.
       by suff : ((Z.pos (Pos.of_nat k)) = (Z.of_nat k))%nat by lia.
  have Klt : (0 <= K+1)%Z by lia.
  rewrite simp_exp in diam1.
  rewrite powerRZ2_neg_pos in diam1.
  have d := (extend_diam_ub klt' Klt _ diam1 _ lt').
  split; first by apply extend_bounded;apply QtoIR_bounded.
  - apply /Rle_trans.
  apply d; by [apply QtoIR_bounded | apply (QtoIR_correct (nat2p k) (phi eps))].
  rewrite (tpmn_half n).
  rewrite {1}(tpmn_half n.+1).
  apply Rplus_le_compat; [apply Rplus_le_compat;apply /tpmnP;apply /leP | ].
  - move /leP :  kprp.
    by rewrite /addn/addn_rec/subn/subn_rec;lia.
  - move /leP :  kprp.
    by rewrite /addn/addn_rec/subn/subn_rec;lia.
  rewrite <- powerRZ2_neg_pos.
  rewrite !powerRZ_Rpower; try by lra.
  apply Rle_Rpower; first by lra.
  apply IZR_le.
  rewrite /nat2p/SFBI2.PtoP/BigZ.lt. 
  rewrite [[_]%bigZ]//=.
  rewrite BigN.spec_of_pos zp.
  move /leP: kprp.
  rewrite Nat2Z.inj_le.
  rewrite !Nat2Z.inj_succ Nat2Z.inj_add.
  rewrite <- !Z.add_1_r.
  rewrite Z2Nat.id; last by [].
  by lia.
Qed.

Lemma RQ_IR_id_cont : (id : (RQ -> IR)) \is_continuous.
Proof.
  exists RQ_IR_id_rlzr.
  by split; [apply RQ_IR_id_rlzr_spec | apply RQ_IR_id_rlzr_cont].
Qed.
 
Print SFBI2.type.
Definition Float2Q d := match d with
                        | Fnan => 0%Q
                        | Float m e => ((inject_Z [m]%bigZ) * (Qpower (1+1)%Q [e]%bigZ))%Q
                        end.
Lemma Qpower_Rpower a b: (Q2R (Qpower a b)) = (powerRZ a b).
Admitted.
Lemma Float2Q_spec d : (D2R d) = (Q2R (Float2Q d)).
Proof.
  rewrite /D2R.
  case d => //=[| m e]; first by lra.
  rewrite D2R_SFBI2toX D2R_Float Q2R_mult Qpower_Rpower.
  by rewrite /Q2R Rinv_1 !Rmult_1_r.
Qed.
Definition diamQ I := (Float2Q (upper I)-(Float2Q (lower I)))%Q.
Lemma diamQ_spec I : (Q2R (diamQ I)) = (diam I).
Proof.
   by rewrite  !Float2Q_spec Q2R_minus.
Qed.

Definition IR_RQ_M In (neps : nat*Q) := let n := neps.1 in
                              let eps := neps.2 in
                              if Qle_bool (diamQ (In n)) eps
                              then Some (Float2Q (lower (In n)))
                              else None.
Lemma IR_RQ_M_spec In x: (In \describes x \wrt IR) -> (forall (eps : Q), (0 < eps)-> exists n q, (IR_RQ_M In (n,eps)) = (Some q) /\ (\| q - x| <= (Q2R eps))).                                                 
Proof.
  move => [xcont shrink] eps epsgt.
  case  (dns0_tpmn epsgt) => n nprop.
  apply Rlt_le in nprop.
  case (shrink n) => N Nprop.
  exists N; exists (Float2Q (lower (In N))).
  rewrite /IR_RQ_M //=.
  rewrite ifT; last first.
  - apply Qle_bool_iff.
    apply Rle_Qle.
    rewrite diamQ_spec.
    apply /(Rle_trans _ _  _ _ nprop).
    by apply (Nprop);apply /leP;lia.
  split; first by [].
  apply /(Rle_trans _ _  _ _ nprop).
  have t : (N <= N)%nat by apply/leP;lia.
  have [Nprop1 Nprop2] := (Nprop N t).
  apply /(Rle_trans _ _  _ _ Nprop2).
  apply ID_bound_dist; try by [].
  rewrite <- Float2Q_spec.
  apply upper_lower_contained; try by [].
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
  Require Extraction.

  Require ExtrHaskellBasic.
  Require ExtrHaskellZInteger.
  Require ExtrHaskellNatInteger.
  Extraction Language Haskell.

Extract Inlined Constant Z.abs => "(Prelude.abs)".
Extract Inlined Constant Z.geb => "(Prelude.>=)".
Extract Inlined Constant Z.leb => "(Prelude.<=)".
Extract Inlined Constant Z.gtb => "(Prelude.>)".
Extract Inlined Constant Z.ltb => "(Prelude.<)".
Extract Inlined Constant Z.opp => "(Prelude.negate)".
Extract Inlined Constant Z.succ => "(Prelude.succ)".
Extract Inlined Constant Z.pow_pos => "(Prelude.^)".
Extract Inlined Constant Z.quotrem => "(Prelude.quotRem)".
Extract Inlined Constant Z.compare => "(Prelude.compare)".
Extract Inlined Constant Pos.leb => "(Prelude.<=)".
Extract Inlined Constant Pos.ltb => "(Prelude.<)".
Extract Inlined Constant Pos.succ => "(Prelude.succ)".
Extract Inlined Constant Pos.compare => "(Prelude.compare)".
Extract Inlined Constant StdZRadix2.mantissa_add => "(Prelude.+)".
Extract Inlined Constant StdZRadix2.mantissa_sub => "(Prelude.-)".
Extract Inlined Constant StdZRadix2.mantissa_mul => "(Prelude.*)".
Extract Inlined Constant StdZRadix2.mantissa_cmp => "(Prelude.compare)".
Extract Inductive Coq.Init.Datatypes.comparison => "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].
(* Extract Inlined Constant StdZRadix2.digits_aux => "(let da m n = if m Prelude.== 1 then n else (da (m `Prelude.div` 2) (Prelude.succ n)) in da)". *)
  Extraction "logisticZ" logistic_map_mp_rlzrZ.
  Compute (logistic_map_mp_rlzrZ 400 800).
  Print StdZRadix2.digits_aux.
  Fixpoint mantissa_digits n:=
    match n with
      | (p~1)%positive | (p~0)%positive => (Pos.succ (mantissa_digits p))
      | 1%positive => 1%positive
    end.
  Lemma mantissa_digits_eq' : forall n k, ((mantissa_digits n)+k)%positive = (StdZRadix2.digits_aux n (Pos.succ k)).
  Proof.
  elim => [p IH k | p IH k | k ].
  rewrite /StdZRadix2.digits_aux //=;rewrite <-IH;by lia.
  rewrite /StdZRadix2.digits_aux //=;rewrite <-IH;by lia.
  simpl.
  case k => [p | p |]; by lia.
  Qed.
  Lemma mantissa_digits_eq : forall n, (mantissa_digits n) = (StdZRadix2.digits_aux n 1).
  Proof.
    elim => [p IH | p IH | ] //=.
    have -> :(2%positive = Pos.succ 1) by lia.
    rewrite <- mantissa_digits_eq'; by lia.
    have -> :(2%positive = Pos.succ 1) by lia.
    rewrite <- mantissa_digits_eq'; by lia.
  Qed.
  Search _ (Z -> Z).
  Print Z.pow_pos.
  Require Import Program.
  Program Fixpoint digitsUP n m {measure (Z.to_nat (n-(Z.pow_pos 2 m)))} :=
    match (Z.to_nat (n-(Z.pow_pos 2m))) with
      0%nat => m |
    _ => (digitsUP n (2*m)%positive)
    end.
  Obligation 1.
  Admitted.
  Definition bs_digits n u l 
  Definition log_map_Q N :=(logistic_map_Q (1#2) (15#4) N).
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
