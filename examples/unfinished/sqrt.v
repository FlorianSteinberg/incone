From Coquelicot Require Import Coquelicot.
From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_rlzrs.
From metric Require Import reals.
Require Import all_cs_base classical_mach.
Require Import Reals Psatz FunctionalExtensionality ClassicalChoice.
Require Import axioms all_cs cs_mtrc metric_names hyper_spaces.
From metric Require Import all_metric reals standard Qmetric.
Require Import Ibounds IrealsZ.
Require Import search.
Require Import Iextract.
From Interval Require Import Interval_tactic.
From Interval Require Import Interval_specific_ops Interval_bigint_carrier Interval_stdz_carrier.
From Interval Require Import Interval_interval_float_full Interval_interval.
From Interval Require Import Interval_xreal.
Import BigN BigZ.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import softcomparison.
Local Open Scope Z_scope.
Import QArith.
Local Open Scope R_scope.

(* Some convenient definitions *)
Definition lim := \F_limit_eff_rlzrM.
Notation lim_eff:= (efficient_limit: (IR\^w) ->> IR).
Definition IR_nonneg := make_subset (fun (x : IR) => 0 <= x).
Definition one := (FloattoIR 1%Z 0%Z).
Definition one_half := (FloattoIR 1%Z (-1)%Z).
Definition two := (FloattoIR 1%Z 1%Z).

Lemma tpmn_mult_l n m : (/ 2 ^ (n * m)%nat) = ((/ 2 ^ m) ^ n).
Proof.
  rewrite <- powerRZ2_neg_pos, powerRZ_Rpower; last by lra.
  rewrite Nat2Z.inj_mul Zopp_mult_distr_r mult_IZR Rmult_comm.
  rewrite <-Rpower_mult.
  rewrite <- INR_IZR_INZ.
  by rewrite  <- powerRZ_Rpower, Rpower_pow, powerRZ2_neg_pos; [|apply powerRZ_lt;lra |lra].
Qed.

Lemma one_describes_one : (one \is_name_of 1).
Proof.
  suff <- : (D2R (Float 1%Z 0%Z)) = 1 by apply FloattoIR_correct.
  by rewrite D2R_Float //=;lra.
Qed.

Definition tpnIR n := (FloattoIR 1%Z n).

Lemma tpnIR_spec n : (tpnIR n) \is_name_of (powerRZ 2 n).
Proof.
  rewrite /tpnIR.
  suff -> : (powerRZ 2 n) = (D2R (Float 1%Z n)) by apply FloattoIR_correct.
  by rewrite D2R_Float;lra.
Qed.

Definition tpmnIR_rlzr phi := (tpnIR (-(Z.of_nat (phi tt)))%Z).
Lemma tpmnIR_rlzr_spec : (F2MF tpmnIR_rlzr) \realizes (fun (n : nat) => (/ 2 ^ n)).
Proof.
  rewrite F2MF_rlzr => phi n phin.
  rewrite /tpmnIR_rlzr phin.
  rewrite <- powerRZ2_neg_pos.
  by apply tpnIR_spec.
Qed.

Lemma mul_comp (phi psi : B_(IR))  (x y : R) : (phi \is_name_of x) -> (psi \is_name_of y) -> (((phi \* psi) : B_(IR)) \is_name_of (x*y)).
Proof.
  move => phin psin.
  have /F2MF_rlzr cln := cleanup_spec.
  suff xyname : (pair (phi,psi) : B_(IR \*_cs IR)) \is_name_of (x,y).
  - apply cln.
    have  :=  (Rmult_rlzr_spec ).
    rewrite F2MF_rlzr => sp.
    by apply (sp _ _ xyname).
    rewrite prod_name_spec.
  by rewrite lprj_pair rprj_pair.
Qed.

Lemma plus_comp (phi psi : B_(IR)) (x y : R) : (phi \is_name_of x) -> (psi \is_name_of y) -> (((phi \+ psi) : B_(IR)) \is_name_of (x+y)).
Proof.
  move => phin psin.
  have /F2MF_rlzr cln := cleanup_spec.
  suff xyname : (pair (phi,psi) : B_(IR \*_cs IR)) \is_name_of (x,y).
  - apply cln.
    have  :=  (Rplus_rlzr_spec ).
    rewrite F2MF_rlzr => sp.
    by apply (sp _ _ xyname).
    rewrite prod_name_spec.
  by rewrite lprj_pair rprj_pair.
Qed.
Lemma div_comp phi psi (x y : R) : (y <> 0) -> (phi \is_name_of x) -> (psi \is_name_of y) -> (((phi \: psi) : (B_(IR))) \is_name_of (x/y)).
Proof.
  move => yneg0 phin psin.
  have /F2MF_rlzr cln := cleanup_spec.
  suff xyname : (pair (phi,psi) : B_(IR \*_cs IR)) \is_name_of (x,y).
  - apply cln.
    have  :=  (Rdiv_rlzr_spec ).
    rewrite F2MF_slvs => sp.
    case (sp _ _  xyname) => [| xy [[_ /= xy_prop] P]]; first by exists (x/y).
    rewrite /Rdiv in xy_prop.
    rewrite <- xy_prop.                                                              
    by apply P.                                                    
  rewrite prod_name_spec.
  by rewrite lprj_pair rprj_pair.
Qed.
Section heron.
(* To approximate sqrt(x) for 0.25 <= x <= 2 we use the Heron method. *)

(* sqrt_approx does n iterations of the Heron method with initial value x0 *)
Fixpoint sqrt_approx x0 n x := match n with
                               | 0%nat => x0
                               | (S n') => let P := (sqrt_approx x0 n' x) in
                                          (/ 2) * (P + (x / P))
                               end.         

Lemma sqrt_approx_gt_0 x x0 n : (0 <= x) ->  (0 < x0) -> 0 < (sqrt_approx x0 n x).
Proof.
  move => xge x0gt.
  elim n => [| /= n' IH]; first by auto.
  apply Rmult_lt_0_compat; try by lra.
  apply Rplus_lt_le_0_compat; first by lra.
  by apply Rcomplements.Rdiv_le_0_compat;lra.
Qed.

(* sqrt_approx converges from above *)
Lemma sqrt_approx_gt x x0 n : (0 <= x) -> (0 < x0) -> (sqrt x) <= (sqrt_approx x0 n.+1 x).
  move => xge x0gt.
  have := (sqrt_approx_gt_0 n xge x0gt).
    set y := (sqrt_approx x0 n x).
  move => ygt.
  rewrite <- sqrt_pow2.
  - rewrite /sqrt_approx.
    apply sqrt_le_1; [by lra| by apply pow2_ge_0|].
    rewrite Rpow_mult_distr.
    rewrite - /sqrt_approx.
    have -> : (y + (x/y))^2 = (y^2 + 2*x + (x/y)^2) by field_simplify_eq;lra.
    suff : (0 <= (y ^ 2 - 2*x + (x/y)^2)) by lra.
    have -> : y^2 - 2*x + (x / y)^2 = ((y-(x/y)) ^ 2) by field_simplify_eq;lra.
    by apply pow2_ge_0.
  apply Rlt_le.
  by apply (sqrt_approx_gt_0 n.+1); lra.
Qed.

(* For 0.25 <= x <= 2 and x0 = 1  the method converges quadratically *)
Lemma sqrt_approx_correct x (n :nat) :  ((/ 4) <= x <= 2) ->  (Rabs ((sqrt_approx 1 n x) - (sqrt x))) <= (/ 2 ^ (2 ^ n)).
Proof.
  move => bnd.
  have sqrtbnd : (sqrt (/4)) <= (sqrt x) <= (sqrt 2) by split; apply sqrt_le_1; lra.
  elim n => [| n' IH].
  - apply Rcomplements.Rabs_le_between'.
    split;simpl;interval.
  have xge : (0 <= x) by lra.
  have -> : (sqrt x) = (/ 2)*((sqrt x) + (x / sqrt x)).
  - field_simplify_eq.
    rewrite //= Rmult_1_r sqrt_sqrt; lra.
    by interval.
  rewrite /sqrt_approx.
  rewrite <- Rmult_minus_distr_l, Rabs_mult, Rabs_right; last by lra.
  have t : (0 < 1) by lra.
  have := (sqrt_approx_gt_0 n' xge t).
  rewrite -/sqrt_approx.
  remember (sqrt_approx 1 n' x) as y.
  move => ygt.
  have -> : y + (x/y) - ((sqrt x) + (x / sqrt x)) = (y - (sqrt x))+(x/y - (x / sqrt x)) by lra.
  have -> : y - (sqrt x) + ((x/y) - (x / sqrt x)) = (y - sqrt x)*(y - (x / sqrt x ))*(/ y).
  - field_simplify_eq;try by lra.
    split; try by lra.
    by interval.
 have -> : (y - (sqrt x))*(y - (x / sqrt x)) = ((y - (sqrt x)) ^ 2).
 - field_simplify_eq; try by interval.
   rewrite /= !Rmult_1_r.
   by rewrite !sqrt_sqrt; lra.
  suff H : Rabs (/ y) <= 2.
  - rewrite Rabs_mult.
    ring_simplify.
    rewrite <- RPow_abs.
    apply /Rle_trans.
    apply Rmult_le_compat_l; first by apply Rmult_le_pos; [lra|apply pow2_ge_0].
    apply H.
    suff : (Rabs (y - sqrt x))^2 <= (/ 2 ^ (2 ^ (n'.+1))) by lra.
    have -> : ((2 ^ (n'.+1)) = ((2 ^ n')*2))%nat by rewrite Nat.pow_succ_r' Nat.mul_comm.
    rewrite pow2_abs.
    rewrite pow_mult.
    rewrite Rinv_pow; last by apply pow_nonzero;lra.
    by apply pow_maj_Rabs.
  rewrite Rabs_Rinv; last by lra.
  rewrite Rabs_right; last by lra.
  have -> : (2 = / / 2) by lra.
  apply Rle_Rinv; try by lra.
  move : Heqy.
  case n' => [| m Heqy]; first by simpl;lra.
  have H := (sqrt_approx_gt m xge t).
  suff -> : (/ 2) = (sqrt (/ 4)) by lra.
  have -> : (/ 4) = (/ 2) ^ 2 by lra.
  rewrite sqrt_pow2;lra.
Qed.

(* The sequence we use for the efficient limit *)
Definition sqrt_approx_seq x (n : nat) := (sqrt_approx 1 (Nat.log2 n.+1).+1 x).
Lemma sqrt_approx_seq_spec x n :  ((/ 4) <= x <= 2) -> Rabs (sqrt_approx_seq x n-(sqrt x)) <= (/ 2 ^ n).
Proof.
  move => xp.
  have e := (sqrt_approx_correct (Nat.log2 n.+1).+1 xp).
  rewrite /sqrt_approx_seq.
  suff : (/ 2 ^ (2 ^ (Nat.log2 n.+1).+1)) <= (/ 2 ^ n) by lra.
  apply /tpmnP.
  apply /leP.
  suff : (n.+1 < (2 ^ (Nat.log2 n.+1).+1))%coq_nat by lia.
  by apply Nat.log2_spec;lia.
Qed.

(* realizer for the sqrt_approx function *)
Fixpoint sqrt_approx_rlzr phi0 n phi := match n with
                                 | 0%nat => phi0 
                                 | (S n') => let P := (memoize_real (sqrt_approx_rlzr phi0 n' phi)) in
                                          one_half \* (P \+ (phi \: P))
                                 end : B_(IR).


(* realizer for the square root approximation function *)
Definition sqrt_approx_n x n := (sqrt_approx_rlzr one (Nat.log2 n.+1).+1 x).

Lemma sqrt_approx_step (phi psi : B_(IR)) (x x0 :IR) : (phi \is_name_of x) -> (psi \is_name_of x0) -> (@representation IR (sqrt_approx_rlzr psi 0%nat phi) x0) /\ forall n y, (@representation IR (sqrt_approx_rlzr psi n phi) y) -> (y <> 0) -> (@representation IR (sqrt_approx_rlzr psi n.+1 phi) (/2 * (y + (x /y)))).
Proof.
  split => [| n y P yneq0]; first by auto.
  rewrite /sqrt_approx_rlzr.
  apply mul_comp.
  - suff <- : (D2R (Float 1%Z (-1)%Z)) = (/ 2) by apply FloattoIR_correct.
    rewrite D2R_Float //=.
    by lra.
  rewrite memoize_real_correct.
  apply plus_comp; try by auto.
  apply div_comp; try by auto.
Qed.



Lemma sqrt_approx_n_rlzr_spec phi x n : (phi \is_name_of x) -> ((/ 4) <= x <= 2) -> ((sqrt_approx_n phi n) : B_(IR)) \is_name_of (sqrt_approx_seq x n).
Proof.
  move => phin xbnd /=.
  have [P1 P2] := (sqrt_approx_step phin one_describes_one).
  rewrite /sqrt_approx_n /sqrt_approx_seq.
  set m := (Nat.log2 n.+1).+1.
  elim m => [| m' IH]; first by apply P1.
  apply P2; first by apply IH.
  rewrite -/sqrt_approx.
  suff : 0 < (sqrt_approx 1 m' x) by lra.
  by apply sqrt_approx_gt_0;lra.
Qed.

End heron.
Section scaling.
(* To extend the square root we define a scaling function *)
Definition next_even z := (if Z.even z then (z+2)%Z else (z+1)%Z). 
Definition scaleM phi m := match (magnitude_rlzrM_gt0 phi m) with
                                              (Some p)  =>
                                              let p' := next_even p in
                                              let psi := (tpnIR (-p')%Z) \* phi in 
                                                (Some (psi, (p'/2)%Z))
                                              | _ => None
                                              end : (option (B_(IR) * Z)).

Definition scaleM_correct phi x m psi p:  (phi \is_name_of x) -> (0 < x) -> (scaleM phi m) = (Some (psi, p)) -> exists (y : IR), (psi \is_name_of y) /\ ((/ 4) <= y <= 2) /\ (powerRZ 4 p)*y = x.
Proof.
  move => phin xgt0.
  rewrite /scaleM.
  case e: (magnitude_rlzrM_gt0 _ _) => [z | ] //.
  have M := (magnitude_rlzrM_gt0_correct phin xgt0 e).
  case => H. 
  have := (mul_comp (tpnIR_spec (- (next_even z))%Z) phin).
  rewrite /next_even => H' pprp.
  rewrite <- H.
  have pwrz_simpl z' : (powerRZ 2 (z - z')) <= (powerRZ 2 (-z')%Z)*x <= (powerRZ 2 ((z+2)-z')).
  - rewrite Rmult_comm.
    rewrite powerRZ_add; try by lra.
    rewrite powerRZ_add; try by lra.
    split; by apply Rmult_le_compat_r; [apply powerRZ_le;lra |lra].
  have p' : (2*p = z+(if (Z.even z) then 2 else 1))%Z.
  - rewrite <- pprp.
    rewrite <-Z_div_exact_2 => //;case is_even : (Z.even z); try by lia.
    by rewrite (Zmod_even _) Z.even_add is_even /=.
    by rewrite (Zmod_even _) Z.even_succ Zodd_even_bool is_even /=.
  have pwrz_simpl2 z1' z2' z1 z2 v : (z1' <= z1)%Z -> (z2 <= z2')%Z -> ((powerRZ 2 z1) <= v <= (powerRZ 2 z2))  -> (powerRZ 2 z1') <= v <= (powerRZ 2 z2').
  - rewrite !powerRZ_Rpower; try by lra.
    move => H1 H2 H3.
    split.
    + apply /Rle_trans.
      apply Rle_Rpower; try by lra.
      apply IZR_le.
      apply H1.
      by apply H3.
    apply /Rle_trans.
    apply H3.
    apply Rle_Rpower; try by lra.
    apply IZR_le.
    by apply H2.
  have -> : 2 = (powerRZ 2 1%Z) by simpl; lra.
  have -> : (/ 4) = (powerRZ 2 (-2)%Z) by simpl; lra.
  have -> z' : (powerRZ 4 z') = (powerRZ 2 (2*z')%Z).
  - rewrite !powerRZ_Rpower; try by lra.
    rewrite mult_IZR.
    rewrite <- Rpower_mult.
    rewrite <- (powerRZ_Rpower 2%Z _); try by lra.
    by have -> : (powerRZ 2 2) = 4 by simpl;lra.
  exists  (powerRZ 2 (- (if Z.even z then (z+2)%Z else (z + 1)%Z)) * x).
  split => //.
  rewrite <- Rmult_assoc.
  rewrite <- powerRZ_add; try by lra.
  rewrite p'.
  case (Z.even z);split; try by rewrite Z.add_opp_diag_r /= ;lra.
  - apply (pwrz_simpl2 _ _ (z-(z+2))%Z (z+2-(z+2))%Z); try by lia.
    by apply pwrz_simpl.
 apply (pwrz_simpl2 _ _ (z-(z+1))%Z (z+2-(z+1))%Z); try by lia.
 by apply pwrz_simpl.
Qed.

Lemma scaleM_term phi x : (phi \is_name_of x) -> (0 < x) -> exists m, forall m', (m <= m')%nat -> exists a, (scaleM phi m') = (Some a).
Proof.
  move => phin xgt0.
  case (magnitude_rlzrM_gt0_term1 phin xgt0) => m mprp.
  exists m => m' m'prp. 
  case (mprp _ m'prp) => p pprp.
  exists (((((cleanup \o_f Rmult_rlzrf) (mp (tpnIR (- next_even p)%Z) phi)) : B_(IR)), (next_even p / 2)%Z)).
  by rewrite /scaleM pprp.
Qed.


Lemma scale_exists x : (0 < x) -> exists p y, ((/ 4) <= y <= 2) /\ (powerRZ 4 p)*y = x.
Proof.
  move => xgt0.
  set p := ((ln x)/(ln 4)).
  have pprp : -1 <= ((ln x)/(ln 4) - up p) <= 0 by have := (archimed p); rewrite /p;lra.
  have : (/ 4) <= (Rpower 4 ((ln x)/(ln 4)-up p)) <= 1.
  - have -> : (/ 4) = (Rpower 4 (-1)) by rewrite Rpower_Ropp Rpower_1; lra.
    have -> : 1 = (Rpower 4 0) by rewrite Rpower_O;lra.
    split;apply Rle_Rpower;try by lra.
  exists (up p).
  exists (Rpower 4 ((ln x/ ln 4) - up p)).
  split;first by lra.
  rewrite powerRZ_Rpower; last by lra.
  rewrite <- Rpower_plus.
  have -> : (up p + (ln x / ln 4 - up p)) = (ln x / ln 4) by lra.
  rewrite /Rpower.
  have -> : (ln x/ln 4)*(ln 4) = (ln x) by rewrite /Rdiv Rmult_assoc Rinv_l;have := ln_lt_2;have := (ln_le 2 4);lra.
  by apply exp_ln;lra.
Qed.
End scaling.

Section total_sqrt.
(* To compute the square root on all x>= 0 we first scale it appropriately *)
Lemma sqrt_approx_scale_correct n x y p:  (powerRZ 4 p)*y = x -> ((/ 4) <= y <= 2) ->(Rabs ((powerRZ 2 p)*(sqrt_approx 1 n y)-sqrt x)) <= (powerRZ 2 p)*(/ 2 ^ (2 ^ n)).
Proof.
  move => <- ygt0.
  rewrite sqrt_mult; [|by apply powerRZ_le;lra | by lra ].
  rewrite <- Rpower_sqrt, (powerRZ_Rpower 4), Rpower_mult;[| by lra | by apply powerRZ_lt;lra].
  rewrite (Rmult_comm p).
  rewrite <- Rpower_mult,  Rpower_sqrt; last by lra.
  have -> : (4 = 2*2) by lra.
  rewrite sqrt_square; last by lra.
  rewrite <- powerRZ_Rpower; last by lra.
  rewrite <-Rmult_minus_distr_l, Rabs_mult.
  rewrite Rabs_pos_eq; last by apply powerRZ_le;lra.
  apply Rmult_le_compat_l; first by apply powerRZ_le;lra.
  by apply sqrt_approx_correct.
Qed.

Lemma sqrt_approx_scale_log_correct n x y p:  (powerRZ 4 p)*y = x -> ((/ 4) <= y <= 2) ->(Rabs ((powerRZ 2 p)*(sqrt_approx_seq y (n+(Z.to_nat p))%nat)-sqrt x)) <= (/ 2 ^ n).
Proof.
  rewrite /sqrt_approx_seq.
  move => yp yb.
  have e := (sqrt_approx_scale_correct (Nat.log2 (n+(Z.to_nat p)).+1).+1 yp yb).
  have B m : (/ 2 ^ (2 ^ (Nat.log2 m.+1).+1)) <= (/ 2 ^ m).
  - apply /tpmnP.
    apply /leP.
    suff : (m.+1 < (2 ^ (Nat.log2 m.+1).+1))%coq_nat by lia.
    by apply Nat.log2_spec;lia.
  suff : (powerRZ 2 p) * (/ 2 ^ (2 ^ (Nat.log2 (n+(Z.to_nat p)).+1).+1)) <= (/ 2 ^ n) by lra.
  case p => [| p' | p']; first by have := (B n); simpl;rewrite <-!plus_n_O;lra.
  - apply /Rle_trans.
    apply Rmult_le_compat_l; first by apply powerRZ_le;lra.
    apply B.
    rewrite <-powerRZ2_neg_pos.
    rewrite Nat2Z.inj_add.
    rewrite Z2Nat.inj_pos positive_nat_Z.
    rewrite <- powerRZ_add; last by lra.
    have -> p0 : (p0 + - (Z.of_nat n + p0) = - (Z.of_nat n))%Z by lia.
    by rewrite powerRZ2_neg_pos;lra.
  rewrite Z2Nat.inj_neg.
  rewrite <- plus_n_O.
  have -> : ( / 2 ^ n) = (1 * (/ 2 ^ n)) by lra.
  apply Rmult_le_compat.
  apply powerRZ_le;lra.
  apply tpmn_pos.
  rewrite <-Pos2Z.opp_pos.
  rewrite <- (positive_nat_Z p').
  rewrite powerRZ2_neg_pos.
  by apply tpmn_bound.
  by apply (B n).
Qed.

(* We now define the multivalued function that our algorithm will compute *)
Definition sqrt_approx_total n := make_mf (fun x y => (true \from (lt_n ((2*n).+1,(x, (/ 2 ^ (2*n)))))) /\ y = 0 \/ (false \from (lt_n ((2*n).+1,(x, (/ 2 ^ (2*n)))))) /\ exists p z,  (powerRZ 4 p)*z = x /\ ((/ 4) <= z <= 2) /\ y = (powerRZ 2 p)*(sqrt_approx_seq z (n +(Z.to_nat p)))).

Definition sqrt_approx_total_seq := make_mf (fun x yn => forall n, (yn n) \from (sqrt_approx_total n x)).

Lemma sqrt_approx_total_correct x (n :nat) y :  (0 <= x) -> (y \from sqrt_approx_total n x) -> (Rabs (y - (sqrt x))) <= (/ 2 ^ n).
Proof.
  move => xgt0.
  case => [[[_ H1] H2] | [H1 ]].
  - have xlt : (x < (/ 2 ^ (2 * n))) by apply Rnot_le_lt => P; have := (H1 P).
    rewrite H2 Rminus_0_l Rabs_Ropp.
    rewrite Rabs_pos_eq; last by apply sqrt_pos.
    have -> : (/ 2 ^ n) = (sqrt (/ 2 ^ (2 * n))) by rewrite tpmn_mult_l sqrt_pow2; last by apply tpmn_pos.
    apply sqrt_le_1; try by lra.
  case => p; case => z [H2 [H3 ->]].
  by apply (sqrt_approx_scale_log_correct n H2 H3).
Qed.

Lemma sqrt_approx_total_is_total n : (sqrt_approx_total n) \is_total.
Proof.
  move => x.
  case (Rlt_or_le x (/ 2 ^ (2 * n))) => xprp.
  - exists 0.
    apply or_introl.
    by split => //; split => //; lra.
  case (@scale_exists x) => [| p]; first by have := (tpmn_lt (2*n));lra.
  case => y [prp1 prp2].  
  exists (powerRZ 2 p * (sqrt_approx_seq y (n + (Z.to_nat p)))).
  apply or_intror; split; [split => //  | exists p; exists y; split => //].
  suff :  0 < (/ ((2 ^ (2*n).+1)))  by lra.
  by apply tpmn_lt. 
Qed.

Lemma sqrt_approx_total_seq_is_total : sqrt_approx_total_seq \is_total.
Proof.
  move => x.
  have := (sqrt_approx_total_is_total _ x).
  by apply choice.
Qed.  

Lemma sqrt_lim_eff x y: (0 <= x) -> (efficient_limit \o_R sqrt_approx_total_seq) x y -> (y = sqrt x).
Proof.
  move => xgt0 H1.
  case H1 => yn [ynp1 ynp2].
  apply Rcomplements.Req_le_aux => eps.
  case (@dns0_tpmn eps); first by apply cond_pos.
  move => n nprp.
  suff : Rabs ( y - sqrt x ) <= (/ 2 ^ n) by rewrite Rabs_minus_sym; lra.
  have -> : y - sqrt x  = (y - (yn n.+1))+((yn n.+1)- sqrt x) by lra.
  apply /Rle_trans.
  apply Rabs_triang.
  apply /Rle_trans.
  apply Rplus_le_compat.
  apply (ynp2 n.+1).
  apply (sqrt_approx_total_correct xgt0 (ynp1 n.+1)).
  by rewrite <- tpmn_half;lra.
Qed. 

(* We show that the efficient limit of our approximation function is an extension of the square root *)
Lemma sqrt_as_lim :  (lim_eff \o sqrt_approx_total_seq)|_IR_nonneg \tightens ((F2MF sqrt)|_IR_nonneg).
Proof.
  apply split_tight.
  - move => x.
    rewrite !dom_restr_spec F2MF_dom.
    case => _ P.
    split => //.
    rewrite <- comp_subs_dom; first by apply sqrt_approx_total_seq_is_total.
    move => yn ynprp.
    exists (sqrt x) => n /=.
    rewrite Rabs_minus_sym.
    have := (ynprp n).
    by apply sqrt_approx_total_correct.
  move => x [t [prp1 prp2] y [xprp1 xprp2]].
  split => // /=.
  have [xprp2' _] := xprp2.
  by rewrite (sqrt_lim_eff xprp1 xprp2').
Qed.


(* Definition of the realizer machine *)
Definition sqrt_approx_total_rlzrMtoIR n phi m := match (lt_n_M (@pair B_(cs_nat) _ ((fun (u : unit) => ((2*n).+1)%nat),(mp phi (tpnIR (-2*(Z.of_nat n))%Z)))) (m,tt)) with
                                          | (Some true)  => (Some (ZtoIR 0%Z))
                                          | (Some false) =>
                                            match (scaleM phi m) with
                                              (Some (psi, p))  =>
                                                (Some ((tpnIR p) \* (sqrt_approx_n psi (n+(Z.to_nat p)))))
                                              | _ => None
                                              end
                                          | _ => None
                                               end.

Definition sqrt_approx_total_rlzrM (n : nat) phi mq := match (sqrt_approx_total_rlzrMtoIR n phi mq.1) with
                                                       | (Some psi) => (Some (psi mq.2))
                                                       | _ => None
                                                     end.



Lemma sqrt_approx_rlzrM_is_total n phi (x : IR) : (phi \is_name_of x) -> \Phi_(sqrt_approx_total_rlzrM n phi) \is_total.
Proof.
  move => phin q.
  rewrite /sqrt_approx_total_rlzrM /sqrt_approx_total_rlzrMtoIR /=.
  have psin : (tpnIR (-2*(Z.of_nat n))%Z) \is_name_of (powerRZ 2 (-2 * (Z.of_nat n))%Z) by apply tpnIR_spec.
  case (lt_N_b_term (2*n).+1  phin psin) => m1; case => b1 mprp1.
  case (Rle_or_lt x 0) => xprp.
  - exists I0; exists m1.
    rewrite (mprp1 _ (le_n m1)).
    suff -> : (b1 = true) by trivial.
   have :=  (lt_N_b_correct phin psin (mprp1 _ (le_n m1))).
   case b1 => //.
   move => [H _].
   apply H.
   have -> : (- 2 * (Z.of_nat n))%Z = (- ((Z.of_nat 2)*(Z.of_nat n)))%Z by lia.
   rewrite <- Nat2Z.inj_mul.
   rewrite powerRZ2_neg_pos.
   rewrite (tpmn_half (2*n)).
   suff : (0 <= (/ 2 ^ (2*n).+1)) by lra.
   by apply tpmn_pos.
  case (scaleM_term phin xprp) => m2 m2prp.
  move : (mprp1 _ (Max.le_max_l m1 m2)).
  move : (m2prp (Nat.max m1 m2)).
  case => [| [psi p] psipprp]; first by apply /leP; apply Max.le_max_r.
  case b1 => ltn; first by exists I0; exists (Nat.max m1 m2); rewrite ltn.
  exists ((cleanup \o_f Rmult_rlzrf)  (mp (tpnIR p) (sqrt_approx_n psi (n+(Z.to_nat p)))) q); exists (Nat.max m1 m2).
  by rewrite ltn psipprp /=.
Qed.

Lemma sqrt_approx_search_simpl n phi q m : (ord_search (fun k => (isSome (sqrt_approx_total_rlzrM n phi (k,q)))) m) = (ord_search (fun k => (isSome (sqrt_approx_total_rlzrMtoIR n phi k))) m).
Proof.
  elim m => // m' IH.
  rewrite !osrchS.
  rewrite IH.
  case e : (sqrt_approx_total_rlzrM n phi _) => [p1 |]; case e' : (sqrt_approx_total_rlzrMtoIR n phi _) => [p2 | ] // /=; by move : e; rewrite /sqrt_approx_total_rlzrM e'.
Qed.

Lemma sqrt_approx_use_first_simpl1 n phi m: exists m', forall q, (use_first (sqrt_approx_total_rlzrM n) phi (m,q)) = (sqrt_approx_total_rlzrM n phi (m', q)). 
Proof.
  exists (ord_search (fun k => (isSome (sqrt_approx_total_rlzrMtoIR n phi k))) m) => q.
  rewrite sfrst_osrch.
  by rewrite sqrt_approx_search_simpl.
Qed.

Lemma sqrt_approx_use_first_simpl2 n phi m0 : (isSome ((use_first (sqrt_approx_total_rlzrM n)) phi (m0,0%nat))) -> exists M, ((forall q, (isSome (sqrt_approx_total_rlzrM n phi (M,q)))) /\ forall m',forall q, ((M <= m')%nat -> (use_first (sqrt_approx_total_rlzrM n) phi (m',q)) = (sqrt_approx_total_rlzrM n phi (M,q))) /\ ((m' < M)%nat -> (use_first (sqrt_approx_total_rlzrM n) phi (m',q)) = None)).
Proof.
  case (sqrt_approx_use_first_simpl1 n phi m0) => m M.
  rewrite (M 0%nat) => H.
  set s1 := (fun k => (isSome (sqrt_approx_total_rlzrMtoIR n phi k))).
  have H' : (s1 m).
  - move : H.
    rewrite /s1 /sqrt_approx_total_rlzrM.
    case e : (sqrt_approx_total_rlzrMtoIR _ _ _) => //.
  exists (ord_search s1 m); split => [q | m' q]; first by have := (@osrch_correct s1 m H');rewrite /s1 /sqrt_approx_total_rlzrM; case e : (sqrt_approx_total_rlzrMtoIR _ _ _) => //.
  split => mprp.
  - rewrite sfrst_osrch sqrt_approx_search_simpl -/s1.
    rewrite <- (@osrch_eq s1 _ m' (@osrch_correct s1 _ (@osrch_correct s1 _ H'))) => //.
    by rewrite osrch_osrch.
  rewrite sfrst_osrch.
  rewrite sqrt_approx_search_simpl -/s1.
  rewrite /sqrt_approx_total_rlzrM /=.
  case e :(sqrt_approx_total_rlzrMtoIR _ _ _) => [p | ]//.
  suff /leP : ((ord_search s1 m) <= m')%nat by move /leP : mprp;lia.
  rewrite <- (@osrch_eq s1 m' m); [by apply osrch_le | by rewrite /s1 e |].
  apply /leP.
  move /leP : mprp.
  have /leP := (osrch_le s1 m).
  by lia.
Qed.


(* square root approximation using linear search without speedup *)
Definition sqrt_approx_totalM_slow phi mnq := (sqrt_approx_total_rlzrM mnq.2.1 phi (mnq.1,mnq.2.2)).

(* sqrt approximation with speedups *)
Definition sqrt_approx_totalM phi mnq := (sqrt_approx_totalM_slow phi ((speedup mnq.1 13),(mnq.2.1,(speedup mnq.2.2 13)))).

  
Lemma sqrt_approx_total_rlzrM_spec : \F_(use_first (sqrt_approx_totalM_slow)) \solves ((sqrt_approx_total_seq : (IR ->> (IR \^w)))).
  move => phi x phin dom.
  rewrite <- (sfrst_dom (sqrt_approx_totalM_slow)).
  rewrite /sqrt_approx_totalM_slow.
  split => [|Fq' prp]; first by apply FM_dom; move => [n q];apply (sqrt_approx_rlzrM_is_total n phin).
  suff H : forall (n : nat), exists fan : IR, (fan \from (sqrt_approx_total n x)) /\ ((fun q => (Fq' (n,q))) \is_name_of fan).
  - apply choice in H.
    case H => f fprp.
    exists f.
    split => n; by apply (fprp n).
  move => n.
  set Fq := (fun q => (Fq' (n,q))).
  have psin : (tpnIR (-2*(Z.of_nat n))%Z) \is_name_of (/ 2 ^ (2 * n)%nat).
  - rewrite <- powerRZ2_neg_pos, Nat2Z.inj_mul, <- Z.mul_opp_l.
    by apply tpnIR_spec.
  case (prp (n, 0)%nat) => m0 m0prp.
  rewrite sfrst_osrch /= in m0prp.
  rewrite <- sfrst_osrch in m0prp.
  have m0prp' : (isSome (use_first (sqrt_approx_total_rlzrM n) phi (m0, 0%nat))) by rewrite m0prp.
  case (sqrt_approx_use_first_simpl2 m0prp') => M [Mprp1 Mprp2].
  have ltnn : (lt_n_M (@pair B_(cs_nat) _ ((fun (u : unit) => ((2*n).+1)%nat),(mp phi (tpnIR (-2*(Z.of_nat n))%Z)))) (M,tt)) = (Some true) \/ (lt_n_M (@pair B_(cs_nat) _ ((fun (u : unit) => ((2*n).+1)%nat),(mp phi (tpnIR (-2*(Z.of_nat n))%Z)))) (M,tt)) = (Some false).
  - have := (Mprp1 0%nat).
    rewrite /sqrt_approx_total_rlzrM /sqrt_approx_total_rlzrMtoIR.
    case e: (lt_n_M _) => [b |] //.
    move : e.
    by case b;auto.
  have Fq_prp : forall q, exists p, (sqrt_approx_total_rlzrM n phi (M, q)) = (Some p) /\ (Fq q) = p.
  - move => q.
    have := (Mprp1 q).
    case e : (sqrt_approx_total_rlzrM _ _ _) => [p | ] // _.
    exists p;split => //.
    case (prp (n,q)) => N Nprp.
    rewrite sfrst_osrch /= in Nprp.
    rewrite <- sfrst_osrch in Nprp.
    have := (Mprp2 N q).
    case => H1 H2.
    case mlt : (M <= N)%nat;first by have := Nprp; rewrite (H1 mlt) e; case.
    move /leP : mlt.
    rewrite Nat.nle_gt => /leP mlt.
    by have := (H2 mlt); rewrite Nprp.
  case ltnn => ltn; have lt := (lt_N_b_correct phin psin ltn).
  - exists 0.
    split; first by apply or_introl; split.
    suff p : forall q, (Fq q) = I0.
    + split => [q | N];first by rewrite (p q) /=;lra.
      exists 0%nat => q _.
      rewrite (p q).
      split => //.
      rewrite Rminus_eq_0.
      by apply tpmn_pos.
    move => q.
    case (Fq_prp q) => p [pprp1 pprp2]. 
    move : pprp1.
    rewrite /sqrt_approx_total_rlzrM /sqrt_approx_total_rlzrMtoIR ltn pprp2.
    by case.
  have : exists psi p, (scaleM phi M) = (Some (psi,p)).
  - have := (Mprp1 0%nat).
    rewrite /sqrt_approx_total_rlzrM /sqrt_approx_total_rlzrMtoIR ltn.
    case e : (scaleM _ _) => [[psi p]   | ] // _.
    by exists psi; exists p.
  case => psi; case => p pspr.
  have xgt0 : (0 < x).
  - have [le _] := lt.
    suff : exists u v, not (x+v <= u) /\  (v <= u) by case => u; case => v;lra.
    exists (/ 2 ^ (2 * n)).
    exists (/ 2 ^ (2 * n).+1).
    split => [H |]; first by have := (le H).
    by apply /tpmnP/leP;lia.
  case  (scaleM_correct phin xgt0 pspr) => [y [yprp1 [yprp2 yprp3]]].
  exists ((powerRZ 2 p)*(sqrt_approx_seq y (n+(Z.to_nat p))%nat)).
  split.
  - apply or_intror.
    split => //.
    exists p; exists y; by split.
  have [sqname1 sqname2] := (mul_comp (tpnIR_spec p) (sqrt_approx_n_rlzr_spec (n+(Z.to_nat p)) yprp1 yprp2)).
  split => q.
  - case (Fq_prp q); rewrite /sqrt_approx_total_rlzrM/sqrt_approx_total_rlzrMtoIR ltn pspr => a [aprp ->].
    move : aprp; case => <-.
    by apply sqname1.
  case (sqname2 q) => N Nprp. 
  exists N => k kprp.
  case (Fq_prp k); rewrite /sqrt_approx_total_rlzrM/sqrt_approx_total_rlzrMtoIR ltn pspr => a [aprp ->].
  move : aprp; case => <-.
  by apply (Nprp _ kprp).
Qed.

Lemma sqrt_approx_tot phi (x : IR) : (phi \is_name_of x) -> (\Phi_(sqrt_approx_totalM_slow phi)) \is_total.
Proof.
  move => phin [n q].
  rewrite /sqrt_approx_totalM_slow /=.
  by apply (sqrt_approx_rlzrM_is_total n phin).
Qed.

Definition sqrt_total_rlzr := (\F_limit_eff_rlzrM \o \F_(use_first sqrt_approx_totalM_slow)).

Lemma sqrt_total_correct :  sqrt_total_rlzr \solves (F2MF sqrt)|_(IR_nonneg).
Proof.
   have t := (slvs_tight _ sqrt_as_lim).
   rewrite /sqrt_total_rlzr.
   apply t.
   apply (slvs_tight (slvs_comp F_lim_eff_rlzrM_spec sqrt_approx_total_rlzrM_spec)).
   by apply tight_restr_w.
Qed.

(* We show that a realizer for the sqrt exists *)
Lemma sqrt_approx_slow_f_exists phi (x : IR)  : phi \is_name_of x ->  {psi | exists (y : (IR\^w)),  y \from (sqrt_approx_total_seq x) /\ psi \is_name_of y}.
Proof.
   move => phin.
   have H : \Phi_(use_first sqrt_approx_totalM_slow phi) \is_total.
   - have -> : (use_first sqrt_approx_totalM_slow phi) = (PhiN.use_first (sqrt_approx_totalM_slow phi)) by apply functional_extensionality.
    rewrite <-sfrst_tot.
    by apply (sqrt_approx_tot phin).
  exists (evaluate H).
  case (sqrt_approx_total_rlzrM_spec phin (sqrt_approx_total_seq_is_total x)  ) => _ prp.
  case (prp (evaluate H)) => [| y yprp]; first by apply FM_Phi;apply eval_spec.
  by exists y.
Defined.

Lemma sqrt_slow_f_exists phi (x: IR) : (0 <= x) -> phi \is_name_of x -> {psi | psi \is_name_of (sqrt x)}.
Proof.
  move => xgt0 phin.
  case (sqrt_approx_slow_f_exists phin) => sqapprx prp.
  have H : \Phi_(limit_eff_rlzrM (sqapprx)) \is_total /\  (forall Fq : B_(IR), Fq \from \F_limit_eff_rlzrM sqapprx -> Fq \is_name_of (sqrt x)).
  - case prp => y [yprp1 yprp2].
    case (F_lim_eff_rlzrM_spec yprp2).
    + exists (sqrt x) => n /=.
      rewrite Rabs_minus_sym.
      by apply (sqrt_approx_total_correct xgt0 (yprp1 n)).
    move => H1 H2.
    split => [ | Fq Fqprp]; first by apply FM_dom.   
    case (H2 Fq Fqprp) => y' [y'prp1 y'prp2].
    move : y'prp2.
    suff -> : y' = (sqrt x) by trivial.
    apply sqrt_lim_eff => //.
    by exists y.
  have [H1 H2] := H.
  exists (evaluate H1).
  have := (@eval_spec _ _ _ H1).
  rewrite <-FM_Phi => e.
  by apply (H2 _ e).
Defined.

(* For now, admit the version with  speedups *)
Lemma speedup_admitted phi : \Phi_(use_first sqrt_approx_totalM phi) \is_total. 
Admitted.
Lemma speedup_admitted2 phi x : exists (y : IR\^w), y \from sqrt_approx_total_seq x /\ ((evaluate (speedup_admitted phi)) : B_(IR\^w)) \is_name_of y.
Admitted.

Lemma sqrt_approx_f_exists phi (x : IR)  : phi \is_name_of x ->  {psi | exists (y : (IR\^w)),  y \from (sqrt_approx_total_seq x) /\ psi \is_name_of y}.
Proof.
   move => phin.
   have H : \Phi_(use_first sqrt_approx_totalM_slow phi) \is_total.
   - have -> : (use_first sqrt_approx_totalM_slow phi) = (PhiN.use_first (sqrt_approx_totalM_slow phi)) by apply functional_extensionality.
    rewrite <-sfrst_tot.
    by apply (sqrt_approx_tot phin).
  exists (evaluate (speedup_admitted phi)).
  by apply speedup_admitted2.
Defined.

Lemma sqrt_f_exists phi (x: IR) : (0 <= x) -> phi \is_name_of x -> {psi | psi \is_name_of (sqrt x)}.
Proof.
  move => xgt0 phin.
  case (sqrt_approx_f_exists phin) => sqapprx prp.
  have H : \Phi_(limit_eff_rlzrM (sqapprx)) \is_total /\  (forall Fq : B_(IR), Fq \from \F_limit_eff_rlzrM sqapprx -> Fq \is_name_of (sqrt x)).
  - case prp => y [yprp1 yprp2].
    case (F_lim_eff_rlzrM_spec yprp2).
    + exists (sqrt x) => n /=.
      rewrite Rabs_minus_sym.
      by apply (sqrt_approx_total_correct xgt0 (yprp1 n)).
    move => H1 H2.
    split => [ | Fq Fqprp]; first by apply FM_dom.   
    case (H2 Fq Fqprp) => y' [y'prp1 y'prp2].
    move : y'prp2.
    suff -> : y' = (sqrt x) by trivial.
    apply sqrt_lim_eff => //.
    by exists y.
  have [H1 H2] := H.
  exists (evaluate H1).
  have := (@eval_spec _ _ _ H1).
  rewrite <-FM_Phi => e.
  by apply (H2 _ e).
Defined.

End total_sqrt.
