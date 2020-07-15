From Coquelicot Require Import Coquelicot.
From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_rlzrs.
From metric Require Import reals.
Require Import all_cs_base classical_mach.
Require Import Reals Psatz FunctionalExtensionality ClassicalChoice.
Require Import axioms all_cs cs_mtrc metric_names hyper_spaces.
From metric Require Import all_metric reals standard Qmetric.
Require Import Ibounds.
Require Import search.
Require Import monotone_machines.
Require Import continuous_machines.
From mathcomp Require Import choice.
From Interval Require Import Interval_tactic.
From Interval Require Import Interval_specific_ops Interval_bigint_carrier Interval_stdz_carrier.
From Interval Require Import Interval_interval_float_full Interval_interval.
From Interval Require Import Interval_xreal.
Import BigN BigZ.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import computable_reals softcomparison magnitude.
Local Open Scope Z_scope.
Import QArith.
Local Open Scope R_scope.

Lemma tpmn_mult_l n m : (/ 2 ^ (n * m)%nat) = ((/ 2 ^ m) ^ n).
Proof.
  rewrite <- powerRZ2_neg_pos, powerRZ_Rpower; last by lra.
  rewrite Nat2Z.inj_mul Zopp_mult_distr_r mult_IZR Rmult_comm.
  rewrite <-Rpower_mult.
  rewrite <- INR_IZR_INZ.
  by rewrite  <- powerRZ_Rpower, Rpower_pow, powerRZ2_neg_pos; [|apply powerRZ_lt;lra |lra].
Qed.

Section heron_method.

(* To approximate sqrt(x) for 0.25 <= x <= 2 we use the Heron method. *)

(* sqrt_approx does n iterations of the Heron method with initial value x0 *)
Definition RS2CS Rc := (Build_continuity_space (representation Rc)).
Coercion RS2CS : computable_reals >-> continuity_space.
Variable (Rc : computable_reals).
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
End  heron_method.

Section scaling.
(* To extend the square root we define a scaling function *)
Definition next_even z := (if Z.even z then (z+2)%Z else (z+1)%Z). 
Definition scale := make_mf (fun x yp => ((/ 4) <= yp.1 <= 2) /\ (powerRZ 4 yp.2)*yp.1 = x).

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

Lemma scale_dom x : (0 < x) <-> (x \from (dom scale)).
Proof.
  split => [prp | [[y p [prp1 <-]]]]; last first.
  apply Rmult_lt_0_compat; last by lra.
  apply powerRZ_lt; lra.
  have [p [y] yprp] := (scale_exists prp).
  by exists (y,p).
Qed.       

Lemma scale_mag x z : (z \from (magnitude x)) -> ((powerRZ 4 (-((next_even z)/2))%Z)*x,((next_even z)/2)%Z) \from (scale x). 
Proof.
  set p := ((next_even z)/2)%Z.
  have p' : (2*p = z+(if (Z.even z) then 2 else 1))%Z.
  - rewrite /p/next_even.
    rewrite <-Z_div_exact_2 => //;case is_even : (Z.even z); try by lia.
    by rewrite (Zmod_even _) Z.even_add is_even /=.
    by rewrite (Zmod_even _) Z.even_succ Zodd_even_bool is_even /=.
  move => [prp1 prp2].
  split => /=; last first.
  - rewrite <-Rmult_assoc.
    rewrite <-powerRZ_add; last by lra.
    have -> : ((p + - p) = 0)%Z by lia.
    by rewrite powerRZ_O;lra.
  have pwrz_simpl z' : (powerRZ 2 (z - z')) <= (powerRZ 2 (-z')%Z)*x <= (powerRZ 2 ((z+2)-z')).
  - rewrite Rmult_comm.
    rewrite powerRZ_add; try by lra.
    rewrite powerRZ_add; try by lra.
    split; by apply Rmult_le_compat_r; [apply powerRZ_le;lra |lra].
  have [s1 s2] := (pwrz_simpl (2*p)%Z).
  suff -> : (powerRZ 4 (-p)%Z) = (powerRZ 2 (-(2*p))%Z).
  - split.
    apply /Rle_trans/s1.
    rewrite p'. 
    rewrite Z.sub_add_distr Z.sub_diag Z.sub_0_l.
    rewrite powerRZ_neg; last by lra.
    case (Z.even z) => /=; by lra.
    apply /Rle_trans.
    apply s2.
    rewrite p'. 
    rewrite Z.sub_add_distr.
    have -> : (z+2 - z = 2)%Z by lia.
    case (Z.even z) => /=; by lra.
  have -> : (4 = 2*2) by lra.
  rewrite powerRZ_mult_distr; last by lra.
  rewrite <-powerRZ_add; last by lra.
  by have -> : ((-p + -p) = (- (2 * p)))%Z by lia.
Qed.
Definition scale_comp := (F2MF (fun zx => ((powerRZ 4 (-zx.1)%Z) * zx.2, zx.1))) \o (F2MF (fun z => ((next_even z)/2)%Z) \o magnitude ** mf_id) \o mf_diag. 
Lemma scale_comp_spec : scale_comp \tightens scale.
Proof.
  rewrite /scale_comp/mf_diag/mf_id/mf.diag.
  move => x dom.
  split.
   apply comp_subs_dom; last by apply F2MF_dom.
   rewrite <-comp_tot_dom; last by apply F2MF_tot.
   rewrite fprd_dom.
   rewrite <-comp_tot_dom; last by apply F2MF_tot.
   move => [x1 x2 [<- <-]].
   split; last by apply F2MF_tot.
   apply magnitude_dom.
   by apply scale_dom.
  rewrite !comp_F2MF.
  move => [y p [[[p' y' [[[[/= m [mprp1 <- _ <- [<- <- _]]]]]]]]]].
  by apply (scale_mag mprp1).
Qed.
End scaling.

Section sqrt_specification.
Variable (Rc : computable_reals).

Definition Rc_pos := (make_subset (fun (x : Rc) => 0 < x)).
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

Definition close_to_zero_check (n : nat) (x :R) := ((2*n).+1, (x, (/ 2 ^ (2*n)))).  
Definition scale_sq n yp := (powerRZ 2 yp.2)*(sqrt_approx_seq yp.1 (n+(Z.to_nat yp.2))).
Definition sqrt_approx_total_comp n := (F2MF (@paib _)) \o ((@mf_cnst R R 0) +s+ (((F2MF (scale_sq n))|_(Rc_pos \x All)) \o scale)) \o (@if_mv R) \o  ((lt_n \o (F2MF (close_to_zero_check n))) ** mf_id) \o (mf_diag).
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

Lemma sq_apprx_tot_cmp_tot n : (sqrt_approx_total_comp n) \is_total.
Proof.
  move => x.
  apply comp_subs_dom; last by rewrite F2MF_dom.
  case => x1 x2 [<- <-].
  apply comp_subs_dom.
  case => b y [[[[m [u v [[<- <- <- [H1 H2] H3 H4]]]]]]].
  rewrite /= in H4.
  rewrite <- H4.
  apply comp_subs_dom; last by rewrite F2MF_dom.
  rewrite /if_mv/uncurry/if_X.
  case => x0.
  move : H2.
  case b => //.
  move => H2.
  have H2' : (x < (/ 2 ^ (2 * n))).
  - suff : not ((/ 2 ^ (2 * n)) <= x) by lra.
    move => H2'.
    by have := (H2 H2').
  case => <-.
  apply comp_subs_dom; first by rewrite F2MF_dom.
  by exists (inl 0).
  move : H1.
  case b => //.
  move => H1.
  have H1' : (0 < x).
  - suff : not (x + (/ 2 ^ (2*n).+1) <= (/ 2 ^ (2*n))).
    rewrite (tpmn_half (2*n)).
    have : (0 < (/ 2 ^ (2*n).+1)) by apply tpmn_lt.
    by lra.
    move => H1'.
    by have := (H1 H1').
  case => <-.
  apply comp_subs_dom; first by rewrite F2MF_dom.
  suff t : x \from (dom (F2MF (scale_sq n) \o scale)).
  case t => k [[/= k' k'prp H]].
  exists (inr k).
  split => //.
  exists k'.
  split; try by apply k'prp.
  split; try by lra.
  move => [q1 q2 [/= prp _]].
  exists (scale_sq n (q1,q2)); split => //.
  split => //.
  by lra.
  apply comp_subs_dom; first by rewrite F2MF_dom.
  by apply scale_dom.
  rewrite fprd_dom.
  split; last by apply F2MF_tot.
  rewrite <-comp_tot_dom; first by apply F2MF_tot.
  apply ltn_tot.
Qed.

Lemma sq_apprx_tot_spec n : (sqrt_approx_total_comp n) \tightens (sqrt_approx_total n).
Proof.
  move => x _.
  rewrite /sqrt_approx_total_comp/mf_id/mf_diag/mf.diag/if_mv/mf_cnst.
  split; first by apply sq_apprx_tot_cmp_tot.
  rewrite !comp_F2MF.
  rewrite /sqrt_approx_total/close_to_zero_check.
  move => y [[[b x0 [[[[[n' [x'1 x'2 [[<- <- <- [H1 H2] ]]]]]]]]]]].
  move => sb1 H3.
  simpl in H3.
  move : H3.
  move => <-.
  rewrite /if_X/uncurry.
  move => [[x1 ]].
  case x1 => x'.
  move : H1 H2.
  case b => /= // H1 H2.
  rewrite /cnst.
  case => [[_]] [[[a' [<- <- ds2 ds3 ds4] | a' [[]] ]]] => //; by auto.
  case; by auto.
  
  move : H1 H2.
  case b => /= // H1 H2.
  rewrite /cnst.
  case; by auto.
  case => [[R1] [[[a [[]] | a [[[[x0' z0' [[H0 R2 [R3' R3] ds1 R4 ds2 ds3 ds4]]]]]]]]] ] => /=.
  rewrite <- R4.
  rewrite <- R3.
  apply or_intror.
  split => //; last first.
  exists z0'; exists x0'; split => //.
  by rewrite R2.
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

Notation lim_eff:= (efficient_limit: (Rc\^w) ->> Rc).
(* We show that the efficient limit of our approximation function is an extension of the square root *)
Lemma sqrt_as_lim :  (lim_eff \o sqrt_approx_total_seq) \tightens ((F2MF sqrt : Rc ->> Rc)|_(make_subset (fun (x : Rc) => 0 <= x))).
Proof.
  apply split_tight.
  - move => x.
    rewrite !dom_restr_spec F2MF_dom.
    case => _ P.
    rewrite <- comp_subs_dom; first by apply sqrt_approx_total_seq_is_total.
    move => yn ynprp.
    exists (sqrt x) => n /=.
    rewrite Rabs_minus_sym.
    have := (ynprp n).
    by apply sqrt_approx_total_correct.
  move => x [t [prp1 prp2] y [xprp1 xprp2]].
  split => // /=.
  by rewrite (sqrt_lim_eff prp1 xprp1).
Qed.


End sqrt_specification.

Section rlzrs.
Variable (Rc : computable_reals).
Arguments partial_function {S} {T}.
Lemma scale_rlzr_spec : {f : partial_function | f \solves (scale : Rc ->> (Rc * cs_Z))}.
Proof.
  have fp : forall f, (f =~= f) by trivial.
  apply cleanup_before_pf.
  apply /cmp_pf_tight; last first.
  apply scale_comp_spec.
  apply diag_pf_exists.
  apply /cmp_pf => //; last first.
  apply /pf_fprd => //; last first.
  apply cleanup_after_pf.
  exists (F2PF (ssrfun.id)).
  rewrite F2PF_spec.
  apply id_rlzr.
  apply /cmp_pf => //; last first.
  apply magnitude_rlzr_spec.
  set rlzr := (fun (phi : B_(cs_Z)) (t : unit) => ((next_even (phi tt))/2)%Z).
  exists (F2PF rlzr). 
  by rewrite F2PF_spec /rlzr F2MF_rlzr => /= phi z <-.
  have comp : (F2MF (fun zx  => ((powerRZ 4 (- zx.1))*zx.2, zx.1))) =~= (((((F2MF (uncurry Rmult)) \o (((F2MF (fun z => (powerRZ 4 z))) \o (F2MF Zopp) ** mf_id))) ** mf_fst  )) \o (@mf_diag (cs_Z*Rc)) : (_ ->> (Rc * cs_Z))). 
  - rewrite /mf_id/mf_fst/mf_diag/mf.diag.
    rewrite F2MF_comp_F2MF.
    rewrite <-!F2MF_fprd.
    rewrite F2MF_comp_F2MF.
    rewrite <-!F2MF_fprd.
    by rewrite F2MF_comp_F2MF /uncurry/fprd =>//.
  apply /cmp_pf; last first.
  apply comp.
  apply diag_pf_exists.
  apply /pf_fprd => //; last first.
  exists (F2PF (@lprj B_(cs_Z) B_(Rc))).
  rewrite F2PF_spec.
  apply fst_rlzr_spec.
  apply /cmp_pf => //; last first.
  apply /pf_fprd => //; last first.
  exists (F2PF (ssrfun.id)).
  rewrite F2PF_spec.
  apply id_rlzr.
  apply /cmp_pf => //; last first.
  set rlzr := (fun (phi : B_(cs_Z)) (t : unit) => (Z.opp (phi tt))).
  exists (F2PF rlzr).
  rewrite F2PF_spec.
  by rewrite F2MF_rlzr /rlzr => phi z /= ->.
  case (F2R Rc) => f2r f2rprp.
  set rlzrf := (fun (phi : B_(cs_Z)) (u : (unit + unit)) => match u with
          | (inl tt) => (1, 2*(phi tt))%Z
           | (inr tt) => (1, 2*(phi tt))%Z
         end).
  have rlzrf_spec : (F2MF rlzrf) \realizes  (fun (z : Z) => (1, 2*z)%Z).
  - rewrite /F2MF_rlzr/rlzrf => phi q /= p [] [z1 z2] [prp1 prp2].
    split => [| Fq Fqprp]; first by exists (rlzrf phi).
    exists (1%Z,2*q)%Z; split => //.
    exists (unpair Fq); split => //; rewrite <-Fqprp.
    by split => // /=; rewrite /rprj /=; rewrite <-p.
  apply /cmp_pf.
  exists (F2PF f2r).
  rewrite F2PF_spec.
  apply f2rprp.
  exists (F2PF rlzrf).
  rewrite F2PF_spec.
  apply rlzrf_spec.
  rewrite F2MF_comp_F2MF /uncurry.
  rewrite <- F2MF_eq => n /=.
  have -> : (4 = 2*2) by lra.
  rewrite powerRZ_mult_distr; last by lra.
  rewrite <-powerRZ_add; last by lra.
  have -> : (n + n = (2*n))%Z by lia.
  by rewrite /=; lra.
  apply (multiplication_rlzr Rc).
Defined.

Definition mp (phi psi : B_(Rc)) := (pair (phi,psi)).
Notation "f '\*' g" := ((partial_composition (partial_composition (projT1 (multiplication_rlzr Rc))  (pprd_rlzrf f g)) (F2PF (fun phi => (pair (phi,phi))))) : (@partial_function B_(Rc) B_(Rc)))   (at level 3).
Notation "f '\+' g" := ((partial_composition (partial_composition (projT1 (addition_rlzr Rc))  (pprd_rlzrf f g)) (F2PF (fun phi => (pair (phi,phi))))) : (@partial_function B_(Rc) B_(Rc)))   (at level 4).
Notation "f '\:' g" := ((partial_composition (partial_composition (projT1 (division_rlzr Rc))  (pprd_rlzrf f g)) (F2PF (fun phi => (pair (phi,phi))))) : (@partial_function B_(Rc) B_(Rc)))   (at level 3).
Notation "<x>" := (F2PF (ssrfun.id : B_(Rc) -> B_(Rc))) (at level 3).
Notation "<x1>" := (F2PF ((@lprj B_(Rc) B_(Rc)) : B_(Rc \*_cs Rc) -> B_(Rc))) (at level 3).
Notation "<x2>" := (F2PF ((@rprj B_(Rc) B_(Rc)) : B_(Rc \*_cs Rc) -> B_(Rc))) (at level 3).
Notation "Fl( x , y )" := (projT1 (Float_constant_pf Rc x y) : (@partial_function B_(Rc) B_(Rc))) (at level 2).
Definition clean := (projT1 (cleanup Rc)).
Lemma sqrt_approx1_inner : {f : partial_function | f \solves (((F2MF (uncurry Rmult)) \o ((@mf_cnst Rc Rc (powerRZ 2 (-1)%Z) \o (@mf_fst Rc  Rc)) ** ((F2MF (uncurry Rplus ) : Rc*Rc ->> Rc) \o ((@mf_snd Rc Rc) ** (Rdiv_mf  : (Rc*Rc ->> Rc)) \o mf_diag))) \o mf_diag)  : _ ->> Rc)}.
Proof.
  have fp : forall f, (f =~= f) by trivial.
  apply cleanup_after_pf.
  apply /cmp_pf => //; last first.
  apply diag_pf_exists.
  apply cleanup_after_pf.
  apply /cmp_pf; last first.
  apply fp.
  apply /pf_fprd => //; last first.
  apply cleanup_after_pf.
  apply /cmp_pf => //; last first.
  apply /cmp_pf => //; last first.
  apply diag_pf_exists.
  apply /pf_fprd => //; last first.
  case (division_rlzr Rc) => div div_spec.
  exists div.
  by rewrite Rdiv_mf_spec.
  apply cleanup_after_pf.
  exists (F2PF ((@rprj B_(Rc) B_(Rc)) : (B_(Rc \*_cs Rc)) -> B_(Rc))).
  rewrite F2PF_spec.
  apply snd_rlzr_spec.
  apply (addition_rlzr Rc).
  apply /cmp_pf => //; last first.
  apply cleanup_after_pf.
  exists (F2PF ((@lprj B_(Rc) B_(Rc)) : (B_(Rc \*_cs Rc)) -> B_(Rc))).
  rewrite F2PF_spec.
  apply fst_rlzr_spec.
  case  (Float_constant_pf Rc 1 (-1)%Z) => rlzr spec.
  apply cleanup_before_pf.
  exists rlzr.
  rewrite /mf_cnst.
  by have -> :(powerRZ 2 (-1)) = 1*(powerRZ 2 (-1)) by lra.
  apply (multiplication_rlzr Rc).
Defined.


Fixpoint sqrt_approx1_rlzr n := match n with
                                 | 0%nat => Fl(1,0)
                                 | (S n') => let P := ((partial_composition clean ((sqrt_approx1_rlzr n'))) : (@partial_function B_(Rc) B_(Rc))) in
                                          (partial_composition (partial_composition (projT1 sqrt_approx1_inner) (pprd_rlzrf <x> P)) (partial_composition (F2PF (fun phi => (pair (phi,phi)))) clean))
                                 end.
Lemma sqrt_approx1_rlzr_spec n : (sqrt_approx1_rlzr n) \solves  (F2MF (sqrt_approx 1 n))|_(Rc_pos Rc).
Proof.
  elim n => [| n' IH] /=.
  - apply /slvs_tight/tight_restr_w.
    suff -> : (F2MF (fun _ : R => 1)) =~= mf_cnst (1 * powerRZ 2 0) by apply (projT2 (Float_constant_pf Rc 1 0)).
    move => x t /=.
    by rewrite /cnst;lra.
    rewrite !pcmp_spec.
    rewrite !F2PF_spec !PF2MF_fprd.
    rewrite !pcmp_spec.
    rewrite !F2PF_spec.
   suff -> : (F2MF (fun x : R => / 2 * (sqrt_approx 1 n' x + x / sqrt_approx 1 n' x)))|_(Rc_pos Rc) =~= ((F2MF (uncurry Rmult)) \o ((@mf_cnst Rc Rc (powerRZ 2 (-1)%Z) \o (@mf_fst Rc  Rc)) ** ((F2MF (uncurry Rplus ) : Rc*Rc ->> Rc) \o ((@mf_snd Rc Rc) ** (Rdiv_mf  : (Rc*Rc ->> Rc)) \o mf_diag))) \o mf_diag) \o ((mf_id ** ((@mf_id Rc) \o (F2MF (sqrt_approx 1 n'))|_((Rc_pos Rc)))))  \o (mf_diag \o mf_id).
    - apply /slvs_comp; last by apply /slvs_comp; [apply diag_rlzr_spec | apply (projT2 (cleanup Rc))].
      apply /slvs_comp; first by apply (projT2 (sqrt_approx1_inner)).
      have -> : (F2MF (fun phipsi => (lprj phipsi, rprj phipsi))) =~= (B_(Rc) \*_cs B_(Rc)).
      + move => x [t1 t2] /=.
        by split => [[<- <-] | [[t1' t2' [<- [<- <-]]]]]; first by exists (lprj x, rprj x).
      rewrite <- (@fprd_rlzr_comp B_(Rc) B_(Rc) B_(Rc) B_(Rc)).
      by apply /prod.fprd_rlzr_spec/slvs_comp/IH/(projT2 (cleanup Rc))/id_rlzr.
    rewrite !comp_id_r !comp_id_l .
    rewrite cnst_comp.
    rewrite F2MF_dom.
    rewrite <- restr_all.
    have -> : (powerRZ 2 (-1)) = (/ 2) by simpl;lra.
    rewrite <-!prd_spec.
    rewrite comp_assoc.
    rewrite <-!prd_spec.
    have -> f g d : (prd_mf f (g|_d)) =~= (prd_mf f g)|_d.
    - move => x [y1 y2].
      by split => /= [[H1 [H2 H3]] | [H1 [H2 H3]]] //.
    rewrite /mf_id.
    rewrite <-prd_f_spec.
   have -> : (F2MF (fun x : R => / 2 * (sqrt_approx 1 n' x + x / sqrt_approx 1 n' x))) =~= (F2MF (uncurry Rmult)) \o (prd_mf (mf_cnst (/ 2)) (F2MF (fun x => (sqrt_approx 1 n' x + x / sqrt_approx 1 n' x)))).
    - rewrite /mf_cnst.
      rewrite <-!prd_f_spec.
      rewrite F2MF_comp_F2MF.
      by apply F2MF_eq.
    have -> f g d : (f \o g)|_d =~= (f \o g|_d).
    -rewrite <-comp_id_restr.    
     rewrite <-(comp_id_restr g).
     by rewrite comp_assoc.
    rewrite !comp_assoc.
    have P f g h : (f =~= g) -> (h \o f =~= h \o g) by move => ->.
    apply P.
    rewrite <-comp_assoc.   
    rewrite /mf_cnst/mf_diag.
    rewrite <-prd_f_spec.
    rewrite /prd /=.
    rewrite comp_F2MF.
    move => x [y1 y2].
    split => [[xgt0 [<- <- ]]|].
    split.
    exists (x, sqrt_approx 1 n' x).
    split => //.
    split => //.
    split => //.
    simpl.   
    exists (sqrt_approx 1 n' x, (x / (sqrt_approx 1 n' x))); try by split => //.
    split => //.
    split => //.
    split => //.
    suff : (0 < sqrt_approx 1 n' x) by lra.
    simpl in xgt0.
    apply (@sqrt_approx_gt_0 x 1 n'); try by lra.
    by rewrite F2MF_dom.
    move => [x1 x2 [_ [<- <- ]]].
    simpl.
    exists (/2, ((sqrt_approx 1 n' x) + x / (sqrt_approx 1 n' x))).
    split => //.
    split; last by rewrite F2MF_dom.
    exists ((sqrt_approx 1 n' x), (x / (sqrt_approx 1 n' x))).
    split => //.
    split => //.
    split => //.
    suff : 0 < (sqrt_approx 1 n' x) by lra.
    apply sqrt_approx_gt_0; try by lra.
    by suff : (0 < x) by lra.
  case => [[[x0 x1 [[Hp [<- <- [/= <- [[[a b [[/= <- [H2 -> <- _ _]]]]]]]] ]]]]].
  by split => //. 
Qed.

Lemma sqrt_approx_rlzr (n : nat) : {f : partial_function | f \solves (F2MF (fun (x : Rc) => (sqrt_approx_seq x n) : Rc))|_(Rc_pos Rc)}.
Proof.
  apply /cleanup_after_pf.
  exists (sqrt_approx1_rlzr (Nat.log2 n.+1).+1).
  by apply sqrt_approx1_rlzr_spec.
Defined.

Lemma sqrt_approx_comp_inner (n : nat) : {f : partial_function | f \solves ((F2MF (fun xnz : sequence_in Rc * Z => xnz.1 (n + Z.to_nat xnz.2)%nat) \o
        (make_mf
           (fun (x : Rc) (yn : sequence_in Rc) =>
             forall n0 : nat, yn n0 \from ((fun n1 : nat => (F2MF (sqrt_approx_seq^~ n1))|_(Rc_pos Rc)) n0) x) **
         F2MF ssrfun.id)) : ((Rc * cs_Z) ->> Rc))}.
Proof.
  have fp : forall f, (f =~= f) by trivial.
  apply /cleanup_after_pf.
  apply /cmp_pf => //.
  set rlzr := F2PF (fun (phi : B_(Rc\^w \*_cs cs_Z)) (q : Q_(Rc)) => ((lprj phi) (((n+(Z.to_nat (rprj phi tt)))%nat), q))).
  have rlzr_spec : (rlzr \realizes (fun xnz => (xnz.1 (n+(Z.to_nat xnz.2))%nat))).
  - rewrite /rlzr F2PF_spec F2MF_rlzr => phi [xn z] /prod_name_spec [/= phin1 ->].
    by apply phin1.
  exists rlzr.
  apply rlzr_spec.
  apply /pf_fprd => //.
  apply /cleanup_before_pf.
  apply /seq_pf => //.
  apply sqrt_approx_rlzr.
  exists (F2PF (ssrfun.id : B_(cs_Z) -> B_(cs_Z))).
  rewrite F2PF_spec.
  apply id_rlzr.
Defined.

Lemma sqrt_approx_comp_inner' : {f : partial_function | f \solves ((F2MF (fun z => (powerRZ 2 z))) \o (F2MF snd) : ((Rc * cs_Z) ->> (Rc)))}.
Proof.
  have fp : forall f, (f =~= f) by trivial.
  apply /cleanup_after_pf.
  apply /cmp_pf => //.
  apply /cleanup_after_pf.
  case (F2R Rc) => f2r /= f2rprp.
  set rlzr := F2PF ((fun (phi : B_(cs_Z)) => (f2r (@pair B_(cs_Z) B_(cs_Z) (Z2csZ 1,phi))) : (B_(Rc)))).
  have rlzr_spec : rlzr \realizes (fun (z : Z) => (powerRZ 2 z)).
  - rewrite /rlzr F2PF_spec F2MF_rlzr => phi z phin.
    case (f2rprp (@pair B_(cs_Z) B_(cs_Z) (Z2csZ 1,phi)) (1,z)%Z) =>  /=.
    exists (Z2csZ 1, phi); split => //.
    rewrite /uncurry.
    exists (powerRZ 2 z) => /=.
    by lra.
    move => [f fprp] Fqprp.
    case (Fqprp f fprp) => F [Fp1 Fp2].
    rewrite fprp.
    rewrite /uncurry/= Rmult_1_l in Fp1.
    by rewrite Fp1.
  exists rlzr.
  apply rlzr_spec.
  exists (F2PF ((@rprj B_(Rc) B_(cs_Z)) : (B_(Rc \*_cs cs_Z)) -> B_(cs_Z))).
  rewrite F2PF_spec.
  apply snd_rlzr_spec.
Defined.
Lemma sqrt_approx_comp_inner'' (n : nat): {f : partial_function | f \solves (((F2MF (uncurry Rmult)) \o (((F2MF (fun z => (powerRZ 2 z))) \o (F2MF snd)) ** ((F2MF (fun xnz : sequence_in Rc * Z => xnz.1 (n + Z.to_nat xnz.2)%nat) \o
        (make_mf
           (fun (x : Rc) (yn : sequence_in Rc) =>
            forall n0 : nat, yn n0 \from ((fun n1 : nat => (F2MF (sqrt_approx_seq^~ n1))|_(Rc_pos Rc)) n0) x) **
         F2MF ssrfun.id))))) : ((Rc * cs_Z) * (Rc * cs_Z) ->> Rc))}.
Proof.
  have fp : forall f, (f =~= f) by trivial.
  apply /cleanup_after_pf.
  apply /cmp_pf => //.
  apply (multiplication_rlzr Rc).
  apply /pf_fprd => //.
  apply /cleanup_after_pf.
  apply sqrt_approx_comp_inner'.
  apply /cleanup_after_pf.
  apply sqrt_approx_comp_inner.
  apply fp.
Defined.

Lemma sqrt_approx_comp_rlzr (n : nat) : {f : partial_function |
  f \solves (F2MF ((fun yp : R * Z => powerRZ 2 yp.2 * sqrt_approx_seq yp.1 (n + Z.to_nat yp.2)) : ((Rc * cs_Z) -> (Rc))))|_((Rc_pos Rc) \x All )}.
Proof.
  have fp : forall f, (f =~= f) by trivial.
  apply /cleanup_after_pf.
  rewrite /sqrt_approx_seq.
  apply /cmp_pf.
  apply /cleanup_after_pf.
  apply (sqrt_approx_comp_inner'' n).
  apply diag_pf_exists.
  rewrite /mf_diag/mf.diag/uncurry !F2MF_comp_F2MF.
  rewrite !comp_F2MF.
  move => [x z] p /=.
  split; last first.
  move => [H1 _].
  case H1 => [[a b [[<-[[[xn z0 [[H0 [<- [<- _ <-] ]]]]] ]]]]].
  split; first by split; [apply (H0 n) | ].
  have := (H0 (n + Z.to_nat z)%nat) => [[_ <-]].
  by rewrite /sqrt_approx_seq /=.
  move => [H0 H1].
  split => // /=; last by move => [a b _]; rewrite F2MF_dom.
  exists (powerRZ 2 z, (sqrt_approx_seq x (n+Z.to_nat z))).
  split => //.
  split => //.
  split; last by rewrite F2MF_dom.
  exists ((sqrt_approx_seq x), z).
  split => //; try by rewrite F2MF_dom.
  split => //.
  move => n0; split => //.
  by apply H0.
Defined.

Lemma close_to_zero_check_const (n : nat) : {f : partial_function | f \solves (((F2MF (cnst (2 * n).+1) ** (F2MF ssrfun.id ** (F2MF (fun n0 : nat => / 2 ^ n0) \o F2MF (cnst (2 * n)%nat))))) : (Rc * (Rc * Rc) ->> (nat * (Rc * Rc))))}. 
  have fp : forall f, (f =~= f) by trivial.
  apply /pf_fprd => //.
  apply /cleanup_before_pf.
  apply /constant_pf_spec.
  have np : (cs_nat (nat2csN ((2*n).+1)) ((2*n).+1)) by auto.
  apply np.
 apply /pf_fprd => //.
  apply /cleanup_after_pf.
  exists (F2PF (ssrfun.id)).
  rewrite F2PF_spec.
  apply id_rlzr.
  apply /cleanup_after_pf.
  apply /cmp_pf => //.
  apply /cleanup_after_pf.
  apply tpmn_rlzr.
  apply /constant_pf_spec.
  have np : (cs_nat (nat2csN ((2*n))) ((2*n)%nat)) by auto.
  apply np.
Defined.

Lemma close_to_zero_check_diag  : {f : partial_function | f \solves (((F2MF ssrfun.id ** mf_diag) \o mf_diag) : (Rc ->> (Rc * (Rc * Rc))))}. 
Proof.
  have fp : forall f, (f =~= f) by trivial.
  apply /cleanup_before_pf.
  apply /cmp_pf => //.
  apply /pf_fprd => //.
  apply /cleanup_after_pf.
  exists (F2PF (ssrfun.id)).
  rewrite F2PF_spec.
  apply id_rlzr.
  apply /cleanup_before_pf.
  apply diag_pf_exists.
  apply /cleanup_before_pf.
  apply diag_pf_exists.
Defined.

Lemma close_to_zero_check_rlzr (n : nat) : {f : partial_function | f \solves ((F2MF (close_to_zero_check n)) : (Rc ->> (cs_nat * (Rc * Rc))))}.
Proof.
  have fp : forall f, (f =~= f) by trivial.
  apply /cleanup_before_pf.
  rewrite /close_to_zero_check.
  apply /cmp_pf =>//.
  apply (close_to_zero_check_const n).
  apply /cleanup_before_pf.
  apply close_to_zero_check_diag.
  rewrite /mf_diag/mf.diag/cnst !F2MF_comp_F2MF.
  rewrite <- !F2MF_fprd.
  by rewrite !F2MF_comp_F2MF /fprd /=.
Defined.

Lemma sqrt_approx_total_rlzr (n : nat) : {f : partial_function | f \solves ((sqrt_approx_total n) : (Rc ->> Rc))}.
Proof.
  have fp : forall f, (f =~= f) by trivial.
  apply /cleanup_after_pf.
  apply /cleanup_before_pf.
  apply /cmp_pf_tight; last first.
  apply (sq_apprx_tot_spec).
  apply diag_pf_exists.
  apply /cleanup_after_pf.
  apply /cmp_pf => //; last first.
  apply /pf_fprd => //; last first.
  apply /cleanup_after_pf.
  exists (F2PF (ssrfun.id)).
  rewrite F2PF_spec.
  apply id_rlzr.
  apply /cmp_pf => //; last first.
  apply /cleanup_before_pf.
  apply close_to_zero_check_rlzr.
  apply ltn_rlzr.
  apply /cmp_pf => //; last first.
  exists (F2PF (@if_rlzrf Rc)).
  rewrite F2PF_spec.
  apply if_rlzrf_spec.
  apply /cleanup_after_pf.
  apply /cmp_pf => //; last first.
  apply /sum_pf => //; last first.
  apply /cleanup_before_pf.
  apply /cmp_pf => //; last first.
  apply scale_rlzr_spec.
  apply /cleanup_after_pf.
  rewrite /scale_sq.
  apply sqrt_approx_comp_rlzr.
  apply /cleanup_after_pf.
  apply int_constant_pf.
  apply paib_pf_exists.
Defined.

Lemma sqrt_rlzr : {f : partial_function | f \solves (F2MF (sqrt : Rc -> Rc))|_(make_subset (fun (x : Rc) => 0 <= x))}.
Proof.
  apply /cleanup_after_pf.
  apply /cleanup_before_pf.
  apply /cmp_pf_tight; last first.
  apply sqrt_as_lim.
  apply /seq_pf.
  apply sqrt_approx_total_rlzr.
  case (limit_rlzr Rc) => l lp.
  by exists l.
Defined.


Lemma sqrt_rlzr_dom phi x : (0 <= x) -> (phi \is_name_of x) -> (phi \from (dom (projT1 sqrt_rlzr))).
Proof.
  move => xgt phin.
  apply (projT2 sqrt_rlzr phi x phin). 
  by exists (sqrt x).
Qed.  
End rlzrs.
