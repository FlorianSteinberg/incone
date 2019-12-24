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
Require Import sqrt.
Local Open Scope R_scope.

Definition QtoIR' q := (fun n => (QtoIR (nat2p n) q)) : B_(IR).

Lemma QtoIR'_correct q :((QtoIR' q) \is_name_of ((Qreals.Q2R q) : IR)).
Proof.
  split => n; first by apply QtoIR_correct.
  Search _ QtoIR.
  case (powerRZ_bound (Qreals.Q2R q)) => K [Kprp1 Kprp2].
  have Kprp3 : (1 < K+2+(Z.of_nat n))%Z by lia.
  apply IZR_lt in Kprp3.
  suff : exists (z : Z),(1 < z) /\ forall (k : Z), (z <= k ) -> (diam (QtoIR k q)) <= (powerRZ 2 (-(Z.of_nat n))%Z).
  - case => z [zprp1 zprp2].
    exists (Z.to_nat z).
    move => k kprp.
    split; first by apply QtoIR_bounded.
    rewrite /QtoIR'.
    have := (zprp2 (Z.of_nat k)).
    rewrite powerRZ2_neg_pos.
    move => H.
    have e : (z <= Z.of_nat k).
    rewrite <- (Z2Nat.id z); last by apply le_IZR;lra.
    apply IZR_le.
    apply inj_le.
    by apply /leP.
    have := (H e).
    suff -> : (Z.of_nat k) = (nat2p k) by auto.
    have : (Z.to_nat 1 < Z.to_nat z)%coq_nat by apply Z2Nat.inj_lt; by (try apply le_IZR; try apply lt_IZR;lra).
    move /leP : kprp.
    rewrite /nat2p.
    case k => [| k' _ _]; first by lia.
     by rewrite <- Pos.of_nat_succ, Zpos_P_of_succ_nat;lia.
  exists ((K+2+(Z.of_nat n))%Z).
  split => // k kprp.
  Search _ QtoIR.
  have p : (1 < k)%Z by apply lt_IZR; lra.
  apply /Rle_trans.
  apply (QtoIR_diam p Kprp2).
  rewrite !powerRZ_Rpower; try by lra.
  apply Rle_Rpower; try by lra.
  apply IZR_le.
  apply le_IZR in kprp.
  by lia.
Qed.

Lemma sqrtq_exists  (n : nat) m : {psi | psi \is_name_of (sqrt (Qreals.Q2R  ((Z.of_nat n) # m)))}.
Proof.
  have p : (0 <= (Qreals.Q2R ((Z.of_nat n) # m))).
  - rewrite /Qreals.Q2R /=.
    by apply Rmult_le_pos;[apply IZR_le;lia | apply Rlt_le;apply Rinv_0_lt_compat;apply IZR_lt;lia].
  apply (sqrt_f_exists p ((QtoIR'_correct ((Z.of_nat n) # m)))).
Defined.

Definition sqrtq n m := (projT1 (sqrtq_exists n m)).
Lemma IR_RQ_RlzrM'_dom phi (x : IR) : (phi \is_name_of x) -> \Phi_(IR_RQ_rlzrM' phi) \is_total.
Proof.
  move => phin.
  apply FM_dom.
  rewrite /IR_RQ_rlzrM' /=.
  apply (F_M_realizer_IR_RQ (speedup_gt _) phin).
  by exists x.
Qed.

Lemma sqrtfun_in_dom n m : \Phi_(IR_RQ_rlzrM' (sqrtq n m)) \is_total.
Proof.
  rewrite /sqrtq.
  by apply (IR_RQ_RlzrM'_dom (projT2 (sqrtq_exists n m))).
Qed.

Definition sqrtqq n m := (evaluate (sqrtfun_in_dom n m)).
Definition sqrt2' a b (p : BinPos.positive):= (sqrtqq a b (1#(10 ^ p))).
Definition qtoPair q := match q with
                          (q1 # q2) => (q1, q2)
                          end.
Extraction "sqrt2" cmp_float mantissa_shr sqrt2'.
