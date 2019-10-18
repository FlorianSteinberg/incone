From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_rlzrs.
From metric Require Import reals.
Require Import all_cs_base classical_mach.
Require Import Reals Psatz FunctionalExtensionality ClassicalChoice.
Require Import Ibounds IrealsZ.
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

Definition to_pair (d : D) := match d with
                         | Fnan => (0%Z, 1%Z)
                         | (Float m e) => (m, e)
                                end.
                          


Definition midpoint_errI I := (to_pair(I.midpoint I), to_pair(SF2.sub Interval_definitions.rnd_UP 1%Z (I.upper I) (I.lower I))).


Definition make_iter T (rlzrf : T -> names_IR) phi  n (m : Z) := match (rlzrf phi n) with
                                    | (Interval_interval_float.Ibnd u l) =>
                                      match (SF2.sub Interval_definitions.rnd_UP 1%Z u l) with
                                      | (Float m' e) =>
                                        if  (Z.leb e m)  then ((Interval_interval_float.Ibnd u l)) else Interval_interval_float.Inan
                                      | _ => (Interval_interval_float.Inan)
                                      end
                                    | _ => Interval_interval_float.Inan
                                    end.

Definition make_iter2 T (rlzrf : T -> names_IR) phi : names_IR := fun n => (make_iter rlzrf phi n (1)%Z). 
Lemma make_iter_correct T (rlzrf : T -> names_IR) phi  (x : R): (rlzrf phi) \is_name_of x -> (make_iter2 rlzrf phi) \is_name_of x. 
Proof.
  move => phin.
  split.
Admitted.
Definition Rmult_rlzrf' phi  := (make_iter2 Rmult_rlzrf phi).
Definition Rplus_rlzrf' phi  := (make_iter2 Rplus_rlzrf phi).
Definition mp (phi psi : names_IR) := (pair (phi,psi)).
Notation "phi '\*' psi" := ((Rmult_rlzrf' (mp phi psi)) : (names_IR)) (at level 3).
Notation "phi '\+' psi" := ((Rplus_rlzrf' (mp phi psi)) : (names_IR)) (at level 4).
Definition opp_rlzr phi := (Rmult_rlzrf' (mp (FloattoIR (-1)%Z 0%Z) phi)) : (names_IR).
Notation "phi '\-' psi" := ((Rplus_rlzrf' (mp phi (opp_rlzr psi))) : (names_IR)) (at level 4).

Lemma mul_comp phi psi (x y : R) : (phi \is_name_of x) -> (psi \is_name_of y) -> (phi \* psi \is_name_of (x*y)).
Proof.
  move => phin psin.
  suff xyname : (pair (phi,psi)) \is_name_of (x,y).
  - apply make_iter_correct.
    have  :=  (Rmult_rlzr_spec ).
    rewrite F2MF_rlzr => sp.
    by apply (sp _ _ xyname).
    rewrite prod_name_spec.
  by rewrite lprj_pair rprj_pair.
Qed.

Lemma plus_comp phi psi (x y : R) : (phi \is_name_of x) -> (psi \is_name_of y) -> (phi \+ psi \is_name_of (x+y)).
Proof.
  move => phin psin.
  suff xyname : (pair (phi,psi)) \is_name_of (x,y).
  - apply make_iter_correct.
    have  :=  (Rplus_rlzr_spec ).
    rewrite F2MF_rlzr => sp.
    by apply (sp _ _ xyname).
    rewrite prod_name_spec.
  by rewrite lprj_pair rprj_pair.
Qed.

Lemma opp_comp phi (x : R) : (phi \is_name_of x) -> (opp_rlzr phi) \is_name_of -x.
Proof.
  move => phin.
  rewrite /opp_rlzr.
  have -> : (-x = (-1)*x) by lra.
  apply mul_comp; last by apply phin.
  by apply FloattoIR_correct. 
Qed.

Lemma minus_comp phi psi (x y : R) : (phi \is_name_of x) -> (psi \is_name_of y) -> (phi \- psi \is_name_of (x-y)).
Proof.
  move => phin psin.
  have oc := (opp_comp psin).
  suff xyname : (pair (phi,(opp_rlzr psi))) \is_name_of (x,-y).
  - apply make_iter_correct.
    have  :=  (Rplus_rlzr_spec ).
    rewrite F2MF_rlzr => sp.
    by apply (sp _ _ xyname).
    rewrite prod_name_spec.
  by rewrite lprj_pair rprj_pair.
Qed.
Require Import Iextract.

Fixpoint logistic_map_cmp (phi r : names_IR)  N : IR_type  := match N with
                                       | 0%nat => phi
                                       | M.+1 => let P := (memoize_real (logistic_map_cmp phi r M)) in r \* P \* ((FloattoIR 1%Z 0%Z) \- P)
                                                                                                        end.

Definition speed_up_monotonic (phi : names_IR) : names_IR := fun n => (phi (2 ^ n)%nat). 
Definition log_map1 N : names_IR := fun m => logistic_map_cmp (FloattoIR 1%Z (-1)%Z) (FloattoIR 15%Z (-2)%Z) N m.
Definition log_map1_fast N := (speed_up_monotonic (log_map1 N)).
Lemma logistic_map_cmp_is_name phi psi N (x0 r : R) : (phi \is_name_of x0) -> (psi \is_name_of r) -> exists x : R, (representation IR (logistic_map_cmp phi psi N) x).
Proof.
  move => phin psin.
  elim N => [| N' IH]; first by exists x0.
  rewrite /logistic_map_cmp/memoize_real.
  rewrite -/logistic_map_cmp.
  case IH => P Pprop.
  exists (r * P * (1 - P)).
  apply mul_comp.
  - by apply mul_comp.
  by apply minus_comp; try by apply FloattoIR_correct.
Qed.


Definition IR_RQ_rlzrM' := (fun phi neps => IR_RQ_rlzrM (2 ^ neps.1)%nat phi neps.2).
Definition IR2Qmf := \F_(IR_RQ_rlzrM').
Lemma pwr2gt : forall n, (n <= (2 ^ n))%nat.
Proof.
  elim => [ | n IH].
  apply /leP;lia.
  rewrite Nat.pow_succ_r'.
  have /leP := IH => IH'.
  apply /leP.
  have lt1 : (n.+1 <= (2 ^ n).+1)%coq_nat by lia.
  apply /Nat.le_trans.
  apply lt1.
  have -> : (2 * 2^ n)%coq_nat = (2^n + 2 ^ n)%coq_nat by lia.
  suff : (1 <= 2^n)%coq_nat by lia.
  have {1}-> : (1%nat = (2 ^ 0)%nat)%coq_nat by auto.
  apply Nat.pow_le_mono_r; by lia.
Qed.

Lemma logistic_map_in_dom phi psi N (x0 r : R) :(phi \is_name_of x0) -> (psi \is_name_of r) -> (logistic_map_cmp phi psi N) \from dom IR2Qmf.
Proof.
  move => phin psin.
  case (logistic_map_cmp_is_name N phin psin ) => x xprp.
  apply (F_M_realizer_IR_RQ pwr2gt xprp).
  by apply F2MF_dom.
Qed.
Lemma log_map1_in_dom N : \Phi_(IR_RQ_rlzrM' (log_map1 N)) \is_total.
Proof.
  apply FM_dom.
  by apply (logistic_map_in_dom _ (FloattoIR_correct 1%Z (-1)%Z) (FloattoIR_correct 15%Z (-2)%Z)). 
Qed.
Definition log_map_Q N := (evaluate (log_map1_in_dom N)).

Definition logistic_map_mp_rlzr' (N :nat) (p : positive):= log_map_Q N (1#(10 ^ p)).
Extraction "logisticC" cmp_float mantissa_shr logistic_map_mp_rlzr'.
