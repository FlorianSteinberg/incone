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


Definition make_iter T (rlzrf : T -> IR_type) phi  (n : nat) (m : Z) := match (rlzrf phi n) with
                                    | (Interval_interval_float.Ibnd u l) =>
                                      match (SF2.sub Interval_definitions.rnd_UP 1%Z u l) with
                                      | (Float m' e) =>
                                        if  (Z.leb e m)  then ((Interval_interval_float.Ibnd u l)) else Interval_interval_float.Inan
                                      | _ => (Interval_interval_float.Inan)
                                      end
                                    | _ => Interval_interval_float.Inan
                                    end.

Definition Rmult_rlzrf' phi n := (make_iter Rmult_rlzrf phi n (1)%Z).
Definition Rplus_rlzrf' phi n := (make_iter Rplus_rlzrf phi n (1)%Z).
Notation "phi '\*' psi" := (Rmult_rlzrf' (IR2 phi psi)) (at level 3).
Notation "phi '\+' psi" := (Rplus_rlzrf' (IR2 phi psi)) (at level 4).
Notation "phi '\-' psi" := (Rplus_rlzrf' (IR2 phi (Rmult_rlzrf' (IR2 (FloattoIR (-1)%Z 0%Z) psi)) )) (at level 4).

Require Import Iextract.

Fixpoint logistic_map_cmp (phi r : (nat -> Interval_interval_float.f_interval (s_float Z Z)))  N : (nat -> Interval_interval_float.f_interval (s_float Z Z))  := match N with
                                       | 0%nat => phi
                                       | M.+1 => let P := (memoize_real (logistic_map_cmp phi r M)) in r \* P \* ((FloattoIR 1%Z 0%Z) \- P)
                                                                                                        end.
Definition logistic_map_cmp1 xrN n := (logistic_map_cmp xrN.1 xrN.2.1 xrN.2.2 n).
Definition logmap_iter := (make_iter logistic_map_cmp1).
Definition log_map1 N := logmap_iter ((FloattoIR 1%Z (-1)%Z),((FloattoIR 15%Z (-2)%Z),N)).
Compute (log_map1 10%nat 20%nat (-1)%Z). 
Definition log_map_Q N n := (IR_RQ_M n (fun m => (log_map1 N m (-1)%Z))).

Definition logistic_map_mp_rlzr' (N :nat) (n :nat) (p : positive):= log_map_Q N n (1#(10 ^ p)).

Compute (logistic_map_mp_rlzr' 10%nat 40%nat 10).

 
Extraction "logisticC" cmp_float mantissa_shl mantissa_shr logistic_map_mp_rlzr'.
