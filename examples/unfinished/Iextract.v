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
Require ExtrHaskellBasic.
Require ExtrHaskellZInteger.
Require ExtrHaskellNatInteger.
Extraction Language Haskell.

Definition memoize_real (phi : IR_type) := phi.

Definition mantissa_shl m (d : Z) :=
  match d with
    (Z.pos p) => (m * (2 ^ p))%positive |
    _ => 1%positive
  end.

Lemma mantissa_shl_spec m d : (mantissa_shl m d) = (StdZRadix2.mantissa_shl m d).
Proof.
  elim d => [| p//= | p //=]; try by compute.
  rewrite Zaux.iter_pos_nat.
  rewrite <-(Pos2Nat.id p) at 1.
  case (Pos2Nat.is_succ p) => n ->.
  elim n => [| n' ]; first by rewrite /Pos.pow //=;lia.
  move => IH.
  rewrite Zaux.iter_nat_S.
  rewrite Nat2Pos.inj_succ; last by lia.
  rewrite Pos.pow_succ_r.
  rewrite Pos.mul_assoc.
  rewrite <- (Pos.mul_comm 2%positive).
  rewrite <- Pos.mul_assoc, IH. 
  by lia.
Qed.


Definition mantissa_shr  m d (pos : Interval_generic.position) :=
  match d with
  | Z.pos nb => let m' := (Z.div m (2 ^ d)) in
               let mp := (m' * (2 ^ d))%Z in
               match pos with
               | Interval_generic.pos_Eq =>
                 if (Z.eqb mp m)
                 then (m', Interval_generic.pos_Eq)
                 else
                   if (Z.eqb ((2*m'+1)*(2 ^ (d-1))) m)
                   then (m', Interval_generic.pos_Mi)
                   else (m', Interval_generic.pos_Up)
               | _ =>  
                 if (Z.eqb mp m)
                 then (m', Interval_generic.pos_Lo)
                 else (m', Interval_generic.pos_Up)
               end
  | _ => (1%Z, Interval_generic.pos_Eq)
  end.

Definition normalize_mantissa m1 e1 m2 e2 :=
  if (Z.leb e1 e2) then (m1, m2 * (2^ (e2 - e1)))%Z else (m1 * (2 ^ (e1 - e2)), m2)%Z.
Definition cmp_float (f1 f2 : D) := 
  match (f1,f2) with
  | (Fnan, _) => Xund
  | (_, Fnan) => Xund
  | ((Float m1 e1), (Float m2 e2)) =>
    let (d1,d2) := (normalize_mantissa m1 e2 m2 e2) in
    if(Z.eqb d1 d2) then Xeq else
      if(Z.ltb d1 d2) then Xlt else Xgt
  end.

Extract Inlined Constant BigZ.abs => "(Prelude.abs)".
Extract Inlined Constant BigZ.leb => "(Prelude.<=)".
Extract Inlined Constant BigZ.eqb => "(Prelude.==)".
Extract Inlined Constant BigZ.ltb => "(Prelude.<)".
Extract Inlined Constant BigZ.opp => "(Prelude.negate)".
Extract Inlined Constant BigZ.succ => "(Prelude.succ)".
Extract Inlined Constant BigZ.pow_pos => "(Prelude.^)".
Extract Inlined Constant BigZ.pow => "(Prelude.^)".
Extract Inlined Constant BigZ.mul => "(Prelude.*)".
Extract Inlined Constant BigZ.div => "(Prelude.div)".
Extract Inlined Constant Z.abs => "(Prelude.abs)".
Extract Inlined Constant Z.geb => "(Prelude.>=)".
Extract Inlined Constant Z.leb => "(Prelude.<=)".
Extract Inlined Constant Z.eqb => "(Prelude.==)".
Extract Inlined Constant Z.gtb => "(Prelude.>)".
Extract Inlined Constant Z.ltb => "(Prelude.<)".
Extract Inlined Constant Z.opp => "(Prelude.negate)".
Extract Inlined Constant Z.succ => "(Prelude.succ)".
Extract Inlined Constant Z.pow_pos => "(Prelude.^)".
Extract Inlined Constant Z.pow => "(Prelude.^)".
Extract Inlined Constant Z.quotrem => "(Prelude.quotRem)".
Extract Inlined Constant Z.mul => "(Prelude.*)".
Extract Inlined Constant Z.div => "(Prelude.div)".
Extract Inlined Constant Nat.leb => "(Prelude.<=)".
Extract Inlined Constant Nat.ltb => "(Prelude.<)".
Extract Inlined Constant Nat.succ => "(Prelude.succ)".
Extract Inlined Constant Nat.add => "(Prelude.+)".
Extract Inlined Constant Nat.mul => "(Prelude.*)".
Extract Inlined Constant Nat.div => "(Prelude.div)".
Extract Inlined Constant addn => "(Prelude.+)".
Extract Inlined Constant muln => "(Prelude.*)".
Extract Inlined Constant subn => "(\n m -> if (n Prelude.> m) then (n Prelude.- m) else 0)".
Extract Inlined Constant Nat.pow => "(Prelude.^)".
Extract Inlined Constant Nat.divmod => "(Prelude.quotRem)".
Extract Inlined Constant Z.compare => "(Prelude.compare)".
Extract Inlined Constant Pos.leb => "(Prelude.<=)".
Extract Inlined Constant Pos.ltb => "(Prelude.<)".
Extract Inlined Constant Pos.succ => "(Prelude.succ)".
Extract Inlined Constant Pos.mul => "(Prelude.*)".
Extract Inlined Constant Pos.pow => "(Prelude.^)".
Extract Inlined Constant Pos.compare => "(Prelude.compare)".
Extract Inlined Constant StdZRadix2.mantissa_add => "(Prelude.+)".
Extract Inlined Constant StdZRadix2.exponent_add => "(Prelude.+)".
Extract Inlined Constant StdZRadix2.mantissa_sub => "(Prelude.-)".
Extract Inlined Constant StdZRadix2.exponent_sub => "(Prelude.-)".
Extract Inlined Constant StdZRadix2.mantissa_mul => "(Prelude.*)".
Extract Inlined Constant StdZRadix2.mantissa_cmp => "(Prelude.compare)".
Extract Inlined Constant StdZRadix2.exponent_cmp => "(Prelude.compare)".
Extract Inlined Constant SF2.cmp => cmp_float.
Extract Inductive Coq.Init.Datatypes.comparison => "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].
Extract Inlined Constant StdZRadix2.mantissa_digits => num_digits.
Extract Inlined Constant StdZRadix2.mantissa_shl => mantissa_shl.
Extract Inlined Constant StdZRadix2.mantissa_shr => mantissa_shr.

Extract Inlined Constant StdZRadix2.mantissa_shl => "(\n m -> Data.Bits.shiftL n (Prelude.fromIntegral m))".
Extract Inlined Constant StdZRadix2.mantissa_digits => "(\n -> Prelude.toInteger (GHC.Exts.I# (GHC.Integer.Logarithms.integerLog2# n)))".
Extract Inlined Constant memoize_real => "Data.Function.Memoize.memoize".
