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
From Interval Require Import Interval_tactic.
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


Definition make_iter T (rlzrf : T -> names_IR) phi  m  := (fun n => match (rlzrf phi n) with
               | (Interval_interval_float.Ibnd l u) =>
                   if  (I.F'.le (SF2.sub_exact u l) (Float 1%Z (- (Z.of_nat m))%Z))
                   then ((Interval_interval_float.Ibnd l u))
                   else Interval_interval_float.Inan
                | _ => Interval_interval_float.Inan
               end) : names_IR.

Definition make_iter2 T (rlzrf : T -> names_IR) phi : names_IR := fun n => (make_iter rlzrf phi 1 n).
Lemma bounded_non_nan I : (bounded I) -> exists u l, (u <> Fnan) /\ (l <> Fnan) /\ I = (Interval_interval_float.Ibnd u l).
  rewrite /bounded.
  move => bnd.
  case e: I => [| l u]; first by rewrite e in bnd. 
  exists l; exists u.
  case uprp: u => [| mnt exp]; first by rewrite e uprp andb_false_r in bnd.
  case lprp: l => [| mnt' exp']; first by rewrite e lprp andb_false_l in bnd.
  split; [| split]; by auto.
Qed.

Lemma make_iter_correct T (rlzrf : T -> B_(IR)) m phi  (x : R): (rlzrf phi) \is_name_of x -> ((make_iter rlzrf phi m) : B_(IR)) \is_name_of x. 
Proof.
  move => [phin1 phin2].
  split => n.
  - rewrite /make_iter2 /make_iter.
    case R: (rlzrf phi n) => [| l u];first by auto.
    case (I.F'.le (SF2.sub_exact u l) (Float 1%Z (- (Z.of_nat m))%Z)); last by auto.
    by rewrite <-R; apply phin1.
  case (phin2 (max n m)) => N Nprp.
  exists N => k kprp.
  rewrite /make_iter. 
  have [bnd diam] := (Nprp k kprp).
  have [l [u [P1 [P2 P3]]]] := (bounded_non_nan bnd).
  rewrite P3 /=.
  have H1 :  (/ 2 ^ (max n m)) <= (/ 2 ^ m) by apply /tpmnP; apply /leP; apply Nat.le_max_r.
  have H2 :  (/ 2 ^ (max n m)) <= (/ 2 ^ n) by apply /tpmnP; apply /leP; apply Nat.le_max_l.
  have -> : (I.F'.le (SF2.sub_exact u l) (Float 1%Z (- (Z.of_nat m))%Z))=true.
  - rewrite /I.F'.le SF2.cmp_correct.
    rewrite SF2.sub_exact_correct.
    rewrite /Xsub.
    rewrite /Xcmp.
    case e:  u; case e':l; try by auto.
    rewrite !D2R_SF2toX;rewrite <-e, <-e'.
    rewrite P3 /= in diam.
    rewrite D2R_Float.
    rewrite powerRZ2_neg_pos Rmult_1_l.
     case cmp : (Raux.Rcompare (D2R u-D2R l) (/2 ^ m)); try by auto.
     + by apply Raux.Rcompare_Gt_inv in cmp;lra.
  rewrite P3 /= in diam.
  split; first by case e : l;case e' : u; auto.
  by simpl;lra.
Qed.

Definition Rmult_rlzrf' phi  := (make_iter2 Rmult_rlzrf phi).
Definition Rplus_rlzrf' phi  := (make_iter2 Rplus_rlzrf phi).
Definition Rdiv_rlzrf' phi  := (make_iter2 Rdiv_rlzrf phi).
Definition Rminus_rlzrf' phi  := (make_iter2 Rminus_rlzrf phi).

Definition mp (phi psi : names_IR) := (pair (phi,psi)).
Notation "phi '\*' psi" := ((Rmult_rlzrf' (mp phi psi)) : (names_IR)) (at level 3).
Notation "phi '\+' psi" := ((Rplus_rlzrf' (mp phi psi)) : (names_IR)) (at level 4).
Notation "phi '\:' psi" := ((Rdiv_rlzrf' (mp phi psi)) : (names_IR)) (at level 4).
Definition opp_rlzr phi := (Rmult_rlzrf' (mp (FloattoIR (-1)%Z 0%Z) phi)) : (names_IR).
Notation "phi '\-' psi" := ((Rminus_rlzrf' (mp phi psi)) : (names_IR)) (at level 4).

Lemma mul_comp (phi psi : B_(IR))  (x y : R) : (phi \is_name_of x) -> (psi \is_name_of y) -> (((phi \* psi) : B_(IR)) \is_name_of (x*y)).
Proof.
  move => phin psin.
  suff xyname : (pair (phi,psi) : B_(IR \*_cs IR)) \is_name_of (x,y).
  - apply make_iter_correct.
    have  :=  (Rmult_rlzr_spec ).
    rewrite F2MF_rlzr => sp.
    by apply (sp _ _ xyname).
    rewrite prod_name_spec.
  by rewrite lprj_pair rprj_pair.
Qed.

Lemma plus_comp (phi psi : B_(IR)) (x y : R) : (phi \is_name_of x) -> (psi \is_name_of y) -> (((phi \+ psi) : B_(IR)) \is_name_of (x+y)).
Proof.
  move => phin psin.
  suff xyname : (pair (phi,psi) : B_(IR \*_cs IR)) \is_name_of (x,y).
  - apply make_iter_correct.
    have  :=  (Rplus_rlzr_spec ).
    rewrite F2MF_rlzr => sp.
    by apply (sp _ _ xyname).
    rewrite prod_name_spec.
  by rewrite lprj_pair rprj_pair.
Qed.

Lemma opp_comp phi (x : R) : (phi \is_name_of x) -> ((opp_rlzr phi) : B_(IR)) \is_name_of -x.
Proof.
  move => phin.
  rewrite /opp_rlzr.
  have -> : (-x = (-1)*x) by lra.
  apply mul_comp; last by apply phin.
  by apply FloattoIR_correct. 
Qed.

Lemma minus_comp phi psi (x y : R) : (phi \is_name_of x) -> (psi \is_name_of y) -> (((phi \- psi) : B_(IR)) \is_name_of (x-y)).
Proof.
  move => phin psin.
  have oc := (opp_comp psin).
  suff xyname : (pair (phi,psi) : B_(IR \*_cs IR)) \is_name_of (x,y).
  - apply make_iter_correct.
    have  :=  (Rminus_rlzr_spec ).
    rewrite F2MF_rlzr => sp.
    by apply (sp _ _ xyname).
    rewrite prod_name_spec.
  by rewrite lprj_pair rprj_pair.
Qed.
Lemma div_comp phi psi (x y : R) : (y <> 0) -> (phi \is_name_of x) -> (psi \is_name_of y) -> (((phi \: psi) : (B_(IR))) \is_name_of (x/y)).
Proof.
  move => yneg0 phin psin.
  suff xyname : (pair (phi,psi) : B_(IR \*_cs IR)) \is_name_of (x,y).
  - apply make_iter_correct.
    have  :=  (Rdiv_rlzr_spec ).
    rewrite F2MF_slvs => sp.
    case (sp _ _  xyname) => [| xy [[_ /= xy_prop] P]]; first by exists (x/y).
    rewrite <- xy_prop.                                                              
    by apply P.                                                    
  rewrite prod_name_spec.
  by rewrite lprj_pair rprj_pair.
Qed.
Require Import Iextract.

Fixpoint logistic_map_cmp (phi r : names_IR)  N : IR_type  := match N with
                                       | 0%nat => phi
                                       | M.+1 => let P := (memoize_real (logistic_map_cmp phi r M)) in r \* P \* ((FloattoIR 1%Z 0%Z) \- P)
                                                                                                        end.

Definition log_map1 N : names_IR := fun m => logistic_map_cmp (FloattoIR 1%Z (-1)%Z) (FloattoIR 15%Z (-2)%Z) N m.

Fixpoint pow n phi  := match n with
                      | 0%nat => (FloattoIR 1%Z 0%Z)
                      | n'.+1 => phi \* (pow n' phi)
                      end.

Fixpoint slowdown (phi : B_(IR)) m := match m with
                           | 0%nat => phi
                           | m'.+1 => (FloattoIR 1%Z 0%Z) \* (slowdown phi m')
                           end.

Definition pow_mu (phi : B_(IR)) (nm : nat * nat) := [:: nm.2].

Lemma pow_mu_is_mod : pow_mu \modulus_function_for (F2M (pow 100)).
Admitted.
Lemma pow_mu_is_mod_mod : pow_mu \modulus_function_for pow_mu.
Admitted.
Check construct_associate.
Lemma nat_eq_dec : forall (n m :nat), decidable (n = m).
Proof.
apply eqT_eqdec.
Defined.
Definition ass := (construct_associate.psi_FM (@Interval_interval_float.Inan (s_float Z Z):replies IR) 0%nat pow_mu (F2M (pow 50)) ).
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

Definition zero_seq nm := ((FloattoIR 1%Z (-Z.of_nat nm.1)%Z) nm.2). 
Definition lim := \F_limit_eff_rlzrM.
Definition speedup n s := (2 ^ (n+s))%nat.

Lemma speedup_gt s n : (n <= (speedup n s))%nat.
Proof.
  rewrite /speedup.
  elim n  => [ | n' IH]; first by apply /leP;lia.
  rewrite /addn /addn_rec.
  have -> : ((n'.+1 + s) = ((n'+s).+1))%coq_nat by rewrite /addn /addn_rec;lia.
  rewrite Nat.pow_succ_r'.
  have /leP := IH => IH'.
  apply /leP.
  have lt1 : (n'.+1 <= (2 ^ (n'+s)).+1)%coq_nat by lia.
  apply /Nat.le_trans.
  apply lt1.
  have -> : (2 * 2^ (n'+s))%coq_nat = (2^(n'+s) + 2 ^ (n'+s))%coq_nat by lia.
  suff : (1 <= 2^(n'+s))%coq_nat by lia.
  have {1}-> : (1%nat = (2 ^ 0)%nat)%coq_nat by auto.
  apply Nat.pow_le_mono_r; by lia.
Qed.

Definition IR_RQ_rlzrM' := (fun phi neps => IR_RQ_rlzrM (speedup neps.1 8) phi neps.2).
Canonical eqQ : eqType.
  apply (@Equality.Pack Q).
  apply eqdec_eqClass => q q'.
  case q => m n; case q' => m' n'.
  case (Z.eq_dec m m') => e1; case (Pos.eq_dec n n') => e2; try by right;case.
  by rewrite e1 e2;auto.
Defined.
Definition one_half := (FloattoIR 1%Z (-1)%Z).
Fixpoint sqrt_approx x0 n x := match n with
                               | 0%nat => x0
                               | (S n') => let P := (sqrt_approx x0 n' x) in
                                          (/ 2) * (P + (x / P))
                               end.         
Fixpoint sqrt_approx_rlzr phi0 n phi := match n with
                                 | 0%nat => phi0 
                                 | (S n') => let P := (memoize_real (sqrt_approx_rlzr phi0 n' phi)) in
                                          one_half \* (P \+ (phi \: P))
                                 end : B_(IR).

Definition two := (FloattoIR 1%Z 1%Z).
Definition one := (FloattoIR 1%Z 0%Z).

Lemma one_describes_one : (one \is_name_of 1).
Proof.
  suff <- : (D2R (Float 1%Z 0%Z)) = 1 by apply FloattoIR_correct.
  by rewrite D2R_Float //=;lra.
Qed.

Lemma sqrt_approx_step (phi psi : B_(IR)) (x x0 :IR) : (phi \is_name_of x) -> (psi \is_name_of x0) -> (@representation IR (sqrt_approx_rlzr psi 0%nat phi) x0) /\ forall n y, (@representation IR (sqrt_approx_rlzr psi n phi) y) -> (y <> 0) -> (@representation IR (sqrt_approx_rlzr psi n.+1 phi) (/2 * (y + (x /y)))).
Proof.
  split => [| n y P yneq0]; first by auto.
  rewrite /sqrt_approx_rlzr.
  apply mul_comp.
  - suff <- : (D2R (Float 1%Z (-1)%Z)) = (/ 2) by apply FloattoIR_correct.
    rewrite D2R_Float //=.
    by lra.
  apply plus_comp; try by auto.
  apply div_comp; try by auto.
Qed.

Lemma sqrt_approx_gt_0 x x0 n : (0 <= x) ->  (0 < x0) -> 0 < (sqrt_approx x0 n x).
Proof.
  move => xge x0gt.
  elim n => [| /= n' IH]; first by auto.
  apply Rmult_lt_0_compat; try by lra.
  apply Rplus_lt_le_0_compat; first by lra.
  by apply Rcomplements.Rdiv_le_0_compat;lra.
Qed.
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

Definition IR_nonneg := make_subset (fun (x : IR) => 0 <= x).


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

Definition sqrt_approx_n x n := (sqrt_approx_rlzr one (Nat.log2 n.+1).+1 x).
Lemma speedup_correct : forall (x : IR) (phi : B_(IR)) s, (phi \is_name_of x) -> (fun (p : Q_(IR)) => (phi (speedup p s)))  \is_name_of x.
Proof.
  move => x phi s [phin1 phin2].
  split => n; first by apply phin1.
  case (phin2 n) => N Nprp.
  exists N => k kprp.
  apply (Nprp (speedup k s)).
  rewrite /speedup.
  rewrite /addn /addn_rec.
  apply /leP.
  move /leP :  kprp => kprp.
  apply /Nat.le_trans.
  apply kprp.
  elim k => [| k' IH]; first by lia.
  simpl.
  rewrite Nat.add_0_r.
  suff : (0 < 2 ^ (k'+s)%coq_nat)%coq_nat by lia.
  apply Nat.Private_NZPow.pow_pos_nonneg; by lia.
Qed.

Notation lim_eff:= (efficient_limit: (IR\^w) ->> IR).
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

Lemma sqrt_as_lim :  (lim_eff \o (F2MF (sqrt_approx_seq))|_IR_nonneg) \tightens (make_mf (fun x y => ((/ 4) <= x <= 2) /\ y = (sqrt x))).
Proof.
  apply split_tight.
  - move => x.
    case => t [prp1 prp2].
    exists t.
    split.
    + exists (sqrt_approx_seq x).
      split=> [| n]; first by split; by [simpl;lra|].
      rewrite /= Rabs_minus_sym prp2.
      by apply (sqrt_approx_seq_spec).
  move => y [yprp1 <-].
  exists (sqrt x) => n.
  rewrite /= Rabs_minus_sym.
  by apply (sqrt_approx_seq_spec n);lra.
  move => y [t [prp1 prp2] x [xprp1 xprp2]].
  split; first by auto.
  case xprp1 => S [[_ Sprp1] Sprp2].
  rewrite <- Sprp1 in Sprp2.
  apply Rcomplements.Req_le_aux => eps.
  case (@dns0_tpmn eps); first by apply cond_pos.
  move => n nprp.
  suff : Rabs (x - sqrt y) <= (/ 2 ^ n) by lra.
  have -> : x - sqrt y = (x - (sqrt_approx_seq y n.+1))+(sqrt_approx_seq y n.+1 - sqrt y) by lra.
  apply /Rle_trans.
  apply Rabs_triang.
  apply /Rle_trans.
  apply Rplus_le_compat.
  apply (Sprp2 n.+1).
  apply (sqrt_approx_seq_spec n.+1 prp1).
  by rewrite <- tpmn_half;lra.
Qed.
Definition sqrt_approx_n' x : B_(IR\^w) := (fun nm => (sqrt_approx_n x nm.1 (speedup nm.2 0))).

Lemma sqrt_approx_rlzr_spec : (F2MF (sqrt_approx_n')) \solves (F2MF (sqrt_approx_seq))|_IR_nonneg.
Proof.
  move => phi x phin xdom.
  split => [| psi psin]; first by apply F2MF_dom.
  case xdom => _ [xprp _].
  exists (sqrt_approx_seq x).
  split; first by split; auto.
  rewrite /from.
  rewrite <- psin.
  move => n.
  have t : (0 < 1) by lra.
  have gt0 := (sqrt_approx_gt_0 _ xprp t).
  rewrite /sqrt_approx_n'.
  apply (@speedup_correct (sqrt_approx_seq x n) (sqrt_approx_n phi n)).
  have [P1 P2] := (sqrt_approx_step phin one_describes_one).
  rewrite /sqrt_approx_n /sqrt_approx_seq.
  set m := (Nat.log2 n.+1).+1.
  elim m => [| m' IH]; first by apply P1.
  apply P2; first by apply IH.
  rewrite -/sqrt_approx.
  by have := (gt0 m');lra.
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

Definition sqrt_rlzr := (\F_limit_eff_rlzrM \o (F2MF sqrt_approx_n')).
Lemma sqrt_correct :  sqrt_rlzr \solves (make_mf (fun x y => ((/ 4) <= x <= 2) /\ y = (sqrt x))).
Proof.
   have t := (slvs_tight _ sqrt_as_lim).
   apply t.
   apply slvs_comp; first by apply F_lim_eff_rlzrM_spec.
   by apply sqrt_approx_rlzr_spec.
Qed.

Definition sqrt2_approx := (sqrt_approx_n' two).

Lemma sqrt_in_dom : \Phi_(limit_eff_rlzrM sqrt2_approx) \is_total.
  apply FM_dom.
  rewrite /sqrt2_approx.
  simpl.
Admitted.
Print SF2.sqrt.
Definition sqrt2 := (evaluate sqrt_in_dom).
Eval vm_compute in (sqrt2 2).
Definition IR2Qmf := \F_(IR_RQ_rlzrM').
Lemma pwr2gt : forall n, (n <= (2 ^ (n+0)))%nat.
Proof.
  move => n.
  rewrite /addn/addn_rec Nat.add_0_r.
  move : n.
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
  apply (F_M_realizer_IR_RQ (speedup_gt _) xprp).
  by apply F2MF_dom.
Qed.
Lemma log_map1_in_dom N : \Phi_(IR_RQ_rlzrM' (log_map1 N)) \is_total.
Proof.
  apply FM_dom.
  by apply (logistic_map_in_dom _ (FloattoIR_correct 1%Z (-1)%Z) (FloattoIR_correct 15%Z (-2)%Z)). 
Qed.


Eval vm_compute in (log_map1 5%nat 20%nat).
Definition diag_rlzrf X (phi : B_ X) := (pair (phi,phi)).

Lemma diag_rlzrf_spec X : (F2MF (@diag_rlzrf X)) \solves mf_diag.
  rewrite F2MF_slvs => phi x phin.
  case => t /=tprp.
  exists (x,x); split; first by auto.
  exists (phi,phi).
  split; by [apply pairK | split].
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
Definition lt_epsK := (make_mf (fun (epsxy : R * (R*R)) k => (let (eps,xy) := epsxy in
                                            let (x,y) := xy in
                                             (eps > 0) /\ (x+eps <= y -> k = true_K) /\ (y <= x -> k = false_K)) /\ k <> bot_K)).
Lemma comp (S T U : cs) (F : S ->> T) (G : U ->> S)  H : {f | (F2MF f) \solves F} -> {g | (F2MF g) \solves G} -> H =~= F \o G -> {h | (F2MF h) \solves H}.
Proof.
  case => f fprp.
  case => g gprp prp.
  exists (f \o_f g).
  rewrite <- F2MF_comp_F2MF. 
  rewrite slvbl_prpr => //.
  apply slvs_comp => //.
  apply fprp.
  apply gprp. 
  by auto.
Qed.

Lemma comp_tight (S T U : cs) (F : S ->> T) (G : U ->> S)  H : {f | (F2MF f) \solves F} -> {g | (F2MF g) \solves G} -> (F \o G) \tightens H -> {h | (F2MF h) \solves H}.
Proof.
  case => f fprp.
  case => g gprp prp.
  exists (f \o_f g).
  rewrite <- F2MF_comp_F2MF. 
  by apply (slvs_tight (slvs_comp fprp gprp)).
Qed.


Lemma prd (S T U V: cs) (F : S ->> T) (G : U ->> V) H  : {f | (F2MF f) \solves F} -> {g | (F2MF g) \solves G} -> H =~= (F ** G) -> {h | (F2MF h) \solves H}.
Proof.
  case => f fprp; case => g gprp hprp.
  exists (fprd_frlzr f g).
  rewrite fprd_frlzr_rlzr.
  rewrite slvbl_prpr => //.
  by apply prod.fprd_rlzr_spec; [apply fprp | apply gprp]. 
  by trivial.   
Qed.
Lemma comp_F2MF S T T' (f : S ->> T) (g : T' -> S) t' : (f \o (F2MF g)) t' === (f (g t')).
Proof.
  exact /comp_F2MF.
Qed.
Lemma dom_lt_epsK x y eps: (eps, (x,y)) \from (dom lt_epsK) <-> (eps > 0). 
Proof.
  split => [ | epsgt0]; first by case => k [[kprp1 _] _].
  case  : (total_order_T x y) => [[xlty | xeqy ] | xgty].
  - exists true_K.
    split; try by auto.
    split; try by auto.
    split; try by auto;lra.
  - exists false_K.
    split; try by auto.
    split; try by auto.
    split; try by auto;lra.
  - exists false_K.
    split; try by auto.
    split; try by auto.
    split; try by auto;lra.
Qed.

Lemma dom_which : dom which === All.
Proof.
  move => [s1 s2].
  split => [ | _] //.
  case e : s1 => [a |].
  - by case a; exists true_K;rewrite /=;auto.
  case e' : s2 => [a |].
  - by case a; exists false_K;rewrite /=;auto.
  by exists bot_K; rewrite /=;auto.
Qed.

Lemma lt_epsK_rlzr_spec : {f | (F2MF f) \solves lt_epsK}.
Proof.
  have fp : forall f, (f =~= f) by trivial.
  apply /comp_tight.
  exists (which_rlzrf : (B_(cs_Sirp \*_cs cs_Sirp) -> B_(cs_Kleeneans))).
  apply /which_rlzrf_spec.
  apply /(@comp (cs_Kleeneans \*_cs cs_Kleeneans) (cs_Sirp \*_cs cs_Sirp) _).
  apply /prd.
  exists (K_truth_rlzrf : (names_Kleeneans -> B_(cs_Sirp))).
  apply /Ktruth_rlzr_spec.
  exists (K_truth_rlzrf : (names_Kleeneans -> B_(cs_Sirp))).
  apply /Ktruth_rlzr_spec.
  apply fp.
  apply /(@comp ((IR \*_cs IR) \*_cs (IR \*_cs IR)) (cs_Kleeneans \*_cs cs_Kleeneans)).
  apply /prd.
  exists (ltK_rlzr : B_(IR \*_cs IR) -> names_Kleeneans).
  apply /ltK_rlzr_spec.
  exists (ltK_rlzr : B_(IR \*_cs IR) -> names_Kleeneans).
  apply /ltK_rlzr_spec.
  apply /fp.
  apply /(@comp ((IR \*_cs (IR \*_cs IR)) \*_cs (IR \*_cs (IR \*_cs IR))) _).
  apply /prd.
  exists ((@rprj _ _): (B_(IR \*_cs (IR \*_cs IR)) -> B_(IR \*_cs IR))).
  apply /snd_rlzr_spec.
  apply /(@comp ((IR \*_cs (IR \*_cs IR)) \*_cs (IR \*_cs (IR \*_cs IR))) (IR \*_cs IR) (IR \*_cs (IR \*_cs IR))).
  apply /prd.
  apply /comp.
  exists ((@rprj _ _) : (B_(IR \*_cs IR) -> B_(IR))).
  apply /snd_rlzr_spec.
  exists ((@rprj _ _) : (B_(IR \*_cs (IR \*_cs IR)) -> (B_(IR\*_cs IR)))).
  apply /snd_rlzr_spec.
  apply /fp.
  apply /comp.
  exists (Rplus_rlzrf : (B_(IR \*_cs IR) -> B_(IR))).
  apply /Rplus_rlzr_spec.
  apply /prd.
  exists (ssrfun.id : B_(IR) -> B_(IR)).
  apply /id_rlzr.
  exists ((@lprj _ _) : (B_(IR\*_cs IR) -> B_(IR))).
  apply /fst_rlzr_spec.
  apply /fp.
  apply /fp.
  apply /fp.
  exists ((@diag_rlzrf _) : (B_(IR \*_cs (IR \*_cs IR)) -> _)).
  apply /diag_rlzrf_spec.
  apply /fp.
  apply /fp.
  exists ((@diag_rlzrf _) : (B_(IR \*_cs (IR \*_cs IR)) -> _)).
  apply /diag_rlzrf_spec.
  apply /fp.
  apply /fp.
  apply /fp.
  rewrite /lt_epsK.
  move => [eps [x y]].
  rewrite !dom_lt_epsK.
  rewrite <-!F2MF_fprd.
  rewrite !F2MF_comp_F2MF.
  rewrite <-!F2MF_fprd.
  rewrite !F2MF_comp_F2MF.
  rewrite <-!F2MF_fprd.
  rewrite !F2MF_comp_F2MF.
  rewrite comp_F2MF => epsgt0.
  split; first by apply comp_subs_dom; [rewrite dom_which | apply F2MF_dom].
  case => H.
  - apply which_spec in H.
    move : H.
    rewrite /K_truthf /uncurry /=.
    case : (total_order_T y (eps+x)) => [[xlty _ | xeqy ] | xgty]; try by trivial.
    by split;  [split; [lra|split;try trivial;lra]|].
  - apply which_spec in H.
    move : H.
    rewrite /K_truthf /uncurry /=.
    case : (total_order_T x y) => [[xlty _ | xeqy ] | xgty]; try by trivial.
    by split;  [split; [lra|split;try trivial;lra]|].
  move : H.
  rewrite /K_truthf /uncurry /=.
  case : (total_order_T x y) => [[xlty | xeqy ] | xgty];case : (total_order_T y (eps+x)) => [[xlty' | xeqy' ] | xgty'];  try by trivial; try by split;lra.
  by case => [[_ H] | ]; [ | case => [[H1 H2] | [H1 H2]]].
  by case => [[_ H] | ]; [ | case => [[H1 H2] | [H1 H2]]].
  by case => [[_ H] | ]; [ | case => [[H1 H2] | [H1 H2]]].
  split; try by trivial.
  split; try by trivial.
  split; try by lra.
  move : H.
  by case => [[_ H] |]; [ | case => [[H1 H2] | [H1 [H2 H3]]]].
  move : H.
  by case => [[_ H] |]; [ | case => [[H1 H2] | [H1 [H2 H3]]]].
  by case => [[_ H] |]; [ | case => [[H1 H2] | [H1 [H2 H3]]]].
Qed.

Definition lt_nK := (make_mf (fun (nxy : nat * (R*R)) k => (let (n,xy) := nxy in
                                            let (x,y) := xy in
                                              (x+(/ 2 ^ n) <= y -> k = true_K) /\ (y <= x -> k = false_K)) /\ k <> bot_K)).
Definition lt_n := (make_mf (fun (nxy : nat * (R*R)) b => (let (n,xy) := nxy in
                                            let (x,y) := xy in
                                             (x+(/ 2 ^ n) <= y -> b = true) /\ (y <= x -> b = false)))).

Lemma lt_n_spec : lt_n =~= (F2MF B2K)\^-1 \o lt_nK.
Proof.
  move => [n [x y] b].
  split => [[P1 P2] | [P1 P2] ].
  - split => [| t [[tprp1 tprp2] tprp3]]; last by case e: t; [exists false | exists true |].
    exists (B2K b).
    rewrite /B2K /lt_nK /=.
    split; [split; last by case b | by auto ].
    by split => H; [rewrite P1| rewrite P2].
  split.
  case P1 => k [[[kprp1 kprp2] kprp3] /= kprp4 H].
  move : kprp4; rewrite /B2K kprp1; by [case b | lra].
  case P1 => k [[[kprp1 kprp2] kprp3] /= kprp4 H].
  move : kprp4; rewrite /B2K kprp2; by [case b | lra].
Qed.

Lemma lt_nK_rlzr_spec : {f | F2MF f \solves lt_nK}.
Proof.
  have fp : forall f, (f =~= f) by trivial.
  apply /comp => //.
  apply lt_epsK_rlzr_spec.
  apply /prd => //.
  exists tpmnIR_rlzr.
  apply tpmnIR_rlzr_spec.
  exists (ssrfun.id).
  apply /id_rlzr.
  move => [n [x y]].
  split => /=.
  - move => [[prp1 prp2] prp3].
    split.
    + exists ((/ 2 ^ n), (x,y)); split; [| split]; try by auto; by split; [apply tpmn_lt|split;by auto].
    move => [eps [x' y']] /= [prp'1 [prp'2 prp'3]].
    exists s.      
    rewrite <-prp'1, <- prp'2, <- prp'3.
    by split; [ split; [apply tpmn_lt | split] | ].
  move => [H1 H2].
  case H1 => [[eps' [x' y']] [[-> [-> ->] [[P1 [P2 P3]] P4]]]].
  by split; [split | ].
Qed.

Definition lt_nk_rlzrf := projT1 lt_nK_rlzr_spec.
Definition lt_n_rlzr := (\F_K2B_rlzrM : B_(cs_Kleeneans) ->> B_(cs_bool)) \o (F2MF lt_nk_rlzrf).

Lemma lt_n_rlzr_spec : lt_n_rlzr \solves lt_n.
Proof.
  rewrite lt_n_spec /lt_n_rlzr.
  by apply slvs_comp; [apply F_K2B_rlzrM_spec | apply (projT2 lt_nK_rlzr_spec)].
Qed.  

Lemma dom_lt_nk : dom lt_nK === All.
Proof.
  move => [n [x y]].
  split => // _.
  case (Rle_or_lt (x + (/2 ^ n)) y) => p.
  - exists true_K.
    split; [split |] => //.
    suff : 0 < ( / 2 ^ n) by lra.
    by apply tpmn_lt.
  exists false_K.
  split; [split |] => //.
  suff : (0 < (/ 2 ^ n)) by lra.
  by apply tpmn_lt.
Qed.

Definition magnitude := make_mf ((fun x n => ((/ 2 ^ n) < x < 4*(/2 ^ n)))).

Lemma magnitude_spec x n: (true \from (lt_n (n.+2,((/ 2 ^ n),x)))) /\ true \from (lt_n (n.+2, (x, 3*(/ 2 ^n)+(/ 2 ^ (n.+2))))) -> n \from (magnitude x).
Proof.
  move => [[_ H12] [_ H21]].
  have xlt : (x < (3*(/ 2 ^ n))+(/ 2 ^ (n.+2))) by apply Rnot_le_lt => e;move : (H21 e).
  have xgt : ((/2 ^ n) < x) by apply Rnot_le_lt => e;move : (H12 e).
  split; [by lra|].
  suff : (/ 2 ^ n.+2) < (/ 2 ^ n) by lra.
  rewrite (@tpmn_half n).
  rewrite (@tpmn_half n.+1).
  suff : 0 < (/ 2 ^ (n.+2)) by lra.
  by apply tpmn_lt.
Qed.

Lemma lt_n_nt1 x n: (/ 2 ^ n)+(/2 ^ (n.+2)) <= x  -> (true \from (lt_n (n.+2,((/ 2 ^ n), x)))).
Proof.
  move => xgt.
  split; first by auto.
  move => H.
  suff : (0 < (/ 2 ^ (n.+2))) by lra.
  by apply tpmn_lt.
Qed.
Lemma lt_n_nf1 x n: (/ 2 ^ n)+(/2 ^ (n.+2)) <= x  -> not (false \from (lt_n (n.+2,((/ 2 ^ n), x)))).
Proof.
  move => xgt.
  case => H1 H2.
  suff : (false = true) by auto.
  by apply H1.
Qed.

Lemma lt_n_nt2 x n: x <= 3*(/ 2 ^ n)  -> (true \from (lt_n (n.+2,(x, 3*(/ 2 ^n) + (/ 2 ^ (n.+2)))))).
Proof.
  move => xgt.
  split; first by auto.
  move => H.
  suff : (0 < (/ 2 ^ (n.+2))) by lra.
  by apply tpmn_lt.
Qed.
Lemma lt_n_nf2 x n: x <= 3*(/ 2 ^ n)  -> not (false \from (lt_n (n.+2,(x, 3*(/ 2 ^n) + (/ 2 ^ (n.+2)))))).
Proof.
  move => xlt.
  case => H1 H2.
  suff : (false = true) by auto.
  apply H1.
  by lra.
Qed.

Lemma magnitude_n_exists x : (0 < x <= 1) -> exists n, ((/2 ^ n) + (/2 ^ (n.+2))) <= x <= 3*(/ 2 ^ n).
Proof.
  move => H.
  suff : exists z, (z < 0)%Z /\ (powerRZ 2 z) + (powerRZ 2 (z-2)) <= x <= 3*(powerRZ 2 z). 
  - case => z [zprp1 zprp2].
    move : zprp2.
    have ->  : (z = (- (Z.of_nat (Z.to_nat (-z))))%Z) by rewrite Z2Nat.id; lia.
    have -> t : (- t - 2)%Z = (-(t + (Z.of_nat 2)))%Z by lia.
    rewrite <- Nat2Z.inj_add.
    have -> t : ((t + 2) = (t.+2))%coq_nat by lia.
    rewrite !powerRZ2_neg_pos => zprp2.
    by exists (Z.to_nat (-z)).
  have helper : (ln 2 <> 0).
  - suff : (/ 2 < ln 2) by lra.
    by apply ln_lt_2.
  have xgt : (powerRZ 2 ((up ((ln (x/3))/(ln 2))))%Z) <= (2*x / 3).
  - rewrite !powerRZ_Rpower; try by lra.
    apply /Rle_trans.
    apply /Rle_Rpower; try by lra.
    have p t : ((up t) <= (t + 1)) by have := (archimed t);lra.
    apply p.
    rewrite Rpower_plus Rpower_1; last by lra.
    rewrite /Rpower /Rdiv Rmult_assoc Rinv_l; last by apply helper.
    by rewrite Rmult_1_r exp_ln; lra.
  have xlt : x <= 3*(powerRZ 2 ((up ((ln (x/3))/(ln 2))))%Z).
  - rewrite !powerRZ_Rpower; try by lra.
    suff : (x / 3) <= (Rpower 2 (up ((ln (x / 3))/(ln 2)))) by lra.
    have p t : (t <= (up t)) by have := (archimed t);lra.
    apply /Rle_trans; last first.
    apply /Rle_Rpower; try by lra.
    apply p.
    rewrite /Rpower /Rdiv Rmult_assoc Rinv_l; last by apply helper.
    by rewrite Rmult_1_r exp_ln; lra.
  have lnlt0 : ((up ((ln (x/3))/(ln 2))) < 0)%Z.
  - apply lt_IZR.
    suff : (ln (x/3))/(ln 2) < -1 by have := (archimed ((ln (x/3))/(ln 2)));lra.
    rewrite Rlt_div_l; last by have := ln_lt_2;lra.
    ring_simplify.
    rewrite <- ln_Rinv; last by lra.
     apply ln_increasing; try by lra.
  exists (up ((ln (x/3))/(ln 2))).
  split; [by trivial| split; try by lra].
  rewrite powerRZ_add /=; by lra.
Qed.
Definition lt_n_M := fun phi => (K2B_rlzrM (lt_nk_rlzrf phi)).

Definition lt_n_partial := (get_partial_function lt_n_M).
Check partial_function.
Definition nat2csN (n : nat) := (fun (_ : unit) => n). 
Definition magnitude_checkM phi n m := match (lt_n_M (@pair B_(cs_nat) _ ((nat2csN n.+2), (mp phi (FloattoIR 3%Z 0%Z) \* (FloattoIR 1%Z (- (Z.of_nat n))%Z) \+ (FloattoIR 1%Z (- (Z.of_nat (n.+2)))%Z)))) (m,tt)) with
                                       | (Some true) =>
                                         match (lt_n_M (@pair B_(cs_nat) _ ((nat2csN n.+2), (mp (FloattoIR 1%Z (- (Z.of_nat n))%Z)) phi)) (m,tt)) with
                                           | (Some true) => true
                                           | (Some false) => false
                                           | _ =>  false
                                         end
                                                    
                                       | (Some false)=> false
                                       | _ => false
                                       end.

Lemma K2B_rlzrM_name (phi : B_(cs_Kleeneans)) m b : (K2B_rlzrM phi m) = (Some b) -> (phi \is_name_of (B2K b)).
Proof.
  - rewrite /K2B_rlzrM /B2K /=.
    case e :(phi (ord_search (fun m0 : nat => phi m0) m.1)) => [a | ]; try by auto.
    move : e.
    case a;case b => e; try by auto.
    exists (ord_search (fun m0 : nat => phi m0) m.1).
    rewrite e; split; try by auto.
    move => n nprp.
    case e' : (phi n) => [b'|]; try by auto.
    have t : (is_true (phi n)) by rewrite e'.
    have /leP := (@osrch_min (fun m0 => phi m0) m.1 n t).
    move /leP : nprp.
    by lia.
    exists (ord_search (fun m0 : nat => phi m0) m.1).
    rewrite e; split; try by auto.
    move => n nprp.
    case e' : (phi n) => [b'|]; try by auto.
    have t : (is_true (phi n)) by rewrite e'.
    have /leP := (@osrch_min (fun m0 => phi m0) m.1 n t).
    move /leP : nprp.
    by lia.
Qed.

Lemma lt_N_b_correct phi psi (x y : IR) n m b : (phi \is_name_of x) -> (psi \is_name_of y) -> (lt_n_M (@pair B_(cs_nat) _ ((nat2csN n),(mp phi psi))) (m,tt)) = (Some b) -> b \from (lt_n (n,(x,y))).
Proof.
  move => phin psin.
  rewrite /lt_n_M lt_n_spec  => /K2B_rlzrM_name H.
  have := (projT2 lt_nK_rlzr_spec (@pair B_(cs_nat) _ ((nat2csN n),(mp phi psi))) (n,(x,y))).
  case.
  apply prod_name_spec; split; first by auto.
  apply prod_name_spec; split; by auto.
  by apply dom_lt_nk.
  move => H1 H2.
  have := (H2 (lt_nk_rlzrf (@pair B_(cs_nat) _ (nat2csN n, mp phi psi)))).
  case; first by auto.
  move => b' [b'prp1 b'prp2].
  rewrite (rep_sing b'prp2 H) in b'prp1.
  split; first by exists (B2K b);split.
  move => k.
  case k; move => [[kprp1 kprp2] kprp3]; try by auto.
  by exists false.
  by exists true.
Qed.
Lemma magnitude_check_cmp_names n : ((Rplus_rlzrf'
                (mp (Rmult_rlzrf' (mp (FloattoIR 3%Z 0%Z) (FloattoIR 1%Z (- Z.of_nat n)%Z)))
                    (FloattoIR 1%Z (- Z.of_nat n.+2)%Z))) : B_(IR)) \is_name_of ((3 * (/ 2 ^ n) + (/ 2 ^ (n.+2))) : IR) /\ (FloattoIR 1%Z (- (Z.of_nat n))%Z) \is_name_of (/ 2 ^ n).
Proof.                                  
  split.
  - rewrite <- !powerRZ2_neg_pos.
    have p n': (powerRZ 2 (n')) = (D2R (Float 1%Z (n')%Z)) by rewrite D2R_Float;lra.
    rewrite !p.
    apply plus_comp; try by apply FloattoIR_correct.
    by apply mul_comp; apply FloattoIR_correct.
  have  := (FloattoIR_correct 1%Z (- (Z.of_nat n))%Z).
  by rewrite D2R_Float Rmult_1_l powerRZ2_neg_pos.
Qed.
Lemma magnitude_check_correct phi n m x : (phi \is_name_of x) -> (0 < x <= 1) -> (magnitude_checkM phi n m)  -> n \from (magnitude x).
Proof.
  move => phin [xgt xlt].
  rewrite /magnitude_checkM.
  case e :lt_n_M => [b |]; try by auto.
  move : e;case b => e; try by auto.
  have [psin psin'] := (magnitude_check_cmp_names n). 
  apply (lt_N_b_correct phin psin) in e.
  case e' :lt_n_M => [b' |]; try by auto.
  move : e';case b' => e'; try by auto.
  apply (lt_N_b_correct psin'  phin) in e'.
  move => _.
  by apply (@magnitude_spec x n).
Qed.

Lemma K2B_rlzrM_terms phi b : (phi \is_name_of (B2K b)) -> exists m, (K2B_rlzrM phi (m,tt)) = (Some b).
  move => phin.
  have := (F_K2B_rlzrM_spec phin).
  case; first by exists b.
  move => H.
  move => H'.
  case H => b' b'prp.
  case  (b'prp tt) => m mprp.
  exists m.
  suff <- : (b' tt) = b by auto.
  case (H' _ b'prp) => b'' /=.
  rewrite /B2K.
  by case b'';case b';case b; move => // [H1 H2].
Qed.

Lemma K2B_rlzrM_monotonic phi b m : (K2B_rlzrM phi (m, tt)) = (Some b) -> forall m', (m <= m')%coq_nat -> (K2B_rlzrM phi (m',tt)) = (Some b).
Proof.
  rewrite /K2B_rlzrM.
  move => /= H m' m'prp.
  suff <- : ((ord_search (fun m0 : nat => phi m0) m)) = ((ord_search (fun m0 : nat => phi m0) m')) by rewrite H.
  apply osrch_eq; last by apply /leP.
  by move : H;case e: (phi (ord_search (fun m0 : nat => phi m0) m)) => [b' | ] //; case b'.
Qed.

Lemma lt_N_b_term phi psi (x y : IR) n : (phi \is_name_of x) -> (psi \is_name_of y) -> exists m, exists b, forall m', (m <= m')%coq_nat -> (lt_n_M (@pair B_(cs_nat) _ ((nat2csN n),(mp phi psi))) (m',tt)) = (Some b).
Proof.
  move => phinx phiny.
  rewrite /lt_n_M.
  have p : ((@pair B_(cs_nat) _ ((nat2csN n), mp phi psi)) : B_(cs_nat \*_cs (IR \*_cs IR))) \is_name_of (n, (x,y)).
  - by apply /prod_name_spec; split; [|apply /prod_name_spec;split ].
  have := (projT2 lt_nK_rlzr_spec _ _ p).
  case; first by apply dom_lt_nk.
  move => H P.
  case H => k' kprp'.
  case (P k' kprp') => k [kprp1 kprp2].
  have : exists b, (B2K b) = k.
  - move : kprp1.
    by case k; move=> [[P1 P2] P3]; [exists false | exists true | ].
  case => b bprp.
  rewrite <- bprp in kprp2.
  case (K2B_rlzrM_terms kprp2 ) => m mprp.
  exists m; exists b.
  apply K2B_rlzrM_monotonic.
  rewrite /lt_nk_rlzrf.
  by rewrite kprp'.
Qed.

Lemma magnitude_check_srch_term phi x : (phi \is_name_of x) -> (0 < x <= 1) -> exists n m, (magnitude_checkM phi n m).
Proof.
  move => phin xbnd.
  case (magnitude_n_exists xbnd) => n [nprp1 nprp2].
  Check lt_n_nf2.
  have is_true1 b : b \from (lt_n (n.+2,(x, (3 * (/ 2 ^n) + (/ 2 ^ n.+2))))) -> b = true.
  - case b; first by auto.
    by have := (lt_n_nf2 nprp2).
  have is_true2 b : b \from (lt_n (n.+2,((/ 2 ^ n), x))) -> b = true.
  - case b; first by auto.
    by have := (lt_n_nf1 nprp1).
  exists n.
  rewrite /magnitude_checkM.
  have [psin psin'] := (magnitude_check_cmp_names n).
  case (lt_N_b_term n.+2 phin psin) => m1; case => b1 m1prp.
  case (lt_N_b_term n.+2 psin' phin) => m2; case => b2 m2prp.
  move : (m1prp _ (Max.le_max_l m1 m2)) => mprp.
  have b1prp : b1 = true.
  - apply is_true1.
    by apply (lt_N_b_correct phin psin mprp ).
  rewrite b1prp in mprp.
  move : (m2prp _ (Max.le_max_r m1 m2)) => mprp'.
  have b2prp : b2 = true.
  - apply is_true2.
    by apply (lt_N_b_correct psin' phin mprp' ).
  rewrite b2prp in mprp'.
  exists (Nat.max m1 m2).
  by rewrite mprp mprp'.
Qed.

Definition magnitude_rlzrM phi m := let n := (ord_search (fun n => (magnitude_checkM phi n m)) m) in
                                    if n == m
                                    then None
                                    else (Some n).
Lemma magnitude_check_monotonic phi n m m' : (m <= m')%nat -> (magnitude_checkM phi n m) -> (magnitude_checkM phi n m').
Proof.
  move /leP => lt.
  rewrite /magnitude_checkM /lt_n_M.
  case e : (K2B_rlzrM _) => [b |] //; case bv : b; try by auto.
  rewrite bv in e.
  case e' : (K2B_rlzrM _) => [b' |] //; case bv' : b'; try by auto.
  rewrite bv' in e' => _.
  rewrite (K2B_rlzrM_monotonic e lt).
  by rewrite (K2B_rlzrM_monotonic e' lt).
Qed.

Lemma magnitude_rlzrM_simpl phi m n : (magnitude_rlzrM phi m) = (Some n) -> (magnitude_checkM phi n m).
Proof.
  rewrite /magnitude_rlzrM.
  set m0 := (ord_search (fun n' => (magnitude_checkM phi n' m)) m).
  move => H.
  have m0lt : (m0 < m)%nat.
  - apply /leP.
    have /leP p0 := (osrch_le (fun n' => (magnitude_checkM phi n' m)) m).
    suff: (m0 <> m) by lia.  
    move : H.
    case e: (m0 == m)%B => // _.
    by move /eqP :e.
  have <- : (m0 = n)%nat.
  - move : H.
    case e: (m0 == m)%B => //.
    by case.
  by have m0prp : (magnitude_checkM phi m0 m); apply (search_lt m0lt).
Qed.

Lemma magnitude_rlzrM_correct phi x m n : (phi \is_name_of x) -> (0 < x <= 1) -> (magnitude_rlzrM phi m) = (Some n) -> (n \from magnitude x).
  move => phin xbnd H.
  have H' := (magnitude_rlzrM_simpl H). 
  by apply (magnitude_check_correct phin xbnd H').
Qed.

Lemma magnitude_rlzrM_term phi x : (phi \is_name_of x) -> (0 < x <= 1) -> exists m, forall m', (m <= m')%nat -> exists n, (magnitude_rlzrM phi m') = (Some n).
Proof.
  rewrite /magnitude_rlzrM.
  move => phin xbnd.
  case (magnitude_check_srch_term  phin xbnd) => n; case => m mprp.
  exists (Nat.max (n.+1) (m.+1)) => m' m'prp.
  have m'le : (m <= m')%nat by apply /leP;have := (Max.le_max_r n.+1 m.+1); move /leP : m'prp;lia.
  have mprp2 := (magnitude_check_monotonic m'le mprp).
  have le := (@osrch_min (fun n => (magnitude_checkM phi n m')) m' n mprp2).
  exists (ord_search (fun n => (magnitude_checkM phi n m')) m').
  apply ifF.
  apply /eqP => P.
  move /leP : le.
  rewrite P.
  have := (Max.le_max_l n.+1 m.+1).
  move /leP : m'prp.
  by lia.
Qed.

Lemma magnitude_rlzrM_spec phi x : (phi \is_name_of x) -> (0 < x <= 1) -> exists m n, (magnitude_rlzrM phi m) = (Some n) /\ (n \from magnitude x).
Proof.
  move => phin xbnd.
  case (magnitude_check_srch_term phin xbnd) => n; case => m mprp.
  exists (Nat.max n m).+1.
  exists (ord_search (fun n' => (magnitude_checkM phi n' (Nat.max n m).+1)) (Nat.max n m).+1).
  rewrite /magnitude_rlzrM.
  have lt1 : (m < (Nat.max n m).+1)%nat.
  - apply /leP.
    have := (Max.le_max_r n m).
    lia.
  have lt2 : (n < (Nat.max n m).+1)%nat.
  - apply /leP.
    by have := (Max.le_max_l n m);lia.
  have le1 : (m <= (Nat.max n m).+1)%nat by apply /leP;lia. 
  have le2 : (n <= (Nat.max n m).+1)%nat by apply /leP;lia. 
  have M := (magnitude_check_monotonic le1 mprp).
  rewrite ifF.
  - split; first by auto.
    by apply (magnitude_check_correct phin xbnd (@search_correct_le (fun n' => (magnitude_checkM phi n' (Nat.max n m).+1)) _ _ M le2)).
  apply ltn_eqF.
  apply /leq_ltn_trans.
  apply (@osrch_min (fun n' => (magnitude_checkM phi n' (Nat.max n m).+1)) _ _ M).
  by apply lt2.
Qed.

Lemma magnitude_inv x n: (0 < x) -> n \from (magnitude (/ x)) ->  (/ 4) * (2 ^ n) < x < (2 ^ n).
Proof.
  move => xlt /= [nprp1 nprp2].
  split.
  - apply Rinv_lt_cancel; first by lra.
    rewrite Rinv_mult_distr; try by lra.
    apply pow_nonzero;lra.
  by apply Rinv_lt_cancel; [apply pow_lt |];lra.
Qed.
Lemma magnitude_1 x : ((/ 2) < x < 2) -> 1%nat \from (magnitude x).
Proof.
  by simpl;lra.
Qed.

Definition magnitude_rlzrM_gt0 (phi : B_(IR)) m := match (lt_n_M (@pair B_(cs_nat) _ ((nat2csN 2), (mp phi (FloattoIR 1%Z 0%Z)))) (m,tt)) with
                                        | (Some true) =>
                                          match (magnitude_rlzrM phi m) with
                                            | (Some n) => (Some (- (Z.of_nat n))%Z)
                                            | _ => None
                                          end
                                        | (Some false) =>
                                         match (lt_n_M (@pair B_(cs_nat) _ ((nat2csN 2), (mp phi (FloattoIR 2%Z 0%Z)))) (m,tt)) with
                                         | (Some true)  => (Some (-1)%Z)
                                         | (Some false) =>
                                          match (magnitude_rlzrM (one \: phi) m) with
                                            | (Some n) => (Some ((Z.of_nat n)-2)%Z)
                                            | _ => None
                                          end
                                         | _ => None
                                         end
                                        | _ => None
                                        end.
                      
Lemma magnitude_rlzrM_gt0_correct phi x m z : (phi \is_name_of x) -> (0 < x) -> (magnitude_rlzrM_gt0 phi m) = (Some z) -> (powerRZ 2 z) < x < (powerRZ 2 (z+2)).
Proof.
  move => phin xlt.
  rewrite /magnitude_rlzrM_gt0.
  have psin : (FloattoIR 1%Z 0%Z) \is_name_of 1 by apply FloattoIR_correct.
  have psin' : (FloattoIR 2%Z 0%Z) \is_name_of 2 by apply FloattoIR_correct.
  have simpl1 y : true \from (lt_n (2%nat,(x,y))) -> (x < y).
  - move => H.
    suff : not (y <= x) by lra.
    move => le.
    case H => _ H'.
    by have := (H' le).
  have simpl2 y : false \from (lt_n (2%nat,(x,y))) -> (y - /2 < x).
  - move => H.
    suff : not (x + (/ 2 ^ 2) <= y) by simpl;lra.
    move => le.
    case H => H' _.
    by have := (H' le).
  case e :(lt_n_M _) => [b |] //;case bv : b; rewrite bv in e.
  - apply (lt_N_b_correct phin psin) in e.
    apply simpl1 in e.
    case M: (magnitude_rlzrM _) => // [n] nprp.
    have /= := (magnitude_rlzrM_correct phin _ M).
    case; first by lra.
    rewrite <- powerRZ2_neg_pos.
    rewrite powerRZ_add /=; try by lra.
    have -> : (- Z.of_nat n)%Z = z by move : nprp; case.
    by lra.   
  apply (lt_N_b_correct phin psin) in e.
  apply simpl2 in e.
  case e' :(lt_n_M _) => [b' |] //;case bv' : b'; rewrite bv' in e'.
  - apply (lt_N_b_correct phin psin') in e'.
    apply simpl1 in e'.   
    move => H.
    have -> /= : (z = -1)%Z by move : H;case.
    by have := (magnitude_1);lra.
  have phind : (Rdiv_rlzrf' (mp one phi) : B_(IR)) \is_name_of (/ x).
  - have xn : (x <> 0) by lra.
    have -> : (/ x = (1 / x)) by lra.
    by apply (div_comp xn one_describes_one phin).
  apply (lt_N_b_correct phin psin') in e'.
  apply simpl2 in e'.
  case M: (magnitude_rlzrM _) => // [n] nprp.
  have := (magnitude_rlzrM_correct phind _ M).
  case.
  - split; first by apply Rinv_0_lt_compat;lra.
    have -> : (1 = (/ 1)) by lra. 
    by apply Rle_Rinv; lra.
   move => H1 H2.
   case (@magnitude_inv _ n xlt); first by simpl; lra.
   have -> : (z = (Z.of_nat n - 2)%Z) by move : nprp;case.
   rewrite !powerRZ_add /=; try by lra.
   rewrite !pow_powerRZ.
   by lra.
 Qed.

Lemma magnitude_rlzrM_gt0_term1 phi x : (phi \is_name_of x) -> (0 < x) -> exists m, forall m', (m <= m')%nat -> exists z, (magnitude_rlzrM_gt0 phi m') = (Some z).
Proof.
  move => phin xgt.
  rewrite /magnitude_rlzrM_gt0.
  have psin : (FloattoIR 1%Z 0%Z) \is_name_of 1 by apply FloattoIR_correct.
  have psin' : (FloattoIR 2%Z 0%Z) \is_name_of 2 by apply FloattoIR_correct.
  have lt_N_term_m : exists m b b', (forall m', (m <= m')%coq_nat -> (((lt_n_M (@pair B_(cs_nat) _ ((nat2csN 2), (mp phi (FloattoIR 1%Z 0%Z)))) (m',tt))) = (Some b)
           /\ ((lt_n_M (@pair B_(cs_nat) _ ((nat2csN 2), (mp phi (FloattoIR 2%Z 0%Z)))) (m',tt))) = (Some b')))
           /\ ((b = true) -> (x < 1)) /\ (b = false -> (/2 < x)) /\ ((b' = true) -> (x < 2)) /\ ((b' = false) -> (1 < x)).
  - case (lt_N_b_term 2%nat phin psin) => m1; case => b1 mprp1.
    case (lt_N_b_term 2%nat phin psin') => m2; case => b2 mprp2.
    exists (Nat.max m1 m2); exists b1; exists b2.
    split =>  [m' m'prp | ].
    + have m'gtm1 : (m1 <= m')%coq_nat by have := (Max.le_max_l m1 m2);lia.
      have m'gtm2 : (m2 <= m')%coq_nat by have := (Max.le_max_r m1 m2);lia.
      have mprp1' := (mprp1 _ m'gtm1).
      have mprp2' := (mprp2 _ m'gtm2).
      by split.
    have mprp1' := (mprp1 _ (le_n m1)).
    have mprp2' := (mprp2 _ (le_n m2)).
    have [P1 P2] := (lt_N_b_correct phin psin mprp1').
    have [P1' P2'] :=(lt_N_b_correct phin psin' mprp2').
    have helper a b: ((a <= b) -> (true = false)) -> (b < a).
    + move => H.
      apply Rnot_le_lt => le.
      by have := (H le).
    have helper' a a' b c: ((a + a' <= b) -> (false = true)) -> (c <= b-a') -> (c < a).
    + move => H H'.
      apply Rnot_le_lt => le.
      have le' : (a + a' <= b) by lra.
      by have := (H le').
    split; [ | split; [| split]] => H; rewrite H /= in P1,P2, P1',P2'; try by apply helper.
    by apply (helper' _ _ _ _ P1); lra.
    by apply (helper' _ _ _ _ P1'); lra.
  case lt_N_term_m => m; case => b; case => b'.
  case : b => [[H1 [P _]] |].
  - have P' : (x < 1) by auto.
    case (magnitude_rlzrM_term phin) => [ | m' m'prp]; first by lra.
    exists (Nat.max m m') => M mprp.
    have  := (H1 M).
    case => [| H1' _]; first move /leP : mprp;have := (Max.le_max_l m m').
    + by lia.
    have  := (m'prp M).
    case => [| n H2']; first apply /leP; have := (Max.le_max_r m m'); move /leP : mprp.
    + by lia.
    by exists (- Z.of_nat n)%Z; rewrite H1' H2'.
  case b' => [[H1 _] |[H1 [_ [_ [_ P]]]]].
  - exists m => M /leP Mprp.
    have [H1' H2'] := (H1 _ Mprp).
    by exists (-1)%Z; rewrite H1' H2'.
  have xinvlt : (/ x) <= 1.
  - suff : (/ x < 1) by lra.
    rewrite <- Rinv_1.
    apply Raux.Rinv_lt;try by lra.
    by auto.
  have phin' : ((Rdiv_rlzrf' (mp one phi)) : B_(IR)) \is_name_of (/ x).     
  - have -> : (/ x = (1 / x)) by lra.
    apply div_comp; by [lra | apply one_describes_one |].
    case (magnitude_rlzrM_term phin') => [ | m' m'prp]; first by split;[apply Rinv_0_lt_compat;lra|lra].
    exists (Nat.max m m') => M Mprp.
    have  := (H1 M).
    case => [| H1' H2']; first move /leP : Mprp;have := (Max.le_max_l m m').
    + by lia.
    have  := (m'prp M).
    case => [| n H3']; first apply /leP; have := (Max.le_max_r m m'); move /leP : Mprp.
    + by lia.
    by exists (Z.of_nat n - 2)%Z; rewrite H1' H2' H3'.
Qed.

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
  rewrite H /next_even => H' pprp.
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
  Search _ (?a - ?a)%Z.
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
  exists ((((Rmult_rlzrf' (mp (tpnIR (- next_even p)%Z) phi)) : B_(IR)), (next_even p / 2)%Z)).
  by rewrite /scaleM pprp.
Qed.



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

Lemma lt_n_M_monotonic phi psi n b m : (lt_n_M (@pair B_(cs_nat) _ ((nat2csN n), (mp phi psi))) (m,tt)) = (Some b) -> forall m', (m <= m')%coq_nat -> (lt_n_M (@pair B_(cs_nat) _ ((nat2csN n), (mp phi psi))) (m',tt)) = (Some b).
Proof.
  rewrite /lt_n_M => prp m' m'prp.
  by apply (K2B_rlzrM_monotonic prp m'prp).
Qed.

Definition sqrt_approx_total n := make_mf (fun x y => (true \from (lt_n ((2*n).+1,(x, (/ 2 ^ (2*n)))))) /\ y = 0 \/ (false \from (lt_n ((2*n).+1,(x, (/ 2 ^ (2*n)))))) /\ exists p z,  (powerRZ 4 p)*z = x /\ ((/ 4) <= z <= 2) /\ y = (powerRZ 2 p)*(sqrt_approx_seq z (n +(Z.to_nat p)))).

Lemma tpmn_mult_l n m : (/ 2 ^ (n * m)%nat) = ((/ 2 ^ m) ^ n).
Proof.
  rewrite <- powerRZ2_neg_pos, powerRZ_Rpower; last by lra.
  rewrite Nat2Z.inj_mul Zopp_mult_distr_r mult_IZR Rmult_comm.
  rewrite <-Rpower_mult.
  rewrite <- INR_IZR_INZ.
  by rewrite  <- powerRZ_Rpower, Rpower_pow, powerRZ2_neg_pos; [|apply powerRZ_lt;lra |lra].
Qed.

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

Definition sqrt_approx_total_seq := make_mf (fun x yn => forall n, (yn n) \from (sqrt_approx_total n x)).
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

Lemma sqrt_total_lim x y: (0 <= x) -> (efficient_limit \o_R sqrt_approx_total_seq) x y -> (y = sqrt x).
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

Lemma sqrt_total_as_lim :  (lim_eff \o sqrt_approx_total_seq)|_IR_nonneg \tightens ((F2MF sqrt)|_IR_nonneg).
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
  by rewrite (sqrt_total_lim xprp1 xprp2').
Qed.



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
  exists (Rmult_rlzrf' (mp (tpnIR p) (sqrt_approx_n psi (n+(Z.to_nat p)))) q); exists (Nat.max m1 m2).
  by rewrite ltn psipprp /=.
Qed.


Lemma lt_n_M_unique phi psi n b b' m m' : (lt_n_M (@pair B_(cs_nat) _ ((nat2csN n), (mp phi psi))) (m,tt)) = (Some b) -> (lt_n_M (@pair B_(cs_nat) _ ((nat2csN n), (mp phi psi))) (m',tt)) = (Some b') -> b = b'.
Proof.
  move => H1 H2.
  case (Nat.le_gt_cases m m') => e.
  - have := (lt_n_M_monotonic H1 e).
    rewrite H2.
    by case.
  have e' : (m' <= m)%coq_nat by lia.
  have := (lt_n_M_monotonic H2 e').
  rewrite H1.
  by case.
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

Lemma sqrt_approx_total_rlzrM_spec n : \F_(use_first (sqrt_approx_total_rlzrM n)) \solves (sqrt_approx_total n).
Proof.
  move => phi x phin dom.
  rewrite <- (sfrst_dom (sqrt_approx_total_rlzrM n)).
  split => [|Fq prp]; first by apply FM_dom;apply (sqrt_approx_rlzrM_is_total n phin).
  have psin : (tpnIR (-2*(Z.of_nat n))%Z) \is_name_of (/ 2 ^ (2 * n)%nat).
  - rewrite <- powerRZ2_neg_pos, Nat2Z.inj_mul, <- Z.mul_opp_l.
    by apply tpnIR_spec.
  case (prp 0%nat) => m0 m0prp.
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
    case (prp q) => N Nprp.
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
Search _ (use_first).

Definition sqrt_approx_totalM_slow phi mnq := (sqrt_approx_total_rlzrM mnq.2.1 phi (mnq.1,mnq.2.2)).

Lemma sqrt_approx_totalM_slow_spec phi : forall (n :nat ), exists N,  forall m q, ((N <= m)%nat -> (isSome (sqrt_approx_totalM_slow phi (m,(n,q))) -> (isSome (sqrt_approx_totalM_slow phi (N, (n,q)))))) /\ ((m < N)%nat -> (sqrt_approx_totalM_slow phi (m,(n,q))) = None).
Proof.                                                                                             
Admitted.

Lemma sqrt_approx_totalM_speedup_spec phi (f : nat -> nat) : (forall n, (n <= (f n))%nat ) -> forall n, exists N,  forall m q, ((N <= (f m))%nat -> (isSome (sqrt_approx_totalM_slow phi ((f m),(n,q))) -> (isSome (sqrt_approx_totalM_slow phi ((f N), (n,q)))))) /\ (((f m) < N)%nat -> (sqrt_approx_totalM_slow phi ((f m),(n,q))) = None).
Proof.
  move => prp n.
  case (sqrt_approx_totalM_slow_spec phi n) => N Nprp.
  case (@classical_count.well_order_nat (fun m => (N <= (f m))%coq_nat)) => [| M [/leP Mprp1 Mprp2]]; first by exists N;apply /leP.
  exists M => m q.
  have [N1 N2] := (Nprp (f m) q).
  split => H1.
  move => H2.
  rewrite /sqrt_approx_totalM_slow/sqrt_approx_total_rlzrM.
Admitted.
Definition sqrt_approx_totalM phi mnq := (sqrt_approx_totalM_slow phi ((speedup mnq.1 13),(mnq.2.1,(speedup mnq.2.2 13)))).


Definition uniform_selection B Q' A' (slct : (B -> nat * Q' -> option A') -> B -> nat*Q' -> option A') M phi := exists m', forall m q a, ((slct M) phi (m,q)) = (Some a) -> (slct M phi (m,q)) = (M phi (m',q)).

  
Lemma sqrt_approx_total_rlzrM_spec2 : \F_(use_first (sqrt_approx_totalM_slow)) \solves ((sqrt_approx_total_seq : (IR ->> (IR \^w)))).
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

Lemma sqrt_approx_dom phi (x : IR) : (phi \is_name_of x) ->  {phi | phi \from (partial_functions.domain (get_pf sqrt_approx_totalM_slow))}.
Proof.
  move => phin.
  exists phi.
  simpl.
  have -> : (use_first sqrt_approx_totalM_slow phi) = (PhiN.use_first (sqrt_approx_totalM_slow phi)) by apply functional_extensionality.
  rewrite <-sfrst_tot.
  by apply (sqrt_approx_tot phin).
Qed.
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
  (* exists (evaluate H). *)
  exists (evaluate (speedup_admitted phi)).
  by apply speedup_admitted2.
  (* case (sqrt_approx_total_rlzrM_spec2 phin (sqrt_approx_total_seq_is_total x)  ) => _ prp. *)
  (* case (prp (evaluate H)) => [| y yprp]; first by apply FM_Phi;apply eval_spec. *)
  (* by exists y. *)
Qed.

Definition sqrt_total_rlzr := (\F_limit_eff_rlzrM \o \F_(use_first sqrt_approx_totalM_slow)).

Lemma sqrt_total_correct :  sqrt_total_rlzr \solves (F2MF sqrt)|_(IR_nonneg).
Proof.
   have t := (slvs_tight _ sqrt_total_as_lim).
   rewrite /sqrt_total_rlzr.
   apply t.
   apply (slvs_tight (slvs_comp F_lim_eff_rlzrM_spec sqrt_approx_total_rlzrM_spec2)).
   by apply tight_restr_w.
Qed.

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
    apply sqrt_total_lim => //.
    by exists y.
  have [H1 H2] := H.
  exists (evaluate H1).
  have := (@eval_spec _ _ _ H1).
  rewrite <-FM_Phi => e.
  by apply (H2 _ e).
Qed.


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
Qed.

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
Definition print_interval d := ((to_pair (lower d)), (to_pair (upper d)), (qtoPair (diamQ d))).
Definition print_interval' I := match I with
                                 | None => (print_interval (two 0%nat))
                                 | Some d => (print_interval d)
                                  end.
(* (* Definition sqrt2' (p : nat):= (print_interval (sqrt2 p)). *) *)
(* Definition sqrt2'' m p := (print_interval' (use_first limit_eff_rlzrM sqrt2_approx (m,p)%nat)). *)
(* Definition log_map_Q N := (evaluate (log_map1_in_dom N)). *)
(* Compute ((FloattoIR 1%Z (-1)%Z) \: (FloattoIR 5%Z (-10)%Z) 10%nat). *)
(* Definition logistic_map_mp_rlzr' (N :nat) (p : BinPos.positive):= log_map_Q N (1#(10 ^ p)). *)
(* Extraction "logisticC" cmp_float mantissa_shr logistic_map_mp_rlzr'. *)
Extraction "sqrt2" cmp_float mantissa_shr sqrt2'.
