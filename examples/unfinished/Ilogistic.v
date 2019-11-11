From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_rlzrs.
From metric Require Import reals.
Require Import all_cs_base classical_mach.
Require Import Reals Psatz FunctionalExtensionality ClassicalChoice.
Require Import axioms all_cs cs_mtrc metric_names hyper_spaces.
From metric Require Import all_metric reals standard Qmetric.
Require Import Ibounds IrealsZ.
From Interval Require Import Interval_tactic.
From Interval Require Import Interval_specific_ops Interval_bigint_carrier Interval_stdz_carrier.
From Interval Require Import Interval_interval_float_full Interval_interval.
From Interval Require Import Interval_xreal.
Require Import multivalued_composition.
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

Lemma make_iter_correct T (rlzrf : T -> names_IR) m phi  (x : R): (rlzrf phi) \is_name_of x -> (make_iter rlzrf phi m) \is_name_of x. 
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
  suff xyname : (pair (phi,psi)) \is_name_of (x,y).
  - apply make_iter_correct.
    have  :=  (Rminus_rlzr_spec ).
    rewrite F2MF_rlzr => sp.
    by apply (sp _ _ xyname).
    rewrite prod_name_spec.
  by rewrite lprj_pair rprj_pair.
Qed.
Lemma div_comp phi psi (x y : R) : (y <> 0) -> (phi \is_name_of x) -> (psi \is_name_of y) -> (phi \: psi \is_name_of (x/y)).
Proof.
  move => yneg0 phin psin.
  suff xyname : (pair (phi,psi)) \is_name_of (x,y).
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
Definition speedup n := (2 ^ n)%nat.
Definition IR_RQ_rlzrM' := (fun phi neps => IR_RQ_rlzrM (speedup neps.1) phi neps.2).
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
Check representation.

Lemma one_describes_one : (one \is_name_of 1).
Proof.
  suff <- : (D2R (Float 1%Z 0%Z)) = 1 by apply FloattoIR_correct.
  by rewrite D2R_Float //=;lra.
Qed.

Lemma sqrt_approx_step (phi psi : names_IR) (x x0 :IR) : (phi \is_name_of x) -> (psi \is_name_of x0) -> (@representation IR (sqrt_approx_rlzr psi 0%nat phi) x0) /\ forall n y, (@representation IR (sqrt_approx_rlzr psi n phi) y) -> (y <> 0) -> (@representation IR (sqrt_approx_rlzr psi n.+1 phi) (/2 * (y + (x /y)))).
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
Definition sqrt_approx_n' x : B_(IR\^w) := (fun nm => (sqrt_approx_n x nm.1 (speedup nm.2))).
Lemma speedup_correct : forall (x : IR) (phi : B_(IR)), (phi \is_name_of x) -> (fun (p : Q_(IR)) => (phi (speedup p)))  \is_name_of x.
Proof.
  move => x phi [phin1 phin2].
  split => n; first by apply phin1.
  case (phin2 n) => N Nprp.
  exists N => k kprp.
  apply (Nprp (speedup k)).
  rewrite /speedup.
  apply /leP.
  move /leP :  kprp => kprp.
  apply /Nat.le_trans.
  apply kprp.
  elim k => [| k' IH]; first by lia.
  simpl.
  rewrite Nat.add_0_r.
  suff : (0 < 2 ^ k')%coq_nat by lia.
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

Definition swap (X Y : cs) (xy : (X * Y)) := (xy.2, xy.1).
Definition mf_swap X Y := (F2MF (@swap X Y)).
Definition swap_rlzr (X Y: cs): B_ (X \*_cs Y) ->> B_ _:= (F2MF (fun (phi : B_ (X \*_cs Y)) => (pair ((rprj phi),(lprj phi))))).
Definition brd (X Y Z : cs) (xyz : (X * (Y * Z))) := ((xyz.1, xyz.2.1),xyz.2.2).
Definition brd_rlzrf (X Y Z : cs) := (fun (phi : B_ (X \*_cs (Y \*_cs Z))) => (pair (pair (lprj phi, lprj (rprj phi)),rprj (rprj phi)))): (B_ (X \*_cs (Y \*_cs Z)) -> B_ ((X \*_cs Y) \*_cs Z)).
Definition diag_rlzrf X (phi : B_ X) := (pair (phi,phi)).

Lemma diag_rlzrf_spec X : (F2MF (@diag_rlzrf X)) \solves mf_diag.
  rewrite F2MF_slvs => phi x phin.
  case => t /=tprp.
  exists (x,x); split; first by auto.
  exists (phi,phi).
  split; by [apply pairK | split].
Qed.  

Lemma brd_rlzrf_spec X Y Z : (F2MF (@brd_rlzrf X Y Z)) \realizes (@brd X Y Z).
Proof.
  rewrite F2MF_rlzr => phi [x [y z]] /prod_name_spec [phin1 /prod_name_spec [phin2 phin3]].
  rewrite /brd /brd_rlzrf /=.
  exists (pair (lprj phi, lprj (rprj phi)), (rprj (rprj phi))).
  split => //.
  split => //.
  by exists ((lprj phi),(lprj (rprj phi))).
Qed.

Definition tpnIR n := (FloattoIR 1%Z n).

Lemma tpnIR_spec n : (tpnIR n) \is_name_of (powerRZ 2 n).
Proof.
  rewrite /tpnIR.
  suff -> : (powerRZ 2 n) = (D2R (Float 1%Z n)) by apply FloattoIR_correct.
  by rewrite D2R_Float;lra.
Qed.
Definition lt_eps_rlzrf :=  which_rlzrf \o_f
                                        (fprd_frlzr K_truth_rlzrf  K_truth_rlzrf)
                                        \o_f (fprd_frlzr ltK_rlzr ltK_rlzr)
                                        \o_f (@fprd_frlzr (IR \*_cs (IR \*_cs IR)) (IR \*_cs IR) (IR \*_cs (IR \*_cs IR)) (IR \*_cs IR)
                                                          (@rprj names_IR (names_IR \*_ns names_IR))
                                                          ((@fprd_frlzr ((IR \*_cs IR) \*_cs IR) IR ((IR \*_cs IR) \*_cs IR) IR (@rprj (names_IR \*_ns names_IR) names_IR) (Rplus_rlzrf' \o_f (@lprj (names_IR \*_ns names_IR) names_IR ))) \o_f (@diag_rlzrf ((IR \*_cs IR) \*_cs IR)) \o_f (@brd_rlzrf IR IR IR))) \o_f (@diag_rlzrf (IR \*_cs (IR \*_cs IR))).
Definition lt_epsK := (make_mf (fun (epsxy : R * (R*R)) k => (let (eps,xy) := epsxy in
                                            let (x,y) := xy in
                                             (eps > 0) /\ (x < y -> k = true_K) /\ (y+eps < x -> k = false_K)) /\ k <> bot_K)).
Definition lt_eps := (make_mf (fun (epsxy : R * (R*R)) b => (let (eps,xy) := epsxy in
                                            let (x,y) := xy in
                                             (x < y -> b = true) /\ (y+eps < x -> b = false)))).
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

Lemma prd (S T U V: cs) (F : S ->> T) (G : U ->> V) H  : {f | (F2MF f) \solves F} -> {g | (F2MF g) \solves G} -> H =~= F ** G -> {h | (F2MF h) \solves H}.
Proof.
  case => f fprp; case => g gprp hprp.
  exists (fprd_frlzr f g).
  rewrite fprd_frlzr_rlzr.
  rewrite slvbl_prpr => //.
  by apply prod.fprd_rlzr_spec; [apply fprp | apply gprp]. 
  by auto.   
Qed.
Lemma which_spec x y : ((x = top) <-> (true_K \from (which (x,y)))) /\ ((y = top) <-> (false_K \from (which (x,y)))). 
Proof.
Admitted.
Lemma comp_F2MF S T T' (f : S ->> T) (g : T' -> S) t' : (f \o (F2MF g)) t' === (f (g t')).
Proof.
  exact /comp_F2MF.
Qed.

Lemma lt_epsK_rlzr_spec : {f | (F2MF f) \solves lt_epsK}.
Proof.
  have fp : forall f, (f =~= f) by auto.
  apply /comp => //.
  exists which_rlzrf.
  apply which_rlzrf_spec.
  apply /comp => //.
  apply /prd => //.
  exists K_truth_rlzrf.
  apply Ktruth_rlzr_spec.
  exists K_truth_rlzrf.
  apply Ktruth_rlzr_spec.
  apply /comp => //.
  apply /prd => //.
  exists (ltK_rlzr : B_(IR \*_cs IR) -> B_(cs_Kleeneans)).
  apply ltK_rlzr_spec.
  exists (ltK_rlzr : B_(IR \*_cs IR) -> B_(cs_Kleeneans)).
  apply ltK_rlzr_spec.
  apply /comp => //.
  apply /prd => //.
  exists ((@rprj _ _): (B_(IR \*_cs (IR \*_cs IR)) -> _)).
  apply snd_rlzr_spec.
  apply /comp => //.
  apply /prd => //.
  apply /comp => //.
  exists (Rplus_rlzrf : (B_(IR \*_cs IR) -> _)).
  apply Rplus_rlzr_spec.
  apply /prd => //.
  exists (ssrfun.id : B_(IR) -> B_(IR)).
  apply id_rlzr.
  exists (@rprj _ _).
  apply snd_rlzr_spec.
  apply /comp => //.
  exists (@lprj _ _).
  apply fst_rlzr_spec.
  exists (@rprj _ _).
  apply snd_rlzr_spec.
  exists (@diag_rlzrf _).
  apply diag_rlzrf_spec.
  exists (@diag_rlzrf _).
  apply diag_rlzrf_spec.
  rewrite /lt_epsK.
  move => [eps [x y]].
  rewrite <-!F2MF_fprd.
  rewrite !F2MF_comp_F2MF.
  rewrite <-!F2MF_fprd.
  rewrite !F2MF_comp_F2MF.
  rewrite <-!F2MF_fprd.
  rewrite !F2MF_comp_F2MF.
  rewrite comp_F2MF => k.
  split =>  [ [[epsgt0 [xltyt yltxf]] snb] | ].
  rewrite /K_truthf /uncurry /=.
  case : (total_order_T x y) => [[xlty | xeqy ] | xgty]; case : (total_order_T (eps+y) x) => [[yltx | yeqx ] | ygtx]; try by auto; try by lra.
  Search _ from composition.
Admitted.
(* assumes x > 0 *)
Fixpoint scale_up phi cnt m := match m with
                                 | 0%nat => (None, cnt)
                                 | m'.+1 => 
                                   match (lt_eps_rlzrf (@pair names_IR _ ((tpnIR (-2)%Z),(mp phi (tpnIR (-2)%Z)))) m) with
                                   | (Some true) => (scale_up ((FloattoIR 1%Z 2%Z) \* phi) (cnt+1)%Z m')
                                   | (Some false) => ((Some phi),cnt)
                                   | None => (None, cnt)
                                   end
                                 end.

Lemma scale_up_spec phi x psi m :(0 < x) -> (phi \is_name_of x) -> forall cnt cnt', ((scale_up phi cnt m) = (Some psi, cnt') -> (exists y, psi \is_name_of y /\ (/ 4) <= y)).
Proof.
  move => gt0 phin.
  elim m => [| m']; first by auto.
Admitted.  
Fixpoint scale_down phi cnt m := match m with
                                 | 0%nat => (None, cnt)
                                 | m'.+1 => 
                                   match (lt_eps_rlzrf (@pair names_IR _ ((tpnIR (-2)%Z),(mp (tpnIR 0%Z) phi))) m) with
                                   | (Some true) => (scale_down ((FloattoIR 1%Z (-2)%Z) \* phi) (cnt+1)%Z m')
                                   | (Some false) => ((Some phi),cnt)
                                   | None => (None, cnt)
                                   end
                                 end.

Fixpoint scale phi m := match (scale_up phi 0 m) with
                          | (None, n) => (None, n)
                          | ((Some psi), n) =>
                            match (scale_down psi 0 m) with
                            | (None, m) => (None, m)
                            | ((Some phi0), m) => ((Some phi0), (m-n)%Z)
                            end
                         end.
Definition sqrt_approx_total (n : nat) phi mq := match (lt_eps_rlzrf (@pair names_IR _ ((tpnIR (-4*(Z.of_nat n))%Z),(mp phi (tpnIR (-2*(Z.of_nat n))%Z)))) mq.1) with
                                          | (Some true)  => (Some (I.fromZ 0))
                                          | (Some false) =>
                                              let (p, s) := (scale phi mq.1) in
                                              match p with
                                                | None => None
                                                | (Some psi) => (Some ((tpnIR s) \* (sqrt_approx_n psi n) mq.2))
                                              end
                                          | _ => None
                                        end.
Definition sqrt_approx_total' n phi mq := (sqrt_approx_total n phi ((speedup mq.1),(speedup mq.2))).

Lemma sqrt_approx_totalt n phi : \Phi_(sqrt_approx_total' n phi) \is_total.
Admitted.
Definition sqrt_approx_f phi nm := (evaluate (sqrt_approx_totalt nm.1 phi) nm.2).
Lemma sqrt_app_in_dom phi : \Phi_(limit_eff_rlzrM (sqrt_approx_f phi)) \is_total.
Admitted.
Definition sqrtfunction phi := (evaluate (sqrt_app_in_dom phi)).
Lemma sqrtfun_in_dom phi : \Phi_(IR_RQ_rlzrM' (sqrtfunction phi)) \is_total.
Admitted.
Definition sqrtq phi := (evaluate (sqrtfun_in_dom phi)).
(* Definition sqrt' phi m := match (sqrt_approx_total phi n 100%nat) with *)
(*                            | (Some phi) => phi *)
(*                            | None => (ZtoIR 111%Z) *)
(*                           end. *)

(* Lemma lt_eps_spec x y eps :  ((lt_eps eps (x,y) true_K) -> (x < y)) /\ ((lt_eps eps (x,y) false_K) -> (y < x + eps)) /\ not (lt_eps eps (x,y) bot_K). *)
(* Proof. *)
(*   rewrite /lt_eps. *)
(*   split; [|split]. *)
(*   case. *)
(*   case. *)
(*   case => a b H. *)
(*   Search _ "_ \from _" composition. *)
(*   move => H. *)
(* Lemma sqrt2_in_dom : \Phi_(IR_RQ_rlzrM' sqrt2) \is_total. *)
(* Admitted. *)
(* Definition sqrt2_approx' n m := (sqrt2_approx (n,m)). *)
(* Lemma sqrt2_approx_in_dom m : \Phi_(IR_RQ_rlzrM' (sqrt2_approx' m)) \is_total. *)
(* Admitted. *)
(* Definition sqrt2Q := (evaluate (sqrt2_in_dom)). *)
(* Definition sqrt2Q' n := (evaluate (sqrt2_approx_in_dom n)). *)
Definition QtoIR' q := (QRtoIR (fun _ => q)). 
Definition sqrt2' a b (p : BinPos.positive):= sqrtq (QtoIR' (a # b)) (1#(10 ^ p)). 
Definition qtoPair q := match q with
                          (q1 # q2) => (q1, q2)
                          end.
Definition print_interval d := ((to_pair (lower d)), (to_pair (upper d)), (qtoPair (diamQ d))).
Definition print_interval' I := match I with
                                 | None => (print_interval (two 0%nat))
                                 | Some d => (print_interval d)
                                  end.
(* Definition sqrt2' (p : nat):= (print_interval (sqrt2 p)). *)
Definition sqrt2'' m p := (print_interval' (use_first limit_eff_rlzrM sqrt2_approx (m,p)%nat)).
Definition log_map_Q N := (evaluate (log_map1_in_dom N)).
Compute ((FloattoIR 1%Z (-1)%Z) \: (FloattoIR 5%Z (-10)%Z) 10%nat).
Definition logistic_map_mp_rlzr' (N :nat) (p : BinPos.positive):= log_map_Q N (1#(10 ^ p)).
Extraction "logisticC" cmp_float mantissa_shr logistic_map_mp_rlzr'.
Extraction "sqrt2" cmp_float mantissa_shr sqrt2' sqrt2''.
