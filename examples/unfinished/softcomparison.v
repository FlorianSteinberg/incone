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

Local Open Scope Z_scope.
Import QArith.
Local Open Scope R_scope.
(* Some helper functions we need that should be moved to another file later *)

Definition nat2csN (n : nat) := (fun (_ : unit) => n). 
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
Defined.

Lemma comp_tight (S T U : cs) (F : S ->> T) (G : U ->> S)  H : {f | (F2MF f) \solves F} -> {g | (F2MF g) \solves G} -> (F \o G) \tightens H -> {h | (F2MF h) \solves H}.
Proof.
  case => f fprp.
  case => g gprp prp.
  exists (f \o_f g).
  rewrite <- F2MF_comp_F2MF. 
  by apply (slvs_tight (slvs_comp fprp gprp)).
Defined.


Lemma prd (S T U V: cs) (F : S ->> T) (G : U ->> V) H  : {f | (F2MF f) \solves F} -> {g | (F2MF g) \solves G} -> H =~= (F ** G) -> {h | (F2MF h) \solves H}.
Proof.
  case => f fprp; case => g gprp hprp.
  exists (fprd_frlzr f g).
  rewrite fprd_frlzr_rlzr.
  rewrite slvbl_prpr => //.
  by apply prod.fprd_rlzr_spec; [apply fprp | apply gprp]. 
  by trivial.   
Defined.
Lemma comp_F2MF S T T' (f : S ->> T) (g : T' -> S) t' : (f \o (F2MF g)) t' === (f (g t')).
Proof.
  exact /comp_F2MF.
Qed.

Section epsilon_test_kleenean.
(* We define a multivalued eps test to compare two real numbers
   For eps > 0, (lt_epsK x y eps) must be true if x+eps <= y and must be false if y <= x 
   otherwise it can be both true or false *)
Definition lt_epsK := (make_mf (fun (epsxy : R * (R*R)) k => (let (eps,xy) := epsxy in
                                            let (x,y) := xy in
                                             (eps > 0) /\ (x+eps <= y -> k = true_K) /\ (y <= x -> k = false_K)) /\ k <> bot_K)).

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

(* We show that there constructively exists a realizer function for the operator *)
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
Defined.

(* We usually want the test in the form eps = (/ 2 ^ n) and therefore define this version, too *)
Definition lt_nK := (make_mf (fun (nxy : nat * (R*R)) k => (let (n,xy) := nxy in
                                            let (x,y) := xy in
                                              (x+(/ 2 ^ n) <= y -> k = true_K) /\ (y <= x -> k = false_K)) /\ k <> bot_K)).

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
Defined.

Definition lt_nk_rlzrf := projT1 lt_nK_rlzr_spec.

(* As / 2 ^ n is always positive lt_nK is total *)
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

End epsilon_test_kleenean.

Section lt_n_test.
(* The previously defined lt_n test always returns true or false, thus we can define a boolean version *)

Definition lt_n := (make_mf (fun (nxy : nat * (R*R)) b => (let (n,xy) := nxy in
                                            let (x,y) := xy in
                                             (x+(/ 2 ^ n) <= y -> b = true) /\ (y <= x -> b = false)))).

(* We get a realizer as composition of the (partial) mapping from Kleeneans
 to Booleans and the test on the Kleeneans *)
Definition lt_n_rlzr := (\F_K2B_rlzrM : B_(cs_Kleeneans) ->> B_(cs_bool)) \o (F2MF lt_nk_rlzrf).

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

Lemma lt_n_rlzr_spec : lt_n_rlzr \solves lt_n.
Proof.
  rewrite lt_n_spec /lt_n_rlzr.
  by apply slvs_comp; [apply F_K2B_rlzrM_spec | apply (projT2 lt_nK_rlzr_spec)].
Qed.  

(* The machine for lt_n *)
Definition lt_n_M := fun phi => (K2B_rlzrM (lt_nk_rlzrf phi)).

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
Lemma lt_n_M_monotonic phi psi n b m : (lt_n_M (@pair B_(cs_nat) _ ((nat2csN n), (mp phi psi))) (m,tt)) = (Some b) -> forall m', (m <= m')%coq_nat -> (lt_n_M (@pair B_(cs_nat) _ ((nat2csN n), (mp phi psi))) (m',tt)) = (Some b).
Proof.
  rewrite /lt_n_M => prp m' m'prp.
  by apply (K2B_rlzrM_monotonic prp m'prp).
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
End lt_n_test.

Section magnitude.
(* As an application we define a multivalued magnitude function using the soft comparison *)
Definition magnitude := make_mf (fun x z => ((powerRZ 2 z) < x < (powerRZ 2 (z+2)))).

(* We first define tha magnitude function for 0 < x <= 1 *)
Definition magnitude1 := make_mf ((fun x n => ((/ 2 ^ n) < x < 4*(/2 ^ n)))).

Lemma magnitude_spec x n: (true \from (lt_n (n.+2,((/ 2 ^ n),x)))) /\ true \from (lt_n (n.+2, (x, 3*(/ 2 ^n)+(/ 2 ^ (n.+2))))) -> n \from (magnitude1 x).
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

(* We can define a machine that checks for a given n if it is in magnitude1 *)
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

Lemma magnitude_check_cmp_names n : ((FloattoIR 3%Z 0%Z) \* (FloattoIR 1%Z (- Z.of_nat n)%Z)
                                     \+ (FloattoIR 1%Z (- Z.of_nat n.+2)%Z) : B_(IR)) \is_name_of ((3 * (/ 2 ^ n) + (/ 2 ^ (n.+2))) : IR) /\ (FloattoIR 1%Z (- (Z.of_nat n))%Z) \is_name_of (/ 2 ^ n).
Proof.                                  
  split.
  - rewrite <- !powerRZ2_neg_pos.
    have p n': (powerRZ 2 (n')) = (D2R (Float 1%Z (n')%Z)) by rewrite D2R_Float;lra.
    rewrite !p /mp.
    have /F2MF_rlzr cln := cleanup_spec.
    have /F2MF_rlzr pls := Rplus_rlzr_spec.
    have /F2MF_rlzr mul := Rmult_rlzr_spec.
    apply cln.
    apply (pls (pair (_,_)) ((3 * (D2R (Float 1%Z (- Z.of_nat n)%Z))), (D2R (Float 1%Z (- Z.of_nat n.+2)%Z)))).
    rewrite prod_name_spec lprj_pair rprj_pair.
    split; try by apply FloattoIR_correct.
    apply cln.
    apply (mul _ (3, (D2R (Float 1%Z (- Z.of_nat n)%Z)))).
    rewrite prod_name_spec lprj_pair rprj_pair.
    split; try by apply FloattoIR_correct.
  have  := (FloattoIR_correct 1%Z (- (Z.of_nat n))%Z).
  by rewrite D2R_Float Rmult_1_l powerRZ2_neg_pos.
Qed.

Lemma magnitude_check_correct phi n m x : (phi \is_name_of x) -> (0 < x <= 1) -> (magnitude_checkM phi n m)  -> n \from (magnitude1 x).
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


(* There always exists n,m such that magnitude_check returns true *)
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

(* the magnitude realizer searches for the first value the check machine returns true *)
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

Lemma magnitude_rlzrM_correct phi x m n : (phi \is_name_of x) -> (0 < x <= 1) -> (magnitude_rlzrM phi m) = (Some n) -> (n \from magnitude1 x).
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

Lemma magnitude_rlzrM_spec phi x : (phi \is_name_of x) -> (0 < x <= 1) -> exists m n, (magnitude_rlzrM phi m) = (Some n) /\ (n \from magnitude1 x).
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

(* Next we extend to all positive real numbers *)
Lemma magnitude_inv x n: (0 < x) -> n \from (magnitude1 (/ x)) ->  (/ 4) * (2 ^ n) < x < (2 ^ n).
Proof.
  move => xlt /= [nprp1 nprp2].
  split.
  - apply Rinv_lt_cancel; first by lra.
    rewrite Rinv_mult_distr; try by lra.
    apply pow_nonzero;lra.
  by apply Rinv_lt_cancel; [apply pow_lt |];lra.
Qed.

Lemma magnitude_1 x : ((/ 2) < x < 2) -> 1%nat \from (magnitude1 x).
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
                                          match (magnitude_rlzrM ((FloattoIR 1%Z 0%Z) \: phi) m) with
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
  have phind : ((cleanup \o_f Rdiv_rlzrf) (mp (FloattoIR 1%Z 0%Z) phi) : B_(IR)) \is_name_of (/ x).
  - have xn : (x <> 0) by lra.
    have /F2MF_rlzr cln := cleanup_spec.
    have /F2MF_slvs div := Rdiv_rlzr_spec.
    apply cln.
    have -> : (/ x = (1 / x)) by lra.
    case (div (pair ((FloattoIR 1%Z 0%Z),phi)) (1, x)); [by rewrite prod_name_spec lprj_pair rprj_pair | by exists (1/x) | ].
    move => xy [[_ /=  xy_prop] P].
    rewrite <- xy_prop.                                                              
    by apply P.                                                    
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
  have phin' : ((cleanup \o_f Rdiv_rlzrf) (mp (FloattoIR 1%Z 0%Z) phi) : B_(IR)) \is_name_of (/ x).
  - have xn : (x <> 0) by lra.
    have /F2MF_rlzr cln := cleanup_spec.
    have /F2MF_slvs div := Rdiv_rlzr_spec.
    apply cln.
    have -> : (/ x = (1 / x)) by lra.
    case (div (pair ((FloattoIR 1%Z 0%Z),phi)) (1, x)); [by rewrite prod_name_spec lprj_pair rprj_pair | by exists (1/x) | ].
    move => xy [[_ /=  xy_prop] P'].
    rewrite <- xy_prop.                                                              
    by apply P'.                                                    
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
  
End magnitude.
