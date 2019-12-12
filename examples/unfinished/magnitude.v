(* Implementation of soft comparisons using machine composition *)
From Coquelicot Require Import Coquelicot.
From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_rlzrs.
From metric Require Import reals.
Require Import all_cs_base classical_mach.
Require Import Reals Psatz FunctionalExtensionality ClassicalChoice.
Require Import axioms all_cs cs_mtrc metric_names hyper_spaces.
Require Import continuous_machines.
Require Import monotone_machine_composition.
From metric Require Import all_metric reals standard Qmetric.
Require Import search.
Require Import computable_reals.
Require Import Ibounds.
Require Import softcomparison.

(* Some helper functions we need that should be moved to another file later *)
Definition nat2csN (n : nat) := (fun (_ : unit) => n). 
Definition Z2csZ (z : Z) := (fun (_ : unit) => z). 


Section magnitude.
(* As an application we define a multivalued magnitude function using the soft comparison *)
Definition magnitude := make_mf (fun x z => ((powerRZ 2 z) < x < (powerRZ 2 (z+2)))).

(* We first define tha magnitude function for 0 < x <= 1 *)
Definition magnitude1 := make_mf ((fun x n => (0 < x <= 1) /\  ((/ 2 ^ n) < x < 4*(/2 ^ n)))).

(* We write a check function for magnitude1 *)
Definition magnitude_check_rhs n (x : R) := (n.+2, (x, 3 * (/ 2 ^ n) + (/ 2 ^ (n.+2)))).
Definition magnitude_check_lhs n (x : R) := (n.+2, ((/ 2 ^ n), x)).

Definition magnitude_check n := (F2MF (uncurry andb)) \o ((lt_n \o (F2MF (magnitude_check_rhs n)))  ** (lt_n \o (F2MF (magnitude_check_lhs n))) \o mf_diag).

Lemma ltn_tot : lt_n \is_total.
Proof.
  move => a.
  rewrite lt_n_spec /lt_nK/B2K.
  rewrite <-comp_dom_codom; first by rewrite dom_lt_nk.
  rewrite <- codom_dom_inv.
  case => Hd; [ by exists false | by exists true |].
  by case Hd => [_ [_ H0]].
Qed.

Lemma dom_magnitude_check n : (magnitude_check n) \is_total.
Proof.
  rewrite /magnitude_check.
  apply comp_tot; last by apply F2MF_tot.
  apply comp_tot; first by apply F2MF_tot.
  apply fprd_tot; apply comp_tot; try by apply F2MF_tot.
  apply ltn_tot.
  apply ltn_tot.
Qed.

Lemma magnitude_check_spec n x: (0 < x <= 1) -> (true \from (magnitude_check n x)) -> n \from (magnitude1 x).
Proof.
  move => xbnd.
  rewrite /magnitude_check => H.
  suff : (true \from (lt_n (n.+2,((/ 2 ^ n),x)))) /\ true \from (lt_n (n.+2, (x, 3*(/ 2 ^n)+(/ 2 ^ (n.+2))))).
  - move => [[_ H12] [_ H21]].
    have xlt : (x < (3*(/ 2 ^ n))+(/ 2 ^ (n.+2))) by apply Rnot_le_lt => e;move : (H21 e).
    have xgt : ((/2 ^ n) < x) by apply Rnot_le_lt => e;move : (H12 e).
    split; [by apply xbnd| split;[by lra|]].
    suff : (/ 2 ^ n.+2) < (/ 2 ^ n) by lra.
    rewrite (@tpmn_half n).
    rewrite (@tpmn_half n.+1).
    suff : 0 < (/ 2 ^ (n.+2)) by lra.
    by apply tpmn_lt.
    case H => [[[b1 b2]  [[[xx [xxprp [[[nxx [nxxprp prp1]] _] [[nxx' [nxxprp' prp1']] _]]]] _] prp2]]] _.
    move : xxprp nxxprp nxxprp' prp1 prp1'.
    rewrite /mf_diag/mf.diag/magnitude_check_rhs/magnitude_check_lhs => <- <- <- H1 H2.
    suff [<-{1} <-] : (b1 = true) /\ (b2 = true) by split.
    move : prp2.
    rewrite /uncurry /=.
    by apply /andP.
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

Lemma magnitude_check_true x n : (true \from (lt_n (n.+2,((/ 2 ^ n), x)))) -> (true \from (lt_n (n.+2,(x, 3*(/ 2 ^n) + (/ 2 ^ (n.+2)))))) -> (true \from (magnitude_check n x)).
Proof.
  move => H1 H2.
  rewrite /magnitude_check.
  split; last by rewrite F2MF_dom. 
  exists (true,true).
  rewrite /magnitude_check_rhs/magnitude_check_lhs.
  split; last by rewrite /uncurry /=.
  split.
  exists (x,x); split; first by trivial.
  split.
  split; first by exists (n.+2, (x,3 * (/2 ^ n)+(/2 ^ n.+2))).
  by case => m [y1 y2] [<- <- <- ]; exists true.
  split; first by exists (n.+2, ((/ 2 ^ n),x)).
  by case => m [y1 y2] [<- <- <- ]; exists true.
  case => y1 y2 /= [] <- <-.
  exists (true,true).
  split.
  split; first by exists (n.+2, (x,3 * (/2 ^ n)+(/2 ^ n.+2))).
  by case => m [y1' y2'] [<- <- <-]; exists true.
  split; first by exists (n.+2, ((/ 2 ^ n),x)).
  by case => m [y1' y2'] [<- <- <- ]; exists true.
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

Definition magnitude_check_mf := (make_mf (fun x n => (0 < x <= 1 /\ true \from (magnitude_check n x)) )). 
Lemma magnitude_check_tight : magnitude_check_mf \tightens magnitude1.
Proof.
  move => x [m [prp1 prp2]].
  split => [ |n [P1 P2]];last by apply (magnitude_check_spec n x).
  case (magnitude_n_exists x prp1) => n [nprp1 nprp2].
  exists n.
  suff : true \from (magnitude_check n x) by trivial.
  apply magnitude_check_true.
  by apply lt_n_nt1.
  by apply lt_n_nt2.
Qed.

Lemma magnitude_check_is_true x : (0 < x <= 1) -> exists n, true \from (magnitude_check n x) /\ not (false \from (magnitude_check n x)).
Proof.
  move => xbnd.
  case (magnitude_n_exists _ xbnd) => n [nprp1 nprp2].
  exists n.
  split.
  apply magnitude_check_true; by [apply lt_n_nt1 | apply lt_n_nt2].
  rewrite /magnitude_check/magnitude_check_rhs/magnitude_check_lhs.
  have andmf f: ((false \from ((F2MF (uncurry andb)) \o f) x)) -> (false, false) \from (f x) \/ (false, true) \from (f x) \/ (true, false) \from (f x).
  - case => [[[b1 b2 []]]].
    by case b1; case b2 => H1 /= // _ _; try by auto.
  have H1 := (lt_n_nf1 _ _ nprp1).
  have H2 := (lt_n_nf2 _ _ nprp2).
  move => H.
  have := (andmf _ H).
  rewrite !comp_F2MF.
  case => [H3 | [H3 | H3]].
  by apply H2;apply H3.
  by apply H2;apply H3.
  by apply H1;apply H3.
Qed.
(* Definition magnitude_check_mf := (make_mf (fun x n => (true \from (magnitude_check n x)) /\ not (false \from magnitude_check n x))).  *)
(* Lemma magnitude_check_tight : magnitude_check_mf \tightens magnitude1. *)
(* Proof. *)
(*   move => x [m [prp1 prp2]]. *)
(*   split => [ |n [p1 p2]]; last by apply (magnitude_check_spec n x). *)
(*   case (magnitude_n_exists x prp1) => n [nprp1 nprp2]. *)
(*   exists n. *)
(*   suff : true \from (magnitude_check n x) /\ not (false \from (magnitude_check n x)) by trivial. *)
(*   split. *)
(*   apply magnitude_check_true. *)
(*   by apply lt_n_nt1. *)
(*   by apply lt_n_nt2. *)
(*   rewrite /magnitude_check/magnitude_check_rhs/magnitude_check_lhs. *)
(*   have andmf f: ((false \from ((F2MF (uncurry andb)) \o f) x)) -> (false, false) \from (f x) \/ (false, true) \from (f x) \/ (true, false) \from (f x).  *)
(*   - case => [[[b1 b2 []]]]. *)
(*     by case b1; case b2 => H1 /= // _ _; try by auto. *)
(*   have H1 := (lt_n_nf1 _ _ nprp1). *)
(*   have H2 := (lt_n_nf2 _ _ nprp2). *)
(*   move => H. *)
(*   have := (andmf _ H). *)
(*   rewrite !comp_F2MF. *)
(*   case => [H3 | [H3 | H3]]. *)
(*   by apply H2;apply H3. *)
(*   by apply H2;apply H3. *)
(*   by apply H1;apply H3. *)
(* Qed. *)


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

Lemma magnitude_split x n: ((x < 2) -> (n \from (magnitude1 (x/2))) -> ((-Z.of_nat n)+1)%Z \from magnitude x) /\ (1 < x -> (n \from (magnitude1 (/x))) -> ((Z.of_nat n)-2)%Z \from (magnitude x)).
Proof.
  split; last first.
  - move => xbnd H.
    case (magnitude_inv x n); [by lra | by trivial |].
    move => b1 b2.
    by split; rewrite !powerRZ_add /=; try rewrite <- pow_powerRZ; lra.
  move => xbnd [nprp1 [b1 b2]].
  split;rewrite !powerRZ_add /=; try by lra.
  - by rewrite !powerRZ2_neg_pos /=;lra.
  by rewrite !powerRZ2_neg_pos /=;lra.
Qed.  

Lemma magnitude1_dom x : (0 < x <= 1) -> x \from (dom magnitude1).
Proof.
  move => xbnd.
  case (magnitude_n_exists x xbnd) => n [nprp1 nprp2].
  exists n.
  split => //.
  split.
  - apply /Rlt_le_trans/nprp1.
    suff : 0 < (/ 2 ^ n.+2) by lra.
    by apply tpmn_lt.
  apply /Rle_lt_trans.
  apply nprp2.
  by lra.
Qed.
Definition lt2_check (x : R) := (1%nat, (x, 2)).
Definition mag_check_lt := (F2MF (fun n => (-(Z.of_nat n)+1)%Z)) \o magnitude1 \o (F2MF (fun x => (x/2))).
Lemma mag_check_lt_dom x : (0 < x <= 2) -> x \from (dom mag_check_lt). 
Proof.
  move => H.
  rewrite /mag_check_lt.
  apply comp_subs_dom; last by rewrite F2MF_dom.
  move => x2 <-.
  apply comp_subs_dom; first by rewrite F2MF_dom.
  apply magnitude1_dom.
  by lra.
Qed.
Definition Rinv_mf := make_mf (fun x y => (x <> 0 /\ y = (Rinv x))).
Lemma Rinv_mf_div : Rinv_mf =~= Rdiv_mf \o (F2MF (fun x => (1,x))).
Proof. 
  move => x y.
  rewrite /Rinv_mf/Rdiv_mf.
  split => [[xprp p]|[/= [[x1 y1] [[<- <-] /= [p2 p3]]]]] /=.
  - split; [exists (1,x);split;[ |split]|] => /= //;try by lra.
    move => a <- /=.
    by exists (1/x).
  split => //.
  by lra.
Qed. 

Definition mag_check_gt := (F2MF (fun n => ((Z.of_nat n)-2)%Z)) \o magnitude1 \o Rinv_mf.

Lemma mag_check_gt_dom x : (1 <= x) -> x \from (dom mag_check_gt). 
Proof.
  move => H.
  rewrite /mag_check_gt/Rinv_mf.
  have xn0 : x <> 0 by lra.
  apply comp_subs_dom; last by exists (/ x).
  move => x2 [_ ->].
  apply comp_subs_dom; first by rewrite F2MF_dom.
  apply magnitude1_dom.
  split; first by apply Rinv_0_lt_compat;lra.
  have -> : (1 = (/ 1)) by lra.
  by apply Rinv_le_contravar;lra.
Qed.
Definition if_X (X : Type) (b : bool) (x : X) := if b then
                                                 inl x 
                                                 else
                                                 inr x.

Definition if_mv X := (F2MF (uncurry (@if_X X))).
Definition magnitude_mf := (F2MF (@paib _)) \o (mag_check_lt +s+ mag_check_gt) \o (if_mv R) \o ((lt_n \o (F2MF lt2_check)) ** mf_id) \o (mf_diag).

Lemma magnitude_dom x : (0 < x) <-> x \from (dom magnitude).
Proof.
  have helper : (ln 2 <> 0).
  - suff : (/ 2 < ln 2) by lra.
    by apply ln_lt_2.
  have xgt : (0 < x) -> (powerRZ 2 ((up ((ln (x/3))/(ln 2))))%Z) <= (2*x / 3).
  - move => H.
    rewrite !powerRZ_Rpower; try by lra.
    apply /Rle_trans.
    apply /Rle_Rpower; try by lra.
    have p t : ((up t) <= (t + 1)) by have := (archimed t);lra.
    apply p.
    rewrite Rpower_plus Rpower_1; last by lra.
    rewrite /Rpower /Rdiv Rmult_assoc Rinv_l; last by apply helper.
    by rewrite Rmult_1_r exp_ln;lra.
  have xlt : (0 < x) -> x <= 3*(powerRZ 2 ((up ((ln (x/3))/(ln 2))))%Z).
  - move => H.
    rewrite !powerRZ_Rpower; try by lra.
    suff : (x / 3) <= (Rpower 2 (up ((ln (x / 3))/(ln 2)))) by lra.
    have p t : (t <= (up t)) by have := (archimed t);lra.
    apply /Rle_trans; last first.
    apply /Rle_Rpower; try by lra.
    apply p.
    rewrite /Rpower /Rdiv Rmult_assoc Rinv_l; last by apply helper.
    by rewrite Rmult_1_r exp_ln; lra.
  split => [bnd |].
  - exists ((up ((ln (x/3))/(ln 2)))).
    split => /=.
    apply /Rle_lt_trans.
    apply xgt; try by lra. 
    by lra.
    apply /Rle_lt_trans.
    apply xlt; try by lra.
    rewrite !powerRZ_add /=; try by lra.
  move => [z [H1 H2]].
  apply /Rlt_trans/H1.
  by apply powerRZ_lt;lra.
Qed.

Lemma magnitude_mf_dom x : (0 < x) -> x \from (dom magnitude_mf).
Proof.
  move => H.
  rewrite /magnitude_mf.
  apply comp_subs_dom; last by rewrite F2MF_dom.
  case => x1 x2 [<- <-].
  apply comp_subs_dom.
  rewrite /lt2_check.
  case => [b y [[[[n [u v [[<- <- <- [H1 H2] H3 [H4]]]]]]] ]].
  rewrite /= in H4.
  rewrite <- H4.
  apply comp_subs_dom; last by rewrite F2MF_dom.
  rewrite /if_mv/uncurry/if_X.
  case => x0.
  move : H2.
  case b => //.
  move => H2.
  have H2' : (x < 2).
  - suff : not (2 <= x) by lra.
    move => H2'.
    by have := (H2 H2').
  case => <-.
  apply comp_subs_dom; first by rewrite F2MF_dom.
  case  (mag_check_lt_dom x) => [|z zprp]; first by lra.
  exists (inl z). 
  by apply zprp.
  move : H1.
  case b => //.
  move => H1.
  have H1' : (1 <= x).
  - suff : not (x + (/ 2 ^ 1) <= 2) by simpl;lra.
    move => H1'.
    by have := (H1 H1').
  case => <-.
  apply comp_subs_dom; first by rewrite F2MF_dom.
  case  (mag_check_gt_dom x) => [|z zprp]; first by lra.
  exists (inr z).
  by apply zprp.
  rewrite !fprd_dom.
  split; last by rewrite F2MF_dom.
  apply comp_subs_dom; last by rewrite F2MF_dom.
  rewrite lt_n_spec /lt_nK/B2K.
  rewrite <-comp_dom_codom; first by rewrite dom_lt_nk.
  rewrite <- codom_dom_inv.
  case => Hd; [ by exists false | by exists true |].
  by case Hd => [_ [_ H0]].
Qed.

Lemma magnitude_mf_spec : magnitude_mf \tightens magnitude.
Proof.
  move => x.
  rewrite <-magnitude_dom => prp.
  split; first by apply magnitude_mf_dom.
  rewrite /magnitude_mf.
  rewrite !comp_F2MF.
  move => z.
  case => [].
  rewrite !comp_F2MF /uncurry/lt2_check/paib/if_mv/if_X.
  case => [[b x0 [[[H1 H2 H3]]]]].
  simpl in H1,H2,H3.
  rewrite <- H3.
  move : H1 H2.
  case b => [_ H2|H1 _] //.
  case => [[[]]] => p [H4] => // <- H5.
  move => H6.
  case H4 => [[x1 [<- [[n [mag <-]]]]]] _ _.
  have [ms1 _] := (magnitude_split x n).
  apply ms1 => //.
  suff : (not (2 <= x)) by lra.
  move => n2.
  by have := (H2 n2).
  case => [[[]]] => p [H4] => // <- H5.
  move => H6.
  case H4 => [[x1] [[_ ->] [[n [mag <-]]]]] _ _.
  have [_ ms2] := (magnitude_split x n).
  apply ms2 => //.
  suff : (not (x+/(2*1) <= 2)) by lra.
  move => n2.
  by have := (H1 n2).
Qed.
End magnitude.

Section machines.
Check if_X.
Definition if_rlzrf X (phi : B_(cs_bool \*_cs X)) q1q2 :=  match (lprj phi tt) with
                                 | true => (inl (rprj phi q1q2.1))
                                 | false => (inr (rprj phi q1q2.2))
                                 end.

Lemma if_rlzrf_spec (X : cs) : (F2MF (@if_rlzrf X)) \realizes (uncurry (@if_X X)).
Proof.
  rewrite /uncurry/if_rlzrf F2MF_rlzr => phi [b x] /prod_name_spec [/= -> phin2].
  rewrite /slct/lslct/rslct.
  case b => /=.
  by exists (inl (rprj phi)).
  by exists (inr (rprj phi)).
Qed.

Definition if_rlzrf_mu X (phi : B_(cs_bool \*_cs X)) (q1q2 : (Q_(X \+_cs X))) := [:: (inl tt); (inr q1q2.1);(inr q1q2.2)].

Lemma if_rlzrf_mod X : (@if_rlzrf_mu X) \modulus_function_for (@if_rlzrf X).
Proof.
  by rewrite /if_rlzrf/lprj/rprj/= => phi q psi [-> [-> [->]]].
Qed.

Lemma if_rlzrf_modmod X : (@if_rlzrf_mu X) \modulus_function_for (@if_rlzrf_mu X).
Proof.
  by trivial.
Qed.

Arguments monotone_machine {Q} {A} {Q'} {A'}.
Definition RS2CS Rc := (Build_continuity_space (representation Rc)).
Coercion RS2CS : computable_reals >-> continuity_space.
Variable (Rc : computable_reals).
Variable default : A_(Rc).

Lemma lt2_check_machine_exists : {M : monotone_machine | \F_M \solves ((F2MF lt2_check) : (Rc ->> (nat*(Rc*Rc))))}.
Proof.
  case (F2R Rc) => f2r /F2MF_rlzr f2r_spec.
  set rlzr := (fun (phi : B_(Rc)) (q : Q_(cs_nat \*_cs (Rc \*_cs Rc))) => match q with
                                                                     | (inl tt) => (1%nat, (default, default))
                                                                     | (inr (inl q')) => (0%nat, ((phi q'), default))
                                                                     | (inr (inr q')) => (0%nat, (default, (f2r (@pair B_(cs_Z) B_(cs_Z) (Z2csZ 2,Z2csZ 0)) q')))
                                                                     end).
  have rlzr_spec : (F2MF rlzr) \realizes (lt2_check : Rc -> (nat * (Rc *Rc))).
  - rewrite F2MF_rlzr/lt2_check => phi x phin.
    exists ((lprj (rlzr phi)), (rprj (rlzr phi))).
    rewrite /lprj/rprj.
    split => //.
    split => //.
    exists ((lprj (rprj (rlzr phi))), (rprj (rprj (rlzr phi)))).
    rewrite /lprj/rprj.
    split => //.
    split => // /=.
    have -> : (snd \o_f (snd \o_f rlzr phi) \o_f inr) \o_f inr =  (f2r (@pair B_(cs_Z) B_(cs_Z) (Z2csZ 2,Z2csZ 0))).
    - apply functional_extensionality.
      by rewrite /rlzr => q /=.
    have f2' := (f2r_spec (@pair B_(cs_Z) B_(cs_Z) (Z2csZ 2,Z2csZ 0)) (2,0)%Z).
    rewrite /uncurry/= in f2'.
    have ->: (2 = 2*1) by lra.
    apply f2'.
    by exists (Z2csZ 2,Z2csZ 0).
    set mu := (fun (phi : B_(Rc)) (q : Q_(cs_nat \*_cs (Rc \*_cs Rc))) => match q with
                                                                        | (inr (inl q')) => [:: q']
                                                                        | _ => [::]
                                                                        end).
  have mum : mu \modulus_function_for rlzr.
  - rewrite /rlzr => phi q psi.
    case q => q' => //.
    case q' => q'' => //.
    by case => ->.
  have mumm : mu \modulus_function_for mu by trivial.
  exists (F2MM mum mumm).
  by rewrite F2M_spec.
Qed.

Definition andb_rlzrf (phi : B_(cs_bool \*_cs cs_bool)) tt := andb (lprj phi tt) (rprj phi tt).
Lemma andb_rlzrf_spec : (F2MF andb_rlzrf) \realizes (uncurry andb).
Proof.
  by rewrite F2MF_rlzr/andb_rlzrf/uncurry =>  phi [b1 b2] /prod_name_spec [/= -> ->].
Qed.
Definition andb_mu (phi : B_(cs_bool \*_cs cs_bool)) (tt : unit) := [:: (inl tt); (inr tt) ].
Lemma andb_mu_mod : andb_mu \modulus_function_for andb_rlzrf.
Proof.
  by rewrite /andb_mu/andb_rlzrf/lprj/rprj => phi n psi /= [] -> [] -> .
Qed.
Lemma andb_mu_modmod : andb_mu \modulus_function_for andb_mu.
Proof.
  by rewrite /andb_mu//=.
Qed.
Lemma constant_machine_spec (S T : cs) (c: T) phi : phi \is_name_of c -> {M : monotone_machine | \F_M \solves (F2MF (@cnst S T c))}.
Proof.
  set mu := (fun _ _ => [::]): (B_(S) -> Q_(T) -> seq (Q_(S))).
  have mm : mu \modulus_function_for (@cnst B_(S) B_(T) phi) by auto.
  have mmm : mu \modulus_function_for mu by auto.
  exists (F2MM mm mmm). 
  rewrite F2M_spec.
  by apply cnst_rlzr.
Defined.

Lemma Float_constant_machine (m e : Z) : {M : monotone_machine | \F_M \solves (F2MF (@cnst Rc Rc (m * (powerRZ 2 e))))}.
Proof.
  case (F2R Rc) => f2r /F2MF_rlzr f2rprp.
  pose f2r' z1 z2 := (f2r (@pair B_(cs_Z) B_(cs_Z) ((Z2csZ z1), (Z2csZ z2)))).
  have f2r_spec z1 z2 : (f2r' z1 z2) \is_name_of (z1 * (powerRZ 2 z2)).
  - rewrite /f2r'.
    apply (f2rprp (@pair B_(cs_Z) B_(cs_Z) ((Z2csZ z1), (Z2csZ z2))) (z1,z2)). 
    rewrite /Z2csZ. 
    by apply prod_name_spec; split => //.
  case (constant_machine_spec Rc Rc _ _ (f2r_spec m e)) => M Mprp.
  by exists M.
Defined.

Lemma int_constant_machine (z : Z) : {M : monotone_machine | \F_M \solves (F2MF (@cnst Rc Rc z))}.
Proof.
  case (Float_constant_machine z 0) => /= M prp.
  exists M.
  by have -> : ((IZR z) = (IZR z)*1)%R by lra.
Defined.

Lemma magnitude_check_rhs_M n: {M : monotone_machine | \F_M \solves (F2MF (magnitude_check_rhs n) : Rc ->> (nat * (Rc * Rc)))}.
Proof.
  have fp : forall f, (f =~= f) by trivial.
  case (F2R Rc) => f2r /F2MF_rlzr f2rprp.
  pose f2r' z1 z2 := (f2r (@pair B_(cs_Z) B_(cs_Z) ((Z2csZ z1), (Z2csZ z2)))).
  have f2r_spec z1 z2 : (f2r' z1 z2) \is_name_of (z1 * (powerRZ 2 z2)).
  - rewrite /f2r'.
    apply (f2rprp (@pair B_(cs_Z) B_(cs_Z) ((Z2csZ z1), (Z2csZ z2))) (z1,z2)). 
    rewrite /Z2csZ. 
    by apply prod_name_spec; split => //.
  have rhs : (F2MF (magnitude_check_rhs n)) =~= (@mf_cnst Rc nat n.+2) ** (mf_id ** (mf_cnst (13 * (powerRZ 2 (-(Z.of_nat (n.+2))))))) \o (mf_id ** mf_diag ) \o mf_diag.
  - rewrite /mf_cnst/mf_id/mf_diag/mf.diag/cnst.
    rewrite <-!F2MF_fprd.
    rewrite !F2MF_comp_F2MF.
    rewrite <-F2MF_eq.
    rewrite /magnitude_check_rhs/fprd => x.
    rewrite powerRZ2_neg_pos /=.
    f_equal.
    f_equal.
    suff -> : ((/ 2 ^ n) = 4*(/ (2 * ( 2 * 2 ^ n)))) by lra.
    rewrite Rinv_mult_distr; try by lra.
    rewrite Rinv_mult_distr; try by lra.
    apply pow_nonzero;lra.
    suff : (2 ^ n) <> 0 by lra.
    apply pow_nonzero;lra.
  apply /cmp_machine; last first.
  apply rhs.
  apply diag_machine_exists.
  apply /cmp_machine => //;last first.
  apply /prd_machine => //; last first.
  apply diag_machine_exists.
  apply id_machine_exists.
  apply /prd_machine => //; last first.
  apply /prd_machine => //; last first.
  apply /constant_machine_spec.
  apply (f2r_spec 13%Z (- Z.of_nat (n.+2))%Z).
  apply id_machine_exists.
  apply /constant_machine_spec.
  have natn : (nat2csN (n.+2)%nat) \describes (n.+2) \wrt cs_nat by rewrite /nat2csN.
  apply natn.
  apply (default,(default,default)).
  apply (default,default).
Defined.

Lemma magnitude_check_lhs_M n: {M : monotone_machine | \F_M \solves (F2MF (magnitude_check_lhs n) : Rc ->> (nat * (Rc * Rc)))}.
Proof.
  have fp : forall f, (f =~= f) by trivial.
  case (F2R Rc) => f2r /F2MF_rlzr f2rprp.
  pose f2r' z1 z2 := (f2r (@pair B_(cs_Z) B_(cs_Z) ((Z2csZ z1), (Z2csZ z2)))).
  have f2r_spec z1 z2 : (f2r' z1 z2) \is_name_of (z1 * (powerRZ 2 z2)).
  - rewrite /f2r'.
    apply (f2rprp (@pair B_(cs_Z) B_(cs_Z) ((Z2csZ z1), (Z2csZ z2))) (z1,z2)). 
    rewrite /Z2csZ. 
    by apply prod_name_spec; split => //.
  have lhs : (F2MF (magnitude_check_lhs n)) =~= (@mf_cnst Rc nat n.+2) ** ((mf_cnst (1 * (powerRZ 2 (-(Z.of_nat n))))) ** mf_id) \o (mf_id ** mf_diag ) \o mf_diag.
  - rewrite /mf_cnst/mf_id/mf_diag/mf.diag/cnst.
    rewrite <-!F2MF_fprd.
    rewrite !F2MF_comp_F2MF.
    rewrite <-F2MF_eq.
    rewrite /magnitude_check_lhs/fprd => x.
    rewrite powerRZ2_neg_pos /=.
    f_equal.
    f_equal.
    by lra.
  apply /cmp_machine; last first.
  apply lhs.
  apply diag_machine_exists.
  apply /cmp_machine => //;last first.
  apply /prd_machine => //; last first.
  apply diag_machine_exists.
  apply id_machine_exists.
  apply /prd_machine => //; last first.
  apply /prd_machine => //; last first.
  apply id_machine_exists.
  apply /constant_machine_spec.
  apply (f2r_spec 1%Z (- Z.of_nat (n))%Z).
  apply /constant_machine_spec.
  have natn : (nat2csN (n.+2)%nat) \describes (n.+2) \wrt cs_nat by rewrite /nat2csN.
  apply natn.
  apply (default,(default,default)).
  apply (default,default).
Defined.


Lemma magnitude_check_machine_spec n : {M : monotone_machine | \F_M \solves ((magnitude_check n) : Rc ->> _ )}.
Proof.
  rewrite /magnitude_check.
  have fp : forall f, (f =~= f) by trivial.
  apply /cmp_machine => //.
  apply ((false,false) : A_(cs_bool \*_cs cs_bool)).
  exists (F2MM andb_mu_mod andb_mu_modmod).
  rewrite F2M_spec.
  apply andb_rlzrf_spec.
  apply /cmp_machine => //; last first.
  apply diag_machine_exists.
  apply /prd_machine => //; try by apply false.
  apply /cmp_machine => //; last first.
  apply magnitude_check_rhs_M.
  apply ltn_machine.
  apply default.
  apply (0%nat, (default, default)).
  apply /cmp_machine => //; last first.
  apply magnitude_check_lhs_M.
  apply ltn_machine.
  apply default.
  apply (0%nat, (default, default)).
  apply (default, default).
Defined.

Definition magnitude_checkM n := (projT1 (magnitude_check_machine_spec n)).
Definition magnitude_rlzrM phi (mu : nat * unit) := let n := (ord_search (fun n => (magnitude_checkM n phi (mu.1,tt)) == (Some true)) mu.1.+1) in
                                    if n == mu.1.+1
                                    then None
                                    else (Some n).
Lemma magnitude_rlzrM_simpl phi mu n : (magnitude_rlzrM phi mu) = (Some n) -> (magnitude_checkM n phi (mu.1,tt)) = (Some true).
Proof. 
  - rewrite /magnitude_rlzrM.
    set m := mu.1.
    case e: ((ord_search _ _) == m.+1) => //.
    case => H.
    rewrite <- H.
    apply /eqP.
    apply (@search_lt (fun n => (magnitude_checkM n phi (m,tt)) == (Some true)) m.+1).
    apply /leP.
    have /eqP := e.
    have /leP := (@osrch_le (fun n => (magnitude_checkM n phi (m,tt)) == (Some true)) m.+1).
    set p1 :=  ((ord_search (fun n : nat => (magnitude_checkM n) phi [m] == Some true) m.+1)).
    move => H1 /eqP/eqP H2.
    have : (p1 <> m.+1)%coq_nat by trivial.
    by lia.
 Qed.

Lemma magntiude_rlzrM_simpl2 phi m n : (magnitude_checkM n phi (m,tt)) = (Some true) -> exists M, exists m0, (magnitude_rlzrM phi (M,tt)) = (Some m0).
  move => H.
  exists (Nat.max n.+1 m).
  rewrite /magnitude_rlzrM.
  exists (ord_search (fun k => (magnitude_checkM k phi ((Nat.max n.+1 m),tt)) == (Some true)) (Nat.max n.+1 m).+1).
  rewrite ifF => //.
  apply /osrch_eqP.
  have lt : (n < ((Nat.max n.+1 m).+1))%nat by apply /ltP; have := (Nat.le_max_l n.+1 m);lia.
  exists (Ordinal lt).
  have [M1 _] := (mon_spec  (magnitude_checkM n)).
  apply /eqP.
  have mm := (@monotone _ _ _ _ _ (monm_mon (magnitude_checkM n))).
  by apply (M1 mm phi tt true m (Nat.max n.+1 m)); first by apply /leP; have /leP := lt; lia.
Qed.

Lemma magnitude_rlzrM_spec : \F_(magnitude_rlzrM) \solves magnitude1.
Proof.
  apply /slvs_tight/magnitude_check_tight.
  move => phi x phin [n [np1 np2]].
  split; last first.
  - move => Fq Fqprp.
    exists (Fq tt); split => //.
    case (Fqprp tt) => m H.
    have := (magnitude_rlzrM_simpl _ _ _ H).
    rewrite /magnitude_checkM => H2.
    case (projT2 (magnitude_check_machine_spec (Fq tt)) phi x phin) => [| _ B]; first by apply dom_magnitude_check.
    case (get_description true) => tphi tphin.
    case (B tphi); first by case; rewrite tphin;exists m.
    rewrite /magnitude_check_mf.
    by case => [[prp1 prp2] | /= []] => //; last by rewrite tphin.
  case (magnitude_check_is_true _ np1) => n' [n'prp1 n'prp2].
  case (projT2 (magnitude_check_machine_spec n') phi x phin) => [| D B]; first by apply dom_magnitude_check.
  case D => pb pbprp.
  case (B pb pbprp) => b [bprp1 bprp2].
  suff bt : (b = true). 
  move: (pbprp tt).
  case => m.
  rewrite bprp2 bt => P.
  case (magntiude_rlzrM_simpl2 phi _ _ P) => M [m' prp].
  case (get_description m') => m'n m'nn.
  exists m'n.
  exists M.
  case q'.
  by rewrite m'nn.
  move : bprp1.
  by case b => //.
Qed.

Definition mod_magnitude_check_nm phi nm := ((modulus (magnitude_checkM nm.1)) phi (nm.2,tt)).

Definition magnitude_check_nm phi nm := match ((magnitude_checkM nm.1) phi (nm.2,tt)) with
                                          | (Some true) => (Some nm.1)
                                          | _ => None
                                        end.
Lemma magnitude_check_nm_spec phi nm : (isSome (magnitude_check_nm phi nm)) <-> ((magnitude_checkM nm.1) phi (nm.2,tt)) = (Some true).
Proof.
  rewrite /magnitude_check_nm.
  split; by case ((magnitude_checkM _) _ _);case =>//.
Qed.
Lemma mod_magnitude_check_nm_spec : mod_magnitude_check_nm \modulus_function_for magnitude_check_nm.
Proof.
  rewrite /magnitude_check_nm/magnitude_checkM/mod_magnitude_check_nm.
  move => phi [n m] psi coin.
  by rewrite (@modulus_correct _ _ _ _ _ (projT1 (magnitude_check_machine_spec n)) phi (m,tt) psi).
Qed.

Lemma mod_magnitude_check_nm_mod : mod_magnitude_check_nm \modulus_function_for mod_magnitude_check_nm.
Proof.
  rewrite /mod_magnitude_check_nm => phi [n m] psi coin.
  by apply modmod.
Qed.

Definition magnitude_rlzrM' phi (mtt : nat * unit) := ((use_first magnitude_check_nm) phi (mtt.1,mtt.1)).

Lemma magnitude_rlzrM'_spec phi m : (magnitude_rlzrM phi (m,tt)) = (magnitude_rlzrM' phi (m, tt)).
Proof.
  rewrite /magnitude_rlzrM/magnitude_rlzrM'.
  rewrite sfrst_osrch.
  have -> : (fun n : nat => ((magnitude_checkM n) phi (m,tt) == Some true)) = (fun k => (isSome (magnitude_check_nm phi (k,m)))).
  - apply functional_extensionality => n.
    apply /eqP.
    case e : (isSome _).
    by rewrite <- (magnitude_check_nm_spec phi (n,m)).
    move => H.
    have [_ H'] :=  (magnitude_check_nm_spec phi (n,m)).
    have := (H' H).
    by rewrite e.
  rewrite osrchS.
  case e :(isSome (_)).
  rewrite ifF.
Admitted.
Definition magnitude_rlzr_mod phi (mtt : nat * unit):= ((FMop.make_monotone mod_magnitude_check_nm) phi (mtt.1,mtt.1)).
Lemma magnitude_rlzr_mod_spec : magnitude_rlzr_mod \modulus_function_for magnitude_rlzrM.
Proof.
  rewrite /magnitude_rlzr_mod => phi [n tt] psi coin.
  case tt.
  rewrite !magnitude_rlzrM'_spec /magnitude_rlzrM'.
  apply (sfrst_modf mod_magnitude_check_nm_spec coin).
Qed.

Lemma magnitude_rlzr_modmod_spec : magnitude_rlzr_mod \modulus_function_for magnitude_rlzr_mod. 
Proof.
  rewrite /magnitude_rlzr_mod => phi [n tt] psi coin.
  apply mkmm_modmod.
  apply mod_magnitude_check_nm_mod.
  by apply coin.
Qed.
Definition magnitude_rlzrMM := (Build_monotone_machine (mkmn_spec (Build_continuous_machine magnitude_rlzr_mod_spec magnitude_rlzr_modmod_spec))).

Lemma magnitude_rlzrMM_spec : {M : monotone_machine | \F_M \solves (magnitude1 : Rc ->> nat)}.
Proof.
  exists magnitude_rlzrMM => /=.
  apply /tight_slvs.
  apply magnitude_rlzrM_spec.
  apply sfrst_spec.
Defined.

Lemma magnitude_machine_spec : {M : monotone_machine | \F_M \solves (magnitude : Rc ->> Z)}.
Proof.  
  have fp : forall f, (f =~= f) by trivial.
  apply /cmp_machine_tight; last first.
  apply magnitude_mf_spec.
  apply diag_machine_exists.
  apply /cmp_machine => //;last first.
  apply /prd_machine => //; last first. 
  apply id_machine_exists.
  apply /cmp_machine => //;last first.
  apply lt2_check_machine_exists. 
  apply ltn_machine.
  apply default.
  apply (0%nat, (default, default)).
  apply default.
  apply false.
  apply /cmp_machine => //; last first.
  exists (F2MM (@if_rlzrf_mod Rc) (@if_rlzrf_modmod Rc)).
  rewrite F2M_spec.
  apply if_rlzrf_spec.
  apply /cmp_machine => //; last first.
  apply /sum_machine => //; last first.
  rewrite /mag_check_gt.
  apply /cmp_machine => //; last first.
  apply /cmp_machine => //; last first.
  apply Rinv_mf_div.
  have c : (F2MF (fun x => (1,x))) =~= ((mf_cnst 1) ** mf_id) \o mf_diag.
  - move => t x.
    rewrite /mf_cnst/mf_id/mf_diag/mf.diag.
    by rewrite <- F2MF_fprd, F2MF_comp_F2MF.
  apply /cmp_machine => //; last first.
  apply c.
  apply diag_machine_exists.
  apply /prd_machine => //; last first.
  apply id_machine_exists.
  apply /(int_constant_machine 1).
  apply default.
  apply (default, default).
  apply (inv_machine Rc).
  apply (default, default).
  apply /cmp_machine => //;last first.
  apply magnitude_rlzrMM_spec.
  set rlzr := (fun (nn : unit -> nat) (tt : unit) => ((Z.of_nat (nn tt))-2)%Z).
  set mu := (fun (nn : unit -> nat) (tt : unit) => [:: tt]).
  have rlzr_spec : ((F2MF rlzr) \realizes (fun n => (Z.of_nat n-2)%Z)) by rewrite F2MF_rlzr/rlzr => phi n /= ->.
  have mu_mod : mu \modulus_function_for rlzr by rewrite /rlzr => phi n psi [->].
  have mu_modmod : mu \modulus_function_for mu by auto. 
  exists (F2MM mu_mod mu_modmod).
  rewrite F2M_spec.
  apply rlzr_spec.
  apply 0%nat.
  apply default.
  rewrite /mag_check_lt.
  apply /cmp_machine => //; last first.
  admit.
  apply /cmp_machine => //; last first.
  apply magnitude_rlzrMM_spec.
  set rlzr := (fun (nn : unit -> nat) (tt : unit) => ((-Z.of_nat (nn tt))+1)%Z).
  set mu := (fun (nn : unit -> nat) (tt : unit) => [:: tt]).
  have rlzr_spec : ((F2MF rlzr) \realizes (fun n => (-Z.of_nat n+1)%Z)) by rewrite F2MF_rlzr/rlzr => phi n /= ->.
  have mu_mod : mu \modulus_function_for rlzr by rewrite /rlzr => phi n psi [->].
  have mu_modmod : mu \modulus_function_for mu by auto. 
  exists (F2MM mu_mod mu_modmod).
  rewrite F2M_spec.
  apply rlzr_spec.
  apply 0%nat.
  apply default.
  rewrite F2M_spec.
  apply rlzr_spec.
  admit.
  apply (inl 0)%Z.
  apply (inl default).
  apply (false, default).
  apply (default,default).
Lemma magnitude_checkM_spec n : {M : (monotone_machine _ _ _ _ ) | \F_M \solves (magnitude_check n)}.
Proof.
  have fp : forall f, (f =~= f) by trivial.
  apply /compM => //.
  apply ((false,false) : A_(cs_bool \*_cs cs_bool)).
  exists (F2MM andb_mu_mod andb_mu_modmod).
  rewrite F2M_spec.
  apply andb_rlzrf_spec.
  apply /compM => //; last first.
  exists (@diagM IR).
  rewrite F2M_spec.
  apply diag_rlzrf_spec.
  apply /prdM => //; try by apply false.
  apply /compM => //; last first.
  exists (F2MM (@magnitude_check_cmp_mu_modr n) (@magnitude_check_mu_modmod n)).
  rewrite F2M_spec.
  apply magnitude_check_rhs_rlzrf_spec.
  apply lt_n_M_spec.
  apply (0%nat, (Interval_interval_float.Inan, Interval_interval_float.Inan)).
  apply /compM => //; last first.
  exists (F2MM (@magnitude_check_cmp_mu_modl n) (@magnitude_check_mu_modmod n)).
  rewrite F2M_spec.
  apply magnitude_check_lhs_rlzrf_spec.
  apply lt_n_M_spec.
  apply (0%nat, (Interval_interval_float.Inan, Interval_interval_float.Inan)).
  apply ((Interval_interval_float.Inan, Interval_interval_float.Inan)).
  by rewrite /magnitude_check.
Defined.

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


Lemma magnitude_rlzrMM_spec : (\F_magnitude_rlzrMM \solves magnitude1). 
Proof.
Admitted.
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

Definition mag_first_check (x : R) := (2%nat, (x, 1)).
Definition mag_second_check (x : R) := (2%nat, (x,2)).
Definition mag_first_check_rlzr (phi : B_(IR)) := (@pair B_(cs_nat) _ (nat2csN 2, (mp phi (FloattoIR 1%Z 0%Z)))).
Definition mag_second_check_rlzr phi := (@pair B_(cs_nat) _ (nat2csN 2, (mp phi (FloattoIR 2%Z 0%Z)))).
Lemma mag_first_check_rlzr_spec  : (F2MF mag_first_check_rlzr) \realizes mag_first_check.
Proof.
  rewrite F2MF_rlzr => phi x phin.
  apply prod_name_spec.
  split; first by rewrite /lprj /= /nat2csN.
  apply prod_name_spec.
  split; rewrite /lprj/rprj/mag_first_check_rlzr; try by auto.
  apply FloattoIR_correct.
Qed.
Lemma mag_second_check_rlzr_spec  : (F2MF mag_second_check_rlzr) \realizes mag_second_check.
Proof.
  rewrite F2MF_rlzr => phi x phin.
  apply prod_name_spec.
  split; first by rewrite /lprj /= /nat2csN.
  apply prod_name_spec.
  split; rewrite /lprj/rprj/mag_second_check_rlzr; try by auto.
  apply FloattoIR_correct.
Qed.

Definition mag_checks_mu (phi : B_(IR))  (q : Q_(cs_nat \*_cs (IR \*_cs IR))):=
  match q with
  | (inl tt) => [:: 0%nat]
  | (inr (inl n)) => [:: 0%nat;n]
  | (inr (inr n)) => [:: 0%nat;n]
  end.
                                                                                               
Lemma mag_checks_mu_mod1 : mag_checks_mu \modulus_function_for mag_first_check_rlzr.
Proof.
  rewrite /mag_checks_mu/mag_first_check_rlzr => phi m psi.
  case m => q /=.
  by case q => /= [] [] ->.
  case q => q' => /= [].
  by case => [] _ [] ->.
  by case => /= ->.
Qed.
Lemma mag_checks_mu_mod2 : mag_checks_mu \modulus_function_for mag_second_check_rlzr.
Proof.
  rewrite /mag_checks_mu/mag_second_check_rlzr => phi m psi.
  case m => q /=.
  by case q => /= [] [] ->.
  case q => q' => /= [].
  by case => _ [->].
  by case => /= [] [] ->.
Qed.

Lemma mag_checks_mu_modmod : mag_checks_mu \modulus_function_for mag_checks_mu.
Proof.
  by rewrite /mag_checks_mu => phi q psi /=.
Qed.

Definition if_rlzrf (X : cs) (phi : B_(cs_bool \*_cs X \*_cs X))  := if (lprj (lprj phi) tt) then (rprj (lprj phi)) else (rprj phi).
Lemma if_rlzrf_spec (X : cs) : (F2MF (@if_rlzrf X)) \solves (@if_mv X).
Proof.
  rewrite F2MF_rlzr/if_rlzrf/uncurry =>  phi [[b1 x] y] /prod_name_spec []  /prod_name_spec [->] /=.
  by case b1=> /=.
Qed.

Definition if_mu X (phi : B_(cs_bool \*_cs X \*_cs X)) (q : Q_(X)) : (seq Q_(cs_bool \*_cs X \*_cs X)) := [:: (inl (inl tt));(inl (inr q)); (inr q) ].
Lemma if_mu_mod X : (@if_mu X) \modulus_function_for (@if_rlzrf X).
Proof.
  rewrite /if_mu/if_rlzrf/lprj/rprj/= => phi n psi /= [-> []] H1 [] H2 _.
  case (psi (inl (inl tt))).1.1 => /=.
  by rewrite H1.
  by rewrite H2.
Qed.

Lemma if_mu_modmod X : (@if_mu X) \modulus_function_for (@if_mu X).
Proof.
  by trivial.
Qed.

Definition Zopp_rlzrf (phi : B_(cs_Z)) tt := (Zopp (phi tt)).
Definition Zopp_rlzr_mu (phi : B_(cs_Z)) (tt : unit) := [:: tt].
Lemma Zopp_rlzrf_spec : (F2MF Zopp_rlzrf) \realizes Zopp.
Proof.
  by rewrite F2MF_rlzr/Zopp_rlzrf => phi z /= ->.
Qed.
Lemma Zopp_rlzr_mu_spec : Zopp_rlzr_mu \modulus_function_for Zopp_rlzrf.
Proof.
  by rewrite /Zopp_rlzrf => phi q psi /= [] ->.
Qed.
Lemma Zopp_rlzr_mu_mod : Zopp_rlzr_mu \modulus_function_for Zopp_rlzr_mu.
Proof.
  by auto.
Qed.

Definition Zofnat_rlzrf (phi : B_(cs_nat)) tt := (Z.of_nat (phi tt)).
Definition Zofnat_rlzr_mu (phi : B_(cs_nat)) (tt : unit) := [:: tt].
Lemma Zofnat_rlzrf_spec : (F2MF Zofnat_rlzrf) \realizes Z.of_nat.
Proof.
  by rewrite F2MF_rlzr/Zofnat_rlzrf => phi z /= ->.
Qed.
Lemma Zofnat_rlzr_mu_spec : Zofnat_rlzr_mu \modulus_function_for Zofnat_rlzrf.
Proof.
  by rewrite /Zofnat_rlzrf => phi q psi /= [] ->.
Qed.
Lemma Zofnat_rlzr_mu_mod : Zofnat_rlzr_mu \modulus_function_for Zofnat_rlzr_mu.
Proof.
  by auto.
Qed.

Definition Zminus2_rlzrf (phi : B_(cs_Z)) tt := ((phi tt)-2)%Z.
Definition Zminus2_rlzr_mu (phi : B_(cs_Z)) (tt : unit) := [:: tt].
Lemma Zminus2_rlzrf_spec : (F2MF Zminus2_rlzrf) \realizes Zminus2.
Proof.
  by rewrite F2MF_rlzr/Zminus2_rlzrf => phi z /= ->.
Qed.
Lemma Zminus2_rlzr_mu_spec : Zminus2_rlzr_mu \modulus_function_for Zminus2_rlzrf.
Proof.
  by rewrite /Zminus2_rlzrf => phi q psi /= [] ->.
Qed.
Lemma Zminus2_rlzr_mu_mod : Zminus2_rlzr_mu \modulus_function_for Zminus2_rlzr_mu.
Proof.
  by auto.
Qed.

Definition Rinv_rlzrf phi := (FloattoIR 1%Z 0%Z) \: phi. 
Lemma Rinv_rlzrf_spec : (F2MF Rinv_rlzrf) \solves Rinv_mf.
Proof.
  rewrite /Rinv_rlzrf/Rinv_mf F2MF_slvs => phi x phin [t [xp a]].
  exists (/ x).
  split => //.
  have /F2MF_rlzr cln := cleanup_spec.
  have /F2MF_slvs div := Rdiv_rlzr_spec.
  apply cln.
  have -> : (/ x = (1 / x)) by lra.
  case (div (pair ((FloattoIR 1%Z 0%Z),phi)) (1, x)).
   rewrite prod_name_spec lprj_pair rprj_pair; split; by [apply FloattoIR_correct | ].
  by exists (1/x).
  move => xy [[_ /=  xy_prop] P].
  rewrite <- xy_prop.                                                              
  by apply P.                                                    
Qed.

Definition Rinv_rlzrf_mu (phi : B_(IR)) (n : nat) := [:: n].
Lemma Rinv_rlzrf_mu_spec : Rinv_rlzrf_mu \modulus_function_for Rinv_rlzrf.
Proof.
  by rewrite /Rinv_rlzrf/Rdiv_rlzrf/mp/lprj/rprj/cleanup/cleanup_generic => phi n psi [] /= ->.
Qed.
Lemma Rinv_rlzrf_mu_mod : Rinv_rlzrf_mu \modulus_function_for Rinv_rlzrf_mu.
Proof.
  by rewrite /Rinv_rlzrf_mu.
Qed.

Definition cnst_rlzrf (phi : B_(IR)) (tt : unit) := (-1)%Z.  
Lemma cnst_rlzrf_spec : (F2MF cnst_rlzrf) \realizes (@cnst R Z (-1)%Z).
Proof.
  by rewrite F2MF_rlzr => phi x.
Qed.
Lemma cnst_mod : (fun phi tt => [::]) \modulus_function_for (cnst_rlzrf).
Proof.
  by auto.
Qed.
Lemma magnitude_machine_spec : {M : (monotone_machine _ _ _ _) | \F_M \solves magnitude_mf}.
Proof.
  rewrite /magnitude_mf.
  have fp : forall f, (f =~= f) by trivial.
  apply /compM => //; last first.
  exists (@diagM IR).
  rewrite F2M_spec.
  apply diag_rlzrf_spec.
  apply /compM => //; last first.
  apply /prdM => //; last first.
  apply /compM => //; last first.
  exists (@diagM IR).
  rewrite F2M_spec.
  apply diag_rlzrf_spec.
  apply /prdM => //; last first.
  exists (idM IR).
  rewrite F2M_spec.
  apply id_rlzr.
  exists (@diagM IR).
  rewrite F2M_spec.
  apply diag_rlzrf_spec.
  apply (Interval_interval_float.Inan).
  apply (Interval_interval_float.Inan, Interval_interval_float.Inan).
  apply (Interval_interval_float.Inan, Interval_interval_float.Inan).
  exists (@diagM IR).
  rewrite F2M_spec.
  apply diag_rlzrf_spec.
  apply ((Interval_interval_float.Inan, Interval_interval_float.Inan), Interval_interval_float.Inan).
  apply (Interval_interval_float.Inan, Interval_interval_float.Inan).
  apply /compM => //; last first.
  apply /prdM => //; last first.
  apply /compM => //; last first.
  apply /prdM => //; last first.
  apply /compM => //; last first.
  exists (F2MM Rinv_rlzrf_mu_spec Rinv_rlzrf_mu_mod).
  rewrite F2M_spec.
  apply Rinv_rlzrf_spec.
  apply /compM => //; last first.
  exists magnitude_rlzrMM.
  apply magnitude_rlzrMM_spec.
  apply /compM => //; last first.
  exists (F2MM Zofnat_rlzr_mu_spec Zofnat_rlzr_mu_mod).
  rewrite F2M_spec.
  apply Zofnat_rlzrf_spec.
  exists (F2MM Zminus2_rlzr_mu_spec Zminus2_rlzr_mu_mod).
  rewrite F2M_spec.
  apply Zminus2_rlzrf_spec.
  apply 0%Z.
  apply 0%nat.
  apply Interval_interval_float.Inan.
  apply /prdM => //; last first.
  have mm : (fun (phi : (Q_(IR) -> A_(IR))) (tt : unit) => [::] : (seq Q_(IR))) \modulus_function_for  (fun (phi : (Q_(IR) -> A_(IR))) (tt : unit) => [::] : (seq Q_(IR))) by auto.
  exists (F2MM (cnst_mod) mm).
  rewrite F2M_spec.
  apply cnst_rlzrf_spec.
  apply /compM => //; last first.
  exists (F2MM mag_checks_mu_mod2 mag_checks_mu_modmod).
  rewrite F2M_spec.
  apply mag_second_check_rlzr_spec.
  apply lt_n_M_spec.
  apply (0%nat, (Interval_interval_float.Inan, Interval_interval_float.Inan)).
  apply 0%Z.
  apply false.
  apply 0%Z.
  apply (false, 0%Z).
  exists (F2MM (@if_mu_mod cs_Z) (@if_mu_modmod cs_Z)).
  rewrite F2M_spec.
  apply if_rlzrf_spec.
  apply ((false, 0%Z), 0%Z).
  apply /prdM => //; last first.
  apply /compM => //; last first.
  exists magnitude_rlzrMM.
  apply magnitude_rlzrMM_spec.
  apply /compM => //; last first.
  exists (F2MM Zofnat_rlzr_mu_spec Zofnat_rlzr_mu_mod).
  rewrite F2M_spec.
  apply Zofnat_rlzrf_spec.
  exists (F2MM Zopp_rlzr_mu_spec Zopp_rlzr_mu_mod).
  rewrite F2M_spec.
  apply Zopp_rlzrf_spec.
  apply 0%Z.
  apply 0%nat.
  apply /compM => //; last first.
  exists (F2MM mag_checks_mu_mod1 mag_checks_mu_modmod).
  rewrite F2M_spec.
  apply mag_first_check_rlzr_spec.
  apply lt_n_M_spec.
  apply (0%nat, (Interval_interval_float.Inan, Interval_interval_float.Inan)).
  apply 0%Z.
  apply false.
  apply 0%Z.
  apply (false, 0%Z).
  exists (F2MM (@if_mu_mod cs_Z) (@if_mu_modmod cs_Z)).
  rewrite F2M_spec.
  apply if_rlzrf_spec.
  apply ((false, 0%Z), 0%Z).
  apply ((Interval_interval_float.Inan, Interval_interval_float.Inan), ((Interval_interval_float.Inan, Interval_interval_float.Inan), Interval_interval_float.Inan)).
  apply (Interval_interval_float.Inan, Interval_interval_float.Inan).
Defined.

Eval vm_compute in (projT1 magnitude_machine_spec (FloattoIR 1%Z (2)%Z) (6%nat,tt)).
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


Definition lt_nk_rlzrM := projT1 lt_nK_M_spec.

(* We get a realizer as composition of the (partial) mapping from Kleeneans
 to Booleans and the test on the Kleeneans *)
Definition lt_n_rlzr := (\F_K2B_rlzrM : B_(cs_Kleeneans) ->> B_(cs_bool)) \o (F2MF lt_nk_rlzrf).
Lemma lt_n_rlzr_spec : lt_n_rlzr \solves lt_n.
Proof.
  rewrite lt_n_spec /lt_n_rlzr.
  by apply slvs_comp; [apply F_K2B_rlzrM_spec | apply (projT2 lt_nK_rlzr_spec)].
Qed.  

(* The machine for lt_n *)
Definition lt_n_M := fun phi => (K2B_rlzrM (lt_nk_rlzrf phi)).
(* Define the machine for K2B *)
Lemma lt_n_M_spec : {M : (monotone_machine _ _ _ _) | \F_M \solves lt_n}.
Proof.
  apply /compM; last first.
  apply lt_n_spec.
  apply lt_nK_M_spec.
  exists K2BM.
  apply F_K2B_rlzrM_spec.
  apply None.
Defined.


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
