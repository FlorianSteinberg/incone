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
Require Import computable_reals_pf.
Require Import Ibounds.
Require Import softcomparison_pf.
(* Some helper functions we need that should be moved to another file later *)
Definition nat2csN (n : nat) := (fun (_ : unit) => n). 
Definition Z2csZ (z : Z) := (fun (_ : unit) => z). 

Definition Rdiv_mf := make_mf (fun xy z => (xy.2 <> 0 /\ z = (xy.1/xy.2))).

Section magnitude.
(* As an application we define a multivalued magnitude function using the soft comparison *)
Definition magnitude := make_mf (fun x z => ((powerRZ 2 z) < x < (powerRZ 2 (z+2)))).

(* We first define tha magnitude function for 0 < x <= 1 *)
Definition magnitude1 := make_mf ((fun x n => (0 < x <= 1) /\  ((/ 2 ^ n) < x < 4*(/2 ^ n)))).

(* We write a check function for magnitude1 *)
Definition magnitude_check_rhs n (x : R) := (n.+2, (x, 3 * (/ 2 ^ n) + (/ 2 ^ (n.+2)))).
Definition magnitude_check_lhs n (x : R) := (n.+2, ((/ 2 ^ n), x)).

Definition magnitude_check n := (F2MF (uncurry andb)) \o ((lt_n \o (F2MF (magnitude_check_rhs n)))  ** (lt_n \o (F2MF (magnitude_check_lhs n))) \o mf_diag).


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

Section rlzrs.
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

Arguments partial_function {S} {T}.
Definition RS2CS Rc := (Build_continuity_space (representation Rc)).
Coercion RS2CS : computable_reals >-> continuity_space.
Variable (Rc : computable_reals).

Lemma lt2_check_pf_exists : {f : partial_function | f \solves ((F2MF lt2_check) : (Rc ->> (nat*(Rc*Rc))))}.
Proof.
  apply cleanup_before_pf.
  case (F2R Rc) => f2r /F2MF_rlzr f2r_spec.
  set rlzr := (fun (phi : B_(Rc)) (q : Q_(cs_nat \*_cs (Rc \*_cs Rc))) => match q with
                                                                     | (inl tt) => (1%nat, ((phi someq), (phi someq)))
                                                                     | (inr (inl q')) => (0%nat, ((phi q'), (phi someq)))
                                                                     | (inr (inr q')) => (0%nat, ((phi someq), (f2r (@pair B_(cs_Z) B_(cs_Z) (Z2csZ 2,Z2csZ 0)) q')))
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
  exists (F2PF rlzr).
  by rewrite F2PF_spec.
Defined.

Definition andb_rlzrf (phi : B_(cs_bool \*_cs cs_bool)) tt := andb (lprj phi tt) (rprj phi tt).
Lemma andb_rlzrf_spec : (F2MF andb_rlzrf) \realizes (uncurry andb).
Proof.
  by rewrite F2MF_rlzr/andb_rlzrf/uncurry =>  phi [b1 b2] /prod_name_spec [/= -> ->].
Qed.
Lemma constant_pf_spec (S T : cs) (c: T) phi : phi \is_name_of c -> {f : partial_function | f \solves (F2MF (@cnst S T c))}.
Proof.
  exists (F2PF (@cnst B_(S) B_(T) phi)). 
  rewrite F2PF_spec.
  by apply cnst_rlzr.
Defined.

Lemma Float_constant_pf (m e : Z) : {f : partial_function | f \solves (F2MF (@cnst Rc Rc (m * (powerRZ 2 e))))}.
Proof.
  apply cleanup_before_pf.
  case (F2R Rc) => f2r /F2MF_rlzr f2rprp.
  pose f2r' z1 z2 := (f2r (@pair B_(cs_Z) B_(cs_Z) ((Z2csZ z1), (Z2csZ z2)))).
  have f2r_spec z1 z2 : (f2r' z1 z2) \is_name_of (z1 * (powerRZ 2 z2)).
  - rewrite /f2r'.
    apply (f2rprp (@pair B_(cs_Z) B_(cs_Z) ((Z2csZ z1), (Z2csZ z2))) (z1,z2)). 
    rewrite /Z2csZ. 
    by apply prod_name_spec; split => //.
  case (constant_pf_spec Rc Rc _ _ (f2r_spec m e)) => M Mprp.
  by exists M.
Defined.

Lemma int_constant_pf (z : Z) : {f : partial_function | f \solves (F2MF (@cnst Rc Rc z))}.
Proof.
  case (Float_constant_pf z 0) => /= M prp.
  exists M.
  by have -> : ((IZR z) = (IZR z)*1)%R by lra.
Defined.

Lemma magnitude_check_rhs_pf n: {f : partial_function | f \solves (F2MF (magnitude_check_rhs n) : Rc ->> (nat * (Rc * Rc)))}.
Proof.
  apply cleanup_before_pf.  
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
  apply /cmp_pf; last first.
  apply rhs.
  apply diag_pf_exists.
  apply /cmp_pf => //;last first.
  apply /prd_pf => //; last first.
  apply diag_pf_exists.
  exists (F2PF (ssrfun.id)).
  rewrite F2PF_spec.
  apply id_rlzr.
  apply /prd_pf => //; last first.
  apply /prd_pf => //; last first.
  apply /constant_pf_spec.
  apply (f2r_spec 13%Z (- Z.of_nat (n.+2))%Z).
  exists (F2PF (ssrfun.id)).
  rewrite F2PF_spec.
  apply id_rlzr.
  apply /constant_pf_spec.
  have natn : (nat2csN (n.+2)%nat) \describes (n.+2) \wrt cs_nat by rewrite /nat2csN.
  apply natn.
Defined.

Lemma magnitude_check_lhs_pf n: {f : partial_function | f \solves (F2MF (magnitude_check_lhs n) : Rc ->> (nat * (Rc * Rc)))}.
Proof.
  apply cleanup_before_pf.  
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
  apply /cmp_pf; last first.
  apply lhs.
  apply diag_pf_exists.
  apply /cmp_pf => //;last first.
  apply /prd_pf => //; last first.
  apply diag_pf_exists.
  exists (F2PF (ssrfun.id)).
  rewrite F2PF_spec.
  apply id_rlzr.
  apply /prd_pf => //; last first.
  apply /prd_pf => //; last first.
  apply cleanup_after_pf.
  exists (F2PF (ssrfun.id)).
  rewrite F2PF_spec.
  apply id_rlzr.
  apply /constant_pf_spec.
  apply (f2r_spec 1%Z (- Z.of_nat (n))%Z).
  apply /constant_pf_spec.
  have natn : (nat2csN (n.+2)%nat) \describes (n.+2) \wrt cs_nat by rewrite /nat2csN.
  apply natn.
Defined.

Lemma magnitude_check_pf_spec n : {f : partial_function | f \solves ((magnitude_check n) : Rc ->> _ )}.
Proof.
  apply cleanup_before_pf.  
  rewrite /magnitude_check.
  have fp : forall f, (f =~= f) by trivial.
  apply /cmp_pf => //.
  exists (F2PF andb_rlzrf).
  rewrite F2PF_spec.
  apply andb_rlzrf_spec.
  apply /cmp_pf => //; last first.
  apply diag_pf_exists.
  apply /prd_pf => //.
  apply /cmp_pf => //; last first.
  apply magnitude_check_rhs_pf.
  apply ltn_rlzr.
  apply /cmp_pf => //; last first.
  apply magnitude_check_lhs_pf.
  apply ltn_rlzr.
Defined.
Definition magnitude_check_seq := (make_mf (fun x bn => forall n, (bn n) \from (magnitude_check n x))).
Lemma magnitude_check_seq_dom : (magnitude_check_seq \is_total).
Proof.
  move => x.
  rewrite /magnitude_check_seq.
  have := (dom_magnitude_check _ x).
  by apply choice.
Qed.

Definition partial_sequence (X Y : cs) (fn : nat -> (@partial_function B_(X) B_(Y))): (@partial_function B_(X) B_(Y\^w)). 
Proof.
  exists (make_subset (fun s  => forall n, ((domain (fn n) s)))).
  case => s sprp.
  move => [n q].
  have p := (sprp n).
  have dom :=(exist (domain (fn n)) s p).
  apply (fn n dom).
  apply q.
Defined.

Lemma partial_sequence_spec X Y (fn : nat -> (@partial_function B_(X) B_(Y))) Fn: (forall n, ((fn n) \solves (Fn n))) ->  ((@partial_sequence X Y fn) \solves (make_mf (fun x yn => forall n, (yn n) \from ((Fn n)) x))).
Proof.
  move => H.
  move => phi x phin [y yprp].
  split.
  - suff d : (phi \from (domain (partial_sequence X Y fn))) by exists (partial_sequence X Y fn (exist (domain (partial_sequence X Y fn)) phi d));exists d.
    move => n.                                                           
    case (H n phi x phin) => [| D _]; first by exists (y n).
    by rewrite PF2MF_dom.
  move => Fq [P <-].
  simpl in Fq.
  simpl in y.
  simpl.
  rewrite /ssr_have/=.
  suff /choice : forall n, exists (y' : Y), y' \from ((Fn n) x) /\ (((fn n) (exist (domain (fn n)) phi (P n))) \is_name_of y'). 
  by case => fa faprp; exists fa; split; by apply faprp.
  move => n.
  case (H n phi x phin) => [| _ B]; first by exists (y n).
  case (B ((fn n) (exist (domain (fn n)) phi (P n)))) => [| y' y'prp]; first by exists (P n).
  by exists y'.                                                                                
Qed.

Lemma seq_pf (X Y : cs) (Fn : nat -> (X ->> Y)) : (forall n, {f : (@partial_function B_(X) B_(Y)) | f \solves (Fn n)}) -> {fn : (@partial_function B_(X) B_(Y\^w)) | fn \solves (make_mf (fun x yn => forall n, (yn n) \from ((Fn n)) x))}. 
Proof.
  move => H.
  set fn := (fun n => (projT1 (H n))).
  exists (partial_sequence X Y fn).
  apply partial_sequence_spec.
  rewrite /fn.
  move => n.
  by apply (projT2 (H n)). 
Defined.

Lemma magnitude_check_seq_pf : {f : partial_function | f \solves (magnitude_check_seq : Rc ->> (cs_bool\^w))}.
  apply /seq_pf.
  move => n.
  by apply (magnitude_check_pf_spec n).
Defined.

Definition search := make_mf (fun (bn : (cs_bool\^w)) n => (bn n) = true).
Lemma search_dom bn n : (bn n) = true -> bn \from (dom search).
Proof.
  move => H.
  by exists n.
Qed.

Definition magnitude1_search := search \o magnitude_check_seq.
Lemma magnitude1_search_spec : magnitude1_search \tightens magnitude_check_mf.
Proof.
  rewrite /magnitude1_search => x [m [prp1 prp2]].
  split.
  - apply comp_subs_dom; last by apply magnitude_check_seq_dom.
    case (magnitude_check_is_true _ prp1) => n [nprp1 nprp2].
    move => bn bnprp.
    have : (bn n) = true.
    + have := (bnprp n).
      by case (bn n) => //.
    by apply search_dom.
  rewrite /magnitude_check_seq/magnitude_check_mf.
  move => n [[bn [p1 p2]] _ ].
  have := (p1 n).
  by rewrite p2.
Qed.
Definition search_rlzrM phi (mq : nat*unit) := if (phi (mq.1,tt)) == true
                                             then (Some mq.1)
                                             else None.
                                                    
Lemma search_rlzrM_spec : \F_(search_rlzrM) \solves search.
Proof.                                              
  rewrite /search_rlzrM => /= phi bn phin [n bp].
  split.
  - exists (fun t => n).
    case; exists n.
    by rewrite (phin n) bp /=.
  move => Fq prp /=.
  case (prp tt) => /= m.
  case e : (phi (m,tt)) => /= //.
  case => H.
  exists m; split => //.
  by have /= <- := (phin m).
Qed.    

Lemma magnitude1_pf : {f : partial_function | f \solves (magnitude1 : Rc ->> nat)}.
Proof.
  apply cleanup_before_pf.
  have t : (search \o magnitude_check_seq) \tightens (magnitude1) by apply /tight_trans/magnitude1_search_spec/magnitude_check_tight.
  apply /cmp_pf_tight/t/magnitude_check_seq_pf.
  exists (get_partial_function search_rlzrM).
  rewrite gtpf_spec.
  by apply /tight_slvs/sfrst_spec/search_rlzrM_spec.
Defined.  

Lemma paib_pf_exists (X : cs) : {f :partial_function | f \realizes (@paib X)}.
Proof.
  set rlzr := (paib (T:=B_(X))) \o_f (@slct B_(X) B_(X)).
  have rlzr_spec : (F2MF rlzr) \realizes (@paib X) by apply paib_rlzr_crct.
  exists (F2PF rlzr).
  rewrite F2PF_spec.
  by apply rlzr_spec.
Defined.


Lemma magnitude_rlzr_spec : {f : partial_function | f \solves (magnitude : Rc ->> Z)}.
Proof.  
  have fp : forall f, (f =~= f) by trivial.
  apply cleanup_before_pf.
  apply /cmp_pf_tight; last first.
  apply magnitude_mf_spec.
  apply diag_pf_exists.
  apply /cmp_pf => //;last first.
  apply /prd_pf => //; last first. 
  apply cleanup_after_pf.
  exists (F2PF (ssrfun.id)).
  rewrite F2PF_spec.
  apply id_rlzr.
  apply cleanup_before_pf.
  apply /cmp_pf => //;last first.
  apply lt2_check_pf_exists. 
  apply ltn_rlzr.
  apply /cmp_pf => //; last first.
  exists (F2PF (@if_rlzrf Rc)).
  rewrite F2PF_spec.
  apply if_rlzrf_spec.
  apply /cmp_pf => //; last first.
  apply /sum_pf => //; last first.
  rewrite /mag_check_gt.
  apply /cmp_pf => //; last first.
  apply /cmp_pf => //; last first.
  apply Rinv_mf_div.
  have c : (F2MF (fun x => (1,x))) =~= ((mf_cnst 1) ** mf_id) \o mf_diag.
  - move => t x.
    rewrite /mf_cnst/mf_id/mf_diag/mf.diag.
    by rewrite <- F2MF_fprd, F2MF_comp_F2MF.
  apply cleanup_before_pf.
  apply /cmp_pf => //; last first.
  apply c.
  apply cleanup_before_pf.
  apply diag_pf_exists.
  apply /prd_pf => //; last first.
  apply cleanup_after_pf.
  exists (F2PF (ssrfun.id)).
  rewrite F2PF_spec.
  apply id_rlzr.
  apply /(int_constant_pf 1).
  apply (division_rlzr Rc).
  apply cleanup_before_pf.
  apply /cmp_pf => //;last first.
  apply magnitude1_pf.
  set rlzr := (fun (nn : unit -> nat) (tt : unit) => ((Z.of_nat (nn tt))-2)%Z).
  have rlzr_spec : ((F2MF rlzr) \realizes (fun n => (Z.of_nat n-2)%Z)) by rewrite F2MF_rlzr/rlzr => phi n /= ->.
  exists (F2PF rlzr).
  rewrite F2PF_spec.
  apply rlzr_spec.
  rewrite /mag_check_lt.
  apply cleanup_before_pf.
  apply /cmp_pf => //; last first.
  have d2 : (F2MF (fun x => Rdiv x 2)) =~= (Rdiv_mf \o (mf_id ** (@mf_cnst Rc Rc 2))) \o mf_diag.
  - rewrite /mf_id/mf_cnst/mf_diag/Rdiv_mf.
    rewrite <- F2MF_fprd.
    rewrite !comp_F2MF.
    rewrite /mf.diag/fprd/cnst/=.
    move => x /=.
    split => // /= [H|].
    split; first by exists (x,2) => /= //.
    move => [x1 x2] /= [prp1 prp2].
    exists (x1/x2); split;  by [lra | ].
    by case => [[[x1 x2 [[<- <- [_ ->]]]]]].
  apply cleanup_before_pf.
  apply /cmp_pf => //; last first.
  apply cleanup_before_pf.
  apply diag_pf_exists.
  apply cleanup_after_pf.
  apply /cmp_pf => //; last first.
  apply fp.
  apply /prd_pf => //; last first.
  apply (int_constant_pf 2%Z).
  apply cleanup_after_pf.
  exists (F2PF (ssrfun.id)).
  rewrite F2PF_spec.
  apply id_rlzr.
  apply (division_rlzr Rc).
  apply cleanup_before_pf.
  apply /cmp_pf => //; last first.
  apply magnitude1_pf.
  set rlzr := (fun (nn : unit -> nat) (tt : unit) => ((-Z.of_nat (nn tt))+1)%Z).
  have rlzr_spec : ((F2MF rlzr) \realizes (fun n => (-Z.of_nat n+1)%Z)) by rewrite F2MF_rlzr/rlzr => phi n /= ->.
  exists (F2PF rlzr).
  rewrite F2PF_spec.
  apply rlzr_spec.
  apply paib_pf_exists.
Defined.

Lemma magnitude_rlzr_dom phi x : (0 < x) -> (phi \is_name_of x) -> (phi \from (dom (projT1 magnitude_rlzr_spec))).
Proof.
  move => xgt phin.
  by case (projT2 magnitude_rlzr_spec phi x phin); first by apply magnitude_dom. 
Qed.
End rlzrs.
