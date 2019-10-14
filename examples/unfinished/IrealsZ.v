From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_rlzrs.
From metric Require Import reals.
Require Import all_cs_base classical_mach.
Require Import Reals Psatz FunctionalExtensionality ClassicalChoice.
Require Import Ibounds.
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

Definition IR_type := nat -> Interval_interval_float.f_interval (s_float Z Z).
Definition IR_pair :=  nat + nat -> Interval_interval_float.f_interval (s_float Z Z) * Interval_interval_float.f_interval (s_float Z Z).

Definition IR2 (phi : IR_type) (psi : IR_type) :  IR_pair :=  fun n => match n with
       | inl x0 => (phi x0, Interval_interval_float.Ibnd Fnan Fnan)
       | inr x0 => (Interval_interval_float.Ibnd Fnan Fnan, psi x0)
       end.
Section representation.
Definition rep_R : (nat -> ID) ->> R:= make_mf (
  fun I x => (forall n,  x \contained_in (I n))
  /\
  forall n, exists N, forall k, (N <= k)%nat -> bounded (I k)
                                                /\
                                                diam (I k) <= /2 ^ n).

Lemma rep_R_sur: rep_R \is_cototal.
Proof.
move => x.
exists (fun n => I.bnd 
	(Float ((Int_part (x * (2 ^ n)))) ((-Z.of_nat n)%Z))
	(Float ((up (x * (2 ^ n)))) ( (-Z.of_nat n)%Z))).
split => n/=.
	have bi:= base_Int_part (x * 2^n); have lt:= pow_lt 2 n; have arc:= archimed (x * 2 ^ n).
	rewrite !D2R_SF2toX;	split; rewrite D2R_Float powerRZ2_neg_pos.
		by apply (Rmult_le_reg_r (2 ^ n)); try lra; rewrite Rmult_assoc Rinv_l; lra.
	by apply (Rmult_le_reg_r (2 ^ n)); try lra; rewrite Rmult_assoc Rinv_l; lra.
exists n.+1 => k ineq; split => //.
have bi:= base_Int_part (x * 2^k); have ltn1:= pow_lt 2 n.+1; have arc:= archimed (x * 2 ^ k).
have ltk:= pow_lt 2 k; have ltn2:= pow_lt 2 n; have eq: 2 ^ k * /2 ^k = 1 by rewrite Rinv_r; lra.
have /=exp: /2 ^ k <= /2 ^ n.+1.
	apply Rinv_le_contravar; try lra.
	by apply Rle_pow; try lra; apply /leP.
rewrite !D2R_Float powerRZ2_neg_pos.
rewrite -Raux.Rmult_minus_distr_r.
rewrite -[/2 ^ n]Rmult_1_l -(Rinv_r 2); try lra.
rewrite Rmult_assoc -Rinv_mult_distr; try lra.
apply Rmult_le_compat; try lra.
by apply /Rlt_le/Rinv_0_lt_compat; lra.
Qed.

Lemma rep_R_sing: rep_R \is_singlevalued.
Proof.
move => In x x' [xeIn convIn] [x'eIn _].
apply cond_eq => e eg0.
have [n [_ ineq]]:= accf_tpmn eg0.
have [N prop]:= convIn n.
have ineq': (N <= N)%nat by trivial.
have [Ibnd dI]:= (prop N ineq').
move: xeIn (xeIn N) => _ xeIn.
move: x'eIn (x'eIn N) => _ x'eIn.
apply/ Rle_lt_trans; last by apply ineq.
case: (In N) Ibnd dI xeIn x'eIn => // l u/=.
case: u; first by case: l.
by case: l => // um ue lm le; rewrite !D2R_SF2toX; split_Rabs; lra.
Qed.

Lemma countable_comp Q Q': Q \is_countable -> (exists cnt : (Q -> Q'), cnt \is_surjective) -> Q' \is_countable .
Proof.
  move => [cnt [H1 H2]].
  case => cnt' p1.
  exists ((F2MF cnt') \o cnt).
  split; first by apply comp_sing; by [apply F2MF_sing | ].
  apply comp_cotot; by [| |].
Qed.

Lemma D_count : D \is_countable.
Proof.
  have [p [p1 p2]]:= ((prod_count (option_count Z_count) Z_count)).
  pose cnt (z : (option Z*Z)) :=  (match z.1 with
             | None => Fnan
             | (Some z') => (Float (z') ((z.2)))
            end) : D.
  exists ((F2MF cnt) \o p).
  - split; first by apply comp_sing; [apply F2MF_sing |].
    apply comp_cotot; try by [].
    rewrite <- F2MF_cotot.
    move => d.
    case d eqn:eq; first by exists (None,0%Z).
    by exists (Some s, e).
Qed.
  
Lemma ID_count: ID \is_countable.
Proof.
  have [p [p1 p2]]:= (option_count (prod_count D_count D_count)).
  
  set cnt := (F2MF (fun (z :(option (D*D))) => match z with
                                            | None => Interval_interval_float.Inan
                                            | (Some z') => (I.bnd z'.1 z'.2)
             end)).
  exists (cnt \o p).
  split; first by apply comp_sing; [apply F2MF_sing |] .
  apply comp_cotot; try by [].
  rewrite /cnt.
  rewrite <- F2MF_cotot.
  case => [| l u]; first by exists None.
  by exists (Some (l,u)).
Qed.

Definition Iall:= @Interval_interval_float.Ibnd D Fnan Fnan. 

Definition IR:= make_cs 0%nat Iall nat_count ID_count rep_R_sur rep_R_sing.
End representation.

Section addition.
Definition Rplus_rlzrf (phi: IR_pair) (n: nat):= I.add (nat2p n) (lprj phi n) (rprj phi n).
Definition Rplus_rlzr: questions (IR \*_cs IR) ->> questions IR := F2MF Rplus_rlzrf.

Lemma Rplus_rlzr_spec : Rplus_rlzr \realizes (F2MF (fun xy => Rplus xy.1 xy.2)).
Proof.
  rewrite F2MF_rlzr_F2MF => phi [x y] [/=[xephin convx] [yephin convy]].
  split => n; first by apply/add_correct_R; [apply xephin | apply yephin].
  case (powerRZ2_bound x y) => K [Kprp1 [Kprp2 Kprp3]].
  have [N Nprp]:= convx n.+2.
  have [M Mprp]:= convy n.+2.
  exists (maxn ((K+n.+1).+3.+2)%nat (maxn M N)) => k ineq.
  have [ | bndl dml]:= Nprp k.
	- apply/leq_trans; first exact: (leq_maxr M N).
  	by apply/leq_trans; first exact: (leq_maxr ((K+n.+1).+3.+2)%nat (maxn M N)).
  have [ | bndr dmr]:= Mprp k.
	- apply/leq_trans; first exact: (leq_maxl M N).
	  by apply/leq_trans; first exact: (leq_maxr ((K+n.+1).+3.+2)%nat (maxn M N)).
  have kgel : ((K+n.+1)%coq_nat.+3.+2 <= k)%coq_nat.
  - by apply (Nat.le_trans ((K+n.+1).+3.+2) (maxn ((K+n.+1).+3.+2) (maxn M N)) k);apply /leP; by [apply (leq_maxl ((K+n.+1).+3.+2) (maxn M N))|].
  have lt: (1 < nat2p k)%Z.
  - suff : (1 < k)%coq_nat.
    rewrite /nat2p/SF2.PtoP //=.   
    rewrite Nat2Z.inj_lt //=.
    by case  k => [|p]; by [lia |rewrite /Z.of_nat Pos.of_nat_succ].
    by lia.
  have lt' : (0 <= Z.of_nat K)%Z by lia. 
  have [bnd err] := (add_error lt lt' bndl dml bndr dmr (xephin k) (yephin k) Kprp2 Kprp3).
  split; first by apply bnd.
  apply /Rle_trans.
  apply err.
  suff H : (powerRZ 2 ((Z.of_nat K)+4 - (nat2p k))) <= (/ 2 ^ n.+1).
  - apply /Rle_trans.
    apply Rplus_le_compat_l.
    apply H.
    by rewrite <- !tpmn_half;lra.
  rewrite <- powerRZ2_neg_pos.
  rewrite !powerRZ_Rpower;try by lra.
  apply Rle_Rpower; try by lra.
  move : lt.
  rewrite /nat2p /SF2.PtoP/StdZRadix2.ZtoE.
  move => lt.
  have zp : (Z.pos (Pos.of_nat k)) = (Z.of_nat k).
  - move :lt.
    case k => [| p H] ; try by simpl; [].
    by rewrite <- Pos.of_nat_succ, Zpos_P_of_succ_nat;lia.
  rewrite zp.
  by apply IZR_le;lia.
Qed.
End addition.

Section multiplication.
Definition Rmult_rlzrf (phi: IR_pair) (n: nat):= I.mul (nat2p n) (lprj phi n) (rprj phi n).

Definition Rmult_rlzr: questions (IR \*_cs IR) ->> questions IR := F2MF Rmult_rlzrf.

Lemma maxN3 x y z B: ((maxn x (maxn  y z)) <= B)%nat -> (x <= B /\ y <= B /\ z <= B)%nat.
Proof.
  split; first by apply (leq_trans (leq_maxl x (maxn y z)) H).
  split.
  - apply /leq_trans.
    apply (leq_maxl y z).
    apply /leq_trans.
    apply (leq_maxr x (maxn y z)).
    by apply H.
  apply /leq_trans.
  apply (leq_maxr y z).
  apply /leq_trans.
  apply (leq_maxr x (maxn y z)).
  by apply H.
Qed.
Lemma Rmult_rlzr_spec : Rmult_rlzr \realizes (F2MF (fun xy => Rmult xy.1 xy.2)).
Proof.
  rewrite F2MF_rlzr_F2MF => phi [x y] [/=[xephin convx] [yephin convy]].
  split => n; first by apply/mul_correct_R; [apply xephin | apply yephin].
  case (powerRZ2_bound x y) => K [Kprp1 [Kprp2 Kprp3]].
  have [N Nprp]:= convx (K+n.+3)%nat.
  have [M Mprp]:= convy (K+n.+3)%nat.
  exists (maxn ((2*K+n.+1).+3.+2)%nat (maxn M N)) => k ineq.
  have [Kp1 [Kp2 Kp3]] := (maxN3 ineq).
  have [ | bndl dml]:= Nprp k; first by [].
  have [ | bndr dmr]:= Mprp k; first by [].
  have lt: (1 < nat2p k)%Z.
  - suff : (1 < k)%coq_nat.
    rewrite /nat2p/SF2.PtoP //=.   
    rewrite Nat2Z.inj_lt //=.
    by case  k => [|p]; by [lia |rewrite /Z.of_nat Pos.of_nat_succ].
    move /ltP : Kp1.
    by lia.
  have lt' : (0 <= Z.of_nat K)%Z by lia. 
  have := (mul_error lt lt' bndl dml bndr dmr (xephin k) (yephin k) Kprp2 Kprp3).
  suff : ((((Z.of_nat K)+1)%Z-(Z.of_nat (K+ (n.+3))%nat)) = -(Z.of_nat (n.+2)))%Z; last by rewrite Nat2Z.inj_add;lia.
  move => -> [bnd err].
  split; first by apply bnd. 
  apply /Rle_trans.
  apply err.
  rewrite powerRZ2_neg_pos.
  suff H : (powerRZ 2 (2*(Z.of_nat K)+4 - (nat2p k))%Z) <= (/ 2 ^ n.+1).
  - apply /Rle_trans.
    apply Rplus_le_compat_l.
    apply H.
    by rewrite <- !tpmn_half;lra.
  rewrite <- powerRZ2_neg_pos.
  rewrite !powerRZ_Rpower;try by lra.
  apply Rle_Rpower; try by lra.
  move : lt.
  rewrite /nat2p /SF2.PtoP/StdZRadix2.ZtoE.
  move => lt.
  have zp : (Z.pos (Pos.of_nat k)) = (Z.of_nat k).
  - move :lt.
    case k => [| p H] ; try by simpl; [].
    by rewrite <- Pos.of_nat_succ, Zpos_P_of_succ_nat;lia.
  rewrite zp.
  apply IZR_le.
  suff : ((((Z.of_nat 2)*Z.of_nat K)+(Z.of_nat n.+1))+(Z.of_nat 4) < (Z.of_nat k))%Z by lia.
  rewrite <- Nat2Z.inj_mul,<- !Nat2Z.inj_add.
  apply inj_lt.
  have p a : (a+4)%coq_nat = (a.+4) by lia.
  rewrite p.
  suff : ((((2*K)+(n.+1)).+4) < k)%nat by apply /ltP.
  by apply Kp1.
Qed.
End multiplication.

Section conversions.
Definition ZtoIR z : (questions IR):= (fun p:nat => (I.fromZ z)).
Definition FloattoIR m e : (questions IR):= (fun p:nat => (I.bnd (Float m e) (Float m e))).
Definition QtoIR p q := match q with 
                        (a#b) => (I.div p  (I.fromZ a) (I.fromZ (Z.pos b)))
                        end.
Require Import Qreals.
Require Import Q_reals.

Lemma QtoIR_correct p q :  (Q2R q) \contained_in (QtoIR p q).
Proof.
  case q => a b.
  suff -> : (Xreal (Q2R (a # b))) = (Xdiv (Xreal (IZR a)) (Xreal (IZR (Z.pos b)))).
  - by apply I.div_correct; apply I.fromZ_correct.
  rewrite /Xdiv' /is_zero//=.
  have -> // : (Raux.Req_bool (IZR (Z.pos b)) 0) = false.
  exact /Raux.Req_bool_false/IZR_nz.
Qed.

Lemma sign_strict_pos b : (I.sign_strict_ (SF2.fromZ (Z.pos b)) (SF2.fromZ (Z.pos b))) = Xgt.
Proof.
  have blt: (0 < IZR (Z.pos b)) by rewrite /IZR;rewrite <- INR_IPR;apply pos_INR_nat_of_P.
 have  := (I.sign_strict_correct_ _ _ _ (I.fromZ_correct (Z.pos b))).
  case e :(I.sign_strict_ (SF2.fromZ (Z.pos b)) (SF2.fromZ (Z.pos b))); try by [];try by lra.
Qed.     

Lemma div_real a b r p : SF2.real (SF2.div r p (SF2.fromZ a) (SF2.fromZ (Z.pos b))).
Proof.
  rewrite SF2.real_correct SF2.div_correct /SF2.toX !SF2.fromZ_correct //= /Xdiv'.
  by have -> : (is_zero (IZR (Z.pos b))) = false by apply Raux.Req_bool_false.
Qed.

Lemma QtoIR_bounded q p : bounded (QtoIR p q).
Proof.
  case q => a b.
  rewrite /QtoIR /SF2.fromZ/I.fromZ /I.div /I.Fdivz/bounded sign_strict_pos.
  by case : (I.sign_strict_ (SF2.fromZ a) (SF2.fromZ a)); try by rewrite !div_real.
Qed.

Notation "'\|' x '|' " := (Rabs x) (format "'\|' x '|' ").

Lemma QtoIR_diam (q:Q) N p: (1 < p)%Z -> \|q| <= powerRZ 2 N ->  diam (QtoIR p q) <= powerRZ 2 (N+2-p)%Z.
Proof. 
  case q => a b pgt qlt.
  suff rnd_error rnd rnd': (SF2.div rnd p (SF2.fromZ a) (SF2.fromZ (Z.pos b))) - (SF2.div rnd' p (SF2.fromZ a) (SF2.fromZ (Z.pos b))) <= powerRZ 2 (N + 2 - p)%Z.
  - rewrite /QtoIR /I.fromZ /I.div /I.Fdivz !sign_strict_pos [SF2.real (SF2.fromZ _)]//=.
    by case:I.sign_strict_; try exact/rnd_error; rewrite /D2R Rminus_0_r;apply powerRZ_le;lra.
  rewrite /D2R !SF2.div_correct.
  rewrite /SF2.toX !SF2.fromZ_correct /Xdiv' //=.
  rewrite /is_zero Raux.Req_bool_false; last exact: IZR_nz.
  apply Rcomplements.Rabs_le_between.
  have -> : forall (u v : R), u - v = (u - (a#b)) +  ((a#b) - v) by intros; lra.
  apply /Rle_trans; first exact/Rabs_triang.
  have -> : forall k, (N+2 - k = (N+1)-k+1)%Z by intros;lia.
  rewrite powerRZ_add ; last by lra.
  rewrite /=Rmult_comm Rmult_1_r double.
  by apply Rplus_le_compat; last rewrite <- Rabs_minus_sym; apply round_error.
Qed.

Definition extend J p := (I.add (nat2p p) J (I.bnd (Float (-1)%Z (-((Z.of_nat p)))%Z) (Float (1)%Z (-((Z.of_nat p)))%Z))).

Lemma extend_diam_lb J p x y: (x \contained_in J) -> (Rabs (y-x)) <= (/ 2 ^ p) -> (y \contained_in (extend J p)). 
Proof.
  move => xc dist.
  set K := (I.bnd (Float (-1)%Z (-((Z.of_nat p)))%Z) (Float (1)%Z (-((Z.of_nat p)))%Z)).
  have -> : y = (x + (y-x)) by lra. 
  suff cnt : ((y-x) \contained_in K) by apply (add_correct_R (nat2p p) xc cnt).
  rewrite //= !Interval_definitions.FtoR_split Float_prop.F2R_Zopp !Float_prop.F2R_bpow.
  rewrite !Raux.bpow_powerRZ/StdZRadix2.EtoZ  //=.
  apply Rcomplements.Rabs_le_between.
  by rewrite powerRZ2_neg_pos.
Qed.

Lemma extend_diam_ub J p n x N: (1 < p)%nat -> (0 <= N)%Z ->
 (bounded J) -> (diam J <= (/ 2 ^ n)) -> (x \contained_in J) -> ((Rabs x) <= (powerRZ 2 N)) -> (diam (extend J p)) <= (/ 2 ^ n)+(/ 2 ^ (p.-1)) + (powerRZ 2 (N + 4 - (nat2p p))%Z).
Proof.
  move => plt Nlt B dJ xc xb.
  set K := (I.bnd (Float (-1)%Z (-((Z.of_nat p)))%Z) (Float (1)%Z (-((Z.of_nat p)))%Z)).
  have plt' : (1 < (nat2p p))%Z.
  - rewrite /nat2p.
    rewrite /SF2.PtoP /StdZRadix2.ZtoE  //=.
    have -> : (p = ((p.-2).+1).+1) by move /leP : plt;lia.
    case (p.-2) => [| m]; rewrite //=;lia.
  have [Bk dK] : (bounded K) /\ ((diam K) <= (/ 2 ^ (p.-1))).
  - split; first by [].
    rewrite !D2R_Float //=.
    ring_simplify.
    rewrite powerRZ2_neg_pos//=.
    have {1}-> : (p = ((p.-1).+1))%nat.
    + rewrite Nat.succ_pred_pos; first by [].
      move /leP : plt.
      by lia.
    rewrite double.
    rewrite <- tpmn_half.
    by lra.
  have c0 : (0 \contained_in K).
  - rewrite //= !Interval_definitions.FtoR_split Float_prop.F2R_Zopp !Float_prop.F2R_bpow.
    rewrite !Raux.bpow_powerRZ/StdZRadix2.EtoZ //=.
    apply Rcomplements.Rabs_le_between.
    rewrite Rabs_R0.
    by apply powerRZ_le; lra.
  apply (add_error plt' Nlt B dJ Bk dK xc c0 xb).
  by rewrite Rabs_R0; apply powerRZ_le;lra.
Qed.

Definition QRtoIR (phi : (Q -> Q)) := (fun p:nat => (extend (QtoIR (nat2p p) (phi (/ (inject_Z (Z.pow 2 (Z.of_nat p))))%Q)) p)).

Lemma eps_simplify p : (Q2R (/ (inject_Z (Z.pow 2 (Z.of_nat p))))%Q) = (/ 2 ^ p).
Proof.
  rewrite Q2R_inv.
  - field_simplify_eq; first by rewrite pow_IZR/inject_Z/Q2R //=;lra. 
    split; first by apply pow_nonzero;lra.
    rewrite /inject_Z/Q2R //=.
    suff: (IZR (2 ^ (Z.of_nat p))) <> (IZR 0) by lra.
    apply IZR_neq.
    by apply Z.pow_nonzero; lia.
  apply Qnot_eq_sym.
  apply Qlt_not_eq.
  rewrite /inject_Z //=.
  apply Rlt_Qlt.
  rewrite /Q2R //=.
  suff : (IZR 0) < (IZR (2 ^ (Z.of_nat p))) by lra.
  apply IZR_lt.
  apply Z.pow_pos_nonneg; by lia.
Qed.

Lemma QRtoIR_contains phi x : (phi \describes x \wrt RQ) -> (forall p, (x \contained_in (QRtoIR phi p))).
  move => //=phin p.
  rewrite /QRtoIR.
  set eps := (/ (inject_Z (Z.pow 2 (Z.of_nat p))))%Q.
  have c := (QtoIR_correct (nat2p p) (phi eps)).
  apply (extend_diam_lb c).
  suff <- : (Q2R eps) = (/ 2 ^ p).
  - apply (phin eps).
    have -> : (0 = Q2R 0) by lra.
    apply Qlt_Rlt.
    apply Qinv_lt_0_compat.
    have -> : (0%Q = (inject_Z 0)) by compute.
    rewrite <- Zlt_Qlt.
    apply Z.pow_pos_nonneg; by lia.
 rewrite /eps.
 apply eps_simplify.
Qed.

Lemma extend_bounded J p : (bounded J) -> (bounded (extend J p)).
Proof.
  rewrite /extend.
  rewrite /I.add //=.
  case J => [| u l]; first by [].
  rewrite /bounded !SF2.real_correct //=.
  case u => [|m e]; case l => [|m' e']; try by [].
  - by rewrite andb_false_r.
 move => _.
  rewrite !SF2.add_correct.
  by rewrite !D2R_SF2toX.
Qed.

Definition RQ_IR_id_rlzr: questions RQ ->> questions IR := F2MF QRtoIR.
Lemma RQ_IR_id_rlzr_cont : RQ_IR_id_rlzr \is_continuous_operator.
Proof.
  rewrite cont_F2MF => phi.
  rewrite /QRtoIR //=.
  by exists (fun n => [:: (/ inject_Z (2 ^ Z.of_nat n))%Q]) => n psi [] ->.
Qed.

Definition RQ_IR_id_rlzr_spec : RQ_IR_id_rlzr \realizes (F2MF (fun x => x)).
Proof.     
  rewrite F2MF_rlzr_F2MF => phi x //= phinx.
  split; first by apply QRtoIR_contains.
  case (powerRZ_bound x) => K [Kprp1 Kprp2].
  move => n.
  exists (((Z.to_nat K)+n).+4.+3)%nat => k kprp.
  rewrite /QRtoIR.
  have klt' : (1 < k)%nat.
    apply /leP.
    move /leP : kprp.
    by lia.
  have klt : (1 < (nat2p k))%Z.
  - suff : (1 < k)%coq_nat; last by apply /leP.
    rewrite /nat2p/SF2.PtoP/BigZ.lt //=.   
    rewrite Nat2Z.inj_lt //=.
    case  k => [|p]; by [lia |rewrite /Z.of_nat Pos.of_nat_succ].
  set eps := (/ inject_Z (2 ^ Z.of_nat k))%Q.
  have epsgt0 : (0 < eps) by rewrite eps_simplify;apply tpmn_lt.
  have lt' : (Rabs (phi eps)) <= (powerRZ 2 (K+1)).
  - rewrite powerRZ_add; last by lra.
    simpl;ring_simplify.
    rewrite double.
    suff : (Rabs (phi eps))  <= (Rabs x)+(powerRZ 2 K) by lra.
    apply Rabs_bnd.
    rewrite Rabs_minus_sym.
    apply /Rle_trans.
    apply (phinx eps); first by [].
    rewrite eps_simplify.
    rewrite Interval_missing.pow_powerRZ.
    rewrite !powerRZ_Rpower; try by lra.
    rewrite <-Rpower_Ropp.
    apply Rle_Rpower; first by lra.
    rewrite <- opp_IZR.
    apply IZR_le.
    by lia.
  have diam1 := (QtoIR_diam klt lt' ).
  have zp : ((Z.pos (Pos.of_nat k)) = (Z.of_nat k)).
  - move : kprp.
    case k => [|k' H]; first by rewrite ltn0.
    rewrite Nat2Pos.inj_succ //=; last by move /leP : H;lia.
    rewrite Pos.succ_of_nat; last by move /leP : H;lia.
    by [].
  have simp_exp : (K+1+2- (nat2p k))%Z = (-Z.of_nat (k - (Z.to_nat K)-3 ))%Z.
  -  
     have -> : (3%nat = (Z.to_nat 3%Z))%nat by auto.
     have -> : (k = (Z.to_nat (Z.of_nat k)))%nat by rewrite Nat2Z.id.
     rewrite <- !Z2Nat.inj_sub; try by lia.
     rewrite Z2Nat.id; last first.
     + suff : ((K+3) < (Z.of_nat k))%Z by lia.
       suff :((Z.to_nat K) + 3 < k)%coq_nat.
       * have -> : (3%Z = (Z.of_nat 3%nat))%nat by auto.
         have {2}-> : (K = (Z.of_nat (Z.to_nat K)))%nat by rewrite Z2Nat.id.
         rewrite <- Nat2Z.inj_add; try by lia.
         by apply inj_lt.
       rewrite /addn/addn_rec.
       move /ltP : kprp.
       rewrite /addn/addn_rec.
       by lia.
       rewrite /nat2p/SF2.PtoP/StdZRadix2.ZtoE.
       rewrite !Nat2Z.id.
       by suff : ((Z.pos (Pos.of_nat k)) = (Z.of_nat k))%nat by lia.
  have Klt : (0 <= K+1)%Z by lia.
  rewrite simp_exp in diam1.
  rewrite powerRZ2_neg_pos in diam1.
  have d := (extend_diam_ub klt' Klt _ diam1 _ lt').
  split; first by apply extend_bounded;apply QtoIR_bounded.
  - apply /Rle_trans.
  apply d; by [apply QtoIR_bounded | apply (QtoIR_correct (nat2p k) (phi eps))].
  rewrite (tpmn_half n).
  rewrite {1}(tpmn_half n.+1).
  apply Rplus_le_compat; [apply Rplus_le_compat;apply /tpmnP;apply /leP | ].
  - move /leP :  kprp.
    by rewrite /addn/addn_rec/subn/subn_rec;lia.
  - move /leP :  kprp.
    by rewrite /addn/addn_rec/subn/subn_rec;lia.
  rewrite <- powerRZ2_neg_pos.
  rewrite !powerRZ_Rpower; try by lra.
  apply Rle_Rpower; first by lra.
  apply IZR_le.
  rewrite /nat2p/SF2.PtoP/StdZRadix2.ZtoE.
  rewrite //=.
  move /leP: kprp.
  rewrite Nat2Z.inj_le.
  rewrite !Nat2Z.inj_succ Nat2Z.inj_add.
  rewrite <- !Z.add_1_r.
  rewrite Z2Nat.id; last by [].
  by lia.
Qed.

Lemma RQ_IR_id_cont : (id : (RQ -> IR)) \is_continuous.
Proof.
  exists RQ_IR_id_rlzr.
  by split; [apply RQ_IR_id_rlzr_spec | apply RQ_IR_id_rlzr_cont].
Qed.
 
Definition Float2Q d := match d with
                        | Fnan => 0%Q
                        | Float m e => ((inject_Z m) * (Qpower (1+1)%Q e))%Q
                        end.
Lemma Qpower_spec r n: ~ r == 0 -> (Q2R r) ^ n = Q2R (r^(Z.of_nat n))%Q.
Proof.
  case: n => [ | n neq]; first by rewrite /Q2R /= Rinv_1; lra.
  rewrite /= /Qpower_positive.
  elim: n => [/= | n ih]; first by rewrite Rmult_1_r; lra.
  have /= /Qeq_eqR ->:= pow_pos_succ Q_Setoid Qmult_comp Qmult_assoc r (Pos.of_succ_nat n).
  by rewrite Q2R_mult ih.
Qed.

Lemma Qpower_minus r z: Qpower r z == Qpower (Qinv r) (Zopp z).
Proof.
  suff eq q p: q^ (Z.pos p) == (/q)^(-Zpos p).
  - case: z => // p.
    by rewrite -Pos2Z.opp_pos Zopp_involutive -{1}(Qinv_involutive r); symmetry; apply/eq.
  rewrite -positive_nat_Z.
  case: (Pos.to_nat p) => //.
  elim => [ | n /=]; first by rewrite /= Qinv_involutive.
  rewrite /Qpower_positive => ih.
  have ->:= pow_pos_succ Q_Setoid Qmult_comp Qmult_assoc q (Pos.of_succ_nat n).
  have ->:= pow_pos_succ Q_Setoid Qmult_comp Qmult_assoc (Qinv q) (Pos.of_succ_nat n).
  by rewrite ih Qinv_mult_distr Qinv_involutive.
Qed.

Lemma Qpower_powerRZ (a:Q) b: (Q2R a <> 0) -> (Q2R (Qpower a b)) = (powerRZ a b).
Proof.
  move => e.
  have e' : (~ a == 0).
    move => e'.
    apply Qeq_eqR in e'.
    by lra.
  case b=>[//=|p|p]; first by lra.
  - rewrite <-positive_nat_Z.
    by rewrite <- Qpower_spec; first by rewrite pow_powerRZ.
  rewrite (Qeq_eqR _ _ (Qpower_minus a (Z.neg p))).
  rewrite [Z.opp _]//=.
  rewrite <- Pos2Z.opp_pos.
  rewrite powerRZ_neg; try by [].
  rewrite <- positive_nat_Z.
  rewrite <- Qpower_spec; last first.
  - move => //= eq.
    apply Qeq_eqR in eq.
    rewrite Q2R_inv in eq; last by [].
    by apply Rinv_neq_0_compat in e;lra.
  rewrite pow_powerRZ //= Q2R_inv; try by [].
Qed.

Lemma Float2Q_spec d : (D2R d) = (Q2R (Float2Q d)).
Proof.
  rewrite /D2R.
  case d => //=[| m e]; first by lra.
  rewrite D2R_SF2toX D2R_Float Q2R_mult Qpower_powerRZ;last by rewrite Q2R_plus RMicromega.IQR_1;lra.
  by rewrite /Q2R Rinv_1 !Rmult_1_r.
Qed.

Definition diamQ I := (Float2Q (upper I)-(Float2Q (lower I)))%Q.
Lemma diamQ_spec I : (Q2R (diamQ I)) = (diam I).
Proof.
   by rewrite  !Float2Q_spec Q2R_minus.
Qed.

Definition IR_RQ_M n (In : (questions IR)) (eps : Q) := 
                              if Qle_bool eps 0%Q then (Some 0%Q) else
                              if (bounded (In n)) && (Qle_bool (diamQ (In n)) eps)
                              then Some (Float2Q (lower (In n)))
                              else None.

Lemma IR_RQ_M_spec In x: (In \describes x \wrt IR) -> (forall (eps : Q), (0 < eps)-> exists n q, (IR_RQ_M n In eps) = (Some q) /\ (\| q - x| <= (Q2R eps))).                                                Proof.
  move => [xcont shrink] eps epsgt.
  case  (dns0_tpmn epsgt) => n nprop.
  apply Rlt_le in nprop.
  case (shrink n) => N Nprop.
  exists N; exists (Float2Q (lower (In N))).
  rewrite /IR_RQ_M //=.
  rewrite ifF; last first.
  -  apply /negP.
     move => /Qle_bool_iff => H'.
     apply Qle_Rle in H'.
     by lra.
  rewrite ifT; last first.
  - apply /andP.
    split; first by apply (Nprop N);apply leqnn.
    apply Qle_bool_iff.
    apply Rle_Qle.
    rewrite diamQ_spec.
    apply /(Rle_trans _ _  _ _ nprop).
    by apply (Nprop);apply /leP;lia.
  split; first by [].
  apply /(Rle_trans _ _  _ _ nprop).
  have t : (N <= N)%nat by apply/leP;lia.
  have [Nprop1 Nprop2] := (Nprop N t).
  apply /(Rle_trans _ _  _ _ Nprop2).
  apply ID_bound_dist; try by [].
  rewrite <- Float2Q_spec.
  apply upper_lower_contained; try by [].
  rewrite /not_empty.
  exists x; by apply xcont.
Qed.

Lemma IR_RQ_M_spec' In x n (eps:Q) q : (0 < eps) -> (In \describes x \wrt IR) -> (IR_RQ_M n In eps) = (Some q) -> (\| q -x | <= (Q2R eps)). 
Proof.
  move => epsgt [N1 N2].
  rewrite /IR_RQ_M.
  rewrite ifF; last first.
  - apply /negP=> H.
    apply Qle_bool_iff in H.
    by apply Qle_Rle in H;lra.
  case B :(bounded (In n));case e : Qle_bool; try by [].
  apply Qle_bool_iff in e.
  case => <-.
  apply Qle_Rle in e.
  apply /(Rle_trans _ _  _ _ e).
  rewrite diamQ_spec.
  rewrite <- Float2Q_spec.
  apply ID_bound_dist; try by [].
  apply upper_lower_contained; try by [].
  exists x; by apply N1.
Qed.

Lemma F_M_realizer_IR_RQ : (\F_IR_RQ_M : ( (name_space IR) ->> (name_space RQ))) \realizes mf_id.
Proof.
  move => phi x phin dom.
  split.
  - apply mach_choice => q'.
    case gt: (Qle_bool q' 0); first by rewrite/IR_RQ_M ;rewrite gt; exists 0%Q; exists 0%nat.
    have qf : (0 < q').
    + move /negP : gt => gt.
      apply Rnot_le_lt.
      move => H.
      apply gt.
      apply Qle_bool_iff.
      by apply Rle_Qle;lra.
    case (IR_RQ_M_spec phin qf) => s.
    case => q [qs_prop1 qs_prop2].
    by exists q; exists s.
  move => psi H.
  exists x.
  split => [eps epsgt | ]; last by [].
  case (H eps) => n np.
  rewrite Rabs_minus_sym.
  apply (IR_RQ_M_spec' epsgt phin np).
Qed.
End conversions.
