From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_rlzrs.
From metric Require Import reals pointwise.
From metric Require Import all_metric reals standard Qmetric.
Require Import axioms all_cs cs_mtrc metric_names hyper_spaces.
Require Import all_cs_base classical_mach.
Require Import Reals Psatz FunctionalExtensionality ClassicalChoice.
Require Import Ibounds.
Require Import naming_spaces.
Import Qreals.
Require Q_reals.
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
(* types (needed for extraction) *)
Definition IR_type := nat -> Interval_interval_float.f_interval (s_float Z Z).
Definition IR_pair :=  nat + nat -> Interval_interval_float.f_interval (s_float Z Z) * Interval_interval_float.f_interval (s_float Z Z).

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

Section representation.

Definition names_IR := Build_naming_space 0%nat nat_count ID_count.


Definition IR2 (phi : IR_type) (psi : IR_type) :  (names_IR \*_ns names_IR) :=  fun n => match n with
       | inl x0 => (phi x0, Interval_interval_float.Ibnd Fnan Fnan)
       | inr x0 => (Interval_interval_float.Ibnd Fnan Fnan, psi x0)
       end.
Definition rep_R : names_IR ->> R:= make_mf (
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

Definition interval_representation := Build_representation_of (Build_represented_over rep_R_sur rep_R_sing).
Canonical IR := repf2cs interval_representation.

End representation.

Section addition.
Definition Rplus_rlzrf (phi: names_IR \*_ns names_IR) (n: nat):= I.add (nat2p n) (lprj phi n) (rprj phi n).
Definition Rplus_rlzr: B_ (IR \*_cs IR) ->>  B_ IR := F2MF Rplus_rlzrf.

Definition Rplus_rlzr_mu (phi : names_IR \*_ns names_IR) n: seq (nat + nat) := [:: (inl n); (inr n)].

Lemma Rplus_rlzr_mu_mod : Rplus_rlzr_mu \modulus_function_for Rplus_rlzrf.
Proof.
  by rewrite /Rplus_rlzrf/lprj/rprj => phi n psi [] /= -> [] ->.
Qed.

Lemma Rplus_rlzr_mu_modmod : Rplus_rlzr_mu \modulus_function_for Rplus_rlzr_mu.
Proof.
  by rewrite /Rplus_rlzr_mu => phi n psi /=.
Qed.
Lemma Rplus_rlzr_spec : Rplus_rlzr \realizes (uncurry Rplus).
Proof.
  rewrite F2MF_rlzr => phi [x y] /prod_name_spec [/=[xephin convx] [yephin convy]].
  split => n;first by  apply/add_correct_R.
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
Section opp.

Definition Ropp_rlzrf (phi : names_IR)  := (fun n => (I.neg (phi n))): names_IR.

Definition Ropp_rlzr: B_ (IR) ->>  B_ IR := F2MF Ropp_rlzrf.
Lemma Ropp_rlzr_spec : Ropp_rlzr \realizes Ropp.
Proof.
  rewrite F2MF_rlzr => phi x [phin1 phin2].
  rewrite /Ropp_rlzrf.
  split => n; first by apply (I.neg_correct (phi n) (Xreal x) (phin1 n)).
  case (phin2 n) => N Nprp.
  exists N => k kprp.
  have := (Nprp k kprp).
  case (phi k) => [| /= l u ]; first by auto.
  case u => [ | u1 u2];case l => [ | l1 l2]; try by rewrite andb_false_r; move => [H1 _].
  move => [_ H]. 
  rewrite !SF2.real_correct !SF2.neg_correct !D2R_SF2toX.
  split; first by auto.
  have negp a b: (D2R (SF2.neg (Float a b))) = - (D2R (Float a b)).
  - rewrite /SF2.neg.
    have := (StdZRadix2.mantissa_sign_correct a).
    case e : StdZRadix2.mantissa_sign => [| s p] ;rewrite !D2R_Float/StdZRadix2.MtoZ.
    + by move ->;lra.
    move => [-> P].
    case e' : s.
    + rewrite /StdZRadix2.mantissa_pos /StdZRadix2.MtoP.
      rewrite Ropp_mult_distr_l.
      rewrite <-opp_IZR.
      by rewrite Pos2Z.opp_neg;lra.
    rewrite /StdZRadix2.mantissa_neg /StdZRadix2.MtoP.
    rewrite Ropp_mult_distr_l.
    rewrite <-opp_IZR.
    by rewrite Pos2Z.opp_pos;lra.
  by rewrite !negp;lra.
Qed.
End opp.
Section subtraction.
Definition Rminus_rlzrf phi := 
                               (Rplus_rlzrf (pair ((lprj phi),(Ropp_rlzrf (rprj phi))))) : names_IR.
Definition Rminus_rlzr := (F2MF Rminus_rlzrf).
Lemma Rminus_rlzr_spec : Rminus_rlzr \realizes (uncurry Rminus).
Proof.
  have -> : (uncurry Rminus) =  (uncurry Rplus) \o_f (fun x => (x.1, -(x.2))).
  - apply functional_extensionality => x.
    by rewrite /uncurry /=; lra.
    Search _ pair.
  rewrite /Rminus_rlzr.
  have ->: Rminus_rlzrf = Rplus_rlzrf \o_f (@fprd_frlzr IR IR IR IR (fun phi => phi) Ropp_rlzrf).
  - apply functional_extensionality => x;by auto.
  rewrite <- !F2MF_comp_F2MF.
  apply slvs_comp; first by apply Rplus_rlzr_spec.
  rewrite (fprd_frlzr_rlzr (ssrfun.id : (B_(IR) -> B_(IR))) (Ropp_rlzrf : B_(IR) -> B_(IR)) ).
  have -> : (fun (x : R*R) => (x.1, -x.2)) = (id **_f Ropp) by auto.
  rewrite F2MF_fprd.
  apply prod.fprd_rlzr_spec; by [apply id_rlzr | apply Ropp_rlzr_spec].
Qed.
End subtraction.
Section multiplication.
Definition Rmult_rlzrf (phi: names_IR \*_ns names_IR) (n: nat):= I.mul (nat2p n) (lprj phi n) (rprj phi n).

Definition Rmult_rlzr: B_ (IR \*_cs IR) ->> B_ IR := F2MF Rmult_rlzrf.

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
Lemma Rmult_rlzr_spec : Rmult_rlzr \realizes uncurry Rmult.
Proof.
  rewrite F2MF_rlzr => phi [x y] /prod_name_spec [/=[xephin convx] [yephin convy]].
  split => n; first by apply/mul_correct_R.
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
Section division.
Definition Rdiv_rlzrf (phi: names_IR \*_ns names_IR) (n: nat):= I.div (nat2p n) (lprj phi n) (rprj phi n).

Definition Rdiv_rlzr: B_ (IR \*_cs IR) ->> B_ IR := F2MF Rdiv_rlzrf.
Lemma Rdiv_rlzr_spec :  Rdiv_rlzr \solves (make_mf (fun xy z => (xy.2 <> 0 /\ z = (Rdiv xy.1 xy.2)))).
Proof.
   move => phi [x y] /prod_name_spec [/=[xephin convx] [yephin convy]].
  case => t [yneq0 tp].
  split; first by exists (fun n : nat => I.div (nat2p n) (lprj phi n) (rprj phi n)).
  move => Fq Fqprp.                   
  exists t; split; first by auto.
  rewrite <-Fqprp, tp.
  split => n; first by apply /div_correct_R.
  case (powerRZ2_bound x (/ y)) => K [Kprp1 [Kprp2 Kprp3]].
  have [N Nprp]:= convx ((K+1)+n.+3)%nat.
  have [M Mprp]:= convy ((3*K+4)+n.+3)%nat.
  exists (maxn ((2*K+n.+2).+4.+4.+1)%nat (maxn M N)) => k ineq.
  have [Kp1 [Kp2 Kp3]] := (maxN3 ineq).
  have [ | bndl dml]:= Nprp k; first by [].
  have [ | bndr dmr]:= Mprp k; first by [].
  have lt' : (0 <= Z.of_nat K)%Z by lia. 
    have lt: (1 < nat2p k)%Z.
  - suff : (1 < k)%coq_nat.
    rewrite /nat2p/SF2.PtoP //=.   
    rewrite Nat2Z.inj_lt //=.
    by case  k => [|p]; by [lia |rewrite /Z.of_nat Pos.of_nat_succ].
    move /ltP : Kp1.
    by lia.
  move : Kprp3.
  have -> : ((Z.of_nat K) = (- (- Z.of_nat K)))%Z by lia.
  rewrite Rabs_Rinv; last by auto.
  rewrite powerRZ_neg; last by lra.
  rewrite powerRZ_inv; last by lra.
  move => Kprp3.
  apply Rinv_le_contravar in Kprp3; last by apply Rinv_0_lt_compat;apply Rabs_pos_lt.
  rewrite !Rinv_involutive in Kprp3;(try by apply powerRZ_NOR;lra);try by apply Rabs_no_R0.
  have Kineq : (Z.of_nat K + 2 <= Z.of_nat (3 * K + 4 + n.+3))%Z.
  - have -> : (2%Z = (Z.of_nat 2))%Z by lia.
    rewrite <-Nat2Z.inj_add.
    apply Nat2Z.inj_le.
    rewrite /addn/muln/addn_rec/muln_rec.
    by lia.
  have [r1 r2] := (div_error lt lt' Kineq bndl dml bndr dmr (xephin k) (yephin k) Kprp2 Kprp3).
  split; first  by apply r1.
  apply /Rle_trans.
  apply r2.
  rewrite <-powerRZ2_neg_pos.
  have -> : (Z.of_nat K + 1 - (Z.of_nat (K + 1 + n.+3)) = (-Z.of_nat (n.+3)))%Z by rewrite !Nat2Z.inj_add; lia.
  have -> : (3*Z.of_nat K + 4 - (Z.of_nat (3*K + 4 + n.+3)) = (-Z.of_nat (n.+3)))%Z by rewrite !Nat2Z.inj_add ; lia.
  suff pwrrz2_ineq : (powerRZ 2 (2 * Z.of_nat K + 4 - nat2p k) <= (powerRZ 2 (- Z.of_nat n.+2))).
  - apply /Rle_trans.
    apply Rplus_le_compat_l.
    apply pwrrz2_ineq. 
    rewrite !powerRZ2_neg_pos.
    rewrite <- !tpmn_half.
    by apply /tpmnP.
  suff exp_ineq : ((2 * Z.of_nat K + 4 - nat2p k) <= ((- Z.of_nat n.+2)))%Z.
  - rewrite !powerRZ_Rpower;try by lra.
    apply Rle_Rpower; try by lra.
    by apply IZR_le.
 suff : (2 * (Z.of_nat K + 4)+(Z.of_nat n.+2) <= nat2p k)%Z by lia.
 have -> : (2 = (Z.of_nat 2))%Z by lia.
 have -> : (4 = (Z.of_nat 4))%Z by lia.
 rewrite <-!Nat2Z.inj_add.
 rewrite <-!Nat2Z.inj_mul.
 rewrite <-!Nat2Z.inj_add.
 have -> : (nat2p k) = (Z.of_nat k).
 - suff : (1 < k)%coq_nat.
    rewrite /nat2p/SF2.PtoP //=.   
    rewrite Nat2Z.inj_lt //=.
    by case  k => [|p]; by [lia |rewrite /Z.of_nat Pos.of_nat_succ].
    move /ltP : Kp1.
    by lia.
 apply inj_le.
 apply Nat.lt_le_incl.
 have /ltP :=  Kp1.
 rewrite /addn /muln /addn_rec /muln_rec.
 by lia.
Qed.  
End division.
Section extension.
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
End extension.
Section limit.
Definition limit_eff_rlzrM (phin : B_(IR\^w)) (mn : nat * nat) :=
  let (m,n) := mn in
  match (phin (n.+1,m)) with
  | (Interval_interval_float.Ibnd l u) =>
      if  (I.F'.le (SF2.sub_exact u l) (Float 1%Z (- (Z.of_nat n.+1))%Z))
      then (Some (extend (Interval_interval_float.Ibnd l u) n.+1))
      else None
    | _ => None
  end.
Notation lim_eff:= (efficient_limit: (IR\^w) ->> IR).
Lemma diam_approx_correct u l n:  (u <> Fnan) -> (l <> Fnan) -> (diam (Interval_interval_float.Ibnd l u)) <= (/ 2 ^ (n.+1)) <-> (I.F'.le (SF2.sub_exact u l) (Float 1%Z (-Z.of_nat n.+1)%Z)).
Proof.
  move => up lp.
  rewrite /I.F'.le SF2.cmp_correct.
  rewrite SF2.sub_exact_correct.
  rewrite /Xsub.
  rewrite /Xcmp.
  case e:  u; case e':l; try by auto.
  rewrite !D2R_SF2toX;rewrite <-e, <-e'.
  rewrite D2R_Float.
  rewrite powerRZ2_neg_pos Rmult_1_l.
  split.
  - move => /= H.
    case H => H'; first by rewrite Raux.Rcompare_Lt.
    by rewrite Raux.Rcompare_Eq.
  case cmp : (Raux.Rcompare (D2R u-D2R l) (/2 ^ (n.+1))) ; last by auto.
  - apply Raux.Rcompare_Eq_inv in cmp.
    rewrite cmp //=; lra.
  apply Raux.Rcompare_Lt_inv in cmp; simpl in cmp.
  by rewrite //=;lra.
Qed.

Lemma F_lim_eff_rlzrM_dom phin xn: (phin \describes xn \wrt delta_(IR\^w)) -> (forall n, exists M, forall m, (M <= m)%nat -> exists I, (limit_eff_rlzrM phin (m,n)) = (Some I) /\ (bounded I) /\ ((xn n.+1) \contained_in I)). 
Proof.
  move => phinn n.
  have [phi_prp1 phi_prp2] := (phinn n.+1).
  case (phi_prp2 (n.+1)) => M Mprp.
  exists M => m mprp.
  have [bnd ineq] := (Mprp _ mprp).
  have := bnd.
  move : ineq.
  case e: (phin (n.+1,m)) => [| d1 d2]; first by auto.
  move => ineq p.
  have [d1prp d2prp] : (d1 <> Fnan) /\ (d2 <> Fnan) by split; move : p;case d1prp' : d1 => [| mant1 exp1]; case d2prp : d2 => [| mant2 exp2].
  exists (extend (Interval_interval_float.Ibnd d1 d2) n.+1).
  split; first by rewrite /= e ifT; last apply diam_approx_correct.
  split; first by apply extend_bounded.
  rewrite <-e.
  apply (extend_diam_lb (phi_prp1 m)).
  rewrite Rcomplements.Rminus_eq_0 Rabs_R0.
  by apply tpmn_pos.
Qed.

Lemma F_lim_eff_rlzrM_contains_lim phin xn x m n I: (phin \describes xn \wrt delta_(IR\^w)) -> (lim_eff xn x) ->(limit_eff_rlzrM phin (m, n)) = (Some I) ->  x \contained_in I.
Proof.
  move => phinn xlim.
  rewrite /limit_eff_rlzrM.
  case e : (phin (n.+1,m)) => [| d1 d2] ; first by auto.
  case (I.F'.le (SF2.sub_exact d2 d1) (Float 1%Z (- Z.of_nat n.+1)%Z)); try by auto.
  move => /Some_inj <-.
  have [phi_prp1 phi_prp2] := (phinn n.+1).
  rewrite <- e.
  apply (extend_diam_lb (phi_prp1 m)).
  by apply xlim.
Qed.

Lemma F_lim_eff_rlzrM_choice_correct phin xn m n I : (phin \describes xn \wrt delta_(IR\^w)) -> (limit_eff_rlzrM phin (m, n)) = (Some I) -> (I = (extend (phin (n.+1,m)) (n.+1))) /\ (bounded (phin (n.+1,m))) /\ (diam (phin (n.+1,m))) <= (/2 ^ (n.+1)).
Proof.
  move => phinn.
  rewrite /limit_eff_rlzrM.
  case e : (phin (n.+1,m)) => [| d1 d2] ; first by auto.
  move => p.
  have [d1prp d2prp] : (d1 <> Fnan) /\ (d2 <> Fnan) by split; move : p;case d1prp' : d1 => [| mant1 exp1]; case d2prp : d2 => [| mant2 exp2].
  move : p.
  case e': (I.F'.le (SF2.sub_exact d2 d1) (Float 1%Z (- Z.of_nat n.+1)%Z)); try by auto.
  move => /Some_inj H.
  split; first by auto.
  split.
  simpl.
  rewrite !SF2.real_correct.
  case d1prp' : d1 => [| mant1 exp1]; case d2prp' : d2 => [| mant2 exp2]; try rewrite !D2R_SF2toX;try by auto.
  by apply diam_approx_correct.
Qed.  

Lemma F_lim_eff_rlzrM_diam phin xn m n I M :  (0 <= M)%Z -> (1 < n.+1)%nat -> (phin \describes xn \wrt delta_(IR\^w)) -> (Rabs (xn (n.+1))) <= (powerRZ 2 M) -> (limit_eff_rlzrM phin (m, n)) = (Some I) -> (bounded I) /\ (diam I) <= (powerRZ 2 (M + 4 - nat2p n)).
Proof.
  move => Mbnd nbnd phinn bnd P.
  have [-> [B diam]] := (F_lim_eff_rlzrM_choice_correct phinn P).
  have [phi_prp1 phi_prp2] := (phinn n.+1).
  split; first by apply extend_bounded.
  apply /Rle_trans.
  apply (extend_diam_ub nbnd Mbnd B diam (phi_prp1 m) bnd).
  have ineq : (/2 ^ n.+1) <= (/2 ^ n.+1.-1) by apply /tpmnP;apply /leP;lia.
  apply /Rle_trans.
  apply Rplus_le_compat_r.
  apply Rplus_le_compat_r.
  apply ineq.
  have /leP := nbnd => nbnd'.
  have -> : (n.+1.-1 = (n.-1.+1))%coq_nat by lia.
  rewrite <- tpmn_half.
  rewrite <- powerRZ2_neg_pos.
  have -> : (M + 4 - (nat2p n.+1) = (M+3-(nat2p n)))%Z.
  - rewrite /nat2p /SF2.PtoP/StdZRadix2.ZtoE.
    rewrite Nat2Pos.inj_succ; by lia.
  have ineq' : (-Z.of_nat n.-1 <= (M + 3 - (nat2p n)))%Z.
  - rewrite Nat2Z.inj_pred; last by lia.
    rewrite /nat2p /SF2.PtoP/StdZRadix2.ZtoE.
    case n => [| n' ]; first by simpl;lia.
    elim n' => [| n'' IH]; first by simpl; lia.
    rewrite Nat2Z.inj_succ.
    rewrite Z.pred_succ.
    rewrite Nat2Pos.inj_succ; by lia.
  have rpwlt : (powerRZ 2 (- Z.of_nat n.-1)%Z) <= (powerRZ 2 (M + 3 - nat2p n)%Z).
  - rewrite !powerRZ_Rpower; try by lra.
    apply Rle_Rpower; try by lra.
    by apply IZR_le.
  apply /Rle_trans.
  apply Rplus_le_compat_r.
  apply rpwlt.
  ring_simplify.
  have {1}-> : (2 = (powerRZ 2 1)) by simpl;lra.
 rewrite <- powerRZ_add; last by lra.
 have ->: (1 + (M+3- nat2p n) = (M+4 - nat2p n))%Z by lia.
 by lra.
Qed.


Lemma F_lim_eff_rlzrM_spec : \F_limit_eff_rlzrM  \solves lim_eff.
Proof.
  move => phin xn phinn [x lim].
  split.
  - apply FM_dom => q.
    case (F_lim_eff_rlzrM_dom phinn q) => s P.
    case (P _ (leqnn s)) => I [Ip1 [Ip2 Ip3]].
    by exists I; exists s.
  move => In Inprp.
  exists x.
  split; first by apply lim.
  split => n.
  - case (Inprp n) => m mprp.
    by apply (F_lim_eff_rlzrM_contains_lim phinn lim mprp ).
 case (powerRZ_bound x) => M [Mprp1 Mprp2].
 exists ((Z.to_nat M)+5+n)%nat => k kprp.
 case (Inprp k) => m mprp.
 have klt :  (1 < k.+1)%nat by apply /leP; have /leP := kprp; rewrite /addn/addn_rec; lia.
 have xnlt : (Rabs (xn k.+1)) <= (powerRZ 2 (M+1)).
  - have l' := (lim k.+1).
    rewrite /= Rabs_minus_sym in l'.
    apply /Rle_trans.
    apply (Rabs_bnd l').
    rewrite powerRZ_add /=; last by lra.
    ring_simplify.
    rewrite [2*(powerRZ _ _)]double.
    apply Rplus_le_compat; try by auto.
    apply /Rle_trans.
    rewrite tech_pow_Rmult.
    apply tpmn_bound.
    have -> : (1 = (powerRZ 2 0)) by auto.
    rewrite !powerRZ_Rpower; try by lra.
    apply Rle_Rpower; try by lra.
    by apply IZR_le.
  have C := (F_lim_eff_rlzrM_diam _ klt phinn xnlt mprp).
  split; first by apply C;lia.
  apply /Rle_trans. 
  apply C; first by lia.
  rewrite <-powerRZ2_neg_pos.
  rewrite !powerRZ_Rpower; try by lra.
  apply Rle_Rpower; try by lra.
  apply IZR_le.
  have /leP := kprp => kprp'.
  suff : (M + 5 + (Z.of_nat n) <= (nat2p k))%Z by lia.
  have -> : (M = (Z.of_nat (Z.to_nat M))) by rewrite Z2Nat.id.
  rewrite /nat2p /SF2.PtoP/StdZRadix2.ZtoE.
  have -> : (5 = (Z.of_nat 5))%Z by lia.
  Search _ ((Z.of_nat _) + (Z.of_nat _))%Z.
  rewrite <-!Nat2Z.inj_add.
  have -> : (Z.pos (Pos.of_nat k)) = (Z.of_nat k).
  - move : klt.
    case k => [|k' klt']; first by auto.
    rewrite Nat2Z.inj_succ.
    elim k' => [|k'' IH]; first by auto.
    rewrite Nat2Pos.inj_succ; last by lia.
    rewrite Pos2Z.inj_succ.
    by lia.
 apply inj_le.
 rewrite /addn/addn_rec in kprp'.
 by lia.
Qed.
Definition lim_eff_rlzr_mu (phin : B_(IR\^w))  (nm : nat * nat) := [:: (nm.2.+1,nm.1)].
Lemma lim_eff_rlzr_mu_spec : lim_eff_rlzr_mu \modulus_function_for limit_eff_rlzrM.
Proof.
  by rewrite /limit_eff_rlzrM /= => phi [n m] psi /= [] ->.
Qed.  
End limit.

Section conversions.
Definition ZtoIR z : B_(IR):= (fun p:nat => (I.fromZ z)).
Definition FloattoIR m e :  B_(IR):= (fun p:nat => (I.bnd (Float m e) (Float m e))).
Lemma FloattoIR_correct m e : (FloattoIR m e) \is_name_of (D2R (Float m e)).
Proof.
  split => n; first by rewrite //= D2R_SF2toX;lra.
  exists 0%nat => k kgt.
  split; first by [].
  simpl; ring_simplify.
  by apply tpmn_pos.
Qed.
Definition QtoIR p q := match q with 
                        (a#b) => (I.div p  (I.fromZ a) (I.fromZ (Z.pos b)))
                        end.

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


Notation "'\|' x '|'" := (Rabs x) (at level 30).
Coercion Q2R: Q >-> R.
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
Lemma QRtoIR_contains phi x : (phi \describes x \wrt delta_(Q_reals.RQ)) -> (forall p, (x \contained_in (QRtoIR phi p))).
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


Definition RQ_IR_id_rlzr: B_(Q_reals.RQ) ->> B_(IR) := F2MF QRtoIR.
Lemma RQ_IR_id_rlzr_cont : RQ_IR_id_rlzr \is_continuous_operator.
Proof.
  rewrite cont_F2MF => phi.
  rewrite /QRtoIR //=.
  by exists (fun n => [:: (/ inject_Z (2 ^ Z.of_nat n))%Q]) => n psi [] ->.
Qed.

Definition RQ_IR_id_rlzr_spec : RQ_IR_id_rlzr \realizes (id:Q_reals.RQ -> IR).
Proof.     
  rewrite F2MF_rlzr => phi x //= phinx.
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

Lemma RQ_IR_id_cont : (id : Q_reals.RQ -> IR) \is_continuous.
Proof.
  exists RQ_IR_id_rlzr.
  by split; try exact /RQ_IR_id_rlzr_spec ;apply RQ_IR_id_rlzr_cont.
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

Definition IR_RQ_rlzrM n (In : names_IR) (eps : Q) := 
                              if Qle_bool eps 0%Q then (Some 0%Q) else
                              if (bounded (In n)) && (Qle_bool (diamQ (In n)) eps)
                              then Some (Float2Q (lower (In n)))
                              else None.

Lemma IR_RQ_rlzrM_dom In x: (In \describes x \wrt delta_(IR)) -> (forall (eps : Q), (0 < eps)-> exists N, forall n, (N <= n)%nat -> exists q, (IR_RQ_rlzrM n In eps) = (Some q) /\ (\| q - x| <= (Q2R eps))).
Proof.
  move => [xcont shrink] eps epsgt.
  case  (dns0_tpmn epsgt) => n nprop.
  apply Rlt_le in nprop.
  case (shrink n) => N Nprop.
  exists N => k kprop.
  exists (Float2Q (lower (In k))).
  rewrite /IR_RQ_rlzrM //=.
  rewrite ifF; last first.
  -  apply /negP.
     move => /Qle_bool_iff => H'.
     apply Qle_Rle in H'.
     by lra.
  rewrite ifT; last first.
  - apply /andP.
    split; first by apply (Nprop _ kprop);apply leqnn.
    apply Qle_bool_iff.
    apply Rle_Qle.
    rewrite diamQ_spec.
    apply /(Rle_trans _ _  _ _ nprop).
    by apply (Nprop _ kprop);apply /leP;lia.
  split; first by [].
  apply /(Rle_trans _ _  _ _ nprop).
  have [Nprop1 Nprop2] := (Nprop k kprop).
  apply /(Rle_trans _ _  _ _ Nprop2).
  apply ID_bound_dist; try by [].
  rewrite <- Float2Q_spec.
  apply upper_lower_contained; try by [].
  rewrite /not_empty.
  exists x; by apply xcont.
Qed.

Lemma IR_RQ_rlzrM_val In x n (eps:Q) q : (0 < eps) -> (In \describes x \wrt delta_(IR)) -> (IR_RQ_rlzrM n In eps) = (Some q) -> (\| q -x | <= (Q2R eps)). 
Proof.
  move => epsgt [N1 N2].
  rewrite /IR_RQ_rlzrM.
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

Lemma F_M_realizer_IR_RQ : forall f, (forall n, (n <= (f n))%nat) -> \F_(fun phi neps => IR_RQ_rlzrM (f neps.1) phi neps.2)  \realizes (id:IR -> Q_reals.RQ).
Proof.
  move => f fprop phi x phin xfd.
  split.
  - apply FM_dom => q'.
    case gt: (Qle_bool q' 0); first by rewrite/IR_RQ_rlzrM /= gt; exists 0%Q; exists 0%nat.
    have qf : (0 < q').
    + move /negP : gt => gt.
      apply Rnot_le_lt.
      move => H.
      apply gt.
      apply Qle_bool_iff.
      by apply Rle_Qle;lra.
    case (IR_RQ_rlzrM_dom phin qf) => s P.
    have := (P _ (fprop s)).
    case => q [qs_prop1 qs_prop2].
    by exists q; exists s.
  move => psi H.
  exists x.
  split  => // eps epsgt.
  case (H eps) => n np.
  rewrite Rabs_minus_sym.
  apply (IR_RQ_rlzrM_val epsgt phin np).
Qed.
Definition IR_RQ_mu (f : nat -> nat) (phin : names_IR) (neps : (nat * Q)) := [:: (f neps.1)].
Lemma IR_RQ_mu_spec f : (IR_RQ_mu f) \modulus_function_for (fun phi neps => (IR_RQ_rlzrM (f neps.1) phi neps.2)).
Proof.
  by rewrite /IR_RQ_rlzrM => phi [n eps] psi /= [] ->.
Qed.  
End conversions.

Section comparison.
Definition lt0_rlzr (phi : names_IR) := (fun n =>
  match (I.sign_strict (phi n)) with
  | Xlt => (Some true)
  | Xgt => (Some false)
  | _ => None
  end) : B_(cs_Kleeneans).
Lemma sign_strict_und I : (0 \contained_in I) -> (I.sign_strict I) = Xeq \/ (I.sign_strict I) = Xund.
Proof.
  move => H.
  have  := (I.sign_strict_correct I ).
  case e : (I.sign_strict I) => P ; try by auto.
  have := (P _ H); by simpl; lra.
  have := (P _ H); by simpl; lra.
Qed.

Lemma lt0_dec1 x phi : (x < 0) -> (phi \is_name_of x) -> exists N, forall n, (N <= n)%nat -> (I.sign_strict (phi n)) = Xlt.
Proof.
  move => xlt [phin1 phin2].
  have xlt' : (0 < -x) by lra.
  case (dns0_tpmn xlt') => n nprp.
  have nprp' : (x < - (/2 ^ n)) by lra.
  case (phin2 n) => N Nprp.
  exists N => k kprp.
  have [Nprp1' Nprp2'] := (Nprp _ kprp).
  rewrite /I.sign_strict.
  case e :(phi k) => [| l u]; first by rewrite e /= in Nprp1'.
  case e' : l => [| lm le]; first by rewrite e e' /= in Nprp1'.
  case e'' : u => [| um ue]; first by rewrite e e'' /= andb_false_r  in Nprp1'.
  rewrite /I.sign_strict_ !SF2.cmp_correct /Xcmp !D2R_SF2toX.
  rewrite <- e', <- e''.
  rewrite e /upper/lower in Nprp2'.
  have := (upper_lower_contained Nprp1' ).
  case => [| uc lc]; first by exists x; apply (phin1 k).
  rewrite !Raux.Rcompare_Lt; try rewrite D2R_Float /= /StdZRadix2.mantissa_zero Rmult_0_l; try by auto.
  - have := (ID_bound_dist Nprp1' uc (phin1 k)).
    rewrite e /= => H.
    have H' : ((Rabs  (u - x))   <= (/ 2 ^ n)) by lra.
    apply Rcomplements.Rabs_le_between' in H'.
    apply /Rle_lt_trans.
    apply H'.
    by lra.
  have := (ID_bound_dist Nprp1' lc (phin1 k)).
  rewrite e /= => H.
  have H' : ((Rabs (l - x))  <= (/ 2 ^ n)) by lra.
  apply Rcomplements.Rabs_le_between' in H'.
  apply /Rle_lt_trans.
  apply H'.
  by lra.
Qed.

Lemma lt0_dec2 x phi : (0 < x) -> (phi \is_name_of x) -> exists N, forall n, (N <= n)%nat -> (I.sign_strict (phi n)) = Xgt.
Proof.
  move => xlt [phin1 phin2].
  case (dns0_tpmn xlt) => n nprp.
  case (phin2 n) => N Nprp.
  exists N => k kprp.
  have [Nprp1' Nprp2'] := (Nprp _ kprp).
  rewrite /I.sign_strict.
  case e :(phi k) => [| l u]; first by rewrite e /= in Nprp1'.
  case e' : l => [| lm le]; first by rewrite e e' /= in Nprp1'.
  case e'' : u => [| um ue]; first by rewrite e e'' /= andb_false_r  in Nprp1'.
  rewrite /I.sign_strict_ !SF2.cmp_correct /Xcmp !D2R_SF2toX.
  rewrite <- e', <- e''.
  rewrite e /upper/lower in Nprp2'.
  have := (upper_lower_contained Nprp1' ).
  case => [| uc lc]; first by exists x; apply (phin1 k).
  rewrite !Raux.Rcompare_Gt; try rewrite D2R_Float /= /StdZRadix2.mantissa_zero Rmult_0_l; try by auto.
  - have := (ID_bound_dist Nprp1' uc (phin1 k)).
    rewrite e /= => H.
    have H' : (Rabs( u - x)  <= (/ 2 ^ n)) by lra.
    apply Rcomplements.Rabs_le_between' in H'.
    by suff : (0 < x - (/ 2 ^ n)); lra.
  have := (ID_bound_dist Nprp1' lc (phin1 k)).
  rewrite e /= => H.
  have H' : (Rabs (l - x)   <= (/ 2 ^ n)) by lra.
  apply Rcomplements.Rabs_le_between' in H'.
  by suff : (0 < x - (/ 2 ^ n)); lra.
Qed.

Lemma lt0_prop1 x (phi : B_(IR)) n : (phi \is_name_of x) -> (I.sign_strict (phi n)) = Xgt -> (0 < x). 
Proof.
  move => [phin1 phin2] H.
  have := (I.sign_strict_correct (phi n)).
  rewrite H => H'.
  by apply (H' _ (phin1 n)).
Qed.
Lemma lt0_prop2 x (phi : B_(IR)) n : (phi \is_name_of x) -> (I.sign_strict (phi n)) = Xlt -> (x < 0). 
Proof.
  move => [phin1 phin2] H.
  have := (I.sign_strict_correct (phi n)).
  rewrite H => H'.
  by apply (H' _ (phin1 n)).
Qed.

Definition ltK (xy : R*R) := let (x,y) := xy in
                     match (total_order_T x y) with
                     | (inleft (left _)) => true_K
                     | (inright _) => false_K
                     | _ => bot_K
                     end.

Lemma ltK_spec x y: ((ltK (x,y)) = true_K <-> (x < y)) /\ ((ltK (x,y)) = false_K <-> (y < x)) /\ ((ltK (x,y)) = bot_K <-> (x = y)). 
Proof.
  rewrite /ltK.
  case: (total_order_T x y) => [[xlty | <-] | xgty].
  split; split;[| | split | split]; try lra;try by auto.
  split; split;[| | split | split]; try lra;try by auto.
  split; split;[| | split | split]; try lra;try by auto.
Qed.

Lemma lt0_rlzr_spec : (F2MF lt0_rlzr) \realizes (fun x => (ltK (x,0))).
Proof.
   rewrite F2MF_rlzr => phi x phin.
   rewrite /ltK /lt0_rlzr.
   have [phin1 phin2] := phin.
   case: (total_order_T x 0) => [[xlt0 | xeq0 ] | xgt0].
   - have P : exists N, (I.sign_strict (phi N) = Xlt).
     + case (lt0_dec1 xlt0 phin) => n nprp.
       by exists n;first by apply (nprp n);apply /leP;lia.
     case (classical_count.well_order_nat P) => N [Nprp1 Nprp2].
     exists N; split=>[| m mprp]; first by rewrite Nprp1.
     case e :(I.sign_strict (phi m)); try by auto.
     have := (Nprp2 _ e).
     move /leP => mprp'.
     move /leP : mprp.
     by lia.
     have := (lt0_prop1 phin e).
     by lra.
   - rewrite xeq0 in phin1.
     move => n.
     by case (sign_strict_und (phin1 n)) => ->.
   have P : exists N, (I.sign_strict (phi N) = Xgt).
    - case (lt0_dec2 xgt0 phin) => n nprp.
      by exists n;first by apply (nprp n);apply /leP;lia.
   case (classical_count.well_order_nat P) => N [Nprp1 Nprp2].
   exists N; split=>[| m mprp]; first by rewrite Nprp1.
   case e :(I.sign_strict (phi m)); try by auto.
   have := (lt0_prop2 phin e).
   by lra.
   have := (Nprp2 _ e).
   move /leP => mprp'.
   move /leP : mprp.
   by lia.
Qed.

Definition ltK_rlzr := lt0_rlzr \o_f Rminus_rlzrf.

Lemma ltK_rlzr_spec : (F2MF ltK_rlzr) \realizes ltK.
Proof.
  rewrite /ltK_rlzr.
  suff -> : ltK = (fun x => (ltK (x, 0))) \o_f (uncurry Rminus).
  - 
    rewrite <- (F2MF_comp_F2MF lt0_rlzr Rminus_rlzrf).
    apply rlzr_comp;[apply lt0_rlzr_spec | apply Rminus_rlzr_spec].
  apply functional_extensionality => [[x y]].
  rewrite /uncurry /=.
  case: (total_order_T x y) => [[xlty | xeqy] | xgty]; case: (total_order_T (x-y) 0) => [[xlty' | ] | xgty']; try by auto; try by lra.
Qed.
Definition ltK_mu (phi : (names_IR \*_ns names_IR)) (n : nat) : seq (nat + nat) := [:: (inr n); (inl n)].
Lemma ltK_mu_mod : ltK_mu \modulus_function_for ltK_rlzr.
Proof.
  by rewrite /ltK_rlzr/lt0_rlzr/Rminus_rlzrf/Rplus_rlzrf/Ropp_rlzrf/rprj/lprj => phi n psi /= [-> [-> _]].
Qed.

Lemma ltK_mu_modmod : ltK_mu \modulus_function_for ltK_mu.
Proof.
  by rewrite /ltK_mu => phi n psi.
Qed.
End comparison.

Section cleanup.

(* The clean up function on the interval reals replaces intervals larger than a given bound by the NAN interval *)
Definition cleanup_generic m phi  := (fun n => match (phi n) with
               | (Interval_interval_float.Ibnd l u) =>
                   if  (I.F'.le (SF2.sub_exact u l) (Float 1%Z (- (Z.of_nat m))%Z))
                   then ((Interval_interval_float.Ibnd l u))
                   else Interval_interval_float.Inan
                | _ => Interval_interval_float.Inan
               end) : names_IR.

Lemma bounded_non_nan I : (bounded I) -> exists u l, (u <> Fnan) /\ (l <> Fnan) /\ I = (Interval_interval_float.Ibnd u l).
  rewrite /bounded.
  move => bnd.
  case e: I => [| l u]; first by rewrite e in bnd. 
  exists l; exists u.
  case uprp: u => [| mnt exp]; first by rewrite e uprp andb_false_r in bnd.
  case lprp: l => [| mnt' exp']; first by rewrite e lprp andb_false_l in bnd.
  split; [| split]; by auto.
Qed.

Lemma cleanup_generic_spec m: (F2MF (cleanup_generic m)) \realizes (id : IR -> IR).  
Proof.
  rewrite F2MF_rlzr /cleanup_generic => phi x [phin1 phin2].
  split => n.
  - case R: (phi n) => [| l u];first by auto.
    case (I.F'.le (SF2.sub_exact u l) (Float 1%Z (- (Z.of_nat m))%Z)); last by auto.
    by rewrite <-R; apply phin1.
  case (phin2 (max n m)) => N Nprp.
  exists N => k kprp.
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

(* We choose size 1/2 as the maximal size of intervals *)
Definition cleanup :=  (cleanup_generic 1%nat).

Lemma cleanup_spec : (F2MF cleanup) \realizes (id : IR -> IR).
Proof.
  by apply cleanup_generic_spec.
Qed.
End cleanup.

Section speedup.
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

Definition IR_RQ_rlzrM' := (fun phi neps => IR_RQ_rlzrM (speedup neps.1 5) phi neps.2).
Canonical eqQ : eqType.
  apply (@Equality.Pack Q).
  apply eqdec_eqClass => q q'.
  case q => m n; case q' => m' n'.
  case (Z.eq_dec m m') => e1; case (Pos.eq_dec n n') => e2; try by right;case.
  by rewrite e1 e2;auto.
Defined.

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

Definition IR2Qmf := \F_(IR_RQ_rlzrM').
End speedup.

(* notations *)

Definition mp (phi psi : names_IR) := (pair (phi,psi)).
Notation "phi '\*' psi" := ((cleanup \o_f Rmult_rlzrf) (mp phi psi)) (at level 3).
Notation "phi '\+' psi" := ((cleanup \o_f Rplus_rlzrf) (mp phi psi)) (at level 4).
Notation "phi '\:' psi" := ((cleanup \o_f Rdiv_rlzrf) (mp phi psi)) (at level 3).
Notation "phi '\-' psi" := ((cleanup \o_f Rminus_rlzrf) (mp phi psi)) (at level 4).



