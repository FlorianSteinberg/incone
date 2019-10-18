(* This file defines two representations of the unit interval: The first one is the signed digit
   representation, where a name of a real number x is a function sds: nat -> {-1,0,1} =: SD such
   that x = sum_i (sds i)/ 2^i.+i. The use of functions is somewhat akward here, a better approach
   would be to use streams. However, I have not gotten around to implement stream representations.
   As a consequence of this, for the proof that the representation is surjective uses an auxiliary
   representation that is closer to the stream representation: in rep_UI_inc a name of a real
   number x is a function that takes a list of signed digits and returns a single digit such that
   if one starts from the empty list and  iterates this proceedure indefinitely to produce a
   stream of signed digits, one obtains a signed digit name of x. An alternative description that
   avoids mentioning the signed digit representation is that a name is a function phi: seq SD -> SD
   such that whenever the input list K sums up to an /2^(size K) approximation, then adding the
   value (phi K)/2^(size K).+1 improves this to a /2^(size K).+1 approximation.
*)
From mathcomp Require Import all_ssreflect all_algebra.
From rlzrs Require Import all_rlzrs.
From metric Require Import all_metric reals standard.
Require Import axioms all_cs classical_func.
Require Import Rstruct under Reals Qreals Psatz ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope R_scope.

Section signed_digits.
  Inductive SD := minusone | zero | one.
  
  Definition SD2OB sd :=
    match sd with
    | minusone => some false
    | zero => None
    | one => some true
    end.

  Lemma SD_eqClass: Equality.class_of SD.
  Proof.
    exists (fun sd sd' => (SD2OB sd == SD2OB sd')%bool).
      by case; case; try exact: ReflectT; try exact: ReflectF.
  Qed.

  Canonical SD_eqType := Equality.Pack SD_eqClass.

  Lemma SD_count: SD \is_countable.
  Proof.
    apply/enum_count.
    exists (fun n => match n with
	     | 0%nat => Some minusone
	     | S 0 => Some zero
	     | S (S n) => Some one
             end).
    by case; [exists 0%nat | exists 1%nat | exists 2%nat].
  Qed.
  
  Coercion SD2Z sd: Z :=
    match sd with
    | one => 1%Z
    | zero => 0%Z
    | minusone => -1%Z
    end.
End signed_digits.

Section SDs_as_functions.
  Implicit Types (sds: nat -> SD).
  Fixpoint SDs2Zn (sds: nat -> SD) n :=
    match n with
    | 0%nat => 0%Z
    | m.+1 => (2 * SDs2Zn sds m + SD2Z (sds m))%Z
    end.

  Lemma SDs2ZnS sds n :
    SDs2Zn sds n.+1 = (2 * SDs2Zn sds n + sds n)%Z.
  Proof. by trivial. Qed.

  Definition SD2R sd :=
    match sd with
    | one => 1
    | zero => 0
    | minusone => -1
    end.

  Coercion IZR: Z >-> R.
  
  Lemma SD2Z_SD2R sd: SD2R sd = SD2Z sd.
  Proof. by case: sd. Qed.
  
  Lemma SDs2Zn_spec sds n:
    SDs2Zn sds n / 2^n = \sum_(i < n) SD2R (sds i) * /2 ^ i.+1.
  Proof.
    symmetry.
    elim: n => [ | n ih]; first by rewrite big_ord0 /GRing.zero /=; try lra.
    rewrite SDs2ZnS plus_IZR mult_IZR Rdiv_plus_distr Rmult_comm /Rdiv.
    rewrite big_ord_recr /= ih SD2Z_SD2R Rmult_assoc.
    have ->: 2 * / (2 * 2 ^ n) = / 2 ^ n by have lt:= pow_lt 2 n; rewrite Rinv_mult_distr; try lra.
    by rewrite /GRing.mul/GRing.add/=; try lra.
  Qed.

  Lemma SDs2Zn_SDs2Rn sds n: IZR (SDs2Zn sds n) = 2 ^ n * \sum_(i < n) SD2R (sds i) * /2 ^ i.+1.
  Proof. by rewrite -SDs2Zn_spec; field; have lt:= pow_lt 2 n; lra. Qed.

  Lemma Rabs_SDs2Rn (sds: nat -> SD) n: Rabs (\sum_(i < n) SD2R (sds i) * /2 ^ i.+1) <= 1 - /2^n.
  Proof.
    case: n => [ | n]; first by rewrite big_ord0/= /GRing.zero /=; split_Rabs; lra.
    elim: n => [ | n ih].
    - rewrite big_ord1/= /GRing.mul /=.
      by case: (sds 0%nat) => /=; split_Rabs; try lra.
    rewrite big_ord_recr/=; apply/Rle_trans; first exact/Rabs_triang.
    have ->: 1 - / (2 * (2 * 2 ^ n)) = 1 - /2^n.+1 + (/2^n.+1 -  / (2 * (2 * 2 ^ n))) by lra.
    have ? := tpmn_lt n; have ?: 0 < 2^n by apply /pow_lt; lra.
    apply Rplus_le_compat; first exact ih; rewrite !Rinv_mult_distr; try lra.
    by case: (sds n.+1); rewrite /GRing.mul /= ?Rmult_0_l; split_Rabs; try lra.
  Qed.

  Lemma SDs2RSn (sds: nat -> SD) n:
    \sum_(i < n.+1) SD2R (sds i) * /2 ^ i.+1
    =
    /2 * (\sum_(i < n) SD2R (sds i.+1) * /2 ^ i.+1) + /2 * SD2R (sds 0%nat).
  Proof.
    rewrite big_ord_recl /= addrC.
    congr (_ + _); last rewrite Rmult_1_r /GRing.mul /=; try lra.
    elim: n => [ | n ih]; first by rewrite !big_ord0 /GRing.zero /=; lra.
    rewrite big_ord_recr /= ih [\sum_(i < n.+1) _] big_ord_recr /=.
    have ->: bump 0%nat n = n.+1 by rewrite /bump.
    rewrite Rmult_plus_distr_l.
    congr (_ + _).
    have plt:= pow_lt 2 n.
    by rewrite !Rinv_mult_distr /GRing.mul /=; try lra.
  Qed.

  Lemma Rabs_SDs2Rnm (sds: nat -> SD) n m:
    let SDs2Rn n := \sum_(i < n) SD2R (sds i) * /2 ^ i.+1 in
    (n <= m)%nat -> Rabs (SDs2Rn m - SDs2Rn n) <= /2^n  - /2^m.
  Proof.
    move => /= ineq.
    elim: n m ineq sds => [m ineq sds| n ih m ineq].
    - by rewrite big_ord0 Rminus_0_r Rinv_1; apply/Rabs_SDs2Rn.
    move => sds; case: m ih ineq => // m ih ineq.
    rewrite !SDs2RSn; specialize (ih m ineq (fun i => sds i.+1)).
    have lt1:= pow_lt 2n; have lt2:= pow_lt 2 m; rewrite /= !Rinv_mult_distr; split_Rabs; try lra.
  Qed.

  Lemma SDs2Rn_fchy (sds: nat -> SD):
    (fun n => \sum_(i < n) SD2R (sds i) * /2 ^ i.+1) \is_fast_Cauchy_sequence.
  Proof.
    move => n m; have ?:= tpmn_lt n; have ?:= tpmn_lt m.
    by case/orP: (leq_total n m) => ?; first rewrite dst_sym;
                                     apply/Rle_trans; try exact/Rabs_SDs2Rnm; lra.
  Qed.

  Lemma cchy_SDs2Rn sds:
    (fun n => \sum_(i < n) SD2R (sds i) * /2 ^ i.+1) \is_Cauchy.
  Proof. exact/fchy_cchy/SDs2Rn_fchy. Qed.

  Local Notation metric_limit:= (pseudo_metric_spaces.limit).

  Definition SDs2R :=
    metric_limit \o (F2MF (fun sds n => \sum_(i < n) SD2R (sds i) * /2 ^ i.+1)).
  
  Lemma SDs2R_tot: SDs2R \is_total.
  Proof.
    rewrite /SDs2R comp_F2MF => sds.
    have [x xprp]:= R_cmplt (cchy_SDs2Rn sds).
    by exists x.
  Qed.

  Lemma SDs2R_sing: SDs2R \is_singlevalued.
  Proof. by apply /comp_sing; [exact /metrics.lim_sing | exact /F2MF_sing]. Qed.

  Notation lim_eff:= efficient_limit.

  Lemma SDs2R_lim_eff:
    SDs2R =~= lim_eff \o (F2MF (fun sds n => \sum_(i < n) SD2R (sds i) * /2 ^ i.+1)).
  Proof.
    rewrite /SDs2R lim_eff_spec !comp_F2MF => sds x.
    split => [limx | [cchy limx]]//.
    by split; first by have := SDs2Rn_fchy sds.
  Qed.

  Lemma SDs2R_eff sds x: x \from SDs2R sds
                         <->
                         x \from lim_eff (fun n => \sum_(i < n) SD2R (sds i) * /2 ^ i.+1).
  Proof. by have:= SDs2R_lim_eff; rewrite comp_F2MF => prp; apply prp. Qed.

  Notation SDs2R_spec:= SDs2R_lim_eff.
  
  Lemma SDs2R_UI u x: SDs2R u x -> -1 <= x <= 1.
  Proof.
    move => /SDs2R_eff val; move: (val 0%nat) => /=.
    by rewrite big_ord0 /distance/= Rminus_0_r; split_Rabs; lra.
  Qed.
End SDs_as_functions.

Section Lists.
  Fixpoint SDL2R L:=
    match L with
    | [::] => 0
    | sd :: K => SDL2R K + SD2R sd * /2 ^ (size L)
    end.

  Lemma SDL2RS sd L: SDL2R (sd :: L) = SDL2R L + SD2R sd * /2 ^ (size L).+1.
  Proof. done. Qed.

  Fixpoint SDL2Z L :=
    match L with
    | [::] => 0%Z
    | sd :: K => (2 * SDL2Z K + SD2Z sd)%Z
    end.

  Lemma SDL2ZS a L: SDL2Z (a :: L) = (2 * SDL2Z L + SD2Z a)%Z.
  Proof. done. Qed.

  Lemma SDL2Z_SDL2R L: IZR (SDL2Z L) = SDL2R L * 2^(size L).
  Proof.
    elim: L => [ | a L]; first by rewrite /=; lra.
    rewrite SDL2ZS [RHS]/= plus_IZR mult_IZR => -> /=; have lt:= pow_lt 2 (size L).
    by rewrite Rmult_plus_distr_r Rmult_assoc Rinv_l ?IZR_SD2Z_SD2R; case: a => /=; lra.
  Qed.

  Lemma SDs2Zn_SDL2Z sds n: SDs2Zn sds n = SDL2Z (iseg sds n).
  Proof. by elim: n => // n ih; rewrite SDs2ZnS ih. Qed.

  Lemma SDL2R_spec sds n: SDL2R (iseg sds n) = \sum_(i < n) SD2R (sds i) * /2 ^ i.+1.
  Proof.
    symmetry.
    elim: n => [ | n ih]; first by rewrite big_ord0.
    by rewrite big_ord_recr /= size_iseg ih.
  Qed.
End Lists.

Notation "'\|' x '|'" := (Rabs x).
Section signed_digit_representations.
  Definition UI := { x | -1 <= x <= 1}.

  Definition sd_names := Build_naming_space 0%nat nat_count SD_count.

  Definition rep_sd := make_mf (fun (sds: sd_names) (x: UI) => SDs2R sds (sval x)).

  Definition sd_inc_names:= Build_naming_space [::] (list_count SD_count) SD_count.

  Definition rep_sd_inc := make_mf (fun (phi: sd_inc_names) (x: UI) =>
	                              forall L, \|sval x - SDL2R L| <= /2^(size L)
	                                   ->
	                                   \|sval x - SDL2R (phi L :: L)| <= /2^(size L).+1).

  (* The non-increasing representation is total and easily shown to be singlevalued.*)
  Lemma rep_sd_tot: rep_sd \is_total.
  Proof. by move => sds; have [x val]:= SDs2R_tot sds; exists (exist _ x (SDs2R_UI val)). Qed.

  Lemma rep_sd_sing: rep_sd \is_singlevalued.
  Proof.
    by move => sds x y sdsnx sdsny; apply /eq_sub /SDs2R_sing; [apply sdsnx | apply sdsny].
  Qed.

  (* The surjectivity for the non-increasing representation is a tricky, however, for the
     increasing one it is not too much work: *)
  Lemma rep_sd_inc_nc (x: UI): 
	(forall q, exists a, Rabs (projT1 x - SDL2R q) <= /2^(size q)
		-> Rabs (projT1 x - SDL2R (a :: q)) <= /2^(size q).+1)
	-> x \from codom rep_sd_inc.
  Proof. by move => /countable_choice P; apply/P; countability; apply/SD_count. Qed.

  Lemma rep_sdi_sur: rep_sd_inc \is_cototal.
  Proof.
    case; intros; apply rep_sd_inc_nc => sdL.
    case: (classic (x <= SDL2R sdL)) => leq; [exists minusone | exists one] => /= ineq';
      rewrite Rinv_mult_distr; have:= pow_lt 2 (size sdL); try lra;
      have:= tpmn_lt (size sdL); split_Rabs; lra.
  Qed.

  (*
    To prove both of these representations from the above lemmas it is sufficient to translate
    from the increasing representation to the other one, so let's do that.
   *)

  Fixpoint sdi2sd_rec (phi: seq SD -> SD) m :=
    match m with
    | 0%nat => [::]
    | S k => (phi (sdi2sd_rec phi k) :: sdi2sd_rec phi k)
    end.

  Lemma sdi2sd_rec_size phi n: size (sdi2sd_rec phi n) = n.
  Proof. by elim: n => // n /= ->. Qed.

  Definition sdi2sd (phi: seq SD -> SD) n := phi (sdi2sd_rec phi n).

  Lemma sdi2sd_iseg phi: iseg (sdi2sd phi) = sdi2sd_rec phi.
  Proof. by apply/fun_ext; elim => // n /= ->. Qed.
  
  Lemma sdi2sd_spec phi x: rep_sd_inc phi x -> rep_sd (sdi2sd phi) x.
  Proof.
    move => phinx.
    apply/SDs2R_lim_eff.
    rewrite comp_F2MF /sdi2sd => n.
    elim: n => [ | n ih].
    - by rewrite big_ord0 /= Rinv_1; case: x phinx => x; rewrite/GRing.zero/=; split_Rabs; try lra.
    have := phinx (iseg (sdi2sd phi) n); rewrite size_iseg => ineq.
    apply/Rle_trans/ineq; last by rewrite SDL2R_spec.
    rewrite big_ord_recr /= size_iseg -sdi2sd_iseg SDL2R_spec /=.
    apply/Req_le; rewrite /GRing.add /=; do 4 f_equal; apply/fun_ext => i; do 3 f_equal.
    by case: i => [[]] // i /= _; rewrite {3}/sdi2sd /= sdi2sd_iseg.
  Qed.
  
  Lemma rep_sdi_rep: rep_sd_inc \is_representation.
  Proof.
    split; try exact/rep_sdi_sur; move => ? ? ? phinx ?.
    by apply/rep_sd_sing; apply/sdi2sd_spec; first exact/phinx.
  Qed.
  
  Definition increasing_sd_representation:= Build_representation_of rep_sdi_rep.
  
  Lemma rep_sd_rep: rep_sd \is_representation.
  Proof.
    split; try exact/rep_sd_sing; move => x.
    by have [phi /sdi2sd_spec]:= rep_sdi_sur x; exists (sdi2sd phi).
  Qed.

  Definition sd_representation:= Build_representation_of rep_sd_rep.
End signed_digit_representations.
Require Import ZArith.
Section equivalence_of_sdi_and_sd_representations.
  Lemma sdi2sd_cont: increasing_sd_representation \translatable_to sd_representation.
  Proof.
    apply/F2MF_cont; exists sdi2sd; split; try exact/F2MF_rlzr/sdi2sd_spec.
    move => phi.
    Print sdi2sd.
    
  Definition sd2sdi sds L :=
    if is_left (Z_lt_dec (SDs2Zn sds (size L).+1) (2 * SDL2Z L))
    then minusone
    else if is_left (Z_lt_dec (2 * SDL2Z L) (SDs2Zn sds (size L).+1))
         then one
	 else zero.
  
  Lemma sd2sdi_spec sds x: x \from rep_sd sds -> x \from rep_sd_inc (sd2sdi sds).
  Proof.

  Admitted.

  Lemma sd2sdi_cont: sd_representation \translatable_to increasing_sd_representation.
  Proof.
    apply/F2MF_cont.
    exists sd2sdi.
    split; try exact/F2MF_rlzr/sd2sdi_spec.
    move =

    Lemma UI2UIi_cont: (@id _: UI_inc -> cs_UI) \is_continuous.
Proof.
  exists (F2MF UI_inc_to_UI); split; last exact/F2MF_rlzr/UI_inc_to_UI_correct.
  apply/cont_F2MF => phi.
  
Admitted.

Lemma UIi2UI_cont: (@id _: cs_UI -> UI_inc) \is_continuous.
Proof.
Admitted.

Lemma UI_UI_inc_iso: cs_UI ~=~ UI_inc.
Proof.
  have /cfun_spec ass := UIi2UI_cont.
  exists (exist _ _ ass). 
  have /cfun_spec ass':= UI2UIi_cont.
  by exists (exist _ _ ass').
Qed.
End UI_and_UI_inc.

Section sd_coinduction.
(*
Lemma SDs2R_hd sds x: SDs2R sds x -> - 1 <= 2 * x - SD2R (sds 0%nat) <= 1.
Proof.
move: x => x; rewrite /=/GRing.zero /=. SDs2R_eff => unx.
specialize (unx 1%nat); move: unx; rewrite /SDs2Rn big_ord1.
by case: (sds 0%nat) => /=; rewrite /GRing.mul /=; split_Rabs; lra.
Qed.*)
(*
Lemma SDs2R_tl sds x: SDs2R sds x -> SDs2R (fun n => sds n.+1) (2 * x - SD2R (sds 0%nat)).
Proof.
rewrite !SDs2R_eff => unx n; apply: (Rmult_le_reg_l (/2)); try lra.
rewrite -[/2 * / _]Rinv_mult_distr; try lra; last by have:= pow_lt 2 n; lra.
apply/ Rle_trans; last by apply: unx n.+1.
rewrite {2}/SDs2Rn big_ord_recl /= /SDs2Rn.
suff <- : (/ 2 * \sum_(i < n) SD2R (sds i.+1) * /2 ^ i.+1) = \sum_(i < n) SD2R (sds (bump 0 i)) * / (2 * (2 * 2 ^ i)) by rewrite /GRing.mul /GRing.add/=; split_Rabs; try lra.
elim: n => [ | n ih]; first by rewrite !big_ord0 /GRing.zero /=; lra.
have p2lt: 0 < 2^n by apply pow_lt; lra.
rewrite big_ord_recr/= Rmult_plus_distr_l ih [RHS]big_ord_recr/=.
congr (_ + _).
have -> : bump 0 n = n.+1%nat by trivial.
rewrite !Rinv_mult_distr; try lra.
by rewrite /GRing.mul/=; try lra.
Qed.*)
End sd_coinduction.

Section output_and_examples.
Definition SDs2Qn sds n := (inject_Z (SDs2Zn sds n) / (2#1)^Z.of_nat n)%Q.
(*Example: Compute Qreduction.Qred (SDs2Qn sds 17). *)
End output_and_examples.

Section all_reals.
  Definition ZUI2R (zx: Z * UI) := IZR zx.1 + projT1 zx.2.
  
  Definition count_pos n :=
    match n with
    | 0%nat => None
    | S n => Some (Pos.of_nat n)
    end.
  
  Lemma count_pos_sur: count_pos \is_surjective.
  Proof.
    case => [p | ]; last by exists 0%nat.
    by exists (Pos.to_nat p).+1; rewrite /count_pos Pos2Nat.id.
  Qed.

  Definition cs_Z:= discrete_space Z_count.

  Definition rep_R := (F2MF ZUI2R) \o (@representation (cs_prod cs_Z cs_UI)).

  Lemma rep_R_sur: rep_R \is_cototal.
  Proof.
    move => x; have ineq: -1 <= x - up x <= 1 by have := archimed x; lra.
    pose y:UI := (exist _ (x - up x) ineq).
    have [phi2 phi2ny]:= rep_UI_sur y.
    pose phi1: B_ cs_Z := (fun _ => up x).
    exists (pair (phi1, phi2: B_ cs_UI)).
    split; last by move => a b; apply F2MF_tot.
    exists (up x, y).
    split; last by rewrite /F2MF /y /ZUI2R /=; lra.
    apply/prod_name_spec.
    have ->:= @lprj_pair cs_Z cs_UI.
    by have ->:= @rprj_pair cs_Z cs_UI.
  Qed.

  Lemma rep_R_sing: rep_R \is_singlevalued.
  Proof. apply/comp_sing; [apply: F2MF_sing | by have:=(@rep_sing (cs_prod cs_Z cs_UI)) ]. Qed.
End all_reals.
