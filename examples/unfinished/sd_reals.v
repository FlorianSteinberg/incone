From mathcomp Require Import all_ssreflect all_algebra.
From rlzrs Require Import all_rlzrs.
Require Import all_cs Rstruct classical_func.
From metric Require Import all_metric reals standard.
Require Import Reals Qreals Psatz ClassicalChoice Streams.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope R_scope.

Section signed_digits.
Inductive SD := minusone | zero | one.

Coercion SD2OB sd := match sd with
	| minusone => some false
	| zero => None
	| one => some true
end.

Lemma SD_eqClass: Equality.class_of SD.
Proof.
  exists (fun sd sd' => (SD2OB sd == SD2OB sd')%bool).
  by case; case; try exact: ReflectT; try exact: ReflectF.
Qed.

Canonical SD_eqType := Equality.Pack SD_eqClass Type.

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

Coercion SD2Z sd: Z := match sd with
	               | one => 1%Z
	               | zero => 0%Z
	               | minusone => -1%Z
end.
End signed_digits.

Section SDs.
Fixpoint SDs2Zn (sds: nat -> SD) n := match n with
	| 0%nat => 0%Z
	| m.+1 => (2 * SDs2Zn sds m + SD2Z (sds m))%Z
end.

Lemma SDs2ZnS sds n :
	SDs2Zn sds n.+1 = (2 * SDs2Zn sds n + sds n)%Z.
Proof. by trivial. Qed.

Definition SD2R sd := match sd with
	| one => 1
	| zero => 0
	| minusone => -1
end.

Coercion IZR: Z >-> R.

Lemma SD2Z_SD2R sd: SD2R sd = SD2Z sd.
Proof. by case: sd. Qed.

Definition SDs2Rn (sds: nat -> SD) n := \sum_(i < n) SD2R (sds i) * /2 ^ i.+1.

Lemma SDs2Rn_SDs2Zn sds n: SDs2Rn sds n = SDs2Zn sds n / 2^n.
Proof.
  elim: n => [ | n ih]; first by rewrite /SDs2Rn big_ord0 /GRing.zero /=; try lra.
  rewrite SDs2ZnS plus_IZR mult_IZR Rdiv_plus_distr Rmult_comm /Rdiv.
  rewrite /SDs2Rn in ih.
  rewrite /SDs2Rn big_ord_recr /= ih SD2Z_SD2R Rmult_assoc.
  have ->: 2 * / (2 * 2 ^ n) = / 2 ^ n by have lt:= pow_lt 2 n; rewrite Rinv_mult_distr; try lra.
  rewrite /GRing.mul/GRing.add/=; try lra.
Qed.

Lemma SDs2Zn_SDs2Rn sds n: IZR (SDs2Zn sds n) = 2 ^ n * SDs2Rn sds n.
Proof.
  have lt:= pow_lt 2 n.
  by rewrite SDs2Rn_SDs2Zn /Rdiv Rmult_comm Rmult_assoc Rinv_l; try lra.
Qed.

Lemma SDs2Rn0 sds: SDs2Rn sds 0%nat = 0.
Proof. by rewrite /SDs2Rn big_ord0. Qed.

Lemma Rabs_SDs2Rn u n : Rabs (SDs2Rn u n) <= 1 - /2^n.
Proof.
  rewrite /SDs2Rn; case: n => [ | n]; first by rewrite big_ord0/= /GRing.zero /=; split_Rabs; lra.
  elim: n => [ | n ih].
  - rewrite /SDs2Rn big_ord1/= /GRing.mul /=.
    by case: (u 0%nat) => /=; split_Rabs; try lra.
  rewrite /SDs2Rn big_ord_recr/=.
  have p2lt: 0 < /2^n by apply /Rinv_0_lt_compat/pow_lt; lra.
  have p2lt': 0 < 2^n by apply /pow_lt; lra.
  apply/Rle_trans; first exact/Rabs_triang.
  have ->: 1 - / (2 * (2 * 2 ^ n)) = 1 - /2^n.+1 + (/2^n.+1 -  / (2 * (2 * 2 ^ n))) by lra.
  apply Rplus_le_compat; first exact ih; rewrite !Rinv_mult_distr; try lra.
  by case: (u n.+1); rewrite /GRing.mul /= ?Rmult_0_l; split_Rabs; try lra.
Qed.

Lemma SDs2RnS sds n : SDs2Rn sds n.+1 = SDs2Rn sds n + SD2R (sds n) * /2^n.+1.
Proof. by rewrite /SDs2Rn big_ord_recr /=. Qed.

Lemma SDs2RSn sds n : SDs2Rn sds n.+1 = /2 * SDs2Rn (fun i => sds i.+1) n + /2 * SD2R (sds 0%nat).
Proof.
  rewrite /SDs2Rn big_ord_recl /= addrC.
  congr (_ + _); last rewrite Rmult_1_r /GRing.mul /=; try lra.
  elim: n => [ | n ih]; first by rewrite !big_ord0 /GRing.zero /=; lra.
  rewrite big_ord_recr /= ih [\sum_(i < n.+1) _] big_ord_recr /=.
  have ->: bump 0%nat n = n.+1 by rewrite /bump.
  rewrite Rmult_plus_distr_l.
  congr (_ + _).
  have plt:= pow_lt 2 n.
  by rewrite !Rinv_mult_distr /GRing.mul /=; try lra.
Qed.

Lemma Rabs_SDs2Rnm sds n m:
  (n <= m)%nat -> Rabs (SDs2Rn sds m - SDs2Rn sds n) <= /2^n  - /2^m.
Proof.
  move => ineq.
  elim: n m ineq sds => [m ineq sds| n ih m ineq].
  - by rewrite {2}/SDs2Rn big_ord0 Rminus_0_r Rinv_1; apply/Rabs_SDs2Rn.
  move => sds; case: m ih ineq => // m ih ineq.
  rewrite !SDs2RSn; specialize (ih m ineq (fun i => sds i.+1)).
  have lt1:= pow_lt 2n; have lt2:= pow_lt 2 m; rewrite /= !Rinv_mult_distr; split_Rabs; try lra.
Qed.

Lemma fchy_SDs2Rn sds : (SDs2Rn sds) \is_fast_Cauchy_sequence.
Proof.
  move => n m; have lt: 0 < /2 ^ m by apply/Rinv_0_lt_compat/pow_lt; lra.
  have lt': 0 < /2 ^ n by apply/Rinv_0_lt_compat/pow_lt; lra.  
  case/orP: (leq_total n m) => ineq; first rewrite dst_sym;
  by apply/Rle_trans; first apply/Rabs_SDs2Rnm => //; lra.
Qed.

Lemma cchy_SDs2Rn sds :	Cauchy_sequence (@d metric_R) (SDs2Rn sds).
Proof. exact/fchy_cchy/fchy_SDs2Rn. Qed.

Definition SDs2R := limit \o (F2MF SDs2Rn).

Lemma SDs2R_tot: SDs2R \is_total.
Proof.
  rewrite /SDs2R comp_F2MF => sds.
  have [x xprp]:= R_cmplt (cchy_SDs2Rn sds).
  by exists x.
Qed.

Lemma SDs2R_sing: SDs2R \is_singlevalued.
Proof. by apply /comp_sing; [exact /lim_sing | exact /F2MF_sing]. Qed.

Notation lim_eff:= efficient_limit.

Lemma SDs2R_lim_eff: SDs2R =~= lim_eff \o (F2MF SDs2Rn).
Proof.
  rewrite /SDs2R lim_eff_spec !comp_F2MF => sds x.
  split => [limx | [cchy limx]]//.
  by split; first by have := fchy_SDs2Rn sds.
Qed.

Lemma SDs2R_eff sds x: x \from SDs2R sds <-> x \from lim_eff (SDs2Rn sds).
Proof. have:= SDs2R_lim_eff; rewrite comp_F2MF => prp; apply prp. Qed.

Lemma SDs2R_spec: SDs2R =~= lim_eff \o F2MF SDs2Rn.
Proof. by move => sds x; rewrite comp_F2MF SDs2R_eff. Qed.  
  
Lemma SDs2R_UI u x: SDs2R u x -> -1 <= x <= 1.
Proof.
  move => /SDs2R_eff val; move: (val 0%nat) => /=.
  by rewrite /SDs2Rn big_ord0 /distance/= Rminus_0_r; split_Rabs; lra.
Qed.
End SDs.

Section Lists.
Fixpoint SDL2R L:= match L with
	| [::] => 0
	| sd :: K => SDL2R K + SD2R sd * /2 ^ (size L)
end.

Lemma SDL2RS sd L: SDL2R (sd :: L) = SDL2R L + SD2R sd * /2 ^ (size L).+1.
Proof. done. Qed.

Fixpoint SDL2Z L := match L with
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

Lemma SDs2Rn_SDL2R sds n: SDs2Rn sds n = SDL2R (iseg sds n).
Proof.
  elim: n => [ | n ih]; first by rewrite /SDs2Rn big_ord0.
  by rewrite /= SDs2RnS /= size_iseg ih.
Qed.
End Lists.

Section rep_UI.
Definition UI := { x | -1 <= x <= 1}.

Definition rep_UI := make_mf (fun sds (x: UI) => SDs2R sds (sval x)).

Lemma rep_UI_tot: rep_UI \is_total.
Proof.
  by move => sds; have [x val]:= SDs2R_tot sds; exists (exist _ x (SDs2R_UI val)).
Qed.

Lemma rep_UI_sing: rep_UI \is_singlevalued.
Proof.
  by move => sds x y sdsnx sdsny; apply /eq_sub /SDs2R_sing; [apply sdsnx | apply sdsny].
Qed.

(* To prove surjectivity it is convenient to a representation that provides more information:
   One where a name allows to extend any valid begining segment of a name in the usual
   representation by a bit. This representation is computably equivalent to the one we are
   actually interested in. *)

Definition rep_UI_inc := make_mf (fun phi (x: UI) =>
	forall L, Rabs (sval x - SDL2R L) <= /2^(size L)
	->
	Rabs (sval x - SDL2R (phi L :: L)) <= /2^(size L).+1).

Fixpoint UI_inc_to_UI_rec (Lf: seq SD -> SD) m :=
  match m with
  | 0%nat => [::]
  | S k => (Lf (UI_inc_to_UI_rec Lf k):: UI_inc_to_UI_rec Lf k)
  end.

Lemma UI_inc_to_UI_rec_size Lf n: size (UI_inc_to_UI_rec Lf n) = n.
Proof. by elim: n => // n /= ->. Qed.

Definition UI_inc_to_UI (Lf: seq SD -> SD) n := Lf (UI_inc_to_UI_rec Lf n).

Lemma UI_inc_to_UI_inseg Lf n: iseg (UI_inc_to_UI Lf) n = UI_inc_to_UI_rec Lf n.
Proof. by elim :n => // n /= ->. Qed.
  
Lemma UI_inc_to_UI_correct Lf x:
  rep_UI_inc Lf x -> rep_UI (UI_inc_to_UI Lf) x.
Proof.
  move => Lfnx.
  split => [ | _ <-]; last exact/R_cmplt/cchy_SDs2Rn.
  exists (SDs2Rn (UI_inc_to_UI Lf)); split => //.
  apply/lim_tpmn; elim => [ | n /=].  
(*  
  split_Rabs; lra.
    by rewrite /= SDs2Rn0; split_Rabs; try lra.
rewrite SDs2RnS SDs2Rn_SDL2R Rabs_minus_sym UI_inc_to_UI_inseg.
have ltn: 0<2^n by apply pow_lt; lra.
rewrite -{2}(UI_inc_to_UI_rec_size Lf n); try lra; move => ih.
have /=:= Lfnx (UI_inc_to_UI_rec Lf n) ih.
by rewrite UI_inc_to_UI_rec_size Rabs_minus_sym.
Qed.*)
Admitted.

Lemma rep_UI_inc_sing: rep_UI_inc \is_singlevalued.
Proof.
  move => Lf x y Lfnx Lfny.
  by apply/rep_UI_sing; apply/UI_inc_to_UI_correct; first exact/Lfnx.
Qed.

Lemma rep_UI_inc_nc (x: UI): 
	(forall q, exists a, Rabs (projT1 x - SDL2R q) <= /2^(size q)
		-> Rabs (projT1 x - SDL2R (a :: q)) <= /2^(size q).+1)
	-> x \from codom rep_UI_inc.
Proof. by move => R; apply (choice _ R). Qed.

Lemma rep_UI_inc_sur: rep_UI_inc \is_cototal.
Proof.
  move => [x ineq].
  apply rep_UI_inc_nc => sdL.
  case: (classic (x <= SDL2R sdL)) => leq.
  - exists minusone => /= ineq'.
    have leq':= pow_lt 2 (size sdL).
    rewrite Rinv_mult_distr; try lra.
    have leq'': 0 < /2 ^ (size sdL) by apply Rinv_0_lt_compat; lra.
    by split_Rabs; try lra.
  exists one => /= ineq'.
  have leq':= pow_lt 2 (size sdL).
  rewrite Rinv_mult_distr; try lra.
  have leq'': 0 < /2 ^ (size sdL) by apply Rinv_0_lt_compat; lra.
  by split_Rabs; try lra.
Qed.

Definition names_UI_inc:= Build_naming_space [::] (list_count SD_count) SD_count.

Definition UI_inc: cs.
  exists UI names_UI_inc rep_UI_inc.
  split; first exact/rep_UI_inc_sur.
  exact/rep_UI_inc_sing.
Defined.

Lemma rep_UI_sur: rep_UI \is_cototal.
Proof.
  move => x.
  have [Lf Lfnx]:= rep_UI_inc_sur x.
  exists (UI_inc_to_UI Lf).
  by apply UI_inc_to_UI_correct.
Qed.

Definition names_UI:= Build_naming_space 0%nat nat_count SD_count.

Definition cs_UI: cs.
  exists UI names_UI rep_UI.
  split; first exact/rep_UI_sur.
  exact/rep_UI_sing.
Defined.
End rep_UI.

Section UI_and_UI_inc.
Definition UI_to_UI_inc sds L :=
	if is_left (Z_lt_dec (SDs2Zn sds (size L).+1) (2 * SDL2Z L)) then minusone
		else if is_left (Z_lt_dec (2 * SDL2Z L) (SDs2Zn sds (size L).+1)) then one
			else zero.

Fixpoint sds n := match n with
	| 0%nat => one
	| S 0 => zero
	| S (S 0) => minusone
	| S (S (S n)) => sds n
end.

(*
Lemma UI_to_UI_inc_correct sds x:
	rep_UI sds x -> rep_UI_inc (UI_to_UI_inc sds) x.
Proof.
move: x => [x xui] /SDs2R_eff /= sdsnx L /= ineq1.
have g0: 0 < 2 ^ size L by apply pow_lt; lra.
have := sdsnx (size L).+1; rewrite Rabs_minus_sym Rinv_mult_distr; try lra.
move => ineq2.
rewrite /UI_to_UI_inc; case: ifP; case: Z_lt_dec => // lt _.
- move/(Zlt_le_succ _ _)/IZR_le: lt.
  rewrite /Z.succ plus_IZR mult_IZR SDs2Zn_SDs2Rn SDL2Z_SDL2R => /= lt.
  have ineq3: (SDs2Rn sds (size L).+1) <= SDL2R L - /2* /2^size L.
  + apply: (Rmult_le_reg_r (2* 2^size L)); try lra.
    rewrite [(_ - _) * _]Rmult_comm Rmult_minus_distr_l.
    by rewrite -Rinv_mult_distr; try lra; rewrite Rinv_r; lra.
    split_Rabs; try lra.
    admit.
case: ifP; case: Z_lt_dec => // gt _.
- move/(Zlt_le_succ _ _)/IZR_le: gt.
  rewrite /Z.succ plus_IZR mult_IZR SDs2Zn_SDs2Rn SDL2Z_SDL2R => /= gt.
  + have ineq3: (SDL2R L) <= SDs2Rn sds (size L).+1 - /2* /2^size L.
		apply: (Rmult_le_reg_r (2* 2^size L)); try lra.
		rewrite [(_ - _) * _]Rmult_comm Rmult_minus_distr_l.
		by rewrite -Rinv_mult_distr; try lra; rewrite Rinv_r; lra.
	        split_Rabs; try lra.
                admit.
have eq: (SDs2Zn sds (size L).+1 = 2 * SDL2Z L)%Z by lia.
have:= IZR_eq _ _ eq.
move: eq; rewrite SDs2Zn_SDs2Rn mult_IZR SDL2Z_SDL2R /= => _ eq.
have: (SDs2Rn sds (size L).+1 = SDL2R L).
	apply: (Rmult_eq_reg_l (2 * 2 ^size L)); lra.
by move <-; split_Rabs; try lra.
Qed.
*)

Local Open Scope cs_scope.
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