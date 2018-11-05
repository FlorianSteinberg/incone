From mathcomp Require Import all_ssreflect.
Require Import all_cs classical_mach reals.
Require Import Qreals Reals Psatz ClassicalChoice FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CAUCHYREALS.
Import QArith.
Local Open Scope R_scope.

Definition rep_C : (Q -> Q) ->> R := make_mf (
  fun phi x => forall eps, 0 < Q2R eps-> Rabs(x-Q2R(phi eps)) <= Q2R eps).
(* This is close to the standard definition of the chauchy representation. Usually integers
are prefered to avoid to many possible answers. I tried using integers, but it got very ugly
so I gave up at some point. I feel like the above is the most natural formulation of the Cauchy
representation anyway. *)

(* Auxillary lemmas for the proof that the Cauchy representation is surjective. *)
Lemma approx : forall r, r - Int_part r <= 1.
Proof. move => r; move: (base_Int_part r) => [bipl bipr]; lra. Qed.

Lemma approx' : forall r, 0 <= r - Int_part r.
Proof. move => r; move: (base_Int_part r) => [bipl bipr]; lra. Qed.

Lemma rep_C_sur: rep_C \is_cototal.
Proof.
move => x.
exists (fun eps => Qmult eps (Qmake(Int_part(x/(Q2R eps))) xH)) => epsr eg0.
rewrite Q2R_mult.
set eps := Q2R epsr.
rewrite Rabs_pos_eq.
	set z := Int_part(x/eps).
	replace (x - eps * Q2R (z#1)) with (eps * (x / eps - z));first last.
		rewrite /Q2R/=; field.
		by apply: Rlt_dichotomy_converse; right; rewrite /eps.
	rewrite -{3}(Rmult_1_r eps).
	apply: Rmult_le_compat_l; first by left; rewrite /eps.
	apply: (approx (x * /eps)).
apply: (Rmult_le_reg_l (/eps)).
	by apply: Rinv_0_lt_compat; rewrite /eps.
rewrite Rmult_0_r.
set z := Int_part(x/eps).
replace (/eps*(x - eps * Q2R (z#1))) with (x/eps - z);last first.
	rewrite /Q2R/=; field.
	by apply: Rlt_dichotomy_converse; right; rewrite /eps.
by apply (approx' (x * /eps)).
Qed.

Definition Rc_interview_mixin: interview_mixin.type (Q -> Q) R.
Proof. exists rep_C; exact/rep_C_sur. Defined.

Definition Rc_interview := interview.Pack Rc_interview_mixin.

Lemma rep_C_sing: rep_C \is_singlevalued.
Proof.
move => phi x x' phinx phinx'.
apply (cond_eq_f accf_Q2R_0) => q qg0.
set r := Q2R (phi (q/(1 + 1))%Q); rewrite /R_dist.
replace (x-x') with ((x-r) + (r-x')) by field.
apply /triang /Rle_trans.
	apply /Rplus_le_compat; last rewrite Rabs_minus_sym; [apply phinx | apply phinx'];
		rewrite Q2R_div; try lra; rewrite {2}/Q2R/=; lra.
by rewrite Q2R_div; try lra; rewrite {2 4}/Q2R/=; lra.
Qed.

Definition Rc_dictionary_mixin: dictionary_mixin.type Rc_interview.
Proof. split; exact rep_C_sing. Defined.

Canonical Rc_dictionary := dictionary.Pack Rc_dictionary_mixin.

Lemma rationals_countable: Q \is_countable.
Proof.
Admitted.

Canonical Rc := continuity_space.Pack
	0%Q
	0%Q
	rationals_countable
	rationals_countable
	Rc_dictionary.

Section addition.
Definition Ropp_rlzrf phi (eps: Q) := Qopp (phi eps).

Definition Ropp_rlzr := F2MF Ropp_rlzrf.

Lemma Ropp_rlzr_spec: Ropp_rlzr \realizes (F2MF Ropp: Rc ->> Rc).
Proof.
rewrite F2MF_rlzr_F2MF => phi x phinx eps epsg0 /=.
rewrite Q2R_opp; move: (phinx eps epsg0); split_Rabs; lra.
Qed.

Lemma Ropp_rlzr_cont: Ropp_rlzr \is_continuous_operator.
Proof.
by rewrite F2MF_cont /Ropp_rlzrf => phi; exists (fun eps => [:: eps]) => psi q' [<-].
Qed.

Lemma Ropp_hcr: (F2MF Ropp: Rc ->> Rc) \has_continuous_realizer.
Proof. exists Ropp_rlzr; split; [apply/Ropp_rlzr_spec | apply/Ropp_rlzr_cont]. Qed.

Lemma Ropp_cont: (Ropp: Rc -> Rc) \is_continuous.
Proof. exact/Ropp_hcr. Qed.

Definition Rplus_rlzrf phi (eps: Q) :=
	(Qplus (phi (inl (Qdiv eps (1+1)))).1 (phi (inr (Qdiv eps (1+1)))).2).

Definition Rplus_rlzr:= F2MF Rplus_rlzrf.

Lemma Rplus_rlzr_spec:
	Rplus_rlzr \realizes (F2MF (fun x => Rplus x.1 x.2) : (Rc \*_cs Rc) ->> Rc).
Proof.
rewrite F2MF_rlzr_F2MF.
move => phi x phinx eps eg0.
rewrite /Rplus_rlzr Q2R_plus.
set phi0 := (fun q => (phi (inl q)).1).
set phi1 := (fun q => (phi (inr q)).2).
set r := Q2R (phi0 (Qdiv eps (1 + 1))).
set q := Q2R (phi1 (Qdiv eps (1 + 1))).
have ->: (x.1 + x.2 - (r + q)) = (x.1 - r + (x.2 - q)) by field.
apply: triang; rewrite -(eps2 (Q2R eps)).
have eq: Q2R eps * / 2 = Q2R (eps / (1 + 1)).
	symmetry; rewrite Q2R_div; last by lra.
	by rewrite {2}/Q2R/=; lra.
by rewrite eq; apply: Rplus_le_compat; apply phinx; lra.
Qed.

Lemma Rplus_rlzr_cont: Rplus_rlzr \is_continuous_operator.
Proof.
rewrite F2MF_cont => phi; exists (fun eps => [:: inl (Qdiv eps (1 + 1)); inr (Qdiv eps (1 + 1))]).
by rewrite /Rplus_rlzrf => psi q' [-> [-> _]].
Qed.

Lemma Rplus_cont: (fun (xy: Rc \*_cs Rc) => xy.1 + xy.2: Rc) \is_continuous.
Proof. exists Rplus_rlzr; split; first exact/Rplus_rlzr_spec; exact/Rplus_rlzr_cont. Qed.
End addition.

Section multiplication.
(* Multiplication is more involved as the precision of approximations that have to be used
depends on the size of the inputs *)
Let trunc (eps: questions Rc) := if Qlt_le_dec eps 1 then eps else (1%Q: questions Rc).
Let rab := (fun (phi : Q -> Q) => inject_Z(up(Rabs(Q2R(phi (1#2)))+1))).
Definition Rmult_rlzr := F2MF (fun phi (eps: Q) =>
  ((phi (inl (trunc eps / (1 + 1)/(rab (fun q => (phi(inr q)).2))))).1
  *
  (phi (inr (eps / (1 + 1)/(rab (fun q => (phi(inl q) ).1))))).2)%Q).

Lemma Rmult_rlzr_crct:
	Rmult_rlzr \realizes (F2MF (fun x => Rmult x.1 x.2):Rc \*_cs Rc ->> Rc).
Proof.
have rab_pos: forall phi, Q2R (rab phi) >= 1.
	move => phi; rewrite /Q2R/rab/=.
	replace (/ 1) with 1 by field; rewrite Rmult_1_r; apply Rle_ge.
	apply: Rle_trans; last by	apply Rlt_le; apply archimed.
	by rewrite -{1}(Rplus_0_l 1); apply Rplus_le_compat_r; exact: Rabs_pos.
rewrite F2MF_rlzr_F2MF.
have ineq: forall eps, Q2R (trunc eps) <= (Q2R eps).
	by move => eps; rewrite /trunc; case: (Qlt_le_dec eps 1) => ass /=; [lra | apply Qle_Rle].
move => phipsi [x y] [phinx psiny] eps eg0 /=.
rewrite Q2R_mult.
set phi := (fun q:Q => (phipsi (inl q)).1:Q).
rewrite -/phi/= in phinx.
set psi := (fun q:Q => (phipsi (inr q)).2:Q).
rewrite -/psi/= in psiny.
set r := Q2R (phi (trunc eps / (1 + 1) / rab psi)%Q).
set q := Q2R (psi (eps / (1 + 1) / rab phi)%Q).
specialize (ineq eps).
have truncI: 0 < Q2R (trunc eps) <= 1.
	rewrite /trunc; case: (Qlt_le_dec eps 1) => /= ass; last by rewrite /Q2R/=; lra.
	split => //; apply Rlt_le; replace 1 with (Q2R 1) by by rewrite /Q2R/=; lra.
	by apply Qlt_Rlt.
have g0: 0 < Q2R (eps / (1 + 1)) by rewrite Q2R_div; first rewrite {2}/Q2R/=; lra.
have rabneq: forall phi', ~ rab phi' == 0.
	move => phi' eq; move: (Qeq_eqR (rab phi') 0 eq).
	apply Rgt_not_eq; replace (Q2R 0) with 0 by by rewrite /Q2R/=; lra.
	specialize (rab_pos phi'); lra.
replace (x * y - r * q) with ((x - r) * y + r * (y - q)) by field.
apply: triang.
replace (Q2R eps) with (Q2R (eps/ (1 + 1)) + Q2R (eps/ (1 + 1))); last first.
	rewrite Q2R_div; first rewrite {2 4}/Q2R/=; lra.
apply: Rplus_le_compat.
	specialize (rab_pos psi).
	rewrite Rabs_mult.
	case: (classic (y = 0)) => [eq | neq].
		by apply/ Rle_trans; last apply/ Rlt_le /g0; rewrite eq Rabs_R0; lra.
	rewrite -(Rmult_1_r (Q2R (eps / (1 + 1)))) -(Rinv_l (Rabs y)); last by split_Rabs; lra.
	rewrite -Rmult_assoc;	apply: Rmult_le_compat; [ split_Rabs | split_Rabs | | ]; try lra.
	apply/ Rle_trans; first apply phinx; rewrite Q2R_div => //.
		apply Rmult_gt_0_compat; last by apply Rlt_gt; apply Rinv_0_lt_compat; lra.
		by apply Rlt_gt; rewrite Q2R_div; first rewrite {2}/Q2R/=; lra.
	apply Rmult_le_compat; [ | apply Rlt_le; apply Rinv_0_lt_compat; lra | | ].
			rewrite Q2R_div; first rewrite {2}/Q2R/=; first apply Rlt_le; lra.
		by rewrite !Q2R_div; [ | lra | lra]; apply Rmult_le_compat_r; first by rewrite /Q2R/=; lra.
	apply: Rinv_le_contravar; first	exact: Rabs_pos_lt.
	rewrite /rab {1}/Q2R/=; replace (/1) with 1 by lra; rewrite Rmult_1_r.
	apply/ Rle_trans; last apply/ Rlt_le; last apply: (archimed (Rabs (Q2R (psi (1#2)))+1)).1.
	suffices: (Rabs y -Rabs (Q2R (psi (1#2))) <= 1) by lra.
	apply/ Rle_trans; first by apply: Rabs_triang_inv.
	apply: Rle_trans; first apply: psiny; rewrite /Q2R/=; lra.
rewrite Rabs_mult.
case: (classic (r = 0)) => [eq | neq].
	by apply/ Rle_trans; [rewrite eq Rabs_R0 | apply/ Rlt_le/ g0]; lra.
rewrite /Qdiv -(Rmult_1_l (Q2R (eps / (1 + 1)))).
rewrite -(Rinv_r (Rabs r)); last by split_Rabs; lra.
rewrite Rmult_assoc.
apply: Rmult_le_compat; [ split_Rabs | split_Rabs | | ]; try lra; rewrite Rmult_comm.
apply/ Rle_trans; first rewrite /q; first apply psiny.
	rewrite Q2R_div => //; apply Rmult_gt_0_compat=>//; apply Rlt_gt.
	by apply Rinv_0_lt_compat; have:= rab_pos phi; lra.
rewrite Q2R_div => //.
apply Rmult_le_compat_l => //; first by rewrite Q2R_div => //; apply Rlt_le; rewrite {2}/Q2R/=; lra.
apply Rle_Rinv; first exact: Rabs_pos_lt.
	specialize (rab_pos phi); lra.
rewrite /rab {1}/Q2R/=; replace (/1) with 1 by lra; rewrite Rmult_1_r.
apply/ Rle_trans; last apply/ Rlt_le; last apply: (archimed (Rabs (Q2R (phi (1#2)))+1)).1.
suffices: (Rabs r -Rabs (Q2R (phi (1#2))) <= 1) by lra.
apply/ Rle_trans; first apply: Rabs_triang_inv.
apply: Rle_trans.
	replace (r - Q2R (phi (1#2))) with ((r - x) - (Q2R (phi (1#2)) - x)) by field.
	apply /triang/ Rplus_le_compat; last by rewrite Ropp_minus_distr; apply phinx; rewrite /Q2R/=; lra.
	rewrite Rabs_minus_sym; apply phinx.
	specialize (rab_pos psi); rewrite !Q2R_div => //; rewrite {2}/Q2R/=.
	by apply Rmult_gt_0_compat; try lra; apply /Rlt_gt/ Rinv_0_lt_compat; lra.
specialize (rab_pos psi).
rewrite !Q2R_div; [ | by lra | trivial].
rewrite {4}/Q2R/= {1}/Rdiv.
replace (1 * / 2) with (/2 * 1) by lra.
rewrite -(Rinv_r (Q2R (rab psi))); try lra.
rewrite -Rmult_assoc -Rmult_plus_distr_r.
apply: Rmult_le_compat_r; first by apply Rlt_le; apply Rinv_0_lt_compat; lra.
suffices: Q2R (trunc eps) / Q2R (1 + 1) <= Q2R (rab psi)/2 by lra.
by rewrite !/Rdiv {2}/Q2R/=; apply Rmult_le_compat; try lra.
Qed.
End multiplication.

Section limit.
(* The unrestricted limit function is discontinuous with respect to the Cauchy representation,
and thus there is no hope to prove it computable *)
Lemma cnst_dscr q: (cnst q) \is_description_of (Q2R q: Rc).
Proof. rewrite /cnst => eps; split_Rabs; lra. Qed.

Lemma cnst_sqnc_dscr q: (cnst q) \is_description_of (cnst (Q2R q): cs_sig_prod Rc).
Proof. rewrite /cnst => n eps ineq; split_Rabs; lra. Qed.

Lemma Q_sqnc_dscr qn:
	(fun neps => qn neps.1) \is_description_of ((fun n => Q2R (qn n)): cs_sig_prod Rc).
Proof. move => n eps ineq /=; split_Rabs; lra. Qed.

Lemma lim_cnst x: lim (cnst x) x.
Proof. exists 0%nat; rewrite /cnst; split_Rabs; lra. Qed.

Lemma lim_not_cont: ~(lim: cs_sig_prod Rc ->> Rc) \has_continuous_realizer.
Proof.
move => [/= F [/= rlzr cont]].
pose xn := cnst (Q2R 0):cs_sig_prod Rc.
have limxn0: lim xn (Q2R 0) by exists 0%nat; rewrite /xn/cnst; split_Rabs; lra.
have qnfdF: cnst 0%Q \from dom F.
	by apply /(rlzr_dom rlzr); [exact/cnst_sqnc_dscr | exists (Q2R 0)].
have [Lf Lmod]:= cont (cnst 0%Q) qnfdF.
set fold := @List.fold_right nat nat.
pose L := Lf 1%Q.
pose m:= fold maxn 0%N (unzip1 L).
have mprop: forall n eps, List.In (n, eps) L -> (n <= m)%nat.
	rewrite /m; elim: {1 2}L => // a K ih n eps /=.
	by case =>[-> | ineq]; apply/leq_trans; [ | apply/leq_maxl | apply/ih/ineq | apply/leq_maxr].
pose yn:= (fun n => Q2R (if (n <= m)%nat then 0%Q else 3#1)): cs_sig_prod Rc.
pose rn (p: nat * Q) := if (p.1 <= m)%nat then 0%Q else 3#1.
have rnyn: rn \is_description_of yn by apply/Q_sqnc_dscr.
have limyn3: lim yn 3.
	exists (S m) => n /leP ineq; rewrite /yn.
	case: ifP => [/leP ineq' | ]; [lia | split_Rabs; lra].
have [phi Frnphi]: rn \from dom F by apply /(rlzr_dom rlzr); first exact/rnyn; exists 3.
have /coin_spec coin: (cnst 0%Q) \and rn \coincide_on L.
	apply /coin_lstn => [[n eps] listin].
	rewrite /cnst /rn; case: ifP => // /= /leP ineq.
	exfalso; apply/ineq/leP/mprop/listin.
have [psi Fqnpsi]:= qnfdF.
have eq: psi 1%Q == phi 1%Q.
	by have [a' crt]:= Lmod 1%Q; rewrite (crt rn coin phi)// (crt (cnst 0%Q) _ psi) //.
have := Qeq_eqR (psi 1%Q) (phi 1%Q) eq.
have psin0: psi \is_description_of (0: Rc).
	apply /(rlzr_val_sing _ rlzr)/Fqnpsi/lim_cnst; first exact/lim_sing.
	rewrite /cnst/=/Q2R /=; split_Rabs; lra.
have phin3: phi \is_description_of (3: Rc).
	by apply/(rlzr_val_sing _ rlzr)/Frnphi/limyn3; first exact/lim_sing.
have l01: 0 < Q2R 1 by rewrite /Q2R/=; lra.
have:= psin0 1%Q l01; have:= phin3 1%Q l01.
by rewrite {2 4}/Q2R/=; split_Rabs; lra.
Qed.

Fixpoint Pos_size p := match p with
	| xH => 1%nat
	| xI p' => S (Pos_size p')
	| xO p' => S (Pos_size p')
end.

Lemma Pos_size_gt0 p: (0 < Pos_size p)%nat.
Proof. by elim p. Qed.

Definition Z_size z:= match z with
	| Z0 => 0%nat
	| Z.pos p => Pos_size p
	| Z.neg p => Pos_size p
end.

Lemma Z_size_eq0 z: Z_size z = 0%nat <-> z = 0%Z.
Proof.
split; last by move => ->.
case z => // p /=; have := Pos_size_gt0 p => /leP ineq eq; rewrite eq in ineq; lia.
Qed.

Lemma Z_size_lt z: IZR z < 2 ^ (Z_size z).
Proof.
rewrite pow_IZR; apply IZR_lt; rewrite -two_power_nat_equiv.
elim: z => // p; elim: p => // p /= ih.
rewrite !Pos2Z.inj_xI two_power_nat_S.
have ineq: (Z.pos p + 1 <= two_power_nat (Pos_size p))%Z by lia.
apply/ Z.lt_le_trans; last by apply Zmult_le_compat_l; last lia; apply ineq.
by lia.
Qed.

Lemma size_Qden_leq eps: 0 < Q2R eps -> /2^(Pos_size (Qden eps)) <= Q2R eps.
Proof.
move => ineq; rewrite /Q2R/Rdiv /Qdiv -[/_]Rmult_1_l.
apply Rmult_le_compat; [ | apply Rlt_le; apply Rinv_0_lt_compat; apply pow_lt | | ]; try lra.
	apply IZR_le; suffices: (0 < Qnum eps)%Z by lia.
	by apply Qnum_gt; apply Rlt_Qlt; rewrite {1}/Q2R/=; try lra.
apply Rinv_le_contravar; first exact /IZR_lt/Pos2Z.is_pos.
by have /=:= Z_size_lt (Z.pos (Qden eps)); lra.
Qed.

Definition lim_eff_frlzr phin eps :=
	phin (S (Pos_size (Qden eps))%nat, (Qmult eps (1#2))): Q.

Definition lim_eff_rlzr := F2MF lim_eff_frlzr.

Lemma lim_eff_frlzr_crct:
	lim_eff_rlzr \realizes (lim_eff: cs_sig_prod Rc ->> Rc).
Proof.
rewrite F2MF_rlzr => psi xn psinxn [x limxnx].
exists x; split => // eps epsg0.
set N:= (Pos_size (Qden eps)).
have ->: x - Q2R (lim_eff_frlzr psi eps) = x - (xn N.+1) + (xn N.+1 - Q2R (lim_eff_frlzr psi eps)) by lra.
rewrite /lim_eff_frlzr -/N; apply/triang/Rle_trans.
	apply/Rplus_le_compat; first by rewrite Rabs_minus_sym; apply/limxnx.
	by apply psinxn; rewrite Q2R_mult {2}/Q2R/=; lra.
have lt1:= pow_lt 2 (Pos_size (Qden eps)); have lt2:= size_Qden_leq epsg0.
by rewrite Q2R_mult {2}/Q2R /= /N Rinv_mult_distr; lra.
Qed.
End limit.

(*
Lemma cont_rlzr_cont (f: Rc -> Rc): (F2MF f) \has_continuous_realizer <-> continuity f.
Proof.
split.
	move => [F [rlzr cont]] x e eg0.
	have [phi phinx]:= get_description (x: Rc).
	have [Fphi FphiFphi]: phi \from dom F by apply/(rlzr_dom rlzr)/F2MF_tot/phinx.
	have Fphinfx: Fphi \is_description_of (f x).
		by apply/(rlzr_val_sing _ rlzr phinx); first exact/F2MF_sing.
	have [eps [epsg0 epsle]]:= accf_Q2R_0 eg0.
	have [ | L [_ /=Lprop]]:= cont phi _ eps; first apply/(rlzr_dom rlzr)/F2MF_tot/phinx.
	elim: L Lprop => [/=Lprop | ].
		exists 1; split => [ | y [cnd neq]]; first by lra.
		rewrite /R_dist.
		set r:= Q2R (Fphi (Qdiv eps (1 + 1))).
		have ->: f y - f x = f y - r - (f x - r) by ring.
		apply/Rle_lt_trans/epsle/Rle_trans.
			apply/triang/Rplus_le_compat; last first.
				rewrite Rabs_Ropp; apply/Fphinfx.
				admit.
			have [psi psiny]:= get_description (y: Rc).
			have [Fpsi FpsiFpsi]: psi \from dom F by apply /(rlzr_dom rlzr)/F2MF_tot/psiny.
			have: F phi Fpsi.
				have <-: Fphi = Fpsi; last done.
					apply functional_extensionality => q'.
					have :=(Lprop Fphi FphiFphi psi _ Fpsi).
					have: Fphi = (fun q' => Fphi q').
			have: Fphi \is_description_of (f y).
			apply/(rlzr_val_sing _ rlzr psiny); first exact/F2MF_sing.
Admitted.

Definition dom_cont g:= make_subset (fun x => continuity_pt g x).
Lemma cont_hcr (f: Rc ->> Rc): f \has_continuous_realizer <-> exists g, f =~= (F2MF g)|_(dom_cont g).
Proof.
Admitted.
*)
End CAUCHYREALS.