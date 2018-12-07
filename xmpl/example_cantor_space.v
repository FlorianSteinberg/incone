From mathcomp Require Import ssreflect ssrfun eqtype ssrbool seq ssrnat.
From rlzrs Require Import choice_mf.
Require Import all_cs dscrt sets Classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Cantor space can be defined as the infinte coproduct of the two point
space **)
Definition Cantor:=  cs_bool\^w.

(** Let's take a look at the characteristic function of the set that only
excludes the constant zero function: **)
Definition nz_bool := make_mf (fun (p: Cantor) (s: cs_bool) =>
                                 (s = true <-> exists n, p n = true)).

(** The function defined above is indeed a function, i.e. it is singlevalued **)
Lemma nz_bool_sing: nz_bool \is_singlevalued.
Proof.
move => p [[ | [[ | n eq _ [_ ->]]]] | []]//; first by exists n.
by move => [_ prp [ex _]]//; apply/prp/ex.
Qed.

(** And total **)
Lemma nz_bool_tot: nz_bool \is_total.
Proof.
move => p.
case: (classic (exists n, p n = true)).
- by exists true.
by exists false.
Qed.

Lemma nz_fun: nz_bool \is_function.
Proof.
apply/fun_spec; first exact/true.
split; [exact/nz_bool_sing | exact/nz_bool_tot].
Qed.

(**However, as a function to the discrete two point space, this function is
not continuous.
Here, the notion of continuity comes from representations that
the Cantor space and the two point space are equipped with.**)
Lemma nz_bool_not_cont: ~ nz_bool \has_continuous_realizer.
Proof.
move => [F [rlzr cont]].
have nmb: xpred0 \is_description_of (false: cs_bool) by trivial.
have nmc: xpred0 \is_description_of (xpred0 : Cantor) by trivial.
have [ | [Fxpred0 val] prp]:= rlzr xpred0 xpred0 nmc.
- by exists false; split => // [[]].
have [b [Fxnf [[]]]]//:= prp Fxpred0 val.
apply/negP => eq'; have eq: b = false by case: b eq' Fxnf.
move: eq' => _; rewrite eq // in Fxnf; move: b eq => _ _.
have [mf mod]:= cont xpred0 Fxpred0 val.
set N:= foldr maxn 0 (map fst (mf tt)).
pose chi n := if n <= N then false else true.
have nz_valtrue: nz_bool chi true by split => // _; exists N.+1; rewrite /chi ltnn.
suff nz_valfalse: nz_bool chi false by have:= (nz_bool_sing nz_valtrue nz_valfalse).
have [psi psinchi] := get_description (chi: Cantor).  
have [ | [Fpsi val'] cnd]:= rlzr psi chi psinchi; first exact/nz_bool_tot.
suff Fpsinf: Fpsi \is_description_of (false: cs_bool).
- by have [b [Fpsinb ]]:= cnd Fpsi val'; have ->:= (rep_sing _ _ _ Fpsinb Fpsinf).  
rewrite /= -Fxnf; apply/mod/val'.
apply/coin_lstn => [[n []]] lstn; rewrite psinchi.
suff ineq: n <= N by rewrite /chi ineq.
rewrite /N; elim: (mf tt) lstn => //k L ih /= [->/= | lstn]; first exact/leq_maxl.
exact/leq_trans/leq_maxr/ih.
Qed.

(**There are several ways to define continuous versions of this function.
The first possibility is to make it a partial function that is undefined in the
zero-function instead of returning false**)

Definition nz_bool_p := make_mf (fun (chi: Cantor) (b: cs_bool) =>
                                   exists n, chi n = true /\ b = true).

(** This function is still singlevalued **)
Lemma nz_bool_p_sing: nz_bool_p \is_singlevalued.
Proof.
by move => chi [[ | _ [n []]] | [[n []] | ]]//.
Qed.

(** But not total anymore **)
Lemma nz_bool_p_not_tot: ~ nz_bool_p \is_total.
Proof. by move => tot; have [[[n []] | [n []]]]//:= tot xpred0. Qed.

(** But, it is continuous. Too prove this, it is necessary to explcitly work
with the encodings **)
Definition nzb_rlzr := make_mf(fun (psi: names Cantor) (b: names cs_bool) =>
                               exists n, psi (n, tt) = true /\ b tt = true).

Lemma nzb_rlzr_spec: nzb_rlzr \realizes nz_bool_p.
Proof.
move => psi chi psinchi [b [n [eq eq']]].
split => [ | Fpsi [k [vq vq']]]; first by exists (fun _ => true); exists n; rewrite psinchi.
by exists true; split; last exists n. 
Qed.

Lemma nzb_rlzr_cntop: nzb_rlzr \is_continuous_operator.
Proof.
move => psi b [_ [_ eq']].
by exists (fun _ => [::]) => [[]] psi' _ b' [_ [_ ->]].
Qed.            

Lemma nz_bool_p_cont: nz_bool_p \has_continuous_realizer.
Proof.
by exists nzb_rlzr; split; [exact/nzb_rlzr_spec | exact/nzb_rlzr_cntop].
Qed.

(** Another way to make the function continuous is to use Sirpinski space.
This space has two points, but is equipped with a different representation,
that makes the same function computable *)
Definition nz_Sirp := make_mf (fun (p: Cantor) (s: cs_Sirp) =>
                                 (s = top <-> exists n, p n = true)).

(** The proofs that this defines a function is identical to thos for bool **)
Lemma nz_Sirp_tot: nz_Sirp \is_total.
Proof.
move => p.
case: (classic (exists n, p n = true)) => [ass | neg].
- by exists top.
by exists bot.
Qed.

Lemma nz_Sirp_sing: nz_Sirp \is_singlevalued.
Proof.
move => p [[ | [[ | n eq _ [_ ->]]]] | []]//; first by exists n.
by move => [_ prp [ex _]]//; apply/prp/ex.
Qed.

(** In contrast to the realizer of the partial function above, the realizer
on Sirpinski-space can be written down explicitly and not only as a relation. **)
Definition nzS_rlzr:= F2MF (fun (phi: names Cantor) (q: questions cs_Sirp) => phi (q, tt): answers cs_Sirp).

Lemma nzS_rlzr_spec: nzS_rlzr \realizes nz_Sirp.
Proof.
rewrite F2MF_rlzr => phi chi phinchi _.  
case: (classic (exists n, chi n = true)) => [[n eq] | ass].
- exists top; split; last by split => // _; exists n.
  by split => // _; exists n; rewrite phinchi.
exists bot; split; [split => // [[n eq]] | by split].
by exfalso; apply/ass; exists n; rewrite -phinchi.
Qed.

Lemma nz_rlzr_cntop: nzS_rlzr \is_continuous_operator.
Proof.
by rewrite cntop_F2MF => phi; exists (fun q => [:: (q, tt)]) => psi q [ -> _].  
Qed.
  
Lemma nz_Sirp_cont: nz_Sirp \has_continuous_realizer.
Proof. exists nzS_rlzr; split; [exact/nzS_rlzr_spec | exact/nz_rlzr_cntop]. Qed.
(** Note that the algorithm of a function to Sirpinskispace has a defined behavior
when the input happens to be the zero function, while a realizer of nz_bool_p
may behave arbitrary in the zero function. Of course, in this case it must
also diverge if it is supposed to be a continuous operator. **)