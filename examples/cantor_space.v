From mathcomp Require Import ssreflect ssrfun eqtype ssrbool seq ssrnat.
From mf Require Import classical_mf.
From rlzrs Require Import all_rlzrs.
Require Import axioms all_cs dscrt sets Classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Cantor space can be defined as the infinte product of the two point
space **)
Definition Cantor:=  cs_bool\^w.

(** Let's take a look at the characteristic function of the set that only
excludes the constant zero function: **)
Definition nz_bool := make_mf (fun (p: Cantor) (s: cs_bool) =>
                                 (s = true <-> exists n, p n = true)).

(** The function defined above is indeed a function, i.e. it is singlevalued **)
Lemma nz_bool_sing: nz_bool \is_singlevalued.
Proof.
  move => p [[ | [[ | n eq _ [_ ->]]]] | []]//.
    by exists n.
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
  apply/(fun_spec _ true); first exact/full_choice.
  by split; [apply/nz_bool_sing | apply/nz_bool_tot].
Qed.

(**However, as a function to the discrete two point space, this function is
not continuous. Here, the notion of continuity comes from representations
that the Cantor space and the two point space are equipped with.**)
Lemma nz_bool_not_cont: ~ nz_bool \has_continuous_realizer.
Proof.
  apply/hcs_spec => [[F [cont rlzr]]].
  have nmb: xpred0 \describes false \wrt (delta_ cs_bool) by trivial.
  have nmc: xpred0 \describes xpred0 \wrt (delta_ Cantor) by trivial.
  have [ | [Fxpred0 val] prp]:= rlzr xpred0 xpred0 nmc; first by exists false; split => // [[]].
  have [b [eq' Fxnf ]]//:= prp Fxpred0 val.
  move: eq' => [[]]//; apply/negP => eq'; have eq: b = false by case: b eq' Fxnf.
  move: eq' => _; rewrite eq // in Fxnf; move: b eq => _ _.
  have [mf mod]:= cont xpred0 Fxpred0 val.
  set N:= foldr maxn 0 (map fst (mf tt)).
  pose chi n := if n <= N then false else true.
  have nz_valtrue: nz_bool chi true by split => // _; exists N.+1; rewrite /chi ltnn.
  suff nz_valfalse: nz_bool chi false by have:= (nz_bool_sing nz_valtrue nz_valfalse).
  have [psi psinchi] := get_description (chi: Cantor).  
  have [ | [Fpsi val'] cnd]:= rlzr psi chi psinchi; first exact/nz_bool_tot.
  suff Fpsinf: Fpsi \is_description_of (false: cs_bool).
  - by have [b [? Fpsinb ]]:= cnd Fpsi val'; have <-:= (rep_sing Fpsinb Fpsinf).  
  rewrite /= -Fxnf; apply/mod/val'.
  apply/coin_agre => [[n []]] lstn; rewrite psinchi.
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
Definition nzb_rlzr : B_ Cantor ->> B_ cs_bool :=
  make_mf(fun psi b =>
            exists n, psi (n, tt) = true /\ b tt = true).

Lemma nzb_rlzr_spec: nzb_rlzr \solves nz_bool_p.
Proof.
  move => psi chi psinchi [b [n [eq eq']]].
  split => [ | Fpsi [k [vq vq']]]; first by exists (fun _ => true); exists n; rewrite psinchi.
  by exists true; split; try exists n. 
Qed.

Lemma nzb_rlzr_cntop: nzb_rlzr \is_continuous_operator.
Proof.
  move => psi b [_ [_ eq']].
  by exists (fun _ => [::]) => [[]] psi' _ b' [_ [_ ->]].
Qed.            

Lemma nz_bool_p_cont: nz_bool_p \has_continuous_realizer.
Proof.
  by exists nzb_rlzr; split; try exact/nzb_rlzr_spec; apply/nzb_rlzr_cntop.
Qed.
(** While the partial function is computable, the above does not have computational content.
It can be implemented as a partial function in Coq by adding a proof that the input eventually
hits zero as input. Another way to implement it is the use of the operator assignment, which
requires to specify slightly more information and is described in more detail in the 
"implementing operators" file. **)

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
  move => p [[[[] | [[ | n eq _ [_ ->]]]]] | []]//; first by exists n.
  by move => [[_ prp [ex _]]]//; apply/prp/ex.
Qed.

(** In contrast to the realizer of the partial function above, the realizer
on Sirpinski-space can be written down explicitly and not only as a relation. **)
Definition nzS_rlzr: B_ Cantor ->> B_ cs_Sirp
  := F2MF (fun phi q => phi (q, tt): replies cs_Sirp).

Lemma nzS_rlzr_spec: nzS_rlzr \solves nz_Sirp.
Proof.
  rewrite F2MF_slvs => phi chi phinchi chifd.  
  case: (classic (exists n, chi n = true)) => [[n eq] | ass].
  - exists top; split; try by split => // _; exists n.
    by split => // _; exists n; rewrite phinchi.
  exists bot; split; [by split | split => // [[n eq]]].
  by exfalso; apply/ass; exists n; rewrite -phinchi.
Qed.

Lemma nz_rlzr_cntop: nzS_rlzr \is_continuous_operator.
Proof.
  by rewrite cont_F2MF => phi; exists (fun q => [:: (q, tt)]) => psi q [ -> _].  
Qed.
  
Lemma nz_Sirp_cont: nz_Sirp \has_continuous_realizer.
Proof. exists nzS_rlzr; split; try exact/nzS_rlzr_spec; apply/nz_rlzr_cntop. Qed.
(** Note that the algorithm of a function to Sirpinskispace has a defined behavior
when the input happens to be the zero function, while a realizer of nz_bool_p
may behave arbitrary in the zero function. Of course, in this case it must
also diverge if it is supposed to be a continuous operator. **)
