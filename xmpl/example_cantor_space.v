From mathcomp Require Import ssreflect ssrfun eqtype ssrbool seq.
Require Import all_cs dscrt sets Classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition Cantor:=  cs_bool\^w.

Definition nz_Sirp := make_mf (fun (p: Cantor) (s: cs_Sirp) =>
                                 (s = top <-> exists n, p n = true)
                                 /\
                                 (s= bot <-> forall n, p n = false)).

Lemma nz_Sirp_tot: nz_Sirp \is_total.
Proof.
move => p.
case: (classic (exists n, p n = true)) => [ass | neg].
- exists top; split; first by split.
  by split => // ass'; have [n]:= ass; rewrite ass'.
exists bot; split; split => // _ n.
by apply/negP => pn; apply/neg; exists n; rewrite pn.
Qed.

Lemma nz_Sirp_sing: nz_Sirp \is_singlevalued.
Proof.
move => p [[]// [[[]// n eq _ _ [[_ <-]//]]] | []//]; first by exists n.
by move => [_ [prp _] [_ [_ <-]]]//; apply/prp.
Qed.

Definition nz_rlzr:= F2MF (fun (phi: names Cantor) (q: questions cs_Sirp) => phi (q, tt): answers cs_Sirp).

Lemma nz_rlzr_spec: nz_rlzr \realizes nz_Sirp.
Proof.
rewrite F2MF_rlzr => phi x phinx _.
case: (classic (forall n, x n = false)) => ass.
- exists bot; split => //.
  - by split => // [[n]]; have /=:= phinx n; rewrite ass /= => ->.
  by split; split => // [[n eq]]; rewrite ass in eq.
exists top; split.
- split => // _.
  have [n neq]:=(not_all_ex_not _ _ ass).
  exists n; have:= phinx n.
  exfalso; apply/ass.
  exists top; split => //; split => // _.
have [n neq]:= (not_all_ex_not _ _ ass).
exists n; have := phinx n.
have -> /=: x n = true by case: (x n) neq => // a; case a.
by case => -> /=.
Qed.

Lemma nz_rlzr_cntop: nz_rlzr \is_continuous_operator.
Proof.
by rewrite F2MF_cont => phi; exists (fun q => [:: (q, tt)]) => psi q [ -> _].  
Qed.
  
Lemma F_cont: nz \has_continuous_realizer.
Proof. exists nz_rlzr; split; [exact/nz_rlzr_spec | exact/nz_rlzr_cntop]. Qed.
