From mathcomp Require Import ssreflect ssrfun seq.
From rlzrs Require Import all_rlzrs choice_dict.
Require Import all_core cs prod sub.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section cs_functions.
Definition associate (X Y: cs):= make_mf (fun psi (f: X -> Y) =>
                                            \F_(M psi) \realizes (F2MF f)).
Arguments associate {X} {Y}.

Notation "X c-> Y" := (codom (@associate X Y)) (at level 2).

Definition function_representation (X Y: cs) := make_mf (fun psi (f: X c-> Y) =>
                                                        associate psi (projT1 f)).

Lemma fun_rep_sur (X Y: cs): (function_representation X Y) \is_cototal.
Proof. by move => [f [psi ass]]/=; exists psi. Qed.

Definition cs_fun_assembly_mixin (X Y: cs) : interview_mixin.type
	(seq (answers X) * questions Y -> seq (questions X) + (answers Y)) (X c-> Y).
Proof. exists (function_representation X Y); exact/fun_rep_sur. Defined.

Lemma fun_rep_sing (X Y : cs): (function_representation X Y) \is_singlevalued.
Proof.
move => phi [f [psi ass]] [f' [psi' ass']] rlzr rlzr'.
exact/eq_sub/(mf_rlzr_f_sing rlzr rlzr').
Qed.

Definition cs_fun_modest_set_mixin (X Y: cs):
	dictionary_mixin.type (interview.Pack (cs_fun_assembly_mixin X Y)).
Proof. split; exact/fun_rep_sing. Defined.

Canonical cs_fun X Y := continuity_space.Pack
	((nil, someq Y))
	(inr (somea Y))
  (prod_count
  	(list_count (answers_countable X))
  	(questions_countable Y))
  (sum_count (list_count (questions_countable X)) (answers_countable Y))
	(dictionary.Pack (cs_fun_modest_set_mixin X Y)).
End cs_functions.
Notation "X c-> Y" := (cs_fun X Y) (at level 2).

Section evaluation.
Definition evaluation X Y (fx: (X c-> Y) * X) := (projT1 fx.1) fx.2.
Arguments evaluation {X} {Y}.

Definition eval_rlzr Q Q' A A' :=
  \F_(fun n (psiphi: _ + Q -> _ * A) => M (lprj psiphi) n (rprj psiphi): Q' -> option A'). 
Arguments eval_rlzr {Q} {Q'} {A} {A'}.

Lemma eval_rlzr_val Q A Q' A' (psiphi: (seq A * Q') + Q -> (seq Q + A') * A):
  eval_rlzr psiphi === \F_(M (lprj psiphi)) (rprj psiphi).
Proof. done. Qed.
  
Lemma eval_rlzr_crct X Y:
	eval_rlzr \realizes (F2MF evaluation: X c-> Y \*_cs X ->> Y).
Proof.
rewrite rlzr_F2MF => phi [[f fhcr] x] [/=phinf phinx].
rewrite /function_representation/= in phinf.
split => [| Fphi RphiFphi]; last by apply/rlzr_val_sing; [apply/F2MF_sing | apply phinf | apply phinx | | ].
have [ | Fphi FphiFphi]:= rlzr_dom phinf phinx; first by apply F2MF_tot.
by exists Fphi; apply/eval_rlzr_val.
Qed.

End evaluation.
Arguments eval_rlzr {Q} {Q'} {A} {A'}.
(*
Section associates.

Lemma prod_space_cont (X Y Z: cs) (f: Z c-> X) (g: Z c-> Y):
  exists (F: cs_fun Z (cs_prod X Y)),
    (forall z, (projT1 F z).1 = (projT1 f) z)
    /\
    (forall z, (projT1 F z).2 = (projT1 g) z).
Proof.
set F := fun z => ((projT1 f) **_f (projT1 g)) (z, z).
have Fhcr: (F2MF F: Z ->> cs_prod X Y) \has_continuous_realizer.
- have ->: (F2MF F) =~= (F2MF (projT1 f) ** F2MF (projT1 g)) \o (F2MF (fun z => (z, z))).
    by rewrite -F2MF_fprd comp_F2MF.
  apply/comp_hcr.
  by apply comp_hcr; [apply diag_hcr | apply mfpp_hcr; [apply (projT2 f) | apply (projT2 g) ]].
by exists (exist_c Fhcr).
Qed.

Definition id_fun X := (exist_c (id_hcr X)).

Lemma id_rec_elt X:
	(id_fun X : X c-> X) \is_recursive_element.
Proof.
exists (fun p => match p.1: seq (questions X* answers X) with
		| nil => inl (p.2:questions X)
		| (q,a):: L => inr (a: answers X)
	end).
abstract by pose id_name p := match p.1: seq (questions X* answers X) with
		| nil => inl (p.2:questions X)
		| (q,a):: L => inr (a: answers X)
	end; rewrite /=/is_fun_name/=/rlzr comp_id_l -{1}(comp_id_r (rep X));
	apply /tight_comp_r/ (mon_cmpt_op); [exact: U_mon | move => phi q; exists 1].
Defined.

Definition composition X Y Z (f: X c-> Y) (g: Y c-> Z) :(X c-> Z) :=
	exist_c (comp_hcr_fun (projT2 f) (projT2 g)).

(*
Lemma fcmp_mon_cmpt X Y Z:
	(@composition X Y Z) \is_monotone_computable.
Proof.
Admitted.
*)

Lemma fst_fun_name X Y:
	(fun Lq => match Lq.1  with
		| nil => inl (inl Lq.2)
		| cons a K => inr a.2.1
		end) \is_name_of (exist_c (@fst_hcr X Y)).
Proof.
set psi:= (fun Lq => match Lq.1  with
	| nil => inl (inl Lq.2)
	| cons a K => inr a.2.1
end).
rewrite /=/is_fun_name.
suffices ->: eval (U psi) =~= F2MF (@lprj X Y) by apply frlzr_rlzr => phi x [/=phinx _].
move => phi Fphi.
split => ass; last by rewrite -ass; exists 1.
apply functional_extensionality => q.
have [n val] := ass q.
have U1: U psi 1 phi q = Some (lprj phi q) by trivial.
apply Some_inj.
rewrite -val.
apply esym.
apply/ U_mon; last apply U1.
rewrite /pickle/=.
by case: n val => // n val; lia.
Qed.

Lemma fst_cmpt (X Y: rep_space):
	(exist_c (@fst_hcr X Y): (rep_space_prod X Y) c-> X) \is_recursive_element.
Proof.
exists (fun Lq => match Lq.1  with
	| nil => inl (inl Lq.2)
	| cons a K => inr a.2.1
end).
exact: fst_fun_name.
Defined.

Lemma snd_fun_name X Y:
	(fun Lq => match Lq.1  with
		| nil => inl (inr Lq.2)
		| cons a K => inr a.2.2
		end) \is_name_of (exist_c (@snd_hcr X Y)).
Proof.
set psi:= (fun Lq => match Lq.1  with
	| nil => inl (inr Lq.2)
	| cons a K => inr a.2.2
end).
rewrite /=/is_fun_name.
suffices ->: eval (U psi) =~= F2MF (@rprj X Y) by apply frlzr_rlzr => phi x [_ phiny].
move => phi Fphi.
split => ass; last by rewrite -ass; exists 1.
apply functional_extensionality => q.
have [n val] := ass q.
have U1: U psi 1 phi q = Some (rprj phi q) by trivial.
apply Some_inj.
rewrite -val.
apply esym.
apply/ U_mon; last apply U1.
rewrite /pickle/=.
by case: n val => // n val; lia.
Qed.

Lemma snd_cmpt (X Y: rep_space):
	(exist_c (@snd_hcr X Y) :(rep_space_prod X Y) c-> Y) \is_recursive_element.
Proof.
exists (fun Lq => match Lq.1  with
	| nil => inl (inr Lq.2)
	| cons a K => inr a.2.2
end).
exact: snd_fun_name.
Defined.

(*
Lemma prod_space_cmpt (X Y Z: rep_space) (f: Z c-> X) (g: Z c-> Y):
	f \is_computable_element -> g \is_computable_element ->
	exists (F: Z c-> (rep_space_prod X Y)) (P:	F \is_computable_element),
		((F2MF (@fst X Y)) o (projT1 F) =~= (projT1 f))
		/\
		((F2MF (@snd X Y)) o (projT1 F) =~= (projT1 g)).
Proof.
move => [phi phinf] [psi psing].
have [F Fprop]:= prod_space_cont f g.
exists F; split; last exact: Fprop.
suffices eq: projT1 F =~= (((projT1 f) ** (projT1 g)) o (F2MF (fun z => (z, z)))).
exists (fun Lq => match Lq.2 with
	|inl q' => match phi (Lq.1, q') with
		| inl q'' => inl q''
		| inr a => inr (a, some_answer Y)
	end
	|inr q' => match psi (Lq.1, q') with
		| inl q'' => inl q''
		| inr a => inr (some_answer X, a)
	end
end).
set psiF:=(fun Lq => match Lq.2 with
	|inl q' => match phi (Lq.1, q') with
		| inl q'' => inl q''
		| inr a => inr (a, some_answer Y)
	end
	|inr q' => match psi (Lq.1, q') with
		| inl q'' => inl q''
		| inr a => inr (some_answer X, a)
	end
end).
*)
End COMPUTABLE_ELEMENTS.
*)
