From mathcomp Require Import ssreflect ssrfun seq.
From rlzrs Require Import all_rlzrs choice_dict.
Require Import axioms all_names cs prod sub facts nvrsl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope cs_scope.
Section cs_functions.
  Context (U: continuous_universal) (X Y: cs).
  Local Notation F_U := (@F_M U).
  
  Definition associate := make_mf (fun psi (f: X -> Y) => (F_U psi) \realizes (F2MF f)).

  Local Notation "X c-> Y" := (codom associate) (at level 2).

  Definition function_representation := make_mf (fun psi (f: X c-> Y) =>
                                                        associate psi (projT1 f)).

  Lemma fun_rep_sur: function_representation \is_cototal.
  Proof. by move => [f [psi ass]]/=; exists psi. Qed.

  Lemma fun_rep_sing: function_representation \is_singlevalued.
  Proof.
    move => phi [f [psi ass]] [f' [psi' ass']] rlzr rlzr'.
    exact/eq_sub/(mf_rlzr_f_sing rlzr rlzr').
  Qed.

  Canonical cs_fun: cs.
    exists {x | x \from X c-> Y} (function_names U B B) function_representation.
    by split; [apply/fun_rep_sur | apply/fun_rep_sing].
  Defined.

  Definition evaluation (fx: cs_prod cs_fun X) := (projT1 fx.1) fx.2.
  
  Definition eval_rlzr:=
    make_mf (fun psiphi => F_U (lprj psiphi: function_names U (names X) (names Y)) (rprj psiphi)).
  
  Lemma eval_rlzr_val psiphi:
    eval_rlzr psiphi === F_U (lprj psiphi) (rprj psiphi).
  Proof. done. Qed.
  
  Lemma eval_rlzr_crct: eval_rlzr \realizes (F2MF evaluation).
  Proof.
    rewrite rlzr_F2MF => phi [[f fhcr] x] [/=phinf phinx].
    rewrite /function_representation/= in phinf.
    split => [| Fphi RphiFphi]; last by apply/rlzr_val_sing; [apply/F2MF_sing | apply phinf | apply phinx | | ].
    have [ | Fphi FphiFphi]:= ntrvw.rlzr_dom phinf phinx; first by apply F2MF_tot.
    by exists Fphi; apply/eval_rlzr_val.
  Qed.
End cs_functions.
Notation "X c-> Y" := (cs_fun F_U X Y) (at level 2): cs_scope.

Section associates.
  Definition id_ass X Lq := match Lq.1: seq (answers X) with
		            | nil => inl ([::Lq.2:queries X])
		            | a:: L => inr (a: answers X)
	                    end.

  Lemma id_ass_eval (X: cs): \F_(U (@id_ass X)) =~= mf_id.
  Proof.
    apply/eval_F2MF/mon_eval; first exact/U_mon; first exact/F2MF_sing.
    by move => phi _ <- q'; exists 2; rewrite /U/=.
  Qed.
  
  Lemma id_ass_spec X: associate F_U X X (@id_ass X) id.
  Proof. exact/ntrvw.tight_rlzr/eval_F2MF/id_ass_eval/id_rlzr. Qed.
  
  Definition fst_ass X Y (Lq: seq (answers (cs_prod X Y)) * (queries X)) :=
    match Lq.1 with
    | nil => inl [::inl Lq.2 : _ + (queries Y)]
    | cons a K => inr a.1: (_ + answers X) 
    end.

  Lemma fst_ass_eval (X Y: cs): \F_(U (@fst_ass X Y)) =~= (fst_rlzr X Y).
  Proof.
    apply/eval_F2MF/mon_eval; first exact/U_mon; first exact/F2MF_sing.
    by move => phi _ <- q'; exists 2; rewrite /U /=.
  Qed.
  
  Lemma fst_ass_spec X Y: associate F_U _ X (@fst_ass X Y) fst.
  Proof. exact/ntrvw.tight_rlzr/eval_F2MF/fst_ass_eval/fst_rlzr_spec. Qed.
  
  Definition snd_ass X Y (Lq: seq (answers (cs_prod X Y)) * (queries Y)) :=
    match Lq.1 with
    | nil => inl [::inr Lq.2 : (queries X) + _]
    | cons a K => inr a.2: (_ + answers Y) 
    end.
  
  Lemma snd_ass_eval (X Y: cs): \F_(U (@snd_ass X Y)) =~= (snd_rlzr X Y).
  Proof.
    apply/eval_F2MF/mon_eval; first exact/U_mon; first exact/F2MF_sing.
    by move => phi _ <- q'; exists 2; rewrite /U /=.
  Qed.
  
  Lemma snd_ass_spec X Y: associate F_U _ Y (@snd_ass X Y) snd.
  Proof. exact/ntrvw.tight_rlzr/eval_F2MF/snd_ass_eval/snd_rlzr_spec. Qed.
End associates.

