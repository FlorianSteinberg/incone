From mathcomp Require Import ssreflect ssrfun seq.
From rlzrs Require Import all_rlzrs choice_dict.
Require Import all_core cs prod sub facts Duop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope cs_scope.
Section cs_functions.
  Context (X Y: cs).
  Definition associate := make_mf (fun psi (f: X -> Y) =>
    (\F_(U psi): questions X ->> questions Y) \realizes (F2MF f)).

  Notation "X c-> Y" := (codom associate) (at level 2).

  Definition function_representation := make_mf (fun psi (f: X c-> Y) =>
                                                        associate psi (projT1 f)).

  Lemma fun_rep_sur: function_representation \is_cototal.
  Proof. by move => [f [psi ass]]/=; exists psi. Qed.

  Lemma fun_rep_sing: function_representation \is_singlevalued.
  Proof.
    move => phi [f [psi ass]] [f' [psi' ass']] rlzr rlzr'.
    exact/eq_sub/(mf_rlzr_f_sing rlzr rlzr').
  Qed.

  Canonical cs_fun_class:= @continuity_space.Class _ _ _
    (interview.Mixin fun_rep_sur) (dictionary.Mixin fun_rep_sing) 
    (continuity_space.Mixin 
	((nil, someq Y)) (inr (somea Y))
        (prod_count (list_count (A_count X)) (Q_count Y))
        (sum_count (list_count (Q_count X)) (A_count Y))).
  Canonical cs_fun := continuity_space.Pack cs_fun_class.
End cs_functions.
Notation "X c-> Y" := (cs_fun X Y) (at level 2): cs_scope.

Section evaluation.
  Definition evaluation X Y (fx: (X c-> Y) \*_cs X) := (projT1 fx.1) fx.2.
  Arguments evaluation {X} {Y}.
  
  Definition eval_rlzr Q Q' A A' :=
    \F_(fun n (psiphi: _ + Q -> _ * A) => U (lprj psiphi) n (rprj psiphi): Q' -> option A'). 
  Arguments eval_rlzr {Q} {Q'} {A} {A'}.
  
  Lemma eval_rlzr_val Q A Q' A' (psiphi: (seq A * Q') + Q -> (seq Q + A') * A):
  eval_rlzr psiphi === \F_(U (lprj psiphi)) (rprj psiphi).
  Proof. done. Qed.
  
  Lemma eval_rlzr_crct X Y:
    (eval_rlzr: questions (X c-> Y \*_cs X) ->> questions Y) \realizes (F2MF evaluation).
  Proof.
    rewrite rlzr_F2MF => phi [[f fhcr] x] [/=phinf phinx].
    rewrite /function_representation/= in phinf.
    split => [| Fphi RphiFphi]; last by apply/rlzr_val_sing; [apply/F2MF_sing | apply phinf | apply phinx | | ].
    have [ | Fphi FphiFphi]:= rlzr_dom phinf phinx; first by apply F2MF_tot.
    by exists Fphi; apply/eval_rlzr_val.
  Qed.
End evaluation.
Arguments eval_rlzr {Q} {Q'} {A} {A'}.

Section associates.
  Definition id_ass X Lq := match Lq.1: seq (answers X) with
		            | nil => inl ([::Lq.2:queries X])
		            | a:: L => inr (a: answers X)
	                    end.
  
  Lemma id_ass_eval (X: cs): (U (@id_ass X)) \evaluates_to mf_id.
  Proof.
    apply/mon_eval; first exact/U_mon; first exact/F2MF_sing.
    by move => phi _ <- q'; exists 2; rewrite /U/=.
  Qed.
  
  Lemma id_ass_spec X: associate X X (@id_ass X) id.
  Proof. exact/ntrvw.tight_rlzr/id_ass_eval/id_rlzr. Qed.
  
  Definition fst_ass X Y (Lq: seq (answers (X \*_cs Y)) * (queries X)) :=
    match Lq.1 with
    | nil => inl [::inl Lq.2 : _ + (queries Y)]
    | cons a K => inr a.1: (_ + answers X) 
    end.

  Lemma fst_ass_eval (X Y: cs): (U (@fst_ass X Y)) \evaluates_to (fst_rlzr X Y).
  Proof.
    apply/mon_eval; first exact/U_mon; first exact/F2MF_sing.
      by move => phi _ <- q'; exists 2; rewrite /U /=.
  Qed.
  
  Lemma fst_ass_spec X Y: associate (X \*_cs Y) X (@fst_ass X Y) fst.
  Proof. exact/ntrvw.tight_rlzr/fst_ass_eval/fst_rlzr_spec. Qed.
  
  Definition snd_ass X Y (Lq: seq (answers (X \*_cs Y)) * (queries Y)) :=
    match Lq.1 with
    | nil => inl [::inr Lq.2 : (queries X) + _]
    | cons a K => inr a.2: (_ + answers Y) 
    end.
  
  Lemma snd_ass_eval (X Y: cs): (U (@snd_ass X Y)) \evaluates_to (snd_rlzr X Y).
  Proof.
    apply/mon_eval; first exact/U_mon; first exact/F2MF_sing.
      by move => phi _ <- q'; exists 2; rewrite /U /=.
  Qed.
  
  Lemma snd_ass_spec X Y: associate (X \*_cs Y) Y (@snd_ass X Y) snd.
  Proof. exact/ntrvw.tight_rlzr/snd_ass_eval/snd_rlzr_spec. Qed.
End associates.

