From mathcomp Require Import ssreflect ssrfun seq.
From rlzrs Require Import all_rlzrs choice_dict.
Require Import axioms all_names cs prod sub.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope cs_scope.
Section cs_functions.
  Context (X Y: cs).

  Definition function_names (B B': naming_space): naming_space.
    exists (seq (questions B * answers B) * (questions B'))%type (seq (questions B) + answers B')%type.
    apply/(nil, someq).
    apply/prod_count/naming_spaces.Q_count/list_count/prod_count/naming_spaces.A_count/naming_spaces.Q_count.
    exact/sum_count/naming_spaces.A_count/list_count/naming_spaces.Q_count.
  Defined.

  Definition associate := make_mf (fun psi (f: X -> Y) => \F_(U psi) \realizes f).

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
    exists {x | x \from X c-> Y} (function_names B_ _ B_ _) function_representation.
    by split; [apply/fun_rep_sur | apply/fun_rep_sing].
  Defined.

  Definition evaluation (fx: cs_prod cs_fun X) := (projT1 fx.1) fx.2.  

  Local Open Scope name_scope.
  Definition eval_rlzrM (psiphi: function_names B_(X) B_(Y) \*_ns B_(X)) :=
    U (lprj psiphi) (rprj psiphi).

  Lemma map_lstn T T' (K: seq T) (f: T -> T') q:
    q \from L2SS K -> f q \from L2SS (map f K).
  Proof. by elim: K => // q' K' ih /=[<- | /ih]; [left | right]. Qed.
    
  Lemma map_subl T T' (K K': seq T) (f: T -> T'):
    K \is_sublist_of K' -> (map f K) \is_sublist_of (map f K').
  Proof.
    elim: K K' => [K' _ q | q K ih K' subl q' /=[<- | lstn]]//; first by apply/map_lstn/subl; left.
    by apply/ih/lstn => ? ?; apply/subl; right.
  Qed.
  
  Lemma eval_rlzrM_cntf: eval_rlzrM \is_continuous_functional.
  Proof.
    move => psiphi.
    exists (fun nq' =>
              map inr (gather_queries (lprj psiphi) (rprj psiphi) nq')
                  ++ map inl (gather_queries (D (rprj psiphi)) (lprj psiphi) nq')
           ); case => n q' psiphi'.
    elim: n => // n.
    rewrite /eval_rlzrM => ih /coin_cat [coin coin'].
    rewrite /eval_rlzrM US [RHS]US ih; last first.
    - apply/coin_cat; split; first exact/coin_subl/coin/map_subl/gq_mon.
      exact/coin_subl/coin'/map_subl/gq_mon.
    case: U => //.
  Admitted.
  Local Close Scope name_scope.

  Definition eval_rlzr:= get_partial_function eval_rlzrM.

  Lemma eval_rlzr_cntop: eval_rlzr \is_continuous_operator.
  Proof. exact/gtpf_cntf_cont/eval_rlzrM_cntf. Qed.
    
  Lemma eval_rlzr_val psiphi:
    PF2MF eval_rlzr psiphi === \F_(U (lprj psiphi)) (rprj psiphi).
  Proof.
    rewrite gtpf_spec -FMop.sing_sfrst //.    
    by apply/FMop.mon_sing => psiphi'; have mon := @U_mon _ _ _ _ (lprj psiphi'); apply/mon.
  Qed.
  
  Lemma eval_rlzr_crct: eval_rlzr \realizes evaluation.
  Proof.
    rewrite rlzr_F2MF => phi [[f fhcr] x] [[_ [<-  [phinf phinx]]]].
    rewrite /function_representation/= in phinf.
    split => [ | Fphi RphiFphi]; last first.
    - by apply/rlzr_val_sing; [apply/F2MF_sing | | apply/phinx | | apply/eval_rlzr_val ].
    have [ | Fphi FphiFphi]:= ntrvw.rlzr_dom phinf phinx; first by apply F2MF_tot.
    by exists Fphi; apply/eval_rlzr_val.
  Qed.
End cs_functions.
Notation "X c-> Y" := (cs_fun X Y) (at level 2): cs_scope.

Section associates.
  Definition id_ass X KLq := match KLq.1: seq (queries X * replies X) with
		            | nil => inl ([::KLq.2:queries X])
		            | qa:: L => inr (qa.2: replies X)
	                    end.

  Lemma id_ass_eval (X: cs): \F_(U (@id_ass X)) =~= mf_id.
  Proof.
    apply/eval_F2MF/mon_eval; first exact/U_mon; first exact/F2MF_sing.
    by move => phi _ <- q'; exists 2; rewrite /U/=.
  Qed.
  
  Lemma id_ass_spec X: associate X X (@id_ass X) id.
  Proof. exact/ntrvw.tight_rlzr/eval_F2MF/id_ass_eval/id_rlzr. Qed.
  
  Definition fst_ass X Y
             (KLq: seq (queries (cs_prod X Y ) * replies (cs_prod X Y)) * (queries X)) :=
    match KLq.1 with
    | nil => inl [::inl KLq.2 : _ + (queries Y)]
    | cons qa K => inr qa.2.1: (_ + replies X) 
    end.

  Lemma fst_ass_eval (X Y: cs): \F_(U (@fst_ass X Y)) =~= (fst_rlzr X Y).
  Proof.
    apply/eval_F2MF/mon_eval; first exact/U_mon; first exact/F2MF_sing.
    by move => phi _ <- q'; exists 2; rewrite /U /=.
  Qed.
  
  Lemma fst_ass_spec X Y: associate _ X (@fst_ass X Y) fst.
  Proof. exact/ntrvw.tight_rlzr/eval_F2MF/fst_ass_eval/fst_rlzr_spec. Qed.
  
  Definition snd_ass X Y
             (KLq: seq (queries (cs_prod X Y) * replies (cs_prod X Y)) * (queries Y)) :=
    match KLq.1 with
    | nil => inl [::inr KLq.2 : (queries X) + _]
    | cons qa K => inr qa.2.2: (_ + replies Y) 
    end.
  
  Lemma snd_ass_eval (X Y: cs): \F_(U (@snd_ass X Y)) =~= (snd_rlzr X Y).
  Proof.
    apply/eval_F2MF/mon_eval; first exact/U_mon; first exact/F2MF_sing.
    by move => phi _ <- q'; exists 2; rewrite /U /=.
  Qed.
  
  Lemma snd_ass_spec X Y: associate _ Y (@snd_ass X Y) snd.
  Proof. exact/ntrvw.tight_rlzr/eval_F2MF/snd_ass_eval/snd_rlzr_spec. Qed.
End associates.
