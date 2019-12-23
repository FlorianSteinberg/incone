From mathcomp Require Import ssreflect ssrfun seq.
From rlzrs Require Import all_rlzrs choice_dict.
Require Import axioms all_names representations cs prod sub.
Require Import continuous_machines.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope cs_scope.
Section function_representation.
  Context X X' (delta: representation_of X) (delta': representation_of X').

  Definition function_names (B B': naming_space): naming_space.
    exists (seq (questions B * answers B) * (questions B'))%type (answers B' + seq (questions B))%type.
    apply/(nil, someq).
    apply/prod_count/naming_spaces.Q_count/list_count/prod_count/naming_spaces.A_count/naming_spaces.Q_count.
    exact/sum_count/list_count/naming_spaces.Q_count/naming_spaces.A_count.
  Defined.

  Definition associate := make_mf (fun psi (f: X -> X') => (F2MF f) \realized_by \F_(U psi) \wrt delta \and delta').

  Local Notation "X c-> X'" := (codom associate) (at level 2).

  Local Notation rep_fun := (make_mf (fun (psi:function_names _ _) (f: X c-> X') => associate psi (projT1 f))).

  Lemma fun_rep_sur: rep_fun \is_cototal.
  Proof. by move => [f [psi ass]]/=; exists psi. Qed.

  Lemma fun_rep_sing: rep_fun \is_singlevalued.
  Proof.
    move => phi [f [psi ass]] [f' [psi' ass']] rlzr rlzr'.
    exact/eq_sub/(mf_rlzr_f_sing (D := delta') (I:= delta) rlzr).
  Qed.

  Definition function_representation : representation_of (X c-> X').
    exists (function_names (name_space delta) (name_space delta')).
    exists rep_fun; try apply/fun_rep_sing; try apply/fun_rep_sur.
  Defined.
End function_representation.

Section function_space.
  Context (X Y: cs).
  Canonical function_space:= repf2cs (function_representation (delta_ X) (delta_ Y)).

  Definition evaluation (fx: function_space \*_cs X) := (projT1 fx.1) fx.2.  

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

  Lemma lprj_coin_inl (B B': naming_space) (psiphi psiphi': B \*_ns B') K:
    psiphi \coincides_with psiphi' \on (map inl K) ->
    (lprj psiphi) \coincides_with (lprj psiphi') \on K.
  Proof.
    by elim: K => // q K ih; rewrite map_cons /lprj /=; case => <- coin; split; last exact/ih.
  Qed.

  Lemma rprj_coin_inr (B B': naming_space) (psiphi psiphi': B \*_ns B') K:
    psiphi \coincides_with psiphi' \on (map inr K) ->
    (rprj psiphi) \coincides_with (rprj psiphi') \on K.
  Proof.
    by elim: K => // q K ih; rewrite map_cons /rprj /=; case => <- coin; split; last exact/ih.
  Qed.

  Lemma eval_rlzrM_cntf: eval_rlzrM \is_continuous_functional.
  Proof.
    move => psiphi.
    exists (fun nq' =>
              map inr (gather_queries (lprj psiphi) (rprj psiphi) nq')
                  ++ map inl (traces (rprj psiphi) (lprj psiphi) nq')
           ); case => n q' psiphi' /coin_cat [/rprj_coin_inr coin /lprj_coin_inl coin'].
    rewrite /eval_rlzrM.
    rewrite (trcs_modf_U coin').
    move: coin.
    rewrite (trcs_modf_gq coin') => coin.
    exact/gq_modf_U.
  Qed.
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
    move => phi [[f fhcr] x] [[? ?] [[<- <-] [phinf phinx]]].
    rewrite /function_representation/= in phinf.
    split => [ | Fphi RphiFphi]; last first.
    - by exists (f x); split; last apply/rlzr_val/eval_rlzr_val/RphiFphi.
    have [ | Fphi FphiFphi]:= ntrvw.rlzr_dom phinf phinx; first by apply F2MF_tot.
    by exists Fphi; apply/eval_rlzr_val.
  Qed.
End function_space.
Notation "X c-> Y" := (function_space X Y) (at level 2): cs_scope.

From mathcomp Require Import eqtype ssrbool ssrnat.
Require Import FMop construct_associate.
Section construct_function_names.
  Context (X Y: cs).
  Context (somea: replies X).
  
  Local Open Scope name_scope.
  Arguments continuous_machine (fuel) {Q} {A} {Q'} {A'}.
  Definition continuous_solution fuel (F: X ->> Y) (M: continuous_machine fuel):= \F_M \solves F.

  Definition implements fuel (f: X -> Y) (M: continuous_machine fuel):= \F_M \realizes f.

  Lemma F2MF_mplmnt fuel f (M: continuous_machine fuel):
    continuous_solution (F2MF f) M <-> implements f M.
  Proof. done. Qed.
  
  Hypothesis (eq_dec: forall (q q': queries X), decidable (q = q')).
  
  Definition EQ: eqType.
    exists (queries X).
    exists (fun q q' => match eq_dec q q' with
                | left _ => true
                | right _ => false
                end).
    by move => q q'; apply/(iffP idP); case: eq_dec.
  Defined.

  Definition construct_associate M
             (KLq': seq (queries X * replies X) * queries Y): replies Y + seq (queries X):=
    psi_FM somea (someq: EQ) (modulus M) M KLq'.

  Lemma cass_spec (f: X -> Y) M:
    implements f M -> associate X Y (construct_associate M) f.
  Proof.
    move => rlzr.
    apply/tight_slvs/(psi_FM_spec somea (someq: EQ))/countable_choice/Q_count => //.
    exact/modmod.
    exact/mod.
  Qed.
    
  Definition id_ass X KLq := match KLq.1: seq (queries X * replies X) with
		            | nil => inr ([::KLq.2:queries X])
		            | qa:: L => inl (qa.2: replies X)
	                    end.

  Lemma id_ass_eval: \F_(U (@id_ass X)) =~= mf_id.
  Proof.
    apply/eval_F2MF/mon_eval; first exact/U_mon; first exact/F2MF_sing.
    by move => phi _ <- q'; exists 2; rewrite /U/=.
  Qed.
  
  Lemma id_ass_spec: associate (delta_ X) (delta_ X) (@id_ass X) id.
  Proof. exact/ntrvw.tight_rlzr/eval_F2MF/id_ass_eval/id_rlzr. Qed.
  
  Definition fst_ass (KLq: seq (queries (cs_prod X Y ) * replies (cs_prod X Y)) * (queries X)) :=
    match KLq.1 with
    | nil => inr [::inl KLq.2 : _ + (queries Y)]
    | cons qa K => inl qa.2.1: (replies X + _) 
    end.

  Lemma fst_ass_eval: \F_(U fst_ass) =~= (fst_rlzr X Y).
  Proof.
    apply/eval_F2MF/mon_eval; first exact/U_mon; first exact/F2MF_sing.
    by move => phi _ <- q'; exists 2; rewrite /U /=.
  Qed.
  
  Lemma fst_ass_spec: associate _ X fst_ass fst.
  Proof. exact/ntrvw.tight_rlzr/eval_F2MF/fst_ass_eval/fst_rlzr_spec. Qed.

  Definition cs_fst: (X \*_cs Y) c-> X.
    exists fst; exists fst_ass; exact/fst_ass_spec.
  Defined.
  
  Definition snd_ass
             (KLq: seq (queries (cs_prod X Y) * replies (cs_prod X Y)) * (queries Y)) :=
    match KLq.1 with
    | nil => inr [::inr KLq.2 : (queries X) + _]
    | cons qa K => inl qa.2.2: (replies Y + _) 
    end.
  
  Lemma snd_ass_eval: \F_(U snd_ass) =~= (snd_rlzr X Y).
  Proof.
    apply/eval_F2MF/mon_eval; first exact/U_mon; first exact/F2MF_sing.
    by move => phi _ <- q'; exists 2; rewrite /U /=.
  Qed.
  
  Lemma snd_ass_spec: associate _ Y snd_ass snd.
  Proof. exact/ntrvw.tight_rlzr/eval_F2MF/snd_ass_eval/snd_rlzr_spec. Qed.

  Definition cs_snd: (X \*_cs Y) c-> Y.
    exists snd; exists snd_ass; exact/snd_ass_spec.
  Defined.
End construct_function_names.
