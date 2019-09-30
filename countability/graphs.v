From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype choice seq.
From mf Require Import all_mf.
Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section L2SS.
  Context (T: Type).
  Definition L2SS (L: seq T):= make_subset (fun s => List.In s L).
  
  Local Notation "L '\is_sublist_of' K" := (L2SS L \is_subset_of L2SS K) (at level 2).

  Lemma subl0 (L: seq T): L \is_sublist_of [::] -> L = [::].
  Proof. by elim: L => // t L ih subl; have []:= subl t; left. Qed.

  Lemma drop_subl (L : seq T) n: (drop n L) \is_sublist_of L.
  Proof.
    elim: n => [ | n ih]; first by rewrite drop0.
    rewrite -add1n -drop_drop drop1 => t lstn.
      by apply/ih; case: (drop n L) lstn => //; right.
  Qed.
  
  Lemma lstn_app (L K: seq T)t: List.In t (L ++ K) <-> List.In t L \/ List.In t K.
  Proof.
    split; last by have:= List.in_or_app L K t.
    elim: L => [ | l L ihL /= [eq | lstn]]; [ | left; left | ] => //.
    - by elim: K => // l K ihK /= [eq | lstn]; [right; left | right; right].
        by case: (ihL lstn); [ left; right | right ].
  Qed.

  Lemma L2SS_incl L K: L \is_sublist_of K <-> List.incl L K.
  Proof. done. Qed.

  Lemma L2SS_eq L K:
    (L2SS L) === (L2SS K) <-> L \is_sublist_of K /\ K \is_sublist_of L.
  Proof. exact/set_eq_subs. Qed.

  Lemma L2SS_cat (L K: seq T): L2SS (L ++ K) === ((L2SS L) \u (L2SS K)).
  Proof.
    move => t.
    elim: L => [ | a L ih /=]; first by split; [right | case].
    split => [[ | /ih []] | ]; [left; left | left; right | right | ] => //.
    by rewrite /= in ih; rewrite ih => [[[] | ]]; [left | right; left | right; right ].
  Qed.

  Lemma L2SS_rev K: L2SS K === L2SS (rev K).
  Proof.
    elim: K => // a K ih a' /=; rewrite /rev/=catrevE lstn_app.
    by split => [[-> /= | /ih lstn] | [/ih lstn | []//]]; [right; left | left | right | left].
  Qed.
End L2SS.
Notation "L '\is_sublist_of' K" := (L2SS L \is_subset_of L2SS K) (at level 2).


Section GL2MF.
  Context (T T': Type).
  Implicit Types (KL: seq (T * T')) (phi: T -> T').
  Definition G2MF (G: subset (T * T')):= make_mf (fun s t => (s,t) \from G).

  Lemma G2MF_eq (G G': subset (T * T')): G === G' <-> G2MF G =~= G2MF G'.
  Proof. by split => [eq s t | eq [s t]]; apply/eq. Qed.
  
  Definition GL2MF (KL: seq (T * T')):= G2MF (L2SS KL).

  Definition F2GL phi K := zip K (map phi K).

  Lemma icf_GL2MF phi K: phi \is_choice_for (GL2MF (F2GL phi K)).
  Proof.
    elim: K => [q [] | q L ih q' [a /=[[<-] | lstn]]] //=; first by left.
    by right; apply/ih; exists a.
  Qed.

  Lemma lstn_F2GL phi K q a: (q, a) \from L2SS (F2GL phi K) <-> q \from L2SS K /\ a = phi q.
  Proof.
    split.
    - elim: K => // q' K ih /= [[-> ->] | ]; first by split; first by left.
      by split; first right; apply ih.
    by elim: K => [[] | q' K ih [/=[-> -> | lstn]]]//; [left |right; apply/ih].
  Qed.

  Lemma F2GL_cat phi K K': F2GL phi (K ++ K') = F2GL phi K ++ F2GL phi K'.
  Proof. by rewrite /F2GL map_cat zip_cat // size_map. Qed.
    
  Lemma GL2MF_spec phi K: GL2MF (F2GL phi K) =~= (F2MF phi)|_(L2SS K).
  Proof.
    move => q a; case: K => [ | q' K]; first by rewrite /=; firstorder.
    have /= -> := lstn_F2GL phi K q a.
    by split => // [[[<- <-] | ] | [[-> -> | lstn ->]]]; firstorder.
  Qed.
  End GL2MF.

  Section agree_on.
  Context (Q A : Type).
  (* Q is for questions, A is for answers*)
  Local Notation B := (Q -> A).
  (* The topology on Baire space is the topology of pointwise convergence the following are
     the basic open ets (in the sens that for each finite list L and each element phi of Baire
     space the set {psi | coin phi psi L} is a basic open set *)

  Definition agree_on P (phi psi: B):= forall q, q \from P -> phi q = psi q.

  Lemma agre_ref L: Reflexive (agree_on L).
  Proof. done. Qed.
  
  Lemma agre_sym L: Symmetric (agree_on L).
  Proof. by move => phi psi coin q Lq; rewrite coin. Qed.
  
  Lemma agre_trans L: Transitive (agree_on L).
  Proof. by move => phi psi psi' coin coin' q Lq; rewrite coin // coin'. Qed.

  Global Instance agre_equiv L: Equivalence (agree_on L).
  Proof. by split; [apply agre_ref | apply agre_sym | apply agre_trans]. Qed.

  Notation "phi '\agrees_with' psi '\on' P" := (agree_on P phi psi) (at level 2).

  Global Instance agre_prpr:
    Proper (@set_equiv Q ==> @eqfun A Q ==> @eqfun A Q ==> iff) agree_on.
  Proof.
    move => P P' Peq phi phi' phieq psi psi' psieq.
    split => agre q /Peq Pq; first by rewrite -phieq -psieq; apply /agre.
    by rewrite phieq psieq; apply/agre.
  Qed.

  Lemma agre_union (P P': subset _) phi psi: phi \agrees_with psi \on (P \u P') <->
        phi \agrees_with psi \on P /\ phi \agrees_with psi \on P'.
  Proof.
    split => [agre | [agre agre'] q [Pq | P'q]]; [ | apply agre | apply agre'] => //.
    by split => q Pq; apply/agre; [left | right].
  Qed.
  
  Lemma agre_spec P phi psi:
    phi \agrees_with psi \on P <-> (F2MF phi)|_P =~= (F2MF psi)|_P.
  Proof.
    split => [coin s t | eq q Pq]; last by have []:= (eq q (phi q)).1.
    by split; case => Ps <-; [rewrite coin | rewrite -coin].
  Qed.

  Lemma agre_subs phi psi P P':
    P \is_subset_of P' -> phi \agrees_with psi \on P' -> phi \agrees_with psi \on P.
  Proof. by move => subs agre q /subs Pq; apply/agre. Qed.
End agree_on.
Notation "phi '\agrees_with' psi '\on' P" :=
  (agree_on (P: subset _) phi psi) (at level 2): mf_scope.
