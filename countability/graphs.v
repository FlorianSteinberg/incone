(** 
    This file introduces some data structures that are used throughout the
    Development, provides translations and basic Lemmas. I attempted to choose
    somewhat consistent shorthands. Here is a short overview over the abbrevi-
    ations. Most of them are about multifunctions of type Q ->> A where Q and
    A are arbitrary input and output types (Q is for questions, A for answers):
    - L : a finite list of elements from a type.
    - SS: subset, i.e. function from type to Prop. For instance any list
          can be considered a code for the set of its elements and this
          assignment is realized through L2SS (list (L) to (2) subset (SS)).
    - G : a subset of (Q * A) considered the graph of a multifunction.
    - GL: graph list, some KL: seq (Q * A) that should be thought of as the
          finite multifunction GL2MF KL (q) := {a | (q, a) \from KL}.
    - LF: list function, some Lf: Q -> seq A, can be considered a multi-
          function with finite value set via LF2MF Lf (q) := L2SS (Lf q).
    The "extend" function translates a list function to a function by always
    choosing the first element in the list. It needs a default value.
    We also introduce notions for relativizing functional equality to subsets,
    i.e. phi \agrees_with psi \on A <~> forall q \from A, phi q = psi q. For
    phi \coincides_with psi \on K <-> phi \agrees_with psi \on (L2SS K) we
    provide a more direct inductive definition.
**)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype choice seq.
From mf Require Import all_mf.
Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section lists_and_subsets.
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

  Lemma cons_subs t (L: seq T) P:
    L2SS (t :: L) \is_subset_of P <-> t \from P /\ L2SS L \is_subset_of P.
  Proof.
    split => [subs | [Pa subs] q /=[<- | ]]//; last by apply/subs.
    by split => [ | q lstn]; apply/subs; [left | right].
  Qed.
End lists_and_subsets.
Notation "L '\is_sublist_of' K" := (L2SS L \is_subset_of L2SS K) (at level 2).
Coercion L2SS: seq >-> subset.

Lemma L2SS_flatten T (Ln: seq (seq T)) t:
  t \from L2SS (flatten Ln) <-> exists L, t \from L2SS L /\ L \from L2SS Ln.
Proof.
  split.
  - elim: Ln => [| L Ln ih /=]// /lstn_app [lstn | lstn]; first by exists L; split => //; left.
    by have [K []] := ih lstn; exists K; split => //; right.
  elim: Ln => [[L []] | L Ln ih [K [lstn /=[-> | lstn']]]]//; apply/lstn_app; first by left.
  by right; apply/ih; exists K.
Qed.

Lemma flatten_subl T (Ln Kn: seq (seq T)):
  Ln \is_sublist_of Kn -> (flatten Ln) \is_sublist_of (flatten Kn).
Proof.
  move => subl t /L2SS_flatten [L [lstn lstn']].
  by rewrite L2SS_flatten; exists L; split; last apply subl.
Qed.

Section auxiliary_lemmas.
  Lemma zip_nill S T (L: seq T): zip ([::]:seq S) L = nil.
  Proof. by case: L. Qed.

  Lemma zip_nilr S T (K: seq S): zip K ([::]:seq T) = nil.
  Proof. by case: K. Qed.

  Lemma inP (T: eqType) q (L: seq T): reflect (q \from L2SS L) (q \in L).
  Proof.
    elim: L => [ | t L ih]; [exact/ReflectF | rewrite in_cons].
      by apply/(iffP idP) => [/orP [/eqP -> | /ih ]| /= [-> |/ih lstn]];
                               try apply/orP; [left | right | left | right ].
  Qed.
  
  Fixpoint check_sublist (Q: eqType) (K L: seq Q):=
    match K with
    | nil => true
    | q :: K' => (q \in L) && check_sublist K' L
    end.

  Lemma clP (Q: eqType) (K K': seq Q): reflect (K \is_sublist_of K') (check_sublist K K').
  Proof.
    apply/(iffP idP).
    elim: K => [_ q | q K ih ]//= /andP [lstn cl].
    by apply/cons_subs; split; [exact/inP | apply/ih].
    elim: K => // q K ih /cons_subs [lstn subl] /=.
    by apply/andP; split; [exact/inP | apply/ih].
  Qed.
End auxiliary_lemmas.

Section lists_and_multifunctions.
  Context (Q A: Type).
  Implicit Types (G: subset (Q * A)) (KL: seq (Q * A)) (phi: Q -> A).

  Definition G2MF G:= make_mf (fun q a => (q, a) \from G).

  Lemma G2MF_eq G G': G === G' <-> G2MF G =~= G2MF G'.
  Proof. by split => [eq s t | eq [s t]]; apply/eq. Qed.
  
  Definition GL2MF KL:= G2MF (L2SS KL).

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

  Lemma GL2MF_dom KL: dom (GL2MF KL) === L2SS (unzip1 KL).
  Proof.
    elim: KL => [ | [q a] KL ih q']; first by split => //; case.
    split => [[a' /=[[<- _] | lstn]] | ]; [left | right; apply/ih; exists a' | ] => //.
    move => /=[-> | /ih [a' val]]; first by exists a; left.
    by exists a'; right.
  Qed.
  
  Fixpoint GL2LF (T: eqType) T' (KL: seq (T * T')) q:=
    match KL with
    | nil => nil
    | qa :: KL' => if qa.1 == q
                   then qa.2 :: GL2LF KL' q
                   else GL2LF KL' q
    end.

  Definition LF2MF (Lf: Q -> seq A):= make_mf (fun s => L2SS (Lf s)).

  Definition LF2pf (Lf: Q -> seq A) q:= head None (map Some (Lf q)).
  
  Lemma LF2pf_spec Lf: (LF2pf Lf) \is_partial_choice_for (LF2MF Lf).
  Proof. by rewrite /LF2pf => q a /=; case: (Lf q) => // a'; exists a'; split; last left. Qed.
  
  Context (default: A).
  Definition LF2F (Lf: Q -> seq A) q := head default (Lf q).
  
  Lemma LF2F_spec Lf: (LF2F Lf) \is_choice_for (LF2MF Lf).
  Proof.
    rewrite /LF2F => q [a /=].
    by case: (Lf q) => // q' K /= [-> | ]; left.
  Qed.
End lists_and_multifunctions.

Lemma GL2LF_spec (T: eqType) T' (KL: (seq (T * T'))): LF2MF (GL2LF KL) =~= GL2MF KL.
Proof.    
  rewrite /GL2MF.
  elim: KL => // [[t t'] KL] ih t'' t''' /=.
  case: ifP => [/eqP eq | neq].
  - split; first by case => [-> | ]; [left; rewrite eq | right; apply/ih].
    by case => [[<- <-] | ]; [left | right; apply/ih].
  split; first by right; apply/ih.
  by case => [[/eqP] | lstn]; [rewrite neq | apply/ih].
Qed.

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

Section coincide.
  Context (Q A: Type).
  Local Notation B := (Q -> A).

  Fixpoint coincide L (phi psi: B) :=
    match L with
    | nil => True
    | cons s K => (phi s = psi s) /\ (coincide K phi psi)
    end.
  Local Notation "phi \coincides_with psi \on L" := (coincide L phi psi) (at level 20).

  Lemma coin_agre L (phi psi: B) :
    phi \coincides_with psi \on L <-> phi \agrees_with psi \on (L2SS L).
  Proof.
    elim: L => [ | q L ih /=]; first by split => // _ q.
    split => [[eq /ih agre] s [<- | lstn] // | agre]; first exact/agre.
    split; first by apply/agre; left.
    by apply/ih => s lstn; apply/agre; right.
  Qed.

  Lemma coin_L2SS (phi psi: B) (L: seq Q):
    phi \coincides_with psi \on L <-> (forall q, q \from L2SS L -> phi q = psi q).
  Proof. exact/coin_agre. Qed.

  Lemma coin_cat (phi psi: B) L K: phi \coincides_with psi \on (L ++ K)
                <-> (phi \coincides_with psi \on L /\ phi \coincides_with psi \on K).
  Proof.
    rewrite !coin_agre; have ->:= agre_prpr (L2SS_cat L K); try exact/frefl.    
    exact/agre_union.
  Qed.

  Lemma coin_subl phi psi L K:
    L \is_sublist_of K -> phi \coincides_with psi \on K -> phi \coincides_with psi \on L.
  Proof. by rewrite !coin_agre => subl agre q lstn; apply/agre/subl. Qed.

  Lemma coin_spec L (phi psi: B):
    phi \coincides_with psi \on L <-> (F2MF phi)|_(L2SS L) =~= (F2MF psi)|_(L2SS L).
  Proof. by rewrite -agre_spec; exact/coin_agre. Qed.

  Lemma coin_ref L: Reflexive (coincide L).
  Proof. by elim: L. Qed.

  Lemma coin_sym L: Symmetric (coincide L).
  Proof. by move => phi psi /coin_agre agre; apply/coin_agre/agre_sym. Qed.

  Lemma coin_trans L: Transitive (coincide L).
  Proof.
    move => phi psi psi' /coin_agre agre /coin_agre agre'.
    exact/coin_agre/agre_trans/agre'.
  Qed.

  Global Instance coin_equiv L: Equivalence (coincide L).
  Proof. by split; [apply coin_ref | apply coin_sym | apply coin_trans]. Qed.

  Lemma coin_map (phi phi': B) K:
    phi \coincides_with phi' \on K -> map phi K = map phi' K.
  Proof. by elim: K => // q K ih /=[-> coin]; rewrite ih. Qed.

  Lemma coin_GL2MF phi psi K:
    phi \coincides_with psi \on K <-> phi \is_choice_for (GL2MF (F2GL psi K)).
  Proof.
    elim: K => [ | q L ih /=]; first by split => // _ q [] a.
    split => [[eq /ih coin] q' [a /=[[<- _] | lstn]] | icf]; first by left; rewrite eq.
    -  by right; apply/coin; exists a.
    split; first by have/=[|[]|]//:=icf q; [exists (psi q);left|elim: (L) =>//q' L' ih' /=[[<-]|]].
    apply/ih => q' [a val].
    have /=[ | [-> <-] | ] //:= icf q'; first by exists a; right.
    move: val; elim: (L) => //q'' L' ih' /=[[->] | lstn]; first by left.
    by right; apply/ih'.
  Qed.    

  Lemma coin_F2GL phi psi K:
    phi \coincides_with psi \on K <-> F2GL phi K = F2GL psi K.
  Proof. by elim: K => // q K ih /=; rewrite ih /F2GL /=; split => [[-> ->] | []]//. Qed.
  
  Lemma coin_GL2MF_eq phi psi K:
    phi \coincides_with psi \on K <-> GL2MF (F2GL phi K) =~= GL2MF (F2GL psi K).
  Proof. by rewrite coin_agre agre_spec !GL2MF_spec. Qed.
End coincide.
Notation "phi '\coincides_with' psi '\on' L" := (coincide L phi psi) (at level 30): name_scope.

Local Open Scope name_scope.
Lemma coin_funeq (T: eqType) S (L: seq T) (phi psi: T -> S):
	phi \coincides_with psi \on L <-> {in L, phi =1 psi}.
Proof.
  rewrite /prop_in1 /in_mem /=; elim: L => // t L /=->.
  split => [[eq coin] s /orP [/eqP -> | Ls] | prp]//; first exact/coin.
  by split => [ | s Ls]; apply/prp/orP; [left | right].
Qed.
Local Close Scope name_scope.
