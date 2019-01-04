From mathcomp Require Import ssreflect ssrfun seq ssrbool eqtype ssrnat.
From rlzrs Require Import all_mf.
Require Import iseg.
Require Import Morphisms.

Axiom functional_extensionality: forall Q A (f g: Q -> A), f =1 g -> f = g.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope baire_scope with baire.
Local Open Scope baire_scope.
Section L2SS.
  Context (T: Type).
  
  Definition L2SS (L: seq T):= make_subset (fun s => List.In s L).

  Lemma L2SS_subs L K: L \is_sublist_of K <-> (L2SS L) \is_subset_of (L2SS K).
  Proof. done. Qed.

  Lemma L2SS_eq L K:
    (L2SS L) === (L2SS K) <-> L \is_sublist_of K /\ K \is_sublist_of L.
  Proof. by rewrite set_eq_subs !L2SS_subs. Qed.

  Lemma L2SS_cat (L K: seq T): L2SS (L ++ K) === (L2SS L) \u (L2SS K).
  Proof.
    move => t.
    elim: L => [ | a L ih /=]; first by split; [right | case].
    split => [[ | /ih []] | ]; [left; left | left; right | right | ] => //.
    by rewrite /= in ih; rewrite ih => [[[] | ]]; [left | right; left | right; right ].
  Qed.
End L2SS.

Section coincide.
  Context (Q A : Type).
  (* Q is for questions, A is for answers*)
  Local Notation B := (Q -> A).
  (* The topology on Baire space is the topology of pointwise convergence the following are
     the basic open ets (in the sens that for each finite list L and each element phi of Baire
     space the set {psi | coin phi psi L} is a basic open set *)

  Definition agree_on P (phi psi: B):= forall q, P q -> phi q = psi q.
  
  Lemma agre_ref L: Reflexive (agree_on L).
  Proof. done. Qed.
  
  Lemma agre_sym L: Symmetric (agree_on L).
  Proof. by move => phi psi coin q Lq; rewrite coin. Qed.
  
  Lemma agre_trans L: Transitive (agree_on L).
  Proof. by move => phi psi psi' coin coin' q Lq; rewrite coin // coin'. Qed.

  Global Instance agre_equiv L: Equivalence (agree_on L).
  Proof. by split; [apply agre_ref | apply agre_sym | apply agre_trans]. Qed.

  Notation "phi '\agrees_with' psi '\on' P" :=
    (agree_on (P: subset _) phi psi) (at level 2).

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

  Fixpoint coincide L (phi psi: B) :=
    match L with
    | nil => True
    | cons s K => (phi s = psi s) /\ (coincide K phi psi)
    end.
  Local Notation "phi \and psi \coincide_on L" := (coincide L phi psi) (at level 20).
  
  Lemma coin_lstn (phi psi: B) (L: seq Q):
    phi \and psi \coincide_on L <-> (forall q, List.In q L -> phi q = psi q).
  Proof.
    elim: L => //; split => [ [ass1 ass2] q' [<- | listin] | ass ] //; first by apply H.1.
    by split; last (apply H.2; intros); apply ass; [left | right].
  Qed.

  Lemma coin_cat (phi psi: B) L K:
    phi \and psi \coincide_on (L ++ K) <-> (phi \and psi \coincide_on L /\ phi \and psi \coincide_on K).
  Proof.
    split; first by elim: L => [| a L ih] //=; case => eq b; have []:= ih b; do 2 try split.
    by elim: L => [[_ coin]| a L ih [/=[/=ass1 ass2] ass3]] => //=; split => //; apply ih.
  Qed.

  Lemma coin_subl phi psi L K:
    L \is_sublist_of K -> phi \and psi \coincide_on K -> phi \and psi \coincide_on L.
  Proof. by rewrite !coin_lstn; intros; apply/H0/H. Qed.

  Lemma coin_iseg phi psi cnt n m:
    n <= m -> phi \and psi \coincide_on (iseg cnt m) -> phi \and psi \coincide_on (iseg cnt n).
  Proof. by move => ineq; apply/coin_subl; first apply/iseg_subl/ineq. Qed.

  Lemma list_melt (cnt: nat -> Q) (sec: Q -> nat) K (phi psi: B): cancel sec cnt ->
    phi \and psi \coincide_on (iseg cnt (max_elt sec K)) -> phi \and psi \coincide_on K.
  Proof.
    move => cncl; apply/coin_subl; elim: K => // q K subl q' /=[-> | lstn].
    - exact/iseg_subl/lstn_iseg_S/cncl/leq_maxl.
    exact/iseg_subl/subl/lstn/leq_maxr.
  Qed.

  Lemma coin_agre L (phi psi: B) :
    phi \and psi \coincide_on L <-> phi \agrees_with psi \on (L2SS L).
  Proof.
    elim: L => [ | q L ih /=]; first by split => // _ q.
    split => [[eq /ih agre] s [<- | lstn] // | agre]; first exact/agre.
    split; first by apply/agre; left.
    by apply/ih => s lstn; apply/agre; right.
  Qed.

  Lemma coin_spec L (phi psi: B):
    phi \and psi \coincide_on L <-> (F2MF phi)|_(L2SS L) =~= (F2MF psi)|_(L2SS L).
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
    phi \and phi' \coincide_on K -> map phi K = map phi' K.
  Proof. by elim: K => // q K ih /=[-> coin]; rewrite ih. Qed.

End coincide.
Notation "phi '\agrees_with' psi '\on' P" :=
  (agree_on (P: subset _) phi psi) (at level 2): mf_scope.
Notation "phi '\and' psi '\coincide_on' L" := (coincide L phi psi) (at level 2): baire_scope.

Lemma coin_funeq (T: eqType) S (L: seq T) (phi psi: T -> S):
	phi \and psi \coincide_on L <-> {in L, phi =1 psi}.
Proof.
  rewrite /prop_in1 /in_mem /=; elim: L => // t L /=->.
  split => [[eq coin] s /orP [/eqP -> | Ls] | prp]//; first exact/coin.
  by split => [ | s Ls]; apply/prp/orP; [left | right].
Qed.

Section closures.
  Context (Q A : Type).
  Notation B := (Q -> A).

  Definition closure (P: subset B):=
    make_subset (fun phi => forall L, exists psi, phi \and psi \coincide_on L /\ P psi).

  Lemma subs_clos P: P \is_subset_of (closure P).
  Proof. by move => phi; exists phi; split => //; apply: coin_ref. Qed.
  Arguments subs_clos (P) : clear implicits.

  Lemma clos_subs P P': P \is_subset_of P' -> (closure P) \is_subset_of (closure P').
  Proof.
    move => subs phi cPphi L; have [psi []]:= cPphi L.
    by exists psi; split => //; apply subs.
  Qed.

  Lemma clos_clos P: closure (closure P) === closure P.
  Proof.
    rewrite set_eq_subs; split; last exact/subs_clos.
    move => phi ccPphi L; have [psi [coin cPpsi]] := ccPphi L; have [psi' [coin' Ppsi']] := cPpsi L.
    by exists psi'; split => //; apply: coin_trans coin coin'.
  Qed.
End closures.

Section sequences.
  Context (Q A: Type).
  Notation B := (Q -> A).
  Notation sequence:= (nat -> B).

  Definition image (phin: sequence) := make_subset (fun phi => exists n, phi = phin n).

  Lemma img_subs phin P:
    (image phin \is_subset_of P) <-> (forall n, P (phin n)).
  Proof. by split => H m; [apply/ H; exists m | move => [n ->]; apply H]. Qed.

  Definition limit := make_mf (fun phin (psi: B) =>
    forall L, exists n, forall m, n <= m -> psi \and (phin m) \coincide_on L).
  Local Notation "psi '\is_limit_of' phin" := (limit phin psi) (at level 50).

  Lemma lim_const phi: phi \is_limit_of (cnst phi).
  Proof. move => L; exists 0 => m _; apply/coin_ref. Qed.

  Lemma lim_sing: limit \is_singlevalued.
  Proof.
    move => phin phi psi lim lim'; apply functional_extensionality => q.
    have [n /=prp]:= lim [:: q]; have [m /=prp']:= lim' [:: q].
    have [-> _]:= prp (maxn n m) (leq_maxl n m).
    by have [-> _]:= prp' (maxn n m) (leq_maxr n m).
  Qed.
  
  Lemma conv_cP P phin psi:
    psi \is_limit_of phin /\ (image phin \is_subset_of P) -> psi \from closure P.
  Proof.
    rewrite img_subs; case => conv elts L; have [n prop]:= conv L.
    by exists (phin n); split => //; apply (prop n).
  Qed.
End sequences.
Arguments limit {Q} {A}.
Notation "phi \is_limit_of phin" := (limit phin phi) (at level 23): baire_scope.