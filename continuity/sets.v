From mathcomp Require Import ssreflect ssrfun seq ssrbool eqtype ssrnat.
From mf Require Import all_mf.
Require Import iseg smod graphs.
Require Import Morphisms ChoiceFacts.

Axiom functional_extensionality: forall Q A (f g: Q -> A), f =1 g -> f = g.
Local Notation funext:= functional_extensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope name_scope with name.
Local Open Scope name_scope.

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

  Lemma coin_iseg phi psi cnt n m:
    n <= m -> phi \coincides_with psi \on (iseg cnt m) -> phi \coincides_with psi \on (iseg cnt n).
  Proof. by move => ineq; apply/coin_subl; first apply/iseg_subl/ineq. Qed.

  Lemma list_melt (cnt: nat -> Q) (sec: Q -> nat) K (phi psi: B): cancel sec cnt ->
    phi \coincides_with psi \on (iseg cnt (max_elt sec K)) -> phi \coincides_with psi \on K.
  Proof.
    move => cncl; apply/coin_subl; elim: K => // q K subl q' /=[-> | lstn].
    - exact/iseg_subl/lstn_iseg_S/cncl/leq_maxl.
    exact/iseg_subl/subl/lstn/leq_maxr.
  Qed.

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
Notation "phi '\and' psi '\coincide_on' L" := (coincide L phi psi) (at level 2): name_scope.
Notation "phi '\coincides_with' psi '\on' L" := (coincide L phi psi) (at level 2): name_scope.

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

  Definition closed P := closure P === P.
End closures.

Section sequences.
  Context (Q A: Type).
  Local Notation B := (Q -> A).
  Local Notation sequence := (nat -> B).

  Definition image (phin: sequence) := make_subset (fun phi => exists n, phi = phin n).

  Lemma img_subs phin P:
    (image phin \is_subset_of P) <-> (forall n, P (phin n)).
  Proof. by split => H m; [apply/ H; exists m | move => [n ->]; apply H]. Qed.

  Definition limit := make_mf (fun phin (psi: B) =>
    forall q, exists n, forall m, n <= m -> psi q = phin m q).
  Local Notation "phi '\is_limit_of' phin" := (phi \from limit phin) (at level 50).

  Lemma lim_coin phin phi:
    phi \from limit phin <-> forall L, exists n, forall m, n <= m -> phi \and (phin m) \coincide_on L.
  Proof.
    split => [lim | lim q]; last by have [n prp]:= lim [:: q]; exists n; apply prp.
    elim => [ | q L [n prp]]; first by exists 0.
    have [n' prp']:= lim q.
    exists (maxn n n') => m ineq.
    split; first exact/prp'/leq_trans/ineq/leq_maxr.
    exact/prp/leq_trans/ineq/leq_maxl.
  Qed.
    
  Lemma lim_const phi: phi \is_limit_of (cnst phi).
  Proof. by exists 0. Qed.

  Lemma lim_sing: limit \is_singlevalued.
  Proof.
    move => phin phi psi lim lim'; apply functional_extensionality => q.
    have [n /=prp]:= lim q; have [m /=prp']:= lim' q.
    rewrite (prp (maxn n m)); last exact/leq_maxl.
    by rewrite (prp' (maxn n m)); last exact/leq_maxr.
  Qed.
  
  Lemma conv_cP P phin psi:
    psi \is_limit_of phin /\ (image phin \is_subset_of P) -> psi \from closure P.
  Proof.
    rewrite img_subs; case => /lim_coin lim elts L; have [n prp] := lim L.
    by exists (phin n); split => //; apply (prp n).
  Qed.
End sequences.
Arguments limit {Q} {A}.
Notation "phi \is_limit_of phin" := (phi \from limit phin) (at level 23): name_scope.

Section overtness.
  Local Open Scope name_scope.
  Context (Q A: Type). 
  Notation B := (Q -> A).

  Lemma cons_subs T t (L: seq T) P:
    L2SS (t :: L) \is_subset_of P <-> t \from P /\ L2SS L \is_subset_of P.
  Proof.
    split => [subs | [Pa subs] q /=[<- | ]]//; last by apply/subs.
    by split => [ | q lstn]; apply/subs; [left | right].
  Qed.

  Definition cylinder := make_mf (fun KL (phi: Q -> A) => phi \is_choice_for (GL2MF KL)).

  Lemma cldr_spec (phi: B) KL: phi \from cylinder KL <-> phi \is_choice_for (GL2MF KL).
  Proof. done. Qed.

  Definition overt (P: subset B):= exists (ov: nat -> option B),
      (codom (pf2MF ov) \is_subset_of P) /\ P \is_subset_of (closure (codom (pf2MF ov))).

  Definition projection_on (D: subset B):= cylinder|^D.
        
  Lemma dom_po D phi K:
    phi \from D -> zip K (map phi K) \from dom (projection_on D).
  Proof. by move => phifd; exists phi; split; last exact/icf_GL2MF. Qed.

  Lemma zip_po D phi K: phi \from D -> zip K (map phi K) \from dom (projection_on D).
  Proof. by exists phi; split; last exact/icf_GL2MF. Qed.

  Lemma po_val D phi K: phi \from D -> projection_on D (zip K (map phi K)) \is_subset_of D.
  Proof. by move => phifd psi []. Qed.

  Lemma dp_val_dom D phi psi L:
    phi \from D -> projection_on D (zip L (map phi L)) psi -> psi \from D.
  Proof. by move => phifd pr; apply/po_val/pr. Qed.
  
  Lemma dp_coin D phi psi K: projection_on D (zip K (map phi K)) psi ->
                       phi \and psi \coincide_on K.
  Proof. by move => [_ coin]; apply/coin_sym/coin_GL2MF. Qed.
End overtness.
Arguments cylinder {Q} {A}.

Section mathcomp.
  Local Open Scope name_scope.
  Context (Q A: eqType). 
  Notation B := (Q -> A).

  Lemma inP (T: eqType) q (L: seq T): reflect (q \from L2SS L) (q \in L).
  Proof.
    elim: L => [ | t L ih]; [exact/ReflectF | rewrite in_cons].
    by apply/(iffP idP) => [/orP [/eqP -> | /ih ]| /= [-> |/ih lstn]];
                             try apply/orP; [left | right | left | right ].
  Qed.  

  Definition check_choice (phi: B) KL:=
    all (fun q => has (fun qa => (q == qa.1) && (phi q == qa.2)) (KL)) (unzip1 KL).

  Lemma icfP (phi: B) KL:
    reflect (phi \is_choice_for (GL2MF KL)) (check_choice phi KL).
  Proof.
    apply/(iffP idP) => [/allP prp q [a lstn] |icf].
    - suff /hasP [[q' a'] lstn' /andP [/eqP -> /eqP ->]]:
        has (fun qa => (q == qa.1) && (phi q == qa.2)) KL by apply/inP.
      apply/prp/inP; move: prp => _.
      by elim: KL lstn => //; case => q' a' KL /= ih [[->] |/ih ]; [left | right].
    apply/allP => q /inP lstn.      
    have qfd: exists a, (q, a) \from L2SS KL.
    - elim: (KL) lstn => //.
      by case => q' a' KL' ih /=[<- | /ih [b']]; [exists a'; left | exists b'; right].
    apply/hasP.
    have lstn' := icf q qfd.
    by exists (q, phi q); [exact/inP | exact/andP].
  Qed.
End mathcomp.