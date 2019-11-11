(** 
    This file introduces some basic notions on the space of functions B:=Q -> A where Q and A are
    arbitrary input and output types (Q is for questions, a is for answers) and are considered
    with the discrete topology. The limit operator lim: (nat -> B) ->> B is the singlevalued
    multifunction such that phi: Q -> A is the eligible return value for a sequence of functions
    of type Q -> A if and only if the sequence converges to phi with respect to the pointwise
    convergence relation. I.e. for any input q there exists a number N such that for any m >= N
    the m-th element of the sequence returns phi q when evaluated in q.
    The file also gives some descriptions of the more common topological concepts when the topology
    corresponding to this convergence relation is used. That these notions can be recovered using
    an appropriate metric is the topic of the file "metric_names.v".
**)
From mathcomp Require Import ssreflect ssrfun seq ssrbool eqtype ssrnat.
From mf Require Import all_mf.
Require Import iseg graphs.
Require Import Morphisms ChoiceFacts.

Axiom functional_extensionality: forall Q A (f g: Q -> A), f =1 g -> f = g.
Local Notation funext:= functional_extensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope name_scope with name.
Local Open Scope name_scope.

Section opens.
  Context (Q A: Type).
  Notation B := (Q -> A).

  (**
     The basic opens of Baire-space are given by the cylinders.
   **)
  Definition cylinder := make_mf (fun KL (phi: Q -> A) => phi \is_choice_for (GL2MF KL)).

  Lemma cldr_spec (phi: B) KL: phi \from cylinder KL <-> phi \is_choice_for (GL2MF KL).
  Proof. done. Qed.

  (**
     BO2O (basic opens (BO) to (2) opens (O)) takes a family of lists, interprets each member as
     cylinder and takes the union of all members of the family to obtain an open set.
   **)
  Definition BO2O (P: subset (seq (Q * A))):=
    make_subset (fun phi => exists KL, KL \from P /\ phi \from cylinder KL).

  Definition open (U: subset B) := exists P, U === BO2O P.

  (**
     The interior of an arbirtary subset is the union of all basic open sets contained in the set.
   **)
  Definition interior (U: subset B) := BO2O (make_subset (fun KL => cylinder KL \is_subset_of U)).

  Lemma open_intr (U: subset B): open (interior U).
  Proof. by exists (make_subset (fun KL => cylinder KL \is_subset_of U)). Qed.
End opens. 
Arguments cylinder {Q} {A}.

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
    phi \from limit phin <-> forall L, exists n, forall m, n <= m -> phi \coincides_with (phin m) \on L.
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

  Definition complement T (A: subset T) := make_subset(fun phi => ~ phi \from A).

  Lemma cmpl_prpr T: Proper (@set_equiv T ==> @set_equiv T) (@complement T).
  Proof. by move => U U' eq t; split => tcU tU; apply/tcU/eq. Qed.
End sequences.
Arguments limit {Q} {A}.
Notation "phi \is_limit_of phin" := (phi \from limit phin) (at level 23): name_scope.

Section closures.
  Context (Q A : Type).
  Notation B := (Q -> A).

  Definition closure (P: subset B):=
    make_subset (fun phi => forall L, exists psi, phi \coincides_with psi \on L /\ P psi).

  Lemma clos_prpr:
    Proper (@set_equiv B ==> @set_equiv B) closure.
  Proof.
    move => P P' eq phi.
    by split => clsr K; have [psi ]:= clsr K; exists psi; [rewrite -eq | rewrite eq].
  Qed.

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

  Lemma clsd_subs P: closed P <-> closure P \is_subset_of P.
  Proof.
    split => [eq q | subs]; first by rewrite eq.
    by apply/set_eq_subs; split => //; apply/subs_clos.
  Qed.

  Lemma clsd_prpr: Proper (@set_equiv B ==> iff) closed.
  Proof.
    move => P P' eq; rewrite !clsd_subs.
    by split => subs q clsr; apply/eq/subs; apply/clos_prpr/clsr => //; symmetry.
  Qed.
    
  Lemma conv_cP P phin psi:
    psi \is_limit_of phin /\ (image phin \is_subset_of P) -> psi \from closure P.
  Proof.
    rewrite img_subs; case => /lim_coin lim elts L; have [n prp] := lim L.
    by exists (phin n); split => //; apply (prp n).
  Qed.

  Lemma open_sclsd (U: subset B): open U -> closed (complement U).
  Proof.
    move => [P eq] phi.
    split => [clsr /= | ]; last exact/subs_clos.
    rewrite eq; case => KL [PKL phiKL].
    have [psi [/coin_agre coin psicU]]:= clsr (unzip1 KL).
    apply/psicU; rewrite eq; exists KL.
    split => // q /GL2MF_dom qfd.
    by have <-:= coin q; first by apply/phiKL/GL2MF_dom.
  Qed.
End closures.
    
Section overtness.
  Local Open Scope name_scope.
  Context (Q A: Type). 
  Notation B := (Q -> A).

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

  Lemma po_val_dom D phi psi L:
    phi \from D -> projection_on D (zip L (map phi L)) psi -> psi \from D.
  Proof. by move => phifd pr; apply/po_val/pr. Qed.
  
  Lemma po_coin D phi psi K: projection_on D (zip K (map phi K)) psi ->
                       phi \coincides_with psi \on K.
  Proof. by move => [_ coin]; apply/coin_sym/coin_GL2MF. Qed.
End overtness.

Section mathcomp.
  Local Open Scope name_scope.
  Context (Q A: eqType). 
  Notation B := (Q -> A).

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
