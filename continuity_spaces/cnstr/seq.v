From mathcomp Require Import ssreflect ssrfun seq ssrnat.
From rlzrs Require Import all_rlzrs.
Require Import all_cs_base dscrt.
From metric Require Import pointwise.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SEQ.
  Local Open Scope curry_scope.
  Context (X: cs).
  Fixpoint rep_seq_rec phi L :=
    match L with
      | nil => forall q, (phi q) = [::]
      | (a :: L') => (forall q, phi q <> [::])
                     /\ (fun q => head (somea X) (phi q)) \describes a \wrt X
                     /\ (rep_seq_rec (fun q => (behead (phi q))) L')
      end.

  Definition rep_seq := make_mf rep_seq_rec.

  Lemma rep_seq_sur: rep_seq \is_cototal.
  Proof.
    elim => [ | a L' [phi']]; first by exists (fun q => [::]).
    have [phi phip] := (get_description a).
    by exists (fun q => (phi q)::(phi' q)).
  Qed.
  
  Lemma rep_seq_sing: rep_seq \is_singlevalued.
  Proof.
    move => phi L.
    elim: L phi => [phi [ | a L' phinL [prp]]//| a L ih phi [[prp] | a' L' phinaL phina'L']//];
                     try by have := prp (someq X).
    f_equal; last by apply/ih; [apply phinaL | apply phina'L'].
    by apply/rep_sing; [apply phinaL | apply phina'L'].
  Qed.

  Definition cs_seq := make_cs (someq X) [::] (queries_countable X) (list_count (answers_countable X)) rep_seq_sur rep_seq_sing.

  Definition size_rlzrf (phi : (name_space cs_seq)) (tt: unit) := (size (phi (someq X))).

  Definition size_rlzr: name_space cs_seq ->> name_space cs_nat := F2MF size_rlzrf.

  Lemma size_rlzr_cntop: size_rlzr \is_continuous_operator.
  Proof.
    rewrite cont_F2MF /size_rlzrf => phi.
    by exists (fun _ => [::someq X]) => q' psi /= [-> _].
  Qed.
    
  Lemma size_rlzr_spec: size_rlzr \realizes (F2MF size).
  Proof.
    apply/F2MF_rlzr_F2MF => phi L/=; rewrite /size_rlzrf.
    elim : L phi => [phi -> | a L IH phi phinaL]//=.    
    case E : (phi (someq X)) => [ | a' L']; first by have:= (phinaL.1 (someq X)).
    rewrite -(IH (fun q => behead (phi q))); last by apply phinaL.
    by rewrite size_behead /= E.
  Qed.

  Lemma size_cont: (size: cs_seq -> cs_nat) \is_continuous.
  Proof. by exists size_rlzr; split; [exact/size_rlzr_spec | exact/size_rlzr_cntop]. Qed.

  Definition head_rlzrf phi (psi: name_space cs_seq) q := head (phi q) (psi q).

  Definition head_rlzr: name_space (X \*_cs cs_seq) ->> name_space X :=
    F2MF (fun phi => head_rlzrf (lprj phi) (rprj phi)).

  Lemma head_rlzr_cntop: head_rlzr \is_continuous_operator.
  Proof.
    apply/cont_F2MF; rewrite /head_rlzrf/lprj/rprj.
    by exists (fun q => [:: inl q; inr q]) => q psi /= [-> [->]].
  Qed.
              
  Lemma head_rlzr_spec: head_rlzr \realizes (F2MF (fun xL => head xL.1 xL.2)).
  Proof.
    apply/F2MF_rlzr_F2MF => phi [x L] [/=phinx].
    case: L => [prp | y L [neq [phiny _]]].
    - suff ->: head_rlzrf (lprj phi) (rprj phi) = lprj phi by trivial.
      by apply/functional_extensionality => q; rewrite /head_rlzrf prp.
    suff ->: head_rlzrf (lprj phi) (rprj phi) = fun q => head (some_answer X) (rprj phi q) by trivial.
    apply/functional_extensionality => q.
    by rewrite /head_rlzrf; have:= neq q; case: (rprj phi q) => //.
  Qed.

  Lemma head_cont: (head : X -> cs_seq -> X) \is_continuous.
  Proof. by exists head_rlzr; split; [exact/head_rlzr_spec | exact/head_rlzr_cntop]. Qed.
   
  Definition cons_rlzrf (phi : name_space X) psi := (fun q => (cons (phi q) (psi q))).

  Definition cons_rlzr: name_space (X \*_cs cs_seq) ->> (name_space cs_seq) :=
    F2MF (fun phi => cons_rlzrf (lprj phi) (rprj phi)).
  
  Lemma cons_rlzr_cntop: cons_rlzr \is_continuous_operator.
  Proof.
    apply/cont_F2MF; rewrite /cons_rlzrf/lprj/rprj.
    by exists (fun q => [:: inl q; inr q]) => q' psi /=[-> [->]].
  Qed.
  
  Lemma cons_rlzr_spec: cons_rlzr \realizes (F2MF (fun xL => cons xL.1 xL.2)).
  Proof. exact/F2MF_rlzr_F2MF. Qed.

  Lemma cons_cont: (cons: X -> cs_seq -> cs_seq) \is_continuous.
  Proof.
    by exists cons_rlzr; split; [exact/cons_rlzr_spec | exact/cons_rlzr_cntop].
  Qed.
End SEQ.