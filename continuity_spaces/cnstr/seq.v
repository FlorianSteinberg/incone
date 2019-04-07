From mathcomp Require Import ssreflect ssrfun seq ssrnat.
From rlzrs Require Import all_rlzrs.
Require Import all_cs_base dscrt.
From metric Require Import pointwise.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SEQ.
  Context (X: cs).
  Fixpoint rep_seq_rec phi L :=
    match L with
      | nil => forall q, (phi q) = [::]
      | (a :: L') => (not (phi (someq X) = [::])) /\ (fun q => (head (somea X) (phi q))) \describes a \wrt X
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
    move => phi L1.
    elim : L1 phi => [phi [ | a L H1 []]// | a L IH phi [[] | a' L' phinaL phina'L']//].
    f_equal; last by apply/IH; [apply phinaL | apply phina'L'].
    by apply/rep_sing; [apply phinaL | apply phina'L'].
  Qed.

  Definition cs_seq := make_cs (someq X) [::] (queries_countable X) (list_count (answers_countable X)) rep_seq_sur rep_seq_sing.

  Definition size_rlzrf (phi : (names cs_seq)) (tt: unit) := (size (phi (someq X))).

  Definition size_rlzr: names cs_seq ->> names cs_nat := F2MF size_rlzrf.

  Lemma size_rlzr_cntop: size_rlzr \is_continuous_operator.
  Proof.
    rewrite cont_F2MF /size_rlzrf => phi.
    by exists (fun _ => [::someq X]) => q' psi /= [-> _].
  Qed.
    
  Lemma size_rlzr_spec: size_rlzr \realizes (F2MF size).
  Proof.
    apply/F2MF_rlzr_F2MF => phi L/=; rewrite /size_rlzrf.
    elim : L phi => [phi -> | a L IH phi phinaL]//=.    
    case E : (phi (someq X)) => [| a' L']; first by case phinaL.
    rewrite -(IH (fun q => behead (phi q))); last by apply phinaL.
    by rewrite size_behead /= E.
  Qed.

  Lemma size_cont: (size: cs_seq -> cs_nat) \is_continuous.
  Proof.
    exists size_rlzr; split; [exact/size_rlzr_spec | exact/size_rlzr_cntop].
  Qed.

  (*  Definition list_head (phi0 : (names X)) (phi : (names seq_cs)) := (fun q => (head (phi0 q) (phi q))). *)

 (*  Lemma head_spec1 x L' phi : forall phi0, phi \describes x::L' \wrt seq_cs -> ((list_head phi0 phi) \describes x \wrt X). *)
 (*  move => phi0. *)
 (*  move => [H1 [H2 H3]]. *)
 (*  rewrite /list_head. *)
 (*  have p1 : 0 < size(x :: L') by auto. *)
 (*  have p2 : forall q, not ((phi q) = [::]).  *)
 (*  - move => q. *)
 (*    suff : not ((size (phi q)) = 0). *)
 (*    * suff : (phi q = [::]) -> (size (phi q)) = 0 by auto. *)
 (*      move => H. *)
 (*      by rewrite H. *)
 (*   specialize (H1 q). *)
 (*   symmetry in H1. *)
 (*   by rewrite H1. *)
 (*  specialize (H2 0 p1). *)
 (*  rewrite nth0 in H2. *)
 (*  rewrite /list_head. *)
 (*  have fun_eq : (fun q => (head (phi0 q) (phi q))) = (fun q => (nth (somea X) (phi q)) 0). *)
 (*  - apply functional_extensionality. *)
 (*    move => q. *)
 (*    rewrite  nth0. *)
 (*    case P : (phi q). *)
 (*     -specialize (p2 q); by contradiction. *)
 (*    done. *)
 (*  by rewrite fun_eq. *)
 (*  Qed. *)

 (*  Lemma head_spec2 phi : forall phi0, phi \describes [::] \wrt seq_cs -> (list_head phi0 phi) = phi0. *)
 (*  Proof. *)
 (*    move => phi0. *)
 (*    move => [H1 H2]. *)
 (*    have P : forall q, (phi q) = [::]. *)
 (*    - move => q. *)
 (*      suff : (size (phi q)) = 0 by apply size0nil. *)
 (*      specialize (H1 q). *)
 (*      symmetry in H1. *)
 (*      by rewrite H1. *)
 (*   rewrite /list_head. *)
 (*   apply functional_extensionality. *)
 (*   move => q. *)
 (*   by rewrite (P q). *)
 (* Qed. *)

 Definition list_cons (phi0 : names X) phi := (fun q => (cons (phi0 q) (phi q))).

 Lemma cons_spec x L phi0 phi : phi0 \describes x \wrt X /\ phi \describes L \wrt seq_cs -> (list_cons phi0 phi) \describes (x :: L) \wrt seq_cs.
 Proof.
   done.
 Qed.
End SEQ.

Definition nat_list := (rep_seq cs_nat).
