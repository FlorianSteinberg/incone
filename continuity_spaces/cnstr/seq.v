From mathcomp Require Import ssreflect ssrfun seq ssrnat ssrbool.
From rlzrs Require Import all_rlzrs.
Require Import classical_count classical_cont classical_mach classical_func all_cs_base dscrt seq_cont sub.
From metric Require Import pointwise.
Require Import FunctionalExtensionality ClassicalChoice ChoiceFacts.
Require Import Psatz.
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
    move => L.
    elim : L.
    - by exists (fun q => [::]).
    move => a L' [phi' //=IH]//=.
    have [phi phip] := (get_description a).
    by exists (fun q => (phi q)::(phi' q)).
  Qed.
  
  Lemma rep_seq_sing: rep_seq \is_singlevalued.
  Proof.
    move => phi L1.
    move : phi.
    elim : L1.
    - move => phi L2//=.
      case L2; first by [].
      rewrite /rep_seq_rec//=.
      move => a l H1 [H2 _].
      specialize (H1 (someq X)).
      contradiction.
    move => a l IH//= phi.
    move => L2 [H1 [H2 H3]].
    case : L2.
    - simpl.
      move => H4.
      specialize (H4 (someq X)).
      contradiction.
    move => a' l' H4.
    have [H1' [H2' H3']] := H4.
    f_equal.
    - by apply (rep_sing H2).
    apply (IH (fun q => behead (phi q))); first by apply H3.
    by apply H3'.
  Qed.

  Definition seq_cs := make_cs (someq X) [::] (queries_countable X) (list_count (answers_countable X)) rep_seq_sur rep_seq_sing.

  Definition list_size (phi : (names seq_cs)) := (size (phi (someq X))).

  Lemma size_spec L phi : phi \describes L \wrt seq_cs -> (list_size phi) = (size L). 
  Proof.
    move : phi.
    elim : L.
    move => phi //=H1.
    rewrite /list_size.
    by rewrite (H1 (someq X)).
    move => a l IH //=.
    move => phi [H1 [H2 H3]].
    rewrite /list_size.
    case E : (phi (someq X)) => [| a' l']; first by contradiction.
    simpl.
    have IH' :=(IH (fun q => behead (phi q)) H3).
    simpl in IH'.
    rewrite /list_size in IH'.
    symmetry in IH'.
    rewrite IH'.
    rewrite size_behead.
    have p0 : (size l') = (size (a'::l')).-1 by [].
    rewrite p0.
    by rewrite E.
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
