From mathcomp Require Import ssreflect ssrfun choice ssrnat ssrbool.
From rlzrs Require Import all_mf.
Require Import iseg Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section COUNTABILITY.
Definition is_count Q :=
	exists cnt: nat -> option Q, cnt \is_surjective.
Notation "T '\is_countable'" := (is_count T) (at level 2).

Definition minimal_section Q (cnt: nat -> Q) (sec : Q -> nat) :=
  cancel sec cnt /\ forall s,(forall m, cnt m = s -> sec s <= m).

Lemma countMixin_count T : Countable.mixin_of T -> T \is_countable.
Proof.
move=> [pickle unpickle pickleK].
exists (fun n => if n isn't n.+1 then None else unpickle n).
move=> [x|]; last by exists 0.
by exists (pickle x).+1; rewrite pickleK.
Qed.

Lemma countType_count (T : countType) : T \is_countable.
Proof. by apply: countMixin_count; case: T => [?[]]. Qed.

Lemma nat_count: nat \is_countable.
Proof. exact: countType_count. Qed.

Lemma count_sur Q: (exists cnt: nat -> Q, cnt \is_surjective) <-> inhabited Q /\ Q \is_countable.
Proof.
split => [ [cnt sur] | [[someq [cnt sur]]]].
- split; first exact (inhabits (cnt 0)).
  exists (fun n => match n with
	   | 0 => None
	   | S n' => Some (cnt n')
	   end) => q.
  case: q => [q | ]; last by exists 0.
  by have [n val] := sur (q); exists (S n); rewrite val.
exists (fun n => match cnt n with
	| None => someq
	| Some q => q
end) => q.
by have [n val] := sur (some q); exists n; rewrite val.
Qed.

(*Quentin Garchery removed the use of classical reasoning for the countability of products etc. *)

Lemma surj_unopt A (f : nat -> option A) :
  (forall j : A, exists i : nat, f i = Some j) -> 
  A \is_countable.
Proof.
  
  exists (fun i => match i with
                   | 0 => None
                   | S j => f j end).

  move => [b | ]. destruct (H b). exists (S x). assumption.
  exists 0. reflexivity.
Qed.


Lemma option_count T : T \is_countable -> (option T) \is_countable.
Proof.
  move => [f sf].
  apply surj_unopt with (fun x => Some (f x)) => j.
  have [i fi] := sf j.
  now exists i; f_equal.
Qed.

Lemma sum_count Q Q': Q \is_countable -> Q' \is_countable ->
                      (Q + Q') \is_countable.
Proof.
  move => [fq sfq] [fq' sfq'].
  pose f := fun os => match os with
                      | None => None
                      | Some s => match s with
                                  | inl n => match fq n with
                                             | None => None
                                             | Some q => Some (inl q) end
                                  | inr n' => match fq' n' with
                                              | None => None
                                              | Some q' => Some (inr q')
                                              end
                                  end
                      end.
  apply surj_unopt with (f \o_f unpickle).
  move => [q | q'].
  -have [n fn] := sfq (Some q).
   by exists (pickle (inl nat n)); rewrite /= pickleK /= fn.
  -have [n' fn'] := sfq' (Some q').
   by exists (pickle (inr nat n')); rewrite /= pickleK /= fn'.
Qed.

Lemma prod_count Q Q':
  Q \is_countable -> Q' \is_countable -> (Q * Q') \is_countable.
Proof.
  move => [fq sfq] [fq' sfq'].
  pose f := fun op => match op with
                      | None => None
                      | Some (n, n') => match fq n with
                                        | None => None
                                        | Some q => match fq' n' with
                                                    | None => None
                                                    | Some q' => Some (q, q') end
                                        end
                      end.
  apply surj_unopt with (f \o_f unpickle).
  move => [q q'].
  have [n fqn] := sfq (Some q); have [n' fqn'] := sfq' (Some q').
  by exists (pickle (n, n')); rewrite /= pickleK /= fqn fqn'.
Qed.

Fixpoint factorize_opt {A}  (l : list (option A)) :=
  match l with
  | nil => Some nil
  | cons h t =>
    match factorize_opt t with
    | None => None
    | Some l =>  match h with
                 | None => None
                 | Some a => Some (cons a l)
                 end
    end
  end.

Definition apply_opt {Q} (fq : nat -> option Q) ol :=
  match ol with
  | None => None
  | Some l => factorize_opt (List.map fq l) 
  end.

Lemma apply_opt_surj (Q : Type) (fq : nat -> option Q) :
  fq \is_surjective -> forall lq , exists ln, apply_opt fq (Some ln) = Some lq.
Proof.
  move => sfq lq.
  elim : lq => [ | a lq [ln /= aln]]; first by exists nil.
  have [h fh] := sfq (Some a).
  exists (cons h ln).
  rewrite /= aln. now rewrite fh.
Qed.
  
Lemma list_count Q: Q \is_countable -> (list Q) \is_countable.
Proof.
  move => [fq sfq].
  apply surj_unopt with (apply_opt fq \o_f unpickle) => lq.
  have [ln aln] := apply_opt_surj sfq lq.
  exists (pickle ln). remember (apply_opt fq) as g. 
  move : aln => /=. rewrite Heqg; clear Heqg g.
  by rewrite pickleK.
Qed.


End COUNTABILITY.
Notation "T '\is_countable'" := (is_count T) (at level 2).
