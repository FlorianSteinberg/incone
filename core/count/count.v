From mathcomp Require Import ssreflect ssrfun choice ssrnat ssrbool.
From rlzrs Require Import all_mf.
Require Import iseg Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section COUNTABILITY.
Definition countable Q := exists cnt: nat -> option Q, cnt \is_psurjective.
Notation "T '\is_countable'" := (countable T) (at level 2).

Lemma unpickle_sur A : (@unpickle A) \is_psurjective.
Proof. by move => a; exists (pickle a); rewrite pickleK. Qed.

Lemma countMixin_count T : Countable.mixin_of T -> T \is_countable.
Proof. by move=> [pickle unpickle pickleK]; exists unpickle => a; exists (pickle a); rewrite pickleK. Qed.

Lemma countType_count (T : countType) : T \is_countable.
Proof. by apply: countMixin_count; case: T => [?[]]. Qed.

Lemma nat_count: nat \is_countable.
Proof. exact: countType_count. Qed.

Lemma count_sur Q: (exists cnt: nat -> Q, cnt \is_surjective) <-> inhabited Q /\ Q \is_countable.
Proof.
split => [ [cnt sur] | [[someq [cnt sur]]]].
- split; first exact/inhabits/cnt/0.
  by exists (Some \o_f cnt); exact/sur_psur.
exists (fun n => match cnt n with
	| None => someq
	| Some q => q
         end) => q.
by have [n val] := sur q; exists n; rewrite val.
Qed.

(*Quentin Garchery removed the use of classical reasoning for the countability of products etc. *)

Lemma sum_count Q Q': Q \is_countable -> Q' \is_countable -> (Q + Q') \is_countable.
Proof.
move => [cnt sur] [cnt' sur'].
exists (cnt +s+_p cnt' \o_p unpickle).
apply/comp_psur/unpickle_sur; apply/PF2MF_cotot; rewrite PF2MF_fsum.
exact/fsum_cotot/PF2MF_cotot/sur'/PF2MF_cotot.
Qed.

Lemma option_count T : T \is_countable -> (option T) \is_countable.
Proof.
move => [cnt sur].
exists (fun n => match n with
         | 0 => Some None
         | n.+1 => Some (cnt n)
         end).
move => [t | ]; last by exists 0.
by have [n <-] := sur t; exists n.+1.
Qed.

Lemma prod_count Q Q':
  Q \is_countable -> Q' \is_countable -> (Q * Q') \is_countable.
Proof.
move => [cnt sur] [cnt' sur'].
exists (cnt **_p cnt' \o_p unpickle).
apply/comp_psur/unpickle_sur; apply/PF2MF_cotot; rewrite PF2MF_fprd.
exact/fprd_cotot/PF2MF_cotot/sur'/PF2MF_cotot.
Qed.

Lemma list_count Q: Q \is_countable -> (list Q) \is_countable.
Proof.
move => [cnt sur]; exists (pmap cnt \o_p unpickle); apply/comp_psur/unpickle_sur.
by rewrite PF2MF_cotot -PF2MF_map; apply map_sur; rewrite -PF2MF_cotot.
Qed.

End COUNTABILITY.
Notation "T '\is_countable'" := (countable T) (at level 2).
