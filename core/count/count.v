From mathcomp Require Import ssreflect ssrfun choice ssrnat ssrbool.
From rlzrs Require Import all_mf.
Require Import iseg Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section COUNTABILITY.
Definition is_count Q :=
	exists cnt: nat -> option Q, cnt \is_surjective_function.
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

Lemma count_sur Q: (exists cnt: nat -> Q, cnt \is_surjective_function) <-> inhabited Q /\ Q \is_countable.
Proof.
split => [ [cnt sur] | [[someq [cnt sur]]]].
	split; first exact (inhabits (cnt 0)).
	exists (fun n => match n with
		| 0 => None
		| S n' => Some (cnt n')
	end).
	move => q.
	case: q; last by exists 0.
	move => q.
	have [n val] := sur (q).
	by exists (S n); rewrite val.
exists (fun n => match cnt n with
	| None => someq
	| Some q => q
end) => q.
have [n val] := sur (some q).
by exists n; rewrite val.
Qed.

End COUNTABILITY.
Notation "T '\is_countable'" := (is_count T) (at level 2).