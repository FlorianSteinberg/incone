From mathcomp Require Import ssreflect ssrfun choice ssrnat ssrbool.
From rlzrs Require Import all_mf.
Require Import iseg Morphisms.
Require Import Reals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section COUNTABILITY.
Definition countable Q := exists cnt: nat ->> Q, cnt \is_singlevalued /\ cnt \is_cototal.
Notation "T '\is_countable'" := (countable T) (at level 2).

Lemma fun_count Q : (exists cnt: nat -> Q, cnt \is_surjective) -> Q \is_countable.
Proof. by move => [cnt sur]; exists (F2MF cnt); split; [exact/F2MF_sing | exact/F2MF_cotot]. Qed.

Lemma pfun_count Q: (exists cnt: nat -> option Q, cnt \is_psurjective) -> Q \is_countable.
Proof. move => [cnt sur]; exists (PF2MF cnt); split; [exact/PF2MF_sing | exact/PF2MF_cotot]. Qed.

Lemma unpickle_sur A : (@unpickle A) \is_psurjective.
Proof. by move => a; exists (pickle a); rewrite pickleK. Qed.

Lemma countMixin_count T : Countable.mixin_of T -> T \is_countable.
Proof.
move => [pickle unpickle pickleK]; apply/pfun_count.
by exists unpickle => a; exists (pickle a); rewrite pickleK.
Qed.

Lemma countType_count (T : countType) : T \is_countable.
Proof. by apply/pfun_count; exists unpickle; exact/unpickle_sur. Qed.

(*Quentin Garchery removed the use of classical reasoning for the countability of products etc. *)

Lemma sum_count Q Q': Q \is_countable -> Q' \is_countable -> (Q + Q') \is_countable.
Proof.
move => [cnt [sing sur]] [cnt' [sing' sur']].
exists (cnt +s+ cnt' \o (PF2MF unpickle)).
split; first exact/comp_sing/PF2MF_sing/fsum_sing/sing'/sing.
exact/comp_cotot/PF2MF_cotot/unpickle_sur/fsum_cotot/sur'/sur/PF2MF_sing.
Qed.

Lemma option_count T : T \is_countable -> (option T) \is_countable.
Proof.
move => [cnt [sing sur]].
exists (make_mf (fun n t => match n with
                    | 0 => t = None
                    | n.+1 => exists s, t = Some s /\ (cnt n s)
                    end)).
split => [[/=_ _ -> -> | /= n t t' [s [-> cntns] [s' [-> cntns']]]]// | [s | ]]; last by exists 0.
- f_equal; apply/sing/cntns'/cntns.
by have [n cntns]:= sur s; exists n.+1; exists s.
Qed.

Lemma prod_count Q Q':
  Q \is_countable -> Q' \is_countable -> (Q * Q') \is_countable.
Proof.
move => [cnt [sing sur]] [cnt' [sing' sur']].
exists (cnt ** cnt' \o (PF2MF unpickle)).
split; first exact/comp_sing/PF2MF_sing/fprd_sing/sing'/sing.
exact/comp_cotot/PF2MF_cotot/unpickle_sur/fprd_cotot/sur'/sur/PF2MF_sing.
Qed.

Lemma map_sing S T (f: S ->> T): f \is_singlevalued -> (mf_map f) \is_singlevalued.
Proof.
move => sing.
elim => [[[] | ] | s K ih]// [] // t L [] // t' L' /=[fst val] [fs't' val'].
exact/f_equal2/ih/val'/val/sing/fs't'/fst.    
Qed.

Lemma list_count Q: Q \is_countable -> (list Q) \is_countable.
Proof.
move => [cnt [sing sur]]; exists (mf_map cnt \o (PF2MF unpickle)).
split; first exact/comp_sing/PF2MF_sing/map_sing/sing.
exact/comp_cotot/PF2MF_cotot/unpickle_sur/map_sur/sur/PF2MF_sing.
Qed.

End COUNTABILITY.
Notation "T '\is_countable'" := (countable T) (at level 2).

Section countable_types.
Lemma unit_count: unit \is_countable.
Proof. by apply/fun_count; exists (fun _ => tt) => [[]]; exists 0. Qed.

Lemma bool_count: bool \is_countable.
Proof. exact/countType_count. Qed.

Lemma nat_count: nat \is_countable.
Proof. exact: countType_count. Qed.

Lemma pos_count: positive \is_countable.
Proof.
apply/fun_count.
exists (fun n => Pos.of_nat n) => p.
by exists (Pos.to_nat p); rewrite Pos2Nat.id.
Qed.

Lemma Z_count: Z \is_countable.
Proof.
have [cnt [sing sur]]:= option_count (sum_count pos_count pos_count).
pose f q := match q with
            | None => Z0
            | Some (inl p) => Zpos p
            | Some (inr p) => Zneg p
            end.
exists (F2MF f \o cnt).
split; first exact/comp_sing/sing/F2MF_sing.
apply/comp_cotot/sur; first exact/sing.
by rewrite -F2MF_cotot; case => [ | p | p]; [exists None | exists (Some (inl p)) | exists (Some (inr p))].
Qed.

Lemma Q_countable: (QArith_base.Q) \is_countable.
Proof.
have [cnt [sing sur]]:= prod_count Z_count pos_count.
pose f p := match p with
            | p => (QArith_base.Qmake p.1 p.2)
            end.
exists (F2MF f \o cnt).
split; first exact/comp_sing/sing/F2MF_sing.
apply/comp_cotot/sur; first exact/sing.
by rewrite -F2MF_cotot; case => e d; exists (e, d).
Qed.

End countable_types.