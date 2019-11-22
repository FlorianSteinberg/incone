(**
   This file provides a very weak definition of countability: T is called countable if it is
   possible to specify a surjective partial function from nat to T. The notion is then compared
   to the more common one that it is provable that there exists a surjection from nat to T.
   Without axioms the former notion is strictly weaker than the later, if the meta-theory is
   classical and countable choice is assumed they are equivalent (a proof of the latter can be
   found in the file classical_count.v). The last section proves a number of types countable.
**)

From mathcomp Require Import ssreflect ssrfun choice ssrnat ssrbool eqtype.
From mf Require Import all_mf.
Require Import iseg search.
Require Import Reals Morphisms ChoiceFacts ConstructiveEpsilon.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section enumerability.
  Definition enumerable Q := exists cnt: nat -> option Q, cnt \is_psurjective.
  
  Lemma enum_inh Q: enumerable Q /\ inhabited Q <->
                     (exists cnt: nat -> Q, cnt \is_surjective).   
  Proof.
    split => [[[cnt sur] [someq]] | [cnt /F2MF_cotot sur]].
    - exists (fun n => match cnt n with |Some q => q | None => someq end).
      by move => q; have [n val]:= sur q; exists n; rewrite val.
    split; last by apply/inhabits/(cnt 0).
    by exists (Some \o_f cnt); apply/pf2MF_cotot.
  Qed.

  Lemma unpickle_sur A : (@unpickle A) \is_psurjective.
  Proof. by move => a; exists (pickle a); rewrite pickleK. Qed.

  Lemma countMixin_enum T: Countable.mixin_of T -> enumerable T.
  Proof.
    move => [pickle unpickle pickleK].
    by exists unpickle => a; exists (pickle a); rewrite pickleK.
  Qed. 

  Lemma countType_enum (T: countType): enumerable T.
  Proof. by exists unpickle; apply/unpickle_sur. Qed.

  Lemma sum_enum Q Q': enumerable Q -> enumerable Q' -> enumerable (Q + Q').
  Proof.
    move => [cnt /pf2MF_cotot sur] [cnt' /pf2MF_cotot sur'].
    exists ((cnt +s+_p cnt') \o_p unpickle).
    apply/pf2MF_cotot.
    rewrite -pf2MF_comp_pf2MF.
    apply/comp_cotot/pf2MF_cotot/unpickle_sur.
    - exact/pf2MF_sing.
    rewrite pf2MF_fsum.
    exact/fsum_cotot.
  Qed.

  Lemma prod_enum Q Q': enumerable Q -> enumerable Q' -> enumerable (Q * Q').
  Proof.
    move => [cnt /pf2MF_cotot sur] [cnt' /pf2MF_cotot sur'].
    exists ((cnt **_p cnt') \o_p unpickle).
    apply/pf2MF_cotot.
    rewrite -pf2MF_comp_pf2MF.
    apply/comp_cotot/pf2MF_cotot/unpickle_sur.
    - exact/pf2MF_sing.
    rewrite pf2MF_fprd.
    exact/fprd_cotot.
  Qed.

  Lemma option_enum Q: enumerable Q -> enumerable (option Q).
  Proof.
    move => [cnt /pf2MF_cotot sur].
    exists (fun n => match n with
                     | 0 => Some None
                     | S n => Some (cnt n)
                     end).
    move => [t | ]; last by exists 0.
    have [n /=]:= sur t.
    case E: (cnt n) => [t' | ]// <-.
    by exists n.+1; rewrite E.
  Qed.
  
  Lemma list_enum Q: enumerable Q -> enumerable (list Q).
  Proof.
    move => [cnt /pf2MF_cotot sur].
    exists ((pmap cnt) \o_p unpickle).
    apply/pf2MF_cotot.
    rewrite -pf2MF_comp_pf2MF.
    apply/comp_cotot/pf2MF_cotot/unpickle_sur.
    - exact/pf2MF_sing.
    rewrite -pf2MF_map.
    exact/map_sur.
  Qed.
End enumerability.

Section countability.
  Definition is_countable Q := exists cnt: nat ->> Q, cnt \is_singlevalued /\ cnt \is_cototal.
  Notation "T '\is_countable'" := (is_countable T) (at level 2).

  Lemma enum_count Q: enumerable Q -> Q \is_countable.
  Proof. by move => [cnt /pf2MF_cotot sur]; exists (pf2MF cnt); split; first exact/pf2MF_sing. Qed.

  Lemma pfun_count Q: (exists cnt: nat -> option Q, cnt \is_psurjective) -> Q \is_countable.
  Proof. move => [cnt sur]; exists (pf2MF cnt); split; [exact/pf2MF_sing | exact/pf2MF_cotot]. Qed.
  
  Lemma countType_count (T : countType) : T \is_countable.
  Proof. exact/enum_count/countType_enum. Qed.

  (*Quentin Garchery removed the use of classical reasoning for the countability
    of products etc. *)

  Lemma sum_count Q Q': Q \is_countable -> Q' \is_countable -> (Q + Q') \is_countable.
  Proof.
    move => [cnt [sing sur]] [cnt' [sing' sur']].
    exists (cnt +s+ cnt' \o (pf2MF unpickle)).
    split; first exact/comp_sing/pf2MF_sing/fsum_sing/sing'/sing.
    exact/comp_cotot/pf2MF_cotot/unpickle_sur/fsum_cotot/sur'/sur/pf2MF_sing.
  Qed.

  Lemma option_count T : T \is_countable -> (option T) \is_countable.
  Proof.
    move => [cnt [sing sur]].
    exists (make_mf (fun n t =>
                       match n with
                       | 0 => t = None
                       | n.+1 => exists s, t = Some s /\ (cnt n s)
                       end)).
    split => [[/=_ _->->|/=n t t' [s [-> cntns] [s' [-> cntns']]]]// | [s | ]]; last by exists 0.
    - f_equal; apply/sing/cntns'/cntns.
    by have [n cntns]:= sur s; exists n.+1; exists s.
  Qed.

  Lemma prod_count Q Q':
    Q \is_countable -> Q' \is_countable -> (Q * Q') \is_countable.
  Proof.
    move => [cnt [sing sur]] [cnt' [sing' sur']].
    exists (cnt ** cnt' \o (pf2MF unpickle)).
    split; first exact/comp_sing/pf2MF_sing/fprd_sing/sing'/sing.
    exact/comp_cotot/pf2MF_cotot/unpickle_sur/fprd_cotot/sur'/sur/pf2MF_sing.
  Qed.

  Lemma map_sing S T (f: S ->> T): f \is_singlevalued -> (mf_map f) \is_singlevalued.
  Proof.
    move => sing.
    elim => [[[] | ] | s K ih]// [] // t L [] // t' L' /=[fst val] [fs't' val'].
    exact/f_equal2/ih/val'/val/sing/fs't'/fst.    
  Qed.

  Lemma list_count Q: Q \is_countable -> (list Q) \is_countable.
  Proof.
    move => [cnt [sing sur]]; exists (mf_map cnt \o (pf2MF unpickle)).
    split; first exact/comp_sing/pf2MF_sing/map_sing/sing.
    exact/comp_cotot/pf2MF_cotot/unpickle_sur/map_sur/sur/pf2MF_sing.
  Qed.
End countability.
Notation "T '\is_countable'" := (is_countable T) (at level 2).
Notation "T '\is_enumerable'" := (enumerable T) (at level 2).

Section mathcomp.
  Lemma inh_enum T (t: T):
    enumerable T <-> exists cnt: nat -> T, cnt \is_surjective.
  Proof.
    split => [[cnt sur] | [cnt sur]]; last by exists (Some \o_f cnt); apply/sur_psur.
    exists (fun n => match cnt n with
                     | None => t
                     | Some t' => t'
                     end).
      by move => t'; have [n eq]:= sur t'; exists n; rewrite eq.
  Qed.

  Lemma exists_minsec_eqT (Q: eqType) (cnt: nat -> Q):
    cnt \is_surjective -> exists sec, minimal_section Q cnt sec.
  Proof.
    move => sur.
    have sur_p: forall q, exists n, cnt n == q by move => q; have [n /eqP eq]:= sur q; exists n.
    pose p q n:= cnt n == q.
    have p_dec: forall q n, {p q n} + {~ p q n} by move => q n; case: (p q n); [left | right].
    suff f: forall (q: Q), {n | p q n}.
    - exists (fun q => nat_search (p q) (sval (f q))).
      split => [q | q m /eqP eq]; last exact/nsrch_min.
      by apply/eqP/(@nsrch_correct (p q)); have := (projT2 (f q)).
    move => q.
    exists (constructive_ground_epsilon_nat (p q) (p_dec q) (sur_p q)).
    exact/(constructive_ground_epsilon_spec_nat (p q)).
  Qed.

  Lemma cT_inh_enum (T:countType) (somet: T):
    exists (cnt: nat -> T) (sec: T -> nat), minimal_section T cnt sec.
  Proof.
    have /(inh_enum somet) [cnt sur]:= countType_enum T.
    by exists cnt; apply/exists_minsec_eqT.
  Qed.

  Lemma eqdec_eqClass Q:
  (forall (q q': Q), {q = q'} + {q <> q'}) -> Equality.class_of Q.
  Proof.                      
    move => eqdec.
    apply/(@Equality.Mixin _ (fun q q' => if eqdec q q' then true else false) _).
    by move => q q'; apply/(iffP idP); case: ifP; try case: (eqdec q q').
  Qed.

  Lemma eqT_eqdec (Q: eqType) (q q': Q): {q = q'} + {q <> q'}.
  Proof. by case E: (q == q'); [left; apply/eqP | right => /eqP]; rewrite E. Defined.

  Lemma count_choice_eqdec Q: Q \is_countable -> FunctionalChoice_on Q nat
                            ->
                            exists P: forall (q q': Q), decidable (q = q'), True.
  Proof.
    move => [cnt [sing sur]] choice.
    have /choice [sec cncl] := sur.
    exists => // q q'.
    case E: (sec q == sec q'); last by right => eq; move: E; rewrite eq => /eqP.
    left; apply/sing/cncl; move /eqP: E => <-.
    exact/cncl.
  Qed.
End mathcomp.

Section enumerable_types.
  Lemma unit_enum: enumerable unit.
  Proof. by exists (fun _ => Some tt) => [[]]; exists 0. Qed.

  Lemma unit_count: unit \is_countable.
  Proof. exact/enum_count/unit_enum. Qed.

  Lemma bool_enum: enumerable bool.
  Proof. exact/countType_enum. Qed.

  Lemma bool_count: bool \is_countable.
  Proof. exact/countType_count. Qed.

  Lemma nat_enum: enumerable nat.
  Proof. exact: countType_enum. Qed.

  Lemma nat_count: nat \is_countable.
  Proof. exact: countType_count. Qed.

  Lemma pos_enum: enumerable positive.
  Proof.
    exists (fun n => Some (Pos.of_nat n)) => p.
    by exists (Pos.to_nat p); rewrite Pos2Nat.id.
  Qed.

  Lemma pos_count: positive \is_countable.
  Proof. exact/enum_count/pos_enum. Qed.

  Lemma Z_enum: enumerable Z.
  Proof.
    have [cnt sur]:= option_enum (sum_enum pos_enum pos_enum).
    pose f q := match q with
                | None => Z0
                | Some (inl p) => Zpos p
                | Some (inr p) => Zneg p
                end.
    exists ((Some \o_f f) \o_p cnt).
    apply/pf2MF_cotot.
    rewrite -pf2MF_comp_pf2MF.
    apply/comp_cotot/pf2MF_cotot/sur/F2MF_cotot.
    - exact/pf2MF_sing.
    rewrite -F2MF_cotot; case => [ | p | p]; first by exists None.
    - by exists (Some (inl p)).
    by exists (Some (inr p)).
  Qed.

  Lemma Z_count: Z \is_countable.
  Proof. exact/enum_count/Z_enum. Qed.

  Lemma Q_enum: enumerable (QArith_base.Q).
  Proof.
    have [cnt sur]:= prod_enum Z_enum pos_enum.
    pose f p := match p with
                | p => (QArith_base.Qmake p.1 p.2)
                end.
    exists (Some \o_f f \o_p cnt).
    apply/pf2MF_cotot; rewrite -pf2MF_comp_pf2MF; apply/comp_cotot/pf2MF_cotot/sur.
    - exact/pf2MF_sing.
    by rewrite -F2MF_cotot; case => e d; exists (e, d).
  Qed.

  Lemma Q_count: is_countable (QArith_base.Q).
  Proof. exact/enum_count/Q_enum. Qed.

  Lemma enum_eqT_choice (Q: eqType) T: inhabited Q -> Q \is_enumerable ->
                                     FunctionalCountableChoice_on T -> FunctionalChoice_on Q T.
  Proof.
    move => [someq] /(inh_enum someq) [cnt sur] countable_choice F tot.
    pose R n t:= F (cnt n) t.
    have [n | f fprp]:= countable_choice R; first by have [t val]:= tot (cnt n); exists t.
    have [sec [cncl min]]:= exists_minsec_eqT sur.
    exists (f \o_f sec) => q /=.
    by have:= fprp (sec q); rewrite /R cncl.
  Qed.
End enumerable_types.

Ltac countability :=
  repeat apply/list_count || apply/prod_count || apply/sum_count || apply/option_count
  || apply/unit_count || apply/bool_count || apply/nat_count || apply/Z_count || apply/Q_count.      

Section ListedTypes.
  Structure ListedType :=
    {
      type:> Type;
      enumeration: nat -> option type;
      enumerated: enumeration \is_psurjective;
    }.

  Context (T: ListedType).

  Definition find (p: pred T) (n: nat):=
    match direct_search (enumeration T) (fun ot => if ot is Some t then p t else false) n with
    | Some (Some t) => Some t
    | _ => None
    end.
  
  Lemma find_correct (p: pred T) n x: find p n = Some x -> p x.
  Proof.
    rewrite /find.
    case E: direct_search => [ot |] //.
    have := (@dsrch_correct (option T) (enumeration T) _ _ _ E).
    by case: ot E => // t E pt [<-].
  Qed.

  Lemma LType_choice (p: pred T): (exists t, p t) -> {t | p t}.
  Proof.
    move => ex.
    pose p' n := if enumeration T n is Some t then p t else false.
    have ex': exists n, p' n by case: ex => t pt; have [n eq]:= enumerated t; exists n; rewrite /p' eq.
    have [ | n]:= constructive_indefinite_description_nat p' _ ex'.
    - move => n; rewrite /p'.
      case: (enumeration T n) => [t | ]; last by right.
      by case: (p t); [left | right].
    by rewrite /p'; case eq: enumeration => [t | ]// pt; exists t.
  Qed.
End ListedTypes.
