From mathcomp Require Import ssreflect ssrnat ssrbool choice eqtype ssrfun seq.
From mf Require Import all_mf choice_mf.
Require Import baire cont seq_cont classical_cont iseg count.
Require Import ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma exists_minsec Q (cnt: nat -> Q):
  cnt \is_surjective -> exists sec, minimal_section cnt sec.
Proof.
move => sur.
set R := make_mf (fun s n => cnt n = s /\ (forall m, cnt m = s -> n <= m)).
have Rtot: R \is_total by move => s; have [n]:= well_order_nat (sur s); exists n.
by have [sec]:= (choice _ Rtot); exists sec; split => s; have []:= p s.
Qed.

Lemma count_countMixin Q : Q \is_countable ->
  exists P : Countable.mixin_of Q, True.
Proof.
move => [_ [/pfun_spec [cnt <-]/PF2MF_cotot sur]].
pose cnt' := (fun n => match n with | 0 => None | S n => cnt n end).
have sur': cnt' \is_surjective by move => [q | ]; [have [n]:= sur q; exists n.+1 | exists 0].
have [sec' [issec min]] := exists_minsec sur'.
unshelve eexists (@Countable.Mixin _ (sec' \o_f Some) cnt' _) => //.
by move=> x /=; rewrite issec.
Qed.

Lemma classic_eqClass Q : exists P : Equality.class_of Q, True.
Proof.
have /choice[eq eqP]: forall q, exists b, (q.1 = q.2 :> Q) <-> (b = true).
  by move=> q; case: (classic (q.1 = q.2)) => ass; [exists true|exists false].
unshelve eexists (@Equality.Mixin _ (fun x y => eq (x, y)) _) => //.
by move=> x y; apply: (iffP idP) => [/eqP//|->]; apply/eqP.
Qed.

Lemma count_countClass Q  : Q \is_countable ->
  exists P : Countable.class_of Q, True.
Proof.
move=> /count_countMixin[cmQ _]; have [eqQ _] := classic_eqClass Q.
set QeqType := EqType Q eqQ.
set QchoiceType := ChoiceType QeqType (CountChoiceMixin cmQ).
by exists (Countable.class (CountType QchoiceType cmQ)).
Qed.

Lemma pfun_count_iff Q: Q \is_countable <-> exists cnt: nat -> option Q, cnt \is_psurjective.
Proof.
by split => [[_ [/pfun_spec [cnt <-] /PF2MF_cotot sur]] | ]; [exists cnt | exact/pfun_count].
Qed.

Lemma count_fun T (pcnt: nat -> option T): inhabited T -> pcnt \is_psurjective -> exists cnt: nat -> T, cnt \is_surjective.
Proof.
move => [somet] sur.
exists (fun n => match pcnt n with
         | None => somet
         | Some t => t
         end).
by move => t; have [n eq]:= sur t; exists n; rewrite eq.
Qed.

Local Open Scope baire_scope.
Lemma scnt_cont Q A Q' A' (F: (Q -> A) ->> (Q' -> A')):
  Q \is_countable -> F \is_sequentially_continuous -> F \is_continuous.
Proof.
  move => [cnt' [sing cotot]].
  case: (classic (inhabited Q)) => [[someq] | neg]; last first.
  - move => scnt phi Fphi val; exists (fun _ => nil) => q' phi' coin Fphi' val'.
    suff lmt: Fphi \is_limit_of (cnst Fphi').
    + by have [n prp]:= lmt [:: q']; have []//:= prp n.
    apply/scnt/val; last by move => n; apply/val'.
    move => L; exists 0 => m ineq.
    elim: L => // q.
    by exfalso; apply/neg/inhabits/q.
  have [cnt icf]:= exists_choice cnt' someq.
  have sur: cnt \is_surjective.
  - move => q; have [n val]:= cotot q.
    by exists n; apply/sing/val/icf/val.
  have [sec ms]:= exists_minsec sur.  
  move => scnt phi Fphi val.
  suff: forall q', exists L, certificate F L phi q' (Fphi q') by apply/choice.
  move => q'.
  apply/not_all_not_ex => prp.
  have /choice [phin phinprp]: forall n, exists psi,
        phi \and psi \coincide_on (iseg cnt n)
        /\
        psi \from dom F
        /\
        forall Fpsi, F psi Fpsi -> Fpsi q' <> Fphi q'.
  - move => n.
    have /not_all_ex_not [psi cnd]:= prp (iseg cnt n).
    exists psi.
    split; first exact/(not_imply_elim _ _ cnd).
    split => [ | Fpsi val' eq].
    + have /not_all_ex_not [Fpsi cnd']:= (not_imply_elim2 _ _ cnd).
      by exists Fpsi; apply/(not_imply_elim _ _ cnd').
    apply/cnd => coin Fpsi' val''.
    by rewrite (scnt_sing scnt val'' val').
  have lmt: phi \is_limit_of phin.
  - move => L; exists (max_elt sec L) => m ineq.
    apply/coin_subl/(phinprp m).1.
    exact/subl_trans/iseg_subl/ineq/iseg_melt.
  have /choice [Fphin lmts]: forall n, exists Fphi, F (phin n) Fphi.
  - by move => n; have [_ []]:= phinprp n.
  have [N eq]:= scnt phi phin Fphin Fphi lmt lmts val [:: q'].
  have [_ [_ prp']]:= phinprp N.
  apply/prp'; first exact/lmts.
  by have []//:= eq N.
Qed.
