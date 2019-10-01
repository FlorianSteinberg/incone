From mathcomp Require Import ssreflect ssrnat ssrbool choice eqtype ssrfun seq.
From mf Require Import all_mf classical_mf.
Require Import iseg sets search count axioms.
Require Import ClassicalChoice ChoiceFacts ConstructiveEpsilon.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.  

Lemma subs_count Q (P: mf_set.subset Q): Q \is_countable -> {q: Q | P q} \is_countable.
Proof.
  move => [cnt [sing sur]]; exists (make_mf (fun n q => cnt n (sval q))).
  by split => [n q q' val val'  | q]; [apply/eq_sub/sing/val'/val | apply/sur].
Qed.

Lemma well_order_nat_choice (P : nat -> Prop):
  FunctionalCountableChoice_on bool ->
  (exists n, P n) -> exists n, P n /\ forall m, P m -> n <= m.
Proof.
  move => choice.
  pose R:= (fun n b => P n <-> is_true b).
  have [ | p prop]:= @choice R.
    by move => n; case: (classic (P n)) => pn; [exists true|exists false]; split.
  move => [m Pm].
  have ex: exists n, p n by exists m; apply prop.
  have [n [pn min]]:= (worder_nat ex).
  by exists n; split => [ | k Pk ]; [ | apply min]; apply prop.
Qed.

Lemma well_order_nat (P : nat -> Prop):
  (exists n, P n) -> exists n, P n /\ forall m, P m -> n <= m.
Proof. exact/well_order_nat_choice/countable_choice/nat_count. Qed.

Lemma count_enum_choice T: FunctionalCountableChoice_on (option T) -> T \is_countable -> enumerable T.
Proof.
  move => choice [R [sing tot]].
  have [ | cnt tight]:= exists_pchoice R; first exact/choice.
  exists cnt.
  apply/pf2MF_cotot => t.
  have [n val] := tot t.
  have [ | [t' eq] subs]:= tight n; first by exists t.
  exists n; move: eq.
  rewrite /=; case E: (cnt n) => [t'' | ]// _.
  by apply/sing/val/subs => /=; rewrite E.
Qed.

Lemma count_enum T: T \is_countable -> enumerable T.
Proof. exact/count_enum_choice/countable_choice/nat_count. Qed.  
  
Lemma minsec_eqdec Q cnt sec:
  minimal_section Q cnt sec -> forall (q q': Q), {q = q'} + {~ q = q'}.
Proof.
  move => [cncl min] q q'.
  case E: (sec q == sec q').
  - left; move: E => /eqP eq.
    by have <-:= cncl q; rewrite eq.
  right => eq.
  suff: false by trivial.
  by rewrite -E eq; apply/eqP.
Qed.

Lemma minsec_eqT Q cnt sec:
  minimal_section Q cnt sec -> exists P: Equality.class_of Q, True.
Proof.
  move => /minsec_eqdec eqdec.
  pose eq := fun q q' => match eqdec q q' with
                         | left _ => true
                         | right _ => false
                         end.  
  unshelve eexists (@Equality.Mixin _ eq _) => //.
  by move => x y; apply: (iffP idP) => [ | xy]; rewrite /eq; case:(eqdec x y) => //.
Qed.

Lemma enum_eqT_countMixin (Q: eqType): enumerable Q -> exists P: Countable.mixin_of Q, True.
Proof.
  move => [cnt sur].
  pose cnt' := (fun n => match n with | 0 => None | S n => cnt n end).
  have sur': cnt' \is_surjective by move => [q | ]; [have [n]:= sur q; exists n.+1 | exists 0].
  have [sec' [cncl min]] := exists_minsec_eqT sur'.
  unshelve eexists (@Countable.Mixin _ (sec' \o_f Some) cnt' _) => //.
  by move => x /=; rewrite cncl.
Qed.

Lemma enum_eqT_countClass (Q: eqType): enumerable Q -> exists P : Countable.class_of Q, True.
Proof.
  move=> /enum_eqT_countMixin[cmQ _].
  set QchoiceType := ChoiceType Q (CountChoiceMixin cmQ).
  by exists (Countable.class (CountType QchoiceType cmQ)).
Qed.

Lemma count_eqT_countMixin (Q: eqType) : Q \is_countable -> exists P : Countable.mixin_of Q, True.
Proof. by move => /count_enum; apply/enum_eqT_countMixin. Qed.
  
Lemma count_eqT_countClass (Q: eqType): Q \is_countable -> exists P : Countable.class_of Q, True.
Proof.
  move=> /count_eqT_countMixin[cmQ _].
  set QchoiceType := ChoiceType Q (CountChoiceMixin cmQ).
  by exists (Countable.class (CountType QchoiceType cmQ)).
Qed.

Lemma count_iff_enum Q: Q \is_countable <-> enumerable Q.
Proof. by split; [apply/count_enum | apply/enum_count]. Qed.  
  
Lemma classic_eqClass Q : FunctionalChoice_on (Q * Q) bool -> exists P : Equality.class_of Q, True.
Proof.
  move => choice.
  pose R q b:= (q.1 = q.2 :> Q) <-> (b = true).
  suff /choice [eq eqP]: forall q, exists b, R q b.
  - unshelve eexists (@Equality.Mixin _ (fun x y => eq (x, y)) _) => //.
    by move=> x y; apply: (iffP idP) => [/eqP//|->]; apply/eqP.
  by move=> q; case: (classic (q.1 = q.2)) => ass; [exists true|exists false].
Qed.

Lemma exists_minsec Q (cnt: nat -> Q):
  cnt \is_surjective -> exists sec, minimal_section Q cnt sec.
Proof.
  move => sur.
  have choice: FunctionalChoice_on (Q * Q) bool.
  - by apply countable_choice; apply prod_count; apply/enum_count/(inh_enum (cnt 0)); exists cnt.
  have [eqC _]:= classic_eqClass choice.
  pose eqQ:= @Equality.Pack Q eqC.
  by have := @exists_minsec_eqT eqQ cnt sur.
Qed.

Lemma count_eqT_choice (Q: eqType) T: Q \is_countable ->
                                      inhabited T \/ inhabited Q -> FunctionalChoice_on Q T.
Proof.
  have nat_choice: FunctionalCountableChoice by apply/countable_choice/nat_count.
  case: (classic (inhabited Q)) => [[someq] count impl F tot | ninh count [[somet] | inh] F tot].
  - move: count => /count_enum/(inh_enum someq) [cnt sur].
    pose R n t:= F (cnt n) t.
    have [n | f fprp]:= nat_choice _ R; first by have [t val]:= tot (cnt n); exists t.
    have [sec [cncl min]]:= exists_minsec_eqT sur.
    exists (f \o_f sec) => q /=.
    by have:= fprp (sec q); rewrite /R cncl.
  - by exists (fun _ => somet) => q; exfalso; apply/ninh/inhabits/q.
  by exfalso; apply/ninh.
Qed.

Lemma count_inh_choice_eqdec Q (someq: Q): Q \is_countable ->
                            (forall T, FunctionalChoice_on Q T)
                            <->
                            exists P: forall (q q': Q), decidable (q = q'), True.
Proof.
  move => count; split => [choice | [/eqdec_eqClass eCQ _] T]; first exact/count_choice_eqdec.
  pose eTQ:= EqType Q eCQ.
  apply (@count_eqT_choice eTQ); first exact/count.
  by right; apply/inhabits/someq.
Qed.
