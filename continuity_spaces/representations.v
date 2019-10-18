From mathcomp Require Import ssreflect ssrfun.
From rlzrs Require Import all_rlzrs dict data_spaces.
Require Import all_cont naming_spaces.
Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope cs_scope with cs.
Local Open Scope cs_scope.

Notation "F \is_continuous_operator" := (continuous F) (at level 30): cs_scope.
Notation "f \is_continuous_functional" := (continuous_function f) (at level 30): cs_scope.
Section representations.
  Structure represented_over (B: naming_space) X :=
    {
      representation:> B ->> X;
      surjective: representation \is_cototal;
      deterministic: representation \is_singlevalued;
    }.

  Coercion rep2dict B X (representation: represented_over B X): Dictionary B X.
  exists representation; first exact/surjective; exact/deterministic.
  Defined.

  Lemma rep_sur B X (delta: represented_over B X): delta \is_cototal.
  Proof. exact/(conv_sur delta). Qed.

  Lemma rep_sing B X (delta: represented_over B X): delta \is_singlevalued.
  Proof. by have := @answer_unique _ _ (rep2dict delta). Qed.

  Structure representation_of X :=
    {
      name_space: naming_space;
      delta:> represented_over name_space X;
    }.

  Coercion rep2enc X (delta: representation_of X): encoding_of descriptions X.
    by exists (name_space delta); apply/delta.
  Defined.

  Definition enc2rep X (delta: encoding_of descriptions X): representation_of X.
    exists (data delta); exists (data_spaces.delta delta); try exact/(conv_sur delta).
    exact/(@answer_unique _ _ delta).
  Defined.
  
  Definition solution_wrt
             (B B': naming_space) X X' (delta: B ->> X) (delta': B' ->> X') (f: X ->> X') F:=
  f \realized_by F \wrt delta \and delta'.

  Definition has_continuous_solution_wrt
      (B B': naming_space) X X' (delta: B ->> X) (delta': B' ->> X') (f: X ->> X') :=
    exists F, F \is_continuous_operator /\ solution_wrt delta delta' f F. 

  Definition continuous_wrt (B B': naming_space) X X' (delta: B ->> X) (delta': B' ->> X') f :=
    has_continuous_solution_wrt delta delta' (F2MF f).

  Notation hcr_wrt delta delta' f:= (has_continuous_solution_wrt delta delta' (F2MF f)).

  Local Notation "delta '\translatable_to' delta'" := (hcr_wrt delta delta' id) (at level 35).
  
  Definition equivalent X (delta delta': representation_of X):=
    delta \translatable_to delta' /\  delta' \translatable_to delta.

  Canonical name_pairs:= Build_pairs_data unpair_sur.

  Canonical product_representation X X' (delta: representation_of X) (delta' : representation_of X')
    := enc2rep (product_encoding name_pairs delta delta').

  Definition sum_representation X Y (delta: representation_of X) (delta': representation_of Y):
    representation_of (X + Y).
  exists (sum_names (name_space delta) (name_space delta')).
  exists ((delta +s+ delta') \o_R (F2MF (@slct _ _))).
  - exact/rcmp_cotot/slct_sur/fsum_cotot/rep_sur/rep_sur.
  exact/rcmp_sing/F2MF_sing/fsum_sing/rep_sing/rep_sing.
  Defined.
End representations.
Notation "delta '\equivalent_to' delta'" := (equivalent delta delta') (at level 30): cs_scope.
Notation "phi '\names' x '\wrt' delta" :=
  (delta (phi: name_space delta) x) (at level 30): cs_scope.
Notation "phi '\describes' x '\wrt' delta" :=
  (delta (phi: name_space delta) x) (at level 30): cs_scope.
