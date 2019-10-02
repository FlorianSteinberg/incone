(**
   This file contains basics about the notion of continuity of operators on Baire space that the
   incone library uses.
**)
Require Import Psatz.
From mathcomp Require Import all_ssreflect.
From metric Require Import all_metric.
Require Import all_names metric_names search classical_cont classical_count.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope name_scope.
Section basic_continuity.
  Context (Q A Q' A': Type).
  Notation B := (nat -> nat).
  (**
     We are interested in continuity of operators f of type B -> B and partial such operators.
     Continuity of such an operator is defined to mean that for any input function phi
     there exists a function Lf that asigns to each input n to f phi a list Lf n of natural
     numbers such that f phi n does not change if we only change phi outside of this list.
     The formal definition does not make the restriction that B = nat -> nat but allows each
     copy of the natural numbers to be a distinct type (that will often be assumed countable).
   **)
  Print continuous_function.
  (**
     An operator that can be defined directly in coq is usually readily be proven continuous,
     as Lf n can be chosen as the elements whose values are mentioned in the definition. Let's
     take a look at the two examples that are also considered in the Kleene-Kreisel example:
   **)
  Definition F0 phi n := phi n + phi 0.
  Definition F1 (phi: B) n := phi (phi n).
 
  Lemma contF0 : F0 \is_continuous_function.
  Proof.
    rewrite /F0 => phi.
    by exists (fun n => [::n; 0]) => m psi [-> [->]].
  Qed.

  Lemma contF1 : F1 \is_continuous_function.
  Proof.
    rewrite/F1 => phi.
    by exists (fun n => [:: n; phi n]) => m psi [-> [->]].
  Qed.
  (** 
      More interesting examples are continuous partial operators that do not have a total extension
      In this case it is convenient to use specifications since partial operators can not be
      expressed in coq and the usual way to identify a partial function with a function to the
      option type does not work too well in this setting (it kind of implies that the domain is
      decidable and in this case it is usually far from being decidable).
   **)
  Print pdom_dec.
  (**
     Standard examples of continuous operators whose maximal domain is not decidable include
     the search operator and the operator that returns minimal sections. These are discussed in
     the file "implementing_operators.v" in more detail. For now, let us use the tools provided
     by the library to verify that the notion of continuity above coincides with the standard
     notions in the case where Q = A = nat. For this specific case, the following definition
     can be found in many sources:
   **)

  Definition baire_continuous (f: B -> B):=
    forall phi n, exists m, forall phi', {in init_seg m, phi =1 phi'} -> {in init_seg n, f phi =1 f phi'}.

  (**
     It is not too difficult to prove that this is equivalent to the continuity used in the library
     directly, however, here we proceed by going through a metric on Baire-space. To construct a
     metric space structure on Baire-space we need to construct a metric. There is an appropriate
     construction provided in the library:
   **)
  Check baire_metric.
  Check baire_distance.
  (**
     Where we should choose Q to be the natural numbers, the enumeration to be the identity and
     have to provide a proof that the identity is a surjective function.
   **)
  
  Canonical metric_baire: MetricSpace.
    exists (nat -> nat) (@baire_distance _ (@id nat) nat_eqType).
    by apply/baire_metric => n; exists n.
  Defined.

  (**
     The tools we need for verifying that continuity with respect to the above metric structure
     is equivalent to the definition we listed above are available in the libraries. Specifically
     we need that elements are close with respect to the baire_distance iff the coincide on
     initial segments, and that for metric continuity it suffices to consider epsilons and deltas
     of the form /2^n. I.e.:
   **)
  Check dst_coin.
  Check cont_tpmn.
  
  Lemma mcnt_spec f: baire_continuous f <-> (f \is_continuous)%metric.
  Proof.
    split => [cont phi | /cont_tpmn cont phi n].
    - apply/cntp_tpmn => n.
      have [m mprp]:= cont phi n.
      exists m => psi /dst_coin /coin_funeq coin.
      exact/dst_coin/coin_funeq/mprp.
    have [m mprp]:= cont phi n.
    exists m => psi /coin_funeq/dst_coin dst.
    exact/coin_funeq/dst_coin/mprp.
  Qed.

  (**
     Now it is easy to compare to the notion of continuity that we used in the begining of the
     section, as a full comparison of metric and this notion is part of the incone library.
   **)
  Check cont_f_cont.

  Lemma cont_spec (f: B -> B): f \is_continuous_function <-> baire_continuous f.
  Proof.
    rewrite mcnt_spec.
    apply/cont_f_cont.
    by split => [ | n _ ->]; last exact/leqnn.
  Qed.

  (* The same can be done for partial operators: *)
  Definition baire_pcontinuous (f: partial_function B B) := forall phi n, exists m, forall psi,
          {in init_seg m, sval phi =1 sval psi} -> {in init_seg n, f phi =1 f psi}.

  Lemma mcnt_pspec f: baire_pcontinuous f <->
                      ((f: subspace (domain f) -> metric_baire) \is_continuous)%metric.
  Proof.
    split => [cont phi | /cont_tpmn cont phi n].
    - apply/(@cntp_tpmn (subspace (domain f))) => n.
      have [m mprp]:= cont phi n.
      exists m => psi /dst_coin /coin_funeq coin.
      exact/dst_coin/coin_funeq/mprp.
    have [m mprp]:= cont phi n.
    exists m => psi /coin_funeq/dst_coin dst.
    exact/coin_funeq/dst_coin/mprp.
  Qed.

  Lemma pcont_spec (f: partial_function B B): f \is_continuous <-> baire_pcontinuous f.
  Proof.
    rewrite mcnt_pspec.
    apply/cont_pcont.
    by split => //= m n <-.
  Qed.
End basic_continuity.
