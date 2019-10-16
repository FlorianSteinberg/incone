(** 
    This file considers two partial operators that have non-decidable domain and can not
    be continuously extended to operators that do. This is a very common situation in computable
    analysis as realizers of functions between represented spaces are often of this form
    (division of real numbers in the Cauchy representation is a good example). In coq, such
    functions are problematic as dependent types become necessary for describing them properly.
    The incone library provides some machinery for working in this setting without getting too
    involved with complicated parts of coq's type-system and this file outlines how to use this
    machinery.
 **)
Require Import Psatz.
From mathcomp Require Import all_ssreflect.
From metric Require Import all_metric.
Require Import all_names all_cmpt metric_names search classical_cont classical_count.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope name_scope.
Notation B:= (nat -> nat).
  (** 
      There exist interesting continuous partial operators on Baire-space that do not have any
      extension whose domain is decidable. As coq functions are always total, these operators can
      not be directly implemented. One of the standard ways of dealing with partiality in coq is
      by using functions to an option type and not well suited for this setting as it renders the
      domain of the function decidable.
   **)
  Check pdom_dec.
  (** Another approach is to modify the input type to be a dependent type. **)
  Print partial_function.
  (**
     Proper handling of dependent types requires considerable expertise and even then often leads
     to complications in proofs. Thus, the incone library often opts for not using this approach
     and indstead operates on relational specifications directly. To add computational content
     to this setting, partial computable functions are introduced using the not too uncommon
     fuel based approach. A fueled algorithm computing a partial operator is often fairly straight
     forward to write down and an implementation using dependent types can be recovered. We
     present this machinery along the two examples of computing the minimal section of an element
     of Baire-space and searching for the first zero. Due to the typing being more in line with 
     incone we start with minimal sections.
   **)

Section minimal_sections.
  (**
     A definition of what it means to be a minimal section is included in the incone library.
   **)
  Print minimal_section.
  (**
     Setting Q:= nat specializes this to a multi-function on the Baire space that we want to
     investigate closer here:
   **)
  Notation minsec:= (minimal_section nat).
  (**
     The domain of this operator consists exactly of the surjective functions and a proof can be
     given by using the existence theorem for minimal sections provided by the incone library.
   **)
  Lemma dom_minsec: dom minsec === surjectives nat nat.
  Proof.
    split => [[sec [cncl min]] q| sur].
    - by exists (sec q); apply/cncl.
    exact/exists_minsec.
  Qed.

  (** While the operator is not total, it still is continuous. **)
  Lemma minsec_cont: minsec \is_continuous.
  Proof.
    move => phi sec [cncl min].
    exists (fun n => init_seg (sec n).+1) => n psi /coin_agre coin sec' [cncl' min'].
    apply/eqP; rewrite eqn_leq.
    suff ineq: sec' n <= sec n.
    - apply/andP; split => //.
      apply/min; rewrite coin //.
      by apply/L2SS_iseg; exists (sec' n); split => //.    
    by apply/min'; rewrite -coin //; apply/L2SS_iseg; exists (sec n).
  Qed.

  (** Which in particular implies that the operator is singlevalued. **)
  Lemma minsec_sing: minsec \is_singlevalued.
  Proof. exact/cont_sing/minsec_cont. Qed.

  (**
     Since coq-functions are always total, the operator can not be implemented directly. However,
     it is possible to implement minsec using the operator assignment from the library i.e. to
     define a function minsecM: B -> nat * nat -> option nat such that minsec can be recovered
     through the operator assignment, i.e. such that minsec = \F_(minsecM). Where \F_ is called
     the "operator assignment" and basically follows the ideas of the fuel based approach to
     defining partial computable functions in coq:
   **)
  Print operator.

  (**
     That is, the function minsecM gets the inputs phi and n and an additional natural number
     input that can be used as a bound for something that should be an unbounded loop or search.
     If this input is to small the proceedure may abort and return an error symbol. Afterwards,
     M hast to be proven appropriate by demonstrating that for any valid inputs there exists an
     n that is sufficiently large for M to actually return something.
   **)
  Definition minsecM phi (mn: nat * nat) :=
    let m := search (fun k => phi k == mn.2) mn.1 in
    if m < mn.1 then Some m else None. 

  Lemma minsecM_spec: minsec =~= \F_minsecM.
  Proof.
    rewrite /minsecM => phi sec.
    split => [[cncl min] n | val].
    - exists (sec n).+1; rewrite /minsecM /=.
      case: ifP => /searchP; last first.
      + by move => fls; exfalso; apply/fls; exists (sec n); split; first apply/eqP.
      move => [m [eq ineq]]; f_equal.
      apply/eqP; rewrite eqn_leq; apply/andP; split; first exact/search_min/eqP/cncl.
      exact/min/eqP/(@search_correct_le (fun k => phi k == n))/leq_trans/ineq/leqnSn.
    split => [n | _ m <-]; last by have[k]:= val (phi m); case:ifP=>//= _ [<-]; apply/search_min.
    have [k]:= val n; case: ifP => //= /searchP [m [eq ineq]] [<-].
    exact/eqP/(@search_correct_le (fun k => phi k == n))/leq_trans/ineq/leqnSn.
  Qed.

  (**
     As the operator assignment is also suited for handling multivalued operations, another
     approach could have been to first define a function that produces as a specification just
     being a section without the minimality condition:
   **)
  Definition secM phi (mn: nat * nat) :=
    if phi mn.1 == mn.2 then Some mn.1 else None.  

  Lemma secM_val_spec phi sec: sec \from \F_secM phi <-> cancel sec phi.
  Proof.
    rewrite /secM; split => [val n | cncl n]; last by exists (sec n); rewrite cncl eq_refl.
    by have [m]:= val n; case: ifP => //= /eqP <- [<-].
  Qed.

  (**
     This operator can then be made singlevalued by sticking with the minimal fuel that works.
     There is an automatic proceedure for this in the incone library that is called "use_first".
     That this produces the right returnvalue in this case is due to use_first choosing the
     minimal value that works, which in our case is coincidentally the correct one.
   **)
  Lemma sfrst_secM_spec: \F_(use_first secM) =~= minsec.
  Proof.
    rewrite /secM /use_first/PhiN.use_first /= => phi sec.
    split => [val | [cncl min] n /=].
    - split => [n | _ n <-].
      + by have [m] := val n; case: ifP => //= /eqP eq [<-].
      have [m]:= val (phi n); case: ifP => //= /eqP _ [<-].
      by apply/search_min; rewrite eq_refl.
    exists (sec n).
    have <-: (fun k => phi k == n) = (fun k => if phi k == n then Some k else None).
    - by apply/functional_extensionality => k; case: ifP.
    case: ifP => [eq | /negP fls]; last first.
    - by exfalso; apply/fls; apply/(@search_correct_le (fun k => phi k == n))/min/cncl/eqP/cncl.
    f_equal; apply/eqP.
    rewrite eqn_leq; apply/andP; split; first exact/search_le.
    exact/min/eqP.
  Qed.

  (**
     In general, use_first provides a cannonical way to cut down a multivalued operation that
     was implemented using the operator assignment to a singlevalued one while preserving the
     specifications.
     An alternative proof that minsec is continuous can be obtained by specifying a modulus
     for secM (which is very simple) and automatically generating one for \F_(use_first secM).
   **)

  Lemma minsec_cont': minsec \is_continuous.
  Proof.
    rewrite -sfrst_secM_spec /secM; apply/sfrst_cntf_cont => phi.
    by exists (fun mn => [:: mn.1]); case => [m n] psi [/= <-].
  Qed.

  (** From secM, one can also obtain definition of minsec as a partial function: **)

  Definition minsecf:= get_partial_function secM.

  (** and proof that this is a correct implementation of the minsec specification: **)
  Lemma minsecf_spec: minsecf =~= minsec.
  Proof. by rewrite -sfrst_secM_spec gtpf_spec. Qed.

  (** 
      Note however, that while the values of secM and minsecM can easily be accessed inside of
      coq, the same is not true for the partial function which requires the availability of
      a proof of appropriateness of the functional input and does not fully reduce even if
      given such a proof. It does lead to the correct program when used in extraction, though.
   **)
End minimal_sections.

Section continuous_search.
  (**
     The search operator returns for an element of Baire space the first input on which the
     return value is zero. This gives the search operator the type B -> nat and to get nat
     as a return-value type of an operator we have to encode its elements as functions from the
     unit type to nat.
   **)
  Notation N := (unit -> nat).

  (** The specification of the operator minZ (minimal zero) described above is then given by: **)
  Definition min_zero := make_mf (fun phi n => phi (n tt) = 0 /\ forall m, phi m = 0 -> n tt <= m).
  (** 
      This indeed specifies a partial operator, i.e. F is singlevalued (we will prove the stronger
      statement that it is continuous below). The domain of F are the functions that vanish
      eventually:
   **)
  Lemma dom_F phi: phi \from dom min_zero <-> exists n, phi n = 0.
  Proof. by split => [[n []] | /well_order_nat [n []]]; [exists (n tt) | exists (cnst n)]. Qed.

  (** 
      To implement this operator we proceed like at the end of the last section. I.e. we first
      implement the multivalued operator that returns any zero and then select the smalles one.
   **)
  
  Definition zeroM phi (ntt:nat * unit) := if phi ntt.1 == 0 then Some ntt.1 else None.

  Lemma zeroM_val_spec phi z: \F_zeroM phi z <-> phi (z tt) = 0.
  Proof.
    rewrite /zeroM; split => [val | eq [/=]]; last by exists (z tt); rewrite eq.
    by case: (val tt) => n; case: ifP => // /eqP eq [<-].
  Qed.

  Lemma sfrst_zeroM_spec: \F_(use_first zeroM) =~= min_zero. 
  Proof.
    rewrite /zeroM /use_first /PhiN.use_first => phi z.
    split => [val | [cncl min] []].
    - have [n /=]:= val tt; case: ifP => // eq [<-]; split; first exact/eqP.
      by move => m /eqP eq'; apply/search_min; rewrite eq'.
    exists (z tt).
    have <- /=: (fun k => phi k == 0) = fun k => if phi k == 0 then Some k else None.
    - by apply/functional_extensionality => k; case: ifP.
    rewrite (@search_correct (fun k => phi k == 0)); last exact/eqP.
    f_equal; apply/eqP; rewrite eqn_leq; apply/andP; split; first exact/search_le.
    exact/min/eqP/(@search_correct (fun k => phi k == 0))/eqP.
  Qed.

  (** From this implementation, the continuity can easily be deduced. **)
  Lemma min_zero_cont: min_zero \is_continuous.
  Proof.
    rewrite -sfrst_zeroM_spec; apply/sfrst_cntf_cont => phi.
    by exists (fun ntt => [:: ntt.1]); rewrite /zeroM => ntt psi [<-].
  Qed.

  (** and here is the partial function: **)
  Definition min_zerof:= get_partial_function zeroM.

  Lemma min_zerof_spec: min_zerof =~= min_zero.
  Proof. by rewrite -sfrst_zeroM_spec gtpf_spec. Qed.
End continuous_search.
