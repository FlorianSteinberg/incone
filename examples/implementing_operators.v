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
Require Import all_names all_cmpt metric_names search classical_cont classical_count continuous_machines.

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
    let m := ord_search (fun k => phi k == mn.2) mn.1 in
    if m < mn.1 then Some m else None. 

  Lemma minsecM_spec: minsec =~= \F_minsecM.
  Proof.
    rewrite /minsecM => phi sec.
    split => [[cncl min] n | val].
    - exists (sec n).+1; rewrite /minsecM /=.
      case: ifP => /osrch_ltP; last first.
      + by move => fls; exfalso; apply/fls; exists (Ordinal (ltnSn (sec n))); apply/eqP => /=.
      move => [[/=m ineq] eq]; f_equal.
      apply/eqP; rewrite eqn_leq; apply/andP; split; first exact/osrch_min/eqP/cncl.
      exact/min/eqP/(@search_correct_le (fun k => phi k == n))/leq_trans/ineq/leqnSn.
    split => [n | _ m <-]; last by have[k]:= val (phi m); case:ifP=>//= _ [<-]; apply/osrch_min.
    have [k]:= val n; case: ifP => //= /osrch_ltP [[/=m ineq] eq] [<-].
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
    rewrite /secM /= => phi sec.
    split => [val | [cncl min] n].
    - split => [n | _ n <-].
      + by have [m] := val n; rewrite sfrst_osrch; case: ifP => //= /eqP eq [<-].
      have [m]:= val (phi n); rewrite sfrst_osrch; case: ifP => //= /eqP _ [<-].
      by apply/osrch_min; rewrite eq_refl.
    exists (sec n).
    rewrite sfrst_osrch /=.
    rewrite (@osrch_ext _ (fun k => phi k == n)) => [ | [/=m _]]; last by case: ifP.
    case: ifP => [eq | /negP fls]; last first.
    - by exfalso; apply/fls; apply/(@search_correct_le (fun k => phi k == n))/min/cncl/eqP/cncl.
    f_equal; apply/eqP.
    rewrite eqn_leq; apply/andP; split; first exact/osrch_le.
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

From incone Require Import all_cs cantor_space.
Section continuous_search.
  (**
     As an example that uses represented spaces, let us check the search operator that on cantor
     space as it was considered in the file "cantor_space.v". Cantor space is the countable
     product space of bool as discrete space.
   **)
  Print Cantor.

  (** This means that a description of an element of Cantor space is a function from nat * unit -> bool.
   **)
  Compute descriptions B_ Cantor.
  (**
     Here, the additional unit type comes from the construction of the discrete space bool where
     the only description of b is the constant function unit -> bool with value b.
     The function we are intersted in was defined in the cantor_space file as follows:
   **)
  Print nz_bool_p.

  (** 
      Note that this gives our realizer the type (nat * unit -> bool) -> unit -> bool and recall
      that the corresponding machine will have an additional natural number input.
      Instead of doing the implementation in two steps as above, we will rely on search functions
      that are defined in the incone library.
   **)
  Definition zeroM phi (ntt:nat* unit) :=
    match direct_search id (fun n => phi (n, tt) == true) ntt.1 with
    | Some n => Some true
    | None => None
    end.

  Lemma zeroM_spec: \F_zeroM \solves nz_bool_p.
  Proof.
    move => phi chi phinchi [b [n [/eqP val eq]]].
    split.
    - exists (fun _ => true); case.
      exists n; rewrite /zeroM dsrch_osrch /=.
      have -> //:= @osrch_correct_le (fun n => phi (n, tt) == true) n.
      by rewrite phinchi.
    move => Fphi val'.
    exists true; split.
    - by exists n; split => //; apply/eqP.
    have [m /=] := val' tt.
    by rewrite /zeroM; case ds: direct_search => //; case => <-.
  Qed.

  (**
     From this an implementation as a partial function in coq can be recovered. However, from the
     point of view of computable analysis, this set of information is still not satisfactory.
     I.e. a name of nz_bool_p in the function space representation contains continuity information
     and can thus not be recovered from an M fulfilling the specification above alone. To be able
     to recover a name we need to provide evidence that the M we implemented is indeed continuous.
     We do this by specifying a modulus of continuity of M:
   **)
  Definition zeromu phi (ntt: nat * unit) :=
    map (fun n => (n, tt)) (init_seg (nat_search (fun n => phi (n, tt) == true) ntt.1).+1).

  Lemma zero_mod: zeromu \modulus_function_for zeroM.
  Proof.
    move => phi [n []] psi /coin_agre coin.
    rewrite /zeroM !dsrch_nsrch /=.
    have -> //:= @nsrch_cont (fun n => phi (n, tt) == true) (fun n => psi (n, tt) == true) n.
    move => k ineq.
    have  -> //:= coin (k, tt).
    rewrite /zeromu classical_mach.map_iseg.
    by apply/L2SS_iseg; exists k; split => //.
  Qed.

  (**
     In addition to the above specification we need that the modulus is self-modulating.
   **)
  
  Lemma zero_modmod: zeromu \modulus_function_for zeromu.
  Proof.
    move => phi [n []] psi /coin_agre coin.
    rewrite /zeromu /=.
    have -> //:= @nsrch_cont (fun n => phi (n, tt) == true) (fun n => psi (n, tt) == true) n.
    move => k ineq.
    have  -> //:= coin (k, tt).
    rewrite /zeromu classical_mach.map_iseg.
    by apply/L2SS_iseg; exists k; split => //.
  Qed.

  (**
     The above set of information can be packaged to a "continuous_machine".
   **)
  Definition zero_machine:= Build_continuous_machine zero_mod zero_modmod :
  continuous_machine _ _ _ (queries cs_bool) (replies cs_bool).
  
  (**
     The pair (M, mu) provides enough information to automatically generate a description of the
     function via a protocoll of how to exchange finite chunks of information.
   **)

  Definition nz_bool_p_ass:=
    construct_associate (eq_dec:= @eqT_eqdec _) (true: replies Cantor) zero_machine.
  (**
     This name can be evaluated using the universal U from the library.
   **)
  Compute (U nz_bool_p_ass) (fun n => if n == (10, tt) then true else false) (5, tt).
  Compute (U nz_bool_p_ass) (fun n => if n == (10, tt) then true else false) (12, tt).

  (**
     It is prooven in the library, that this reproduces the values of \F_M
   **)
  Check cass_spec.
  (**
     However, the performance of M and U may differ. While in the case we just considered, the
     performance of U is worse as no value is accessed twice, it may well happen that it performs
     better as a careless implementation of M may lead to exessive recomputation and the
     construction of the associate acts as a caching procedure.
   **)
  Compute zeroM (fun n => if n == (30, tt) then true else false) (32, tt).
  Compute (U nz_bool_p_ass) (fun n => if n == (30, tt) then true else false) (32, tt).

  (**
     Also note that the duration of the computation is determined by the inputs and not by the
     fuel:
   **)
  Compute (U nz_bool_p_ass) (fun n => if n == (10, tt) then true else false) (100, tt).

  (**
     An easy way to make the associate more competitive is to do bigger steps in the access to
     the functional input. For instance one can double the initial segment to look at each time
     the effort parameter n is increased by one.
   **)
     
  Definition zeroM' phi (ntt:nat* unit) :=
    match direct_search id (fun n => phi (n, tt) == true) (2^ntt.1).+1 with
    | Some n => Some true
    | None => None
    end.

  Lemma pwr2lt n: (n < 2^n.+1)%nat.
  Proof.
    elim: n => // n ih.
    have lt: (n.+1 < (2 ^ n.+1).+1)%nat by trivial.
    apply/leq_trans; first exact/lt.
    rewrite [X in _ < X]Nat.pow_succ_r; last by lia.
    rewrite -[X in X < _]mul1n.
    suff: 1 * 2 ^ n.+1 < 2 * 2 ^ n.+1 by trivial.
    rewrite ltn_mul2r; apply/andP; split => //; apply/leP.
    by have:= Nat.pow_nonzero 2 n.+1; lia.
  Qed.

  Lemma pwr2le n: (n <= (2^n).+1)%nat.
  Proof. by case: n => // n; apply/leq_trans; first exact/pwr2lt. Qed.
  
  Lemma zeroM'_spec: \F_zeroM' \solves nz_bool_p.
  Proof.
    move => phi chi phinchi [b [n [/eqP val eq]]].
    split.
    - exists (fun _ => true); case.
      exists n; rewrite /zeroM' dsrch_osrch /=.
      have -> //:= @osrch_correct_le (fun n => phi (n, tt) == true) n; last exact/pwr2le.
      by rewrite phinchi.
    move => Fphi val'.
    exists true; split.
    - by exists n; split => //; apply/eqP.
    have [m /=] := val' tt.
    by rewrite /zeroM'; case ds: direct_search => //; case => <-.
  Qed.

  Definition zeromu' phi (ntt: nat * unit) :=
    map (fun n => (n, tt)) (init_seg (nat_search (fun n => phi (n, tt) == true) (2^ntt.1).+1).+1).

  Lemma zero_mod': zeromu' \modulus_function_for zeroM'.
  Proof.
    move => phi [n []] psi /coin_agre coin.
    rewrite /zeroM' !dsrch_nsrch /=.
    have -> //:= @nsrch_cont (fun n => phi (n, tt) == true) (fun n => psi (n, tt) == true) (2^n).+1.
    move => k ineq.
    have  -> //:= coin (k, tt).
    rewrite /zeromu' classical_mach.map_iseg.
    by apply/L2SS_iseg; exists k; split => //.
  Qed.

  (**
     In addition to the above specification we need that the modulus is self-modulating.
   **)
  
  Lemma zero_modmod': zeromu' \modulus_function_for zeromu'.
  Proof.
    move => phi [n []] psi /coin_agre coin.
    rewrite /zeromu' /=.
    have -> //:= @nsrch_cont (fun n => phi (n, tt) == true) (fun n => psi (n, tt) == true) (2^n).+1.
    move => k ineq.
    have  -> //:= coin (k, tt).
    rewrite /zeromu' classical_mach.map_iseg.
    by apply/L2SS_iseg; exists k; split => //.
  Qed.

  Definition zero_machine':= Build_continuous_machine zero_mod' zero_modmod' :
  continuous_machine _ _ _ (queries cs_bool) (replies cs_bool).

  Definition nz_bool_p_ass':= construct_associate (eq_dec:= @eqT_eqdec _) (true: replies Cantor) zero_machine'.

  Compute zeroM (fun n => if n == (30, tt) then true else false) (32, tt).
  Compute (U nz_bool_p_ass') (fun n => if n == (30, tt) then true else false) (32, tt).

  (**
     In general, the overhead should be expected to be linear in the time needed for computation,
     but quadratic in the number of values that need to be accessed from the functional input and
     cubic in the number of back and forth of answers and questions needed. These are only numbers
     for the implementation used in the library and they could be further improved by use of more
     efficient algorithms for operations on lists.
   **)
End continuous_search.

