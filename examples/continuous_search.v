(** This file considers the function that searches for the minimal input such
    that a function vanishes as an example of a continuous partial operator on
    baire space and shows that the continuity on baire spaces is equivalent to
    the traditional definition for nat -> nat. **)
Require Import Psatz.
From mathcomp Require Import all_ssreflect.
From metric Require Import all_metric.
Require Import all_names baire_metric classical_cont classical_count.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope name_scope.
Section baire_space.
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
      The standard example of such an operator is the search operator. I.e. the operator F whose
      domain are the elements of B that eventually return zero and whose value phi is the smallest
      natural number n such that phi n = 0. Following this definition, the operator F has type
      B -> nat and the continuity framework from the library is only set up to handle operators
      of the form B -> B. To circumvent this restriction we identify the natural numbers with the
      type unit -> nat to make it accessible to the continuity notion.
   **)
  Notation N := (unit -> nat).

  (**
     The specification of the operator described above is then given by:
   **)
  Definition F := make_mf (fun phi n => phi (n tt) = 0 /\ forall m, phi m = 0 -> n tt <= m).
  (**
     This indeed specifies a partial operator with the domain that we claimed it to have:
   **)
  Lemma dom_F phi: phi \from dom F <-> exists n, phi n = 0.
  Proof.
    split => [[n []] | /well_order_nat [n []]]; first by exists (n tt).
    by exists (fun _ => n).
  Qed.
  (**
     Note that it is not clear how to define the operator as a function from B to option N
     unless the equality on B is made decidable through the use of axioms. While the domain
     lemma above also uses classical reasoning, there is a difference between using axioms
     to prove specifications and using them definitionally. A more appropriate substitue for
     the option type construction in the operator setting is discussed below. But first,
     let's prove that F is continuous.
   **)

  Lemma F_cont: F \is_continuous.
  Proof.
    move => phi nf [val prp].
    exists (fun _ => init_seg (nf tt).+1); case => psi /coin_agre coin nf' [val' prp'].  
    apply/eqP; rewrite eqn_leq; apply/andP.
    split; [apply/prp'; rewrite -coin// | apply/prp]; first by apply/lstn_iseg; exists (nf tt).
    rewrite -coin // in val'.
    apply/lstn_iseg; exists (nf' tt); split => //.
    suff ineq: (nf' tt).+1 <= (nf tt).+1 by apply/ineq.
    by apply/prp'; rewrite -coin //; apply/lstn_iseg; exists (nf tt).
  Qed.

  (**
     Since the specification of F was relational, it is not immediate that the return value is
     uniquely determined. In this case it is easily checked, however, it is also true that
     any specification that can be proven continuous in the above sense is automatically
     deterministic:
   **)
  
  Lemma F_sing: F \is_singlevalued.
  Proof. exact: cont_sing F_cont. Qed.

  (**
     Consider the operator that approximates the unbounded search embodied by F by a bounded
     search and takes the depth of this search as an additional argument, i.e.
   **)
  Definition MF phi (ntt:nat * unit) :=
    let m := search (fun k => phi k == 0) ntt.1 in
    if m < ntt.1 then Some m else None. 
  (**
     This coq-function may be interpreted as a partial operator by considering n a return value
     if and only if there exists a natural number k such that M_F k phi tt = Some n.
     Actually, each coq-function of type nat -> (Q -> A) -> Q' -> option A' may be assigned a
     specification of operators of type (Q -> A) -> (Q' -> A') -> Prop in this way. There is a
     designated in- and output, i.e. the specification relation should be considered a multivalued
     function and the library uses the notation (Q -> A) ->> (Q' -> A') for this kind of
     specifications. The notation for the correspondens described above in the library is \F_(_)
     and we can prove that M_F is appropriate in this sense. The last bit we need for this is the
     appropriate equality of multivalued functions which is denoted by =~=.
   **)

  Lemma MF_val phi n m: MF phi (n,tt) = Some m -> phi m = 0.
  Proof.
    rewrite /MF.
    case ineq: (search _ n < n) => // => [[<-]].
    apply/eqP/(@search_lt (fun k => phi k == 0)).
    by rewrite ineq.
  Qed.

  Lemma MF_spec: \F_(MF) =~= F.
  Proof.
    rewrite /MF => phi Fphi /=.
    split => [prp | [/eqP val min] []].
    - move: prp (prp tt) => _ [] n eq.
      split => [ | m val]; first exact/MF_val/eq.
      case ineq: (search _ n < n) eq => // => [[<-]].
      exact/(@search_min (fun k => phi k == 0))/eqP.
    exists (Fphi tt).+1.
    have ->: search (fun k => phi k == 0) (Fphi tt).+1 < (Fphi tt).+1 by apply/search_min.    
    f_equal.
    have <- // :=(@search_eq (fun k => phi k == 0) (Fphi tt) (Fphi tt).+1).
    have /leP:= search_le (fun k => phi k == 0) (Fphi tt).
    have /eqP prp := @search_correct (fun k => phi k == 0) _ val.
    have /leP:= min (search (fun k => phi k == 0) (Fphi tt)) prp.
    lia.
  Qed.
    
  (**
     If Q and A are countable, the space Q -> A can be made a metric space in a fairly canonical
     way that reproduces the topology of pointwise convergence. There is a proof in the library
     That the notion of metric continuity and the specialized notion of continuity for baire
     spaces conicide in this case and there are proofs in the library. The statements are some-
     what involved as they have minimalized hypothesises and the handling of partial operators
     needs to really consider metric continuity on a subspace.
   **)
  Check cont_f_cont.
  Check cont_cont.

  (**
     In the concrete case where Q and A are nat, we can directly prove the characterization and
     additionally avoid mentioning metric spaces by using the tranditional description of
     continuity on Baire space that relies on initial segments.
   **)
  Lemma leq_max (F: nat -> nat) n : forall i, i < n -> F i <= \max_(i <- init_seg n) F i.
  Proof.
    elim: n => //n ih i; rewrite leq_eqVlt/= big_cons /=.
    by case /orP => [/eqP [->] | ineq]; [exact/leq_maxl | exact/leq_trans/leq_maxr/ih].
  Qed.

  (** This is the traditional description of continuity on baire space: **)
  Notation max_elt:= (max_elt id).
  Lemma cont_spec (F: B -> B): F \is_continuous_function <->
                               forall phi n, exists m, forall phi',
                                     {in init_seg m, phi =1 phi'} -> {in init_seg n, F phi =1 F phi'}.
  Proof.
    have ms: minimal_section _ id id by split => // m n ->.
    split => [cont phi n | cont].
    - have [Lf md]:= cont phi.
      set m := \max_(i <- init_seg n) max_elt (Lf i).
      exists m => psi/coin_funeq/coin_subl coin; rewrite -coin_funeq coin_agre => q lstn.
      apply/md/coin/subs_trans; first exact/iseg_melt/ms.
      exact/iseg_subl/leq_max/(@iseg_base _ id id)/lstn/ms.
    rewrite F2MF_cont_choice => [phi n | ]; last exact/countable_choice.
    have [m md]:= cont phi n.+1.
    exists (init_seg m) => psi /coin_funeq coin.
    have /coin_funeq/coin_agre prp:= md psi coin.
    by apply/prp/lstn_iseg; exists n.
  Qed.

  (* The same can be done for partial operators: *)
  Lemma PF2MF_continuous (F: B -> option B): (pf2MF F) \is_continuous <->
    forall phi psi, F phi = Some psi -> forall n, exists m,
          forall phi' psi', F phi' = some psi' -> 
	                    {in init_seg m, phi =1 phi'} -> {in init_seg n, psi =1 psi'}.
  Proof.
    have ms: minimal_section _ id id by split => // m n ->.
    split => [cont phi psi val n | cont].
    - have [ | Lf md]/=:= cont phi psi; first by rewrite val.
      set m := \max_(i <- init_seg n) max_elt (Lf i).
      exists m => phi' psi' val'/coin_funeq coin.
      apply/coin_funeq/coin_agre => k lstn; symmetry; apply/md.
      + apply/coin_subl/coin/subs_trans/iseg_subl/leq_max/iseg_base/lstn/ms.
        exact/iseg_melt/ms.
      by rewrite /= val'.
    rewrite cont_choice => phi /=; last exact/countable_choice.
    case val: (F phi) => [psi | ]// _ <- n.
    have [m md]:= cont phi psi val n.+1.
    exists (init_seg m)=> phi' /coin_funeq coin.
    case val': (F phi') => [psi' | ]// _ <-.
    have /coin_funeq/coin_agre prp:= md phi' psi' val' coin.
    by symmetry; apply/prp/lstn_iseg; exists n.
  Qed.
End baire_space.