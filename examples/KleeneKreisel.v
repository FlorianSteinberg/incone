From mathcomp Require Import all_ssreflect.
From incone Require Import all_cs.

(* Let's assume we are interested in operating on operators on baire space. For instance one may
   want to consider operators such as *)
Definition F (f: nat -> nat) (n: nat) := f n + f 0.
Definition F' (f: nat -> nat) (n: nat) := f (f n).
(* as input to a computations. Since these operators are continuous, they can be represented by a
   Kleene-Kreisel associate. The construction the library uses is actually slightly different,
   so lets take a slightly more detailed look. The above operator is of the type
   F: (nat -> nat) -> (nat -> nat), and here the last brackets are not strictly necessary since
   everything is total. However, partial operators can be handled and they will always be partial
   in the sense indicated by the bracketing, i.e they return a total function. First off, the
   library types the in and outputs, the typing is also usefull to keep track. So lets assume
   that we are interested in operators G: (Q -> A) -> (Q' -> A'). An associate of such an operator
   will be a function psi: seq A * Q' -> seq Q + A'. The idea is that for each fixed q', the
   associate specifies how an operator acts on a finite approximation L of the input function.
   If on input (L, q') the function psi returns an inr a, this is interpreted as a being the value
   of G phi q' for any phi whose return-values are consistent with the information from the list L.
   If it returns inl K with K a list of elements from Q, this is interpreted as indication that
   L did not contain enough information and that it should be extended by the values of the
   functional input on K, i.e. the associate expects to be called again with the updated input
   (map phi K ++ L, q').
   The best way to understand this is probably an example. To help with parsing let us first
   introduce some notations: *)
Notation pose_queries := inr.
Notation return_value := inl.

(* I claim that the following defines an associate of the operator F above: *)
Definition psi_F (KLn: seq (nat * nat) * nat) :=
  let KL := KLn.1 in
  let n := KLn.2 in
  if KL is nil then pose_queries [:: n; 0] else return_value (head (0,0) KL).2.
(* For F' the associate looks somewhat more complicated, since it is necessary to do ask queries
   depending on the return-value of previous queries. I claim that the following works: *)
Definition psi_F' (KLn: seq (nat * nat) * nat) :=
  let KL := KLn.1 in
  let n := KLn.2 in
  if KL is [:: nffn; fn] then return_value nffn.2
  else if KL is [:: nfn] then pose_queries [::nfn.2]
       else pose_queries [::KLn.2].

(* As should be clear from the description given above, an associate must be iterated to reproduce
   The value of its operator. An unbounded and possibly divergent iteration can not be done in coq
   but the function named U can do a arbitrary but bounded number of iterations. In case the
   specified number of inputs is not sufficient U psi_F f n will return None, if it is it will
   return Some F f n, Let's say we want to execute F on the following input: *)
Definition f n := n * n + 5 * n + 7.
Compute U psi_F f (0,8).
Compute U psi_F f (1,8).
Compute U psi_F f (2,8).

Compute U psi_F' f (0,8).
Compute U psi_F' f (1,8).
Compute U psi_F' f (2,8).
Compute U psi_F' f (3,8).
  
(* To prove correctness of the associate we can use relational semantics. An operator F is assigned
   the relation, or multivalued function F2MF F: (Q -> A) -> (Q' -> A') -> Prop specified by
   (F2MF F) f Ff <-> F f = Ff. For such a binary relation that is supposed to be interpreted
   as a multifunction we use the notation (Q -> A) ->> (Q' -> A'). Note that U psi_F has
   type nat -> (Q -> A) -> Q' -> option A' and that the way we interpreted the funciton values
   makes it reasonable to assign it the multivalued function \F_(U psi_F): (Q -> A) ->> (Q' -> A')
   specified by \F_(U psi_F) f Ff <-> forall q', exists n, U psi_F n q' = Some (Ff q').
   Finally note that =~= is an abreviation for the appropriate equality of multivalued funciton
   and it should become clear, that the following lemma indeed states that psi_F is an associate
   of F. *)

Lemma associate_psi_F':
  \F_(U psi_F') =~= F2MF F'.
Proof.
  split => [ass | <- n]; last by exists 3; rewrite /U/F'/=.
  apply/functional_extensionality => n.
  have [[// | [// | [// | k]]]]:= ass n.  
  suff ->: U psi_F' s (k.+3, n) = Some (F' s n) by case.
  have /mon_spec prp:= @U_mon _ _ _ _ psi_F'.
  exact/(prp _ _ _ 3).
Qed.
(* The detailed specification of U can be found in the lemma U_val_spec and by unfolding the
   definitions of the involved operations (operator is what \F_(_) is a notation for) *)
Check U_val_spec.
Print communication.
Print consistent.
Print operator.

(* A function for tracking the evaluation of an associate is "gather_queries", which will
   return the accumulated queries to the functional input afther n loops through U and
   inputs that the associate was run on and be constant afterwards. *)
Compute gather_queries psi_F f (0,8).
Compute gather_queries psi_F f (1,8).
Compute gather_queries psi_F f (100,8).

Compute gather_queries psi_F' f (0,8).
Compute gather_queries psi_F' f (1,8).
Compute gather_queries psi_F' f (2,8).

(* It is also possible to do higher order stuff. *)
Definition Phi F: nat -> nat:= F (@id nat).

Definition psi_Phi := @D nat nat nat nat id.

Lemma associate_psi_Phi:
  forall psi F, \F_(U psi) =~= F2MF F -> \F_(U psi_Phi) psi === singleton (Phi F).
Proof.
  rewrite /Phi /psi_Phi => psi F eq Fphi.
  by split => [/D_spec val | <-]; [apply/eq | apply/D_spec; rewrite eq].
Qed.
