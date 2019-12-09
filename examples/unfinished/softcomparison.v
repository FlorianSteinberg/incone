(* Implementation of soft comparisons using machine composition *)
From Coquelicot Require Import Coquelicot.
From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_rlzrs.
From metric Require Import reals.
Require Import all_cs_base classical_mach.
Require Import Reals Psatz FunctionalExtensionality ClassicalChoice.
Require Import axioms all_cs cs_mtrc metric_names hyper_spaces.
Require Import continuous_machines.
Require Import monotone_machine_composition.
From metric Require Import all_metric reals standard Qmetric.
Require Import search.
Require Import computable_reals.
Require Import Ibounds.

(* Some helper functions we need that should be moved to another file later *)
Definition nat2csN (n : nat) := (fun (_ : unit) => n). 

(* specification of the epsilon test with multivalued functions *)
Section epsilon_test_kleenean.
(* We define a multivalued eps test to compare two real numbers
   For eps > 0, (lt_epsK x y eps) must be true if x+eps <= y and must be false if y <= x 
   otherwise it can be both true or false *)
Definition lt_epsK := (make_mf (fun (epsxy : R * (R*R)) k => (let (eps,xy) := epsxy in
                                            let (x,y) := xy in
                                             (eps > 0) /\ (x+eps <= y -> k = true_K) /\ (y <= x -> k = false_K)) /\ k <> bot_K)).

(* the domain is all triples of reals where eps > 0 *)
Lemma dom_lt_epsK x y eps: (eps, (x,y)) \from (dom lt_epsK) <-> (eps > 0). 
Proof.
  split => [ | epsgt0]; first by case => k [[kprp1 _] _].
  case  : (total_order_T x y) => [[xlty | xeqy ] | xgty].
  - exists true_K.
    split; try by auto.
    split; try by auto.
    split; try by auto;lra.
  - exists false_K.
    split; try by auto.
    split; try by auto.
    split; try by auto;lra.
  - exists false_K.
    split; try by auto.
    split; try by auto.
    split; try by auto;lra.
Qed.

(* We usually want the test in the form eps = (/ 2 ^ n) and therefore define this version, too *)
Definition lt_nK := (make_mf (fun (nxy : nat * (R*R)) k => (let (n,xy) := nxy in
                                            let (x,y) := xy in
                                              (x+(/ 2 ^ n) <= y -> k = true_K) /\ (y <= x -> k = false_K)) /\ k <> bot_K)).

(* As / 2 ^ n is always positive lt_nK is total *)
Lemma dom_lt_nk : dom lt_nK === All.
Proof.
  move => [n [x y]].
  split => // _.
  case (Rle_or_lt (x + (/2 ^ n)) y) => p.
  - exists true_K.
    split; [split |] => //.
    suff : 0 < ( / 2 ^ n) by lra.
    by apply tpmn_lt.
  exists false_K.
  split; [split |] => //.
  suff : (0 < (/ 2 ^ n)) by lra.
  by apply tpmn_lt.
Qed.

End epsilon_test_kleenean.

Section lt_n_test.
(* The previously defined lt_n test always returns true or false, thus we can define a boolean version *)

Definition lt_n := (make_mf (fun (nxy : nat * (R*R)) b => (let (n,xy) := nxy in
                                            let (x,y) := xy in
                                             (x+(/ 2 ^ n) <= y -> b = true) /\ (y <= x -> b = false)))).

(* We can write the lt_n test as composition of multivalued functions *)
Lemma lt_n_spec : lt_n =~= (F2MF B2K)\^-1 \o lt_nK.
Proof.
  move => [n [x y] b].
  split => [[P1 P2] | [P1 P2] ].
  - split => [| t [[tprp1 tprp2] tprp3]]; last by case e: t; [exists false | exists true |].
    exists (B2K b).
    rewrite /B2K /lt_nK /=.
    split; [split; last by case b | by auto ].
    by split => H; [rewrite P1| rewrite P2].
  split.
  case P1 => k [[[kprp1 kprp2] kprp3] /= kprp4 H].
  move : kprp4; rewrite /B2K kprp1; by [case b | lra].
  case P1 => k [[[kprp1 kprp2] kprp3] /= kprp4 H].
  move : kprp4; rewrite /B2K kprp2; by [case b | lra].
Qed.

End lt_n_test.


Section basic_machines.
Arguments monotone_machine {Q} {A} {Q'} {A'}.
Definition which_machine := (F2MM which_rlzrf_mu_mod which_rlzrf_mu_modmod).
Definition K_truth_machine := (F2MM K_truth_mu_mod K_truth_mu_modmod).

Lemma K2B_machine_exists : { M : monotone_machine | \F_M \solves (F2MF B2K\^-1)}.
Proof.
  set K2BcM := (Build_continuous_machine K2B_mu_mod K2B_mu_modmod).
  have mon : K2BcM \is_monotone.
  - move => phi q n /=.
    move => H.
    case e : (K2B_rlzrM phi (n,q)) => [b|] //.
    have t : (n <= n.+1)%coq_nat by lia.
    by apply (K2B_rlzrM_monotonic e t).
  have term : terminates_with K2BcM K2B_mu.
  - move => phi q' n.
    rewrite /K2B_mu.
    move => H.
    suff :  (isSome (phi (ord_search (fun m : nat => phi m) n))) by rewrite osrchS => ->.
    move : H.
    rewrite /= /K2B_rlzrM.
    by case e: (phi _) => //.
  exists (Build_monotone_machine (Build_is_monotone mon term)).
  simpl.
  apply F_K2B_rlzrM_spec.
Defined.

Definition rprj_mu B B' (phipsi : B \*_ns B') q : seq (Q_(B \*_ns B')) := [:: (inr q)]. 
Definition lprj_mu B B' (phipsi : B \*_ns B') q : seq (Q_(B \*_ns B')) := [:: (inl q)]. 

Lemma diag_machine_exists (X : cs) : {M : monotone_machine | \F_M \solves (mf_diag : X ->> _)}.
Proof.
  set mu := ((fun phi q => [:: someq;(paib q)]) : (B_(X) -> Q_(X \*_cs X) -> (seq Q_(X)))).
  have modf : mu  \modulus_function_for (fun phi => (pair (phi,phi))).
  - rewrite /paib/pair/mu => phi q psi [] /=.
    by case q => q' -> [-> _].
  have modmod: mu \modulus_function_for mu by trivial.
  exists (F2MM modf modmod).
  rewrite F2M_spec.
  rewrite F2MF_slvs => phi x phin.
  case => t /=tprp.
  exists (x,x); split; first by auto.
  exists (phi,phi).
  split; by [apply pairK | split].
Defined.

Lemma rprj_mu_mod B B' : (@rprj_mu B B') \modulus_function_for (@rprj B B').
Proof.
  by rewrite /rprj => phi q psi [] /= ->.
Qed.

Lemma rprj_mu_modmod B B' : (@rprj_mu B B') \modulus_function_for (@rprj_mu B B').
Proof.
  by rewrite /rprj_mu => phi q psi [] /=.
Qed.

Lemma lprj_mu_mod B B' : (@lprj_mu B B') \modulus_function_for (@lprj B B').
Proof.
  by rewrite /lprj => phi q psi [] /= ->.
Qed.

Lemma lprj_mu_modmod B B' : (@lprj_mu B B') \modulus_function_for (@lprj_mu B B').
Proof.
  by rewrite /lprj_mu => phi q psi [] /=.
Qed.
Definition rprjM B B' := (@F2MM  Q_(B \*_ns B') Q_(B') A_(B \*_ns B')  A_(B') (@rprj B B') _ (@rprj_mu_mod B B') (@rprj_mu_modmod B B')).
Definition lprjM B B' := (@F2MM  Q_(B \*_ns B') Q_(B) A_(B \*_ns B')  A_(B) (@lprj B B') _ (@lprj_mu_mod B B') (@lprj_mu_modmod B B')).


Lemma id_machine_exists (X : cs) : {M : monotone_machine | \F_M \solves (mf_id : X ->> X)}. 
Proof.
  set mu := (fun phi q => [:: q]) : (B_(X) -> Q_(X) -> seq Q_(X)).
  have modf : mu \modulus_function_for (ssrfun.id : B_(X)->B_(X)) by move => phi q psi [].
  have modmod : mu \modulus_function_for mu by trivial.
  exists (F2MM modf modmod).
  rewrite F2M_spec.
  apply id_rlzr.
Defined.
End basic_machines.

(* We now define realizers for the multifunctions defined above *)
Section machines.
Arguments monotone_machine {Q} {A} {Q'} {A'}.
Definition RS2CS Rc := (Build_continuity_space (representation Rc)).
Coercion RS2CS : computable_reals >-> continuity_space.
Variable (Rc : computable_reals).
Variable default : A_(Rc).
(* We often need the operation n -> / 2 ^ n so we define a machine *)
Lemma tpmn_machine : {M : monotone_machine | \F_M \realizes ((fun (n : nat) => (/ 2 ^ n)) : (nat -> Rc))}.
Proof.
  have fp : forall f, (f =~= f) by trivial.
  (* A realizer for the function n -> (1,-n)) *)
  set rlzrf := (fun (n : B_(cs_nat)) (u : (unit + unit)) => match u with
          | (inl tt) => (1, -(Z.of_nat (n tt)))%Z
           | (inr tt) => (1, -(Z.of_nat (n tt)))%Z
         end).
  have rlzrf_spec : (F2MF rlzrf) \realizes  (fun (n : nat) => (1, -(Z.of_nat n))%Z).
  - rewrite /F2MF_rlzr/rlzrf => phi q /= p [] [z1 z2] [prp1 prp2].
    split => [| Fq Fqprp]; first by exists (rlzrf phi).
    exists (1%Z,(-Z.of_nat q)%Z); split => //.
    exists (unpair Fq); split => //; rewrite <-Fqprp.
    by split => // /=; rewrite /rprj /=; rewrite <-p.
  set mu := (fun phi u => [:: tt]) : (B_(cs_nat) -> Q_(cs_Z \*_cs cs_Z) -> seq Q_(cs_nat) ).
  have rlzrf_mod : mu \modulus_function_for rlzrf by rewrite /rlzrf => phi q psi [] ->.
  have rlzrf_modmod: mu \modulus_function_for mu by trivial.
  apply /cmp_machine.
  apply ((0,0)%Z : A_(cs_Z \*_cs cs_Z)).
  apply (F2R_machine Rc).
  exists (F2MM rlzrf_mod rlzrf_modmod).
  rewrite F2M_spec.
  apply rlzrf_spec.
  rewrite F2MF_comp_F2MF /uncurry.
  rewrite <- F2MF_eq => n /=.
  by rewrite powerRZ2_neg_pos;lra.
Defined.

(* We show that there constructively exists a realizer function for the operator *)
Lemma lt_epsK_machine : {f : (monotone_machine ) | \F_f \solves (lt_epsK : Rc * (Rc * Rc) ->> cs_Kleeneans)}.
Proof.
  have fp : forall f, (f =~= f) by trivial.
  apply /(cmp_machine_tight ((false, false) : A_(cs_Sirp \*_cs cs_Sirp))).
  exists which_machine.
  rewrite F2M_spec.
  apply /which_rlzrf_spec.
  apply /(cmp_machine ((None, None) : A_(cs_Kleeneans \*_cs cs_Kleeneans))) => //.
  apply /prd_machine =>// ; try by apply false.
  exists K_truth_machine.
  rewrite F2M_spec.
  apply Ktruth_rlzr_spec.
  exists K_truth_machine.
  rewrite F2M_spec.
  apply Ktruth_rlzr_spec.
  apply /cmp_machine => //.
  apply (((default, default), (default, default)) : A_((Rc \*_cs Rc) \*_cs (Rc \*_cs Rc))).
  apply /prd_machine => //; try by apply None.
  apply (ltk_machine Rc).
  apply (ltk_machine Rc).
  apply /cmp_machine => //.
  apply (((default, (default, default)), (default, (default, default))) : A_((Rc \*_cs (Rc \*_cs Rc)) \*_cs (Rc \*_cs (Rc \*_cs Rc)))).
  apply /prd_machine; try by apply (default, default).
  exists (@rprjM (B_(Rc)) (B_(Rc \*_cs Rc))).
  rewrite F2M_spec.
  apply snd_rlzr_spec.
  apply /cmp_machine => //.
  apply (((default, (default, default)), (default, (default, default))) : A_((Rc \*_cs (Rc \*_cs Rc)) \*_cs (Rc \*_cs (Rc \*_cs Rc)))).
  apply /prd_machine => //; try by apply default.
  apply /cmp_machine => //.
  apply ((default, default) : (A_(Rc \*_cs Rc))).
  exists (@rprjM (B_(Rc)) (B_(Rc))).
  rewrite F2M_spec.
  apply snd_rlzr_spec.
  exists (@rprjM (B_(Rc)) (B_(Rc \*_cs Rc))).
  rewrite F2M_spec.
  apply snd_rlzr_spec.
  apply /cmp_machine => //.
  apply ((default, default) : (A_(Rc \*_cs Rc))).
  apply (addition_machine Rc).
  apply /prd_machine => //; try by apply default.
  apply id_machine_exists.
  exists (@lprjM _ _).
  rewrite F2M_spec.
  apply fst_rlzr_spec.
  apply diag_machine_exists.
  apply fp.
  apply diag_machine_exists.
  rewrite /lt_epsK/mf_id.
  move => [eps [x y]].
  rewrite !dom_lt_epsK.
  rewrite <-!F2MF_fprd.
  rewrite !F2MF_comp_F2MF.
  rewrite <-!F2MF_fprd.
  rewrite !F2MF_comp_F2MF.
  rewrite <-!F2MF_fprd.
  rewrite !F2MF_comp_F2MF.
  rewrite comp_F2MF => epsgt0.
  split; first by apply dom_crct;apply dom_which.
  case => H.
  - apply which_spec in H.
    move : H.
    rewrite /K_truthf /uncurry /=.
    case : (total_order_T y (eps+x)) => [[xlty _ | xeqy ] | xgty]; try by trivial.
    by split;  [split; [lra|split;try trivial;lra]|].
  - apply which_spec in H.
    move : H.
    rewrite /K_truthf /uncurry /=.
    case : (total_order_T x y) => [[xlty _ | xeqy ] | xgty]; try by trivial.
    by split;  [split; [lra|split;try trivial;lra]|].
  move : H.
  rewrite /K_truthf /uncurry /=.
  case : (total_order_T x y) => [[xlty | xeqy ] | xgty];case : (total_order_T y (eps+x)) => [[xlty' | xeqy' ] | xgty'];  try by trivial; try by split;lra.
  by case => [[_ H] | ]; [ | case => [[H1 H2] | [H1 H2]]].
  by case => [[_ H] | ]; [ | case => [[H1 H2] | [H1 H2]]].
  by case => [[_ H] | ]; [ | case => [[H1 H2] | [H1 H2]]].
  split; try by trivial.
  split; try by trivial.
  split; try by lra.
  move : H.
  by case => [[_ H] |]; [ | case => [[H1 H2] | [H1 [H2 H3]]]].
  move : H.
  by case => [[_ H] |]; [ | case => [[H1 H2] | [H1 [H2 H3]]]].
  by case => [[_ H] |]; [ | case => [[H1 H2] | [H1 [H2 H3]]]].
Defined.

Lemma lt_nK_machine : {M : monotone_machine| \F_M \solves (lt_nK : nat * (Rc * Rc) ->> Kleeneans)}.
Proof.
  have fp : forall f, (f =~= f) by trivial.
  apply /cmp_machine => //.
  apply ((default, (default, default)) : (A_(Rc \*_cs (Rc \*_cs Rc)))).
  apply lt_epsK_machine.
  apply /prd_machine => //; try by apply default.
  apply tpmn_machine.
  apply id_machine_exists.
  move => [n [x y]].
  split => /=.
  - move => [[prp1 prp2] prp3].
    split.
    + exists ((/ 2 ^ n), (x,y)); split; [| split]; try by auto; by split; [apply tpmn_lt|split;by auto].
    move => [eps [x' y']] /= [prp'1 [prp'2 prp'3]].
    exists s.      
    rewrite <-prp'1, <- prp'2, <- prp'3.
    by split; [ split; [apply tpmn_lt | split] | ].
  move => [H1 H2].
  case H1 => [[eps' [x' y']] [[-> [-> ->] [[P1 [P2 P3]] P4]]]].
  by split; [split | ].
Defined.

Lemma ltn_machine : {M : monotone_machine | \F_M \solves (lt_n : nat * (Rc * Rc) ->> bool)}.
Proof.
  apply /cmp_machine; last first.
  apply lt_n_spec.
  apply lt_nK_machine.
  apply K2B_machine_exists.
  by apply None.
Defined.


End machines.
