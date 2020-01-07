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
Require Import computable_reals_pf.
Require Import Ibounds.

(* Some helper functions we need that should be moved to another file later *)
Definition ltK (xy : R*R) := let (x,y) := xy in
                     match (total_order_T x y) with
                     | (inleft (left _)) => true_K
                     | (inright _) => false_K
                     | _ => bot_K
                     end.
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

Lemma ltn_tot : lt_n \is_total.
Proof.
  move => a.
  rewrite lt_n_spec /lt_nK/B2K.
  rewrite <-comp_dom_codom; first by rewrite dom_lt_nk.
  rewrite <- codom_dom_inv.
  case => Hd; [ by exists false | by exists true |].
  by case Hd => [_ [_ H0]].
Qed.
End lt_n_test.


(* We now define realizers for the multifunctions defined above *)
Section realizers.
Arguments partial_function {S} {T}.
Definition RS2CS Rc := (Build_continuity_space (representation Rc)).
Coercion RS2CS : computable_reals >-> continuity_space.
Variable (Rc : computable_reals).


Lemma cleanup_before_pf (X : cs) (F : Rc ->> X) : {f : partial_function  | f \solves F} -> {f : partial_function | f \solves F}.
Proof.
  have fp : forall f, (f =~= f) by trivial.
  move => H.
  apply /cmp_pf; last first.
  rewrite <- (comp_id_r F).
  apply fp.
  case (cleanup Rc) => cln clnprp.
  exists cln.
  apply clnprp.
  apply H.
Defined.
Lemma cleanup_after_pf (X : cs) (F : X ->> Rc) : {f : partial_function  | f \solves F} -> {f : partial_function | f \solves F}.
Proof.
  have fp : forall f, (f =~= f) by trivial.
  move => H.
  apply /cmp_pf; last first.
  rewrite <- (comp_id_l F).
  apply fp.
  apply H.
  case (cleanup Rc) => cln clnprp.
  exists cln.
  apply clnprp.
Defined.
(* We often need the operation n -> / 2 ^ n so we define a function *)
Lemma tpmn_rlzr : {f : partial_function | f \realizes ((fun (n : nat) => (/ 2 ^ n)) : (nat -> Rc))}.
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
  apply /cmp_pf.
  case (F2R Rc) => f2r f2rprp.
  exists (F2PF f2r).
  rewrite F2PF_spec.
  apply f2rprp.
  exists (F2PF rlzrf).
  rewrite F2PF_spec.
  apply rlzrf_spec.
  rewrite F2MF_comp_F2MF /uncurry.
  rewrite <- F2MF_eq => n /=.
  by rewrite powerRZ2_neg_pos;lra.
Defined.

Lemma diag_pf_exists (X : cs) : {f : partial_function  | f \solves (mf_diag : X ->> _)}.
Proof.
  exists (F2PF (fun phi => (pair (phi,phi)))).
  rewrite F2PF_spec.
  rewrite F2MF_slvs => phi x phin.
  case => t /=tprp.
  exists (x,x); split; first by auto.
  exists (phi,phi).
  split; by [apply pairK | split].
Defined.

Lemma innertest_exists : {f : partial_function | f \solves
                                          (F2MF (snd : (Rc *(Rc * Rc)) -> (Rc * Rc)) **
  (((F2MF snd \o F2MF snd) ** (F2MF ((uncurry Rplus) : ((Rc*Rc) -> Rc)) \o (F2MF (ssrfun.id ) ** F2MF (fst : (Rc \*_cs Rc -> _))))) \o
     (mf_diag )))
}.
Proof.
  have fp : forall f, (f =~= f) by trivial.
  apply/pf_fprd => //.
  exists (F2PF ((@rprj (B_(Rc)) (B_(Rc \*_cs Rc))) : (B_(Rc \*_cs (Rc \*_cs Rc)) -> B_(Rc \*_cs Rc)))).
  rewrite F2PF_spec.
  apply snd_rlzr_spec.
  apply /cmp_pf => //.
  apply /pf_fprd => //.
  apply cleanup_after_pf.
  apply /cmp_pf => //.
  apply cleanup_after_pf.
  exists (F2PF ((@rprj (B_(Rc)) (B_(Rc))) : (B_((Rc \*_cs Rc)) -> B_(Rc )))).
  rewrite F2PF_spec.
  apply snd_rlzr_spec.
  exists (F2PF ((@rprj (B_(Rc)) (B_(Rc \*_cs Rc))) : (B_(Rc \*_cs (Rc \*_cs Rc)) -> B_(Rc \*_cs Rc)))).
  rewrite F2PF_spec.
  apply snd_rlzr_spec.
  apply /cmp_pf => //.
  apply (addition_rlzr Rc).
  apply /pf_fprd => //.
  apply cleanup_before_pf.
  exists (F2PF (ssrfun.id)).
  rewrite F2PF_spec.
  apply id_rlzr.
  apply cleanup_after_pf.
  exists (F2PF ((@lprj (B_(Rc)) (B_(Rc))) : (B_((Rc \*_cs Rc)) -> B_(Rc)))).
  rewrite F2PF_spec.
  apply fst_rlzr_spec.
  apply diag_pf_exists.
Defined.

Lemma Ktruth_cmp_exists : {f : partial_function | f \solves (((F2MF K_truthf) ** (F2MF K_truthf)) \o ((F2MF (ltK : (Rc * Rc) -> cs_Kleeneans)) ** (F2MF (ltK : (Rc * Rc) -> cs_Kleeneans))))}.
Proof.
  have fp : forall f, (f =~= f) by trivial.
  apply /(cmp_pf) => //.
  apply /pf_fprd =>//.
  exists (F2PF (K_truth_rlzrf : B_(cs_Kleeneans) -> B_(cs_Sirp))).
  rewrite F2PF_spec.
  apply Ktruth_rlzr_spec.
  exists (F2PF (K_truth_rlzrf : B_(cs_Kleeneans) -> B_(cs_Sirp))).
  rewrite F2PF_spec.
  apply Ktruth_rlzr_spec.
  apply /pf_fprd =>//.
  apply (ltk_rlzr Rc).
  apply (ltk_rlzr Rc).
Defined.
(* We show that there constructively exists a realizer function for the operator *)
Lemma lt_epsK_rlzr : {f : (partial_function ) | f \solves (lt_epsK : Rc * (Rc * Rc) ->> cs_Kleeneans)}.
Proof.
  have fp : forall f, (f =~= f) by trivial.
  apply /(cmp_pf_tight).
  exists (F2PF (which_rlzrf : (B_(cs_Sirp \*_cs cs_Sirp) -> B_(cs_Kleeneans)))).
  rewrite F2PF_spec.
  apply /which_rlzrf_spec.
  apply /(cmp_pf) => //.
  apply Ktruth_cmp_exists.
  apply /cmp_pf => //.
  apply innertest_exists.
  apply diag_pf_exists.
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

Lemma lt_nK_rlzr : {f : partial_function | f \solves (lt_nK : nat * (Rc * Rc) ->> Kleeneans)}.
Proof.
  have fp : forall f, (f =~= f) by trivial.
  apply /cmp_pf => //.
  apply lt_epsK_rlzr.
  apply /pf_fprd => //.
  apply cleanup_after_pf.
  apply tpmn_rlzr.
  exists (F2PF (ssrfun.id)).
  rewrite F2PF_spec.
  apply id_rlzr.
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

Lemma ltn_rlzr : {f : partial_function | f \solves (lt_n : nat * (Rc * Rc) ->> bool)}.
Proof.
  apply /cmp_pf; last first.
  apply lt_n_spec.
  apply lt_nK_rlzr.
  exists (get_partial_function K2B_rlzrM).
  rewrite gtpf_spec.
  apply /tight_slvs.
  apply F_K2B_rlzrM_spec.
  by apply sfrst_spec.
Defined.
End realizers.
