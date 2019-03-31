(** This file proves that closed choice on the natural numbers is discontinuous.
    The proof is done with respect to the representation of closed subsets of 
    the naturals that uses enumerations of the complement as names. The corresponding
    space is defined in the library, called cs_AN and the library also contains a
    proof that cs_AN is isomorphic to A(nat) (the later represents a closed subset by
    a name of the characteristic function of the complement as continuous function to
    Sirpinski space). **)

Require Import Psatz.
From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_rlzrs.
Require Import all_cs sets classical_cont classical_func.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section closed_choice_on_the_naturals.
  
  Definition closed_choice_on X := make_mf (@A2SS X).

  Definition nonempties X:= dom (closed_choice_on X).
  
  Definition CN: cs_AN ->> cs_nat := make_mf (fun (A: pred nat) n => A n).

  Lemma CN_CN'_val A: closed_choice_on cs_nat  A === CN (sval A).
  Proof. by move => n; split => /= [eq | ]; [rewrite eq | case: (sval A n) => [[]|]]. Qed.

  Lemma CN_CN': closed_choice_on cs_nat =~= CN \o F2MF Anat2AN.
  Proof.
    move => A.
    rewrite comp_F2MF.
    exact/CN_CN'_val.
  Qed.

  Lemma CN_CN'_hcr: CN \has_continuous_realizer
                    <-> (closed_choice_on cs_nat) \has_continuous_realizer.
  Proof.
    split => cont.
    rewrite CN_CN'.
    exact/comp_hcr/cont/Anat2AN_cont.
    rewrite -(comp_id_r CN).
    suff <-: F2MF Anat2AN \o F2MF AN2Anat =~= mf_id.
    - by rewrite -comp_assoc -CN_CN'; apply/comp_hcr/cont/AN2Anat_cont.
    rewrite comp_F2MF => p p'/=; split => <-.
    - apply/functional_extensionality => n/=.
      by rewrite /AN2Anat/Anat2AN/P2CF /=; case: ifP.
    apply/functional_extensionality => n/=.
    by rewrite /AN2Anat/Anat2AN/P2CF /=; case: ifP.
  Qed.

  Lemma inP (T: eqType) q (L: seq T): reflect (List.In q L) (q \in L).
  Proof.
    elim: L => [ | t L ih]; first by apply/ReflectF.
    case E: (q \in t :: L).
    - rewrite seq.inE in E.
      by apply/ReflectT; case/orP: E => [/eqP -> | /ih ]; [left | right].
    apply/ReflectF => [/= [eq | lstn]]; suff: false by trivial.
    - by rewrite -E seq.inE; apply/orP; left; rewrite eq.
    by rewrite -E seq.inE; apply/orP; right; apply/ih.
  Qed.  

  Lemma bigmax_lt T (L: seq T) (t: T) (phi: T -> nat):
    List.In t L -> phi t < \max_(n <- L) (phi n).+1.
  Proof.
    elim: L => // n L ih.
    rewrite big_cons => /=[[<- | lstn]].
    - exact/leq_trans/leq_maxl.
    exact/leq_trans/leq_maxr/ih.
  Qed.

  Lemma bigmax_notin L: \max_(n <- L) n.+1 \in L = false.
  Proof.
    case: L => // n L.
    apply/negP => /inP max.
    have := bigmax_lt id max.  
    rewrite ltnNge => /negP ineq; apply /ineq.
    exact/leqnn.
  Qed.

  Lemma CN_not_cont: ~ (closed_choice_on cs_nat) \has_continuous_realizer.
  Proof.
    apply/CN_CN'_hcr => [[F [rlzr cont]]].
    pose sing0:= (fun n => if n == 0 then top else bot): cs_AN.
    have [phi phin0]:= get_description sing0.
    have [ | [Fphi val] prp] := rlzr _ _ phin0; first by exists 0.
    have [L /= mod]:= cont phi Fphi val.
    pose phi' n := if n \in (L tt) then phi n else 1.
    have coin: (phi \and phi' \coincide_on (L tt))%baire.
    - apply/coin_lstn => n lstn.
      rewrite /phi'.
      suff ->: n \in L tt = true by trivial.
      exact/inP.
    have [A phi'nA]: phi' \from dom (rep cs_AN).
    - exists (fun n => if (n.+1 \in map phi (L tt)) || (n == 0) then bot else top) => m.
      rewrite /phi'; split => [ | [n ]].
      + case: ifP => /orP// [/mapP [n lstn eq] _ | /eqP -> _] .
        * by exists n; rewrite lstn eq.
          exists (\max_(n <- L tt) n.+1).
        by rewrite bigmax_notin.
      case: ifP => [lstn eq | _ [eq]]; case: ifP => // /orP cnd; exfalso; apply/cnd.
      + by left; apply/mapP; exists n.
      by right; apply/eqP.
    have [ | [Fphi' val'] prp']:= rlzr _ _ phi'nA.
    - exists (\max_(n <- (L tt)) (phi n).+1).+1 => //.
      suff Am: A (\max_(n <- L tt) (phi n).+1).+1 by trivial.
      apply/negbNE/negP => /phi'nA [m].
      rewrite /phi'.
      case: ifP => [/inP lstn eq | /inP lstn eq] //.
      have:= bigmax_lt phi lstn.
      rewrite eq ltnNge => /negP ineq.
      exact/ineq/leqW.
    have valeq: Fphi' tt = Fphi tt by apply/mod/val'/coin.
    have eq1: Fphi tt = 0.
    - by have [n [-> ]]:= prp Fphi val; rewrite /sing0 /=; case: ifP => // /eqP.
    have : Fphi' tt <> 0.
    - have [n [-> /negP ex eq']]:= prp' Fphi' val'.
      apply/ex/negP/phi'nA.
      exists (\max_(n <- L tt) n.+1).
      rewrite /phi' eq'.
      case: ifP => // lstn.
      by have := bigmax_notin (L tt); rewrite lstn.
    by rewrite valeq eq1.
  Qed.
End closed_choice_on_the_naturals.