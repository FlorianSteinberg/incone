From Coq.micromega Require Import Psatz.
From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_rlzrs.
Require Import all_cs sets classical_cont classical_func.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section closed_choice_on_the_naturals.

Definition nonemptyA X := make_subset (fun (A: \A(X)) => exists x, x \from A2SS A).

Definition closed_choice_on X := (make_mf A2SS)|_(nonemptyA X).

Local Notation CN:= (closed_choice_on cs_nat).

Definition CN': cs_AN ->> cs_nat := make_mf (fun A n => A n = top /\ exists m, A m = top).

Lemma sval_cont: (sval: \A(cs_nat) -> cs_AN) \is_continuous.
Proof.
  rewrite/continuous -(comp_id_l (F2MF sval)).
  have <-: F2MF (@complement cs_nat) \o F2MF complement =~= mf_id.
  - by rewrite F2MF_comp_F2MF -F2MF_eq => x; exact/complement_involutive.  
  rewrite comp_assoc.
  apply/(@comp_hcr \A(cs_nat) cs_ON cs_AN)/cont_cmpl.
  apply/(@comp_hcr \A(cs_nat) cs_AN cs_ON)/cmpl_cont.
  rewrite -(comp_id_l (F2MF sval)).
Admitted.

Lemma sval_cont_inv: (F2MF sval: \A(cs_nat) ->> cs_AN)\^-1 \has_continuous_realizer.
Proof.
Admitted.

Lemma CN_CN'_val A: CN A === CN' (sval A).
Proof.
  move => n; split => [[[m Am] [[eq]]] | [eq ex]]; last by split; first exists n.
  split; first by move: eq => /=; case: (sval A n) => // [[]].
  by exists n; move: eq => /=; case: (sval A n) => // [[]].
Qed.

Lemma CN_CN': CN =~= CN' \o (F2MF sval).
Proof.
  move => A.
  rewrite comp_F2MF.
  exact/CN_CN'_val.
Qed.

Lemma CN_CN'_hcr: CN \has_continuous_realizer <-> CN' \has_continuous_realizer.
Proof.
  rewrite CN_CN'.
  split => cont; last exact/comp_hcr/cont/sval_cont.
  have : (F2MF sval \o F2MF sval\^-1) =~= mf_id.
Admitted.

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

Lemma bigmax_lt L m: m \in L -> m < \max_(n <- L) n.+1.
Proof.
  elim: L => // n L ih.
  rewrite seq.inE big_cons => /orP [/eqP -> | lst].
  - exact/leq_trans/leq_maxl.
  exact/leq_trans/leq_maxr/ih.
Qed.    

Lemma bigmax_notin L: \max_(n <- L) n.+1 \in L = false.
Proof.
  case: L => // n L.
  apply/negP => max.
  have := bigmax_lt max.
  rewrite ltnNge => /negP ineq; apply /ineq.
  apply/leqnn.
Qed.

Lemma CN_not_cont: ~ (closed_choice_on cs_nat) \has_continuous_realizer.
Proof.
  apply/CN_CN'_hcr => [[F [rlzr cont]]].
  pose sing0:= (fun n => if n == 0 then top else bot): cs_AN.
  have [phi phin0]:= get_description sing0.
  have [Fphi val]: phi \from dom F.
  - have [ | fd prp]:= rlzr _ _ phin0.
    + exists 0 => /=.
      split => //.
      by exists 0.
    done.
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
    case: ifP => [lstn eq | _ [eq]]; case: ifP => // /orP prp; exfalso; apply/prp.
    - by left; apply/mapP; exists n.
    by right; apply/eqP.
  have []:= rlzr _ _ phi'nA.
  exists (\max_(n <- map phi (L tt)) n.+1).
  rewrite /=; split.
  apply/eqP/negP.
  rewrite /= in phi'nA.
  

  move => /CN_CN'_hcr [F [rlzr cont]].
  pose sing0 := (fun n => if n is 0 then top else bot).
  have fd: sing0 \from dom CN' by exists 0; split => //; exists 0.
  pose phi n := n.+2.
  have phin0: phi \describes sing0 \wrt cs_AN.
  - by move => [ | n]; split => //; [case; rewrite /phi | exists n].
  have [[Fphi val] prp]:= rlzr phi sing0 phin0 fd.
  have [L mod]:= cont phi Fphi val.
  pose k := foldr maxn 1 (L tt).
  have klt: 0 < k.
  - rewrite /k; elim: (L tt) => //n K ih /=.
    case: n => [ | n]; first by rewrite max0n.
    exact/leq_trans/leq_maxl.
  pose psi n := if n == k.+1 then 1 else phi n.
  have coin : (phi \and psi \coincide_on (L tt))%baire.
  - suff coin: (phi \and psi \coincide_on (init_seg k.+1))%baire.
    + apply/coin_subl/coin.
      rewrite /k; elim: (L tt) => // m K ih l lstn.
      rewrite /= in lstn; case: lstn => [-> | lstn].
      * apply/lstn_iseg; exists l; split => //=.
        by have:= leq_maxl l (foldr maxn 1 K).
      apply/lstn_iseg; exists l; split => //.
      have /lstn_iseg [n [ineq <-]]:= ih l lstn.
      apply/leq_trans; first exact/ineq.
      by have:= leq_maxr m (foldr maxn 1 K).
    apply/coin_lstn => _ /lstn_iseg [n [ineq <-]].
    rewrite/psi; suff -> : n == k.+1 = false by trivial.
    apply/eqP => eq'; rewrite eq' in ineq.
    by move /eqP: ineq; rewrite subSn.
  pose singk n:= if n == k then top else bot.
  have : psi \describes singk \wrt cs_AN.
  - move => [ | n].
    + split => [ | [k']]; first by exists k.+1; rewrite /psi; case: ifP => /eqP.
      rewrite /singk; case: ifP => // /eqP eq.
      by rewrite - eq in klt.
      split.
      
    rewrite /singk; case: ifP => // /eqP.



                                          + rewrite/singk; case: ifP => // /eqP neq _.
      case: k.
      
    Search _ maxn.
    Search _ maxn.
    
    rewrite /psi -eq; case: ifP => /eqP; last first.
    rewrite /phi => //.
    
    rewrite /psi /singk; case: ifP => /eqP//.
    case: ifP => [/eqP <- | ].
    move =>

    done.
    suff
    done.
    move => stuff.
      
      rewrite /=.
      move 
      exists l; split => //.

      have := ih m.

      Search _ maxn.

      have := ih m.

      apply/ih.
      rewrite /=.
    - rewrite /psi/k; elim: (L tt) => // m K /coin_lstn ih /=.
      split.
      
      case: ifP => [/eqP -> | ].

      End opens.