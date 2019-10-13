From mathcomp Require Import ssreflect ssrfun seq ssrnat.
From rlzrs Require Import all_rlzrs.
Require Import all_cs_base dscrt.
From metric Require Import pointwise.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SEQ.
  Context (X: cs).

  Definition list_names := Build_naming_space someq (Q_count X) (list_count (A_count X)).
  
  Fixpoint rep_seq_rec (phi: list_names) L :=
    match L with
      | nil => forall q, phi q = [::]
      | x :: L' => (forall q, phi q <> [::])
                     /\ (forall a, (fun q => head a (phi q)) \describes x \wrt (delta_ X))
                     /\ rep_seq_rec (fun q => behead (phi q)) L'
      end.

  Definition rep_seq := make_mf rep_seq_rec.

  Lemma rep_seq_rep: rep_seq \is_representation.
  Proof.
    split => [ | phi L].
    - elim => [ | a L' [phi']]; first by exists (fun q => [::]).
      have [phi phip] := (get_description a).
      by exists (fun q => (phi q)::(phi' q)).
    elim: L phi => [phi [ | x L' phinL [prp]]//| x L ih phi [[prp] | x' L' phinaL phina'L']//];
                     try by have := prp someq.
    f_equal; last by apply/ih; [apply phinaL | apply phina'L'].
    case E: (phi someq); first by have:= (phinaL.1 someq); rewrite E.
    by apply/rep_sing; [apply/phinaL.2.1 | apply/phina'L'.2.1].
  Qed.

  Canonical list_representation:= Build_representation_of rep_seq_rep.

  Canonical cs_seq:= repf2cs list_representation.
  
  Definition size_rlzrf (phi : (B_ cs_seq)) (tt: unit) := (size (phi someq)).

  Definition size_rlzr: B_ cs_seq ->> B_ cs_nat := F2MF size_rlzrf.

  Lemma size_rlzr_cntop: size_rlzr \is_continuous_operator.
  Proof.
    rewrite cont_F2MF /size_rlzrf => phi.
    by exists (fun _ => [::someq]) => q' psi /= [-> _].
  Qed.
    
  Lemma size_rlzr_spec: size_rlzr \realizes (size: cs_seq -> cs_nat).
  Proof.
    apply/F2MF_rlzr_F2MF => phi L/=; rewrite /size_rlzrf.
    elim : L phi => [phi -> | a L IH phi phinaL]//=.    
    case E : (phi someq) => [ | a' L']; first by have:= (phinaL.1 someq).
    rewrite -(IH (fun q => behead (phi q))); last by apply phinaL.
    by rewrite size_behead /= E.
  Qed.

  Lemma size_cont: size \is_continuous.
  Proof. by exists size_rlzr; split; try exact/size_rlzr_spec; exact/size_rlzr_cntop. Qed.

  Definition head_rlzrf phi (psi: B_ cs_seq) q := head (phi q) (psi q).

  Definition head_rlzr: B_ (cs_prod X cs_seq) ->> B_ X :=
    F2MF (fun (phi: B_ (cs_prod X cs_seq)) => head_rlzrf (lprj phi) (rprj phi)).

  Lemma head_rlzr_cntop: head_rlzr \is_continuous_operator.
  Proof.
    apply/cont_F2MF; rewrite /head_rlzrf/lprj/rprj.
    by exists (fun q => [:: inl q; inr q]) => q psi /= [-> [->]].
  Qed.
              
  Lemma head_rlzr_spec: head_rlzr \realizes (fun xL => head xL.1 xL.2).
  Proof.
    apply/F2MF_rlzr => phi [x L] /prod_name_spec [phinx/=].
    case: L => [prp | y L [neq [phiny _]]].
    - suff ->: head_rlzrf (lprj phi) (rprj phi) = lprj phi by trivial.
      by apply/functional_extensionality => q; rewrite /head_rlzrf prp.
    suff ->: head_rlzrf (lprj phi) (rprj phi) = fun q => head (lprj phi someq) (rprj phi q).
    - by apply/phiny.
    apply/functional_extensionality => q.
    by rewrite /head_rlzrf; have:= neq q; case: (rprj phi q) => //.
  Qed.

  Lemma head_cont: (uncurry head) \is_continuous.
  Proof. by exists head_rlzr; split; try exact/head_rlzr_spec; exact/head_rlzr_cntop. Qed.
   
  Definition cons_rlzrf (phi : B_ X) psi := (fun q => (cons (phi q) (psi q))).

  Definition cons_rlzr: B_ (X \*_cs cs_seq) ->> (B_ cs_seq) :=
    F2MF (fun (phi: B_ (cs_prod X cs_seq)) => cons_rlzrf (lprj phi) (rprj phi)).
  
  Lemma cons_rlzr_cntop: cons_rlzr \is_continuous_operator.
  Proof.
    apply/cont_F2MF; rewrite /cons_rlzrf/lprj/rprj.
    by exists (fun q => [:: inl q; inr q]) => q' psi /=[-> [->]].
  Qed.
  
  Lemma cons_rlzr_spec: cons_rlzr \realizes (fun xL => cons xL.1 xL.2).
  Proof.
    by apply/F2MF_rlzr => phi L /prod_name_spec phinL /=; split => //; split => [a | ]; apply phinL.
  Qed.

  Lemma cons_cont: (uncurry cons) \is_continuous.
  Proof. by exists cons_rlzr; split; try exact/cons_rlzr_spec; exact/cons_rlzr_cntop. Qed.
End SEQ.
