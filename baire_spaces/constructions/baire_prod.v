From mathcomp Require Import ssreflect ssrfun seq.
From rlzrs Require Import all_rlzrs.
Require Import baire cont.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope baire_scope.
Section baire_product.
  (** A baire space has a defined input and output type. This file specifies
      possible input and ouptut types for pairs of functions and proves them to be
      well behaved. There are several ways to do this, the way chosen is such that
      the projections can be written down without matching. **)

  Context (Q A Q' A': Type) (a: A) (a': A').  
  Notation B:= (Q -> A).
  Notation B' := (Q' -> A').

  Definition bair_product := Q + Q' -> A * A'.
  
  Definition lprj (phipsi: bair_product) q := (phipsi (inl q)).1.
  Definition rprj (phipsi: bair_product) q := (phipsi (inr q)).2.

  Definition pair (phi: B * B'): bair_product:=
    fun c => match c with
	     | inl s => (phi.1 s, a')
	     | inr t => (a, phi.2 t)
	     end.

  Lemma lprj_pair phi psi: lprj (pair (phi, psi)) =  phi.
  Proof. by trivial. Qed.
  
  Lemma rprj_pair phi psi: rprj (pair (phi, psi)) =  psi.
  Proof. by trivial. Qed.

  Definition unpair (phipsi: bair_product): (B * B'):= (lprj phipsi, rprj phipsi).

  Lemma pairK: cancel pair unpair.
  Proof. by case. Qed.

  Definition rep_prod := F2MF unpair.
    
  Lemma rep_prod_sur: rep_prod \is_cototal.
  Proof.
    move => [phi psi].
    exists (pair (phi, psi)).
    exact/pairK.
  Qed.

  Lemma rep_prod_sing: rep_prod \is_singlevalued.
  Proof. by move => phipsi _ _ <- <-. Qed.

  Definition prod_interview_mixin:= interview.Mixin rep_prod_sur.
  Canonical prod_interview_struc:= interview.Struc prod_interview_mixin.
  Definition prod_dictionary_mixin := dictionary.Mixin rep_prod_sing.
  Canonical prod_dictionary_class := dictionary.Class prod_dictionary_mixin.
  Canonical prod_dict:= dictionary.Pack prod_dictionary_class.

  Lemma lprj_cont: lprj \is_continuous_function.
  Proof. by move => phi; exists (fun q => [:: inl q]) => psi q' [eq _]; rewrite /lprj eq. Qed.
  
  Lemma rprj_cont: rprj \is_continuous_function.
  Proof. by move => phi; exists (fun q => [:: inr q]) => psi q' [eq _]; rewrite /rprj eq. Qed.

  (** Note that pair and unpair are not well-typed for continuity, thus it is not proven.
   The same is true for upair o pair (although it is the identity and should be considered
   continuous. **)

  Lemma pair_cont: (pair \o_f unpair) \is_continuous_function.
  Proof.
    move => phi.
    exists (fun qq' => [:: qq']).
    by rewrite /pair/unpair/lprj/rprj /= => [[] q psi [->]].
  Qed.
End baire_product.
Arguments bair_product {Q} {A} {Q'} {A'}. 
Arguments lprj {Q} {A} {Q'} {A'}.
Arguments rprj {Q} {A} {Q'} {A'}.
Arguments pair {Q} {A} {Q'} {A'}.
Arguments unpair {Q} {A} {Q'} {A'}.
Arguments prod_dict {Q} {A} {Q'} {A'}.

Section diagonal_mapping.
  Context (Q A: Type) (a: A).
  Notation B := (Q -> A).

  Definition diag (phi: B) q:=
    match q with
    | inl q' => (phi q', a)
    | inr q' => (a, phi q')
    end.

  Lemma diag_spec phi: diag phi = pair a a (phi, phi).
  Proof. done. Qed.

  Lemma diag_cont: (F2MF diag) \is_continuous.
  Proof.
    apply/cont_F2MF => phi.
    exists (fun q => match q with
                     | inl q' => [:: q']
                     | inr q' => [:: q']
                     end) => [[] q psi []];
    by rewrite /diag => ->.
  Qed.
End diagonal_mapping.

Section baire_fprd.
  Context (Q Q' A A' S S' T T': Type) (t: T) (t': T') (a: A) (a': A').
  Notation B:= (Q -> A).
  Notation B':= (Q' -> A').
  Notation D:= (S -> T).
  Notation D':= (S' -> T').
  
  Definition fprd_rlzr (F: B ->> D) (G: B' ->> D'):
    questions (prod_dict a a') ->> questions (prod_dict t t'):=
    make_mf (fun phipsi FphiGpsi =>
	       FphiGpsi = pair t t' (unpair FphiGpsi)
	       /\
	       (F ** G) (unpair phipsi) (unpair FphiGpsi)).
  
  Lemma fprd_rlzr_spec F G: (fprd_rlzr F G) \realizes (F ** G).
  Proof.
    move => phipsi _ <- [[Fphi Gpsi] val].
    split => [ | FphiGpsi' [eq val']]; first by exists (pair t t' (Fphi, Gpsi)).
    by exists (unpair FphiGpsi').
  Qed.
    
  Lemma fprd_cont F G: F \is_continuous -> G \is_continuous -> (fprd_rlzr F G) \is_continuous.
  Proof.
    have mapl: forall K (q: Q), List.In q K -> List.In ((@inl _ Q') q) (map inl K).
    elim => // q K ih q' /=listin; by case: listin => ass; [left; rewrite -ass | right; apply ih].
    have mapr: forall K (q:Q'), List.In q K -> List.In ((@inr Q _) q) (map inr K).
    elim => // q K ih q' /=listin; by case: listin => ass; [left; rewrite -ass | right; apply ih].
    rewrite !cont_spec => cont cont' phi [FGphi [np [/=FphiFGphi GphiFGphi]]].
    have [ | Lf mod]:= cont (lprj phi); first by exists (lprj FGphi).
    have [ | Lf' mod']:= cont' (rprj phi); first by exists (rprj FGphi).
    exists (fun qq' => match qq' with
	               | inl q => map inl (Lf q)
	               | inr q' => map inr (Lf' q')
                       end) => [[q | q']].
    - have [psi' crt]:= mod q; exists (FGphi (inl q)).
      move => psi /coin_lstn coin Fpsi [ np' [/=val'l val'r]].
      rewrite np np'; apply injective_projections => //=.
      rewrite (crt (lprj phi) _ (lprj FGphi))//; last exact/coin_ref.
      rewrite (crt (lprj psi) _ (lprj Fpsi))// coin_lstn /lprj => q' lstn.
      by rewrite (coin (inl q')) //; apply (mapl (Lf q) q').
    have [psi' crt]:= mod' q'; exists (FGphi (inr q')).
    move => psi /coin_lstn coin Fpsi [ np' [/=val'l val'r]].
    rewrite np np'; apply injective_projections => //=.
    rewrite (crt (rprj phi) _ (rprj FGphi))//; last exact/coin_ref.
    rewrite (crt (rprj psi) _ (rprj Fpsi))// coin_lstn /rprj => q lstn.
    by rewrite (coin (inr q)) //; apply (mapr (Lf' q') q).
  Qed.

  Definition lcry_rlzr (F: bair_product ->> D) (phi: B): B' ->> D :=
    (make_mf (fun psi => F (pair a a' (phi,psi)))).
  
  Fixpoint collect_right S T (L: seq (S + T)) :=
    match L with
    | nil => nil
    | a :: L' => match a with
                 | inr b => b :: (collect_right L')
                 | inl _ => collect_right L'
                 end
    end.
  
  Lemma lcry_cont F phi: F \is_continuous -> (lcry_rlzr F phi) \is_continuous.
  Proof.
    rewrite !cont_spec => cont psi [Fphipsi /= val].
    have [ | mf mod]:= cont (pair a a' (phi,psi)); first by exists Fphipsi.
    exists (fun q => collect_right (mf q)) => q.
    exists (Fphipsi q) => psi' coin Fphipsi' val'.
    apply/crt_icf/val'; first exact/val; first exact/mod.
    by elim: (mf q) coin => // [[q' L ih /=/ih | q' L ih /= [-> /ih]]].
  Qed.

  Definition rcry (F: bair_product ->> D) (psi: B'): B ->> D:=
    make_mf (fun phi => F (pair a a' (phi, psi))).
  
  Fixpoint collect_left S T (L: seq (S + T)) :=
    match L with
    | nil => nil
    | a :: L' => match a with
                 | inl b => b :: (collect_left L')
                 | inr _ => collect_left L'
                 end
    end.
  
  Lemma rcry_cont F psi: F \is_continuous -> (rcry F psi) \is_continuous.
  Proof.
    rewrite !cont_spec => cont phi [Fphipsi /= val].
    have [ | mf mod]:= cont (pair a a' (phi, psi)); first by exists Fphipsi.
    exists (fun q => collect_left (mf q)) => q.
    exists (Fphipsi q) => psi' coin Fphipsi' val'.
    apply/(crt_icf _)/val'; first exact/val; first exact/mod.
    by elim: (mf q) coin => // [[q' L ih /= [-> /ih] | q' L ih /= /ih]].
  Qed.
End baire_fprd.