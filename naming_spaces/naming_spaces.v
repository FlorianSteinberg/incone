From mathcomp Require Import ssreflect ssrfun seq .
From mf Require Import all_mf.
From rlzrs Require Import all_rlzrs.
Require Import all_cont.
Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope name_scope.
Section naming_spaces.
  Structure naming_space :=
    {
      questions: Type;
      answers: Type;
      default_question: questions;
      questions_countable: questions \is_countable;
      answers_countable: answers \is_countable;
    }.

  Definition descriptions B:= questions B -> answers B.
  Coercion descriptions: naming_space >-> Sortclass.
End naming_spaces.
Notation Q := (questions _).
Notation A := (answers _).
Notation someq := (default_question _).

Lemma Q_count B: (questions B) \is_countable.
Proof. exact/questions_countable. Qed.

Lemma A_count B: (answers B) \is_countable.
Proof. exact/answers_countable. Qed.

Ltac countability := repeat apply/Q_count || apply/A_count || countability.count.countability.
Section name_product.
  (** A naming space has a defined input and output type. This file specifies
      possible input and ouptut types for pairs of functions and proves them to be
      well behaved. There are several ways to do this, the way chosen is such that
      the projections can be written down without matching. **)

  Context (B B': naming_space).
  Local Notation Q := (questions B).
  Local Notation A := (answers B).
  Local Notation Q' := (questions B').
  Local Notation A' := (answers B').

  Definition product_names: naming_space.
    exists (Q + Q')%type (A * A')%type; try countability.
    exact/inl/someq.
  Defined.
  
  Definition lprj (phipsi: product_names) := fst \o_f phipsi \o_f inl.
  Definition rprj (phipsi: product_names) := snd \o_f phipsi \o_f inr.

  Definition pair (phi: B * B'): product_names:=
    fun c => match c with
	     | inl s => (phi.1 s, phi.2 someq)
	     | inr t => (phi.1 someq, phi.2 t)
	     end.

  Lemma lprj_pair phi psi: lprj (pair (phi, psi)) =  phi.
  Proof. done. Qed.
  
  Lemma rprj_pair phi psi: rprj (pair (phi, psi)) =  psi.
  Proof. done. Qed.

  Definition unpair (phipsi: product_names): (B * B'):= (lprj phipsi, rprj phipsi).

  Lemma pairK: cancel pair unpair.
  Proof. by case. Qed.
  
  Lemma unpair_sur: unpair \is_surjective.
  Proof.
    move => [phi psi].    
    exists (pair (phi, psi)).
    exact/pairK.
  Qed.

  Lemma lprj_cont: lprj \is_continuous_function.
  Proof. by rewrite/lprj => phi; exists (fun q => [:: inl q]) => psi q' /= [->]. Qed.
  
  Lemma rprj_cont: rprj \is_continuous_function.
  Proof. by rewrite/rprj => phi; exists (fun q => [:: inr q]) => psi q' /=[->]. Qed.

  (** Note that pair and unpair are not well-typed for continuity, thus it is not proven.
   The same is true for upair o pair (although it is the identity and should be considered
   continuous. **)

  Lemma pair_cont_l psi : (fun (phi: B) => pair (phi, psi)) \is_continuous_function.
  Proof.
    move => phi; exists (fun q => if q is inl q' then [::q'; someq] else [::someq]) => qq' phi'.
    by rewrite /pair/=; case qq' => [q | q'] // [->].
  Qed.

  Lemma pair_cont_r phi: (fun (psi: B') => pair (phi, psi)) \is_continuous_function.
  Proof.
    move => psi; exists (fun q => if q is inr q' then [::q'; someq] else [:: someq]) => qq' psi'.
    by rewrite /pair/=; case qq' => [q | q'] // [->].
  Qed.

  Lemma unpair_cont_l: (fun phipsi => (unpair phipsi).1) \is_continuous_function.
  Proof.
    rewrite /unpair/lprj/= => phipsi.
    by exists (fun q => [::inl q]) => q phipsi' /=[->].
  Qed.

  Lemma unpair_cont_r: (fun phipsi => (unpair phipsi).2) \is_continuous_function.
  Proof.
    rewrite /unpair/rprj/= => phipsi.
    by exists (fun q => [::inr q]) => q phipsi' /=[->].
  Qed.

  Lemma pair_cont: (pair \o_f unpair) \is_continuous_function.
  Proof.
    move => phi.
    exists (fun qq' => [:: qq'; inl someq; inr someq]).
    by rewrite /pair/unpair/lprj/rprj /= => [[q psi [-> [_ [->]]] | q psi [-> [-> ]]]] //.
  Qed.
End name_product.
Notation "B \*_ns B'" := (product_names B B') (at level 30): name_scope.  

Section name_sum.
  Context (B B': naming_space).

  Definition sum_names: naming_space.
    exists (questions B * questions B')%type (answers B + answers B')%type.
    apply/(someq, someq).
    apply/prod_count/Q_count/Q_count.
    apply/sum_count/A_count/A_count.
  Defined.

  Definition linc (phi: B):sum_names := inl \o_f phi \o_f fst.

  Lemma linc_cntf: linc \is_continuous_function.
  Proof. by rewrite/linc => phi /=; exists (fun q => [:: q.1]) => q' psi [<-]. Qed.

  Definition rinc (phi: B'): sum_names := inr \o_f phi \o_f snd.

  Lemma rinc_cntf: rinc \is_continuous_function.
  Proof. by rewrite /rinc => phi; exists (fun q => [:: q.2]) => psi q' /=[-> ]. Qed.

  Definition inc phi: sum_names:=
    match phi with
    | inl phi => linc phi
    | inr phi  => rinc phi
    end.
  
  Definition lslct (phipsi: sum_names) (somea: A) : B:=
    fun q => match phipsi (q, someq) with
	          | inl a => a
	          | inr _ => somea
	          end.

  Definition rslct (phipsi: sum_names) (somea: A) : B':=
    fun q' => match phipsi (someq, q') with
		    | inl _ => somea
		    | inr b => b
	            end.
  
  Definition slct (phipsi: sum_names): B + B':=
    match phipsi (someq, someq) with
    | inl a => inl (lslct phipsi a)
    | inr b => inr (rslct phipsi b)
    end.
  
  Lemma lslct_linc phi (somea: A): lslct (linc phi) somea = phi.
  Proof. by trivial. Qed.
  
  Lemma rslct_rinc psi (somea: A): rslct (rinc psi) somea = psi.
  Proof. by trivial. Qed.
  
  Lemma slct_sur: slct \is_surjective.
  Proof. by move => [phi | phi]; [exists (linc phi) | exists (rinc phi)]. Qed.
End name_sum.
  
Section diagonal_mapping.
  Context (B: naming_space).

  Definition diag (phi: B) : (product_names B B):= pair (phi, phi).

  Lemma diag_cont: diag \is_continuous_function.
  Proof.
    rewrite /diag/pair => phi.
    by exists (fun q => match q with
                        | inl q' => [:: q'; someq]
                        | inr q' => [:: q'; someq]
                        end) => [/=[|] q psi [] -> [->]].
  Qed.
End diagonal_mapping.
