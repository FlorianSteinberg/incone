From mathcomp Require Import ssreflect seq ssrnat ssrbool eqtype ssrfun.
From mf Require Import all_mf.
Require Import all_cont PhiN FMop Umach.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CM2A.
  (*
  Context (Q: eqType) (someq: Q) ( Q' A A': Type).
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Local Open Scope name_scope.
  Context (F: partial_function B B').
  Context (mu: partial_function B (Q' -> seq Q)).
  Context (N: nat * seq (Q * A) -> option B).
  Hypothesis mon: PhiN.monotone N.
  Hypothesis dp_dom: dom \Phi_N === dom (projection_on (dom F)).
  Hypothesis dp_spec: (projection_on (dom F)) \extends \Phi_N.
  Hypothesis mod: mu \modulus_for F.
  Hypothesis modmod: mu \modulus_for mu.
    
  Lemma dp_nil: dom F === (projection_on (dom F)) nil.
  Proof. by move => phi; split => [phifd | []]//; split => // q []. Qed.
    
  Fixpoint count_someq (K: seq Q) :=
    match K with
    | nil => 0
    | q :: K' => if q == someq then (count_someq K').+1 else count_someq K'
    end.

  Lemma dp_val KL n phi: N (n, KL) = Some phi -> phi \from domain F.
  Proof. by move => eq; rewrite PF2MF_dom; have []//:= @dp_spec KL phi; exists n. Qed.

  Lemma dp_val_mu KL n phi: N (n, KL) = Some phi -> phi \from domain mu.
  Proof. by move => eq; rewrite PF2MF_dom; apply mod; have []//:= @dp_spec KL phi; exists n. Qed.
  
  Lemma psi_step_dep (L: seq A) (q': Q') (K: seq Q) m:
    {Ka': seq Q + A' | (exists phi, N (m, rev (zip (rev K) (rev L))) = Some phi /\
                             exists psi psi', sval psi = phi /\ sval psi' = phi /\
                                              Ka' =
                                              if check_sublist (mu psi q') K
                                              then inr (F psi' q')
                                              else inl (mu psi q')) \/ Ka' = inl [:: someq]}.
  Proof.
    case eq: (N (m,  rev (zip (rev K) (rev L)))) => [phi | ]; last first.
    - by exists (inl [::someq]); right.
    case cl: (check_sublist (mu (exist _ phi (dp_val_mu eq)) q') K).
    - exists (inr (F (exist _ phi (dp_val eq)) q')).
      left; exists phi; split => //.
      exists (exist _ phi (dp_val_mu eq)).
      exists (exist _ phi (dp_val eq)) => /=.
      by do 2 split => //; rewrite cl.
    exists (inl (mu (exist _ phi (dp_val_mu eq)) q')).
    left; exists phi; split => //.
    exists (exist _ phi (dp_val_mu eq)).
    exists (exist _ phi (dp_val eq)) => /=.
    by do 2 split => //; rewrite cl.
  Qed.

  Definition psi_step phi q' K m :=
    if check_sublist (mu psi q') K
                     then inr 
  Definition psi_step L q' K m:= sval (psi_step_dep L q' K m).

  Lemma pstp_spec L q' K m:
    (exists phi, N (m, rev (zip (rev K) (rev L))) = some phi /\
                 exists psi psi', sval psi = phi /\ sval psi' = phi /\
                                  psi_step L q' K m = if check_sublist (mu psi q') K
                                                      then inr (F psi' q')
                                                      else inl (mu psi q'))
    \/ psi_step L q' K m = inl [:: someq].
  Proof. exact/(svalP (psi_step_dep L q' K m)). Qed.

  Lemma pstp_nnil L q' K m K': psi_step L q' K m = inl K' -> K' <> nil.
  Proof.
    case: (pstp_spec L q' K m) => [[phi [eq [psi [psi' [eq' [eq'' ->]]]]]] | -> [<-]]//.
    by case: ifP => //; case: (mu psi q') => // q K'' _ [<-].
  Qed.
    
  Fixpoint psi_rec (phi: seq (Q * A)) (q': Q') n m: seq Q + A':=
    match n with
    | 0 => psi_step phi q' nil m
    | S n' => match psi_rec L q' n' m with
              | inr a' => inr a'
              | inl K => match psi_step L q' K m with
                          | inl K' => inl (K' ++ K)
                          | inr a' => inr a'
                          end
              end
    end.

  Lemma psi_rec_spec L q' phi:
    exists k, forall n m, k <= n -> k <= m -> psi_rec L q' n m = inr (F phi q').
  Proof.
    
  Admitted.
    
  Definition CM2A (phiq': seq (Q * A) * Q') :=
    psi_rec phiq'.1 phiq'.2 (size phiq'.1) (size phiq'.1).

  Lemma CM2A_nnil L q' K: CM2A (L,q') = inl K -> K <> nil.
  Proof.
    rewrite /CM2A; case: L => /= [eq | a L]; first exact/pstp_nnil/eq.
    case: (psi_rec _ _ _) => // K'; case E: (psi_step _ _ _) => [K'' | ]//; case => <-.
    by case: K' E => // [eq | ]; [rewrite cats0; apply/pstp_nnil/eq | case: K''].
  Qed.
  
  Lemma CM2A_spec: (U CM2A) \evaluates F.
  Proof.
    move => phi.
    rewrite -PF2MF_dom => phifd.
    split.
    apply/FM_dom => q'.
    exists (F (exist _ phi phifd) q').
    rewrite /=.    
  Admitted.    *)
End CM2A.