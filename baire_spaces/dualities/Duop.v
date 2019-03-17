From mathcomp Require Import ssreflect seq ssrnat ssrbool eqtype ssrfun.
From mf Require Import all_mf.
Require Import all_cont FMop Umach Ucont Uuniv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section duality_operator.
  (* Q: Questions, A: Answers *)
  Context (Q Q' A A' : Type).
  (* B: Baire space *)
  Local Notation B := (Q -> A).
  Local Notation B' := (Q' -> A').
  Local Open Scope baire_scope.
  Local Notation "? K" := (@inl (list Q) A' K) (format "'?' K", at level 50).
  Local Notation "! a'" := (@inr (list Q) A' a') (format "'!' a'", at level 50).

  Fixpoint collect_left (Ka's: seq (seq Q + A')) : seq Q :=
    match Ka's with
    | nil => nil
    | cons Ka' Ka's' => match Ka' with
                        | inl K => K ++ collect_left Ka's'
                        | inr a' => nil
                        end
    end.

  Fixpoint D (phi: B) (Ka'sq': seq (seq Q + A') * Q') : seq (seq A * Q') + A' :=
    match Ka'sq'.1 with
    | nil => inl [::(nil, Ka'sq'.2)]
    | Ka' :: Ka's => match Ka' with
                     | inl K => inl [::(map phi (collect_left Ka'sq'.1), Ka'sq'.2)]
                     | inr a' => inr a'
                     end
    end.
  
  Lemma D_cont: D \is_continuous_function.
  Proof.
    exists (fun Ka'sq' => match Ka'sq'.1 with
                          | inl K :: Ka's => collect_left Ka'sq'.1
                          | _ => nil
                          end).
    move => [Ka's q'] psi coin.
    rewrite /D /=; case: Ka's coin => // [[]]//= K Ka's coin.
    by f_equal; f_equal; rewrite (coin_map coin).
  Qed.

  Lemma U_rec_D psi n phi q':
    U_rec (D phi) n.+1 psi q' =
    match U_rec psi n phi q' with
    | inl _ => inl (iseg (fun i => (map phi (gather_queries psi i phi q'), q')) n.+1)
    | inr a' => inr a'
    end.
  Proof.
    elim: n => [ | n ih]; first by rewrite /=/U_step/=.
    rewrite unfold_U_rec ih /U_step unfold_U_rec /U_step.
    case: (U_rec_spec psi n phi q') => [eq | [a' ->] ] //.
    rewrite eq /=/U_step eq /=.
    case E: (psi (map phi (gather_queries psi n phi q'), q')) => [K | a'] //.
    f_equal; move: ih => _ /=; do 4 f_equal.

    elim: n K eq E => //n ih K eq E.
    have eq': U_rec psi n phi q' = ?(gather_queries psi n phi q').
    - by move: eq; rewrite /=/U_step; case (U_rec_spec psi n phi q') => [ | [a' ->]].
    have:= (ih _ eq'); move: ih => _ ih /=.
    rewrite /= eq'/U_step in eq; move: eq.
    case E': (psi (map phi (gather_queries psi n phi q'), q')) => [K' | ]// _.
    by rewrite /U_step eq' E'; f_equal; apply/ih/E'.
  Qed.

  Lemma D_gq psi phi q' n:
    gather_queries (D phi) n.+1 psi q' = build_shapes psi n phi q'.
  Proof. 
    elim: n => [ | n ih]; first by rewrite /=/U_step/=; case: (psi (nil, q')).
    rewrite unfold_bs -ih unfold_gq U_rec_D.
    by case: (U_rec psi n.+1 phi q').
  Qed.

  Lemma D_spec psi phi: \F_(U (D phi)) psi === \F_(U psi) phi.
  Proof.
    move => Fphi.
    split => /FU_spec evl q'; have [Qn [cns val]]:= evl q'.
    - exists (size Qn).
      have:= U_rec_D psi (size Qn) phi q'.
      case: (U_rec_spec (D phi) (size Qn) psi q') => [eq | [a' eq]]//.
      + rewrite unfold_U_rec eq /U_step (gq_cns cns) val.
        case E: (U_rec psi (size Qn) phi q') => [ | b']// [->].
        by rewrite /U E.
     move: val; rewrite -(U_rec_inr_spec (Fphi q') cns) => ->.
     case E: (U_rec psi (size Qn) phi q') => [K' | b'] //.
     - by rewrite /U E => [[<-]].    
     exists (size Qn).+2; rewrite /U unfold_U_rec.
     case: (U_rec_spec (D phi) (size Qn).+1 psi q') => [ | [a']].
     - rewrite D_gq => ->; rewrite /U_step {1}unfold_bs.
       rewrite (U_rec_inl_spec psi (size Qn) phi q' (flatten Qn)).2 /=; last by exists Qn.
       by rewrite (gq_cns cns) val.
    rewrite U_rec_D; case E: (U_rec psi (size Qn) phi q') => [K' | b'] //.
    by move: val; rewrite -(U_rec_inr_spec)// unfold_U_rec E => [[->]].
  Qed.
End duality_operator.