From mathcomp Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype.
From mf Require Import all_mf classical_mf.
Require Import all_cont seq_cont PhiN FMop classical_count.
Require Import axioms Classical Psatz ChoiceFacts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope name_scope.
Section classical_lemmas.
  Context (Q Q' A A': Type) (noq: Q).
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Local Open Scope name_scope.
  Context (cnt: nat -> Q) (sec: Q -> nat) (ms: minimal_section Q cnt sec).
  Notation minimal_modulus := (minimal_modulus cnt sec).
  Notation init_seg := (iseg cnt).
  Notation max_elt := (max_elt sec).
  
  Lemma F2MF_cont_choice (f: B -> B'): FunctionalChoice_on Q' (seq Q) ->
    f \is_continuous_function <->
    forall phi q', exists L, forall psi, phi \coincides_with psi \on L -> f phi q' = f psi q'.
  Proof.
    move => choice.
    split=> [cont phi q' | cont phi].
    - by have [Lf mod]:= cont phi; exists (Lf q') => psi; apply/mod.
    by have [Lf mod]:= choice _ (cont phi); exists Lf => q' psi; apply/mod.
  Qed.

  Lemma cert_cdom (F: B ->> B') phi q' a':
    ~ phi \from closure (dom F) -> exists L, certificate F L phi q' a'.
  Proof.
    move => neg.
    have [L Lprop]: exists L, forall psi, ~ (phi \coincides_with psi \on L /\ psi \from dom F).
    - apply NNPP => ex; apply neg => L; apply NNPP => negi.
      exfalso; apply ex; exists L => psi [] coin val.
      by apply negi; exists psi.
    exists L => psi coin Fpsi FpsiFpsi.
    exfalso; apply (Lprop psi).
    by split; last exists Fpsi.
  Qed.

  Lemma dom_minmod_choice (F: B ->> B'):
    FunctionalChoice_on Q' nat -> FunctionalCountableChoice_on bool ->
    dom (minimal_modulus F) === dom (continuity_modulus F).
  Proof.
    move => choice choice' phi.
    split => [[mf [mod min]] | [Lf mod]]; first by exists (fun q' => init_seg (mf q')).
    pose R q' n :=
      (exists a', certificate F (init_seg n) phi q' a')
      /\
      forall (L: seq Q), (exists a', certificate F L phi q' a') -> n <= max_elt L.
    have Rtot: forall q', exists n, R q' n.
    - move => q'; pose p n := exists a', certificate F (init_seg n) phi q' a'.
      have ex: exists n, p n.
      - exists (max_elt (Lf q')); have [a' crt]:= (mod q').
        by exists a'; apply/crt_exte/crt/iseg_melt.
      have [n [prp min]]:= well_order_nat_choice choice' ex; exists n; split => //L [a' crt].
      by apply/min; exists a'; apply/crt_exte/crt/iseg_melt.
    have [mf mfprop] := choice _ Rtot; exists mf.
    by split => [q' | L q']; [apply/(mfprop q').1 | apply/(mfprop q').2].
  Qed.

  Lemma dom_minmod (F: B ->> B'):
    Q' \is_countable -> dom (minimal_modulus F) === dom (continuity_modulus F).
  Proof.
    move => count.
    apply/dom_minmod_choice; try apply/countable_choice => //.
    exact/nat_count.
  Qed.

  Lemma exists_minmod_choice (F: B ->> B'):
    FunctionalChoice_on Q' nat -> FunctionalChoice_on B (Q' -> nat) ->
    FunctionalCountableChoice_on bool ->
    F \is_continuous ->
    exists mf, forall phi, phi \from dom F -> minimal_modulus F phi (mf phi).
  Proof.
    move => choice' choice choice''.
    have [mf icf]:= exists_choice (minimal_modulus F) (fun _ => 0) choice => /cont_spec cont.
    exists mf => phi [Fphi val].
    have [ | mf' mod']:= (dom_minmod_choice F choice' choice'' phi).2.
    - by apply/cont; exists Fphi.
    by split => [q' | Lf mod q']; have [ | cont' prp]:= icf phi; try apply/prp; try by exists mf'.
  Qed.
  
  Lemma exists_modmod_fullchoice (F: B ->> B'):
    F \is_continuous ->
    exists mu, mu \modulus_for F /\ mu \modulus_for mu.
  Proof.
    move => cont.
    have [mu mod]:= exists_minmod_choice full_choice full_choice full_choice cont.
    exists ((F2MF (fun phi q' => iseg cnt (mu phi q')))|_(dom F)).
    split.
    - split => [phi phifd | phi _ [phifd <-]]; first by exists (fun q' => init_seg (mu phi q')).
      by have []:= mod phi phifd.
    have [ecQ' _]:= @classic_eqClass Q' full_choice.
    pose etQ' := Equality.Pack ecQ' Q.
    have [_ md]:= @minm_modmod etQ' Q A A' F cnt sec ms mu mod.
    split => // phi _ [phifd <-] q'.
    have [ | n md']//:= md phi (fun q' => init_seg (mu phi q')) _ q'.
    exists (init_seg (mu phi q')) => psi coin mfpsi [psifd <-].
    have ->:= md' psi coin (mu psi); last by split; last exact/mod.
    by have ->:= md' phi (coin_ref _ _) (mu phi); last by split; last exact/mod.
  Qed.
End classical_lemmas.  

Lemma scnt_cont Q A Q' A' (F: (Q -> A) ->> (Q' -> A')):
  Q \is_countable -> Q' \is_countable -> F \is_sequentially_continuous -> F \is_continuous.
Proof.
  have nat_choice: FunctionalCountableChoice by apply/countable_choice/nat_count.
  case: (classic (inhabited Q)) => [[someq] | neg _ _ scnt]; last first.
  - move => phi Fphi val; exists (fun _ => nil) => q' phi' coin Fphi' val'.
    suff lmt: Fphi \is_limit_of (cnst Fphi').
    + by have [n prp]:= lmt q'; symmetry; apply/(prp n).
    apply/scnt/val; last by move => n; apply/val'.
    move => q; exists 0 => m ineq.
    by exfalso; apply/neg/inhabits/q.
  move => /count_enum/(inh_enum someq) [cnt sur] count' scnt phi Fphi val.
  have [sec ms]:= exists_minsec sur.
  suff: forall q', exists L, certificate F L phi q' (Fphi q') by apply countable_choice.
  move => q'.
  apply/not_all_not_ex => prp.
  have /nat_choice [phin phinprp]: forall n, exists psi,
        phi \coincides_with psi \on (iseg cnt n)
        /\
        psi \from dom F
        /\
        forall Fpsi, F psi Fpsi -> Fpsi q' <> Fphi q'.
  - move => n.
    have /not_all_ex_not [psi cnd]:= prp (iseg cnt n).
    exists psi.
    split; first exact/(not_imply_elim _ _ cnd).
    split => [ | Fpsi val' eq].
    + have /not_all_ex_not [Fpsi cnd']:= (not_imply_elim2 _ _ cnd).
      by exists Fpsi; apply/(not_imply_elim _ _ cnd').
    apply/cnd => coin Fpsi' val''.
    by rewrite (scnt_sing scnt val'' val').
  have lmt: phi \is_limit_of phin.
  - apply/lim_coin => L; exists (max_elt sec L) => m ineq.
    apply/coin_subl/(phinprp m).1.
    exact/subs_trans/iseg_subl/ineq/iseg_melt.
  have /nat_choice [Fphin lmts]: forall n, exists Fphi, F (phin n) Fphi.
  - by move => n; have [_ []]:= phinprp n.
  have [N eq]:= scnt phi phin Fphin Fphi lmt lmts val q'.
  have [_ [_ prp']]:= phinprp N.
  apply/prp'; first exact/lmts.
  by symmetry; apply/eq.
Qed.

Section mathcomp.
  Context (Q': eqType) (Q A A': Type).
  Notation B := (Q -> A).
  Notation B' := (Q' -> A').
  Local Open Scope name_scope.
  Context (cnt: nat -> Q) (sec: Q -> nat) (ms: minimal_section Q cnt sec).
  Notation minimal_modulus := (minimal_modulus cnt sec).
  Notation init_seg := (iseg cnt).
  Notation max_elt := (max_elt sec).

  Lemma F2MF_cont_eqT_choice (f: B -> B'): Q' \is_countable ->
    f \is_continuous_function <->
    forall phi q', exists L, forall psi, phi \coincides_with psi \on L -> f phi q' = f psi q'.
  Proof.
    by move => count; apply/F2MF_cont_choice/count_eqT_choice; last by left; apply/inhabits/nil.
  Qed.
End mathcomp.
