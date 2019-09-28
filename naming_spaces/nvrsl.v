From mathcomp Require Import all_ssreflect.
From mf Require Import all_mf classical_mf.
Require Import axioms all_cont naming_spaces FMop classical_mach Umach classical_cont classical_count.
Require Import Psatz Classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope name_scope.
Section continuous_universals.
  Structure continuous_universal :=
    {
      function_names: naming_space -> naming_space -> naming_space;
      F_M: forall B B', function_names B B' -> B ->> B';
      FM_univ: forall (B B': naming_space) (F: B ->> B'),
          F \is_continuous -> exists psi, (F_M psi) \tightens F;
      FM_cont: forall (B B': naming_space) (psi: function_names B B'), (F_M psi) \is_continuous;
    }.
  Coercion F_M: continuous_universal >-> Funclass.
End continuous_universals.

Section U_universal.
  Definition fun_names (B B': naming_space): naming_space.
    exists (seq (questions B * answers B) * (questions B'))%type (seq (questions B) + answers B')%type.
    apply/(nil, someq).
    apply/prod_count/Q_count/list_count/prod_count/A_count/Q_count.
    exact/sum_count/A_count/list_count/Q_count.
  Defined.

  Definition F_U: continuous_universal.
    exists (fun_names) (fun B B' (psi: fun_names B B') => \F_(U psi)).
    - by move => B B' F cont; apply/exists_associate/cont/Q_count/A_count/Q_count.
    by move => B B' psi; apply/FU_cont.
  Defined.    
End U_universal.

(*
Section computable_universals.
  Structure computable_universal :=
    {
      function_names: naming_space -> naming_space -> naming_space;
      M: forall B B', function_names B B' -> B -> nat * questions B' -> option (answers B');
      mu: forall B B', function_names B B' -> B -> nat * questions B' -> seq (questions B);
      mu_mod: forall B B' (psi: function_names B B'), (mu psi) \modulus_function_for (M psi);
      mu_modmod: forall B B' (psi: function_names B B'), (mu psi) \modulus_function_for (mu psi);
      psi: forall (B B': naming_space),
          (B -> nat * questions B' -> option (answers B')) ->
          (B -> nat * questions B' -> seq (questions B)) ->
          function_names B B';
      M_univ: forall (B B': naming_space) (N: B -> nat * questions B' -> option (answers B')) nu,
          nu \modulus_function_for N -> nu \modulus_function_for nu ->
          \F_(M (psi N nu)) \tightens \F_N;
    }. 

  Coercion M: computable_universal >-> Funclass.
  Context (U: computable_universal).

  Lemma M_cont B B' psi: (U B B' psi) \is_continuous_function.
  Proof. exact/modf_cont/mu_mod. Qed.

  Lemma FufM_cont B B' psi: \F_(use_first (U B B' psi)) \is_continuous.
  Proof. exact/cntf_mon_cont/sfrst_mon/sfrst_cntf/M_cont. Qed.

    
  Canonical cmpU2cU: continuous_universal.
  - exists (function_names U) (fun B B' psi => \F_(use_first (U B B' psi))).
    move => B B' F cont.
    have : exists mu, mu \modulus_for F /\ mu \modulus_for mu.
    + apply/exists_modmod; try exact/cont.
    have [cnt sur]:= count_enum (Q_count B).
    have := exists_minsec sur.
    apply/cont_exte; first exact/tight; first exact/FufM_cont.
    apply/sing_tight.
    Search _ tight continuous singlevalued.
    exact/FufM_cont.
End continuous_universals.
 *)