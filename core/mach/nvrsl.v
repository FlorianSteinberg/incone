From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_mf.
Require Import all_cont FMop Umach Ucont classical_mach.
Require Import Psatz FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module continuous_universal.
  Structure type := Pack {
                        funQ : Type -> Type -> Type -> Type -> Type;
                        funQ_count: forall Q A Q' A',
                            Q \is_countable -> A \is_countable ->
                            Q' \is_countable -> A' \is_countable ->
                            funQ Q A Q' A' \is_countable;
                        funA: Type -> Type -> Type -> Type -> Type;
                        funA_count: forall Q A Q' A',
                            Q \is_countable -> A \is_countable ->
                            Q' \is_countable -> A' \is_countable ->
                            funA Q A Q' A' \is_countable;
                        F_M: forall Q A Q' A', (funQ Q A Q' A' -> funA Q A Q' A') -> (Q -> A) ->> (Q' -> A');
                        FM_universal: forall Q A Q' A' (F: (Q -> A) ->> (Q' -> A')),
                            Q -> A -> (Q' -> A') ->
                            Q \is_countable -> A \is_countable ->
                            Q' \is_countable -> A' \is_countable ->
                            F \is_continuous_operator -> exists psi, (F_M psi) \tightens F;
                        FM_cont_spec: forall Q A Q' A',
                            exists FqM FsM,
                              forall psi phi,
                                dom (@F_M Q A Q' A' psi) \is_subset_of dom (FqM psi)
                                /\
                                dom (F_M psi) \is_subset_of dom (FsM psi)
                                /\
                                (forall qf,
                                    FqM psi phi qf ->
                                    continuity_modulus (F_M psi) phi qf
                                    /\
                                    continuity_modulus (FqM psi) phi qf
                                    /\
                                    continuity_modulus (FsM psi) phi qf)
                                /\
                                (forall sf,
                                    FsM psi phi sf ->
                                    continuity_modulus
                                      (make_mf (fun psi' => F_M psi' phi))
                                      psi sf
                                    /\
                                    continuity_modulus
                                      (make_mf (fun psi' => FqM psi phi))
                                      psi sf
                                    /\
                                    continuity_modulus
                                      (make_mf (fun psi' => FsM psi phi))
                                      psi sf)
                                       ;
                              
                      }.  
End continuous_universal.                                             
