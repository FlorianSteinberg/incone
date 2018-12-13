From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_mf.
Require Import all_cont FMop.
Require Import Psatz FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module continuous_universal.
  Structure type := Pack {
                        funQ : Type -> Type -> Type -> Type -> Type;
                        somefunQ: forall Q A Q' A', funQ Q A Q' A';
                        funQ_count: forall Q A Q' A',
                            Q \is_countable -> A \is_countable ->
                            Q' \is_countable -> A' \is_countable ->
                            (funQ Q A Q' A') \is_countable;
                        funA: Type -> Type -> Type -> Type -> Type;
                        somefunA: forall Q A Q' A', funA Q A Q' A';
                        funA_count: forall Q A Q' A',
                            Q \is_countable -> A \is_countable ->
                            Q' \is_countable -> A' \is_countable ->
                            (funA Q A Q' A') \is_countable;
                        F_M: forall Q A Q' A', (funQ Q A Q' A' -> funA Q A Q' A') -> (Q -> A) ->> (Q' -> A');
                        FM_universal: forall Q A Q' A' (F: (Q -> A) ->> (Q' -> A')),
                            Q -> A -> (Q' -> A') ->
                            Q \is_countable -> A \is_countable ->
                            Q' \is_countable -> A' \is_countable ->
                            F \is_continuous_operator -> exists psi, (F_M psi) \tightens F;
                        FM_cont_spec: forall Q A Q' A',
                            exists FqM FsM,
                              (forall psi,
                                dom (@F_M Q A Q' A' psi) \is_subset_of dom (FqM psi)
                                /\
                                dom (F_M psi) \is_subset_of dom (FsM psi))
                              /\
                              (forall psi,
                                (continuity_modulus (F_M psi)) \extends (FqM psi)
                                /\
                                (continuity_modulus (FqM psi)) \extends (FqM psi)
                                /\
                                (continuity_modulus (FsM psi)) \extends (FqM psi))
                              /\
                              (forall phi,
                                  (continuity_modulus (make_mf (fun psi' => F_M psi' phi)))
                                    \extends (make_mf (fun psi' => FsM psi' phi))
                                  /\
                                  (continuity_modulus (make_mf (fun psi' => FqM psi' phi)))
                                    \extends (make_mf (fun psi' => FsM psi' phi))
                                  /\
                                  (continuity_modulus (make_mf (fun psi' => FsM psi' phi)))
                                    \extends (make_mf (fun psi' => FsM psi' phi)));
                        D: forall Q A Q' A', (Q -> A) ->
                                                (funQ (funQ Q A Q' A') (funA Q A Q' A') Q' A' ->
                                                 funA (funQ Q A Q' A') (funA Q A Q' A') Q' A');
                        D_spec: forall Q A Q' A' psi phi,
                            (F_M (@D Q A Q' A' phi) psi) === F_M psi phi;
                        D_cntop: forall Q A Q' A', (F2MF (@D Q A Q' A')) \is_continuous_operator;
                      }.

End continuous_universal.                                             
                        
Notation F_M:= continuous_universal.F_M.
Arguments F_M {t} {Q} {A} {Q'} {A'}.
Notation FM_cont_spec:= continuous_universal.FM_cont_spec.
Notation funQ:= continuous_universal.funQ.
Notation funA:= continuous_universal.funA.
Notation somefunQ:= continuous_universal.somefunQ.
Notation somefunA:= continuous_universal.somefunA.
Notation funQ_count:= continuous_universal.funQ_count.
Notation funA_count:= continuous_universal.funA_count.
Notation FM_universal:= continuous_universal.FM_universal.
Notation D := continuous_universal.D.
Notation D_spec := continuous_universal.D_spec.
Notation D_cntop:= continuous_universal.D_cntop.

Section continuous_universals.
Context (Q A Q' A': Type).
Notation B:= (Q -> A).
Notation B':= (Q' -> A').
Context (U: continuous_universal.type).
Lemma FM_cont psi: (@F_M U Q A Q' A' psi) \is_continuous_operator.
Proof.
move => phi Fphi val.
have [FqM [FsM [dm' [cont' _]]]]:= FM_cont_spec U Q A Q' A'.
have [dm _]:= dm' psi; move: dm' => _.
have [cont _]:= cont' psi; move: FsM cont' => _ _.
have [ | qf mod]:= dm phi; first by exists Fphi.
exists qf => q'.                                      
have [a' crt]:= cont phi qf mod q'.
by apply/crt_icf/crt.
Qed.
End continuous_universals.