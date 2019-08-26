Section baire_fprd.
  Context (B B' D D': naming_space).
  
  Definition fprd_rlzr (F: B ->> D) (G: B' ->> D'):=
    make_mf (fun phipsi FphiGpsi =>
	       FphiGpsi = pair (unpair FphiGpsi)
	       /\
	       (F ** G) (unpair phipsi) (unpair FphiGpsi)).

  Lemma fprd_rlzr_spec (F: B ->> D) (G: B' ->> D'):
    realizer (prod_dict a a') (prod_dict t t') (fprd_rlzr F G) (F ** G).
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
      move => psi /coin_agre coin Fpsi [ np' [/=val'l val'r]].
      rewrite np np'; apply injective_projections => //=.
      rewrite (crt (lprj phi) _ (lprj FGphi))//; last exact/coin_ref.
      rewrite (crt (lprj psi) _ (lprj Fpsi))// coin_agre /lprj => q' lstn.
      by rewrite (coin (inl q')) //; apply (mapl (Lf q) q').
    have [psi' crt]:= mod' q'; exists (FGphi (inr q')).
    move => psi /coin_agre coin Fpsi [ np' [/=val'l val'r]].
    rewrite np np'; apply injective_projections => //=.
    rewrite (crt (rprj phi) _ (rprj FGphi))//; last exact/coin_ref.
    rewrite (crt (rprj psi) _ (rprj Fpsi))// coin_agre /rprj => q lstn.
    by rewrite (coin (inr q)) //; apply (mapr (Lf' q') q).
  Qed.

  Definition lcry_rlzr (F: bair_product ->> D) (phi: B): B' ->> D :=
    (make_mf (fun psi => F (pair a a' (phi,psi)))).
  
  Fixpoint collect_right S T (L: seq.seq (S + T)) :=
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
  
  Fixpoint collect_left S T (L: seq.seq (S + T)) :=
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