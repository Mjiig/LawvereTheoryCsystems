Require Export UniMath.CategoryTheory.limits.pullbacks.
Require Export TypeTheory.Csystems.lC0systems.
Require Export TypeTheory.Csystems.lCsystems.

Open Scope cat.

Definition has_canonical_pullbacks (CC : lC0system) := 
  ∏ (X Y : CC) (gt0: ll X > 0) (f : Y --> ft X), 
    isPullback 
      ((C0emor gt0 f) · f )
      (pX X) 
      (pX (f_star gt0 f))
      (q_of_f gt0 f)
      (C0ax5c gt0 f).

Definition lCsystem' := total2 (fun CC => has_canonical_pullbacks CC).

Lemma idftf_is_fft (CC : lC0system) (X Y : CC) (f : Y --> X) : (identity Y) · (ftf f) = f · (pX X).
Proof.
  rewrite (id_left (ftf f)).
  unfold ftf.
  apply idpath.
Defined.

Lemma ftn1_is_ft (CC : lC0system) (X : CC) : ftn 1 X = ft X.
Proof.
  apply idpath.
Defined.

Definition C0emor_inv { CC : lC0system }
           { X Y : CC } ( gt0 : ll X > 0 ) ( f : Y --> ft X ):
  Y --> ft ( f_star gt0 f ) := idtomor _ _ (pathsinv0 (@C0ax5b CC X Y gt0 f )).

Definition idmorcomp (C : precategory) (X Y : C) (p : X=Y) : idtomor Y X (!p) · idtomor X Y p = identity Y.
Proof.
  induction p.
  cbn.
  rewrite id_left.
  apply idpath.
Defined.

Lemma C0emor_cancellation { CC : lC0system } 
    { X Y : CC } (gt0 : ll X > 0) (f : Y--> ft X) : (C0emor_inv gt0 f) · (C0emor gt0 f) = identity Y.
Proof.
  unfold C0emor_inv, C0emor, C0ax5b_mor. apply idmorcomp.
Defined.

(*
Theorem canonical_pullbacks_to_Csystem (CC: lC0system) (pb : has_canonical_pullbacks CC) : lCsystem.
Proof.
  use tpair. { exact CC. }
  cbn.
  use tpair.
  - unfold sf_type.
    intros.
    use tpair.
    + rewrite ftn1_is_ft.
      rewrite ft_f_star.
      pose (comm:=idftf_is_fft CC X Y f).
      rewrite <- (C0emor_cancellation gt0 (ftf f)) in comm.
      rewrite <- assoc in comm.
      exact (pr1 (pr1 (pb X Y gt0 (ftf f) Y (C0emor_inv gt0 (ftf f)) f (comm)))).
    + cbn.
      set (p:=C0emor_cancellation gt0 (ftf f)).
      set (q:=(assoc (C0emor_inv gt0 (ftf f)) (C0emor gt0 (ftf f)) (ftf f))).
      set (r:= ft_f_star gt0 (ftf f)).
      set (s:= (internal_paths_rew_r (pr1 CC ⟦ Y, Y ⟧) (C0emor_inv gt0 (ftf f) · C0emor gt0 (ftf f)) 
                 (identity Y) (λ p0 : pr1 CC ⟦ Y, Y ⟧, p0 · ftf f = f · pX X) (idftf_is_fft CC X Y f) p)).
      cbn in s.
      fail.
*)