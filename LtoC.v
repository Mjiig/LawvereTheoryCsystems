Require Export UniMath.CategoryTheory.limits.initial.
Require Export pullback_csystem.
Require Export Lawvere.

Open Scope cat.

Section LtoC.
Variable (lt : LT).

Definition homset_opp (C : precategory) ( p : has_homsets C) :
  has_homsets (opp_precat C).
Proof.
    unfold has_homsets.
    intros.
    apply p.
Defined.

Lemma succ_is_plus_1 (n : nat) : S n = n + 1.
  induction n.
  + apply idpath.
  + cbn.
    rewrite IHn.
    apply idpath.
Defined.

Definition L := LT_L lt.
Definition T := LT_T lt.

Definition ll (X:T) := LT_L_inv lt X.
Definition ft (X:T) := L ((ll X) - 1).

Lemma ll_of_ft (X:T) : ll(ft X) = ll(X) - 1.
Proof.
  unfold ft, ll.
  rewrite LT_L_cancel.
  apply idpath.
Defined.

Lemma ft_on_0_is_id (X : T) (q : ll X = 0) : ft X = X.
Proof.
  unfold ft.
  rewrite q.
  cbn.
  rewrite <- q.
  rewrite LT_L_cancel2.
  apply idpath.
Defined.

(* The inverse of the father function, only well defined in l-bijective Csystems *)
Definition child (Y : T) : T := L (ll Y + 1).

Lemma ll_child_gt0 (X : T) : ll (child X) > 0.
Proof.
  unfold child, ll.
  rewrite LT_L_cancel.
  rewrite <- succ_is_plus_1.
  apply natgthsn0.
Defined.

Lemma ft_ch_id (X : T) : ft (child X) = X.
Proof.
  unfold ft, child, ll.
  rewrite LT_L_cancel.
  rewrite plusminusnmm.
  rewrite LT_L_cancel2.
  apply idpath.
Defined.

Lemma ch_ft_id (X : T) (gt0 : ll X > 0) : child (ft X) = X.
Proof.
  unfold child, ft, ll.
  rewrite LT_L_cancel.
  rewrite (minusplusnmm (LT_L_inv lt X) 1 gt0).
  apply LT_L_cancel2.
Defined.

Definition general_coprod (n m c : nat) (p : n+m = c) : 
  ∑inc: ((L n)-->(L c))×((L m)-->(L c)),
    isBinCoproduct T (L n) (L m) (L c) (pr1 inc) (pr2 inc).
Proof.
  pose (d:=LT_coprods lt n m).
  destruct p.
  use tpair.
  + split.
    - exact (#L (F_inc1 n m)).
    - exact (#L (F_inc2 n m)).
  + cbn.
    exact d.
Defined.

Lemma xminusplus (x : nat) (gt0 : x > 0) : x - 1 + 1 = x.
Proof.
  rewrite (minusplusnmm x 1 gt0).
  apply idpath.
Defined.

Definition x_is_coprod (X : T) (gt0 : ll X > 0) : 
  ∑inc: (ft X)-->X × (L 1)-->X, isBinCoproduct T (ft X) (L 1) X (pr1 inc) (pr2 inc).
Proof.
  pose (c:=general_coprod (ll X - 1) 1 (ll X) (xminusplus (ll X) gt0)).
  unfold ft.
  pose (q:=LT_L_cancel2 lt X).
  unfold L, ll in c.
  rewrite q in c.
  exact c.
Defined.

Definition x_coprod (X : T) (gt0 : ll X > 0) : BinCoproduct T (ft X) (L 1).
Proof.
  pose (is_coprod := x_is_coprod X gt0).
  use tpair.
    + use tpair.
      - exact X.
      - cbn.
        split.
        * exact (pr1 (pr1 is_coprod)).
        * exact (pr2 (pr1 is_coprod)).
    + cbn.
      exact (pr2 is_coprod).
Defined.

Definition sngt0 (m n : nat) (p : eq m (S n)) : m > 0.
Proof.
  rewrite p.
  apply natgthsn0.
Defined.

Definition ll_destruct (X : T) : (ll X = 0) ⨿ (ll X > 0).
Proof.
  pose (p := natchoice0 (ll X)).
  destruct p as [eq | gt].
  + left.
    exact (!eq).
  + right.
    exact gt.
Defined.

Definition p (X : T) : ft X --> X.
Proof.
  destruct (ll_destruct X) as [eq0 | gt0].
  + rewrite (ft_on_0_is_id X eq0).
    exact (identity X).
  + pose (coprod := x_coprod X gt0).
    exact (BinCoproductIn1 T coprod).
Defined.

Definition p2 (X : T) (gt0 : ll X > 0) : L 1 --> X.
Proof.
  pose (coprod := x_coprod X gt0).
  exact (BinCoproductIn2 T coprod).
Defined.

Definition emor' (Y : (T^op)) : T^op ⟦(ft (child Y)), Y⟧.
  apply (idtomor (C:=T^op) (ft (child Y)) Y (ft_ch_id Y)).
Defined.

Definition emor (Y : T) : T ⟦ Y, ft(child Y) ⟧.
  exact (emor' Y).
Defined.

Definition child_proj (X : T) : X --> child X := emor X · (p (child X)).

Definition q (X Y : T) (gt0 : ll X > 0) (f : ft(X) --> Y) : X --> child (Y).
Proof.
  pose (coprod:= x_coprod X gt0).
  exact (BinCoproductArrow T coprod (f · child_proj Y) (p2 (child Y) (ll_child_gt0 Y))).
Defined.

Lemma gt_irrelevance (n : nat) (a b : n > 0) : a = b.
Proof.
  apply proofirrelevance.
  exact (propproperty (natgth n 0)).
Defined.

Lemma p_inc (X : T) (gt0 : ll X > 0) : p X = BinCoproductIn1 T (x_coprod X gt0).
Proof.
  unfold p.
  destruct (ll_destruct X).
  + pose (gt0' := gt0).
    rewrite p0 in gt0'.
    induction (isirreflnatgth 0 gt0').
  + rewrite (gt_irrelevance (ll X) gt0 h).
    apply idpath.
Defined.

Lemma p2_inc (X : T) (gt0 : ll X > 0) : p2 X gt0 = BinCoproductIn2 T (x_coprod X gt0).
Proof.
  unfold p2.
  apply idpath.
Defined.

Lemma retransport (T : UU) (a b : T) (p : a = b) (P : T -> UU) (Z : P b):
  transportf P (p) (transportf P (!p) Z) = Z.
Proof.
  destruct p.
  cbn.
  unfold idfun.
  apply idpath.
Defined.

Lemma idtomor_is_transport (X Y : T) (eq : X = Y) : idtomor X Y eq = transportf (fun x => X --> x) eq (identity X).
Proof.
  destruct eq.
  cbn.
  unfold idfun.
  apply idpath.
Defined.

Lemma id_square (A B : T) (eq1 : A = B) (eq2 : ft A = ft B) : 
  (p A) · (idtomor A B eq1) = (idtomor (ft A) (ft B) (maponpaths ft eq1)) · (p B).
Proof.
  destruct eq1.
  cbn.
  rewrite id_right.
  rewrite id_left.
  apply idpath.
Defined.

Lemma idtomor_invert (A B : T) (eq : A = B) : idtomor (C:=T^op) A B eq = idtomor B A (!eq).
Proof.
  destruct eq.
  cbn.
  apply idpath.
Defined.

Lemma id_square_commute (X : T) (eq : X = child (ft X)) : 
  p X · transportf (fun x => X --> x) eq (identity X) = emor (ft X) · p (child (ft X)).
Proof.
  rewrite <- idtomor_is_transport.
  unfold emor, emor'.
  rewrite idtomor_invert.
  assert (! ft_ch_id (ft X) = maponpaths ft eq) as eq_irrelevance.
  {
    apply proofirrelevance.
    apply (LT_ob_set lt).
  }
  unfold T. (* This appears to do nothing, but it unfolds a hidden term coq can't handle on it's own *)
  rewrite eq_irrelevance.
  apply id_square.
  rewrite ft_ch_id.
  apply idpath.
Defined.

Lemma id_line_commute (X : T) (eq : X = child (ft X)) (gt0: ll X > 0) (gt0' : ll (child (ft X)) > 0):
  p2 X gt0 · transportf (fun x => X --> x) eq (identity X) = p2 (child (ft X)) gt0'.
Proof.
  destruct eq.
  cbn.
  unfold idfun.
  rewrite id_right.
  rewrite (gt_irrelevance (ll X) gt0 gt0').
  apply idpath.
Defined.

Lemma q_square (X Y : T) (gt0 : ll X > 0) (eq : Y = ft (child Y)) (f : ft X --> Y):
  f · ((idtomor Y (ft (child Y)) eq) · p (child Y)) = p X · q X Y gt0 f.
Proof.
  unfold q.
  rewrite (p_inc X gt0).
  unfold child_proj, emor, emor'.
  rewrite (BinCoproductIn1Commutes T (ft X) (L 1) (x_coprod X gt0)).
  rewrite idtomor_invert.
  assert (eq = (! ft_ch_id Y)) as eqeq.
  + apply proofirrelevance.
    apply LT_ob_set.
  + rewrite eqeq.
    apply idpath.
Defined.

Lemma assoc4 (A B C D E: T) (f : A --> B) (g: B --> C) (h : C --> D) (i : D --> E) :
  f · g · h · i = (f · (g · h)) · i.
Proof.
  rewrite assoc.
  apply idpath.
Defined.

Lemma comp_square_commute (X Y Z : T) (gt0 : ll X > 0) (gt0' : ll (child Y) > 0) (f : ft X --> Y) (g : ft (child Y) --> Z) :
  p X · (q X Y gt0 f · q (child Y) Z gt0' g) = (f · idtomor Y (ft (child Y)) (!ft_ch_id Y) · g) · child_proj Z.
Proof.
  rewrite <- assoc.
  unfold child_proj, emor, emor'.
  rewrite idtomor_invert.
  pose (sq1 := q_square (child Y) Z gt0' (! ft_ch_id Z) g).
  unfold T.
  unfold T in sq1.
  rewrite sq1.
  rewrite assoc.
  rewrite assoc.
  rewrite assoc4.
  rewrite (q_square X Y gt0).
  apply idpath.
Defined.

Lemma comp_line_commute (X Y Z : T) (gt0 : ll X > 0) (gt0' : ll (child Y) > 0) (gt0'' : ll (child Z) > 0) (f : ft X --> Y) (g : ft (child Y) -->  Z) :
  p2 X gt0 · q X Y gt0 f · q (child Y) Z gt0' g = p2 (child Z) gt0''.
Proof.
  unfold p2.
  unfold q.
  rewrite (BinCoproductIn2Commutes T (ft X) (L 1) (x_coprod X gt0)).
  unfold p2.
  rewrite (gt_irrelevance (ll (child Y)) (ll_child_gt0 Y) gt0').
  rewrite (BinCoproductIn2Commutes T (ft (child Y)) (L 1) (x_coprod (child Y) (gt0'))).
  rewrite (gt_irrelevance (ll (child Z)) (ll_child_gt0 Z) gt0'').
  apply idpath.
Defined.

Lemma Ax7 (X Y Z : T) (gt0 : ll X > 0) (gt0' : ll (child Y) > 0) (f : ft X --> Y) (g : ft (child Y) --> Z) :
  q X Y gt0 f · q (child Y) Z gt0' g = q X Z gt0 (f · idtomor Y (ft (child Y)) (!ft_ch_id Y) · g).
Proof.
  (* This protects these two instances of q from being unfolded *)
  set (q1 := q X Y gt0 f).
  set (q2 := q (child Y) Z gt0' g).
  unfold q.
  set (a := (f · idtomor Y (ft (child Y)) (! ft_ch_id Y) · g · child_proj Z)).
  set (b := (p2 (child Z) (ll_child_gt0 Z))).
  rewrite (BinCoproductArrowUnique T (ft X) (L 1) (x_coprod X gt0) (child Z) a b (q1 · q2)).
  + apply idpath.
  + rewrite <- p_inc.
    unfold q1, q2, a.
    apply comp_square_commute.
  + rewrite <- p2_inc.
    unfold q1, q2, b.
    rewrite assoc.
    apply comp_line_commute.
Defined.

Definition T_op_setcategory : setcategory.
  use tpair.
  + exact (opp_precat T).
  + split.
    - apply LT_ob_set.
    - apply homset_opp.
      apply homset_property.
Defined.

Definition T_tower_str : ltower_str T_op_setcategory.
  use tpair.
  + use tpair.
    - exact ll.
    - exact ft.
  + split.
    - apply ll_of_ft.
    - apply ft_on_0_is_id.
Defined.

Definition T_tower : ltower_precat := tpair _ T_op_setcategory T_tower_str.

Definition T_tower_with_p : ltower_precat_and_p := tpair _ T_tower p.

Definition T_tower_is_pointed : ispointed_type T_tower_with_p.
Proof.
  use tpair.
  + use tpair.
    - exact (L 0).
    - cbn.
      rewrite (LT_L_cancel lt).
      apply idpath.
  + cbn.
    intros.
    destruct t as [t1 t2].
    use total2_paths_f.
    - cbn.
      rewrite <- t2.
      rewrite LT_L_cancel2.
      apply idpath.
    - apply proofirrelevance.
      apply nateq.
Defined.

Definition T_pointed_tower : pltower_precat_and_p := tpair _ T_tower_with_p T_tower_is_pointed.

Definition LtoC_obj_C0 : lC0system.
Proof.
  use tpair.
    - use tpair.
      * exact T_pointed_tower.
      * cbn.
        unfold q_data_type.
        intros.
        use tpair; cbn in *.
        { exact (child Y). }
        exact (q X Y gt0 f).
    - cbn.
      split.
      * unfold C0ax4_type.
        cbn.
        change (isInitial T (L 0)).
        exact (pr1 (pr2 (pr2 lt))).
      * cbn.
        use tpair.
        { split.
          + unfold C0ax5a_type.
            cbn.
            intros.
            apply ll_child_gt0.
          + use tpair.
            - unfold C0ax5b_type.
              cbn.
              intros.
              apply ft_ch_id.
            - cbn.
              unfold C0ax5c_type.
              cbn.
              intros.
              unfold C0ax5b_mor.
              cbn.
              unfold q.
              rewrite (p_inc X gt0).
              unfold child_proj, emor, emor'.
              rewrite (BinCoproductIn1Commutes T (ft X) (L 1) (x_coprod X gt0)).
              rewrite assoc.
              apply idpath.
        }
        cbn.
        unfold C0ax6_type.
        cbn.
        split.
        {
          intros.
          unfold mor_to_constr.
          use total2_paths_f.
          + unfold mor_to_constr.
            cbn.
            apply ch_ft_id.
            exact gt0.
          + cbn.
            assert ((q X (ft X) gt0 (identity (ft X))) = transportf (λ x : T, X-->x) (!(ch_ft_id X gt0)) (identity X)) as q_val.
            - unfold q.
              set (f := identity (ft X) · child_proj (ft X)).
              set (g := p2 (child (ft X)) (ll_child_gt0 (ft X))).
              set (ident := transportf (λ x : T, T ⟦ X, x ⟧) (! ch_ft_id X gt0) (identity X)).
              rewrite <- (BinCoproductArrowUnique T (ft X) (L 1) (x_coprod X gt0) (child (ft X)) f g ident).
              * apply idpath.
              * rewrite <- p_inc.
                unfold f.
                rewrite id_left.
                apply id_square_commute.
              * rewrite <- p2_inc.
                unfold g.
                apply id_line_commute.
            - unfold T.
              rewrite q_val.
              apply retransport.
        }
        unfold C0ax7_type.
        cbn.
        intros.
        unfold mor_to_constr.
        use total2_paths_f. { apply idpath. }
        cbn.
        unfold C0ax5b_mor.
        cbn.
        rewrite idtomor_invert.
        apply Ax7.
Defined.

Definition q_continues_p2 (X Y : T) (gt0 : ll X > 0) (f : ft X --> Y) : 
  p2 (child Y) (ll_child_gt0 Y) = p2 X gt0 · q X Y gt0 f.
Proof.
  unfold q.
  set (p2Y := p2 (child Y) (ll_child_gt0 Y)).
  rewrite p2_inc.
  rewrite (BinCoproductIn2Commutes T (ft X) (L 1) (x_coprod X gt0)).
  apply idpath.
Defined.

Definition LtoC_obj_has_pullbacks : has_canonical_pullbacks LtoC_obj_C0.
Proof.
  cbn.
  unfold has_canonical_pullbacks.
  intros.
  cbn in *.
  unfold isPullback.
  intros.
  cbn in *.
  pose (y_coprod := x_coprod (child Y) (ll_child_gt0 Y)).
  use tpair.
   + use tpair.
      - exact (BinCoproductArrow T y_coprod h ((p2 X gt0) · k)).
      - cbn.
        split.
        * rewrite (p_inc (child Y) (ll_child_gt0 Y)).
          rewrite (BinCoproductIn1Commutes T (ft (child Y)) (L 1) y_coprod e).
          apply idpath.
        * apply (BinCoproductArrowsEq T (ft X) (L 1) (x_coprod X gt0)).
          { rewrite <- p_inc.
            rewrite assoc.
            rewrite <- (q_square X Y gt0 (!(ft_ch_id Y))).
            rewrite (p_inc (child Y) (ll_child_gt0 Y)).
            unfold y_coprod.
            rewrite assoc.
            rewrite <- assoc.
            rewrite (BinCoproductIn1Commutes T (ft (child Y)) (L 1) (x_coprod (child Y) (ll_child_gt0 Y))).
            unfold C0emor, C0ax5b_mor in H.
            cbn in H.
            rewrite idtomor_invert in H.
            unfold T.
            unfold T in H.
            rewrite H.
            apply idpath.
          }
          rewrite assoc.
          unfold q.
          rewrite (BinCoproductIn2Commutes T (ft X) (L 1) (x_coprod X gt0)).
          rewrite (p2_inc (child Y) (ll_child_gt0 Y)).
          rewrite (BinCoproductIn2Commutes T (ft (child Y)) (L 1) y_coprod ).
          apply idpath.
  + cbn.
    intros.
    destruct t as [tmor [th tk]].
    use total2_paths_f.
    - cbn.
      apply (BinCoproductArrowUnique T (ft (child Y)) (L 1) y_coprod e h (p2 X gt0 · k) tmor).
      * unfold y_coprod.
        rewrite <- p_inc.
        exact th.
      * unfold y_coprod.
        rewrite <- p2_inc.
        rewrite (q_continues_p2 X Y gt0 f).
        rewrite <- assoc.
        unfold T in *.
        rewrite tk.
        apply idpath.
    - cbn.
      apply dirprodeq; apply proofirrelevance; apply (homset_property T).
Defined.

Definition LtoC_obj : lCsystem' := tpair _ LtoC_obj_C0 LtoC_obj_has_pullbacks.
End LtoC.