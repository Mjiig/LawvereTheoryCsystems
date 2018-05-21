Require Export UniMath.Foundations.NaturalNumbers.
Require Export UniMath.CategoryTheory.Categories.
Require Export UniMath.CategoryTheory.functor_categories.
Require Export UniMath.CategoryTheory.limits.initial.
Require Export UniMath.CategoryTheory.limits.bincoproducts.
Require Export UniMath.Foundations.UnivalenceAxiom.

(* First we define the category F *)

(* Proofs of the greater than relation are unique, so this is the type of natural numbers
less than n. We know this because the greater than relation is an hprop *)
Definition stn (n : nat) : UU := total2 ( fun x : nat => n > x).

Definition stn_isaset (n : nat) : isaset (stn n).
Proof.
  apply (isofhleveltotal2 2).
  - exact isasetnat.
  - intros.
    assert (isofhlevel 1 (n>x)).
    + apply natgth.
    + apply hlevelntosn; assumption.
Defined.

Lemma stn_nat_eq (n : nat) (a b : stn n) (p : (pr1 a) = (pr1 b)) : a=b.
Proof.
  use total2_paths_f.
  assumption.
  apply proofirrelevance.
  apply natgth.
Defined.

Definition F_mor (n m : nat) := stn(n) -> stn(m).

Definition F_ob_mor := precategory_ob_mor_pair nat F_mor.

Definition F_identity (n : nat) : (F_mor n n) := (fun x => x).

Definition F_comp (a b c : nat) (f : F_mor a b) (g : F_mor b c) :=
  fun (x : stn a) => g (f x).

Definition F_data := precategory_data_pair F_ob_mor F_identity F_comp.

Open Scope cat.

(*I'm not sure why Coq fails to infer this, so let's be explicit...*)
Notation "f · g" := (compose (C:=F_data) f g).

Definition F_left_comp (n m : nat) (f : F_mor n m) : 
  (F_identity n) · f = f.
Proof.
  apply idpath.
Defined.

Definition F_right_comp (n m : nat) (f : F_mor n m) : 
  f · (F_identity m) = f.
Proof.
  apply idpath.
Defined.

Definition F_assoc_comp (k l m n : nat) (f : F_mor k l) (g : F_mor l m) (h : F_mor m n) :
  (f · g) · h = f · (g · h).
Proof.
  apply idpath.
Defined.

Definition F_is_precategory := mk_is_precategory (C:=F_data) F_left_comp F_right_comp F_assoc_comp.

Definition F_pre : precategory := mk_precategory F_data F_is_precategory.

(*Surely this is already proven somewhere? *)
Lemma hlevel2isaset (X:UU) (p : isofhlevel 2 X) : isaset X.
Proof.
  assumption.
Defined.

Definition F_has_homsets (n m : nat) : isaset (F_mor n m).
Proof.
  change isaset with (isofhlevel 2).
  apply impred.
  intros.
  apply stn_isaset.
Defined.

Definition F : category := category_pair F_pre F_has_homsets.

(* We define the coproduct inclusions in F *)

Lemma m_lt_sn {n m} (P : n > m) : S n > m.
Proof.
  apply (istransnatgth (S n) (S m) m).
  + cbn.
    assumption.
  + exact (natgthsnn m).
Defined.

Lemma x_lt_nm {n m x : nat} (p : n > x) : (n + m) > x.
Proof.
  induction m.
  + rewrite natplusr0.
    assumption.
  + rewrite natplusnsm.
  exact (m_lt_sn IHm).
Defined.

Lemma xn_lt_nm {n m x : nat} (p : m > x) : (n + m) > (n + x).
Proof.
  induction n.
  + rewrite !natplusl0.
    assumption.
  + cbn.
    cbn in IHn.
    assumption.
Defined.

Definition F_inc1 (n m : nat) : F_mor n (n+m) := 
  (fun x => tpair _ (pr1 x) (x_lt_nm (pr2 x))).

Definition F_inc2 (n m : nat) : F_mor m (n+m) := 
  (fun x => tpair _ (n + (pr1 x)) (xn_lt_nm (pr2 x))).

Lemma t (b : nat) : ∏ a : nat, b>=a -> a + (b - a) = b.
Proof.
  induction b.
  - intros.
    induction a.
    + apply idpath.
    + induction (nopathsfalsetotrue X).
  - intros.
    induction a.
    + apply idpath.
    + cbn.
      rewrite (IHb a).
      * apply idpath.
      * apply X.
Defined.

Lemma s (a b d : nat) (p : b>=d) (q : a > b) : a - d > b - d.
Proof.
  apply (natgthandpluslinv (a - d) (b - d) d).
  rewrite (t b d p).
  rewrite (t a d).
  - assumption.
  - apply natgthtogeh.
    apply (natgthgehtrans a b d q p).
Defined.

Lemma r (n m x : nat) (p : x >= n) (q : n+m > x) : m > x - n.
Proof.
  assert (n + m - n > x - n).
  apply (s (n+m) x n p q).
  rewrite (natpluscomm n m) in X.
  rewrite plusminusnmm in X.
  assumption.
Defined.

Definition F_coprod_rect 
  (k n m : nat) (f : F_mor n k) (g : F_mor m k) : 
  F_mor (n+m) k :=
    fun (x : stn (n+m)) => 
      coprod_rect 
        (fun _ => stn k)
        (fun p =>  f (tpair _ (pr1 x) p))
        (fun p =>  g (tpair _ ((pr1 x) - n) (r n m (pr1 x) p (pr2 x))))
        (natlthorgeh (pr1 x) n).

Check natlthorgeh.

Lemma eqfuneqatpoint (A B : UU) (x : A) (f g : A -> B) (p : f = g) : f x = g x.
Proof.
  rewrite p.
  apply idpath.
Defined.

(* This could definitely do with a refactor... *)
Definition F_coprods (n m : nat) : isBinCoproduct F n m (n + m) (F_inc1 n m) (F_inc2 n m).
Proof.
  use mk_isBinCoproduct.
  - exact F_has_homsets.
  - intros.
    use iscontrpair.
    + use tpair.
      * exact (F_coprod_rect c n m f g).
      * cbn.
        split.
        { apply funextfun.
          unfold homot.
          intro.
          unfold F_comp, F_inc1, F_coprod_rect.
          cbn.
          destruct (natlthorgeh (pr1 x) n).
          { cbn.
            apply maponpaths.
            apply stn_nat_eq.
            apply idpath.
          }
          unfold natgeh in h.
          destruct x as [x xn].
          apply natlehtonegnatgth in h as h1.
          induction (h1 xn).
        }
        apply funextfun.
        unfold homot.
        intro.
        unfold F_comp, F_inc2, F_coprod_rect.
        cbn.
        destruct (natlthorgeh (n + pr1 x) n).
        { change (n + pr1 x < n) with (n > n + pr1 x) in h.
          induction (negnatgthnplusnm n (pr1 x) h).
        }
        cbn.
        apply maponpaths.
        apply stn_nat_eq.
        cbn.
        rewrite natpluscomm.
        apply plusminusnmm.
    + intros.
      use total2_paths_f.
      * apply funextfun.
        unfold homot.
        intro.
        unfold F_comp, F_coprod_rect.
        cbn.
        destruct t0 as [k [eq1 eq2]].
        destruct (natlthorgeh (pr1 x) n).
        { cbn.
          apply (eqfuneqatpoint (stn n) (stn c) (pr1 x,, h)) in eq1.
          unfold F_inc1 in eq1.
          cbn in eq1.
          unfold F_comp in eq1.
          cbn in eq1.
          assert (x = (pr1 x,, x_lt_nm h)).
          { apply stn_nat_eq.
            apply idpath.
          }
          destruct x as [x xnm].
          cbn.
          cbn in eq1, X.
          rewrite <- X in eq1.
          assumption.
        }
        cbn.
        apply (eqfuneqatpoint (stn m) (stn c) (pr1 x - n,, r n m (pr1 x) h (pr2 x))) in eq2.
        unfold F_inc2 in eq2.
        cbn in eq2.
        unfold F_comp in eq2.
        cbn in eq2.
        assert (x = n + (pr1 x - n),, xn_lt_nm (r n m (pr1 x) h (pr2 x))).
        { apply stn_nat_eq.
          cbn.
          apply pathsinv0.
          apply t.
          assumption.
        }
        destruct x as [x xnm].
        cbn.
        cbn in eq2, X.
        rewrite <- X in eq2.
        assumption.
      * apply proofirrelevance.
        apply isofhleveldirprod.
        { assert (isofhlevel 2 (F_mor n c)).
          { apply F_has_homsets. }
          unfold isofhlevel in X.
          unfold isofhlevel.
          intros.
          apply X.
        }
        assert (isofhlevel 2 (F_mor m c)).
        { apply F_has_homsets. }
        unfold isofhlevel in X.
        unfold isofhlevel.
        intros.
        apply X.
Defined.

(* We define the type of a Lawvere theory *)

Definition LT_data := total2 (fun (T:category) => functor F T).

Definition LT_T (LT : LT_data) : category := pr1 LT.

Definition LT_L (LT : LT_data) : functor F (LT_T LT) := pr2 LT.

(*The coercion here could be automatic but I don't trust it*)
Definition LT_bij_on_objects (LT : LT_data) := 
  isweq (functor_on_objects (LT_L LT)).

Definition LT_L0_initial (LT : LT_data) := isInitial (LT_T LT) (LT_L LT 0).

Definition LT_has_coprods (LT : LT_data) := 
  ∏ n m : nat, 
    isBinCoproduct 
      (LT_T LT)
      (LT_L LT n)
      (LT_L LT m)
      (LT_L LT (n+m))
      (#(LT_L LT) (F_inc1 n m)) 
      (#(LT_L LT) (F_inc2 n m)).

Definition is_LT (LT : LT_data)
  := (LT_bij_on_objects LT) × (LT_L0_initial LT) × (LT_has_coprods LT).

Definition LT := total2(fun LT_data : LT_data => is_LT LT_data).

Definition LT_data_from_LT (A : LT) : LT_data := pr1 A.
Coercion LT_data_from_LT : LT >-> LT_data.

(* A couple of lemmas about Lawvere Theories *)

Definition LT_L_weq (lt : LT) : weq nat (LT_T lt) :=
  tpair _ (functor_on_objects (LT_L lt)) (pr1 (pr2 lt)).

Definition LT_L_inv (lt : LT) : (LT_T lt) -> nat :=
  invmap (LT_L_weq lt).

Definition LT_coprods (lt : LT) : LT_has_coprods lt := pr2 (pr2 (pr2 lt)).

Lemma LT_L_cancel (lt : LT) (x : nat) : LT_L_inv lt (LT_L lt x) = x.
Proof.
  unfold LT_L_inv.
  apply homotinvweqweq.
Defined.

Lemma LT_L_cancel2 (lt : LT) (x : LT_T lt) : LT_L lt (LT_L_inv lt x) = x.
Proof.
  unfold LT_L_inv.
  (* Babysit coq's unification slightly... *)
  change (functor_on_objects (LT_L lt)) with (pr1weq (LT_L_weq lt)).
  apply homotweqinvweq.
Defined.

(* The category of Lawvere theories *)

Definition LT_mor_data (A B : LT) := functor (LT_T A) (LT_T B).

Definition is_LT_mor (A B : LT) (G : LT_mor_data A B) := 
  functor_composite (LT_L A) G = (LT_L B).

Definition LT_mor (A B : LT) := total2 (fun mor_data => is_LT_mor A B mor_data).

Lemma LT_ob_set (A : LT) : isaset (LT_T A).
Proof.
  apply (isofhlevelweqf 2 (X:=nat)).
  - use tpair.
    + exact (LT_L A).
    + exact (pr1 (pr2 A)).
  - apply isasetnat.
Defined.

Lemma is_LT_mor_prop (A B : LT) (G : LT_mor_data A B) : isaprop (is_LT_mor A B G).
Proof.
  assert (isofhlevel 2 (functor F (LT_T B))).
  - apply functor_isaset.
    + exact (homset_property (LT_T B)).
    + apply (LT_ob_set B).
  - unfold isaprop.
    unfold is_LT_mor.
    exact (X (LT_L A ∙ G) (LT_L B)).
Defined.

Definition LT_cat_ob_mor := precategory_ob_mor_pair LT LT_mor.

Definition LT_cat_identity (A : LT) : LT_mor A A.
Proof.
  use tpair.
  - exact (functor_identity (LT_T A)).
  - cbn.
    unfold is_LT_mor.
    apply functor_identity_right.
Defined.

Definition LT_cat_composition (A B C : LT) (G : LT_mor A B) (H: LT_mor B C) : LT_mor A C.
Proof.
  destruct G as [G G_proof].
  destruct H as [H H_proof].
  use tpair.
  - exact (functor_composite G H).
  - cbn.
    unfold is_LT_mor.
    rewrite <- (functor_assoc F (LT_T A) (LT_T B) (LT_T C) (LT_L A) G H).
    rewrite G_proof.
    rewrite H_proof.
    apply idpath.
Defined.

Definition LT_cat_data : precategory_data := 
  precategory_data_pair LT_cat_ob_mor LT_cat_identity LT_cat_composition.

Definition LT_cat_is_precategory : is_precategory LT_cat_data.
Proof.
  repeat split; cbn; intros.
  - unfold LT_cat_composition.
    use total2_paths_f.
    + cbn.
      apply functor_identity_left.
    + apply proofirrelevance.
      apply is_LT_mor_prop.

  - unfold LT_cat_composition.
    use total2_paths_f.
    + cbn.
      apply functor_identity_right.
    + apply proofirrelevance.
      apply is_LT_mor_prop.

  - unfold LT_cat_composition.
    use total2_paths_f.
    + cbn.
      rewrite <- functor_assoc.
      apply idpath.
    + apply proofirrelevance.
      apply is_LT_mor_prop.
Defined.

Definition LT_precat : precategory := mk_precategory LT_cat_data LT_cat_is_precategory.

Definition LT_cat_has_homsets (A B : LT) : isaset (LT_mor A B).
Proof.
  change isaset with (isofhlevel 2).
  unfold LT_mor.
  apply isofhleveltotal2.
  + apply (functor_isaset).
    - exact (homset_property (LT_T B)).
    - apply (LT_ob_set B).
  + intros F.
    apply hlevelntosn.
    apply is_LT_mor_prop.
Defined.

Definition LT_cat : category := category_pair LT_precat LT_cat_has_homsets.

Close Scope cat.