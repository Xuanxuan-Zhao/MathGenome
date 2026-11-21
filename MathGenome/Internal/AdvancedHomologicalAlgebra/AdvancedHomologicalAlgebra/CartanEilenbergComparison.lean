import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CartanEilenbergComparison
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SplitRowExtension
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DoubleTotalization

/-! Comparison of arbitrary Cartan–Eilenberg injective resolutions.
Source: HA-G02, notes/002/advanced-homological-algebra.tex, 2499–2550.
-/

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace AdvancedHomologicalAlgebra.CartanEilenbergComparison

open CartanEilenbergData SplitRowExtension

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Descent through an exact pair followed by extension along the next kernel.
This is relative injectivity along admissible maps, not injectivity in the
abelian category of all horizontal complexes. -/
lemma descend_and_extend {U V W X T : CochainComplex C ℤ}
    (a : U ⟶ V) (b : V ⟶ W) (c : W ⟶ X)
    (hab : a ≫ b = 0) (hbc : b ≫ c = 0)
    (hex₁ : (ShortComplex.mk a b hab).Exact)
    (hex₂ : (ShortComplex.mk b c hbc).Exact)
    (hc : Admissible (kernel.ι c)) (hT : HasExtensionProperty T)
    (f : V ⟶ T) (hf : a ≫ f = 0) :
    ∃ g : W ⟶ T, b ≫ g = f := by
  let e : V ⟶ kernel c := kernel.lift c b hbc
  have he : Epi e := hex₂.epi_kernelLift
  have hae : a ≫ e = 0 := by
    apply (cancel_mono (kernel.ι c)).1
    simp [e, Category.assoc, hab]
  let S := ShortComplex.mk a e hae
  let φ : S ⟶ ShortComplex.mk a b hab :=
    { τ₁ := 𝟙 U
      τ₂ := 𝟙 V
      τ₃ := kernel.ι c
      comm₂₃ := by simp [S, e] }
  have hS : S.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hex₁
  obtain ⟨g, hg⟩ := hT (kernel.ι c) hc (hS.desc f hf)
  refine ⟨g, ?_⟩
  calc
    b ≫ g = e ≫ (kernel.ι c ≫ g) := by simp [e]
    _ = e ≫ hS.desc f hf := by rw [hg]
    _ = f := hS.g_desc f hf

variable {K L : CochainComplex C ℤ}

lemma augmentation_comp_d (R : ResolutionData K) :
    R.augmentation ≫ R.bicomplex.flip.d 0 1 = 0 := by
  ext p
  exact R.augmentation_d p

lemma row_exact_zero (R : ResolutionData K) :
    (ShortComplex.mk R.augmentation (R.bicomplex.flip.d 0 1)
      (augmentation_comp_d R)).Exact := by
  apply exact_of_degreewise_exact
  intro p
  exact (R.terms p).exact_zero

lemma row_exact_pos (R : ResolutionData K) (q : ℤ) (hq : 0 < q) :
    (ShortComplex.mk (R.bicomplex.flip.d (q - 1) q)
      (R.bicomplex.flip.d q (q + 1)) (R.bicomplex.flip.d_comp_d _ _ _)).Exact := by
  apply exact_of_degreewise_exact
  intro p
  exact ((R.bicomplex.X p).exactAt_iff' (q - 1) q (q + 1)
    (by simp) (by simp)).mp ((R.terms p).exact_pos q hq)

lemma descend_zero (R : ResolutionData K) (J : ResolutionData L) (r : ℤ) (hr : 0 ≤ r)
    (f : R.bicomplex.flip.X 0 ⟶ J.bicomplex.flip.X r)
    (hf : R.augmentation ≫ f = 0) :
    ∃ g : R.bicomplex.flip.X 1 ⟶ J.bicomplex.flip.X r,
      R.bicomplex.flip.d 0 1 ≫ g = f := by
  apply descend_and_extend R.augmentation (R.bicomplex.flip.d 0 1)
    (R.bicomplex.flip.d 1 2) (augmentation_comp_d R)
    (R.bicomplex.flip.d_comp_d _ _ _) (row_exact_zero R)
    (by simpa using row_exact_pos R 1 (by omega))
    (by simpa using verticalKernelAdmissible R 1 (by omega))
    (rowExtension J r hr) f hf

lemma descend_pos (R : ResolutionData K) (J : ResolutionData L) (q r : ℤ)
    (hq : 0 < q) (hr : 0 ≤ r)
    (f : R.bicomplex.flip.X q ⟶ J.bicomplex.flip.X r)
    (hf : R.bicomplex.flip.d (q - 1) q ≫ f = 0) :
    ∃ g : R.bicomplex.flip.X (q + 1) ⟶ J.bicomplex.flip.X r,
      R.bicomplex.flip.d q (q + 1) ≫ g = f := by
  apply descend_and_extend (R.bicomplex.flip.d (q - 1) q)
    (R.bicomplex.flip.d q (q + 1)) (R.bicomplex.flip.d (q + 1) (q + 1 + 1))
    (R.bicomplex.flip.d_comp_d _ _ _) (R.bicomplex.flip.d_comp_d _ _ _)
    (row_exact_pos R q hq) (by
      have h := row_exact_pos R (q + 1) (by omega)
      rw [show q + 1 - 1 = q by omega] at h
      exact h)
    (verticalKernelAdmissible R (q + 1) (by omega))
    (rowExtension J r hr) f hf

/-- The nonnegative vertical part, with objects the horizontal complexes. -/
noncomputable def nonnegativeRows (R : ResolutionData K) :
    CochainComplex (CochainComplex C ℤ) ℕ :=
  CochainComplex.of (fun n => R.bicomplex.flip.X (n : ℤ))
    (fun n => R.bicomplex.flip.d (n : ℤ) (↑n + 1))
    (fun n => by simp)

@[simp] lemma nonnegativeRows_X (R : ResolutionData K) (n : ℕ) :
    (nonnegativeRows R).X n = R.bicomplex.flip.X (n : ℤ) := rfl

@[simp] lemma nonnegativeRows_d (R : ResolutionData K) (n : ℕ) :
    (nonnegativeRows R).d n (n + 1) = R.bicomplex.flip.d (n : ℤ) (↑n + 1) := by
  apply CochainComplex.of_d

noncomputable def comparisonZero (R : ResolutionData K) (J : ResolutionData L) (f : K ⟶ L) :
    R.bicomplex.flip.X 0 ⟶ J.bicomplex.flip.X 0 :=
  Classical.choose (rowExtension J 0 (by omega) R.augmentation
    (augmentationAdmissible R) (f ≫ J.augmentation))

@[reassoc (attr := simp)] lemma augmentation_comparisonZero
    (R : ResolutionData K) (J : ResolutionData L) (f : K ⟶ L) :
    R.augmentation ≫ comparisonZero R J f = f ≫ J.augmentation :=
  Classical.choose_spec (rowExtension J 0 (by omega) R.augmentation
    (augmentationAdmissible R) (f ≫ J.augmentation))

noncomputable def comparisonOne (R : ResolutionData K) (J : ResolutionData L) (f : K ⟶ L) :
    R.bicomplex.flip.X 1 ⟶ J.bicomplex.flip.X 1 :=
  Classical.choose (descend_zero R J 1 (by omega)
    (comparisonZero R J f ≫ J.bicomplex.flip.d 0 1)
    (by rw [← Category.assoc, augmentation_comparisonZero, Category.assoc,
      augmentation_comp_d, comp_zero]))

@[reassoc (attr := simp)] lemma d_comparisonOne
    (R : ResolutionData K) (J : ResolutionData L) (f : K ⟶ L) :
    R.bicomplex.flip.d 0 1 ≫ comparisonOne R J f =
      comparisonZero R J f ≫ J.bicomplex.flip.d 0 1 :=
  Classical.choose_spec (descend_zero R J 1 (by omega)
    (comparisonZero R J f ≫ J.bicomplex.flip.d 0 1)
    (by rw [← Category.assoc, augmentation_comparisonZero, Category.assoc,
      augmentation_comp_d, comp_zero]))

lemma comparison_step (R : ResolutionData K) (J : ResolutionData L) (n : ℕ)
    (g : (nonnegativeRows R).X n ⟶ (nonnegativeRows J).X n)
    (g' : (nonnegativeRows R).X (n + 1) ⟶ (nonnegativeRows J).X (n + 1))
    (w : g ≫ (nonnegativeRows J).d n (n + 1) = (nonnegativeRows R).d n (n + 1) ≫ g') :
    ∃ g'' : (nonnegativeRows R).X (n + 2) ⟶ (nonnegativeRows J).X (n + 2),
      g' ≫ (nonnegativeRows J).d (n + 1) (n + 2) =
        (nonnegativeRows R).d (n + 1) (n + 2) ≫ g'' := by
  have hw : R.bicomplex.flip.d (n : ℤ) (↑n + 1) ≫ g' =
      g ≫ J.bicomplex.flip.d (n : ℤ) (↑n + 1) := by
    simpa using w.symm
  have hz : R.bicomplex.flip.d ((↑n + 1) - 1) (↑n + 1) ≫
      (g' ≫ J.bicomplex.flip.d (↑n + 1) (↑n + 1 + 1)) = 0 := by
    rw [add_sub_cancel_right, ← Category.assoc, hw, Category.assoc,
      d_comp_d, comp_zero]
  obtain ⟨g'', hg''⟩ := descend_pos R J (↑n + 1) (↑n + 1 + 1)
    (by omega) (by omega) _ hz
  exact ⟨g'', by simpa [nonnegativeRows_d, Nat.cast_add, Nat.cast_one] using hg''.symm⟩

/-- Recursive comparison on all nonnegative rows. -/
noncomputable def nonnegativeComparison (R : ResolutionData K) (J : ResolutionData L)
    (f : K ⟶ L) : nonnegativeRows R ⟶ nonnegativeRows J :=
  CochainComplex.mkHom _ _ (comparisonZero R J f) (comparisonOne R J f)
    (by simp)
    (fun n s => ⟨Classical.choose (comparison_step R J n s.1 s.2.1 s.2.2),
      Classical.choose_spec (comparison_step R J n s.1 s.2.1 s.2.2)⟩)

lemma negativeRow (R : ResolutionData K) (q : ℤ) (hq : q < 0) :
    IsZero (R.bicomplex.flip.X q) := by
  rw [IsZero.iff_id_eq_zero]
  ext p
  exact (R.nonnegative p q hq).eq_of_src _ _

/-- Extend a map on nonnegative rows by zero in negative vertical degrees. -/
noncomputable def extendRowsMap (R : ResolutionData K) (J : ResolutionData L)
    (t : nonnegativeRows R ⟶ nonnegativeRows J) :
    R.bicomplex.flip ⟶ J.bicomplex.flip :=
  CochainComplex.ofHom
    (fun q => match q with
      | .ofNat n => t.f n
      | .negSucc _ => 0)
    (fun q => by
      cases q with
      | ofNat n =>
        have ht := t.comm n (n + 1)
        simp only [nonnegativeRows_d] at ht
        exact ht
      | negSucc n => exact (negativeRow R _ (by omega)).eq_of_src _ _)

@[simp] lemma extendRowsMap_f (R : ResolutionData K) (J : ResolutionData L)
    (t : nonnegativeRows R ⟶ nonnegativeRows J) (n : ℕ) :
    (extendRowsMap R J t).f (n : ℤ) = t.f n := rfl

/-- A comparison in the source's horizontal/vertical convention. -/
noncomputable def comparison (R : ResolutionData K) (J : ResolutionData L) (f : K ⟶ L) :
    R.bicomplex ⟶ J.bicomplex :=
  (HomologicalComplex₂.flipFunctor C (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
    (extendRowsMap R J (nonnegativeComparison R J f))

lemma comparison_augmentation (R : ResolutionData K) (J : ResolutionData L) (f : K ⟶ L) :
    R.augmentation ≫
      ((HomologicalComplex₂.flipFunctor C (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
        (comparison R J f)).f 0 = f ≫ J.augmentation := by
  exact augmentation_comparisonZero R J f

noncomputable def restrictRowsMap (R : ResolutionData K) (J : ResolutionData L)
    (t : R.bicomplex.flip ⟶ J.bicomplex.flip) :
    nonnegativeRows R ⟶ nonnegativeRows J :=
  CochainComplex.ofHom (fun n => t.f (n : ℤ))
    (fun n => by
      simp only [nonnegativeRows_d]
      exact t.comm (n : ℤ) (↑n + 1))

lemma descendRowsZero (R : ResolutionData K) (J : ResolutionData L) (r : ℕ)
    (f : (nonnegativeRows R).X 0 ⟶ (nonnegativeRows J).X r)
    (hf : R.augmentation ≫ f = 0) :
    ∃ g : (nonnegativeRows R).X 1 ⟶ (nonnegativeRows J).X r,
      (nonnegativeRows R).d 0 1 ≫ g = f := by
  obtain ⟨g, hg⟩ := descend_zero R J (r : ℤ) (by omega) f hf
  refine ⟨g, ?_⟩
  simp only [nonnegativeRows_d]
  exact hg

lemma descendRowsSucc (R : ResolutionData K) (J : ResolutionData L) (n r : ℕ)
    (f : (nonnegativeRows R).X (n + 1) ⟶ (nonnegativeRows J).X r)
    (hf : (nonnegativeRows R).d n (n + 1) ≫ f = 0) :
    ∃ g : (nonnegativeRows R).X (n + 2) ⟶ (nonnegativeRows J).X r,
      (nonnegativeRows R).d (n + 1) (n + 2) ≫ g = f := by
  have hf' : R.bicomplex.flip.d ((↑n + 1) - 1) (↑n + 1) ≫ f = 0 := by
    rw [add_sub_cancel_right]
    simp only [nonnegativeRows_d] at hf
    exact hf
  change R.bicomplex.flip.X ((n : ℤ) + 1) ⟶ J.bicomplex.flip.X (r : ℤ) at f
  obtain ⟨g, hg⟩ := descend_pos R J ((n : ℤ) + 1) (r : ℤ) (by omega) (by omega) f hf'
  refine ⟨g, ?_⟩
  simp only [nonnegativeRows_d]
  exact hg

/-- Relative comparison homotopy on nonnegative rows. -/
noncomputable def nonnegativeNullHomotopy (R : ResolutionData K) (J : ResolutionData L)
    (e : nonnegativeRows R ⟶ nonnegativeRows J) (he : R.augmentation ≫ e.f 0 = 0) :
    Homotopy e 0 := by
  classical
  let P := nonnegativeRows R
  let Q := nonnegativeRows J
  let s₁ := Classical.choose (descendRowsZero R J 0 (e.f 0) he)
  have hz : P.d 0 1 ≫ s₁ = e.f 0 :=
    Classical.choose_spec (descendRowsZero R J 0 (e.f 0) he)
  have hres : P.d 0 1 ≫ (e.f 1 - s₁ ≫ Q.d 0 1) = 0 := by
    rw [Preadditive.comp_sub, ← e.comm, ← Category.assoc, hz, sub_self]
  let s₂ := Classical.choose (descendRowsSucc R J 0 1 _ hres)
  have hs₂ : P.d 1 2 ≫ s₂ = e.f 1 - s₁ ≫ Q.d 0 1 :=
    Classical.choose_spec (descendRowsSucc R J 0 1 _ hres)
  have h₁ : e.f 1 = s₁ ≫ Q.d 0 1 + P.d 1 2 ≫ s₂ := eq_add_of_sub_eq' hs₂.symm
  refine Homotopy.mkCoinductive e s₁ hz.symm s₂ h₁ ?_
  rintro n ⟨s, s', hs⟩
  have hres' : P.d (n + 1) (n + 2) ≫
      (e.f (n + 2) - s' ≫ Q.d (n + 1) (n + 2)) = 0 := by
    rw [Preadditive.comp_sub, ← e.comm, hs, Preadditive.add_comp,
      Category.assoc, d_comp_d, comp_zero, zero_add, Category.assoc, sub_self]
  let s₃ := Classical.choose (descendRowsSucc R J (n + 1) (n + 2) _ hres')
  have hs₃ : P.d (n + 2) (n + 3) ≫ s₃ =
      e.f (n + 2) - s' ≫ Q.d (n + 1) (n + 2) :=
    Classical.choose_spec (descendRowsSucc R J (n + 1) (n + 2) _ hres')
  exact ⟨s₃, eq_add_of_sub_eq' hs₃.symm⟩

noncomputable def extendHomComponents (R : ResolutionData K) (J : ResolutionData L)
    (h : ∀ n m, (nonnegativeRows R).X n ⟶ (nonnegativeRows J).X m) :
    ∀ q r, R.bicomplex.flip.X q ⟶ J.bicomplex.flip.X r
  | .ofNat n, .ofNat m => h n m
  | .ofNat _, .negSucc _ => 0
  | .negSucc _, _ => 0

/-- Homotopies on nonnegative rows extend across the zero negative rows. -/
noncomputable def extendRowsHomotopy (R : ResolutionData K) (J : ResolutionData L)
    {a b : R.bicomplex.flip ⟶ J.bicomplex.flip}
    (h : Homotopy (restrictRowsMap R J a) (restrictRowsMap R J b)) : Homotopy a b where
  hom := extendHomComponents R J h.hom
  zero q r hqr := by
    cases q with
    | negSucc n => rfl
    | ofNat n =>
      cases r with
      | negSucc m => rfl
      | ofNat m => exact h.zero n m (by simp only [ComplexShape.up_Rel, Int.ofNat_eq_natCast] at *; omega)
  comm q := by
    cases q with
    | negSucc n => exact (negativeRow R _ (by omega)).eq_of_src _ _
    | ofNat n =>
      cases n with
      | zero =>
        have hz : prevD (C := R.bicomplex.flip) (D := J.bicomplex.flip) 0
            (extendHomComponents R J h.hom) = 0 := by
          erw [prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)]
          change (0 : R.bicomplex.flip.X 0 ⟶ J.bicomplex.flip.X (-1)) ≫ _ = 0
          simp
        have hd : dNext (C := R.bicomplex.flip) (D := J.bicomplex.flip) 0
            (extendHomComponents R J h.hom) = R.bicomplex.flip.d 0 1 ≫ h.hom 1 0 := by
          erw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 from rfl)]
          rfl
        erw [hz, hd, add_zero]
        have hc := h.comm 0
        rw [dNext_eq (C := nonnegativeRows R) (D := nonnegativeRows J) _
          (show (ComplexShape.up ℕ).Rel 0 1 from rfl),
          Homotopy.prevD_zero_cochainComplex, add_zero] at hc
        simp only [restrictRowsMap, nonnegativeRows_d] at hc
        exact hc
      | succ n =>
        simp only [Int.ofNat_eq_natCast]
        erw [dNext_eq (C := R.bicomplex.flip) (D := J.bicomplex.flip) _ (show (ComplexShape.up ℤ).Rel (↑(n + 1)) (↑(n + 2)) from rfl),
          prevD_eq (C := R.bicomplex.flip) (D := J.bicomplex.flip) _ (show (ComplexShape.up ℤ).Rel (↑n) (↑(n + 1)) from rfl)]
        have hc := h.comm (n + 1)
        rw [dNext_eq (C := nonnegativeRows R) (D := nonnegativeRows J) _ (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) from rfl),
          prevD_eq (C := nonnegativeRows R) (D := nonnegativeRows J) _ (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)] at hc
        simp only [restrictRowsMap, nonnegativeRows_d] at hc
        exact hc

/-- A lift exists for every map of the augmented source complexes. -/
theorem liftExists : Specs.LiftExists.{v, u} := by
  intro C _ _ K L R J f
  exact ⟨comparison R J f, comparison_augmentation R J f⟩

/-- Any two comparisons of the same map are vertically homotopic through
horizontal chain maps. -/
theorem liftHomotopy : Specs.LiftHomotopy.{v, u} := by
  intro C _ _ K L R J f a b ha hb
  have he : R.augmentation ≫ (restrictRowsMap R J (rowMap a - rowMap b)).f 0 = 0 := by
    change R.augmentation ≫ ((rowMap a).f 0 - (rowMap b).f 0) = 0
    rw [Preadditive.comp_sub, ha, hb, sub_self]
  have h := nonnegativeNullHomotopy R J (restrictRowsMap R J (rowMap a - rowMap b)) he
  have h' : Homotopy (restrictRowsMap R J (rowMap a - rowMap b))
      (restrictRowsMap R J (0 : R.bicomplex.flip ⟶ J.bicomplex.flip)) := h
  exact ⟨Homotopy.equivSubZero.invFun (extendRowsHomotopy R J h')⟩

section TotalHomotopy
variable {I J : DoubleComplex C}
variable [I.HasTotal (ComplexShape.up ℤ)] [J.HasTotal (ComplexShape.up ℤ)]
variable {a b : I ⟶ J}

/-- Sum the signed vertical components on one diagonal. -/
noncomputable def signedHom (s : VerticalHomotopy a b) (n m : ℤ) :
    (DoubleTotalization.sumTotal I).X n ⟶ (DoubleTotalization.sumTotal J).X m :=
  if h : m + 1 = n then
    I.totalDesc (c₁₂ := ComplexShape.up ℤ) (fun p q hpq =>
      p.negOnePow • ((s.hom q (q - 1)).f p ≫
        J.ιTotal (ComplexShape.up ℤ) p (q - 1) m
          (by change p + (q - 1) = m; change p + q = n at hpq; omega)))
  else 0

@[reassoc] lemma ι_signedHom (s : VerticalHomotopy a b) (p q n m : ℤ)
    (e : p + q = n) (h : m + 1 = n) :
    I.ιTotal (ComplexShape.up ℤ) p q n e ≫ signedHom s n m =
      p.negOnePow • ((s.hom q (q - 1)).f p ≫
        J.ιTotal (ComplexShape.up ℤ) p (q - 1) m (by change p + (q - 1) = m; omega)) := by
  simp only [signedHom, dite_eq_left h, HomologicalComplex₂.ι_totalDesc]

omit [I.HasTotal (ComplexShape.up ℤ)] in
lemma vertical_component_congr (s : VerticalHomotopy a b)
    (p q r r' n : ℤ) (h : p + r = n) (h' : p + r' = n) (e : r = r') :
    (s.hom q r).f p ≫ J.ιTotal (ComplexShape.up ℤ) p r n h =
      (s.hom q r').f p ≫ J.ιTotal (ComplexShape.up ℤ) p r' n h' := by
  subst r'
  rfl

lemma signedHom_comm (s : VerticalHomotopy a b) (n : ℤ) :
    (totalMap a).f n =
      (DoubleTotalization.sumTotal I).d n (n + 1) ≫ signedHom s (n + 1) n +
      signedHom s n (n - 1) ≫ (DoubleTotalization.sumTotal J).d (n - 1) n +
      (totalMap b).f n := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  dsimp only [totalMap]
  rw [Preadditive.comp_add, Preadditive.comp_add]
  simp only [HomologicalComplex₂.ιTotal_map]
  rw [← Category.assoc, DoubleTotalization.sumDifferential I p (p + 1) q (q + 1)
    n (n + 1) rfl rfl hpq (by change p + q = n at hpq; omega)
      (by change p + q = n at hpq; omega)]
  simp only [Preadditive.add_comp, Category.assoc, Linear.units_smul_comp,
    ι_signedHom, Linear.comp_units_smul]
  erw [ι_signedHom_assoc s p q n (n - 1) hpq (by omega)]
  simp only [Linear.units_smul_comp, Category.assoc]
  erw [DoubleTotalization.sumDifferential J p (p + 1) (q - 1) q
    (n - 1) n rfl (by change q - 1 + 1 = q; omega)
    (by change p + q = n at hpq; omega)
    (by change p + q = n at hpq; omega) hpq]
  simp only [DoubleTotalization.sumInjection,
    show (ComplexShape.up ℤ).ε p = p.negOnePow from rfl,
    Int.negOnePow_succ, Units.neg_smul, Preadditive.comp_add, smul_add,
    Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul]
  erw [(s.hom q (q - 1)).comm_assoc p (p + 1)]
  have hs := s.comm q
  rw [dNext_eq (C := I.flip) (D := J.flip) _ (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl),
    prevD_eq (C := I.flip) (D := J.flip) _ (show (ComplexShape.up ℤ).Rel (q - 1) q by simp)] at hs
  have hs' := congrArg (fun f => f.f p ≫ J.ιTotal (ComplexShape.up ℤ) p q n hpq) hs
  simp only [rowMap, HomologicalComplex₂.flipFunctor_map_f_f,
    comp_f, add_f_apply, Preadditive.add_comp, Category.assoc] at hs'
  dsimp only [HomologicalComplex₂.flip_d_f, HomologicalComplex₂.flip_X_d] at hs'
  rw [hs']
  erw [vertical_component_congr s p (q + 1) (q + 1 - 1) q n _ hpq (by omega)]
  dsimp only [HomologicalComplex₂.flip_X_d]
  abel

/-- The sign on a vertical homotopy is the horizontal parity. -/
noncomputable def totalHomotopy (s : VerticalHomotopy a b) :
    Homotopy (totalMap a) (totalMap b) where
  hom := signedHom s
  zero n m h := by
    exact dite_eq_right h
  comm n := by
    rw [dNext_eq (C := DoubleTotalization.sumTotal I) (D := DoubleTotalization.sumTotal J)
        _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl),
      prevD_eq (C := DoubleTotalization.sumTotal I) (D := DoubleTotalization.sumTotal J)
        _ (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)]
    exact signedHom_comm s n

end TotalHomotopy

/-- Every vertical homotopy induces the stated signed total homotopy. -/
theorem signedTotalHomotopy : Specs.SignedTotalHomotopy.{v, u} := by
  intro C _ _ I J _ _ a b s
  refine ⟨totalHomotopy s, ?_⟩
  intro p q n e
  exact ι_signedHom s p q n (n - 1) e (by omega)

/-- The induced morphism of total complexes is independent in the homotopy
category of all choices of comparison lift. -/
theorem comparisonIndependence : Specs.ComparisonIndependence.{v, u} := by
  intro C _ _ K L R J _ _ f a b ha hb
  obtain ⟨s⟩ := liftHomotopy R J f a b ha hb
  exact HomotopyCategory.eq_of_homotopy _ _ (totalHomotopy s)

lemma isLift_comp {M : CochainComplex C ℤ}
    (R : ResolutionData K) (J : ResolutionData L) (T : ResolutionData M)
    {f : K ⟶ L} {g : L ⟶ M} {a : R.bicomplex ⟶ J.bicomplex}
    {b : J.bicomplex ⟶ T.bicomplex} (ha : IsLift R J f a) (hb : IsLift J T g b) :
    IsLift R T (f ≫ g) (a ≫ b) := by
  change R.augmentation ≫ ((rowMap a).f 0 ≫ (rowMap b).f 0) =
    (f ≫ g) ≫ T.augmentation
  rw [← Category.assoc, ha, Category.assoc, hb, ← Category.assoc]

lemma isLift_id (R : ResolutionData K) : IsLift R R (𝟙 K) (𝟙 R.bicomplex) := by
  change R.augmentation ≫ 𝟙 _ = (𝟙 K) ≫ R.augmentation
  simp

/-- Compatibility with the total augmentations, on every degree component. -/
theorem totalAugmentationCompatibility : Specs.TotalAugmentationCompatibility.{v, u} := by
  intro C _ _ K L R J _ _ f a ha p
  dsimp only [totalMap]
  erw [HomologicalComplex₂.ιTotal_map]
  have h := congrArg (fun z => z.f p ≫
    J.bicomplex.ιTotal (ComplexShape.up ℤ) p 0 p (by simp)) ha
  simpa only [comp_f, rowMap, HomologicalComplex₂.flipFunctor_map_f_f,
    Category.assoc] using h

/-- Inverse comparisons already exist before totalization. -/
theorem verticalInverseComparisons : Specs.VerticalInverseComparisons.{v, u} := by
  intro C _ _ K R J
  obtain ⟨a, ha⟩ := liftExists R J (𝟙 K)
  obtain ⟨b, hb⟩ := liftExists J R (𝟙 K)
  have hab : IsLift R R (𝟙 K) (a ≫ b) := by
    simpa using isLift_comp R J R ha hb
  have hba : IsLift J J (𝟙 K) (b ≫ a) := by
    simpa using isLift_comp J R J hb ha
  exact ⟨a, b, ha, hb, liftHomotopy R R (𝟙 K) (a ≫ b) (𝟙 _) hab (isLift_id R),
    liftHomotopy J J (𝟙 K) (b ≫ a) (𝟙 _) hba (isLift_id J)⟩

/-- Comparisons of two resolutions of the same complex are inverse up to
vertical homotopy, and induce inverse homotopy equivalences of totals. -/
theorem inverseComparisons : Specs.InverseComparisons.{v, u} := by
  intro C _ _ K R J _ _
  obtain ⟨a, b, ha, hb, ⟨sab⟩, ⟨sba⟩⟩ := verticalInverseComparisons R J
  refine ⟨a, b, ha, hb, ⟨sab⟩, ⟨sba⟩, ?_⟩
  let e : HomotopyEquiv (DoubleTotalization.sumTotal R.bicomplex)
      (DoubleTotalization.sumTotal J.bicomplex) :=
    { hom := totalMap a
      inv := totalMap b
      homotopyHomInvId := by
        simpa only [totalMap, HomologicalComplex₂.total.map_comp,
          HomologicalComplex₂.total.map_id] using totalHomotopy sab
      homotopyInvHomId := by
        simpa only [totalMap, HomologicalComplex₂.total.map_comp,
          HomologicalComplex₂.total.map_id] using totalHomotopy sba }
  exact ⟨e, rfl, rfl⟩

end AdvancedHomologicalAlgebra.CartanEilenbergComparison
