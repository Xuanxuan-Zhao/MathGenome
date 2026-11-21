import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DoubleComplexConvergence
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison
import Mathlib.Algebra.Homology.Embedding.Restriction

noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped Classical
universe v u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison
open DoubleTotalization FiniteDiagonalFiltrations
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A horizontal complex regarded as a double complex on the zero row. -/
def axisComplex {c : ComplexShape ℤ} (L : HomologicalComplex A c) :
    HomologicalComplex₂ A c c :=
  ((HomologicalComplex.single A c 0).mapHomologicalComplex c).obj L

/-- An augmentation killed by the vertical differential is a bicomplex map. -/
def columnLift (K : Bicomplex A) (L : CochainComplex A ℤ)
    (a : L ⟶ K.flip.X 0)
    (z : ∀ p q, (ComplexShape.up ℤ).Rel 0 q → a.f p ≫ (K.X p).d 0 q = 0) :
    axisComplex L ⟶ K where
  f p := HomologicalComplex.mkHomFromSingle (K := K.X p) (a.f p) (z p)
  comm' p p' _ := by
    apply HomologicalComplex.from_single_hom_ext
    simp only [HomologicalComplex.comp_f, HomologicalComplex.mkHomFromSingle_f]
    rw [Category.assoc]
    change (HomologicalComplex.singleObjXSelf _ _ _).hom ≫ a.f p ≫ (K.d p p').f 0 =
      ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).map (L.d p p')).f 0 ≫
        (HomologicalComplex.singleObjXSelf _ _ _).hom ≫ a.f p'
    rw [HomologicalComplex.single_map_f_self]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact congrArg (fun t => (HomologicalComplex.singleObjXSelf _ _ _).hom ≫ t)
      (a.comm p p')

/-- Axis support is finite on each diagonal, even for an unbounded L. -/
theorem axis_support_finite {c : ComplexShape ℤ} (L : HomologicalComplex A c) (n : ℤ) :
    {i : Diagonal n | ¬ IsZero (((axisComplex L).X i.val.1).X i.val.2)}.Finite := by
  apply (Set.finite_singleton (⟨(n,0),add_zero n⟩ : Diagonal n)).subset
  intro i hi
  have hq : i.val.2 = 0 := by
    by_contra hq
    exact hi (HomologicalComplex.isZero_single_obj_X _ 0 _ _ hq)
  simp only [Set.mem_singleton_iff]
  apply Subtype.ext
  change i.val = (n,0)
  exact Prod.ext (by have := i.property; omega) hq

theorem axis_finite (L : CochainComplex A ℤ) : FiniteDiagonals (axisComplex L) :=
  axis_support_finite L

attribute [local instance] Abelian.hasFiniteBiproducts
instance axis_hasTotal {c : ComplexShape ℤ} [ComplexShape.TensorSigns c]
    (L : HomologicalComplex A c) : (axisComplex L).HasTotal c := by
  intro n
  have : HasBiproduct (fun i : Diagonal n => ((axisComplex L).X i.val.1).X i.val.2) :=
    hasBiproduct_of_finite_nonzero _ (axis_support_finite L n)
  change HasCoproduct (fun i : Diagonal n => ((axisComplex L).X i.val.1).X i.val.2)
  exact inferInstance

/-- The inclusion of the only possibly nonzero diagonal summand, for both shapes. -/
def axisInclusion {c : ComplexShape ℤ} [ComplexShape.TensorSigns c]
    (L : HomologicalComplex A c) : L ⟶ sumTotal (axisComplex L) where
  f n := (HomologicalComplex.singleObjXSelf c 0 (L.X n)).inv ≫
    sumInjection (axisComplex L) n 0 n (add_zero n)
  comm' n m h := by
    rw [Category.assoc]
    change (HomologicalComplex.singleObjXSelf c 0 (L.X n)).inv ≫
      (sumInjection (axisComplex L) n 0 n (add_zero n) ≫
        ((axisComplex L).D₁ c n m + (axisComplex L).D₂ c n m)) = _
    rw [Preadditive.comp_add, HomologicalComplex₂.ι_D₁,
      HomologicalComplex₂.ι_D₂, HomologicalComplex₂.d₁_eq _ c h 0 m (add_zero m)]
    have hz : (axisComplex L).d₂ c n 0 m = 0 := by
      simp only [HomologicalComplex₂.d₂, axisComplex,
        Functor.mapHomologicalComplex_obj_X, HomologicalComplex.single_obj_d,
        zero_comp, smul_zero]
    rw [hz, add_zero]
    have he : c.ε₁ c c (n,0) = 1 := rfl
    rw [he, one_smul]
    change (HomologicalComplex.singleObjXSelf c 0 (L.X n)).inv ≫
      ((HomologicalComplex.single A c 0).map (L.d n m)).f 0 ≫
        sumInjection (axisComplex L) m 0 m (add_zero m) = _
    rw [HomologicalComplex.single_map_f_self]
    simp only [Iso.inv_hom_id_assoc, Category.assoc]

/-- The total of an axis complex is the original complex. -/
instance axisInclusion_isIso {c : ComplexShape ℤ} [ComplexShape.TensorSigns c]
    (L : HomologicalComplex A c) : IsIso (axisInclusion L) := by
  have hc : ∀ n, IsIso ((axisInclusion L).f n) := by
    intro n
    let K := axisComplex L
    let r : (sumTotal K).X n ⟶ L.X n := K.totalDesc (fun p q h =>
      if hq : q = 0 then
        (HomologicalComplex.singleObjXIsoOfEq c 0 (L.X p) q hq).hom ≫
          (L.XIsoOfEq (by change p+q=n at h; omega : p = n)).hom
      else 0)
    have hr : (axisInclusion L).f n ≫ r = 𝟙 _ := by
      dsimp only [axisInclusion]
      rw [Category.assoc, HomologicalComplex₂.ι_totalDesc]
      simp only [dite_true, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, comp_id]
      exact Iso.inv_hom_id _
    have hr' : r ≫ (axisInclusion L).f n = 𝟙 _ := by
      apply HomologicalComplex₂.total.hom_ext
      intro p q h
      by_cases hq : q = 0
      · subst q
        have hp : p = n := by change p+0=n at h; omega
        subst p
        dsimp only [r, axisInclusion]
        rw [HomologicalComplex₂.ι_totalDesc_assoc]
        simp only [dite_true, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, comp_id]
        change (HomologicalComplex.singleObjXSelf c 0 (L.X n)).hom ≫
          (HomologicalComplex.singleObjXSelf c 0 (L.X n)).inv ≫ _ = _
        rw [Iso.hom_inv_id_assoc]
      · exact (HomologicalComplex.isZero_single_obj_X _ 0 (L.X p) q hq).eq_of_src _ _
    exact ⟨⟨r,hr,hr'⟩⟩
  have := hc
  exact HomologicalComplex.Hom.isIso_of_components _

theorem cochain_column_assembly : Specs.CochainColumn.{v,u} := by
  intro A _ _ K hK hneg _ L a z hzero hother
  let b := columnLift K L a z
  have hb : ∀ p, QuasiIso (b.f p) := by
    intro p
    rw [quasiIso_iff]
    intro q
    apply (quasiIsoAt_iff_isIso_homologyMap _ q).2
    by_cases hq : q = 0
    · subst q
      exact hzero p
    · exact (HomologicalComplex.isZero_single_obj_homology _ 0 (L.X p) q hq).isIso
        (hother p q hq) _
  have ht := DoubleComplexConvergence.double_complex_comparison
    (axisComplex L) K (axis_finite L) hK b (Or.inl hb)
  let f := axisInclusion L ≫ HomologicalComplex₂.total.map b (ComplexShape.up ℤ)
  refine ⟨f, ?_, ?_⟩
  · have := ht
    dsimp only [f]
    infer_instance
  · intro n
    dsimp only [f, HomologicalComplex.comp_f, axisInclusion]
    rw [Category.assoc, HomologicalComplex₂.ιTotal_map]
    change (HomologicalComplex.singleObjXSelf _ _ _).inv ≫
      (HomologicalComplex.mkHomFromSingle (K := K.X n) (a.f n) (z n)).f 0 ≫ _ = _
    rw [HomologicalComplex.mkHomFromSingle_f]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Axis interchange has multiplier one on the augmented axis. -/
theorem cochain_row_assembly : Specs.CochainRow.{v,u} := by
  intro A _ _ K hK hneg _ L a z hzero hother
  obtain ⟨f,hf,hform⟩ := cochain_column_assembly K.flip
    (DoubleComplexFirstPages.finiteDiagonals_flip K hK)
    (fun p q hq => hneg q p hq) L a z hzero hother
  let g := f ≫ (K.totalFlipIso (ComplexShape.up ℤ)).hom
  refine ⟨g, ?_, ?_⟩
  · have := hf
    dsimp only [g]
    infer_instance
  · intro n
    dsimp only [g, HomologicalComplex.comp_f]
    rw [hform, Category.assoc, HomologicalComplex₂.ιTotal_totalFlipIso_f_hom]
    change a.f n ≫ ((0 * n).negOnePow • sumInjection K 0 n n (zero_add n)) = _
    simp only [zero_mul, Int.negOnePow_zero, one_smul]

/-- Negating integer indices converts a chain complex to a cochain complex. -/
def negEmbedding : (ComplexShape.up ℤ).Embedding (ComplexShape.down ℤ) :=
  ComplexShape.Embedding.mk' _ _ (fun n => -n) neg_injective (by
    intro i j
    simp only [ComplexShape.up_Rel, ComplexShape.down_Rel]
    omega)

instance : negEmbedding.IsRelIff := inferInstanceAs
  ((ComplexShape.Embedding.mk' (ComplexShape.up ℤ) (ComplexShape.down ℤ)
    (fun n => -n) neg_injective _).IsRelIff)

@[simp] theorem negEmbedding_f (n : ℤ) : negEmbedding.f n = -n := rfl

abbrev cochainOfChain (L : ChainComplex A ℤ) : CochainComplex A ℤ :=
  L.restriction negEmbedding

/-- Reindexing carries the actual three-term homology complex to the old one. -/
def negScNatIso (n : ℤ) :
    negEmbedding.restrictionFunctor A ⋙
      HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) n ≅
    HomologicalComplex.shortComplexFunctor A (ComplexShape.down ℤ) (-n) :=
  NatIso.ofComponents (fun L => ShortComplex.isoMk
    (L.XIsoOfEq (by simp only [negEmbedding_f, CochainComplex.prev, ChainComplex.prev]; omega))
    (Iso.refl _)
    (L.XIsoOfEq (by simp only [negEmbedding_f, CochainComplex.next, ChainComplex.next]; omega))
    (by simp) (by simp)) (by
      intro L M f
      ext <;> simp [HomologicalComplex.XIsoOfEq_hom_naturality])

theorem quasiIsoAt_regrade_iff {L M : ChainComplex A ℤ} (f : L ⟶ M) (n : ℤ) :
    QuasiIsoAt (HomologicalComplex.restrictionMap f negEmbedding) n ↔
      QuasiIsoAt f (-n) := by
  rw [quasiIsoAt_iff, quasiIsoAt_iff]
  exact ShortComplex.quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoOfNatIso (negScNatIso n) (Arrow.mk f))

theorem quasiIso_regrade_iff {L M : ChainComplex A ℤ} (f : L ⟶ M) :
    QuasiIso (HomologicalComplex.restrictionMap f negEmbedding) ↔ QuasiIso f := by
  simp only [quasiIso_iff, quasiIsoAt_regrade_iff]
  constructor
  · intro h n
    simpa only [neg_neg] using h (-n)
  · intro h n
    exact h (-n)

/-- Reindex both directions, retaining the unsigned commuting differentials. -/
def cochainBicomplex (K : HomologicalComplex₂ A (ComplexShape.down ℤ) (ComplexShape.down ℤ)) :
    Bicomplex A :=
  ((negEmbedding.restrictionFunctor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (K.restriction negEmbedding)

def cochainBicomplexMap
    {K J : HomologicalComplex₂ A (ComplexShape.down ℤ) (ComplexShape.down ℤ)} (f : K ⟶ J) :
    cochainBicomplex K ⟶ cochainBicomplex J :=
  ((negEmbedding.restrictionFunctor A).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (HomologicalComplex.restrictionMap f negEmbedding)

section RegradeTotal
variable (K : HomologicalComplex₂ A (ComplexShape.down ℤ) (ComplexShape.down ℤ))
variable [K.HasTotal (ComplexShape.down ℤ)]
variable [(cochainBicomplex K).HasTotal (ComplexShape.up ℤ)]

/-- The totalization reindexing map has coefficient one on every summand. -/
def regradeTotalComponent (n : ℤ) :
    (sumTotal (cochainBicomplex K)).X n ⟶ (sumTotal K).X (-n) :=
  (cochainBicomplex K).totalDesc (fun p q h =>
    sumInjection K (-p) (-q) (-n) (by change p+q=n at h; omega))

@[reassoc (attr := simp)]
theorem injection_regradeTotalComponent (p q n : ℤ) (h : p+q=n) :
    sumInjection (cochainBicomplex K) p q n h ≫ regradeTotalComponent K n =
      sumInjection K (-p) (-q) (-n) (by omega) := by
  apply HomologicalComplex₂.ι_totalDesc

/-- Regrading commutes with totalization, including the parity sign. -/
def regradeTotalMap : sumTotal (cochainBicomplex K) ⟶ cochainOfChain (sumTotal K) where
  f := regradeTotalComponent K
  comm' n m hnm := by
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    have hn : n + 1 = m := hnm
    have hpq' : p+q=n := hpq
    change sumInjection (cochainBicomplex K) p q n hpq ≫
        (regradeTotalComponent K n ≫ (sumTotal K).d (-n) (-m)) =
      sumInjection (cochainBicomplex K) p q n hpq ≫
        ((sumTotal (cochainBicomplex K)).d n m ≫ regradeTotalComponent K m)
    rw [injection_regradeTotalComponent_assoc]
    rw [← Category.assoc, sumDifferential _ (-p) (-(p+1)) (-q) (-(q+1)) (-n) (-m)
      (by change -(p+1)+1 = -p; omega) (by change -(q+1)+1 = -q; omega)
      (by omega) (by omega) (by omega)]
    rw [sumDifferential _ p (p+1) q (q+1) n m
      (by simp) (by simp) hpq' (by omega) (by omega)]
    simp only [Preadditive.add_comp, Category.assoc, Linear.units_smul_comp,
      injection_regradeTotalComponent]
    change _ + (-p).negOnePow • _ = _ + p.negOnePow • _
    rw [Int.negOnePow_neg]
    rfl

instance regradeTotalMap_isIso : IsIso (regradeTotalMap K) := by
  have hc : ∀ n, IsIso ((regradeTotalMap K).f n) := by
    intro n
    let r : (sumTotal K).X (-n) ⟶ (sumTotal (cochainBicomplex K)).X n :=
      K.totalDesc (fun p q h =>
        (K.XXIsoOfEq _ _ _ (by simp : p = -(-p)) (by simp : q = -(-q))).hom ≫
          sumInjection (cochainBicomplex K) (-p) (-q) n
            (by change p+q = -n at h; omega))
    have h₁ : (regradeTotalMap K).f n ≫ r = 𝟙 _ := by
      apply HomologicalComplex₂.total.hom_ext
      intro p q h
      change sumInjection (cochainBicomplex K) p q n h ≫
        (regradeTotalComponent K n ≫ r) = _
      rw [injection_regradeTotalComponent_assoc]
      dsimp only [r]
      rw [HomologicalComplex₂.ι_totalDesc]
      change ((cochainBicomplex K).XXIsoOfEq _ _ _
        (by simp : p = -(-p)) (by simp : q = -(-q))).hom ≫
          sumInjection (cochainBicomplex K) (-(-p)) (-(-q)) n _ = _
      rw [HomologicalComplex₂.XXIsoOfEq_hom_ιTotal]
      simp only [comp_id]
    have h₂ : r ≫ (regradeTotalMap K).f n = 𝟙 _ := by
      apply HomologicalComplex₂.total.hom_ext
      intro p q h
      dsimp only [r, regradeTotalMap]
      rw [HomologicalComplex₂.ι_totalDesc_assoc, Category.assoc,
        injection_regradeTotalComponent]
      exact (K.XXIsoOfEq_hom_ιTotal (ComplexShape.down ℤ) (by simp : p = -(-p))
        (by simp : q = -(-q)) (-n) (by change p+q = -n at h; simpa using h)).trans
          (by simp)
    exact ⟨⟨r,h₁,h₂⟩⟩
  have := hc
  exact HomologicalComplex.Hom.isIso_of_components _

end RegradeTotal

/-- Compatibility of regrading with the total map, on the actual summands. -/
theorem regradeTotalMap_naturality
    (K J : HomologicalComplex₂ A (ComplexShape.down ℤ) (ComplexShape.down ℤ))
    [K.HasTotal (ComplexShape.down ℤ)] [J.HasTotal (ComplexShape.down ℤ)]
    [(cochainBicomplex K).HasTotal (ComplexShape.up ℤ)]
    [(cochainBicomplex J).HasTotal (ComplexShape.up ℤ)] (f : K ⟶ J) :
    regradeTotalMap K ≫ HomologicalComplex.restrictionMap
      (HomologicalComplex₂.total.map f (ComplexShape.down ℤ)) negEmbedding =
    HomologicalComplex₂.total.map (cochainBicomplexMap f) (ComplexShape.up ℤ) ≫
      regradeTotalMap J := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, regradeTotalMap,
    injection_regradeTotalComponent_assoc, HomologicalComplex.restrictionMap_f,
    negEmbedding_f, HomologicalComplex₂.ιTotal_map_assoc,
    injection_regradeTotalComponent]
  simp only [sumInjection, HomologicalComplex₂.ιTotal_map]
  rfl

/-- The established cochain comparison transports to downward integer indices. -/
theorem chain_total_comparison
    (K J : HomologicalComplex₂ A (ComplexShape.down ℤ) (ComplexShape.down ℤ))
    (hK : FiniteDiagonals (cochainBicomplex K))
    (hJ : FiniteDiagonals (cochainBicomplex J))
    [K.HasTotal (ComplexShape.down ℤ)] [J.HasTotal (ComplexShape.down ℤ)]
    (f : K ⟶ J) (hf : ∀ p, QuasiIso (f.f p)) :
    QuasiIso (HomologicalComplex₂.total.map f (ComplexShape.down ℤ)) := by
  have := (FiniteDiagonalFiltrations.totalizationsExist _ hK).1
  have := (FiniteDiagonalFiltrations.totalizationsExist _ hJ).1
  have hc : ∀ p, QuasiIso ((cochainBicomplexMap f).f p) := by
    intro p
    change QuasiIso (HomologicalComplex.restrictionMap (f.f (-p)) negEmbedding)
    exact (quasiIso_regrade_iff _).2 (hf (-p))
  have ht := DoubleComplexConvergence.double_complex_comparison
    (cochainBicomplex K) (cochainBicomplex J) hK hJ (cochainBicomplexMap f) (Or.inl hc)
  have ht' : QuasiIso (regradeTotalMap K ≫ HomologicalComplex.restrictionMap
      (HomologicalComplex₂.total.map f (ComplexShape.down ℤ)) negEmbedding) := by
    rw [regradeTotalMap_naturality]
    have := ht
    infer_instance
  exact (quasiIso_regrade_iff _).1 ((quasiIso_iff_comp_left _ _).1 ht')

/-- A first-quadrant chain bicomplex has finite diagonals after regrading. -/
theorem chain_quadrant_finite
    (K : HomologicalComplex₂ A (ComplexShape.down ℤ) (ComplexShape.down ℤ))
    (hK : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((K.X p).X q)) :
    FiniteDiagonals (cochainBicomplex K) := by
  intro n
  let s : Set (Diagonal n) := {i | ¬ IsZero (diagonalFamily (cochainBicomplex K) n i)}
  have hp : ∀ i ∈ s, n ≤ i.val.1 ∧ i.val.1 ≤ 0 := by
    intro i hi
    have hb : i.val.1 ≤ 0 ∧ i.val.2 ≤ 0 := by
      by_contra hb
      apply hi
      exact hK (-i.val.1) (-i.val.2) (by omega)
    have he := i.property
    exact ⟨by omega, hb.1⟩
  have ht : Set.Finite ((fun i : Diagonal n => i.val.1) '' s) :=
    (Set.finite_Icc n 0).subset (by
      rintro _ ⟨i,hi,rfl⟩
      exact hp i hi)
  apply Set.Finite.of_finite_image ht
  intro i hi j hj hij
  apply Subtype.ext
  apply Prod.ext hij
  have hi' := i.property
  have hj' := j.property
  dsimp at hij
  omega

/-- A first-quadrant chain bicomplex has a direct-sum totalization. -/
theorem chain_quadrant_hasTotal
    (K : HomologicalComplex₂ A (ComplexShape.down ℤ) (ComplexShape.down ℤ))
    (hK : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((K.X p).X q)) :
    K.HasTotal (ComplexShape.down ℤ) := by
  intro n
  let e : Diagonal n ≃ Diagonal (-n) :=
    { toFun := fun i => ⟨(-i.val.1, -i.val.2), by have := i.property; omega⟩
      invFun := fun i => ⟨(-i.val.1, -i.val.2), by have := i.property; omega⟩
      left_inv := fun i => Subtype.ext (Prod.ext (neg_neg _) (neg_neg _))
      right_inv := fun i => Subtype.ext (Prod.ext (neg_neg _) (neg_neg _)) }
  have : HasCoproduct (diagonalFamily (cochainBicomplex K) (-n)) :=
    (totalizationsExist _ (chain_quadrant_finite K hK)).1 (-n)
  change HasCoproduct (fun i : Diagonal n => (K.X i.val.1).X i.val.2)
  exact hasCoproduct_of_equiv_of_iso (diagonalFamily (cochainBicomplex K) (-n)) _
    e (fun i => K.XXIsoOfEq _ _ _ (neg_neg i.val.1).symm (neg_neg i.val.2).symm)

/-- The zero-row chain complex still has one possibly nonzero summand per diagonal. -/
theorem regraded_axis_finite (L : ChainComplex A ℤ) :
    FiniteDiagonals (cochainBicomplex (axisComplex L)) := by
  intro n
  apply (Set.finite_singleton (⟨(n,0),add_zero n⟩ : Diagonal n)).subset
  intro i hi
  have hq : i.val.2 = 0 := by
    by_contra hq
    exact hi (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℤ) 0 (L.X (-i.val.1)) (-i.val.2) (by omega))
  simp only [Set.mem_singleton_iff]
  apply Subtype.ext
  change i.val = (n,0)
  exact Prod.ext (by have := i.property; omega) hq

/-- Incoming vertical boundaries are killed by a chain augmentation. -/
def chainColumnMap
    (K : HomologicalComplex₂ A (ComplexShape.down ℤ) (ComplexShape.down ℤ))
    (L : ChainComplex A ℤ) (a : K.flip.X 0 ⟶ L)
    (z : ∀ p q, (ComplexShape.down ℤ).Rel q 0 → (K.X p).d q 0 ≫ a.f p = 0) :
    K ⟶ axisComplex L where
  f p := HomologicalComplex.mkHomToSingle (K := K.X p) (a.f p) (z p)
  comm' p p' _ := by
    apply HomologicalComplex.to_single_hom_ext
    simp only [HomologicalComplex.comp_f, HomologicalComplex.mkHomToSingle_f]
    change (a.f p ≫ (HomologicalComplex.singleObjXSelf _ _ _).inv) ≫
      ((HomologicalComplex.single A (ComplexShape.down ℤ) 0).map (L.d p p')).f 0 = _
    rw [HomologicalComplex.single_map_f_self]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, a.comm]
    simp only [Category.assoc]
    rfl

theorem chain_column_assembly : Specs.ChainColumn.{v,u} := by
  intro A _ _ K hK _ L a z hzero hpositive
  let b := chainColumnMap K L a z
  have hb : ∀ p, QuasiIso (b.f p) := by
    intro p
    rw [quasiIso_iff]
    intro q
    apply (quasiIsoAt_iff_isIso_homologyMap _ q).2
    by_cases hq : q = 0
    · subst q
      exact hzero p
    · have hz : IsZero ((K.X p).homology q) := by
        rcases lt_or_gt_of_ne hq with hq | hq
        · exact (HomologicalComplex.ExactAt.of_isZero (hK p q (Or.inr hq))).isZero_homology
        · exact hpositive p q hq
      exact hz.isIso (HomologicalComplex.isZero_single_obj_homology _ 0 (L.X p) q hq) _
  have ht := chain_total_comparison K (axisComplex L) (chain_quadrant_finite K hK)
    (regraded_axis_finite L) b hb
  let f := HomologicalComplex₂.total.map b (ComplexShape.down ℤ) ≫ inv (axisInclusion L)
  refine ⟨f, ?_, ?_⟩
  · have := ht
    dsimp only [f]
    infer_instance
  · intro p q n h
    change sumInjection K p q n h ≫
      ((HomologicalComplex₂.total.map b (ComplexShape.down ℤ)).f n ≫
        (inv (axisInclusion L)).f n) = _
    rw [HomologicalComplex₂.ιTotal_map_assoc]
    by_cases hq : q = 0
    · subst q
      have hp : p = n := by omega
      subst p
      simp only [dite_true, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, id_comp, comp_id]
      change (HomologicalComplex.mkHomToSingle (K := K.X n) (a.f n) (z n)).f 0 ≫
        sumInjection (axisComplex L) n 0 n (add_zero n) ≫ (inv (axisInclusion L)).f n = _
      have hinv : (HomologicalComplex.singleObjXSelf (ComplexShape.down ℤ) 0 (L.X n)).inv ≫
          sumInjection (axisComplex L) n 0 n (add_zero n) ≫
            (inv (axisInclusion L)).f n = 𝟙 _ := by
        rw [← Category.assoc]
        change (axisInclusion L).f n ≫ (inv (axisInclusion L)).f n = _
        rw [← HomologicalComplex.comp_f, IsIso.hom_inv_id, HomologicalComplex.id_f]
      rw [HomologicalComplex.mkHomToSingle_f]
      simp only [Category.assoc, hinv, comp_id]
    · rw [dite_eq_right hq]
      have hz : (axisComplex L).ιTotal (ComplexShape.down ℤ) p q n h = 0 :=
        (HomologicalComplex.isZero_single_obj_X _ 0 (L.X p) q hq).eq_of_src _ _
      rw [hz, zero_comp, comp_zero]

/-- The horizontal chain augmentation has the same outgoing direction. -/
theorem chain_row_assembly : Specs.ChainRow.{v,u} := by
  intro A _ _ K hK _ L a z hzero hpositive
  obtain ⟨f,hf,hform⟩ := chain_column_assembly K.flip
    (fun p q h => hK q p (by tauto)) L a z hzero hpositive
  let g := (K.totalFlipIso (ComplexShape.down ℤ)).inv ≫ f
  refine ⟨g, ?_, ?_⟩
  · have := hf
    dsimp only [g]
    infer_instance
  · intro p q n h
    change sumInjection K p q n h ≫
      ((K.totalFlipIso (ComplexShape.down ℤ)).inv.f n ≫ f.f n) = _
    rw [← Category.assoc, HomologicalComplex₂.ιTotal_totalFlipIso_f_inv,
      Linear.units_smul_comp, hform]
    by_cases hp : p = 0
    · subst p
      simp only [dite_true]
      change (0 * q).negOnePow •
        ((HomologicalComplex.XIsoOfEq (K.flip.X q) rfl).hom ≫ a.f q ≫
          (L.XIsoOfEq (by omega : q = n)).hom) = _
      simp only [zero_mul, Int.negOnePow_zero, one_smul]
    · simp only [dite_eq_right hp, smul_zero]

end AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison
