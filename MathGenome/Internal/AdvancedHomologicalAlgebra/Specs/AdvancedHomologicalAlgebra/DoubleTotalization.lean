import Mathlib.Algebra.Homology.TotalComplexSymmetry
import Mathlib.Algebra.Homology.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-! HA-B01, notes/002/advanced-homological-algebra.tex, Totalization and
interchange of the axes. Canonical input objects and independent contracts.
`HomologicalComplex₂` is the commuting convention, with no boundedness condition.
Only the coproducts/products of each individual diagonal are required. -/

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category Opposite

namespace AdvancedHomologicalAlgebra.DoubleTotalization

/-- Reverse a shape's arrows, retaining its parity character. -/
instance tensorSignsSymm {I : Type*} [AddMonoid I] (c : ComplexShape I)
    [ComplexShape.TensorSigns c] : ComplexShape.TensorSigns c.symm where
  ε' := ComplexShape.TensorSigns.ε' c
  rel_add p q r h := ComplexShape.rel_add c h r
  add_rel p q r h := ComplexShape.add_rel c r h
  ε'_succ p q h := by
    have h' := ComplexShape.ε_succ c h
    exact neg_eq_iff_eq_neg.mp h'.symm

@[simp] theorem epsilon_symm {I : Type*} [AddMonoid I] (c : ComplexShape I)
    [ComplexShape.TensorSigns c] (p : I) : c.symm.ε p = c.ε p := rfl

/-- Simultaneously take opposites in both differential directions. -/
def oppositeBicomplex {C I : Type*} [Category* C] [Preadditive C]
    {c : ComplexShape I} (K : HomologicalComplex₂ C c c) :
    HomologicalComplex₂ Cᵒᵖ c.symm c.symm where
  X p := (K.X p).op
  d p p' :=
    { f := fun q => ((K.d p' p).f q).op
      comm' q q' _ := by
        apply Quiver.Hom.unop_inj
        exact (K.d_comm p' p q' q).symm }
  shape p p' h := by
    ext q
    simp [K.shape_f p' p h q]
  d_comp_d' p p' p'' _ _ := by
    ext q
    simp [← op_comp]

/-- Reversing both integer indices changes cohomological to homological grading. -/
def reverseIndices {C : Type*} [Category* C] [Preadditive C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :
    HomologicalComplex₂ C (ComplexShape.down ℤ) (ComplexShape.down ℤ) :=
  HomologicalComplex₂.ofGradedObject _ _
    (fun i => (K.X (-i.1)).X (-i.2))
    (fun p p' q => (K.d (-p) (-p')).f (-q))
    (fun p q q' => (K.X (-p)).d (-q) (-q'))
    (by intro p p' h q; apply K.shape_f; intro h'; apply h; simp only [ComplexShape.down_Rel, ComplexShape.up_Rel] at *; omega)
    (by intro p q q' h; apply HomologicalComplex.shape; intro h'; apply h; simp only [ComplexShape.down_Rel, ComplexShape.up_Rel] at *; omega)
    (by intros; apply HomologicalComplex₂.d_f_comp_d_f)
    (by intros; apply HomologicalComplex.d_comp_d)
    (by intros; apply HomologicalComplex₂.d_comm)

/-- The downwards integer shape has the same parity character. -/
instance tensorSignsDownInt : ComplexShape.TensorSigns (ComplexShape.down ℤ) :=
  inferInstanceAs (ComplexShape.TensorSigns (ComplexShape.up ℤ).symm)

/-- The axis-interchange signs are unchanged on reversing the complex shape. -/
instance symmetrySymm {I : Type*} [AddMonoid I] (c : ComplexShape I)
    [ComplexShape.TensorSigns c] [TotalComplexShapeSymmetry c c c] :
    TotalComplexShapeSymmetry c.symm c.symm c.symm where
  symm p q := ComplexShape.π_symm c c c p q
  σ p q := ComplexShape.σ c c c p q
  σ_ε₁ {p p'} h q := by
    have h' := ComplexShape.σ_ε₁ (c₁ := c) c c h q
    dsimp at h' ⊢
    rw [mul_one] at h' ⊢
    change ComplexShape.σ c c c p q = c.ε q * ComplexShape.σ c c c p' q
    rw [h', ← mul_assoc, Int.units_mul_self, one_mul]
  σ_ε₂ p {q q'} h := by
    have h' := ComplexShape.σ_ε₂ c (c₂ := c) c p h
    dsimp at h' ⊢
    rw [one_mul] at h' ⊢
    change ComplexShape.σ c c c p q * c.ε p = ComplexShape.σ c c c p q'
    rw [← h', mul_assoc, Int.units_mul_self, mul_one]

@[simp] theorem sigma_symm {I : Type*} [AddMonoid I] (c : ComplexShape I)
    [ComplexShape.TensorSigns c] [TotalComplexShapeSymmetry c c c] (p q : I) :
    ComplexShape.σ c.symm c.symm c.symm p q = ComplexShape.σ c c c p q := rfl

instance symmetryDownInt : TotalComplexShapeSymmetry
    (ComplexShape.down ℤ) (ComplexShape.down ℤ) (ComplexShape.down ℤ) :=
  inferInstanceAs (TotalComplexShapeSymmetry
    (ComplexShape.up ℤ).symm (ComplexShape.up ℤ).symm (ComplexShape.up ℤ).symm)

section Canonical
variable {C : Type*} [Category* C] [Preadditive C]
variable {c : ComplexShape ℤ} [ComplexShape.TensorSigns c]
variable (K : HomologicalComplex₂ C c c)

/-- Existence of exactly the diagonal products, expressed dually as coproducts.
The equivalence with `∀ n, HasProduct (fun i : {i : ℤ × ℤ // i.1 + i.2 = n} =>
(K.X i.1.1).X i.1.2)` is an implementation obligation below. -/
abbrev HasProductTotal := (oppositeBicomplex K).HasTotal c.symm

noncomputable abbrev sumTotal [K.HasTotal c] := K.total c
noncomputable abbrev productTotal [HasProductTotal K] :=
  ((oppositeBicomplex K).total c.symm).unopSymm

noncomputable abbrev sumInjection [K.HasTotal c] (p q n : ℤ) (h : p + q = n) :=
  K.ιTotal c p q n h
noncomputable abbrev productProjection [HasProductTotal K] (p q n : ℤ) (h : p + q = n) :=
  ((oppositeBicomplex K).ιTotal c.symm p q n h).unop

/-- Rescaled vertical differential; this is the anticommuting convention. -/
def signedVertical (p q q' : ℤ) : (K.X p).X q ⟶ (K.X p).X q' :=
  c.ε p • (K.X p).d q q'

/-- Contravariance in the opposite category, in both directions. -/
def oppositeMap {L : HomologicalComplex₂ C c c} (f : K ⟶ L) :
    oppositeBicomplex L ⟶ oppositeBicomplex K :=
  HomologicalComplex₂.homMk (fun i => ((f.f i.1).f i.2).op)
    (by intro p p' q _; apply Quiver.Hom.unop_inj
        exact (HomologicalComplex₂.comm_f f p' p q).symm)
    (by intro p q q' _; apply Quiver.Hom.unop_inj
        exact ((f.f p).comm q' q).symm)

noncomputable def productMap {L : HomologicalComplex₂ C c c}
    [HasProductTotal K] [HasProductTotal L] (f : K ⟶ L) :
    productTotal K ⟶ productTotal L :=
  ((HomologicalComplex.opInverse C c).map
    (HomologicalComplex₂.total.map (oppositeMap K f) c.symm)).unop

variable [TotalComplexShapeSymmetry c c c]
instance productFlipExists [HasProductTotal K] : HasProductTotal K.flip :=
  inferInstanceAs ((oppositeBicomplex K).flip.HasTotal c.symm)

noncomputable abbrev productFlipIso [HasProductTotal K] :
    productTotal K ≅ productTotal K.flip :=
  ((HomologicalComplex.opInverse C c).mapIso
    ((oppositeBicomplex K).totalFlipIso c.symm)).unop

end Canonical

namespace Specs
variable {C : Type*} [Category* C] [Preadditive C]
variable {c : ComplexShape ℤ} [ComplexShape.TensorSigns c]

-- Definitions have independent expected values, rather than assumed certificates.
def SumType := ∀ (K : HomologicalComplex₂ C c c) [K.HasTotal c], HomologicalComplex C c
noncomputable def sumValue : SumType (C := C) (c := c) := fun K => K.total c

def ProductType := ∀ (K : HomologicalComplex₂ C c c) [HasProductTotal K], HomologicalComplex C c
noncomputable def productValue : ProductType (C := C) (c := c) :=
  fun K => ((oppositeBicomplex K).total c.symm).unopSymm

-- Component formulas permit arbitrary related degrees; for up ℤ these are p+1,q+1.
def SumDifferential : Prop := ∀ (K : HomologicalComplex₂ C c c) [K.HasTotal c]
    (p p' q q' n n' : ℤ) (_hp : c.Rel p p') (_hq : c.Rel q q')
    (h : p + q = n) (hh : p' + q = n') (hv : p + q' = n'),
  sumInjection K p q n h ≫ (sumTotal K).d n n' =
    (K.d p p').f q ≫ sumInjection K p' q n' hh +
    c.ε p • ((K.X p).d q q' ≫ sumInjection K p q' n' hv)

def ProductDifferential : Prop := ∀ (K : HomologicalComplex₂ C c c) [HasProductTotal K]
    (p p' q q' n n' : ℤ) (_hp : c.Rel p' p) (_hq : c.Rel q' q)
    (h : p + q = n') (hh : p' + q = n) (hv : p + q' = n),
  (productTotal K).d n n' ≫ productProjection K p q n' h =
    productProjection K p' q n hh ≫ (K.d p' p).f q +
    c.ε p • (productProjection K p q' n hv ≫ (K.X p).d q' q)

def UnchangedSumDifferential : Prop := ∀ (K : HomologicalComplex₂ C c c) [K.HasTotal c]
    (p p' q q' n n' : ℤ) (_hp : c.Rel p p') (_hq : c.Rel q q')
    (h : p + q = n) (hh : p' + q = n') (hv : p + q' = n'),
  sumInjection K p q n h ≫ (sumTotal K).d n n' =
    (K.d p p').f q ≫ sumInjection K p' q n' hh +
    signedVertical K p q q' ≫ sumInjection K p q' n' hv

def UnchangedProductDifferential : Prop := ∀ (K : HomologicalComplex₂ C c c) [HasProductTotal K]
    (p p' q q' n n' : ℤ) (_hp : c.Rel p' p) (_hq : c.Rel q' q)
    (h : p + q = n') (hh : p' + q = n) (hv : p + q' = n),
  (productTotal K).d n n' ≫ productProjection K p q n' h =
    productProjection K p' q n hh ≫ (K.d p' p).f q +
    productProjection K p q' n hv ≫ signedVertical K p q' q

def SumSquareZero : Prop := ∀ (K : HomologicalComplex₂ C c c) [K.HasTotal c] (i j k : ℤ),
  (sumTotal K).d i j ≫ (sumTotal K).d j k = 0

def ProductSquareZero : Prop := ∀ (K : HomologicalComplex₂ C c c) [HasProductTotal K] (i j k : ℤ),
  (productTotal K).d i j ≫ (productTotal K).d j k = 0

def ProductExistence : Prop := ∀ (K : HomologicalComplex₂ C c c),
  HasProductTotal K ↔ ∀ n : ℤ,
    HasProduct (fun i : {i : ℤ × ℤ // i.1 + i.2 = n} => (K.X i.1.1).X i.1.2)

def SignConvention : Prop := ∀ (K : HomologicalComplex₂ C c c),
  (∀ p q q' q'', signedVertical K p q q' ≫ signedVertical K p q' q'' = 0) ∧
  (∀ p p' q q', c.Rel p p' →
    (K.d p p').f q ≫ signedVertical K p' q q' +
    signedVertical K p q q' ≫ (K.d p p').f q' = 0) ∧
  (∀ p q q', c.ε p • signedVertical K p q q' = (K.X p).d q q')

def ProductUniversal : Prop := ∀ (K : HomologicalComplex₂ C c c) [HasProductTotal K]
    (n : ℤ) (A : C) (f : ∀ p q : ℤ, p + q = n → (A ⟶ (K.X p).X q)),
  ∃! g : A ⟶ (productTotal K).X n, ∀ p q (h : p + q = n),
    g ≫ productProjection K p q n h = f p q h

/-- Full reindexing construction, with objects C^(-p,-q) and inherited differentials. -/
def HomologicalReindexType :=
  HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) →
    HomologicalComplex₂ C (ComplexShape.down ℤ) (ComplexShape.down ℤ)
def homologicalReindexValue : HomologicalReindexType (C := C) := reverseIndices

/-- These equalities identify all abstract sign characters used above with the
source's (-1)^p and (-1)^(pq), for both cochain and chain grading. -/
def GradingSigns : Prop := ∀ p q : ℤ,
  (ComplexShape.up ℤ).ε p = p.negOnePow ∧
  (ComplexShape.down ℤ).ε p = p.negOnePow ∧
  ComplexShape.σ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) p q =
    (p * q).negOnePow ∧
  ComplexShape.σ (ComplexShape.down ℤ) (ComplexShape.down ℤ) (ComplexShape.down ℤ) p q =
    (p * q).negOnePow ∧
  (-p).negOnePow = p.negOnePow ∧
  ((-p) * (-q)).negOnePow = (p * q).negOnePow

variable [TotalComplexShapeSymmetry c c c]
def SumSymmetryType := ∀ (K : HomologicalComplex₂ C c c) [K.HasTotal c],
  sumTotal K ≅ sumTotal K.flip
noncomputable def sumSymmetryValue : SumSymmetryType (C := C) (c := c) :=
  fun K => (K.totalFlipIso c).symm

def SumSymmetryFormula : Prop := ∀ (K : HomologicalComplex₂ C c c) [K.HasTotal c]
    (p q n : ℤ) (h : p + q = n),
  sumInjection K p q n h ≫ (K.totalFlipIso c).inv.f n =
    ComplexShape.σ c c c p q • sumInjection K.flip q p n (by simpa [add_comm] using h)

def SumNaturality : Prop := ∀ (K L : HomologicalComplex₂ C c c) [K.HasTotal c] [L.HasTotal c]
    (f : K ⟶ L),
  HomologicalComplex₂.total.map f c ≫ (L.totalFlipIso c).inv =
    (K.totalFlipIso c).inv ≫ HomologicalComplex₂.total.map
      (show K.flip ⟶ L.flip from (HomologicalComplex₂.flipFunctor C c c).map f) c

def ProductSymmetryType := ∀ (K : HomologicalComplex₂ C c c) [HasProductTotal K],
  productTotal K ≅ productTotal K.flip
noncomputable def productSymmetryValue : ProductSymmetryType (C := C) (c := c) :=
  fun K => productFlipIso K

def ProductSymmetryFormula : Prop := ∀ (K : HomologicalComplex₂ C c c) [HasProductTotal K]
    (p q n : ℤ) (h : p + q = n),
  (productFlipIso K).hom.f n ≫ productProjection K.flip q p n (by simpa [add_comm] using h) =
    ComplexShape.σ c c c p q • productProjection K p q n h

def ProductNaturality : Prop := ∀ (K L : HomologicalComplex₂ C c c)
    [HasProductTotal K] [HasProductTotal L] (f : K ⟶ L),
  productMap K f ≫ (productFlipIso L).hom =
    (productFlipIso K).hom ≫ productMap K.flip
      (show K.flip ⟶ L.flip from (HomologicalComplex₂.flipFunctor C c c).map f)


/- Closed expected types retain the full universe and category quantifiers. -/
def ExpectedSumType := ∀ {C : Type u} [Category.{v} C] [Preadditive C] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c], SumType (C := C) (c := c)

def ExpectedProductType := ∀ {C : Type u} [Category.{v} C] [Preadditive C] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c], ProductType (C := C) (c := c)

def ExpectedSumDifferential := ∀ {C : Type u} [Category.{v} C] [Preadditive C] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c], SumDifferential (C := C) (c := c)

def ExpectedProductDifferential := ∀ {C : Type u} [Category.{v} C] [Preadditive C] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c], ProductDifferential (C := C) (c := c)

def ExpectedUnchangedSumDifferential := ∀ {C : Type u} [Category.{v} C] [Preadditive C] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c], UnchangedSumDifferential (C := C) (c := c)

def ExpectedUnchangedProductDifferential := ∀ {C : Type u} [Category.{v} C] [Preadditive C] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c], UnchangedProductDifferential (C := C) (c := c)

def ExpectedSumSquareZero := ∀ {C : Type u} [Category.{v} C] [Preadditive C] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c], SumSquareZero (C := C) (c := c)

def ExpectedProductSquareZero := ∀ {C : Type u} [Category.{v} C] [Preadditive C] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c], ProductSquareZero (C := C) (c := c)

def ExpectedProductExistence := ∀ {C : Type u} [Category.{v} C] [Preadditive C] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c], ProductExistence (C := C) (c := c)

def ExpectedSignConvention := ∀ {C : Type u} [Category.{v} C] [Preadditive C] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c], SignConvention (C := C) (c := c)

def ExpectedProductUniversal := ∀ {C : Type u} [Category.{v} C] [Preadditive C] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c], ProductUniversal (C := C) (c := c)

def ExpectedHomologicalReindexType := ∀ {C : Type u} [Category.{v} C] [Preadditive C], HomologicalReindexType (C := C)

def ExpectedGradingSigns := GradingSigns

def ExpectedSumSymmetryType := ∀ {C : Type u} [Category.{v} C] [Preadditive C] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c] [TotalComplexShapeSymmetry c c c], SumSymmetryType (C := C) (c := c)

def ExpectedSumSymmetryFormula := ∀ {C : Type u} [Category.{v} C] [Preadditive C] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c] [TotalComplexShapeSymmetry c c c], SumSymmetryFormula (C := C) (c := c)

def ExpectedSumNaturality := ∀ {C : Type u} [Category.{v} C] [Preadditive C] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c] [TotalComplexShapeSymmetry c c c], SumNaturality (C := C) (c := c)

def ExpectedProductSymmetryType := ∀ {C : Type u} [Category.{v} C] [Preadditive C] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c] [TotalComplexShapeSymmetry c c c], ProductSymmetryType (C := C) (c := c)

def ExpectedProductSymmetryFormula := ∀ {C : Type u} [Category.{v} C] [Preadditive C] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c] [TotalComplexShapeSymmetry c c c], ProductSymmetryFormula (C := C) (c := c)

def ExpectedProductNaturality := ∀ {C : Type u} [Category.{v} C] [Preadditive C] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c] [TotalComplexShapeSymmetry c c c], ProductNaturality (C := C) (c := c)

end Specs
end AdvancedHomologicalAlgebra.DoubleTotalization
