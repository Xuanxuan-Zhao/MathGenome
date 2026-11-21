import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.MappingCones
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-! HA-K04, source lines 1297–1330. A degreewise splitting is specified by
retractions r and sections s with ur=1, sv=1, ru+vs=1. Thus it is exactly a
graded identification Bⁿ ≅ Aⁿ ⊞ Cⁿ compatible with u,v; no abelian hypothesis
or splitting by cochain maps is imposed. The third cone arrow is -p.
-/
set_option linter.checkUnivs false
set_option linter.unusedVariables false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe v u
open CategoryTheory CategoryTheory.Limits
open HomologicalComplex CochainComplex CochainComplex.HomComplex
namespace Specs.AdvancedHomologicalAlgebra.SplitSequenceTriangles
variable {D : Type u} [Category.{v} D] [Preadditive D]

abbrev DegreewiseSplitting (S : ShortComplex (CochainComplex D ℤ)) :=
  ∀ n : ℤ, (S.map (eval D _ n)).Splitting

abbrev boundary (S : ShortComplex (CochainComplex D ℤ)) (σ : DegreewiseSplitting S) :=
  homOfDegreewiseSplit S σ

noncomputable def coneComparison [HasBinaryBiproducts D]
    (S : ShortComplex (CochainComplex D ℤ)) : mappingCone S.f ⟶ S.X₃ :=
  mappingCone.desc S.f 0 S.g (by simp [S.zero])

/-- The connecting cochain map C → A[1], with the usual positive cocycle-lift sign. -/
def boundaryType := ∀ (D : Type u) [Category.{v} D] [Preadditive D]
  (S : ShortComplex (CochainComplex D ℤ)) (σ : DegreewiseSplitting S),
  S.X₃ ⟶ S.X₁⟦(1 : ℤ)⟧
def boundaryValue : boundaryType := fun _ _ _ S σ => boundary S σ

def boundary_componentsType := ∀ (D : Type u) [Category.{v} D] [Preadditive D]
  (S : ShortComplex (CochainComplex D ℤ)) (σ : DegreewiseSplitting S) (n : ℤ),
  (boundary S σ).f n = (σ n).s ≫ S.X₂.d n (n+1) ≫ (σ (n+1)).r

/-- The graded identifications and the full block differential in source order A,C. -/
def coordinatesType := ∀ (D : Type u) [Category.{v} D] [Preadditive D]
  [HasBinaryBiproducts D] (S : ShortComplex (CochainComplex D ℤ))
  (σ : DegreewiseSplitting S) (n : ℤ),
  let e := (σ n).isoBinaryBiproduct
  let e' := (σ (n+1)).isoBinaryBiproduct
  S.f.f n ≫ e.hom = biprod.inl ∧
  e.inv ≫ S.g.f n = biprod.snd ∧
  e.inv ≫ S.X₂.d n (n+1) ≫ e'.hom =
    biprod.lift (biprod.fst ≫ S.X₁.d n (n+1) +
      biprod.snd ≫ (boundary S σ).f n) (biprod.snd ≫ S.X₃.d n (n+1))

/-- Naturality for every map of short complexes and any two graded splittings. -/
def naturalityHomotopyType := ∀ (D : Type u) [Category.{v} D] [Preadditive D]
  (S S' : ShortComplex (CochainComplex D ℤ)) (σ : DegreewiseSplitting S)
  (σ' : DegreewiseSplitting S') (φ : S ⟶ S'),
  Nonempty (Homotopy (boundary S σ ≫ φ.τ₁⟦(1 : ℤ)⟧')
    (φ.τ₃ ≫ boundary S' σ'))

def independentType := ∀ (D : Type u) [Category.{v} D] [Preadditive D]
  (S : ShortComplex (CochainComplex D ℤ)) (σ τ : DegreewiseSplitting S),
  (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map (boundary S σ) =
    (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map (boundary S τ)

def naturalityType := ∀ (D : Type u) [Category.{v} D] [Preadditive D]
  (S S' : ShortComplex (CochainComplex D ℤ)) (σ : DegreewiseSplitting S)
  (σ' : DegreewiseSplitting S') (φ : S ⟶ S'),
  let Q := HomotopyCategory.quotient D (ComplexShape.up ℤ)
  Q.map (boundary S σ) ≫ Q.map (φ.τ₁⟦(1 : ℤ)⟧') =
    Q.map φ.τ₃ ≫ Q.map (boundary S' σ')

/-- Naturality expressed using the actual shift functor on the homotopy category. -/
def naturalityShiftType := ∀ (D : Type u) [Category.{v} D] [Preadditive D]
  (S S' : ShortComplex (CochainComplex D ℤ)) (σ : DegreewiseSplitting S)
  (σ' : DegreewiseSplitting S') (φ : S ⟶ S'),
  let Q := HomotopyCategory.quotient D (ComplexShape.up ℤ)
  (trianglehOfDegreewiseSplit S σ).mor₃ ≫ (Q.map φ.τ₁)⟦(1 : ℤ)⟧' =
    Q.map φ.τ₃ ≫ (trianglehOfDegreewiseSplit S' σ').mor₃

def coneComparisonType := ∀ (D : Type u) [Category.{v} D] [Preadditive D]
  [HasBinaryBiproducts D] (S : ShortComplex (CochainComplex D ℤ)),
  mappingCone S.f ⟶ S.X₃
noncomputable def coneComparisonValue : coneComparisonType := fun _ _ _ _ S => coneComparison S

def comparison_componentsType := ∀ (D : Type u) [Category.{v} D] [Preadditive D]
  [HasBinaryBiproducts D] (S : ShortComplex (CochainComplex D ℤ)) (n : ℤ),
  (coneComparison S).f n =
    (Specs.AdvancedHomologicalAlgebra.MappingCones.targetProjection S.f n) ≫ S.g.f n

/-- The isomorphism fixes A,B and is the splitting-independent map (b,a') ↦ v(b)
on the third object. This expresses canonicity, including the three row squares. -/
def coneRowIsoType := ∀ (D : Type u) [Category.{v} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]
  (S : ShortComplex (CochainComplex D ℤ)) (σ : DegreewiseSplitting S),
  ∃ e : mappingCone.triangleh S.f ≅ trianglehOfDegreewiseSplit S σ,
    e.hom.hom₁ = 𝟙 _ ∧ e.hom.hom₂ = 𝟙 _ ∧
      e.hom.hom₃ = (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map (coneComparison S)

/-- Explicitly fixes the third-arrow convention used in subsequent triangles. -/
def negativeProjectionType := ∀ (D : Type u) [Category.{v} D] [Preadditive D]
  [HasBinaryBiproducts D] (X Y : CochainComplex D ℤ) (f : X ⟶ Y),
  (mappingCone.triangle f).mor₃ =
    -Specs.AdvancedHomologicalAlgebra.MappingCones.projectionToShift f
end Specs.AdvancedHomologicalAlgebra.SplitSequenceTriangles
