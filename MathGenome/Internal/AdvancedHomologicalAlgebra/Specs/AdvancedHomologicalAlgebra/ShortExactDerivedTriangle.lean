import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.MappingCones
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DerivedCategory
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
HA-D04, notes/002/advanced-homological-algebra.tex:1547–1573.
The global convention is cohomological: X[1]^n = X^(n+1), with negative
shift differential. The category is any abelian category, the complexes
are unbounded, and no degreewise splitting is assumed. We use the same
chosen derived category as HA-D03 (the standard choice exists for every A).
`projectionToShift` is the positive projection from HA-K02. Consequently
the last arrow uses its negative. The shift comparison of Q is displayed
explicitly because Q(X[1]) and (Q X)[1] need not be definitionally equal.
The ordinary boundary below is the snake-lemma boundary of the short exact
sequence, whose lift-and-differential characterization is stated explicitly.
-/

set_option linter.checkUnivs false
universe w v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex
open Specs.AdvancedHomologicalAlgebra.MappingCones
open Specs.AdvancedHomologicalAlgebra.DerivedCategory

namespace Specs.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle

section Constructions
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The map q(b,a)=v(b), defined even before exactness is assumed. -/
noncomputable abbrev coneToThird (S : ShortComplex (CochainComplex A ℤ)) :=
  mappingCone.descShortComplex S

variable [HasDerivedCategory.{w} A]

noncomputable abbrev connecting {S : ShortComplex (CochainComplex A ℤ)}
    (hS : S.ShortExact) := _root_.DerivedCategory.triangleOfSESδ hS

noncomputable abbrev row {S : ShortComplex (CochainComplex A ℤ)}
    (hS : S.ShortExact) := _root_.DerivedCategory.triangleOfSES hS

end Constructions

def coneToThirdType := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  (S : ShortComplex (CochainComplex A ℤ)), coneComplex S.f ⟶ S.X₃
noncomputable def coneToThirdValue : coneToThirdType := fun _ _ _ S => coneToThird S

def coneToThird_coordinatesType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  (S : ShortComplex (CochainComplex A ℤ)) (n : ℤ),
  (degreeBiproductIso S.f n).inv ≫ (coneToThird S).f n = biprod.desc (S.g.f n) 0

def coneToThird_quasiIsoType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  (S : ShortComplex (CochainComplex A ℤ)), S.ShortExact → QuasiIso (coneToThird S)

def connectingType := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (S : ShortComplex (CochainComplex A ℤ)) (_ : S.ShortExact),
  _root_.DerivedCategory.Q.obj S.X₃ ⟶ (_root_.DerivedCategory.Q.obj S.X₁)⟦(1 : ℤ)⟧
noncomputable def connectingValue : connectingType := fun _ _ _ _ _ hS => connecting hS

/-- Composition is written in diagrammatic order: q⁻¹ followed by Q(-p). -/
def connecting_formulaType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact),
  letI := mappingCone.quasiIso_descShortComplex hS
  connecting hS = inv (_root_.DerivedCategory.Q.map (coneToThird S)) ≫
    _root_.DerivedCategory.Q.map (-projectionToShift S.f) ≫
      (_root_.DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app S.X₁

def triangleType := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (S : ShortComplex (CochainComplex A ℤ)) (_ : S.ShortExact),
  Triangle (D A)
noncomputable def triangleValue : triangleType := fun _ _ _ _ _ hS => row hS

def triangle_arrowsType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact),
  row hS = Triangle.mk (_root_.DerivedCategory.Q.map S.f)
    (_root_.DerivedCategory.Q.map S.g) (connecting hS)

def distinguishedType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact),
  row hS ∈ distTriang (D A)

/-- All morphisms of short exact sequences give the indicated morphism of triangles. -/
def triangleMapType := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (S S' : ShortComplex (CochainComplex A ℤ))
  (hS : S.ShortExact) (hS' : S'.ShortExact) (_f : S ⟶ S'), row hS ⟶ row hS'
noncomputable def triangleMapValue : triangleMapType :=
  fun _ _ _ _ _ _ hS hS' f => _root_.DerivedCategory.triangleOfSES.map hS hS' f

def naturalityType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (S S' : ShortComplex (CochainComplex A ℤ))
  (hS : S.ShortExact) (hS' : S'.ShortExact) (f : S ⟶ S'),
  connecting hS ≫ (_root_.DerivedCategory.Q.map f.τ₁)⟦(1 : ℤ)⟧' =
    _root_.DerivedCategory.Q.map f.τ₃ ≫ connecting hS'

/-- Under the canonical identifications with ordinary cohomology, the boundary
of the derived triangle is exactly the usual snake-lemma connecting morphism. -/
def cohomology_boundaryType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
  (n m : ℤ) (h : n + 1 = m),
  _root_.DerivedCategory.HomologySequence.δ (row hS) n m h ≫
      (_root_.DerivedCategory.homologyFunctorFactors A m).hom.app S.X₁ =
    (_root_.DerivedCategory.homologyFunctorFactors A n).hom.app S.X₃ ≫
      hS.δ n m h

/-- Lift a cocycle c to b in B; lift db along u to a in A. The ordinary
boundary is [a]. This is stated with test objects, so it applies in any
abelian category and does not require elements or projectives. -/
def lift_differentialType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
  (n m : ℤ) (h : n + 1 = m) (P : A)
  (c : P ⟶ S.X₃.X n) (hc : c ≫ S.X₃.d n m = 0)
  (b : P ⟶ S.X₂.X n) (hb : b ≫ S.g.f n = c)
  (a : P ⟶ S.X₁.X m) (ha : a ≫ S.f.f m = b ≫ S.X₂.d n m),
  S.X₃.liftCycles c m ((ComplexShape.up ℤ).next_eq' h) hc ≫ S.X₃.homologyπ n ≫ hS.δ n m h =
    S.X₁.liftCycles a (m + 1) (by simp) (by
      have := hS.mono_f
      rw [← cancel_mono (S.f.f (m + 1)), Category.assoc, ← S.f.comm,
        reassoc_of% ha, HomologicalComplex.d_comp_d, comp_zero, zero_comp]) ≫
          S.X₁.homologyπ m

/-- Every six-term window in the resulting long cohomology sequence is exact. -/
def cohomologyExactType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact),
  Specs.AdvancedHomologicalAlgebra.TriangleExactSequences.LongExact (HD A 0) (row hS)

end Specs.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle
