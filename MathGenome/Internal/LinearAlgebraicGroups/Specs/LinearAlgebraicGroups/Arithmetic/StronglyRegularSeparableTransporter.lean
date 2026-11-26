import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SteinbergGeometricFibres
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AutomorphismSequence
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.NonabelianCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.CartesianMonoidalCategory Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.StronglyRegularSeparableTransporter

open GeometricRadicals (IsReductive IsSplitTorus IsTorus)
open SteinbergGeometricFibres (IsPointCentralizer)
open AutomorphismSequence (AdjointQuotient automorphisms groupSections innerAut)
open _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology (pointMap pointAction)

noncomputable section

variable {k S : Type u} [Field k] [Field S] [Algebra k S]

/-- The rational section of the extended scheme corresponding to an extension-field point. -/
def extendedPoint {X : SchemeOver k} (y : Points X (CommAlgCat.of k S)) :
    𝟙_ (SchemeOver S) ⟶ (baseChange k S).obj X :=
  (Over.mapPullbackAdj (fieldSpecMap k S)).homEquiv _ _
    (Over.homMk (𝟙 _) (by simp) ≫ y)

/-- Fixing a rational point under the inner action, tested on an arbitrary family. -/
def Fixes {G H : GroupScheme k} (a : groupSections H ⟶ automorphisms G)
    (x : 𝟙_ (SchemeOver k) ⟶ G.X) {Y : SchemeOver k} (h : Y ⟶ H.X) : Prop :=
  let U := Over.mk (𝟙 Y)
  ((a.app (op Y) ⟨h⟩).asIso.hom.app (op U)).hom (toUnit Y ≫ x) = toUnit Y ≫ x

/-- The full transporter has a separable point, and the ground-field centralizer is a torus. -/
def SeparableTransporter : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (f : S →ₐ[k] AlgebraicClosure k) (x : 𝟙_ (SchemeOver k) ⟶ G.val.X)
      (y : Points G.val.X (CommAlgCat.of k S))
      (C : ClosedSubgroup ((groupBaseChange k S).obj G.val)),
      IsSplitTorus C.group → IsPointCentralizer C (extendedPoint y) →
      (∃ g : Points G.val.X (CommAlgCat.of k (AlgebraicClosure k)),
        g * (toUnit _ ≫ x) * g⁻¹ = pointMap k S G.val.X f y) →
      (∃ b : Points G.val.X (CommAlgCat.of k S), b * (toUnit _ ≫ x) * b⁻¹ = y) ∧
      ∃ T : ClosedSubgroup G.val, IsTorus T.group ∧ IsPointCentralizer T x

/-- The torus stabilizer in the adjoint group represents fixing on every test scheme.
Its section map over the separable closure is an equivariant injection with the stated range. -/
def AdjointTorusStabilizer : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (x : 𝟙_ (SchemeOver k) ⟶ G.val.X) (T : ClosedSubgroup G.val),
      IsTorus T.group → IsPointCentralizer T x →
      ∀ (Q : AdjointQuotient G) (a : groupSections Q.quotient.val ⟶ automorphisms G.val),
        (∀ (Y : SchemeOver k) (g : Y ⟶ G.val.X),
          a.app (op Y) ⟨g ≫ Q.projection.hom.hom⟩ = innerAut g) →
        ∃ D : ClosedSubgroup Q.quotient.val, IsTorus D.group ∧
          RepresentsSubgroup D (fun _ h ↦ Fixes a x h) ∧
          ∃ p : Points D.group.X (CommAlgCat.of k S) →*
              Points Q.quotient.val.X (CommAlgCat.of k S),
            (∀ t, p t = t ≫ D.inclusion.hom.hom) ∧ Function.Injective p ∧
            (∀ (σ : Gal(S/k)) t, p (pointAction k S D.group.X σ t) =
              pointAction k S Q.quotient.val.X σ (p t)) ∧
            ∀ h, h ∈ p.range ↔ Fixes a x h

end
end LinearAlgebraicGroups.Specs.StronglyRegularSeparableTransporter
