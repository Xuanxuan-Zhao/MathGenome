import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.GeometricReductivity
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.HomogeneousQuotient

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.ClosedHomogeneousOrbits

open GeometricRadicals (IsSemisimple)
open Unipotent (closedSubgroupAlgebraicGroup)
open RootWeightAction (Representation act)

noncomputable section

variable {k : Type u} [Field k]

/-- Affine space with its coordinates indexed by a basis of the dual. -/
abbrev vectorSpace (k I : Type u) [Field k] : SchemeOver k :=
  (testSpec k).obj (op (CommAlgCat.of k (MvPolynomial I k)))

/-- The point with the given coordinates over a commutative test algebra. -/
def vectorPoint {I : Type u} (R : TestAlgebra k) (v : I → R) :
    Points (vectorSpace k I) R :=
  (testSpec k).map (CommAlgCat.ofHom (MvPolynomial.aeval v)).op

/-- The fppf right quotient of a special linear group by a closed semisimple
subgroup is affine and is the closed orbit of its identity coset in a rational
linear representation. The stabilizer represents the same functor after every
field extension. -/
def ClosedHomogeneousOrbit : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (m : ℕ) (P : AffineAlgebraicGroup k)
    (_ : (groupPointsFunctor k).obj P.val ≅
      StandardGroups.specialLinearPoints k (ULift.{u} (Fin m)))
    (H : ClosedSubgroup P.val), IsSemisimple (closedSubgroupAlgebraicGroup H) →
    ∃ (Q : QuotientEmbedding.Presentation H)
      (I : Type u) (_ : Fintype I) (_ : DecidableEq I)
      (ρ : Representation P.val I) (a : ModObj P.val.X (vectorSpace k I))
      (b : ModObj P.val.X Q.scheme) (j : Q.scheme ⟶ vectorSpace k I),
      let x := η[P.val.X] ≫ Q.projection ≫ j
      IsAffine Q.scheme.left ∧
      HomogeneousQuotient.IsQuotientTorsor Q ∧ Smooth Q.projection.left ∧
      IsClosedImmersion j.left ∧
      (∀ (R : TestAlgebra k) (g : Points P.val.X R) (v : I → R),
        lift g (vectorPoint R v) ≫ a.smul = vectorPoint R (act ρ R g v)) ∧
      b.smul ≫ j = (𝟙 P.val.X ⊗ₘ j) ≫ a.smul ∧
      Q.projection ≫ j = SmoothOrbit.orbitMap a x ∧
      RepresentsSubgroup H (fun _ g ↦ Stabilizes a.smul x g) ∧
      ∀ (K : Type u) [Field K] [Algebra k K],
        ∃ h : IsClosedImmersion ((groupBaseChange k K).map H.inclusion).hom.hom.left,
          RepresentsSubgroup (scalarExtendedSubgroup K H h) (fun _ g ↦
            Stabilizes (baseChangeAction K a.smul) (scalarExtendedRationalPoint K x) g)

end

end LinearAlgebraicGroups.Specs.ClosedHomogeneousOrbits
