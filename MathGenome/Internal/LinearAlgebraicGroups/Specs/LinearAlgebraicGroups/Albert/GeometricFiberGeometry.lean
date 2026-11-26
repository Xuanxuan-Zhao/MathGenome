import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.ShortDirections
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.TensorProduct.Basic

namespace LinearAlgebraicGroups.Albert.GeometricFiberSpecification

open AlgebraicGeometry ShortDirectionSpecification
open scoped TensorProduct

abbrev FiberRing (P : IntegralPresentation) (k : Type) [Field k] :=
  letI : Module ℤ k := Algebra.toModule
  letI : Module ℤ P.Coordinates := Algebra.toModule
  k ⊗[ℤ] P.Coordinates

noncomputable abbrev fiberScheme (P : IntegralPresentation) (k : Type) [Field k] : Scheme :=
  Spec (CommRingCat.of (FiberRing P k))

noncomputable def fiberStructure (P : IntegralPresentation) (k : Type) [Field k] :
    fiberScheme P k ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (FiberRing P k)))

/-- The tensor-product fiber of the integral presentation is smooth and irreducible
over every algebraically closed field, including characteristics two and three. -/
def GeometricFiberGeometryType : Prop :=
  ∀ (P : IntegralPresentation) (e : P.Coordinates →ₐ[ℤ] ℤ),
    P.IsIdentity e →
    (∀ (k : Type) [Field k], ∃ f : P.Coordinates,
      algebraMap ℤ k (e f) ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension 52 ℤ (Localization.Away f)) →
    ∀ (k : Type) [Field k] [IsAlgClosed k],
      Smooth (fiberStructure P k) ∧ IrreducibleSpace (fiberScheme P k)

end LinearAlgebraicGroups.Albert.GeometricFiberSpecification
