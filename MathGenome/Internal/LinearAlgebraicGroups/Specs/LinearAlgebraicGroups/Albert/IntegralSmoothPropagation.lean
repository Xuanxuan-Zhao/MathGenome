import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.Basic

open AlgebraicGeometry
open scoped TensorProduct

namespace Specs.LinearAlgebraicGroups.Albert.IntegralSmoothPropagation

/-- Propagation of smoothness of fixed relative dimension from the augmentation
charts of a finitely presented integral algebra with smooth irreducible geometric fibers. -/
def IntegralSmoothPropagationType : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra.FinitePresentation ℤ A]
    (e : A →ₐ[ℤ] ℤ) (d : ℕ),
    (∀ (k : Type) [Field k], ∃ f : A, algebraMap ℤ k (e f) ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension d ℤ (Localization.Away f)) →
    (∀ (k : Type) [Field k] [IsAlgClosed k],
      Algebra.Smooth k (k ⊗[ℤ] A) ∧ IrreducibleSpace (PrimeSpectrum (k ⊗[ℤ] A))) →
    SmoothOfRelativeDimension d (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))) ∧
      GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap ℤ A)))

end Specs.LinearAlgebraicGroups.Albert.IntegralSmoothPropagation
