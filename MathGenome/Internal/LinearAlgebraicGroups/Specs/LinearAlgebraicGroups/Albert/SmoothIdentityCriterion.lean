import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

open TensorProduct

namespace Specs.LinearAlgebraicGroups.Albert.SmoothIdentityCriterion

/-- The cotangent fiber of an algebra at the point specified by its map to a field. -/
abbrev CotangentFiber (R A K : Type*) [CommRing R] [CommRing A] [Field K]
    [Algebra R A] [Algebra A K] :=
  K ⊗[A] Ω[A⁄R]

/-- The cotangent fiber map. On simple tensors it takes (k \otimes db) to
(k \otimes d(f(b))). Its field-linear dual is the relative tangent map. -/
noncomputable def cotangentFiberMap (R B C K : Type*)
    [CommRing R] [CommRing B] [CommRing C] [Field K]
    [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
    [Algebra B K] [Algebra C K] [IsScalarTower B C K] :
    CotangentFiber R B K →ₗ[K] CotangentFiber R C K :=
  (KaehlerDifferential.mapBaseChange R B C).baseChange K ∘ₗ
    (AlgebraTensorModule.cancelBaseChange B C K K Ω[B⁄R]).symm.toLinearMap

/-- Relative smoothness detected by a smooth parametrization at a field-valued point.
The algebra tower (B \to C \to K) specifies the two compatible points. The
source is smooth at the point with relative dimension (d), expressed by
the dimension of its cotangent fiber there. -/
def SmoothIdentityCriterionType : Prop :=
  ∀ (R B C K : Type*) [CommRing R] [CommRing B] [CommRing C] [Field K]
    [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
    [Algebra B K] [Algebra C K] [IsScalarTower B C K]
    [Algebra.FinitePresentation R B] [Algebra.FinitePresentation R C]
    (d : ℕ),
    (letI : (RingHom.ker (algebraMap C K)).IsPrime := RingHom.ker_isPrime _
     Algebra.IsSmoothAt R (RingHom.ker (algebraMap C K))) →
    Module.finrank K (CotangentFiber R C K) = d →
    Function.Bijective (cotangentFiberMap R B C K).dualMap →
    ∃ b : B, algebraMap B K b ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension d R (Localization.Away b)

/-- The same criterion stated using precomposition on field-valued relative
derivations. The algebra structures on the field give the module actions at
the two compatible points. -/
def DerivationSmoothIdentityCriterionType : Prop :=
  ∀ (R B C K : Type*) [CommRing R] [CommRing B] [CommRing C] [Field K]
    [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
    [Algebra B K] [Algebra C K] [IsScalarTower B C K]
    [Algebra R K] [IsScalarTower R B K] [IsScalarTower R C K]
    [Algebra.FinitePresentation R B] [Algebra.FinitePresentation R C]
    (d : ℕ),
    (letI : (RingHom.ker (algebraMap C K)).IsPrime := RingHom.ker_isPrime _
     Algebra.IsSmoothAt R (RingHom.ker (algebraMap C K))) →
    Module.finrank K (CotangentFiber R C K) = d →
    Function.Bijective (fun D : Derivation R C K => D.compAlgebraMap B) →
    ∃ b : B, algebraMap B K b ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension d R (Localization.Away b)

end Specs.LinearAlgebraicGroups.Albert.SmoothIdentityCriterion
