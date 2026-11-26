import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.PowerSeriesLocalCohomology
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.NoncompleteDVRLocalCohomology

open CategoryTheory IsLocalRing

namespace Specs.CommutativeAlgebraNotes.PowerSeriesAndNoncompleteDVR

open PowerSeriesLocalCohomology
open NoncompleteDVRLocalCohomology
open CompletionOfTorsionModules (Completion IsPowerTorsion completionModule completionScalarTower)
open _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs (residueFieldEnvelopeValue)

universe u

/-- The inverse-monomial basis and the local cohomology and dual of the local line. -/
def LocalCohomologyExamples : Prop :=
  ∀ (k : Type u) [Field k],
    (∀ d : ℕ,
      ∃ π : ModuleCat.of (Series k d) (Localization.Away (fullProduct k d)) ⟶ top k d,
        Function.Surjective π ∧ π.hom.ker = faceImages k d ∧
          ∃ b : Module.Basis (Index d) k (topOverField k d),
            (∀ a, b a = π (inverseMonomial k d a)) ∧
            (d = 0 → ∀ a, b a = π 1) ∧
            ∀ E : residueFieldEnvelopeValue (Series k d),
              Nonempty (top k d ≅ ModuleCat.of (Series k d) E.carrier)) ∧
    (let T := LocalLine k
     IsDiscreteValuationRing T ∧ maximalIdeal T = Ideal.span {parameter k} ∧
       ¬ IsAdicComplete (maximalIdeal T) T ∧
       Nonempty (TopCohomology k ≃ₗ[T] FractionQuotient k) ∧
       ∀ E : residueFieldEnvelopeValue T,
         Nonempty (TopCohomology k ≃ₗ[T] E.carrier) ∧
         ∃ (h : IsPowerTorsion T E.carrier) (e : Completion T ≃ₐ[T] PowerSeries k),
           letI := completionModule h
           letI := completionScalarTower h
           letI : Module (Completion T) (PowerSeries k) := Module.compHom _ e.toRingHom
           Nonempty ((TopCohomology k →ₗ[T] E.carrier) ≃ₗ[Completion T] PowerSeries k))

end Specs.CommutativeAlgebraNotes.PowerSeriesAndNoncompleteDVR
