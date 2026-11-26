import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.TwoDegreeExampleCechCalculation
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.TwoDegreeExampleDualizingCalculation

open CategoryTheory CategoryTheory.Limits

namespace Specs.CommutativeAlgebraNotes.TwoDegreeDualizingComplexExample

universe u

open TwoDegreeExampleCechCalculation
open TwoDegreeExampleDualizingCalculation (XQuotient toXQuotient xQuotientModule coefficientModule)
open RegularCoverDualizingModel (ShiftedRingResolution dualizingComplex)

/-- The local and dualizing cohomology of the same quotient of `k[[x,y]]`.
The isomorphism with one-variable power series identifies the two quotient actions.
The dualizing calculation holds for every bounded injective model of `S[2]`,
and such a model exists. -/
def Cohomology : Prop :=
  ∀ (k : Type u) [Field k],
    (∀ r : R k, r ∈ IdealTorsion.idealTorsion (IsLocalRing.maximalIdeal (R k)) (R k) ↔
      ∃ c : k, r = c • x k) ∧
    (∃ e : XQuotient k ≃+* A k, ∀ r : R k, e (toXQuotient k r) = project k r) ∧
    Nonempty (cohomology k 0 ≅ ModuleCat.of (R k) (xLine k)) ∧
    Nonempty (cohomology k 1 ≅ ModuleCat.of (R k) (L k ⧸ powerSeriesInLaurent k)) ∧
    Nonempty (ShiftedRingResolution (S k) 2) ∧
    ∀ J₀ : ShiftedRingResolution (S k) 2,
      let D := dualizingComplex (Ideal.Quotient.mk (J k)) J₀.complex
      Nonempty (D.homology (-1) ≅ xQuotientModule k) ∧
      Nonempty (D.homology 0 ≅ coefficientModule k) ∧
      ∀ q : ℤ, q ≠ -1 → q ≠ 0 → IsZero (D.homology q)

end Specs.CommutativeAlgebraNotes.TwoDegreeDualizingComplexExample
