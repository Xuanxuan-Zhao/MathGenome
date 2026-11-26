import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.DimensionConventions
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse

open scoped TensorProduct
open IsLocalRing
open P103.Specs.Ch06.DimensionConventions (moduleDimensionValue)

namespace CommutativeAlgebraNotes.Intersection.UnramifiedPrimeQuotientIntersection.Specs

open IsolatedIntersectionEuler.Specs (intersectionEuler)

universe u

/-- The dimension bound, vanishing, and positivity for isolated intersections
of prime quotients of a power-series ring over a complete DVR with uniformizer `p`. -/
def primeQuotientIntersectionType : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] [CharZero V]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField V) p],
    Irreducible (p : V) → ∀ (a : ℕ),
      let R := MvPowerSeries (Fin a) V
      let d : WithBot ℕ∞ := ((a + 1 : ℕ) : WithBot ℕ∞)
      ∃ hreg : IsRegularLocalRing R,
        letI := hreg
        ringKrullDim R = d ∧
        (p : R) ∉ maximalIdeal R ^ 2 ∧
        ∀ (P Q : Ideal R) [P.IsPrime] [Q.IsPrime],
          let M := ModuleCat.of R (R ⧸ P)
          let N := ModuleCat.of R (R ⧸ Q)
          IsFiniteLength R (M ⊗[R] N) →
            let s := moduleDimensionValue R M + moduleDimensionValue R N
            s ≤ d ∧
              (s < d → intersectionEuler M N = 0) ∧
              (s = d → 0 < intersectionEuler M N)

end CommutativeAlgebraNotes.Intersection.UnramifiedPrimeQuotientIntersection.Specs
