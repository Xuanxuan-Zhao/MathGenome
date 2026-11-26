import Mathlib.RingTheory.Valuation.ValuationRing

universe u v

namespace Specs.CommutativeAlgebraNotes

/-- Proposition 5.15, with each of the three tests characterizing a valuation ring. -/
def intrinsicValuationTestsType : Prop :=
  ∀ (V : Type u) (K : Type v) [CommRing V] [IsDomain V] [Field K]
    [Algebra V K] [IsFractionRing V K],
    (ValuationRing V ↔ ∀ x : K, x ≠ 0 →
      x ∈ (algebraMap V K).range ∨ x⁻¹ ∈ (algebraMap V K).range) ∧
    (ValuationRing V ↔ ∀ I J : Ideal V, I ≤ J ∨ J ≤ I) ∧
    (ValuationRing V ↔ IsLocalRing V ∧ ∀ I : Ideal V, I.FG → I.IsPrincipal)

end Specs.CommutativeAlgebraNotes
