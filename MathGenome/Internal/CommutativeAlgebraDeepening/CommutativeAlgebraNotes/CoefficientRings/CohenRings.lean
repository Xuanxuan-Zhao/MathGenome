import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoefficientRings.CohenRings
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CohenRingExistence
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CohenRingTruncationSmoothness

namespace CommutativeAlgebraNotes.CoefficientRings

/-- A Cohen ring with prescribed residue field and formally smooth positive truncations. -/
theorem cohenRingWithSmoothTruncations :
    _root_.Specs.CommutativeAlgebraNotes.CoefficientRings.cohenRingWithSmoothTruncations := by
  intro p hp k _ _
  obtain ⟨Λ, hRing, hDomain, hDVR, hCharZero, hComplete, hUniformizer, hResidue⟩ :=
    cohenRingExistence p hp k
  let : Fact p.Prime := ⟨hp⟩
  let : CommRing Λ := hRing
  let : IsDomain Λ := hDomain
  let : IsDiscreteValuationRing Λ := hDVR
  let : IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ := hComplete
  exact ⟨Λ, hRing, hDomain, hDVR, hCharZero, hComplete, hUniformizer, hResidue,
    cohenRingTruncationSmoothness Λ p hUniformizer.symm⟩

end CommutativeAlgebraNotes.CoefficientRings
