import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.ElementaryIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.GeneratedRingAlgebra
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Independent statement of paper.tex:6274–6286. The measures are on A_V,
and equality is required precisely on R_V. Integrability is absolute
integrability of the actual real functions, with no unit or mass assumption. -/

open Set MeasureTheory
universe u

namespace Specs.D11.Ch23.LocalizedSigmaRingUniqueness

open _root_.D11.Ch23.Specs

def localized_sigma_ring_uniqueness : Prop :=
  ∀ {X : Type u} (V : Submodule ℝ (X → ℝ)),
    IsVectorLattice V → IsStone V →
    ∀ L : V →ₗ[ℝ] ℝ, IsElementaryIntegral V L →
    letI : MeasurableSpace X := positiveLevelMeasurableSpace V
    ∀ μ ν : Measure X,
      (∀ f : V, Integrable (f : X → ℝ) μ ∧ ∫ x, (f : X → ℝ) x ∂μ = L f) →
      (∀ f : V, Integrable (f : X → ℝ) ν ∧ ∫ x, (f : X → ℝ) x ∂ν = L f) →
      ∀ A : Set X, A ∈ positiveLevelSigmaRing V → μ A = ν A

end Specs.D11.Ch23.LocalizedSigmaRingUniqueness
