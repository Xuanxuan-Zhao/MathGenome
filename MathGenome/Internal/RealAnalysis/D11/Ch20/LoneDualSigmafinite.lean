import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.LoneDualSigmafinite
import MathGenome.Internal.RealAnalysis.D11.Ch20.LpDualSigmafiniteLocal

/-! The p = 1 specialization of sigma-finite scalar duality, packaged as
a linear isometric equivalence. It applies to real and complex scalars,
including zero measures and empty underlying spaces. -/
open MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace D11.Ch20.LoneDualSigmafinite

theorem lone_dual_sigmafinite :
    Specs.D11.Ch20.LoneDualSigmafinite.lone_dual_sigmafinite := by
  intro X 𝕜 _ _ μ _
  let J : Lp 𝕜 ∞ μ →ₗᵢ[𝕜] (Lp 𝕜 1 μ →L[𝕜] 𝕜) :=
    { (IntegralPairing.pairing μ 1 ∞).toLinearMap with
      norm_map' := LpDualSigmafiniteLocal.pairing_norm μ 1 ∞ }
  have hJ : Function.Surjective J := by
    intro ℓ
    obtain ⟨g, hg, _⟩ := LpDualSigmafiniteLocal.sigmaFinite_duality
      μ 1 ∞ (by simp) ℓ
    refine ⟨g, ?_⟩
    ext f
    exact (IntegralPairing.pairing_eq_integral μ 1 ∞ g f).2.trans
      ((hg.1 f).2.symm)
  refine ⟨LinearIsometryEquiv.ofSurjective J hJ, ?_⟩
  intro g f
  exact IntegralPairing.pairing_eq_integral μ 1 ∞ g f

end D11.Ch20.LoneDualSigmafinite
