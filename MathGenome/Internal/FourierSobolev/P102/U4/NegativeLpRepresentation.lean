import MathGenome.Internal.FourierSobolev.Specs.P102.U4.NegativeLpRepresentation
import MathGenome.Internal.RealAnalysis.D11.Ch20.LpDualSigmafiniteLocal

/-! Scalar dual representation for the canonical DomainLp spaces.
MathGenome's sigma-finite duality theorem uses native Mathlib Lp and the
scalar-linear integral of the product, with no complex conjugation.
Restricted Euclidean Lebesgue measure is sigma-finite, including for empty
domains and in dimension zero. No finite-measure hypothesis is introduced.
-/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal

namespace P102.U4

/-- Every scalar-linear continuous Lp functional has a bilinear Lq density. -/
theorem negative_lp_representation_integral :
    NegativeLpRepresentationExpected.IntegralRepresentation := by
  intro d 𝕜 _ Ω p _ _ hp g
  let : Fact (1 ≤ ENNReal.conjExponent p) :=
    ⟨by simp only [ENNReal.conjExponent]; exact le_self_add⟩
  obtain ⟨a, ha, _⟩ := D11.Ch20.LpDualSigmafiniteLocal.sigmaFinite_duality
    (volume.restrict (Ω : Set (Space d))) p (ENNReal.conjExponent p) hp g
  refine ⟨a, fun v => ?_⟩
  exact (ha.1 v).2.trans (integral_congr_ae (Filter.Eventually.of_forall
    (fun x => mul_comm (v x) (a x))))

/-- Bundled form for assembling the negative Sobolev representation. -/
theorem negative_lp_representation_pairing :
    NegativeLpRepresentationExpected.PairingRepresentation := by
  intro d 𝕜 _ Ω p _ hp1 hp g
  let : Fact (1 ≤ ENNReal.conjExponent p) :=
    ⟨by simp only [ENNReal.conjExponent]; exact le_self_add⟩
  obtain ⟨a, ha⟩ := negative_lp_representation_integral Ω p hp1 hp g
  refine ⟨a, fun v => ?_⟩
  rw [ContinuousLinearMap.lpPairing_eq_integral, ha v]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x => mul_comm (a x) (v x)))

end P102.U4
