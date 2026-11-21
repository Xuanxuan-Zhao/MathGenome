import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.LinearityOrder
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import MathGenome.Internal.RealAnalysis.D11.Ch05.AlgebraNull

/-! Linearity, order and absolute-value bound (paper.tex:1806–1838).
The upstream scalar-integral bridge identifies the paper's construction
with the Bochner integral on actually measurable, absolutely integrable
scalar functions. We retain those hypotheses when applying library results.
The nonnegative-integral bridge identifies the absolute integral exactly.
-/

open MeasureTheory
open scoped ENNReal
universe u
noncomputable section

namespace D11.Ch06.LinearityOrder

open ScalarIntegral
open D11.Ch04.AeCommonException
open D11.Ch05.NonnegativeIntegral

theorem linearity : Specs.D11.Ch06.LinearityOrder.linearity := by
  intro X 𝕜 _ _ _ _ μ f g a b hf hg
  have hfi := (scalarIntegrable_iff μ f).mp hf
  have hgi := (scalarIntegrable_iff μ g).mp hg
  have hab : scalarIntegrable μ (fun x => a * f x + b * g x) :=
    (scalarIntegrable_iff μ _).mpr
      ⟨(measurable_const.mul hfi.1).add (measurable_const.mul hgi.1),
        (hfi.2.const_mul a).add (hgi.2.const_mul b)⟩
  refine ⟨hab, ?_⟩
  change (∫ x, a * f x + b * g x ∂μ) =
    a * (∫ x, f x ∂μ) + b * (∫ x, g x ∂μ)
  rw [integral_add (hfi.2.const_mul a) (hgi.2.const_mul b),
    integral_const_mul, integral_const_mul]

theorem monotonicity : Specs.D11.Ch06.LinearityOrder.monotonicity := by
  intro X _ μ f g hf hg hfg
  change (∫ x, f x ∂μ) ≤ (∫ x, g x ∂μ)
  exact integral_mono_ae ((scalarIntegrable_iff μ f).mp hf).2
    ((scalarIntegrable_iff μ g).mp hg).2
    ((almostEverywhere_iff_native μ _).mp hfg)

theorem absolute_value_bound : Specs.D11.Ch06.LinearityOrder.absolute_value_bound := by
  intro X 𝕜 _ _ _ _ μ f hf
  change ‖(∫ x, f x ∂μ)‖ ≤
    (nonnegativeIntegral μ (fun x => ENNReal.ofReal ‖f x‖)).toReal
  rw [integral_eq_lintegral]
  exact norm_integral_le_lintegral_norm f

end D11.Ch06.LinearityOrder
