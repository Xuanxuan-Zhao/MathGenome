import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.IntegralDetection
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! Detection by integrals on measurable sets (paper.tex:1994–2011).

The scalar-integrability bridge supplies native integrability, which also
supplies integrability on every restriction used below. Mathlib's detection
lemmas work for arbitrary measures and only need the integral hypothesis on
finite-measure measurable sets; the paper's hypothesis supplies these tests.
The a.e. bridges return a measurable null envelope in the original space.
-/

open MeasureTheory

universe u
noncomputable section

namespace D11.Ch06.IntegralDetection

open ScalarIntegral
open D11.Ch04.AeCommonException

theorem nonnegative_detection :
    Specs.D11.Ch06.IntegralDetection.nonnegative_detection := by
  intro X _ μ f hf hsets
  have hfi : Integrable f μ := ((scalarIntegrable_iff μ f).mp hf).2
  apply (almostEverywhere_iff_native μ (fun x => 0 ≤ f x)).mpr
  exact ae_nonneg_of_forall_setIntegral_nonneg hfi (fun E hE _ => hsets E hE)

theorem equality_detection :
    Specs.D11.Ch06.IntegralDetection.equality_detection := by
  intro X 𝕜 _ _ _ _ μ f g hf hg hsets
  have hfi : Integrable f μ := ((scalarIntegrable_iff μ f).mp hf).2
  have hgi : Integrable g μ := ((scalarIntegrable_iff μ g).mp hg).2
  apply (aeEq_iff_native μ f g).mpr
  exact Integrable.ae_eq_of_forall_setIntegral_eq f g hfi hgi
    (fun E hE _ => hsets E hE)

end D11.Ch06.IntegralDetection
