import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.OrderContinuityNecessary
import MathGenome.Internal.RealAnalysis.D11.Ch23.ElementaryIntegral
import MathGenome.Internal.RealAnalysis.D11.Ch06.DominatedConvergence
import Mathlib.Topology.Order.MonotoneConvergence

/-! Necessity of the elementary-integral conditions, paper.tex:6296–6303.
The representing map is initially arbitrary. All integral applications below
retain the original measurable and absolute-integrability hypotheses. -/

universe u

open Filter MeasureTheory
open scoped Topology

namespace D11.Ch23.OrderContinuityNecessary

open D11.Ch06.ScalarIntegral
open D11.Ch04.AeCommonException

/-- Integral representation implies real linearity, positivity, and
continuity from above at zero, including on the empty domain. -/
theorem order_continuity_necessary :
    _root_.Specs.D11.Ch23.OrderContinuityNecessary.order_continuity_necessary := by
  intro X _ V _hV μ L hint hrep
  have hi (f : V) : Integrable (f : X → ℝ) μ :=
    ((scalarIntegrable_iff μ (f : X → ℝ)).mp (hint f)).2
  have hrepNative (f : V) : L f = ∫ x, (f : X → ℝ) x ∂μ := hrep f
  -- The linear structure is proved from the representation, not assumed of L.
  let A : V →ₗ[ℝ] ℝ :=
    { toFun := L
      map_add' := by
        intro f g
        rw [hrepNative (f + g), hrepNative f, hrepNative g]
        exact integral_add (hi f) (hi g)
      map_smul' := by
        intro a f
        rw [hrepNative (a • f), hrepNative f]
        change (∫ x, a * (f : X → ℝ) x ∂μ) = a * ∫ x, (f : X → ℝ) x ∂μ
        exact integral_const_mul a _ }
  refine ⟨A, fun _ => rfl, ?_, ?_⟩
  · intro f hf
    change 0 ≤ L f
    rw [hrepNative f]
    exact integral_nonneg hf
  · intro f hanti hlim
    change Tendsto (fun n => L (f n)) atTop (𝓝 0)
    -- Each decreasing real sequence with limit zero lies above zero.
    have hnonneg (n : ℕ) (x : X) : 0 ≤ (f n : X → ℝ) x :=
      (hanti x).le_of_tendsto (hlim x) n
    have hbound (n : ℕ) :
        almostEverywhere μ (fun x => ‖(f n : X → ℝ) x‖ ≤ (f 0 : X → ℝ) x) :=
      almostEverywhere_of_forall μ _ (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg n x)]
        exact hanti x (Nat.zero_le n))
    obtain ⟨_, _, _, _, hconv⟩ :=
      D11.Ch06.DominatedConvergence.dominated_convergence μ
        (fun n => (f n : X → ℝ)) (fun _ => (0 : ℝ)) (f 0 : X → ℝ)
        (fun n => (hint (f n)).1) measurable_const (hint (f 0)) (hnonneg 0)
        hbound (almostEverywhere_of_forall μ _ hlim)
    simp only [hrepNative]
    simpa only [_root_.Specs.D11.Ch06.ScalarIntegral.scalarIntegral_value,
      integral_zero] using hconv

end D11.Ch23.OrderContinuityNecessary
