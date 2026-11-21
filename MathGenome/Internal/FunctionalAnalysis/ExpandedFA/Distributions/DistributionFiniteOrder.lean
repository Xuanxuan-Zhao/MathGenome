import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.TestFunctionBoundedSets
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.DistributionFiniteOrder

open Set TopologicalSpace
open scoped Distributions NNReal

namespace ExpandedFA.Distributions

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}

/-- The displayed derivative seminorms increase with their order. -/
theorem stepSeminorm_monotone (K : Compacts (Domain d)) :
    Monotone (stepSeminorm 𝕜 K) := by
  intro m n hmn
  unfold stepSeminorm
  apply Finset.sup_le
  intro k hk
  apply Finset.sup_le
  intro a _
  exact coordinate_le_stepSeminorm K a
    ((Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans hmn)

/-- On a compact step, continuity of a linear functional is equivalent to
control by one of the increasing derivative seminorms. -/
theorem continuous_step_iff_finite_order (K : Compacts (Domain d))
    (v : Step 𝕜 K →ₗ[𝕜] 𝕜) :
    Continuous v ↔ ∃ C : ℝ, 0 ≤ C ∧ ∃ m : ℕ, ∀ φ : Step 𝕜 K,
      ‖v φ‖ ≤ C * stepSeminorm 𝕜 K m φ := by
  classical
  have hp := step_seminorm_topology 𝕜 d K
  constructor
  · intro hv
    let q := (normSeminorm 𝕜 𝕜).comp v
    have hq : Continuous q := hv.norm
    obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous hp q hq
    have hs : s.sup (stepSeminorm 𝕜 K) ≤ stepSeminorm 𝕜 K (s.sup id) := by
      apply Finset.sup_le
      intro m hm
      exact stepSeminorm_monotone K (Finset.le_sup (f := id) hm)
    refine ⟨C, C.coe_nonneg, s.sup id, fun φ => ?_⟩
    exact (hC φ).trans (mul_le_mul_of_nonneg_left (hs φ) C.coe_nonneg)
  · rintro ⟨C, hC, m, hm⟩
    apply hp.continuous_normedSpace_rng 𝕜 v
    refine ⟨{m}, ⟨C, hC⟩, ?_⟩
    rw [Finset.sup_singleton]
    exact hm

/-- Compactwise finite order characterizes distributions. No common order or
common constant over all compact supports is required. -/
theorem finite_order_criterion :
    Specs.ExpandedFA.Distributions.DistributionFiniteOrder.finiteOrderCriterionType := by
  intro 𝕜 _ d Ω u
  rw [TestFunction.continuous_iff_continuous_comp u]
  constructor
  · intro hu K hK
    exact (continuous_step_iff_finite_order K
      (u.comp (TestFunction.ofSupportedInCLM 𝕜 hK).toLinearMap)).mp (hu K hK)
  · intro hu K hK
    exact (continuous_step_iff_finite_order K
      (u.comp (TestFunction.ofSupportedInCLM 𝕜 hK).toLinearMap)).mpr (hu K hK)

end ExpandedFA.Distributions
