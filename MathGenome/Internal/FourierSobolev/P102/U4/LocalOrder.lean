import MathGenome.Internal.FourierSobolev.Specs.P102.U4.LocalOrder
import MathGenome.Internal.FourierSobolev.P102.U4.TestSpace

noncomputable section
open Set TopologicalSpace
open scoped ContDiff Distributions

namespace P102.U4

/-- The defining coordinate seminorms increase with the allowed derivative order. -/
theorem coordinateSupSeminorm_monotone {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (K : Compacts (Space d)) : Monotone (coordinateSupSeminorm 𝕜 K) := by
  intro m n hmn
  exact Finset.sup_mono (Finset.range_mono (Nat.add_le_add_right hmn 1))

/-- On a fixed support, continuity is equivalent to a bound by a single q_m. -/
theorem fixedSupport_localOrder {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (K : Compacts (Space d)) (S : FixedSupport d 𝕜 K →ₗ[𝕜] 𝕜) :
    Continuous S ↔ ∃ C : ℝ, 0 ≤ C ∧ ∃ m : ℕ,
      ∀ φ, ‖S φ‖ ≤ C * coordinateSupSeminorm 𝕜 K m φ := by
  classical
  have hp := coordinateStageTopology d 𝕜 K
  constructor
  · intro hS
    let q : Seminorm 𝕜 (FixedSupport d 𝕜 K) := (normSeminorm 𝕜 𝕜).comp S
    have hq : Continuous q := hS.norm
    obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous hp q hq
    refine ⟨C, C.coe_nonneg, s.sup id, fun φ => ?_⟩
    have hs : s.sup (coordinateSupSeminorm 𝕜 K) ≤
        coordinateSupSeminorm 𝕜 K (s.sup id) := by
      apply Finset.sup_le
      intro m hm
      exact coordinateSupSeminorm_monotone 𝕜 K (Finset.le_sup (f := id) hm)
    exact (hC φ).trans (mul_le_mul_of_nonneg_left (hs φ) C.coe_nonneg)
  · rintro ⟨C, hC, m, hbound⟩
    apply hp.continuous_normedSpace_rng 𝕜 S
    refine ⟨{m}, ⟨C, hC⟩, ?_⟩
    intro φ
    rw [Finset.sup_singleton]
    exact hbound φ

/-- A scalar-linear functional is a distribution precisely when its order is
finite on each compact support; the order may vary with the support. -/
theorem localOrder : Expected.LocalOrder := by
  intro d 𝕜 _ Ω T
  rw [finalTopology d 𝕜 Ω 𝕜 T]
  constructor
  · intro h K hK
    exact (fixedSupport_localOrder 𝕜 K
      (T.comp (stageInclusion 𝕜 hK).toLinearMap)).mp (h K hK)
  · intro h K hK
    exact (fixedSupport_localOrder 𝕜 K
      (T.comp (stageInclusion 𝕜 hK).toLinearMap)).mpr (h K hK)

end P102.U4
