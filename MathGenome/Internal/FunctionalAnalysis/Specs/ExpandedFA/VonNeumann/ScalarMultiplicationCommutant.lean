import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.Holder

/-! The scalar multiplication commutant calculation in the proof of
`fa2:p2:abelian-von-neumann`. Both real and complex scalars are covered. No topology on the
measure space, countable generation of its sigma algebra, or separability of L² is assumed. -/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ExpandedFA.VonNeumann.ScalarMultiplicationCommutant.Spec
universe v u
variable {𝕜 : Type v} [RCLike 𝕜]

/-- The ordinary pointwise multiplication operator, with an L∞ coefficient. -/
def multiplier {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (h : Lp 𝕜 ∞ μ) : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ :=
  (ContinuousLinearMap.mul 𝕜 𝕜).holderL μ ∞ 2 2 h

/-- Commutation with every essentially bounded scalar multiplication. -/
def CommutesWithMultipliers {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (T : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ) : Prop :=
  ∀ h : Lp 𝕜 ∞ μ, T.comp (multiplier μ h) = (multiplier μ h).comp T

/-- Finite positive measures, including the zero measure. Coefficients are
unique as L∞ equivalence classes, and the norm is the essential supremum. -/
def FiniteCommutant : Prop :=
  ∀ (𝕜 : Type v) [RCLike 𝕜] (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (T : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ), CommutesWithMultipliers μ T →
    ∃! h : Lp 𝕜 ∞ μ, T = multiplier μ h ∧ ‖T‖ = ‖h‖

/-- The same full conclusion for sigma-finite measures. -/
def SigmaFiniteCommutant : Prop :=
  ∀ (𝕜 : Type v) [RCLike 𝕜] (X : Type u) [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (T : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ), CommutesWithMultipliers μ T →
    ∃! h : Lp 𝕜 ∞ μ, T = multiplier μ h ∧ ‖T‖ = ‖h‖

/-- Every multiplication belongs to the commutant, with its exact norm. -/
def MultiplicationProperties : Prop :=
  ∀ (𝕜 : Type v) [RCLike 𝕜] (X : Type u) [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (h : Lp 𝕜 ∞ μ),
    CommutesWithMultipliers μ (multiplier μ h) ∧ ‖multiplier μ h‖ = ‖h‖

end ExpandedFA.VonNeumann.ScalarMultiplicationCommutant.Spec
