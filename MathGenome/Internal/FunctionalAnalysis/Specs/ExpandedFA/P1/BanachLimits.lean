import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Order.LiminfLimsup

/-! Independent specification of the Banach-limit corollary,
`paper.tex:5313–5336`. Natural coordinate `n` is manuscript coordinate `n+1`.
The averages at positive `n` use the first `n` coordinates; the value at zero
is zero and has no effect on convergence. -/

noncomputable section
open Filter
open scoped Topology ENNReal

namespace ExpandedFA.P1.BanachLimits
open C01SequenceSpaces

/-- The actual left shift of the canonical bounded real sequence space. -/
def leftShift : SequenceLInfinity ℝ →ₗ[ℝ] SequenceLInfinity ℝ where
  toFun x := ⟨fun n => x (n + 1), memℓp_infty
    ⟨‖x‖, by rintro _ ⟨n, rfl⟩; exact lp.norm_apply_le_norm ENNReal.top_ne_zero x _⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The ordinary Cesàro means, with the harmless zero-th average set to zero. -/
def cesaroMean (x : SequenceLInfinity ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, x j

namespace Spec

/-- All asserted properties hold simultaneously for the chosen functional,
including agreement with *every* convergent Cesàro mean. Representation means
the usual coordinate pairing with an actual element of canonical `ℓ¹`. -/
def BanachLimitsType : Prop :=
  ∃ L : SequenceLInfinity ℝ →L[ℝ] ℝ,
    (∀ x, (∀ n, 0 ≤ x n) → 0 ≤ L x) ∧
    ‖L‖ = 1 ∧
    (∀ (x : SequenceLInfinity ℝ) (a : ℝ),
      Tendsto (fun n => x n) atTop (𝓝 a) → L x = a) ∧
    (∀ x, L (leftShift x) = L x) ∧
    (∀ x, liminf (fun n => x n) atTop ≤ L x ∧
      L x ≤ limsup (fun n => x n) atTop) ∧
    (∀ (x : SequenceLInfinity ℝ) (a : ℝ),
      Tendsto (cesaroMean x) atTop (𝓝 a) → L x = a) ∧
    ¬ ∃ a : SequenceLp ℝ 1, ∀ x : SequenceLInfinity ℝ,
      L x = ∑' n, a n * x n

end Spec
end ExpandedFA.P1.BanachLimits
