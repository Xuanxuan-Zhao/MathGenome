import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Lattice.Fold

open scoped Topology
open Filter

namespace NumAnalysis206.Evolution

/-- The maximum of errors on the finite mesh `0 ≤ n*h ≤ T`, for `T ≥ 0`, `h > 0`.
The accompanying maximum characterization makes the admissible indices explicit. -/
noncomputable def meshErrorMax (T h : ℝ) (e : ℕ → ℝ) : ℝ :=
  (Finset.range (⌊T / h⌋₊ + 1)).sup'
    (by exact ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩) e

end NumAnalysis206.Evolution

namespace Specs.NumAnalysis206.Evolution

/-- p206:W17: nonuniform local defects, including zero steps and `L = 0`. -/
def WeightedPropagation : Prop :=
  ∀ (T h L : ℝ) (e τ : ℕ → ℝ),
    0 < T → 0 < h → 0 ≤ L →
    (∀ j, 0 ≤ e j) → (∀ j, 0 ≤ τ j) →
    (∀ j : ℕ, (j + 1 : ℕ) * h ≤ T → e (j + 1) ≤ (1 + L * h) * e j + h * τ j) →
    ∀ n : ℕ, (n : ℝ) * h ≤ T →
      e n ≤ (1 + L * h) ^ n * e 0 +
        ∑ j ∈ Finset.range n, h * (1 + L * h) ^ (n - 1 - j) * τ j

/-- p206:W17: the stated finite-horizon exponential estimate. -/
def UniformPropagation : Prop :=
  ∀ (T h L τ : ℝ) (e : ℕ → ℝ),
    0 < T → 0 < h → 0 ≤ L → 0 ≤ τ → (∀ j, 0 ≤ e j) →
    (∀ j : ℕ, (j + 1 : ℕ) * h ≤ T → e (j + 1) ≤ (1 + L * h) * e j + h * τ) →
    ∀ n : ℕ, (n : ℝ) * h ≤ T →
      e n ≤ Real.exp (L * T) * e 0 + T * Real.exp (L * T) * τ

/-- The finite maximum represents exactly the mesh times in the original statement. -/
def MeshMaximumCharacterization : Prop :=
  ∀ (T h : ℝ) (e : ℕ → ℝ), 0 < T → 0 < h →
    IsGreatest {v : ℝ | ∃ n : ℕ, (n : ℝ) * h ≤ T ∧ e n = v}
      (_root_.NumAnalysis206.Evolution.meshErrorMax T h e)

/-- The same quantitative estimate holds for the maximum. -/
def MeshMaximumBound : Prop :=
  ∀ (T h L τ : ℝ) (e : ℕ → ℝ),
    0 < T → 0 < h → 0 ≤ L → 0 ≤ τ → (∀ j, 0 ≤ e j) →
    (∀ j : ℕ, (j + 1 : ℕ) * h ≤ T → e (j + 1) ≤ (1 + L * h) * e j + h * τ) →
    _root_.NumAnalysis206.Evolution.meshErrorMax T h e ≤
      Real.exp (L * T) * e 0 + T * Real.exp (L * T) * τ

/-- p206:W17: mesh-uniform convergence as the positive step size tends to zero. -/
def MeshMaximumConvergence : Prop :=
  ∀ (T L : ℝ) (e : ℝ → ℕ → ℝ) (τ : ℝ → ℝ),
    0 < T → 0 ≤ L →
    (∀ h : ℝ, 0 < h → ∀ j, 0 ≤ e h j) →
    (∀ h : ℝ, 0 < h → 0 ≤ τ h) →
    (∀ h : ℝ, 0 < h → ∀ j : ℕ, (j + 1 : ℕ) * h ≤ T →
      e h (j + 1) ≤ (1 + L * h) * e h j + h * τ h) →
    Tendsto (fun h => e h 0) (𝓝[>] 0) (𝓝 0) →
    Tendsto τ (𝓝[>] 0) (𝓝 0) →
    Tendsto (fun h => _root_.NumAnalysis206.Evolution.meshErrorMax T h (e h))
      (𝓝[>] 0) (𝓝 0)

end Specs.NumAnalysis206.Evolution
