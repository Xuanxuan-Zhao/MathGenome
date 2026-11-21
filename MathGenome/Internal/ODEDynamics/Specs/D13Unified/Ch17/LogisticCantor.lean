import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.InverseBranchCoding
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.LogisticFixedPoints
import Mathlib.Analysis.Real.Sqrt

/-! Theorem `d13:17:logistic-cantor`. The invariant set in the final
statement is a subset of the real line with its induced metric. The map
on that set is explicitly identified with the given logistic polynomial. -/
noncomputable section
namespace Specs.D13Unified.Ch17.LogisticCantor
open Set Topology NNReal
open Specs.D13Unified.Ch17.ShiftSpaces
open Specs.D13Unified.Ch17.ChaosDefinitions
open Specs.D13Unified.Ch15.LogisticFixedPoints (logisticMap)

def branchZero (μ u : ℝ) : ℝ := (1 - Real.sqrt (1 - 4 * u / μ)) / 2
def branchOne (μ u : ℝ) : ℝ := (1 + Real.sqrt (1 - 4 * u / μ)) / 2
def contractionRate (μ : ℝ) : ℝ := 1 / Real.sqrt (μ * (μ - 4))
def branchType := ℝ → ℝ → ℝ
def contractionRateType := ℝ → ℝ

/-- Exact formulas, inverse identities, separation, injectivity, and the
quantitative common Lipschitz constant, on the entire closed unit interval. -/
def branch_propertiesStatement : Prop :=
  ∀ μ : ℝ, 5 ≤ μ → ∃ (b : Binary → Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1)
    (q : ℝ≥0),
    (q : ℝ) = contractionRate μ ∧ 0 < (q : ℝ) ∧
    (q : ℝ) ≤ 1 / Real.sqrt 5 ∧ (1 : ℝ) / Real.sqrt 5 < 1 ∧
    (∀ i u, (b i u : ℝ) = if i = 0 then branchZero μ u else branchOne μ u) ∧
    (∀ u, (b 0 u : ℝ) < 1 / 2 ∧ 1 / 2 < (b 1 u : ℝ)) ∧
    (∀ i u, logisticMap μ (b i u) = (u : ℝ)) ∧
    (∀ i, LipschitzWith q (b i)) ∧
    (∀ i, Function.Injective (b i)) ∧
    Disjoint (Set.range (b 0)) (Set.range (b 1))

/-- A nonempty compact invariant Cantor subset of [0,1], with its actual
logistic restriction conjugate to the full one-sided binary shift and chaotic.
No isolated points and total disconnectedness specify the Cantor assertion. -/
def logistic_cantorStatement : Prop :=
  ∀ μ : ℝ, 5 ≤ μ → ∃ Λ : Set ℝ,
    Λ.Nonempty ∧ Λ ⊆ Icc 0 1 ∧ IsCompact Λ ∧
    (∀ x : Λ, ∀ V ∈ 𝓝 x, ∃ y ∈ V, y ≠ x) ∧
    TotallyDisconnectedSpace Λ ∧
    logisticMap μ '' Λ = Λ ∧
    ∃ (f : Λ → Λ) (π : OneSided ≃ₜ Λ),
      (∀ x, (f x : ℝ) = logisticMap μ x) ∧
      Continuous f ∧ Function.Surjective f ∧
      (∀ s, f (π s) = π (shiftPlus s)) ∧ Chaotic f

def midpointStatement : Prop :=
  ∀ μ : ℝ, 5 ≤ μ → logisticMap μ (1 / 2) = μ / 4 ∧ 1 < μ / 4

def interval_not_invariantStatement : Prop :=
  ∀ μ : ℝ, 5 ≤ μ → ¬ logisticMap μ '' Icc (0 : ℝ) 1 ⊆ Icc 0 1

end Specs.D13Unified.Ch17.LogisticCantor
