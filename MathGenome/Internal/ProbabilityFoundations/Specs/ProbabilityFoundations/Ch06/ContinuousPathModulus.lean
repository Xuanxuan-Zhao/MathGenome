import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.ContinuousPathGeometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Independent statements for the modulus of continuity in §6.11.
The state norm is the Euclidean norm, including the one-point case `d = 0`.
The metric and norm on continuous maps are the canonical uniform ones. -/

open Filter Topology TopologicalSpace

namespace ProbabilityFoundations.Ch06.Specs

abbrev Path (T : ℝ) (d : ℕ) := C(Set.Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin d))

def increments {T : ℝ} {d : ℕ} (x : Path T d) (δ : ℝ) : Set ℝ :=
  {r | ∃ s t : Set.Icc (0 : ℝ) T, |(s : ℝ) - (t : ℝ)| ≤ δ ∧
    r = ‖x s - x t‖}

noncomputable def modulus {T : ℝ} {d : ℕ} (x : Path T d) (δ : ℝ) : ℝ :=
  sSup (increments x δ)

def PathModulus := {T : ℝ} → {d : ℕ} → Path T d → ℝ → ℝ

noncomputable def PathModulusValue : PathModulus := @modulus

def ModulusFinite : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ (d : ℕ) (x : Path T d) (δ : ℝ), 0 ≤ δ →
    BddAbove (increments x δ) ∧ 0 ≤ modulus x δ ∧ modulus x δ ≤ 2 * ‖x‖ ∧
    ∀ s t : Set.Icc (0 : ℝ) T, |(s : ℝ) - (t : ℝ)| ≤ δ →
      ‖x s - x t‖ ≤ modulus x δ

def ModulusLipschitz : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ (d : ℕ) (δ : ℝ), 0 ≤ δ →
    ∀ x y : Path T d, |modulus x δ - modulus y δ| ≤ 2 * ‖x - y‖

def ModulusContinuous : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ (d : ℕ) (δ : ℝ), 0 ≤ δ →
    LipschitzWith 2 (fun x : Path T d => modulus x δ)

def ModulusEvents : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ (d : ℕ) (δ : ℝ), 0 ≤ δ → ∀ η : ℝ,
    @MeasurableSet (Path T d) (borel (Path T d)) {x | η < modulus x δ} ∧
      IsClosed {x : Path T d | modulus x δ ≤ η}

def ModulusTendstoZero : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ (d : ℕ) (x : Path T d),
    Tendsto (modulus x) (𝓝[>] (0 : ℝ)) (𝓝 0)

def ZeroDimensionalModulus : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ (x : Path T 0) (δ : ℝ), 0 ≤ δ → modulus x δ = 0

def PathSpaceGeometry : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ d : ℕ,
    SeparableSpace (Path T d) ∧ CompleteSpace (Path T d)

end ProbabilityFoundations.Ch06.Specs
