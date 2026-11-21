import MathGenome.Internal.LinearPDE.P201Specs.Heat.HeatBallMeanValue
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Independent specification of the cube-kernel construction in the proof of
`pde:heat-harnack`, paper.tex 2983–3020. The vector `a` translates the cube;
`m j + 1` enumerates precisely the strictly positive integer frequencies.
No convergence, initial-value or positivity certificate is assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace P201Specs.Heat.Cube

abbrev Mode (n : ℕ) := Fin n → ℕ
abbrev KernelPoint (n : ℕ) := Space n × Space n × ℝ

def cube {n : ℕ} (ℓ : ℝ) (a : Space n) : Set (Space n) :=
  {x | ∀ j, a j < x j ∧ x j < a j + ℓ}

def closedCube {n : ℕ} (ℓ : ℝ) (a : Space n) : Set (Space n) :=
  {x | ∀ j, a j ≤ x j ∧ x j ≤ a j + ℓ}

def innerCube {n : ℕ} (ℓ : ℝ) (a : Space n) (δ : ℝ) : Set (Space n) :=
  {x | ∀ j, a j + δ ≤ x j ∧ x j ≤ a j + ℓ - δ}

def sineMode {n : ℕ} (ℓ : ℝ) (a : Space n) (m : Mode n) (x : Space n) : ℝ :=
  ∏ j, Real.sin (((m j : ℝ) + 1) * Real.pi * (x j - a j) / ℓ)

def eigenvalue {n : ℕ} (ℓ : ℝ) (m : Mode n) : ℝ :=
  Real.pi ^ 2 / ℓ ^ 2 * ∑ j, ((m j : ℝ) + 1) ^ 2

def kernelTerm {n : ℕ} (ℓ : ℝ) (a : Space n) (m : Mode n)
    (z : KernelPoint n) : ℝ :=
  (2 / ℓ) ^ n * Real.exp (-eigenvalue ℓ m * z.2.2) *
    sineMode ℓ a m z.1 * sineMode ℓ a m z.2.1

def cubeKernel {n : ℕ} (ℓ : ℝ) (a : Space n) (τ : ℝ) (x y : Space n) : ℝ :=
  ∑' m : Mode n, kernelTerm ℓ a m (x, y, τ)

def kernelSlab {n : ℕ} (ℓ : ℝ) (a : Space n) (s t : ℝ) : Set (KernelPoint n) :=
  closedCube ℓ a ×ˢ closedCube ℓ a ×ˢ Icc s t

def kernelSolution {n : ℕ} (ℓ : ℝ) (a : Space n) (g : Space n → ℝ)
    (τ : ℝ) (x : Space n) : ℝ :=
  ∫ y in cube ℓ a, cubeKernel ℓ a τ x y * g y ∂spatialMeasure n

abbrev cubeType := {n : ℕ} → ℝ → Space n → Set (Space n)
abbrev innerCubeType := {n : ℕ} → ℝ → Space n → ℝ → Set (Space n)
abbrev sineModeType := {n : ℕ} → ℝ → Space n → Mode n → Space n → ℝ
abbrev eigenvalueType := {n : ℕ} → ℝ → Mode n → ℝ
abbrev kernelTermType := {n : ℕ} → ℝ → Space n → Mode n → KernelPoint n → ℝ
abbrev cubeKernelType := {n : ℕ} → ℝ → Space n → ℝ → Space n → Space n → ℝ
abbrev kernelSolutionType := {n : ℕ} → ℝ → Space n → (Space n → ℝ) → ℝ → Space n → ℝ

/-- Unconditional finite-subset summation, stronger than a chosen rectangular
ordering. The zeroth derivative includes the original series. -/
def kernelSeriesStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ ℓ : ℝ, 0 < ℓ → ∀ a : Space n,
  ∀ s t : ℝ, 0 < s → s ≤ t → ∀ k : ℕ,
    (∀ z ∈ kernelSlab ℓ a s t,
      Summable (fun m : Mode n => iteratedFDeriv ℝ k (kernelTerm ℓ a m) z)) ∧
    TendstoUniformlyOn
      (fun F : Finset (Mode n) => fun z =>
        ∑ m ∈ F, iteratedFDeriv ℝ k (kernelTerm ℓ a m) z)
      (fun z => ∑' m : Mode n, iteratedFDeriv ℝ k (kernelTerm ℓ a m) z)
      atTop (kernelSlab ℓ a s t)

def kernelSmoothStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ ℓ : ℝ, 0 < ℓ → ∀ a : Space n,
    ContDiffOn ℝ ∞ (fun z : KernelPoint n => cubeKernel ℓ a z.2.2 z.1 z.2.1)
      {z | 0 < z.2.2}

def kernelDerivativeStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ ℓ : ℝ, 0 < ℓ → ∀ a : Space n,
  ∀ (k : ℕ) (z : KernelPoint n), 0 < z.2.2 →
    iteratedFDeriv ℝ k (fun w : KernelPoint n => cubeKernel ℓ a w.2.2 w.1 w.2.1) z =
      ∑' m : Mode n, iteratedFDeriv ℝ k (kernelTerm ℓ a m) z

def kernelCaloricStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ ℓ : ℝ, 0 < ℓ → ∀ a y : Space n,
    IsClassicalCaloricOn (fun z : SpaceTime n => cubeKernel ℓ a z.2 z.1 y)
      (cube ℓ a ×ˢ Ioi 0)

def kernelBoundaryStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ ℓ : ℝ, 0 < ℓ → ∀ a : Space n,
  ∀ τ : ℝ, 0 < τ → ∀ x y : Space n,
    (x ∈ closedCube ℓ a \ cube ℓ a ∨ y ∈ closedCube ℓ a \ cube ℓ a) →
      cubeKernel ℓ a τ x y = 0

def kernelIntegralStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ ℓ : ℝ, 0 < ℓ → ∀ a : Space n,
  ∀ (g : Space n → ℝ), ContinuousOn g (closedCube ℓ a) →
  ∀ τ : ℝ, 0 < τ → ∀ x : Space n,
    Integrable (fun y => cubeKernel ℓ a τ x y * g y)
      ((spatialMeasure n).restrict (cube ℓ a))

/-- Smooth compactly supported functions in the open cube extend by zero to
exactly the ambient tests used here. Convergence is uniform up to every face. -/
def kernelInitialStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ ℓ : ℝ, 0 < ℓ → ∀ a : Space n,
  ∀ (g : Space n → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
    tsupport g ⊆ cube ℓ a →
    TendstoUniformlyOn (kernelSolution ℓ a g) g (𝓝[>] (0 : ℝ)) (closedCube ℓ a)

def kernelNonnegativeStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ ℓ : ℝ, 0 < ℓ → ∀ a : Space n,
  ∀ τ : ℝ, 0 < τ → ∀ x ∈ closedCube ℓ a, ∀ y ∈ closedCube ℓ a,
    0 ≤ cubeKernel ℓ a τ x y

def kernelPositiveStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ ℓ : ℝ, 0 < ℓ → ∀ a : Space n,
  ∀ τ : ℝ, 0 < τ → ∀ x ∈ cube ℓ a, ∀ y ∈ cube ℓ a,
    0 < cubeKernel ℓ a τ x y

/-- Arbitrary prescribed compact spatial sets inside the cube; this includes
inner cubes with any center and does not restrict them to be concentric. -/
def kernelLowerBoundStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ ℓ : ℝ, 0 < ℓ → ∀ a : Space n,
  ∀ Kx Ky : Set (Space n), IsCompact Kx → Kx ⊆ cube ℓ a →
    IsCompact Ky → Ky ⊆ cube ℓ a →
  ∀ s t : ℝ, 0 < s → s ≤ t → ∃ c : ℝ, 0 < c ∧
    ∀ τ ∈ Icc s t, ∀ x ∈ Kx, ∀ y ∈ Ky, c ≤ cubeKernel ℓ a τ x y

/-- Base convergence and continuity interfaces, also recorded separately so
checked portions of this unfinished construction can be inspected individually. -/
def kernelSummableStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ ℓ : ℝ, 0 < ℓ → ∀ a : Space n,
  ∀ τ : ℝ, 0 < τ → ∀ x y : Space n,
    Summable (fun m : Mode n => kernelTerm ℓ a m (x,y,τ))

def kernelUniformStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ ℓ : ℝ, 0 < ℓ → ∀ a : Space n,
  ∀ s t : ℝ, 0 < s → s ≤ t →
    TendstoUniformlyOn
      (fun F : Finset (Mode n) => fun z : KernelPoint n => ∑ m ∈ F, kernelTerm ℓ a m z)
      (fun z => cubeKernel ℓ a z.2.2 z.1 z.2.1) atTop (kernelSlab ℓ a s t)

def kernelContinuousStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ ℓ : ℝ, 0 < ℓ → ∀ a : Space n,
    ContinuousOn (fun z : KernelPoint n => cubeKernel ℓ a z.2.2 z.1 z.2.1)
      {z | 0 < z.2.2}

def kernelTimeSeriesStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ ℓ : ℝ, 0 < ℓ → ∀ a : Space n,
  ∀ s t : ℝ, 0 < s → s ≤ t → ∀ k : ℕ,
    TendstoUniformlyOn
      (fun F : Finset (Mode n) => fun z : KernelPoint n =>
        ∑ m ∈ F, iteratedDeriv k (fun τ => kernelTerm ℓ a m (z.1,z.2.1,τ)) z.2.2)
      (fun z => ∑' m : Mode n,
        iteratedDeriv k (fun τ => kernelTerm ℓ a m (z.1,z.2.1,τ)) z.2.2)
      atTop (kernelSlab ℓ a s t)

end P201Specs.Heat.Cube
