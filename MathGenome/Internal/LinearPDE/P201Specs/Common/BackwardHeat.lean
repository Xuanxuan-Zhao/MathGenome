import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.PeriodicHilbertScale
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.MetricSpace.Sequences

/-! The corrected backward heat example, paper.tex §C03.
The circle has period one and Haar mass one. Real-valued solutions are embedded
in complex L² and the complex Fourier Sobolev scale, with their usual real norms.
For a real function this embedding preserves every norm and distance in question.
No regularity, convergence, or instability assertion is assumed in these definitions.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Real ENNReal
namespace P201Specs.Common.BackwardHeat

abbrev UnitCircle := AddCircle (1 : ℝ)
abbrev L2 := MeasureTheory.Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))
abbrev RealL2 := MeasureTheory.Lp ℝ 2 (AddCircle.haarAddCircle (T := 1))

/-- Canonical inclusion of real L² into complex L². -/
def complexify : RealL2 →L[ℝ] L2 :=
  Complex.ofRealCLM.compLpL 2 AddCircle.haarAddCircle

abbrev PeriodicHs := ExpandedFA.Sobolev.PeriodicHilbertScale.Hs
abbrev Solution := ℝ → UnitCircle → ℝ

/-- The positive eigenvalue of minus the Laplacian in the period-one coordinate. -/
def eigenvalue (j : ℕ) : ℝ := 4 * π ^ 2 * (j : ℝ) ^ 2

def cosine (j : ℕ) (q : UnitCircle) : ℝ := (fourier (j : ℤ) q).re

def solution (T : ℝ) (j : ℕ) : Solution :=
  fun t q => Real.exp (-eigenvalue j * (T - t)) * cosine j q

def terminal (j : ℕ) : L2 :=
  (1 / 2 : ℂ) • (fourierLp 2 (j : ℤ) + fourierLp 2 (-(j : ℤ)))

def realTerminal (j : ℕ) : RealL2 :=
  Complex.reCLM.compLpL 2 AddCircle.haarAddCircle (terminal j)

/-- The actual cosine coefficient sequence in the full periodic H^s norm.
Normalization is the library isometry multiplying coefficient n by
(1+4π²n²)^(s/2). -/
def cosineHs (s : ℝ) (j : ℕ) : PeriodicHs s :=
  (ExpandedFA.Sobolev.PeriodicHilbertScale.weight s (j : ℤ) : ℂ) •
    (ExpandedFA.Sobolev.PeriodicHilbertScale.normalizedEquiv s).symm
      ((1 / 2 : ℂ) • (lp.single 2 (j : ℤ) 1 + lp.single 2 (-(j : ℤ)) 1))

def initial (s T : ℝ) (j : ℕ) : PeriodicHs s :=
  (Real.exp (-eigenvalue j * T) : ℂ) • cosineHs s j

/-- Initial data are identified by all actual Fourier coefficients. -/
def HasInitial (s : ℝ) (u : Solution) (a : PeriodicHs s) : Prop :=
  ∀ n : ℤ, a n = fourierCoeff (fun q => (u 0 q : ℂ)) n

/-- The initial-data set of precisely the chosen solution class in H^s. -/
def dataSet (s : ℝ) (S : Set Solution) : Set (PeriodicHs s) :=
  {a | ∃ u ∈ S, HasInitial s u a}

/-- A well-defined terminal solution map for this class. No uniqueness theorem
for arbitrary backward solutions is built into this predicate. -/
def IsTerminalMap (s T : ℝ) (S : Set Solution)
    (F : ↥(dataSet s S) → L2) : Prop :=
  ∀ u ∈ S, ∀ a : ↥(dataSet s S), HasInitial s u a.val →
    (F a : UnitCircle → ℂ) =ᵐ[AddCircle.haarAddCircle] (fun q => (u T q : ℂ))

def FormulaStatement : Prop :=
  ∀ (T t x : ℝ) (j : ℕ),
    solution T j t (x : UnitCircle) =
      Real.exp (-4 * π ^ 2 * (j : ℝ) ^ 2 * (T - t)) * Real.cos (2 * π * j * x)

def SmoothPDEStatement : Prop :=
  ∀ (T : ℝ) (j : ℕ),
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => solution T j p.1 (p.2 : UnitCircle)) ∧
    ∀ t x : ℝ,
      deriv (fun r => solution T j r (x : UnitCircle)) t +
        deriv (deriv (fun y : ℝ => solution T j t (y : UnitCircle))) x = 0

def InitialStatement : Prop :=
  ∀ (s T : ℝ) (j : ℕ), HasInitial s (solution T j) (initial s T j)

def InitialConvergenceStatement : Prop :=
  ∀ (s T : ℝ), 0 < T →
    Tendsto (fun n : ℕ => initial s T (n + 1)) atTop (𝓝 0)

def TerminalStatement : Prop :=
  ∀ (T : ℝ) (j : ℕ),
    (terminal j : UnitCircle → ℂ) =ᵐ[AddCircle.haarAddCircle]
      (fun q => (solution T j T q : ℂ))

def TerminalNormStatement : Prop :=
  ∀ (j : ℕ), 1 ≤ j → ‖terminal j‖ = 1 / Real.sqrt 2

def TerminalSeparationStatement : Prop :=
  ∀ (j k : ℕ), 1 ≤ j → 1 ≤ k → j ≠ k →
    inner ℂ (terminal j) (terminal k) = 0 ∧ dist (terminal j) (terminal k) = 1

def NoTerminalLimitStatement : Prop :=
  ¬ ∃ b : L2, Tendsto (fun n : ℕ => terminal (n + 1)) atTop (𝓝 b)

/-- Arbitrary data sets and arbitrary values at zero: even continuity at that
single point is impossible. This also applies if zero already belongs to D. -/
def NoExtensionStatement : Prop :=
  ∀ (s T : ℝ), 0 < T → ∀ (D : Set (PeriodicHs s))
    (hD : ∀ j : ℕ, 1 ≤ j → initial s T j ∈ D)
    (F : ↥D → L2),
    (∀ (j : ℕ) (hj : 1 ≤ j), F ⟨initial s T j, hD j hj⟩ = terminal j) →
    ¬ ∃ E : ↥(insert (0 : PeriodicHs s) D) → L2,
      (∀ a : ↥D, E ⟨a.val, mem_insert_of_mem 0 a.property⟩ = F a) ∧
      ContinuousAt E ⟨0, mem_insert 0 D⟩

/-- Specialization to every real-valued solution class containing the displayed
solutions, with its actual Fourier initial-data set. -/
def ClassNoExtensionStatement : Prop :=
  ∀ (s T : ℝ), 0 < T → ∀ (S : Set Solution),
    (∀ j : ℕ, 1 ≤ j → solution T j ∈ S) →
    ∀ (F : ↥(dataSet s S) → L2), IsTerminalMap s T S F →
    ¬ ∃ E : ↥(insert (0 : PeriodicHs s) (dataSet s S)) → L2,
      (∀ a : ↥(dataSet s S), E ⟨a.val, mem_insert_of_mem 0 a.property⟩ = F a) ∧
      ContinuousAt E ⟨0, mem_insert 0 (dataSet s S)⟩

def ClassDiscontinuityStatement : Prop :=
  ∀ (s T : ℝ), 0 < T → ∀ (S : Set Solution),
    (∀ j : ℕ, 1 ≤ j → solution T j ∈ S) → (0 : Solution) ∈ S →
    ∀ (F : ↥(dataSet s S) → L2), IsTerminalMap s T S F →
    (0 : PeriodicHs s) ∈ dataSet s S ∧
    ∀ (hzero : (0 : PeriodicHs s) ∈ dataSet s S), ¬ ContinuousAt F ⟨0, hzero⟩

/-- The terminal norm and separation in the actual real L² space. -/
def RealTerminalStatement : Prop :=
  (∀ (T : ℝ) (j : ℕ),
    (realTerminal j : UnitCircle → ℝ) =ᵐ[AddCircle.haarAddCircle] solution T j T) ∧
  (∀ j : ℕ, 1 ≤ j → ‖realTerminal j‖ = 1 / Real.sqrt 2) ∧
  (∀ j k : ℕ, 1 ≤ j → 1 ≤ k → j ≠ k → dist (realTerminal j) (realTerminal k) = 1)

/-- The norm bridge for the real-valued interpretation of the example. -/
def ComplexificationStatement : Prop := ∀ f : RealL2, ‖complexify f‖ = ‖f‖

def IsRealTerminalMap (s T : ℝ) (S : Set Solution)
    (F : ↥(dataSet s S) → RealL2) : Prop :=
  ∀ u ∈ S, ∀ a : ↥(dataSet s S), HasInitial s u a.val →
    (F a : UnitCircle → ℝ) =ᵐ[AddCircle.haarAddCircle] u T

def RealClassNoExtensionStatement : Prop :=
  ∀ (s T : ℝ), 0 < T → ∀ (S : Set Solution),
    (∀ j : ℕ, 1 ≤ j → solution T j ∈ S) →
    ∀ (F : ↥(dataSet s S) → RealL2), IsRealTerminalMap s T S F →
    ¬ ∃ E : ↥(insert (0 : PeriodicHs s) (dataSet s S)) → RealL2,
      (∀ a : ↥(dataSet s S), E ⟨a.val, mem_insert_of_mem 0 a.property⟩ = F a) ∧
      ContinuousAt E ⟨0, mem_insert 0 (dataSet s S)⟩

def RealClassDiscontinuityStatement : Prop :=
  ∀ (s T : ℝ), 0 < T → ∀ (S : Set Solution),
    (∀ j : ℕ, 1 ≤ j → solution T j ∈ S) → (0 : Solution) ∈ S →
    ∀ (F : ↥(dataSet s S) → RealL2), IsRealTerminalMap s T S F →
    (0 : PeriodicHs s) ∈ dataSet s S ∧
    ∀ (hzero : (0 : PeriodicHs s) ∈ dataSet s S), ¬ ContinuousAt F ⟨0, hzero⟩

/-- Export types for the example's explicit constructions. -/
abbrev SolutionType := ℝ → ℕ → Solution
abbrev InitialType := (s T : ℝ) → ℕ → PeriodicHs s
abbrev TerminalType := ℕ → L2

end P201Specs.Common.BackwardHeat
