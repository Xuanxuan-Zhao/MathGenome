import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.Exponential
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-!
Independent interface for the finite analytic circular arc assertion in
paper.tex:2660–2669. No connectedness or nonemptiness of the disk union is
assumed. All geometry below is stated by primitive formulas and imports no
pending exhaustion or boundary chart implementation.
-/

noncomputable section
open Set Metric
open scoped Topology

namespace D12Complex.FiniteCircularArcs

/-- The open union, indexed by its finite set of distinct centers. -/
def diskUnion (s : Finset ℂ) (r : ℂ → ℝ) : Set ℂ :=
  ⋃ c ∈ s, Metric.ball c (r c)

/-- Exactly the radius, non-tangency, and no-triple-point hypotheses. -/
def Arrangement (s : Finset ℂ) (r : ℂ → ℝ) : Prop :=
  (∀ c ∈ s, 0 < r c) ∧
  (∀ c ∈ s, ∀ d ∈ s, c ≠ d →
    dist c d ≠ r c + r d ∧ dist c d ≠ |r c - r d|) ∧
  (∀ c ∈ s, ∀ d ∈ s, ∀ e ∈ s, c ≠ d → c ≠ e → d ≠ e →
    ¬ ∃ z : ℂ, dist z c = r c ∧ dist z d = r d ∧ dist z e = r e)

/-- Actual finite closed-arc equality, with regularity in open neighborhoods
of the entire closed parameter intervals. Full circles are allowed. -/
def Decomposition (D : Set ℂ) : Prop :=
  ∃ (n : ℕ) (c : Fin n → ℂ) (R a b : Fin n → ℝ),
    (∀ i, 0 < R i ∧ a i < b i ∧ b i - a i ≤ 2 * Real.pi) ∧
    frontier D = ⋃ i : Fin n,
      (fun t : ℝ => c i + (R i : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) ''
        Set.Icc (a i) (b i) ∧
    ∀ i, (∃ U : Set ℝ, IsOpen U ∧ Set.Icc (a i) (b i) ⊆ U ∧
      AnalyticOnNhd ℝ
        (fun t : ℝ => c i + (R i : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) U ∧
      ∀ t ∈ U, deriv
        (fun t : ℝ => c i + (R i : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) t ≠ 0) ∧
      Set.InjOn
        (fun t : ℝ => c i + (R i : ℂ) * Complex.exp ((t : ℂ) * Complex.I))
        (Set.Ioo (a i) (b i))

end D12Complex.FiniteCircularArcs

namespace Specs.D12Complex.Ch14.FiniteCircularArcs
open _root_.D12Complex.FiniteCircularArcs

/-- Full assigned obligation; the arrangement must produce the decomposition. -/
def finite_circular_arcs_type : Prop :=
  ∀ (s : Finset ℂ) (r : ℂ → ℝ), Arrangement s r → Decomposition (diskUnion s r)

/-- Regularity of the exact primitive parametrization, including endpoints. -/
def circular_parametrization_type : Prop :=
  ∀ (c : ℂ) (R a b : ℝ), 0 < R → a < b → b - a ≤ 2 * Real.pi →
    (AnalyticOnNhd ℝ
      (fun t : ℝ => c + (R : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) Set.univ) ∧
    (∀ t : ℝ, deriv
      (fun t : ℝ => c + (R : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) t ≠ 0) ∧
    Set.InjOn (fun t : ℝ => c + (R : ℂ) * Complex.exp ((t : ℂ) * Complex.I))
      (Set.Ioo a b)

/-- Exact frontier characterization; this is more than a containing circle family. -/
def mem_frontier_diskUnion_type : Prop :=
  ∀ (s : Finset ℂ) (r : ℂ → ℝ), (∀ c ∈ s, 0 < r c) → ∀ z : ℂ,
    z ∈ frontier (diskUnion s r) ↔
      (∃ c ∈ s, dist z c = r c) ∧ ∀ c ∈ s, r c ≤ dist z c

/-- The complete assertion for the empty family. -/
def empty_decomposition_type : Prop :=
  ∀ r : ℂ → ℝ, Decomposition (diskUnion ∅ r)

end Specs.D12Complex.Ch14.FiniteCircularArcs
