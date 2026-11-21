import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch23.OmittedValuesTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt

noncomputable section

namespace D12Complex.AuxiliaryExcludedDisks

/-- The positive real coordinates of the omitted lattice (used for n ≥ 1). -/
def a (n : ℕ) : ℝ := Real.log (Real.sqrt n + Real.sqrt ((n : ℝ) - 1))

/-- Both choices of sign and all integer imaginary translates. -/
def latticePoint (n : ℕ) (k : ℤ) (positive : Bool) : ℂ :=
  ((if positive then a n else -a n : ℝ) : ℂ) +
    (Real.pi : ℂ) * Complex.I * (k : ℂ) / 2

end D12Complex.AuxiliaryExcludedDisks

namespace Specs.D12Complex.Ch23.AuxiliaryExcludedDisks
open _root_.D12Complex _root_.D12Complex.AuxiliaryExcludedDisks Filter
open scoped Topology

def a_type := ℕ → ℝ
def a_value : a_type := fun n => Real.log (Real.sqrt n + Real.sqrt ((n : ℝ) - 1))
def latticePoint_type := ℕ → ℤ → Bool → ℂ
def latticePoint_value : latticePoint_type := fun n k positive =>
  ((if positive then a n else -a n : ℝ) : ℂ) +
    (Real.pi : ℂ) * Complex.I * (k : ℂ) / 2

def a_one_type : Prop := a 1 = 0
def a_strictMono_type : Prop := StrictMonoOn a (Set.Ici 1)
def a_tendsto_type : Prop := Tendsto a atTop atTop
def a_gap_type : Prop := ∀ n : ℕ, 1 ≤ n → a (n + 1) - a n ≤ a 2
def a_two_lt_one_type : Prop := a 2 < 1
def imaginary_spacing_type : Prop := Real.pi / 2 < 2

def lattice_omitted_type : Prop :=
  ∀ (Ω : Set ℂ) (f g : ℂ → ℂ), (∀ z ∈ Ω, f z ≠ 1) →
    (∀ z ∈ Ω, f z = -Complex.exp ((Real.pi : ℂ) * Complex.I *
      Complex.cosh (2 * g z))) →
    ∀ z ∈ Ω, ∀ n : ℕ, 1 ≤ n → ∀ k : ℤ, ∀ positive : Bool,
      g z ≠ latticePoint n k positive

def lattice_meets_disk_type : Prop :=
  ∀ c : ℂ, ∃ n : ℕ, 1 ≤ n ∧ ∃ k : ℤ, ∃ positive : Bool,
    latticePoint n k positive ∈ Metric.ball c 2

def no_disk_of_transform_type : Prop :=
  ∀ (Ω : Set ℂ) (f g : ℂ → ℂ), (∀ z ∈ Ω, f z ≠ 1) →
    (∀ z ∈ Ω, f z = -Complex.exp ((Real.pi : ℂ) * Complex.I *
      Complex.cosh (2 * g z))) →
    ∀ c : ℂ, ¬ Metric.ball c 2 ⊆ g '' Ω

def exists_transform_no_disk_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsDomain Ω → IsSimplyConnected Ω →
    HolomorphicOn Ω f → (∀ z ∈ Ω, f z ≠ 0) → (∀ z ∈ Ω, f z ≠ 1) →
    ∃ g : ℂ → ℂ, HolomorphicOn Ω g ∧
      (∀ z ∈ Ω, f z = -Complex.exp ((Real.pi : ℂ) * Complex.I *
        Complex.cosh (2 * g z))) ∧
      ∀ c : ℂ, ¬ Metric.ball c 2 ⊆ g '' Ω

end Specs.D12Complex.Ch23.AuxiliaryExcludedDisks
