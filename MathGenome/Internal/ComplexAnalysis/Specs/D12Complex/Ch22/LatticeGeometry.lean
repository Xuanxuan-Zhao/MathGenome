import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Independent specification for the lattice portion of paper.tex, d12:22-01. -/
noncomputable section

namespace Specs.D12Complex.Ch22.LatticeGeometry

/-- Integer span of the two given complex periods, with no orientation baked in. -/
def lattice (ω₁ ω₂ : ℂ) : Submodule ℤ ℂ :=
  Submodule.span ℤ {ω₁, ω₂}

def latticeType := ℂ → ℂ → Submodule ℤ ℂ

def Membership : Prop :=
  ∀ (ω₁ ω₂ z : ℂ), z ∈ lattice ω₁ ω₂ ↔
    ∃ m n : ℤ, (m : ℂ) * ω₁ + (n : ℂ) * ω₂ = z

def LowerBound : Prop :=
  ∀ (ω₁ ω₂ : ℂ), ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∃ c : ℝ, 0 < c ∧ ∀ m n : ℤ,
      c * (|(m : ℝ)| + |(n : ℝ)|) ≤ ‖(m : ℂ) * ω₁ + (n : ℂ) * ω₂‖

def Discrete : Prop :=
  ∀ (ω₁ ω₂ : ℂ), ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    DiscreteTopology (lattice ω₁ ω₂)

def BoundedFinite : Prop :=
  ∀ (ω₁ ω₂ : ℂ), ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ (a : ℂ) (R : ℝ),
      Set.Finite ((lattice ω₁ ω₂ : Set ℂ) ∩ Metric.closedBall a R)

/-- The minimum separation is positive and is attained by a nonzero lattice vector. -/
def MinimumDistance : Prop :=
  ∀ (ω₁ ω₂ : ℂ), ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∃ d : ℝ, 0 < d ∧ ∃ z ∈ lattice ω₁ ω₂, z ≠ 0 ∧ ‖z‖ = d ∧
      ∀ x ∈ lattice ω₁ ω₂, ∀ y ∈ lattice ω₁ ω₂, x ≠ y → d ≤ dist x y

/-- Absolute convergence of the real, nonnegative lattice p-series, with zero omitted. -/
def PowerSummable : Prop :=
  ∀ (ω₁ ω₂ : ℂ), ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ s : ℝ, 2 < s →
      Summable (fun z : {z : lattice ω₁ ω₂ // z ≠ 0} => ‖(z.1 : ℂ)‖ ^ (-s))

def Orientation : Prop :=
  ∀ ω₁ ω₂ : ℂ, lattice ω₁ (-ω₂) = lattice ω₁ ω₂ ∧
    ((ω₂ / ω₁).im < 0 → 0 < ((-ω₂) / ω₁).im)

end Specs.D12Complex.Ch22.LatticeGeometry
