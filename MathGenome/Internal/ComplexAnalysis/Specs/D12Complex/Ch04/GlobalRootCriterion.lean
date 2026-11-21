import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PathsChains
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.Exponential

/-! Global nth roots on arbitrary plane domains, paper.tex:1163–1194.
All paths are the canonical piecewise C1 paths on arbitrary compact intervals.
Membership in nℤ is expressed by an integer witness in ℂ. -/
noncomputable section
namespace Specs.D12Complex.Ch04.GlobalRootCriterion
open _root_.D12Complex

def root_periods_type : Prop :=
  ∀ (Ω : Set ℂ) (f g : ℂ → ℂ) (n : ℕ), IsDomain Ω →
    HolomorphicOn Ω f → (∀ z ∈ Ω, f z ≠ 0) → 0 < n →
    HolomorphicOn Ω g → (∀ z ∈ Ω, g z ^ n = f z) →
    ∀ γ : PiecewiseC1Path, γ.trace ⊆ Ω → γ.IsClosed →
      ∃ k : ℤ, (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        γ.integral (fun z => deriv f z / f z) = (n : ℂ) * (k : ℂ)

/-- The constructed root has the prescribed base value and the formula along
EVERY admissible path, thus also along every polygonal path. -/
def root_construction_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ) (n : ℕ), IsDomain Ω →
    HolomorphicOn Ω f → (∀ z ∈ Ω, f z ≠ 0) → 0 < n →
    (∀ γ : PiecewiseC1Path, γ.trace ⊆ Ω → γ.IsClosed →
      ∃ k : ℤ, (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        γ.integral (fun z => deriv f z / f z) = (n : ℂ) * (k : ℂ)) →
    ∀ a ∈ Ω, ∀ c : ℂ, c ^ n = f a → ∃ g : ℂ → ℂ,
      HolomorphicOn Ω g ∧ g a = c ∧ (∀ z ∈ Ω, g z ^ n = f z) ∧
      ∀ γ : PiecewiseC1Path, γ.trace ⊆ Ω → γ.path.source = a →
        g γ.path.target = c * E (γ.integral (fun z => deriv f z / f z) / (n : ℂ))

def root_criterion_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ) (n : ℕ), IsDomain Ω →
    HolomorphicOn Ω f → (∀ z ∈ Ω, f z ≠ 0) → 0 < n →
    ((∃ g : ℂ → ℂ, HolomorphicOn Ω g ∧ ∀ z ∈ Ω, g z ^ n = f z) ↔
      ∀ γ : PiecewiseC1Path, γ.trace ⊆ Ω → γ.IsClosed →
        ∃ k : ℤ, (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          γ.integral (fun z => deriv f z / f z) = (n : ℂ) * (k : ℂ))

def root_unique_type : Prop :=
  ∀ (Ω : Set ℂ) (f g h : ℂ → ℂ) (n : ℕ), IsDomain Ω →
    HolomorphicOn Ω f → (∀ z ∈ Ω, f z ≠ 0) → 0 < n →
    HolomorphicOn Ω g → HolomorphicOn Ω h →
    (∀ z ∈ Ω, g z ^ n = f z) → (∀ z ∈ Ω, h z ^ n = f z) →
    ∃ ζ : ℂ, ζ ^ n = 1 ∧ ∀ z ∈ Ω, g z = ζ * h z

end Specs.D12Complex.Ch04.GlobalRootCriterion
