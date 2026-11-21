import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PathsChains
import Mathlib.Topology.UnitInterval

/-! Independent statements of the homotopy conclusions in paper.tex:975–1002,
1144–1161. The first coordinate is homotopy time and the second is path time.
Each original compact parameter interval, including a degenerate interval,
is traversed by its nondecreasing affine map from the unit interval.
Only continuity is required of the square; its intermediate curves have no
rectifiability or differentiability requirement. -/

noncomputable section
open Set
open scoped unitInterval

namespace Specs.D12Complex.Ch04.HomotopyIntegrals
open _root_.D12Complex

def fixed_endpoint_integral_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), HolomorphicOn Ω f →
  ∀ γ₀ γ₁ : PiecewiseC1Path, γ₀.trace ⊆ Ω → γ₁.trace ⊆ Ω →
  ∀ H : C(I × I, ℂ), (∀ p, H p ∈ Ω) →
    (∀ t : I, H (0, t) = γ₀ (γ₀.path.a + (γ₀.path.b - γ₀.path.a) * (t : ℝ))) →
    (∀ t : I, H (1, t) = γ₁ (γ₁.path.a + (γ₁.path.b - γ₁.path.a) * (t : ℝ))) →
    (∀ s : I, H (s, 0) = γ₀.path.source) →
    (∀ s : I, H (s, 1) = γ₀.path.target) →
    γ₀.integral f = γ₁.integral f

def free_loop_integral_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), HolomorphicOn Ω f →
  ∀ γ₀ γ₁ : PiecewiseC1Path, γ₀.trace ⊆ Ω → γ₁.trace ⊆ Ω →
  γ₀.IsClosed → γ₁.IsClosed →
  ∀ H : C(I × I, ℂ), (∀ p, H p ∈ Ω) →
    (∀ t : I, H (0, t) = γ₀ (γ₀.path.a + (γ₀.path.b - γ₀.path.a) * (t : ℝ))) →
    (∀ t : I, H (1, t) = γ₁ (γ₁.path.a + (γ₁.path.b - γ₁.path.a) * (t : ℝ))) →
    (∀ s : I, H (s, 0) = H (s, 1)) →
    γ₀.integral f = γ₁.integral f

def null_homotopic_integral_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), HolomorphicOn Ω f →
  ∀ γ : PiecewiseC1Path, γ.trace ⊆ Ω → γ.IsClosed →
    (∃ (z : ℂ) (H : C(I × I, ℂ)), (∀ p, H p ∈ Ω) ∧
      (∀ t : I, H (0, t) = γ (γ.path.a + (γ.path.b - γ.path.a) * (t : ℝ))) ∧
      (∀ t : I, H (1, t) = z) ∧ (∀ s : I, H (s, 0) = H (s, 1))) →
    γ.integral f = 0

end Specs.D12Complex.Ch04.HomotopyIntegrals
