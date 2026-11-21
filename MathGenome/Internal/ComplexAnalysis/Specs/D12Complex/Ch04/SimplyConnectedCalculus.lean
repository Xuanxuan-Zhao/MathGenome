import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PrimitivePeriodCriterion
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.GlobalLogarithmCriterion
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.GlobalRootCriterion
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! Global consequences of paper.tex:1144–1161 (D12.04.06).
Simple connectivity is the topological predicate on the induced space Ω.
Holomorphy is the shared weak differentiability predicate. Paths retain their
arbitrary compact parameter intervals; the rectifiable integral is the actual
mesh-limit Stieltjes integral, with no absolute-continuity assumption.
-/
noncomputable section
namespace Specs.D12Complex.Ch04.SimplyConnectedCalculus
open _root_.D12Complex

def zero_periods_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsDomain Ω → IsSimplyConnected Ω →
    HolomorphicOn Ω f →
    ∀ γ : PiecewiseC1Path, γ.trace ⊆ Ω → γ.IsClosed → γ.integral f = 0

def exists_primitive_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsDomain Ω → IsSimplyConnected Ω →
    HolomorphicOn Ω f → ∃ F : ℂ → ℂ,
      HolomorphicOn Ω F ∧ ∀ z ∈ Ω, deriv F z = f z

def closed_rectifiable_integral_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsDomain Ω → IsSimplyConnected Ω →
    HolomorphicOn Ω f →
    ∀ γ : ComplexPath, Stieltjes.Rectifiable γ → γ.trace ⊆ Ω → γ.IsClosed →
      Stieltjes.contourIntegral γ f = 0

def exists_logarithm_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsDomain Ω → IsSimplyConnected Ω →
    HolomorphicOn Ω f → (∀ z ∈ Ω, f z ≠ 0) →
    ∃ L : ℂ → ℂ, HolomorphicOn Ω L ∧ ∀ z ∈ Ω, E (L z) = f z

def exists_root_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsDomain Ω → IsSimplyConnected Ω →
    HolomorphicOn Ω f → (∀ z ∈ Ω, f z ≠ 0) →
    ∀ n : ℕ, 0 < n → ∃ g : ℂ → ℂ,
      HolomorphicOn Ω g ∧ ∀ z ∈ Ω, g z ^ n = f z

end Specs.D12Complex.Ch04.SimplyConnectedCalculus
