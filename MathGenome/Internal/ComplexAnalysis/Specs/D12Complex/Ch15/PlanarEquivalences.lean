import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch15.ComplementPeriods
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PrimitivePeriodCriterion
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.GlobalLogarithmCriterion
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Data.List.TFAE

/-! Independent full statement of paper.tex:2757–2765 (D12.15.07).
Simple connectivity is the usual topological property of the domain subtype.
The remaining six properties quantify over the shared weakly holomorphic
functions, original piecewise C1 paths, and the shared series exponential.
In particular the whole plane is included, and every positive root order
is quantified. No direction of this equivalence is assumed here. -/

noncomputable section
open Set

namespace Specs.D12Complex.Ch15.PlanarEquivalences
open _root_.D12Complex

def planar_equivalences_type : Prop :=
  ∀ Ω : Set ℂ, IsDomain Ω → List.TFAE [
    SimplyConnectedSpace Ω,
    IsConnected (sphereFinite '' Ω)ᶜ,
    (∀ f : ℂ → ℂ, HolomorphicOn Ω f →
      ∀ γ : PiecewiseC1Path, γ.trace ⊆ Ω → γ.IsClosed → γ.integral f = 0),
    (∀ f : ℂ → ℂ, HolomorphicOn Ω f →
      ∃ F : ℂ → ℂ, HolomorphicOn Ω F ∧ ∀ z ∈ Ω, deriv F z = f z),
    (∀ f : ℂ → ℂ, HolomorphicOn Ω f → (∀ z ∈ Ω, f z ≠ 0) →
      ∃ L : ℂ → ℂ, HolomorphicOn Ω L ∧ ∀ z ∈ Ω, E (L z) = f z),
    (∀ f : ℂ → ℂ, HolomorphicOn Ω f → (∀ z ∈ Ω, f z ≠ 0) →
      ∃ g : ℂ → ℂ, HolomorphicOn Ω g ∧ ∀ z ∈ Ω, g z ^ 2 = f z),
    (∀ f : ℂ → ℂ, HolomorphicOn Ω f → (∀ z ∈ Ω, f z ≠ 0) →
      ∀ n : ℕ, 0 < n →
        ∃ g : ℂ → ℂ, HolomorphicOn Ω g ∧ ∀ z ∈ Ω, g z ^ n = f z)]

end Specs.D12Complex.Ch15.PlanarEquivalences
