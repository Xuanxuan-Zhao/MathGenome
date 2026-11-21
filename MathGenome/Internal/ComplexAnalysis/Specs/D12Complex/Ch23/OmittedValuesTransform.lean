import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! The first assertion of paper.tex:4164–4181, d12:23:auxiliary.
The excluded-disk assertion is assigned separately. All functions below are
total representatives; their identities and weak holomorphy are required on Ω.
The construction records actual global logarithms and square roots, rather
than treating them as additional assumptions on f. -/
noncomputable section

namespace Specs.D12Complex.Ch23.OmittedValuesTransform
open _root_.D12Complex

def exists_transform_construction_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsDomain Ω → IsSimplyConnected Ω →
    HolomorphicOn Ω f → (∀ z ∈ Ω, f z ≠ 0) → (∀ z ∈ Ω, f z ≠ 1) →
    ∃ t F A B H g : ℂ → ℂ,
      HolomorphicOn Ω t ∧ HolomorphicOn Ω F ∧
      HolomorphicOn Ω A ∧ HolomorphicOn Ω B ∧
      HolomorphicOn Ω H ∧ HolomorphicOn Ω g ∧
      (∀ z ∈ Ω, Complex.exp (t z) = f z) ∧
      (∀ z ∈ Ω, F z = t z / (2 * (Real.pi : ℂ) * Complex.I)) ∧
      (∀ z ∈ Ω, ∀ k : ℤ, F z ≠ (k : ℂ)) ∧
      (∀ z ∈ Ω, A z ^ 2 = F z) ∧
      (∀ z ∈ Ω, B z ^ 2 = F z - 1) ∧
      (∀ z ∈ Ω, H z = A z - B z) ∧
      (∀ z ∈ Ω, H z * (A z + B z) = 1) ∧
      (∀ z ∈ Ω, H z ≠ 0) ∧
      (∀ z ∈ Ω, Complex.exp (g z) = H z) ∧
      (∀ z ∈ Ω, Complex.cosh (2 * g z) = 2 * F z - 1) ∧
      (∀ z ∈ Ω, f z = -Complex.exp ((Real.pi : ℂ) * Complex.I *
        Complex.cosh (2 * g z)))

def exists_transform_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsDomain Ω → IsSimplyConnected Ω →
    HolomorphicOn Ω f → (∀ z ∈ Ω, f z ≠ 0) → (∀ z ∈ Ω, f z ≠ 1) →
    ∃ g : ℂ → ℂ, HolomorphicOn Ω g ∧
      ∀ z ∈ Ω, f z = -Complex.exp ((Real.pi : ℂ) * Complex.I *
        Complex.cosh (2 * g z))

end Specs.D12Complex.Ch23.OmittedValuesTransform
