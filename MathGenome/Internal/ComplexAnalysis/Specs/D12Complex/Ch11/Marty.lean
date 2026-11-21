import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.SphericalDerivative
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.SphericalCompleteness

/-! Marty’s criterion, paper.tex:2453–2460. The family consists of the
canonical scalar meromorphic maps, with their actual sphere values at poles.
The already shared normality predicate allows a constant infinity limit.
The bound is uniform in both the family member and the point of each compact
subset; it is a bound on the spherical derivative, not on the function. -/
noncomputable section
namespace Specs.D12Complex.Ch11.Marty
open _root_.D12Complex

def LocallyBoundedSphericalDerivatives_type :=
  Set ℂ → Set (ℂ → RiemannSphere) → Prop

def LocallyBoundedSphericalDerivatives_value : LocallyBoundedSphericalDerivatives_type :=
  fun Ω 𝓕 => ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∃ M : ℝ,
    ∀ F ∈ 𝓕, ∀ z ∈ K, SphericalDerivative.sphericalDeriv F z ≤ M

def marty_type : Prop := ∀ (Ω : Set ℂ) (𝓕 : Set (ℂ → RiemannSphere)),
  IsDomain Ω → (∀ F ∈ 𝓕, ScalarMeromorphicOn Ω F) →
    (SphericalCompleteness.SphericallyNormal Ω 𝓕 ↔
      LocallyBoundedSphericalDerivatives_value Ω 𝓕)

end Specs.D12Complex.Ch11.Marty
