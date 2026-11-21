import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.CanonicalGreen

/-! Boundary conclusions of paper.tex:2681–2691. The canonical choice is
only specified on the punctured domain. Its zero boundary extension must
therefore be stated using a separate total representative. -/
noncomputable section
open Set Filter
open scoped Topology

namespace Specs.D12Complex.Ch14.GreenRegularBoundary
open _root_.D12Complex

def canonicalGreenZeroExtension_type := Set ℂ → ℂ → ℂ → ℝ

def canonicalGreenZeroExtension_value : canonicalGreenZeroExtension_type := fun Ω a z =>
  @ite ℝ (z ∈ Ω) (Classical.propDecidable _)
    (CanonicalGreen.canonicalGreen_value Ω a z) 0

/-- Unrestricted approach from the domain at an individually regular point. -/
def regular_point_limit_type : Prop :=
  ∀ (Ω : Set ℂ) (a ξ : ℂ), IsDomain Ω → Bornology.IsBounded Ω → a ∈ Ω →
    BarrierSqueeze.RegularBoundaryPoint_value Ω ξ →
    Tendsto (CanonicalGreen.canonicalGreen_value Ω a) (𝓝[Ω] ξ) (𝓝 0)

/-- Identification with the Dirichlet correction, on its entire natural domain. -/
def regular_domain_identification_type : Prop :=
  ∀ (Ω : Set ℂ) (a : ℂ), IsDomain Ω → Bornology.IsBounded Ω → a ∈ Ω →
    (∀ ξ ∈ frontier Ω, BarrierSqueeze.RegularBoundaryPoint_value Ω ξ) →
    EqOn (CanonicalGreen.canonicalGreen_value Ω a)
      (RegularGreen.regularGreen_value Ω a) (Ω \ {a})

/-- Continuous zero extension and uniqueness, without a positivity assumption
on a competing zero-boundary Green function. -/
def zero_extension_type : Prop :=
  ∀ (Ω : Set ℂ) (a : ℂ), IsDomain Ω → Bornology.IsBounded Ω → a ∈ Ω →
    (∀ ξ ∈ frontier Ω, BarrierSqueeze.RegularBoundaryPoint_value Ω ξ) →
    IsZeroBoundaryGreen Ω a (canonicalGreenZeroExtension_value Ω a) ∧
    EqOn (canonicalGreenZeroExtension_value Ω a)
      (RegularGreen.regularGreen_value Ω a) (closure Ω \ {a}) ∧
    (∀ g : ℂ → ℝ, IsZeroBoundaryGreen Ω a g →
      EqOn g (canonicalGreenZeroExtension_value Ω a) (closure Ω \ {a}))

end Specs.D12Complex.Ch14.GreenRegularBoundary
