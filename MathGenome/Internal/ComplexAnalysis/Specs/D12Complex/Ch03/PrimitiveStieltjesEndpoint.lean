import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.RectifiableStieltjes

/-! Independent statements for the arbitrary rectifiable endpoint formula,
paper.tex:658–669. The derivative is the ordinary pointwise complex derivative;
the integral is the canonical unrestricted mesh limit, with independent tags. -/
noncomputable section
open Set

namespace Specs.D12Complex.Ch03.PrimitiveStieltjesEndpoint
open _root_.D12Complex

def hasIntegral_endpoint_type : Prop :=
  ∀ (Ω : Set ℂ), IsOpen Ω → ∀ (f F : ℂ → ℂ), ContinuousOn f Ω →
    (∀ z ∈ Ω, HasDerivAt F (f z) z) →
    ∀ γ : ComplexPath, Stieltjes.Rectifiable γ → γ.trace ⊆ Ω →
      Stieltjes.HasIntegral γ.a γ.b (f ∘ γ) γ (F γ.target - F γ.source)

def contourIntegral_endpoint_type : Prop :=
  ∀ (Ω : Set ℂ), IsOpen Ω → ∀ (f F : ℂ → ℂ), ContinuousOn f Ω →
    (∀ z ∈ Ω, HasDerivAt F (f z) z) →
    ∀ γ : ComplexPath, Stieltjes.Rectifiable γ → γ.trace ⊆ Ω →
      Stieltjes.contourIntegral γ f = F γ.target - F γ.source

end Specs.D12Complex.Ch03.PrimitiveStieltjesEndpoint
