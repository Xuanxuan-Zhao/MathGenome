import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PolygonalConnectivity

/-! Independent statement of the path-integral construction in paper.tex:646–654.
The hypothesis quantifies over the canonical paths on all compact intervals.
No primitive, analyticity, or simple connectivity is assumed. -/
namespace Specs.D12Complex.Ch03.PrimitiveConstruction
open Set _root_.D12Complex

def construction_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsDomain Ω → ContinuousOn f Ω →
    (∀ γ η : PiecewiseC1Path, γ.trace ⊆ Ω → η.trace ⊆ Ω →
      γ.path.source = η.path.source → γ.path.target = η.path.target →
      γ.integral f = η.integral f) →
    ∀ a ∈ Ω, ∃ F : ℂ → ℂ,
      HolomorphicOn Ω F ∧ (∀ z ∈ Ω, deriv F z = f z) ∧ F a = 0 ∧
      ∀ γ : PiecewiseC1Path, γ.trace ⊆ Ω → γ.path.source = a →
        F γ.path.target = γ.integral f

def exists_primitive_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), IsDomain Ω → ContinuousOn f Ω →
    (∀ γ η : PiecewiseC1Path, γ.trace ⊆ Ω → η.trace ⊆ Ω →
      γ.path.source = η.path.source → γ.path.target = η.path.target →
      γ.integral f = η.integral f) →
    ∃ F : ℂ → ℂ, HolomorphicOn Ω F ∧ ∀ z ∈ Ω, deriv F z = f z

end Specs.D12Complex.Ch03.PrimitiveConstruction
