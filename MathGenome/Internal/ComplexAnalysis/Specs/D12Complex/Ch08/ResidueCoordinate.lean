import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.Residue

/-! Coordinate invariance for arbitrary isolated singularities (paper.tex:1920–1944).
No finite principal part, pole, or growth condition is imposed. -/
open scoped ENNReal
namespace Specs.D12Complex.Ch08.ResidueCoordinate
open _root_.D12Complex _root_.D12Complex.Laurent _root_.D12Complex.Residue

def residue_coordinate_invariant_type : Prop :=
  ∀ (f φ : ℂ → ℂ) (a b : ℂ) (R : ℝ≥0∞) (Ω : Set ℂ),
    0 < R → HolomorphicOn (annulus a 0 R) f →
    HolomorphicOn Ω φ → b ∈ Ω → φ b = a → deriv φ b ≠ 0 →
    residue (fun w => f (φ w) * deriv φ w) b = residue f a

/-- The pullback is defined on a punctured disk inside an actual local
biholomorphism, whose image remains inside the original Laurent disk. -/
def local_coordinate_neighborhood_type : Prop :=
  ∀ (f φ : ℂ → ℂ) (a b : ℂ) (R : ℝ≥0∞) (Ω : Set ℂ),
    0 < R → HolomorphicOn (annulus a 0 R) f →
    HolomorphicOn Ω φ → b ∈ Ω → φ b = a → deriv φ b ≠ 0 →
    ∃ (U V : Set ℂ) (ψ : ℂ → ℂ) (r : ℝ),
      b ∈ U ∧ a ∈ V ∧ U ⊆ Ω ∧ BiholomorphicPair U V φ ψ ∧
      0 < r ∧ Metric.ball b r ⊆ U ∧
      Set.MapsTo φ (annulus b 0 (ENNReal.ofReal r)) (annulus a 0 R) ∧
      HolomorphicOn (annulus b 0 (ENNReal.ofReal r))
        (fun w => f (φ w) * deriv φ w)

end Specs.D12Complex.Ch08.ResidueCoordinate
