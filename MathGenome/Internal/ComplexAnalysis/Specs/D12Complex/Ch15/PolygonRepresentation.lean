import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.FiniteCycleCauchy

/-! Independent specification of paper.tex:2712–2721 (D12.15.02).
The contours are the canonical finite integer combinations of closed paths.
Polygonality concerns the actual parametrized paths, not just their traces.
-/
noncomputable section
open Set

namespace D12Complex.PolygonRepresentation

/-- Each member of a finite C1 partition is an affine segment, with its
actual endpoint values. Zero-piece partitions allow degenerate paths. -/
def IsPolygonalPath (γ : PiecewiseC1Path) : Prop :=
  ∃ P : C1Partition γ.path, ∀ i : Fin P.count, ∀ t ∈ P.pieceSet i,
    γ t = γ (P.node i.castSucc) +
      (((t - P.node i.castSucc) / (P.node i.succ - P.node i.castSucc) : ℝ) : ℂ) *
        (γ (P.node i.succ) - γ (P.node i.castSucc))

/-- Integer multiplicities and orientations remain in the canonical chain. -/
def IsPolygonalCycle (Γ : IntegralCycle) : Prop :=
  ∀ γ ∈ Γ.chain.support, IsPolygonalPath γ

/-- A quantitative, uniform separation, also meaningful for empty sets. -/
def PositivelySeparated (K : Set ℂ) (Γ : IntegralCycle) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, ∀ w ∈ Γ.trace, δ ≤ dist z w

end D12Complex.PolygonRepresentation

namespace Specs.D12Complex.Ch15.PolygonRepresentation
open _root_.D12Complex _root_.D12Complex.PolygonRepresentation

def polygon_representation_type : Prop :=
  ∀ (K U : Set ℂ) (f : ℂ → ℂ),
    IsCompact K → IsOpen U → K ⊆ U → HolomorphicOn U f →
    ∃ Γ : IntegralCycle,
      IsPolygonalCycle Γ ∧ Γ.trace ⊆ U \ K ∧ PositivelySeparated K Γ ∧
      (K = ∅ → Γ = 0) ∧
      ∀ z ∈ K, f z = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        Γ.integral (fun w => f w / (w - z))

end Specs.D12Complex.Ch15.PolygonRepresentation
