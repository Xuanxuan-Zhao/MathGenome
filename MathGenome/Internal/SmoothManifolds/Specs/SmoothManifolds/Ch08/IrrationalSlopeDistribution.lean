import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch08.GlobalLeaves
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.IrrationalLine

/-! The descended constant slope distribution in the quotient torus, and all
its translated integral lines (paper.tex 793–811 and 1665). -/
namespace Specs.SmoothManifolds.Ch08.IrrationalSlopeDistribution
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.MapData _root_.SmoothManifolds.SphereTorusData
  _root_.SmoothManifolds.IrrationalLineData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.DistributionData
  _root_.SmoothManifolds.GlobalLeafData

/-- The construction works for every real slope. It uses the original intrinsic
tangent fibers and requires their coordinates in every actual quotient chart.
Every translated original line has a genuine differential onto these fibers. -/
def slope_distributionType : Prop :=
  ∀ (α : ℝ) (S : SmoothManifold 1 .euclidean ℝ)
    (Q : SmoothManifold 2 .euclidean (FlatTorus 2)),
    S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) realAtlas →
    Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas 2) →
    ∃ (C : CotangentBundle Q) (D : SmoothDistribution C 1),
      IsInvolutive D ∧
      (∀ (a : Euclidean 2) (ε : ℝ)
        (e : ModelChart 2 .euclidean (FlatTorus 2))
        (he : e ∈ Q.smoothStructure.val),
        IsAngleChart a ε e → ∀ (p : FlatTorus 2) (hp : p ∈ e.source)
          (v : TangentSpace Q p),
          v ∈ D.fiber p ↔ C.tangent.fiberCoordinates.equiv e he p hp v ∈
            Submodule.span ℝ {(![1, α] : Euclidean 2)}) ∧
      ∀ p : FlatTorus 2,
        IsIntegralImmersion D S (fun t : ℝ => p + irrationalLine α t)
end Specs.SmoothManifolds.Ch08.IrrationalSlopeDistribution
