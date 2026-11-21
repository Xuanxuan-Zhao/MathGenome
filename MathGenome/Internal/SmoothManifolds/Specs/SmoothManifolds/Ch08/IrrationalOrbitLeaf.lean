import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch08.GlobalLeaves
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.IrrationalLine

/-! Whole-leaf identification for the original irrational line, conditional
only on the integral translation family and the actual universal intrinsic leaf. -/
set_option autoImplicit false
noncomputable section
namespace Specs.SmoothManifolds.Ch08.IrrationalOrbitLeaf
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.MapData _root_.SmoothManifolds.SphereTorusData
  _root_.SmoothManifolds.IrrationalLineData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.CovectorData
  _root_.SmoothManifolds.DistributionData _root_.SmoothManifolds.LeafData
  _root_.SmoothManifolds.GlobalLeafData Set

/-- Both the set equality and the specified diffeomorphism use the genuine
plaque-chain leaf and exactly its intrinsic topology. -/
def orbit_leafType : Prop :=
  ∀ (α : ℝ), Irrational α →
  ∀ (S : SmoothManifold 1 .euclidean ℝ)
    (Q : SmoothManifold 2 .euclidean (FlatTorus 2)),
    S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) realAtlas →
    Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas 2) →
  ∀ (C : CotangentBundle Q) (D : SmoothDistribution C 1),
    (∀ p : FlatTorus 2, IsIntegralImmersion D S (fun t : ℝ => p + irrationalLine α t)) →
  ∀ A : Set (ModelChart 2 .euclidean (FlatTorus 2)),
    IsCountableAdaptedAtlas D A →
  ∀ T : @SmoothManifold 1 .euclidean (leafSet A 1 0) (leafTopology A 1 0),
    @ConnectedSpace (leafSet A 1 0) (leafTopology A 1 0) →
    UniversalIntegralLeaf D A 0 T →
    leafSet A 1 0 = lineRange α ∧
      (letI := leafTopology A 1 0
       ∃ h : Diffeomorph S.smoothStructure.val T.smoothStructure.val,
         ∀ t : ℝ, (h.toEquiv t).val = irrationalLine α t)
end Specs.SmoothManifolds.Ch08.IrrationalOrbitLeaf
