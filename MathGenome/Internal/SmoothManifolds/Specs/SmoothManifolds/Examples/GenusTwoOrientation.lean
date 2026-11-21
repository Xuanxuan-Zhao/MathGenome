import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Examples.GenusTwoAtlas
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.Equivalences

/-! Intrinsic orientation of the fixed connected-sum smooth structure.
Quantifying over realizations with the same maximal atlas lets these independent
Specs state the result without importing the implementation of that structure.
The quotient, generating charts, and chart domains are exactly the upstream ones. -/
namespace Specs.SmoothManifolds.Examples.GenusTwoOrientation
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.GenusTwoData _root_.SmoothManifolds.OrientationData
  _root_.SmoothManifolds.TangentBundleData

/-- Both torus bulks keep the ordered angle orientation. The seam coordinates
are ordered (angle, signed radius), whose negative wedge is positive. All
intrinsic tangent-coordinate systems and all prescribed charts are tested. -/
def orientationType : Prop :=
  ∀ S : SmoothManifold 2 .euclidean Surface,
    S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) constructionAtlas →
    ∃ o : Orientation S,
      ∀ (K : FiberCoordinates S) (e : ModelChart 2 .euclidean Surface)
        (he : e ∈ S.smoothStructure.val),
      (e ∈ bulkAtlas → ∀ p : e.source,
        IsPositive (o.val p.val) (coordinateVector K e he p)) ∧
      (e ∈ seamAtlas → ∀ p : e.source,
        IsPositive (o.val p.val) (-coordinateVector K e he p))

end Specs.SmoothManifolds.Examples.GenusTwoOrientation
