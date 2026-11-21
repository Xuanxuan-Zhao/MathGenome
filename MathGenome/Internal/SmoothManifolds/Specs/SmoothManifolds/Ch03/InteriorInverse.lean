import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.MapClasses
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Boundary

/-! The inverse theorem at interior points. An open partial homeomorphism
records both open neighborhoods and an actual mutually inverse pair of maps.
Its source and target are required to lie in the intrinsic interiors. -/
namespace Specs.SmoothManifolds.Ch03.InteriorInverse
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.BoundaryData _root_.SmoothManifolds.FiniteRegularityData
open Set
universe u v

/-- The full differential is bijective in any vector-space realization of the
canonical tangent fibers. No equality of dimensions or nonemptiness is assumed. -/
def interior_inverseType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (r : ℕ∞), 1 ≤ r →
    ∀ (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
    ManifoldContDiff r S.smoothStructure.val T.smoothStructure.val f →
    ∀ (p : M), p ∈ manifoldInterior S → f p ∈ manifoldInterior T →
    ∀ (F : FiberModel S.smoothStructure.val p)
      (G : FiberModel T.smoothStructure.val (f p)),
    letI := F.group; letI := F.module; letI := G.group; letI := G.module
    ∀ L : CoordinateTangent S.smoothStructure.val p →ₗ[ℝ]
      CoordinateTangent T.smoothStructure.val (f p),
    IsCoordinateDifferential f p F G L → Function.Bijective L →
    ∃ h : OpenPartialHomeomorph M N,
      p ∈ h.source ∧ h.source ⊆ manifoldInterior S ∧
      h.target ⊆ manifoldInterior T ∧ EqOn h f h.source ∧
      ManifoldContDiffOn r S.smoothStructure.val T.smoothStructure.val f h.source ∧
      ManifoldContDiffOn r T.smoothStructure.val S.smoothStructure.val h.symm h.target

end Specs.SmoothManifolds.Ch03.InteriorInverse
