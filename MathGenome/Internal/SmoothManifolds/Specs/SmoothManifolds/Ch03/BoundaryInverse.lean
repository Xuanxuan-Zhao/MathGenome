import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.InteriorInverse
import Mathlib.Topology.Homeomorph.Lemmas

/-! Boundary inverse theorem and the failure of the unrestricted boundary IFT.
The differential is the full coordinate-quotient differential, at finite or
infinite regularity, and local preservation of the intrinsic boundary is explicit. -/
namespace SmoothManifolds.BoundaryInverseData
open ModelData AtlasData MapData BoundaryData FiniteRegularityData Set

/-- Standard global Euclidean chart, with the canonical univ-subtype model. -/
def euclideanChart (n : ℕ) : ModelChart n .euclidean (Euclidean n) :=
  (Homeomorph.Set.univ (Euclidean n)).symm.toOpenPartialHomeomorph

end SmoothManifolds.BoundaryInverseData

namespace Specs.SmoothManifolds.Ch03.BoundaryInverse
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.BoundaryData _root_.SmoothManifolds.FiniteRegularityData
  _root_.SmoothManifolds.BoundaryInverseData Set Filter
open scoped Topology
universe u v

/-- Open neighborhoods in the original manifolds, hence relatively open
half-space neighborhoods in boundary charts, with an actual C^r inverse. -/
def boundary_inverseType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (r : ℕ∞), 1 ≤ r →
    ∀ (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N),
    ManifoldContDiff r S.smoothStructure.val T.smoothStructure.val f →
    ∀ (p : M), p ∈ intrinsicBoundary S → f p ∈ intrinsicBoundary T →
    (∀ᶠ x in 𝓝 p, x ∈ intrinsicBoundary S → f x ∈ intrinsicBoundary T) →
    ∀ (F : FiberModel S.smoothStructure.val p)
      (G : FiberModel T.smoothStructure.val (f p)),
    letI := F.group; letI := F.module; letI := G.group; letI := G.module
    ∀ L : CoordinateTangent S.smoothStructure.val p →ₗ[ℝ]
      CoordinateTangent T.smoothStructure.val (f p),
    IsCoordinateDifferential f p F G L → Function.Bijective L →
    ∃ h : OpenPartialHomeomorph M N,
      p ∈ h.source ∧ EqOn h f h.source ∧
      ManifoldContDiffOn r S.smoothStructure.val T.smoothStructure.val f h.source ∧
      ManifoldContDiffOn r T.smoothStructure.val S.smoothStructure.val h.symm h.target

/-- The explicit inclusion counterexample, in every positive dimension.
Standard structures are identified by their global coordinate charts. The
nonexistence of a section is stronger than nonexistence of a smooth section. -/
def halfSpace_inclusion_counterexampleType : Prop :=
  ∀ n : ℕ, ∃ (S : SmoothManifold (n + 1) .halfSpace (HalfSpace (n + 1)))
    (T : SmoothManifold (n + 1) .euclidean (Euclidean (n + 1))),
    OpenPartialHomeomorph.refl (HalfSpace (n + 1)) ∈ S.smoothStructure.val ∧
    euclideanChart (n + 1) ∈ T.smoothStructure.val ∧
    IsSmoothMap S T Subtype.val ∧
    (∀ p : HalfSpace (n + 1),
      ∃ (F : FiberModel S.smoothStructure.val p)
        (G : FiberModel T.smoothStructure.val p.val),
      letI := F.group; letI := F.module; letI := G.group; letI := G.module
      ∃ L : CoordinateTangent S.smoothStructure.val p →ₗ[ℝ]
        CoordinateTangent T.smoothStructure.val p.val,
        IsCoordinateDifferential Subtype.val p F G L ∧ Function.Bijective L) ∧
    (∀ p : HalfSpace (n + 1),
      (p ∈ intrinsicBoundary S ↔ p.val (Fin.last n) = 0)) ∧
    (∀ p : HalfSpace (n + 1), p.val (Fin.last n) = 0 →
      (¬ ∃ h : OpenPartialHomeomorph (HalfSpace (n + 1)) (Euclidean (n + 1)),
        p ∈ h.source ∧ EqOn h Subtype.val h.source) ∧
      (∀ V : Set (HalfSpace (n + 1)),
        ¬ ∃ W : Set (Euclidean (n + 1)), IsOpen W ∧ p.val ∈ W ∧
          W ⊆ Subtype.val '' V) ∧
      (¬ ∃ (W : Set (Euclidean (n + 1))) (s : W → HalfSpace (n + 1)),
        IsOpen W ∧ p.val ∈ W ∧ ∀ y : W, (s y).val = y.val))

end Specs.SmoothManifolds.Ch03.BoundaryInverse
