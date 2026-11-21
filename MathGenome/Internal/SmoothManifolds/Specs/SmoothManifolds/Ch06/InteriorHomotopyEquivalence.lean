import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Boundary
import Mathlib.Data.Fin.Tuple.Basic

/-! The interior-inclusion clause of M06.06 (paper.tex:1407–1417).
The interval has its subspace topology. Smoothness on its product with a
manifold is tested by ambient extensions in the time and chart coordinates,
including at the interval faces and at corners. The interior carries the
restricted atlas; it is not given an independently chosen smooth structure. -/
namespace SmoothManifolds.InteriorHomotopyData
open ModelData AtlasData MapData BoundaryData Set
universe u v

abbrev HomotopyTime := ↥(Icc (0 : ℝ) 1)
def timeZero : HomotopyTime := ⟨0, le_rfl, zero_le_one⟩
def timeOne : HomotopyTime := ⟨1, zero_le_one, le_rfl⟩

/-- The ordinary smooth product test, also at the faces of the interval.
Extensions may leave both the time interval and the target model. -/
def SmoothHomotopy {n m : ℕ} {a b : ModelKind} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set (ModelChart n a X)) (B : Set (ModelChart m b Y))
    (H : HomotopyTime × X → Y) : Prop :=
  Continuous H ∧ ∀ e ∈ A, ∀ d ∈ B, ∀ z : HomotopyTime × X,
    z.2 ∈ e.source → H z ∈ d.source →
    LocalCoordinateExtension (⊤ : ℕ∞)
      (fun w : HomotopyTime × X => Fin.cons w.1.val (e w.2).val)
      (fun w => (d (H w)).val) z

/-- A smooth homotopy inverse for the actual interior inclusion, together with
one ambient homotopy which restricts to the required homotopy on the interior.
No compactness, positive dimension, or nonempty-boundary hypothesis occurs. -/
structure InteriorHomotopyEquivalence {n : ℕ} {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n kind M) where
  isOpen_interior : IsOpen (manifoldInterior S)
  inverse : M → manifoldInterior S
  smooth_inverse : ManifoldSmooth S.smoothStructure.val
    (openSubsetAtlas S.smoothStructure.val (manifoldInterior S) isOpen_interior) inverse
  smooth_inclusion : ManifoldSmooth
    (openSubsetAtlas S.smoothStructure.val (manifoldInterior S) isOpen_interior)
    S.smoothStructure.val Subtype.val
  homotopy : HomotopyTime × M → M
  smooth_homotopy : SmoothHomotopy S.smoothStructure.val S.smoothStructure.val homotopy
  homotopy_zero : ∀ x, homotopy (timeZero, x) = x
  homotopy_one : ∀ x, homotopy (timeOne, x) = (inverse x).val
  preserves_interior : ∀ (s : HomotopyTime) (x : manifoldInterior S),
    homotopy (s, x.val) ∈ manifoldInterior S
  smooth_restricted_homotopy : SmoothHomotopy
    (openSubsetAtlas S.smoothStructure.val (manifoldInterior S) isOpen_interior)
    (openSubsetAtlas S.smoothStructure.val (manifoldInterior S) isOpen_interior)
    (fun z : HomotopyTime × manifoldInterior S =>
      ⟨homotopy (z.1, z.2.val), preserves_interior z.1 z.2⟩)

end SmoothManifolds.InteriorHomotopyData

namespace Specs.SmoothManifolds.Ch06.InteriorHomotopyEquivalence
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.InteriorHomotopyData
universe u

/-- Inclusion of the full manifold interior is a smooth homotopy equivalence. -/
def interior_inclusion_homotopy_equivalenceType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n kind M), Nonempty (InteriorHomotopyEquivalence S)

end Specs.SmoothManifolds.Ch06.InteriorHomotopyEquivalence
