import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Boundary
import Mathlib.Data.Fin.Tuple.Basic

/-! The collar clause of M06.05, paper.tex:1396–1405.

The source has its actual product topology. Its smooth coordinates are the
first n-1 coordinates of an ambient boundary chart, followed by the time
coordinate. These are precisely the boundary-restriction product coordinates;
no freely chosen smooth structure on the collar source is permitted. Smoothness
in each direction uses the project's local ambient extension definition.
For n=0 the boundary is empty, so both coordinate tests are vacuous.
-/
namespace SmoothManifolds.CollarData
open ModelData AtlasData MapData BoundaryData Set
universe u

/-- The half-open time factor, with its subspace topology. -/
abbrev CollarTime := ↥(Ico (0 : ℝ) 1)

/-- The actual source of a collar, including the empty-boundary case. -/
abbrev CollarSource {n : ℕ} {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n kind M) :=
  intrinsicBoundary S × CollarTime

/-- Time zero belongs to the half-open time factor. -/
def timeZero : CollarTime := ⟨0, le_rfl, zero_lt_one⟩

/-- Boundary-product coordinates: delete the constrained final coordinate and
append time. For n>0 this has exactly n coordinates. The formula is harmless
in dimension zero, where no collar-source point exists. -/
def collarCoordinates {n : ℕ} {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n kind M}
    (e : ModelChart n kind M) (x : CollarSource S) : Euclidean (n - 1 + 1) :=
  Fin.snoc (fun i : Fin (n - 1) =>
    (e x.1.val).val ⟨i.val, lt_of_lt_of_le i.isLt (Nat.sub_le n 1)⟩) x.2.val

/-- A smooth collar onto an open neighborhood of the entire intrinsic boundary.
Both smoothness tests quantify over every ambient smooth boundary chart; the
boundary atlas and its product coordinates are therefore the induced ones.
The inverse is tested on the open image, with its subspace topology. -/
structure SmoothCollar {n : ℕ} {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n kind M) where
  neighborhood : Set M
  isOpen_neighborhood : IsOpen neighborhood
  boundary_subset : intrinsicBoundary S ⊆ neighborhood
  toHomeomorph : CollarSource S ≃ₜ neighborhood
  zero_section : ∀ q : intrinsicBoundary S,
    (toHomeomorph (q, timeZero)).val = q.val
  smooth_forward : ∀ (e d : ModelChart n kind M),
    e ∈ S.smoothStructure.val → d ∈ S.smoothStructure.val →
    ∀ x : CollarSource S, x.1.val ∈ e.source →
      (toHomeomorph x).val ∈ d.source →
      LocalCoordinateExtension (⊤ : ℕ∞) (collarCoordinates e)
        (fun y => (d (toHomeomorph y).val).val) x
  smooth_inverse : ∀ (d e : ModelChart n kind M),
    d ∈ S.smoothStructure.val → e ∈ S.smoothStructure.val →
    ∀ y : neighborhood, y.val ∈ d.source →
      (toHomeomorph.symm y).1.val ∈ e.source →
      LocalCoordinateExtension (⊤ : ℕ∞) (fun z : neighborhood => (d z.val).val)
        (fun z => collarCoordinates e (toHomeomorph.symm z)) y

end SmoothManifolds.CollarData

namespace Specs.SmoothManifolds.Ch06.Collar
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.BoundaryData
  _root_.SmoothManifolds.CollarData
universe u

/-- Every ordinary smooth manifold has a smooth collar of its full intrinsic
boundary. There is no compactness, connectedness, nonemptiness, positive
dimension, or common pre-rescaling time-width assumption. -/
def collar_existsType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n kind M), Nonempty (SmoothCollar S)

end Specs.SmoothManifolds.Ch06.Collar
