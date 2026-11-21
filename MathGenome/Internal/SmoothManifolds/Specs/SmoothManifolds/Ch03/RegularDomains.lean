import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.MapClasses
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Boundary
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! Regular domains have the subspace topology and the same dimension as the
ambient manifold. All boundaries below are the canonical intrinsic boundaries;
they are mapped into the ambient space before comparison with its frontier.
The scalar target is the ordinary real line: `realChart` fixes its coordinates.
-/
namespace SmoothManifolds.RegularDomainData
open ModelData AtlasData MapData BoundaryData MapClassData Set
universe u

/-- The global ordinary coordinate on the real line. -/
def realChart : ModelChart 1 .euclidean ℝ where
  toFun t := ⟨fun _ => t, mem_univ _⟩
  invFun x := x.val 0
  source := univ
  target := univ
  map_source' := fun _ _ => mem_univ _
  map_target' := fun _ _ => mem_univ _
  left_inv' := fun _ _ => rfl
  right_inv' := fun x _ => Subtype.ext (by funext i; change x.val 0 = x.val i; rw [Fin.eq_zero i])
  open_source := isOpen_univ
  open_target := isOpen_univ
  continuousOn_toFun := (continuous_pi (fun _ => continuous_id)).subtype_mk _ |>.continuousOn
  continuousOn_invFun := ((continuous_apply 0).comp continuous_subtype_val).continuousOn

/-- Membership of the global linear coordinate fixes the standard real atlas. -/
def HasStandardRealChart (R : SmoothManifold 1 .euclidean ℝ) : Prop :=
  realChart ∈ R.smoothStructure.val

/-- Closed, full-dimensional, embedded submanifold, with its given intrinsic
smooth structure and the ambient subspace topology. Boundarylessness is an
explicit hypothesis on the ambient manifold in the theorems. -/
def IsRegularDomain {m : ℕ} {a b : ModelKind} {M : Type u} [TopologicalSpace M]
    (T : SmoothManifold m b M) (d : Set M) (S : SmoothManifold m a d) : Prop :=
  IsClosed d ∧ IsSmoothEmbedding S T Subtype.val

def sublevel {M : Type u} (f : M → ℝ) : Set M := {x | f x ≤ 0}

end SmoothManifolds.RegularDomainData

namespace Specs.SmoothManifolds.Ch03.RegularDomains
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.BoundaryData _root_.SmoothManifolds.MapClassData
  _root_.SmoothManifolds.RegularDomainData Set
universe u v

/-- Existence makes the scalar-target convention available independently of
any input function or regularity assertion. -/
def standard_real_structureType : Prop :=
  ∃ R : SmoothManifold 1 .euclidean ℝ, HasStandardRealChart R

/-- No nonemptiness or positive-dimension hypothesis is imposed. The image
notation compares sets in M, rather than confusing the two underlying spaces.
The embedding formulation includes subsets by specializing f to Subtype.val. -/
def regular_domain_topologyType : Prop :=
  ∀ {m : ℕ} {a b : ModelKind} {P : Type u} {M : Type v}
    [TopologicalSpace P] [TopologicalSpace M]
    (S : SmoothManifold m a P) (T : SmoothManifold m b M) (f : P → M),
    intrinsicBoundary T = ∅ → IsClosed (range f) → IsSmoothEmbedding S T f →
    f '' manifoldInterior S = interior (range f) ∧
      f '' intrinsicBoundary S = frontier (range f)

/-- A regular sublevel carries the full-dimensional embedded half-space
structure. This includes m=0, empty sublevels, and the whole ambient manifold.
Regularity is the canonical surjectivity of the full tangent differential. -/
def regular_sublevelType : Prop :=
  ∀ {m : ℕ} {b : ModelKind} {M : Type u} [TopologicalSpace M]
    (T : SmoothManifold m b M) (R : SmoothManifold 1 .euclidean ℝ) (f : M → ℝ),
    intrinsicBoundary T = ∅ → HasStandardRealChart R →
    IsSmoothMap T R f → IsRegularValue T R f 0 →
    ∃ S : SmoothManifold m .halfSpace (sublevel f),
      IsRegularDomain T (sublevel f) S ∧
      Subtype.val '' manifoldInterior S = {x | f x < 0} ∧
      Subtype.val '' intrinsicBoundary S = f ⁻¹' {0} ∧
      interior (sublevel f) = {x | f x < 0} ∧
      frontier (sublevel f) = f ⁻¹' {0}

/-- Empty zero fibers satisfy the original regular-value definition vacuously. -/
def regular_value_empty_zeroType : Prop :=
  ∀ {m : ℕ} {b : ModelKind} {M : Type u} [TopologicalSpace M]
    (T : SmoothManifold m b M) (R : SmoothManifold 1 .euclidean ℝ) (f : M → ℝ),
    f ⁻¹' {0} = ∅ → IsRegularValue T R f 0

end Specs.SmoothManifolds.Ch03.RegularDomains
