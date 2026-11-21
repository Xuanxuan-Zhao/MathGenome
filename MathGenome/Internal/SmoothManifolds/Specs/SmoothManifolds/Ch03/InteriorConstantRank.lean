import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.MapClasses
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Boundary
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Interior constant-rank coordinates. All coordinate neighborhoods are genuine
open partial homeomorphisms. Compatibility is recorded by a C^r Euclidean
coordinate change and its C^r inverse relative to an original atlas chart.
There are no positivity assumptions on the dimensions or the rank. -/
set_option autoImplicit false

namespace SmoothManifolds.InteriorRankData
open ModelData AtlasData MapData BoundaryData Set
open scoped ContDiff
universe u v

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- First k coordinates followed by zeros; valid also for empty blocks. -/
def normalProjection (m n k : ℕ) (u : E m) : E n :=
  WithLp.toLp 2 (fun j => if h : j.val < k ∧ j.val < m then u ⟨j.val, h.2⟩ else 0)

/-- Both directions of the coordinate change are C^r on their actual domains.
The chart's source lies in the ambient interior of an original chart. -/
def CompatibleCoordinates {m : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (r : ℕ∞) (S : SmoothManifold m a M)
    (c : OpenPartialHomeomorph M (E m)) : Prop :=
  ∃ e ∈ S.smoothStructure.val,
  ∃ A : OpenPartialHomeomorph (Euclidean m) (E m),
    ContDiffOn ℝ r A A.source ∧ ContDiffOn ℝ r A.symm A.target ∧
    c.source ⊆ e.source ∩ (fun x => (e x).val) ⁻¹' interior (modelSet m a) ∧
    (∀ x ∈ c.source, (e x).val ∈ A.source ∧ c x = A (e x).val) ∧
    c.target ⊆ A.target ∧
    ∀ u ∈ c.target, (e (c.symm u)).val = A.symm u

/-- Centered compatible coordinates, including maps-to for the whole source
neighborhood and the normal form on the whole coordinate image. -/
def NormalForm {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N] (r : ℕ∞)
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (f : M → N) (p : M) (k : ℕ) : Prop :=
  ∃ c : OpenPartialHomeomorph M (E m),
  ∃ d : OpenPartialHomeomorph N (E n),
    CompatibleCoordinates r S c ∧ CompatibleCoordinates r T d ∧
    p ∈ c.source ∧ c p = 0 ∧ f p ∈ d.source ∧ d (f p) = 0 ∧
    MapsTo f c.source d.source ∧
    ∀ u ∈ c.target, d (f (c.symm u)) = normalProjection m n k u
end SmoothManifolds.InteriorRankData

namespace Specs.SmoothManifolds.Ch03.InteriorConstantRank
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.BoundaryData _root_.SmoothManifolds.MapClassData
  _root_.SmoothManifolds.InteriorRankData Set
universe u v

def interior_constant_rankType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N] (r : ℕ∞), 1 ≤ r →
  ∀ (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
    ManifoldContDiff r S.smoothStructure.val T.smoothStructure.val f →
  ∀ p, p ∈ manifoldInterior S → f p ∈ manifoldInterior T →
  ∀ k, (∃ W : Set M, IsOpen W ∧ p ∈ W ∧ ∀ x ∈ W, rankAt S T f x = k) →
    0 ≤ k ∧ k ≤ min m n ∧ NormalForm r S T f p k

def interior_immersionType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N] (r : ℕ∞), 1 ≤ r →
  ∀ (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
    ManifoldContDiff r S.smoothStructure.val T.smoothStructure.val f →
  ∀ p, p ∈ manifoldInterior S → f p ∈ manifoldInterior T →
    IsImmersionAt S T f p → m ≤ n ∧ NormalForm r S T f p m ∧
    ∃ W : Set M, IsOpen W ∧ p ∈ W ∧
      ∀ x ∈ W, IsImmersionAt S T f x ∧ rankAt S T f x = m

def interior_submersionType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N] (r : ℕ∞), 1 ≤ r →
  ∀ (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
    ManifoldContDiff r S.smoothStructure.val T.smoothStructure.val f →
  ∀ p, p ∈ manifoldInterior S → f p ∈ manifoldInterior T →
    IsSubmersionAt S T f p → n ≤ m ∧ NormalForm r S T f p n ∧
    ∃ W : Set M, IsOpen W ∧ p ∈ W ∧
      ∀ x ∈ W, IsSubmersionAt S T f x ∧ rankAt S T f x = n
end Specs.SmoothManifolds.Ch03.InteriorConstantRank
