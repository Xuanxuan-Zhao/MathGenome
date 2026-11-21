import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Examples.RealProjectiveSpace
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.FiniteRegularity
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Ring

/-! Independent statements for paper.tex, Lemma `p104:good-directions`.
The parameter d denotes the projective dimension, so the ambient space is R^(d+1).
The strict dimension hypotheses imply the ambient dimension is positive.
The orthogonal projection is defined in ambient coordinates and its codomain
is its range, precisely the orthogonal complement of the represented line.
Immersion into this linear subspace is tested after its linear inclusion:
smoothness is preserved/reflected by the split inclusion, and the full
derivative is injective exactly when its ambient-coordinate expression is.
The implementation also supplies actual extensions with values in that range. -/
namespace SmoothManifolds.GoodProjectionData
open ModelData AtlasData MapData FiniteRegularityData ProjectiveData SphereTorusData
open Set
open scoped BigOperators
universe u

/-- The actual one-dimensional linear subspace represented by an antipodal orbit. -/
def directionSubmodule {d : ℕ} (L : RealProjectiveSpace d) :
    Submodule ℝ (Euclidean (d + 1)) :=
  Quotient.lift (fun x : Sphere d => Submodule.span ℝ {x.val}) (by
    rintro x y (h | h)
    · rw [h]
    · rw [h]
      simpa only [antipode, Set.neg_singleton] using
        (Submodule.span_neg ({y.val} : Set (Euclidean (d + 1))))) L

/-- Projection to the orthogonal complement of a unit representative, using the
ordinary sum-of-squares inner product, regardless of the chosen equivalent norm. -/
def representativeProjection {d : ℕ} (x : Sphere d) :
    Euclidean (d + 1) →ₗ[ℝ] Euclidean (d + 1) where
  toFun z := z - (∑ i, x.val i * z i) • x.val
  map_add' z w := by
    ext j
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      mul_add, Finset.sum_add_distrib]
    ring
  map_smul' c z := by
    ext j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [← mul_assoc, mul_comm (x.val _) c, mul_assoc]
    rw [← Finset.mul_sum]
    ring

/-- The orthogonal projection is independent of the sign of the representative. -/
def projectionLinear {d : ℕ} (L : RealProjectiveSpace d) :
    Euclidean (d + 1) →ₗ[ℝ] Euclidean (d + 1) :=
  Quotient.lift representativeProjection (by
    rintro x y (h | h)
    · rw [h]
    · rw [h]
      ext z j
      simp [representativeProjection, antipode, Finset.sum_neg_distrib]) L

noncomputable def projection {d : ℕ} (L : RealProjectiveSpace d) :
    Euclidean (d + 1) →L[ℝ] Euclidean (d + 1) :=
  (projectionLinear L).toContinuousLinearMap

/-- The canonical orthogonal-complement model, realized as the image of the
orthogonal projection. The implementation verifies both orthogonality and
that every perpendicular vector is fixed, as well as its dimension d. -/
abbrev ProjectionSpace {d : ℕ} (L : RealProjectiveSpace d) :=
  LinearMap.range (projectionLinear L)

/-- The actual map into the orthogonal complement, with its subspace topology. -/
noncomputable def projectedMap {d : ℕ} {M : Type u} (L : RealProjectiveSpace d)
    (e : M → Euclidean (d + 1)) : M → ProjectionSpace L :=
  fun p => ⟨projection L (e p), ⟨e p, rfl⟩⟩

/-- The projectivization of a prescribed vector subspace, including the empty
projectivization when V = {0}. -/
def projectiveSubspace {d : ℕ} (V : Submodule ℝ (Euclidean (d + 1))) :
    Set (RealProjectiveSpace d) := {L | directionSubmodule L ≤ V}

/-- Smoothness into Euclidean space, with the shared ambient-extension convention. -/
def IsSmoothEuclidean {n q : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (f : M → Euclidean q) : Prop :=
  ∀ p, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val f p

/-- Full derivative injectivity in every source chart, including normal vectors
at a face. Smoothness is a conclusion/component, rather than an assumed jet. -/
def IsEuclideanImmersion {n q : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (f : M → Euclidean q) : Prop :=
  IsSmoothEuclidean S f ∧ ∀ c ∈ S.smoothStructure.val,
    ∀ p ∈ c.source, Function.Injective (coordinateDerivative c f p)

/-- Lines occupied by nonzero secants. -/
def secantDirections {d : ℕ} {M : Type u} (f : M → Euclidean (d + 1)) :
    Set (RealProjectiveSpace d) :=
  {L | ∃ p p' : M, p ≠ p' ∧ f p - f p' ≠ 0 ∧
    f p - f p' ∈ directionSubmodule L}

/-- Lines occupied by nonzero full tangent images. -/
def tangentDirections {n d : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (f : M → Euclidean (d + 1)) :
    Set (RealProjectiveSpace d) :=
  {L | ∃ c ∈ S.smoothStructure.val, ∃ p ∈ c.source, ∃ v : Euclidean n,
    coordinateDerivative c f p v ≠ 0 ∧
      coordinateDerivative c f p v ∈ directionSubmodule L}

end SmoothManifolds.GoodProjectionData

namespace Specs.SmoothManifolds.Ch04.GoodProjections
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.GoodProjectionData
  _root_.SmoothManifolds.ProjectiveData Set
universe u

/-- Includes the optional exclusion of any prescribed proper projective subspace.
Taking V = bottom gives the assertion without an additional exclusion. -/
def injective_immersion_directions_denseType : Prop :=
  ∀ {n d : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (e : M → Euclidean (d + 1)),
    IsEuclideanImmersion S e → Function.Injective e → 2 * n + 1 < d + 1 →
    ∀ V : Submodule ℝ (Euclidean (d + 1)), V ≠ ⊤ →
      Dense {L : RealProjectiveSpace d | L ∉ projectiveSubspace V ∧
        Function.Injective (projectedMap L e) ∧
        IsEuclideanImmersion S (fun p => (projectedMap L e p).val)}

def immersion_directions_denseType : Prop :=
  ∀ {n d : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (e : M → Euclidean (d + 1)),
    IsEuclideanImmersion S e → 2 * n < d + 1 →
    ∀ V : Submodule ℝ (Euclidean (d + 1)), V ≠ ⊤ →
      Dense {L : RealProjectiveSpace d | L ∉ projectiveSubspace V ∧
        IsEuclideanImmersion S (fun p => (projectedMap L e p).val)}

/-- The tangent exclusion really is empty in dimension zero. -/
def tangentDirections_zeroType : Prop :=
  ∀ {d : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (e : M → Euclidean (d + 1)),
    tangentDirections S e = ∅

end Specs.SmoothManifolds.Ch04.GoodProjections
