import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.SliceStructures
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.InteriorConstantRank
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.Differential

/-! The regular-level theorem uses the actual subspace topology.  A structure
on a nonempty fiber has dimension m-n; no global inequality n ≤ m is imposed.
The local converse is on an open neighborhood, with its induced smooth atlas.
All statements below are independent of the candidate implementation. -/
set_option autoImplicit false

namespace SmoothManifolds.RegularLevelData
open ModelData AtlasData MapData Set
universe u

/-- This singles out the usual Euclidean smooth structure by its global chart. -/
def HasStandardEuclideanChart {d : ℕ}
    (T : SmoothManifold d .euclidean (Euclidean d)) : Prop :=
  ∃ e ∈ T.smoothStructure.val, e.source = univ ∧ ∀ x, (e x).val = x

end SmoothManifolds.RegularLevelData

namespace Specs.SmoothManifolds.Ch03.RegularLevels
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.BoundaryData _root_.SmoothManifolds.MapClassData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.DifferentialData
  _root_.SmoothManifolds.RegularLevelData Set
universe u v

/-- Closedness does not need the regular-value hypothesis. -/
def fiber_closedType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
    IsSmoothMap S T f → ∀ y, IsClosed (f ⁻¹' {y})

/-- Empty fibers impose no dimension restriction. -/
def regular_fiber_dimensionType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
    intrinsicBoundary S = ∅ → intrinsicBoundary T = ∅ → IsSmoothMap S T f →
    ∀ y, IsRegularValue S T f y →
      ((f ⁻¹' {y}).Nonempty → n ≤ m) ∧ (m < n → f ⁻¹' {y} = ∅)

/-- Existence and uniqueness of the maximal atlas on this exact subspace.
The empty fiber is included, even when m<n.  The codimension formula is
asserted only for a nonempty fiber. -/
def regular_fiber_structureType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
    intrinsicBoundary S = ∅ → intrinsicBoundary T = ∅ → IsSmoothMap S T f →
    ∀ y, IsRegularValue S T f y →
    ∃ R : SmoothManifold (m - n) .euclidean (f ⁻¹' {y}),
      IsSmoothEmbedding R S Subtype.val ∧ intrinsicBoundary R = ∅ ∧
      ((f ⁻¹' {y}).Nonempty → (m - n) + n = m) ∧
      ∀ Q : SmoothManifold (m - n) .euclidean (f ⁻¹' {y}),
        IsSmoothEmbedding Q S Subtype.val → Q.smoothStructure = R.smoothStructure

/-- This says bijective identification with the actual linear kernel, via the
inclusion differential.  Both maps are intrinsic germ-derivation differentials;
the tangent space at the inclusion image is definitionally T_p M. -/
def regular_fiber_tangentType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
    intrinsicBoundary S = ∅ → intrinsicBoundary T = ∅ → IsSmoothMap S T f →
    ∀ y, IsRegularValue S T f y →
    ∀ (R : SmoothManifold (m - n) .euclidean (f ⁻¹' {y})),
    IsSmoothEmbedding R S Subtype.val → ∀ p : f ⁻¹' {y},
    ∀ (L : TangentSpace S p.val →ₗ[ℝ] TangentSpace T (f p.val))
      (K : TangentSpace R p →ₗ[ℝ] TangentSpace S p.val),
      IsDifferential S T f p.val L → IsDifferential R S Subtype.val p K →
      Function.Injective K ∧ LinearMap.range K = LinearMap.ker L

/-- A zero-dimensional target has discrete topology.  Hence all fibers are
open as well as closed, consistent with the dimension-m structure above. -/
def zero_target_clopenType : Prop :=
  ∀ {m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold 0 b N) (f : M → N),
    IsSmoothMap S T f → ∀ y, IsOpen (f ⁻¹' {y}) ∧ IsClosed (f ⁻¹' {y})

/-- The defining submersion is local on M, and has the usual Euclidean target.
The atlas equality makes the domain the inherited open-submanifold structure.
No positive codimension assumption is made. -/
def local_defining_submersionType : Prop :=
  ∀ {k m : ℕ} {a b : ModelKind} {M : Type u} {P : Type v}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold m a M) (R : SmoothManifold k b P) (f : P → M),
    intrinsicBoundary S = ∅ → intrinsicBoundary R = ∅ →
    IsSmoothEmbedding R S f → ∀ p : P,
    k ≤ m ∧ ∃ (U : Set M) (hU : IsOpen U), f p ∈ U ∧
      ∃ A : SmoothManifold m a U,
        A.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
          (openSubsetAtlas S.smoothStructure.val U hU) ∧
      ∃ E : SmoothManifold (m - k) .euclidean (Euclidean (m - k)),
        HasStandardEuclideanChart E ∧
      ∃ g : U → Euclidean (m - k),
        IsSmoothMap A E g ∧ IsSubmersion A E g ∧
        ∀ x : U, x.val ∈ range f ↔ g x = 0

end Specs.SmoothManifolds.Ch03.RegularLevels
