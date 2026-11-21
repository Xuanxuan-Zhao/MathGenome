import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.MaximalIntegralCurves

/-! M06.04, paper.tex:1387–1392. Finite endpoints are specified as real
least upper bounds and greatest lower bounds of the actual time interval.
The escape assertions concern arbitrary smooth fields, without support assumptions.
All manifolds here have the boundaryless Euclidean model. -/
namespace Specs.SmoothManifolds.Ch06.EscapeCompleteness
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.TangentBundleData _root_.SmoothManifolds.VectorFieldData
  _root_.SmoothManifolds.IntegralCurveData Set
universe u

/-- Eventually outside each compact set when approaching a finite right endpoint
from within the actual maximal interval. -/
def escape_rightType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B) (p : M) (I : D13Unified.OpenTimeInterval) (γ : ℝ → M),
    IsMaximalThrough X p I γ → ∀ b : ℝ, IsLUB I.carrier b →
    ∀ K : Set M, IsCompact K → ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ I.carrier, b - ε < t → γ t ∉ K

/-- The corresponding assertion at a finite left endpoint. -/
def escape_leftType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B) (p : M) (I : D13Unified.OpenTimeInterval) (γ : ℝ → M),
    IsMaximalThrough X p I γ → ∀ a : ℝ, IsGLB I.carrier a →
    ∀ K : Set M, IsCompact K → ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ I.carrier, t < a + ε → γ t ∉ K

/-- Compact support is the closure in M of the nonzero locus of the actual
intrinsic section. Completeness means every maximal time interval is all of ℝ. -/
def compact_support_completeType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B), IsCompact (sectionSupport X.val) →
    ∀ (p : M) (I : D13Unified.OpenTimeInterval) (γ : ℝ → M),
      IsMaximalThrough X p I γ → I.carrier = univ

/-- No nonemptiness or positive dimension is required. -/
def compact_manifold_completeType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B) (p : M) (I : D13Unified.OpenTimeInterval) (γ : ℝ → M),
    IsMaximalThrough X p I γ → I.carrier = univ

end Specs.SmoothManifolds.Ch06.EscapeCompleteness
