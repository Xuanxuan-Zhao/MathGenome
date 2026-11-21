import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.VectorFieldDerivations
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.SolutionConcepts

/-! M06.03: the maximal-curve clause. Representatives are total functions only
for using ambient calculus; all assertions concern their recorded open interval.
No nonemptiness or positive-dimensionality assumption is made on the manifold. -/
namespace SmoothManifolds.IntegralCurveData
open ModelData AtlasData TangentData TangentBundleData VectorFieldData Set
universe u

/-- Smooth integral curve, expressed in every smooth chart using the intrinsic
coordinate linear equivalence. The continuity clause prevents jumps between
chart neighborhoods. Only times in `I` enter this predicate. -/
def IsIntegralCurveOn {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    (X : SmoothField B) (I : Set ℝ) (γ : ℝ → M) : Prop :=
  ContinuousOn γ I ∧ ∀ t ∈ I,
    ∀ (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
      (ht : γ t ∈ e.source),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun s => (e (γ s)).val) t ∧
      HasDerivAt (fun s => (e (γ s)).val)
        (B.fiberCoordinates.equiv e he (γ t) ht (X.val (γ t))) t

/-- Universal extension property, including equality of the actual curve values
on every comparison interval. It does not compare off-domain representatives. -/
def IsMaximalThrough {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    (X : SmoothField B) (p : M) (I : D13Unified.OpenTimeInterval)
    (γ : ℝ → M) : Prop :=
  0 ∈ I.carrier ∧ γ 0 = p ∧ IsIntegralCurveOn X I.carrier γ ∧
    ∀ (J : D13Unified.OpenTimeInterval) (η : ℝ → M),
      0 ∈ J.carrier → η 0 = p → IsIntegralCurveOn X J.carrier η →
        J.carrier ⊆ I.carrier ∧ EqOn γ η J.carrier
end SmoothManifolds.IntegralCurveData

namespace Specs.SmoothManifolds.Ch06.MaximalIntegralCurves
open _root_.SmoothManifolds _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.TangentBundleData _root_.SmoothManifolds.VectorFieldData
  _root_.SmoothManifolds.IntegralCurveData Set
universe u

/-- Existence and the full universal maximality property. -/
def maximal_existsType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B) (p : M),
    ∃ (I : D13Unified.OpenTimeInterval) (γ : ℝ → M), IsMaximalThrough X p I γ

/-- Equality at any common time implies equality on the entire intersection. -/
def overlap_uniqueType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B) (I J : D13Unified.OpenTimeInterval) (γ η : ℝ → M),
    IsIntegralCurveOn X I.carrier γ → IsIntegralCurveOn X J.carrier η →
    ∀ s ∈ I.carrier ∩ J.carrier, γ s = η s → EqOn γ η (I.carrier ∩ J.carrier)

/-- Uniqueness includes the maximal interval itself. -/
def maximal_uniqueType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B) (p : M) (I J : D13Unified.OpenTimeInterval) (γ η : ℝ → M),
    IsMaximalThrough X p I γ → IsMaximalThrough X p J η →
      I.carrier = J.carrier ∧ EqOn γ η I.carrier
end Specs.SmoothManifolds.Ch06.MaximalIntegralCurves
