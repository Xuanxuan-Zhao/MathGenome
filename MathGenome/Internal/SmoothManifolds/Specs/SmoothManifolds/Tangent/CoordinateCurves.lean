import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Atlases
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Independent curve statements; all coordinates use the shared chart models. -/
namespace Specs.SmoothManifolds.Tangent.CoordinateCurves
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
open Set Filter
open scoped Topology
universe u

/-- The three parameter sets have unique differentiation at zero. -/
def uniqueDiffCurveDomainType : Prop :=
  ∀ J : Set ℝ, J = univ ∨ J = Ici 0 ∨ J = Iic 0 → UniqueDiffWithinAt ℝ J 0

/-- Every coordinate vector is realized, with an ambient smooth extension in
    each chart at the base point. Either endpoint is allowed. -/
def existsCoordinateCurveType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n kind M) (p : M) (e : ModelChart n kind M),
    e ∈ S.smoothStructure.val → p ∈ e.source → ∀ v : Euclidean n,
    ∃ J : Set ℝ, (J = univ ∨ J = Ici 0 ∨ J = Iic 0) ∧
    ∃ c : ℝ → M, c 0 = p ∧ ContinuousWithinAt c J 0 ∧
      HasDerivWithinAt (fun t => (e (c t)).val) v J 0 ∧
      ∀ d ∈ S.smoothStructure.val, p ∈ d.source →
        ∃ W : Set ℝ, IsOpen W ∧ (0 : ℝ) ∈ W ∧
        ∃ H : ℝ → Euclidean n, ContDiffOn ℝ (⊤ : ℕ∞) H W ∧
          (fun t => (d (c t)).val) =ᶠ[𝓝[J] 0] H

/-- The scalar chain rule only needs continuity of the curve within its domain,
    its selected coordinate derivative, and a representative of the scalar germ. -/
def scalarDerivativeAlongCurveType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (p : M) (e : ModelChart n kind M) (J : Set ℝ),
    (J = univ ∨ J = Ici 0 ∨ J = Iic 0) →
    ∀ (c : ℝ → M), c 0 = p → ContinuousWithinAt c J 0 →
    ∀ (v : Euclidean n), HasDerivWithinAt (fun t => (e (c t)).val) v J 0 →
    ∀ (F : Euclidean n → ℝ) (U : Set (Euclidean n)),
      IsOpen U → (e p).val ∈ U → ContDiffOn ℝ (⊤ : ℕ∞) F U →
      ∀ f : M → ℝ, f =ᶠ[𝓝 p] (fun y => F (e y).val) →
        HasDerivWithinAt (f ∘ c) (fderiv ℝ F (e p).val v) J 0

end Specs.SmoothManifolds.Tangent.CoordinateCurves
