import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.ApproximationPropertyDefinitions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.Complement
import Mathlib.Analysis.Normed.Operator.Prod

/-! Independent specifications for the assertions at paper.tex:12912–12918.
The retraction formulation covers every boundedly complemented subspace.
The complexification model records the scalar action, the exact Taylor norm,
completeness, equivalence with the product norm, and the bounded real splitting.
No approximation property is assumed in constructing the model. -/

namespace ExpandedFA.AP.ComplementedAPAndComplexificationSpec

universe u v w
noncomputable section

abbrev AP (𝕜 : Type*) (X : Type*) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : Prop :=
  Compactness.ApproximationPropertyDefinitionsSpec.HasApproximationPropertyValue 𝕜 X

/-- A bounded linear retract of a space with AP has AP, including the zero space. -/
def ComplementedAP : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (X : Type v) (Y : Type w)
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    (i : X →L[𝕜] Y) (p : Y →L[𝕜] X),
    (∀ x, p (i x) = x) → AP 𝕜 Y → AP 𝕜 X

/-- The usual subspace formulation with a bounded projection. -/
def ClosedComplementedAP : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (Y : Type v)
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (M : Submodule 𝕜 Y),
    M.ClosedComplemented → AP 𝕜 Y → AP 𝕜 M

/-- Finite complex rank is finite real rank; norms and compact sets are unchanged. -/
def ComplexAPImpliesRealAP : Prop :=
  ∀ (Y : Type u) [NormedAddCommGroup Y] [NormedSpace ℂ Y],
    AP ℂ Y → AP ℝ Y

/-- A complete complexification, with explicit real coordinates and splitting. -/
structure ComplexificationModel (X : Type u) [NormedAddCommGroup X]
    [NormedSpace ℝ X] where
  carrier : Type u
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [complexNormedSpace : NormedSpace ℂ carrier]
  [realNormedSpace : NormedSpace ℝ carrier]
  [scalarTower : IsScalarTower ℝ ℂ carrier]
  [completeSpace : CompleteSpace carrier]
  coordinates : (X × X) ≃L[ℝ] carrier
  scalar_coordinates : ∀ (c : ℂ) (x y : X),
    c • coordinates (x, y) =
      coordinates (c.re • x - c.im • y, c.im • x + c.re • y)
  norm_coordinates : ∀ x y : X,
    ‖coordinates (x, y)‖ = sSup (Set.range
      (fun θ : ℝ => ‖Real.cos θ • x - Real.sin θ • y‖))
  norm_lower : ∀ x y : X, ‖(x, y)‖ ≤ ‖coordinates (x, y)‖
  norm_upper : ∀ x y : X, ‖coordinates (x, y)‖ ≤ 2 * ‖(x, y)‖
  inclusion : X →L[ℝ] carrier
  projection : carrier →L[ℝ] X
  inclusion_coordinates : ∀ x, inclusion x = coordinates (x, 0)
  projection_coordinates : ∀ x y, projection (coordinates (x, y)) = x
  inclusion_isometry : ∀ x, ‖inclusion x‖ = ‖x‖
  retraction : ∀ x, projection (inclusion x) = x
  complemented_real_copy : inclusion.range.ClosedComplemented
  ap_implies : AP ℂ carrier → AP ℝ X

attribute [instance] ComplexificationModel.normedAddCommGroup
  ComplexificationModel.complexNormedSpace ComplexificationModel.realNormedSpace
  ComplexificationModel.scalarTower ComplexificationModel.completeSpace

/-- Every real Banach space admits this model, without any nontriviality assumption. -/
def CompleteComplexification : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X],
    Nonempty (ComplexificationModel X)

end
end ExpandedFA.AP.ComplementedAPAndComplexificationSpec
