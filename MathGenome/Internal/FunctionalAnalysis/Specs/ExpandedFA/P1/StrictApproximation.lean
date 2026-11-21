import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.RotundDefinitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14Minimization

/-! Independent statements for `fa2:p1:strict-approximation`, paper.tex:4629–4638.
All convexity and positive multiples are real, also for a complex space.
A supporting hyperplane is written Re(f(z)) = a, with f a nonzero continuous
scalar-linear functional, the closed unit ball on its ≤ side, and contact
with that ball. Every continuous real affine hyperplane has this form;
`HyperplaneRepresentation` records the scalar-linear representation explicitly.
Nearest points are actual members minimizing the original norm distance.
No completeness, closedness, or nonemptiness is needed for the uniqueness
characterization. Completeness and reflexivity enter only the existence result.
-/
namespace ExpandedFA.P1.StrictApproximation.Spec
universe u v
noncomputable section

variable (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def TriangleEqualityProperty : Prop :=
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  ∀ x y : E, x ≠ 0 → y ≠ 0 → ‖x + y‖ = ‖x‖ + ‖y‖ →
    ∃ r : ℝ, 0 < r ∧ y = r • x

def IsNearestPoint (C : Set E) (x z : E) : Prop :=
  z ∈ C ∧ ∀ y ∈ C, ‖x - z‖ ≤ ‖x - y‖

def NearestPointUniqueness : Prop :=
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  ∀ C : Set E, Convex ℝ C → ∀ x z w : E,
    IsNearestPoint E C x z → IsNearestPoint E C x w → z = w

def SupportsUnitBall (f : E →L[𝕜] 𝕜) (a : ℝ) : Prop :=
  f ≠ 0 ∧ (∀ z : E, ‖z‖ ≤ 1 → RCLike.re (f z) ≤ a) ∧
    ∃ z : E, ‖z‖ ≤ 1 ∧ RCLike.re (f z) = a

def SupportingHyperplaneUniqueness : Prop :=
  ∀ (f : E →L[𝕜] 𝕜) (a : ℝ), SupportsUnitBall 𝕜 E f a →
    ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 →
      RCLike.re (f x) = a → RCLike.re (f y) = a → x = y

def TriangleCharacterization : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    RotundDefinitions.Spec.RotundValue 𝕜 E ↔ TriangleEqualityProperty 𝕜 E

def NearestCharacterization : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    RotundDefinitions.Spec.RotundValue 𝕜 E ↔ NearestPointUniqueness 𝕜 E

def SupportingCharacterization : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    RotundDefinitions.Spec.RotundValue 𝕜 E ↔ SupportingHyperplaneUniqueness 𝕜 E

def HyperplaneRepresentation : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ g : E →L[ℝ] ℝ, ∃ f : E →L[𝕜] 𝕜,
      (∀ z, RCLike.re (f z) = g z) ∧ ‖f‖ = ‖g‖ ∧ (f = 0 ↔ g = 0)

def ReflexiveUniqueNearestPoint : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
    RotundDefinitions.Spec.RotundValue 𝕜 E →
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ C : Set E, C.Nonempty → IsClosed C → Convex ℝ C →
      ∀ x : E, ∃! z : E, IsNearestPoint E C x z

end
end ExpandedFA.P1.StrictApproximation.Spec
