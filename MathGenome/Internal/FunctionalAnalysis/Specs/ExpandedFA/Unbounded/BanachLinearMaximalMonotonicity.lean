import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.BanachAdjoint
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Monotone.Definitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import Mathlib.Analysis.Convex.StrictConvexSpace

/-! Independent specifications for `fa2:p3:banach-linear-maximal-monotone`,
paper.tex:14249–14345. The bidual identification is canonical evaluation.
The pullback below preserves the exact Banach-adjoint domain. Maximality is
among all monotone graphs, including nonlinear and multivalued extensions.
The last equality concerns norm closures, not the unclosed ranges. -/
noncomputable section
namespace ExpandedFA.Unbounded.BanachLinearMaximalSpec
universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The Banach adjoint pulled back to X by x ↦ (f ↦ f x).
This construction itself does not assume reflexivity or density; its adjoint
interpretation is used with the explicit hypotheses in the statements below. -/
def adjointValue (A : Operator ℝ X (X →L[ℝ] ℝ)) : Operator ℝ X (X →L[ℝ] ℝ) where
  domain := (BanachAdjointSpec.adjointValue A).domain.comap
    (P1.C04CanonicalMap.Spec.CanonicalEvaluationValue ℝ X).toLinearMap
  toFun :=
    { toFun := fun x => BanachAdjointSpec.adjointValue A
        ⟨P1.C04CanonicalMap.Spec.CanonicalEvaluationValue ℝ X x, x.2⟩
      map_add' := by
        intro x y
        rw [← (BanachAdjointSpec.adjointValue A).map_add]
        congr 1
        apply Subtype.ext
        exact map_add _ _ _
      map_smul' := by
        intro c x
        rw [← (BanachAdjointSpec.adjointValue A).map_smul]
        congr 1
        apply Subtype.ext
        exact map_smul _ _ _ }

/-- No stronger notion of extension is substituted for graph maximality. -/
def Criterion : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [StrictConvexSpace ℝ X] [StrictConvexSpace ℝ (X →L[ℝ] ℝ)],
    P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X →
    ∀ (A : Operator ℝ X (X →L[ℝ] ℝ)), A.IsClosed → Dense (A.domain : Set X) →
    Monotone.Spec.LinearMonotoneValue X A →
    (Monotone.Spec.LinearMaximalMonotoneValue X A ↔
      Monotone.Spec.LinearMonotoneValue X (adjointValue A))

def AdjointMaximality : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [StrictConvexSpace ℝ X] [StrictConvexSpace ℝ (X →L[ℝ] ℝ)],
    P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X →
    ∀ (A : Operator ℝ X (X →L[ℝ] ℝ)), A.IsClosed → Dense (A.domain : Set X) →
    Monotone.Spec.LinearMaximalMonotoneValue X A →
    Monotone.Spec.LinearMaximalMonotoneValue X (adjointValue A)

def KernelEquality : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [StrictConvexSpace ℝ X] [StrictConvexSpace ℝ (X →L[ℝ] ℝ)],
    P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X →
    ∀ (A : Operator ℝ X (X →L[ℝ] ℝ)), A.IsClosed → Dense (A.domain : Set X) →
    Monotone.Spec.LinearMaximalMonotoneValue X A → A.ker = (adjointValue A).ker

def RangeClosureEquality : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [StrictConvexSpace ℝ X] [StrictConvexSpace ℝ (X →L[ℝ] ℝ)],
    P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X →
    ∀ (A : Operator ℝ X (X →L[ℝ] ℝ)), A.IsClosed → Dense (A.domain : Set X) →
    Monotone.Spec.LinearMaximalMonotoneValue X A →
    closure (A.toFun.range : Set (X →L[ℝ] ℝ)) =
      closure ((adjointValue A).toFun.range : Set (X →L[ℝ] ℝ))

end ExpandedFA.Unbounded.BanachLinearMaximalSpec
