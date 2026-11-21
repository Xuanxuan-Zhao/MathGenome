import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Monotone.FiniteDimensionalGalerkin
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14BallCharacterization

/-! Independent statements for paper.tex, `fa2:p2:minty-browder`.
The dual is the continuous real-linear dual of the displayed normed space.
Reflexivity means surjectivity of its canonical evaluation into its bidual.
Coercivity is the quotient limit at norm infinity, including the zero space.
The final statement records the source's continuous strictly monotone variant;
it does not require a separate bounded-on-bounded-sets hypothesis. -/
namespace ExpandedFA.Monotone.MintyBrowder.Spec
universe u

def Surjectivity : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X],
    ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X →
    ∀ A : X → X →L[ℝ] ℝ,
      ExpandedFA.Monotone.Spec.BoundedOnBoundedSetsValue X A →
      ExpandedFA.Monotone.Spec.HemicontinuousValue X A →
      ExpandedFA.Monotone.Spec.MonotoneMapValue X A →
      ExpandedFA.Monotone.Spec.CoerciveValue X A → Function.Surjective A

def UniqueSolvability : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X],
    ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X →
    ∀ A : X → X →L[ℝ] ℝ,
      ExpandedFA.Monotone.Spec.BoundedOnBoundedSetsValue X A →
      ExpandedFA.Monotone.Spec.HemicontinuousValue X A →
      ExpandedFA.Monotone.Spec.StrictMonotoneMapValue X A →
      ExpandedFA.Monotone.Spec.CoerciveValue X A →
      ∀ f : X →L[ℝ] ℝ, ∃! x : X, A x = f

def ContinuousUniqueSolvability : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X],
    ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X →
    ∀ A : X → X →L[ℝ] ℝ, Continuous A →
      ExpandedFA.Monotone.Spec.StrictMonotoneMapValue X A →
      ExpandedFA.Monotone.Spec.CoerciveValue X A →
      ∀ f : X →L[ℝ] ℝ, ∃! x : X, A x = f

end ExpandedFA.Monotone.MintyBrowder.Spec
