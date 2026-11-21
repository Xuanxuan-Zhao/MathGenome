import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.EnfloSpace
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15Basis
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.ApproximationPropertyDefinitions

/-! Independent conclusions of `fa2:ap:counterexample`, paper.tex:12884–12923.
AP quantifies over every norm-compact set and every positive tolerance, with
no common bound on the norms of the approximants. Reflexivity is surjectivity
of the canonical continuous linear evaluation map. Both infinite ordered
Schauder bases and finite lists (including the empty list) are excluded. -/
noncomputable section
namespace ExpandedFA.AP.ReflexiveSpaceWithoutAP.Spec
open Compactness.ApproximationPropertyDefinitionsSpec
open ExpandedFA.P1.C15Basis.Spec
open ExpandedFA.P1.C04CanonicalMap.Spec

universe u v

def SchauderBasisImpliesAP : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {e : ℕ → E}, IsRawSchauderBasis (𝕜 := 𝕜) e →
      HasApproximationPropertyValue 𝕜 E

def FiniteBasisImpliesAP : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {d : ℕ} {e : Fin d → E}, IsRawFiniteBasis (𝕜 := 𝕜) e →
      HasApproximationPropertyValue 𝕜 E

def ConstructedSpaceWithoutAP : Prop :=
  ∀ D : EnfloSpace.Spec.IncidenceData,
    ¬ HasApproximationPropertyValue ℝ (EnfloSpace.Spec.X D)

def RealCounterexample : Prop :=
  ∃ (X : Type) (_ : NormedAddCommGroup X) (_ : NormedSpace ℝ X),
    CompleteSpace X ∧ TopologicalSpace.SeparableSpace X ∧
    IsReflexiveValue ℝ X ∧ ¬ HasApproximationPropertyValue ℝ X ∧
    (∀ e : ℕ → X, ¬ IsRawSchauderBasis (𝕜 := ℝ) e) ∧
    (∀ (d : ℕ) (e : Fin d → X), ¬ IsRawFiniteBasis (𝕜 := ℝ) e)

def ComplexCounterexample : Prop :=
  ∃ (Z : Type) (_ : NormedAddCommGroup Z) (_ : NormedSpace ℂ Z),
    CompleteSpace Z ∧ ¬ HasApproximationPropertyValue ℂ Z

end ExpandedFA.AP.ReflexiveSpaceWithoutAP.Spec
