import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.RealNormalControlMeasure
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.CyclicModel
noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
namespace ExpandedFA.VonNeumann.RealNormalControlTopology.Spec
universe u
open RealAbelianComplexification.Spec.NativeLp
open TraceIdeals.RealComplexification
open TraceIdeals.RealComplexification.Spec
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
local instance : CompleteSpace (Space H) := completeSpace
/-- The canonical closed complex cyclic space at the specified real vector. -/
def complexCyclicSpace (N : H →L[ℝ] H) (e : H) : Submodule ℂ (Space H) :=
  (Submodule.span ℂ (Set.range (fun a : StarAlgebra.elemental ℂ (operator N) =>
    (a : Space H →L[ℂ] Space H) (inclusion e)))).topologicalClosure

/-- The real cyclic space uses the real generated star algebra on H itself. -/
def realCyclicSpace (N : H →L[ℝ] H) (e : H) : Submodule ℝ H :=
  (Submodule.span ℝ (Set.range (fun a : StarAlgebra.elemental ℝ N =>
    (a : H →L[ℝ] H) e))).topologicalClosure


/-- Normalized equivariant complex/real cyclic unitary on the SAME measure. -/
def CyclicRealization : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (N : H →L[ℝ] H), IsStarNormal N →
    ∀ C : RealNormalControlMeasure.Spec.AlgebraModel N,
    letI := C.finite
    ∃ (S : Submodule ℂ (Space H)) (hS : IsClosed (S : Set (Space H))),
      letI : CompleteSpace S := hS.completeSpace_coe
      ∃ (U : Lp ℂ 2 C.μ ≃ₗᵢ[ℂ] S) (eS : S),
        S = complexCyclicSpace N C.e ∧
        (eS : Space H) = inclusion C.e ∧
        U (ContinuousMap.toLp 2 C.μ ℂ 1) = eS ∧
        (∀ u : Lp ℂ 2 C.μ,
          (U (conjugatePullback C.involutionData u) : Space H) =
            conjugation (U u : Space H)) ∧
        (∀ (f : C(RealNormalControlMeasure.Spec.Spectrum N, ℂ)) u,
          (U (SpectralMeasure.CyclicModel.Spec.multiplier C.μ f u) : Space H) =
            C.Φ f (U u : Space H)) ∧
        (∀ B, MeasurableSet B → ∀ s : S, C.E B s ∈ S) ∧
        ∃ V : Fixed C.involutionData 2 ≃ₗᵢ[ℝ] realCyclicSpace N C.e,
          (∀ u, inclusion (V u : H) = (U u.val : Space H)) ∧
          (∀ (f : Fixed C.involutionData ∞) u,
            (V (restrictedMultiplier C.involutionData f u) : H) =
              (C.Ψ f : H →L[ℝ] H) (V u : H))
end ExpandedFA.VonNeumann.RealNormalControlTopology.Spec
