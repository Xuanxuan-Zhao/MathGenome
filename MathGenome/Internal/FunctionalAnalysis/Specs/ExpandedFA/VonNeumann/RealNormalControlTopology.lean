import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.RealNormalControlMeasure
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.RealNormalCyclicRealization
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.RealNormalRestrictedResolution

/-! Independent obligations for the real native-Lp predual and whole-algebra
WOT assertion. All algebraic and measure witnesses belong to the same upstream
`AlgebraModel`; the fixed spaces retain their inherited real Banach norms. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
namespace ExpandedFA.VonNeumann.RealNormalControlTopology.Spec
universe u v
open RealAbelianComplexification.Spec.NativeLp
open TraceIdeals.RealComplexification
open TraceIdeals.RealComplexification.Spec

/-- The initial topology of all real L¹ tests, on the entire native real form. -/
def weakStarTopology {X : Type u} [MeasurableSpace X] {μ : Measure X}
    (D : InvolutionData μ) : TopologicalSpace (Fixed D ∞) :=
  .induced (fun f g => pairing D f g) Pi.topologicalSpace

/-- Genuine Banach-predual identification, including its map and exact norm. -/
def NativePredual : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (D : InvolutionData μ),
    ∃ I : Fixed D ∞ ≃ₗᵢ[ℝ] (Fixed D 1 →L[ℝ] ℝ),
      ∀ f g, I f g = pairing D f g

/-- The square-root/phase construction is in the native fixed real L² spaces.
The equality of products is ordinary μ-a.e. equality of representatives. -/
def FixedFactorization : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X) (D : InvolutionData μ)
    (g : Fixed D 1), ∃ a b : Fixed D 2,
      (a.val : X → ℂ) =ᵐ[μ] (fun x => (Real.sqrt ‖g.val x‖ : ℂ)) ∧
      (b.val : X → ℂ) =ᵐ[μ]
        (fun x => g.val x / (Real.sqrt ‖g.val x‖ : ℂ)) ∧
      (fun x => star (a.val x) * b.val x) =ᵐ[μ] g.val

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
local instance : CompleteSpace (Space H) := completeSpace

/-- Each real vector coefficient is a native fixed L¹ test; conversely every
such test is one coefficient on actual vectors in the original H. -/
def CoefficientFunctionals {N : H →L[ℝ] H}
    (C : RealNormalControlMeasure.Spec.AlgebraModel N) : Prop :=
  (∀ x y : H, ∃ g : Fixed C.involutionData 1,
    ∀ f : Fixed C.involutionData ∞,
      ⟪x, (C.Ψ f : H →L[ℝ] H) y⟫_ℝ = pairing C.involutionData f g) ∧
  (∀ g : Fixed C.involutionData 1, ∃ x y : H,
    ∀ f : Fixed C.involutionData ∞,
      pairing C.involutionData f g = ⟪x, (C.Ψ f : H →L[ℝ] H) y⟫_ℝ)

/-- Covariance and Radon--Nikodym uniqueness put the actual coefficient
measure density in the shared native fixed L¹ space. -/
def CoefficientDensities {N : H →L[ℝ] H}
    (C : RealNormalControlMeasure.Spec.AlgebraModel N) : Prop :=
  ∀ x y : H, ∃ g : Fixed C.involutionData 1,
    ∀ B, MeasurableSet B →
      ⟪inclusion x, C.E B (inclusion y)⟫_ℂ = ∫ z in B, g.val z ∂C.μ

/-- The forward coefficient statement retains precisely the supplied model. -/
def ForwardCoefficients : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (N : H →L[ℝ] H) (C : RealNormalControlMeasure.Spec.AlgebraModel N),
    CoefficientDensities C ∧
      (∀ x y : H, ∃ g : Fixed C.involutionData 1,
        ∀ f : Fixed C.involutionData ∞,
          ⟪x, (C.Ψ f : H →L[ℝ] H) y⟫_ℝ = pairing C.involutionData f g)

/-- The normalized complex cyclic model and its real restriction, anchored to
C's vector and vector measure. The spectrum equality is an equality of actual
sets in ℂ, not an identification inferred from the name of a subtype. The PVM
on that spectrum has exactly the original projection action and vector measure. -/
def CyclicOnResolution {N : H →L[ℝ] H}
    (C : RealNormalControlMeasure.Spec.AlgebraModel N) : Prop :=
  letI := C.finite
  ∃ (S : Submodule ℂ (Space H)) (hS : IsClosed (S : Set (Space H))),
    letI : CompleteSpace S := hS.completeSpace_coe
    ∃ (U : Lp ℂ 2 C.μ ≃ₗᵢ[ℂ] S) (R : S →L[ℂ] S)
      (F : SpectralMeasure.ProjectionValuedMeasure (RealNormalControlMeasure.Spec.Spectrum N) S)
      (eS : S),
      S = complexCyclicSpace N C.e ∧
      (eS : Space H) = inclusion C.e ∧
      U (ContinuousMap.toLp 2 C.μ ℂ 1) = eS ∧
      (∀ u : Lp ℂ 2 C.μ,
        (U (conjugatePullback C.involutionData u) : Space H) =
          conjugation (U u : Space H)) ∧
      (∀ (f : C(RealNormalControlMeasure.Spec.Spectrum N, ℂ)) u,
        (U (SpectralMeasure.CyclicModel.Spec.multiplier C.μ f u) : Space H) =
          C.Φ f (U u : Space H)) ∧
      (∀ s : S, (R s : Space H) = operator N s) ∧ IsStarNormal R ∧
      spectrum ℂ R = RealNormalControlMeasure.Spec.Spectrum N ∧
      (∀ B, MeasurableSet B → ∀ s : S, (F B s : Space H) = C.E B s) ∧
      (∀ B, MeasurableSet B → C.μ B = ENNReal.ofReal (‖F B eS‖ ^ 2)) ∧
      (∃ ΦR : (RealNormalControlMeasure.Spec.Spectrum N → ℂ) → S →L[ℂ] S,
        SpectralMeasure.BorelNormSpectrum.Spec.BorelCalculus F ΦR ∧
        ΦR (fun z => (z : ℂ)) = R) ∧
      ∃ V : Fixed C.involutionData 2 ≃ₗᵢ[ℝ] realCyclicSpace N C.e,
        (∀ u, inclusion (V u : H) = (U u.val : Space H)) ∧
        (∀ (f : Fixed C.involutionData ∞) u,
          (V (restrictedMultiplier C.involutionData f u) : H) =
            (C.Ψ f : H →L[ℝ] H) (V u : H))

/-- The cyclic model suffices to transport every fixed L¹ test to actual
real vectors. No cyclicity assumption on all of H occurs. -/
def ReverseFromCyclic : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (N : H →L[ℝ] H) (C : RealNormalControlMeasure.Spec.AlgebraModel N),
    CyclicOnResolution C → ∀ g : Fixed C.involutionData 1, ∃ x y : H,
      ∀ f : Fixed C.involutionData ∞,
        pairing C.involutionData f g = ⟪x, (C.Ψ f : H →L[ℝ] H) y⟫_ℝ

/-- Remaining cyclic construction, with the SAME supplied upstream witnesses. -/
def CyclicConstruction : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (N : H →L[ℝ] H), IsStarNormal N →
      ∀ C : RealNormalControlMeasure.Spec.AlgebraModel N, CyclicOnResolution C

/-- Initial-topology comparison needs exactly the two coefficient directions. -/
def TopologyFromCoefficients : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (N : H →L[ℝ] H) (C : RealNormalControlMeasure.Spec.AlgebraModel N),
    CoefficientFunctionals C →
      weakStarTopology C.involutionData = TopologicalSpace.induced
        (fun f => (C.Ψ f : H →L[ℝ] H)) (OperatorTopology.Spec.WeakTopologyValue ℝ H H)

/-- A single witness package includes the complete finite-control/Borel-image
and real algebra result, the actual native L¹ predual, and whole-algebra WOT. -/
structure Model (N : H →L[ℝ] H) extends RealNormalControlMeasure.Spec.AlgebraModel N where
  predual : Fixed toAlgebraModel.involutionData ∞ ≃ₗᵢ[ℝ]
    (Fixed toAlgebraModel.involutionData 1 →L[ℝ] ℝ)
  predual_apply : ∀ f g, predual f g = pairing toAlgebraModel.involutionData f g
  densities : CoefficientDensities toAlgebraModel
  coefficients : CoefficientFunctionals toAlgebraModel
  cyclic : CyclicOnResolution toAlgebraModel
  topology : weakStarTopology toAlgebraModel.involutionData = TopologicalSpace.induced
    (fun f => (Ψ f : H →L[ℝ] H)) (OperatorTopology.Spec.WeakTopologyValue ℝ H H)

/-- The full corrected real theorem: the representation is constructed, rather
than assumed. Includes all spectral multiplicities and the zero Hilbert space. -/
def RealNormalControlTopology : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (N : H →L[ℝ] H),
    IsStarNormal N → Nonempty (Model N)

/-- This is only an assembly lemma's type; the unconditional theorem above
is the final source obligation and is not replaced by this implication. -/
def AssemblyFromCyclic : Prop := CyclicConstruction.{u} → RealNormalControlTopology.{u}

end ExpandedFA.VonNeumann.RealNormalControlTopology.Spec
