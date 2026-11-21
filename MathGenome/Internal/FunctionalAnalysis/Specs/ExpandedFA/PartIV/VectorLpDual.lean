import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.VectorLpRepresentation
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
Full Bochner duality, `fa2:p4:vector-lp-dual`, paper.tex:20944–21036.
The fixed pairing is evaluation followed by integration, with no conjugation.
Native Bochner Lp consists of a.e. strongly measurable functions modulo ordinary
μ-a.e. equality. No separability assumption on E or completeness of μ is used.
The finite exponent p includes 1, with Hölder conjugate q = infinity.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v

namespace ExpandedFA.PartIV.VectorLpDualSpec
open VectorLpRepresentationSpec

/-- The fixed scalar-linear continuous pairing is an isometric bijection. -/
def IsometricDuality : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E], P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
    ∀ (μ : Measure X) [SigmaFinite μ] (p q : ℝ≥0∞)
      [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q], p ≠ ∞ →
      Isometry (PairingValue (E := E) 𝕜 μ p q) ∧
        Function.Bijective (PairingValue (E := E) 𝕜 μ p q)

/-- A linear isometric equivalence with precisely the stated integral formula. -/
def IsometricEquivalence : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E], P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
    ∀ (μ : Measure X) [SigmaFinite μ] (p q : ℝ≥0∞)
      [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q], p ≠ ∞ →
      ∃ T : Lp (E →L[𝕜] 𝕜) q μ ≃ₗᵢ[𝕜] (Lp E p μ →L[𝕜] 𝕜),
        ∀ (g : Lp (E →L[𝕜] 𝕜) q μ) (f : Lp E p μ),
          Integrable (fun t => g t (f t)) μ ∧ T g f = ∫ t, g t (f t) ∂μ

/-- The norm identity needs no reflexivity assumption. -/
def ExactNorm : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (μ : Measure X) [SigmaFinite μ] (p q : ℝ≥0∞)
      [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q], p ≠ ∞ →
      ∀ g : Lp (E →L[𝕜] 𝕜) q μ, ‖PairingValue 𝕜 μ p q g‖ = ‖g‖

/-- Unique density in the ordinary Bochner quotient, with its exact norm. -/
def Representation : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E], P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
    ∀ (μ : Measure X) [SigmaFinite μ] (p q : ℝ≥0∞)
      [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q], p ≠ ∞ →
      ∀ L : Lp E p μ →L[𝕜] 𝕜, ∃! g : Lp (E →L[𝕜] 𝕜) q μ,
        (∀ f : Lp E p μ, Integrable (fun t => g t (f t)) μ ∧
          L f = ∫ t, g t (f t) ∂μ) ∧ ‖g‖ = ‖L‖

/-- Integral tests determine ordinary a.e. equality, including at q = infinity. -/
def OrdinaryAeUniqueness : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (μ : Measure X) [SigmaFinite μ] (p q : ℝ≥0∞)
      [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q], p ≠ ∞ →
      ∀ g h : Lp (E →L[𝕜] 𝕜) q μ,
        (∀ f : Lp E p μ, (∫ t, g t (f t) ∂μ) = ∫ t, h t (f t) ∂μ) ↔
          (g : X → (E →L[𝕜] 𝕜)) =ᵐ[μ] (h : X → (E →L[𝕜] 𝕜))

/-- A norm-strongly measurable representative exists. Any other a.e. strongly
measurable Lq density agrees a.e., without an assumed norm identity. -/
def StronglyMeasurableRepresentation : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E], P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
    ∀ (μ : Measure X) [SigmaFinite μ] (p q : ℝ≥0∞)
      [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q], p ≠ ∞ →
      ∀ L : Lp E p μ →L[𝕜] 𝕜,
        ∃ g : X → (E →L[𝕜] 𝕜), StronglyMeasurable g ∧ MemLp g q μ ∧
          (∀ f : Lp E p μ, Integrable (fun t => g t (f t)) μ ∧
            L f = ∫ t, g t (f t) ∂μ) ∧
          (eLpNorm g q μ).toReal = ‖L‖ ∧
          ∀ h : X → (E →L[𝕜] 𝕜), MemLp h q μ →
            (∀ f : Lp E p μ, L f = ∫ t, h t (f t) ∂μ) → h =ᵐ[μ] g

end ExpandedFA.PartIV.VectorLpDualSpec
