import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.VectorLpDual
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Basic.Real.ConjExponents

/-! Bochner reflexivity, paper.tex `fa2:p4:vector-lp-reflexive`, 21038–21064.
The spaces and the canonical evaluation are the shared native objects. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v
namespace ExpandedFA.PartIV.VectorLpReflexiveSpec
open VectorLpRepresentationSpec
open P1.C04CanonicalMap.Spec

/-- Under the bilinear pairings the actual evaluation map is pointwise J_E. -/
def CanonicalIdentity : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (f : Lp E p μ) (g : Lp (E →L[𝕜] 𝕜) q μ),
    PairingValue 𝕜 μ q p ((CanonicalEvaluationValue 𝕜 E).compLp f) g =
      CanonicalEvaluationValue 𝕜 (Lp E p μ) f (PairingValue 𝕜 μ p q g)

def Reflexivity : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E], IsReflexiveValue 𝕜 E →
    ∀ (μ : Measure X) [SigmaFinite μ] (p : ℝ≥0∞) [Fact (1 ≤ p)],
      1 < p → p ≠ ∞ → IsReflexiveValue 𝕜 (Lp E p μ)

/-- The normalized indicator realizes the closed isometric copy used in the converse. -/
def IndicatorCopy : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∀ (A : Set X) (hA : MeasurableSet A) (hpos : μ A ≠ 0)
      (hfin : μ A ≠ ∞), ∃ I : E →ₗᵢ[𝕜] Lp E p μ,
        (∀ x, I x = (RCLike.ofReal ((μ.real A ^ (1 / p.toReal))⁻¹) : 𝕜) •
          indicatorConstLp p hA hfin x) ∧ IsClosed (Set.range I)

/-- No sigma-finiteness is needed for the converse. -/
def Converse : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    (∃ A : Set X, MeasurableSet A ∧ μ A ≠ 0 ∧ μ A ≠ ∞) →
      IsReflexiveValue 𝕜 (Lp E p μ) → IsReflexiveValue 𝕜 E

/-- The scalar range is reflexive, but both counting-measure endpoints fail. -/
def Endpoints : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜], IsReflexiveValue 𝕜 𝕜 ∧
    ¬ IsReflexiveValue 𝕜 (Lp 𝕜 1 (Measure.count : Measure ℕ)) ∧
    ¬ IsReflexiveValue 𝕜 (Lp 𝕜 ∞ (Measure.count : Measure ℕ))
end ExpandedFA.PartIV.VectorLpReflexiveSpec
