import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
Independent statements for `fa2:p4:vector-lp-dual`, paper.tex:20944–21036.
All Lp spaces are the native Bochner spaces of a.e. strongly measurable functions,
modulo ordinary a.e. equality. Duals are continuous scalar-linear duals, including
for complex scalars. The endpoint p = 1, q = infinity is included. No separability
or completeness assumption on the measure is imposed.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
universe u v

namespace ExpandedFA.PartIV.VectorLpRepresentationSpec

abbrev PairingType :=
  ∀ (𝕜 : Type) [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q],
    Lp (E →L[𝕜] 𝕜) q μ →L[𝕜] (Lp E p μ →L[𝕜] 𝕜)

/-- The literal evaluation pairing, with no conjugation. -/
def PairingValue : PairingType.{u,v} := fun 𝕜 _ _ _ _ _ _ μ p q _ _ _ =>
  (ContinuousLinearMap.id 𝕜 _).lpPairing μ q p

def PairingFormula : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q]
    (g : Lp (E →L[𝕜] 𝕜) q μ) (f : Lp E p μ),
    Integrable (fun t => g t (f t)) μ ∧
      PairingValue 𝕜 μ p q g f = ∫ t, g t (f t) ∂μ

def PairingBound : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (g : Lp (E →L[𝕜] 𝕜) q μ),
    ‖PairingValue 𝕜 μ p q g‖ ≤ ‖g‖

/-- The complete stated conclusion, for the fixed integral pairing. -/
def FullDuality : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E], P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
    ∀ (μ : Measure X) [SigmaFinite μ] (p q : ℝ≥0∞)
      [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q], p ≠ ∞ →
      Isometry (PairingValue (E := E) 𝕜 μ p q) ∧
        Function.Surjective (PairingValue (E := E) 𝕜 μ p q)

/-- A finite-measure local density, before the Lq norm upgrade. This is a
construction step, not an extra hypothesis of `FullDuality`. -/
def FiniteDensity : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E], P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
    ∀ (μ : Measure X) [IsFiniteMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
      ∀ L : Lp E p μ →L[𝕜] 𝕜, ∃ g : X → (E →L[𝕜] 𝕜),
        Integrable g μ ∧ ∀ (A : Set X) (hA : MeasurableSet A) (x : E),
          L (indicatorConstLp p hA (measure_ne_top μ A) x) =
            ∫ t in A, g t x ∂μ

end ExpandedFA.PartIV.VectorLpRepresentationSpec
