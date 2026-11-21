import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.CurveLength
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcFtc
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.PositiveStieltjes
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Independent statements for paper.tex:4304–4332. Euclidean length uses the
shared strict-partition supremum. Ambient functions are tested only on [a,b];
no injectivity or restriction on repeated traversals is imposed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Specs.D11.Ch12.RectifiableCurveBridge

abbrev CoordinatesAC_type := {d : ℕ} →
  (ℝ → EuclideanSpace ℝ (Fin d)) → ℝ → ℝ → Prop

def CoordinatesAC_value : CoordinatesAC_type := fun γ a b =>
  ∀ i, absolutelyContinuousOnIntervalValue (fun t => γ t i) a b

/-- Constant extension of the actual length function, zero to the left of a.
The zero and constant tails introduce no endpoint atoms for continuous curves. -/
abbrev extendedLength_type := {d : ℕ} →
  (ℝ → EuclideanSpace ℝ (Fin d)) → ℝ → ℝ → ℝ → ℝ
noncomputable def extendedLength_value : extendedLength_type := fun γ a b t =>
  realLengthFunction_value γ a (max a (min b t))

abbrev arcLengthMeasure_type := {d : ℕ} →
  (ℝ → EuclideanSpace ℝ (Fin d)) → ℝ → ℝ → Measure ℝ
/-- The guard only totalizes the definition on nonrectifiable/discontinuous
inputs. Its positive-generator condition is proved from the original hypotheses. -/
noncomputable def arcLengthMeasure_value : arcLengthMeasure_type := by
  classical
  exact fun γ a b => if h : PositiveStieltjes.positiveGenerator_value (extendedLength_value γ a b) then
    PositiveStieltjes.stieltjesMeasure_value _ h else 0

abbrev arcLengthIntegral_type := {K : Type} → [RCLike K] → {d : ℕ} →
  (ℝ → EuclideanSpace ℝ (Fin d)) → ℝ → ℝ → (EuclideanSpace ℝ (Fin d) → K) → K
/-- The Stieltjes integral along the parametrized curve, with convention (a,b]. -/
noncomputable def arcLengthIntegral_value : arcLengthIntegral_type := fun γ a b h =>
  ∫ t in Ioc a b, h (γ t) ∂arcLengthMeasure_value γ a b

def rectifiable_iff : Prop :=
  ∀ {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d)) {a b : ℝ}, a < b →
    ContinuousOn γ (Icc a b) →
    (Rectifiable_value γ a b ↔ ∀ i, BV_value (fun t => γ t i) a b)

/-- All coordinates and the vector have classical derivatives on one common
full-measure subset of the interior. The speed is absolutely integrable. -/
def vector_ftc : Prop :=
  ∀ {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d)) {a b : ℝ}, a < b →
    CoordinatesAC_value γ a b →
    IntegrableOn (deriv γ) (Icc a b) ∧
    (∀ᵐ t ∂volume, t ∈ Ioo a b →
      HasDerivAt γ (deriv γ t) t ∧
      ∀ i, HasDerivAt (fun s => γ s i) (deriv γ t i) t) ∧
    ∀ t ∈ Icc a b, γ t = γ a + ∫ s in a..t, deriv γ s

def length_ac : Prop :=
  ∀ {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d)) {a b : ℝ}, a < b →
    CoordinatesAC_value γ a b →
    absolutelyContinuousOnIntervalValue (realLengthFunction_value γ a) a b

def length_formula : Prop :=
  ∀ {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d)) {a b : ℝ}, a < b →
    CoordinatesAC_value γ a b →
    Rectifiable_value γ a b ∧ IntegrableOn (fun t => ‖deriv γ t‖) (Icc a b) ∧
    curveLength_value γ a b = ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) ∧
    ∀ x y : ℝ, a ≤ x → x ≤ y → y ≤ b →
      curveLength_value γ x y = ENNReal.ofReal (∫ t in x..y, ‖deriv γ t‖) ∧
      realLengthFunction_value γ a y - realLengthFunction_value γ a x =
        ∫ t in x..y, ‖deriv γ t‖

def length_function_formula : Prop :=
  ∀ {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d)) {a b : ℝ}, a < b →
    CoordinatesAC_value γ a b → ∀ t ∈ Icc a b,
      realLengthFunction_value γ a t = ∫ s in a..t, ‖deriv γ s‖

def stieltjes_generator : Prop :=
  ∀ {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d)) {a b : ℝ}, a < b →
    ContinuousOn γ (Icc a b) → Rectifiable_value γ a b →
    PositiveStieltjes.positiveGenerator_value (extendedLength_value γ a b)

/-- Exact density of the Stieltjes measure, including zero endpoint masses. -/
def stieltjes_density : Prop :=
  ∀ {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d)) {a b : ℝ}, a < b →
    CoordinatesAC_value γ a b →
    arcLengthMeasure_value γ a b =
      (volume.restrict (Icc a b)).withDensity (fun t => ENNReal.ofReal ‖deriv γ t‖)

def arc_integral_formula : Prop :=
  ∀ {d : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin d)) {a b : ℝ}
    {K : Type} [RCLike K], a < b →
    CoordinatesAC_value γ a b → ∀ h : EuclideanSpace ℝ (Fin d) → K,
    ContinuousOn h (γ '' Icc a b) →
    IntegrableOn (fun t => h (γ t)) (Ioc a b) (arcLengthMeasure_value γ a b) ∧
    IntervalIntegrable (fun t => ‖deriv γ t‖ • h (γ t)) volume a b ∧
    arcLengthIntegral_value γ a b h = ∫ t in a..b, ‖deriv γ t‖ • h (γ t)

end Specs.D11.Ch12.RectifiableCurveBridge
