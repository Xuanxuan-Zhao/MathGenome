import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.VectorMeasureVariation
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.RCLike.Basic

/-! Statements for paper.tex:20926–20940. The domain is the actual unit
interval with its canonical Lebesgue volume, and the range is real or complex L¹,
with equality of functions interpreted almost everywhere. -/
noncomputable section
open Classical MeasureTheory Set
open scoped ENNReal Topology unitInterval

namespace ExpandedFA.PartIV.VectorRnFailureSpec
abbrev Interval := unitInterval
abbrev μ : Measure Interval := volume
abbrev Y (𝕜 : Type*) [RCLike 𝕜] := Lp 𝕜 1 μ

/-- The canonical a.e. class of the indicator; nonmeasurable inputs are
assigned zero, as required by the native vector-measure interface. -/
def IndicatorValue {𝕜 : Type*} [RCLike 𝕜] (A : Set Interval) : Y 𝕜 :=
  if hA : MeasurableSet A then indicatorConstLp 1 hA (measure_ne_top μ A) (1 : 𝕜) else 0

abbrev IndicatorMeasureType (𝕜 : Type*) [RCLike 𝕜] := VectorMeasure Interval (Y 𝕜)

def IndicatorApply : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (m : IndicatorMeasureType 𝕜), (∀ A, m A = IndicatorValue A) →
    ∀ A, MeasurableSet A → (m A : Interval → 𝕜) =ᵐ[μ] A.indicator (fun _ => 1)

def CountableAdditivity : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (m : IndicatorMeasureType 𝕜), (∀ A, m A = IndicatorValue A) →
    ∀ A : ℕ → Set Interval, (∀ n, MeasurableSet (A n)) →
      Pairwise (fun i j => Disjoint (A i) (A j)) →
        HasSum (fun n => m (A n)) (m (⋃ n, A n))

def Variation : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (m : IndicatorMeasureType 𝕜), (∀ A, m A = IndicatorValue A) → m.variation = μ

def AbsoluteContinuity : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (m : IndicatorMeasureType 𝕜), (∀ A, m A = IndicatorValue A) →
    ∀ A, MeasurableSet A → μ A = 0 → m A = 0

/-- Copy a subset into the left or right half of the unit interval.
For b = 0,1 this is its affine image under x ↦ (x+b)/2. -/
def DyadicCopy (b : ℝ) (S : Set ℝ) : Set ℝ := (fun x => 2 * x - b) ⁻¹' S

/-- The usual alternating dyadic half-sets, recursively constructed by
copying the preceding level into both halves. -/
def RealDyadicHalf : ℕ → Set ℝ
  | 0 => Ico 0 (1 / 2)
  | n + 1 => DyadicCopy 0 (RealDyadicHalf n) ∪ DyadicCopy 1 (RealDyadicHalf n)

def DyadicHalf (n : ℕ) : Set Interval := Subtype.val ⁻¹' RealDyadicHalf n

def DyadicSeparation : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜],
  (∀ n, MeasurableSet (DyadicHalf n) ∧ μ (DyadicHalf n) = 1 / 2) ∧
    ∀ i j, i ≠ j → dist (IndicatorValue (𝕜 := 𝕜) (DyadicHalf i))
      (IndicatorValue (DyadicHalf j)) = 1 / 2

def NoncompactRange : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (m : IndicatorMeasureType 𝕜), (∀ A, m A = IndicatorValue A) →
    ¬ IsCompact (closure (range m))

def NoBochnerDensity : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (m : IndicatorMeasureType 𝕜), (∀ A, m A = IndicatorValue A) →
    ¬ ∃ g : Interval → Y 𝕜, Integrable g μ ∧
      ∀ A, MeasurableSet A → m A = ∫ x in A, g x ∂μ

/-- All assertions concern the same explicitly specified vector measure. -/
def Counterexample : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜], ∃ m : IndicatorMeasureType 𝕜,
    (∀ A, m A = IndicatorValue A) ∧ m.variation = μ ∧
    (∀ A, MeasurableSet A → μ A = 0 → m A = 0) ∧
    (¬ IsCompact (closure (range m))) ∧
    (¬ ∃ g : Interval → Y 𝕜, Integrable g μ ∧
      ∀ A, MeasurableSet A → m A = ∫ x in A, g x ∂μ)
end ExpandedFA.PartIV.VectorRnFailureSpec
