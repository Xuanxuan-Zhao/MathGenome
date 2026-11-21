import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.CcCzero
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.Caratheodory
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
Independent specification of paper.tex:5512–5530.

The real functional is merely linear and positive; it need not be bounded on
all of Cc. Suprema and infima take values in ENNReal. Support includes closure.
The native Riesz construction supplies canonical bundled objects, and the
expected formula below identifies their outer measure on *every* subset with
the paper's open-cover infimum. The two restrictions have distinct measurable
spaces. `Measure.Regular` means compact-finite, outer regular on Borel sets,
and compact-inner regular on opens, exactly the convention in Chapter 18.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Specs.D11.Ch19.PositiveContentOuterMeasure
universe u

abbrev Positive {X : Type u} [TopologicalSpace X]
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) : Prop :=
  ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ I f

def openContent_type : Type (u + 1) :=
  {X : Type u} → [TopologicalSpace X] →
    (CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) → Set X → ℝ≥0∞

noncomputable def openContent_value : openContent_type.{u} :=
  fun I U => ⨆ f : CompactlySupportedContinuousMap _ ℝ,
    ⨆ (_ : ∀ x, 0 ≤ f x ∧ f x ≤ 1),
      ⨆ (_ : closure {x | f x ≠ 0} ⊆ U), ENNReal.ofReal (I f)

def outerCost_type : Type (u + 1) := openContent_type.{u}

noncomputable def outerCost_value : outerCost_type.{u} :=
  fun I A => ⨅ U : Set _, ⨅ (_ : A ⊆ U), ⨅ (_ : IsOpen U), openContent_value I U

/-- Bundling the same unbounded positive real linear functional. -/
def positiveFunctional_type : Type (u + 1) :=
  {X : Type u} → [TopologicalSpace X] →
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) → Positive I →
      (CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ)

def positiveFunctional_value : positiveFunctional_type.{u} :=
  fun I hI => PositiveLinearMap.mk₀ I (fun f hf => hI f hf)

def borelMeasure_type : Type (u + 1) :=
  {X : Type u} → [TopologicalSpace X] → [T2Space X] → [LocallyCompactSpace X] →
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) → Positive I →
      @Measure X (borel X)

noncomputable def borelMeasure_value : borelMeasure_type.{u} :=
  fun {X} _ _ _ I hI =>
    letI : MeasurableSpace X := borel X
    letI : BorelSpace X := ⟨rfl⟩
    RealRMK.rieszMeasure (positiveFunctional_value I hI)

def outerMeasure_type : Type (u + 1) :=
  {X : Type u} → [TopologicalSpace X] → [T2Space X] → [LocallyCompactSpace X] →
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) → Positive I → OuterMeasure X

noncomputable def outerMeasure_value : outerMeasure_type.{u} :=
  fun I hI => @Measure.toOuterMeasure _ (borel _) (borelMeasure_value I hI)

def caratheodoryMeasure_type : Type (u + 1) :=
  {X : Type u} → [TopologicalSpace X] → [T2Space X] → [LocallyCompactSpace X] →
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) → (hI : Positive I) →
      @Measure X (outerMeasure_value I hI).caratheodory

noncomputable def caratheodoryMeasure_value : caratheodoryMeasure_type.{u} :=
  fun I hI => @_root_.Specs.D11.Ch02.Caratheodory.measure_value _ (outerMeasure_value I hI)

def openContent_eq : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) (hI : Positive I)
    (U : Set X), IsOpen U →
      openContent_value I U = borelMeasure_value I hI U

def outerMeasure_formula : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) (hI : Positive I)
    (A : Set X), outerMeasure_value I hI A = outerCost_value I A

def outerMeasure_open : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) (hI : Positive I)
    (U : Set X), IsOpen U → outerMeasure_value I hI U = openContent_value I U

def empty_values : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) (hI : Positive I),
    openContent_value I ∅ = 0 ∧ outerCost_value I ∅ = 0 ∧ outerMeasure_value I hI ∅ = 0

/-- Explicit outer-measure axioms for the literal infimum, on arbitrary subsets. -/
def outerCost_axioms : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) (_hI : Positive I),
    outerCost_value I ∅ = 0 ∧ Monotone (outerCost_value I) ∧
      ∀ A : ℕ → Set X, outerCost_value I (⋃ n, A n) ≤ ∑' n, outerCost_value I (A n)

def borel_caratheodory : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) (hI : Positive I),
    borel X ≤ (outerMeasure_value I hI).caratheodory

def borel_restriction : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) (hI : Positive I)
    (A : Set X), MeasurableSet[borel X] A →
      borelMeasure_value I hI A = outerCost_value I A

def caratheodory_restriction : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) (hI : Positive I)
    (A : Set X), (outerMeasure_value I hI).IsCaratheodory A →
      caratheodoryMeasure_value I hI A = outerCost_value I A

def caratheodory_complete : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) (hI : Positive I),
    @Measure.IsComplete X (outerMeasure_value I hI).caratheodory
      (caratheodoryMeasure_value I hI)

/-- The three Radon conditions spelled out, without an all-Borel inner claim. -/
def radon : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ) (hI : Positive I),
    (∀ K : Set X, IsCompact K → borelMeasure_value I hI K < ∞) ∧
    (∀ A : Set X, MeasurableSet[borel X] A →
      borelMeasure_value I hI A =
        ⨅ (U : Set X) (_ : A ⊆ U) (_ : IsOpen U), borelMeasure_value I hI U) ∧
    (∀ U : Set X, IsOpen U → borelMeasure_value I hI U =
      ⨆ (K : Set X) (_ : K ⊆ U) (_ : IsCompact K), borelMeasure_value I hI K)

end Specs.D11.Ch19.PositiveContentOuterMeasure
