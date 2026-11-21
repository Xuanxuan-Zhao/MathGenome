import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.DiscreteDefinitions
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average

/-!
Independent specification of `paper.tex`, Definition `d13:19:preserving-definition`,
and the sums and averages used throughout Chapter 19.

Measure preservation and null invariance also make sense for general measures.
Ergodicity is exactly the zero-one condition for measurable almost-invariant
sets. It does not include measure preservation. On a probability space the
native `Ergodic` structure is equivalent to this condition together with
separately supplied measure preservation; the bridge below also checks the
native null-measurable-set convention.

`IsMixing` records exactly the correlation limit clause; measurability and
preservation are supplied separately when working in the chapter's setting.
In particular no invertibility, completion, or standard Borel assumption is added.
The averages are defined at zero by the library's zero convention; their use
as time averages in the source is at positive natural times.
-/

namespace Specs.D13Unified.Ch19.MeasureDefinitions

noncomputable section

universe u v
open Set Filter MeasureTheory
open scoped Topology symmDiff BigOperators

def PreservesMeasureType := {X : Type u} → [MeasurableSpace X] →
  (X → X) → Measure X → Prop

/-- Measure preservation, using the native pushforward definition. -/
def PreservesMeasure : PreservesMeasureType :=
  fun T μ => MeasurePreserving T μ μ

def InvariantModNullType := {X : Type u} → [MeasurableSpace X] →
  (X → X) → Measure X → Set X → Prop

/-- The null symmetric-difference condition, applied to measurable sets in the paper. -/
def InvariantModNull : InvariantModNullType :=
  fun T μ E => μ ((T ⁻¹' E) ∆ E) = 0

def IsErgodicType := {X : Type u} → [MeasurableSpace X] →
  (X → X) → Measure X → Prop

/-- The paper's zero-one condition. Measurability of T and the probability
hypothesis belong to the setting, as for `IsMixing`; preservation is separate. -/
def IsErgodic : IsErgodicType :=
  fun T μ => ∀ E : Set _, MeasurableSet E → InvariantModNull T μ E →
    μ E = 0 ∨ μ E = 1

def iteratePreimageType := {X : Type u} → (X → X) → ℕ → Set X → Set X

/-- The notation T^(−n)E denotes a preimage, for an arbitrary self-map. -/
def iteratePreimage : iteratePreimageType :=
  fun T n E => (Specs.D13Unified.Ch15.DiscreteDefinitions.iterate T n) ⁻¹' E

def IsMixingType := {X : Type u} → [MeasurableSpace X] →
  (X → X) → Measure X → Prop

/-- The correlation limit for all measurable pairs, without assuming an inverse. -/
def IsMixing : IsMixingType :=
  fun T μ => ∀ A B : Set _, MeasurableSet A → MeasurableSet B →
    Tendsto (fun n : ℕ => μ (A ∩ iteratePreimage T n B)) atTop (𝓝 (μ A * μ B))

def ergodicSumType := {X : Type u} → {E : Type v} → [AddCommMonoid E] →
  (X → X) → (X → E) → ℕ → X → E

/-- Canonical S_n f, valid for real, complex, and vector-valued observables. -/
def ergodicSum : ergodicSumType :=
  fun T f n x => birkhoffSum T f n x

def ergodicAverageType := {X : Type u} → {E : Type v} → [AddCommMonoid E] → [Module ℝ E] →
  (X → X) → (X → E) → ℕ → X → E

/-- Canonical A_n f = n⁻¹ S_n f, with real scalar multiplication. -/
def ergodicAverage : ergodicAverageType :=
  fun T f n x => birkhoffAverage ℝ T f n x

def preservesMeasure_iffStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X),
  PreservesMeasure T μ ↔ Measurable T ∧
    ∀ E : Set X, MeasurableSet E → μ (T ⁻¹' E) = μ E

def invariantModNull_iffStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X) (E : Set X),
  InvariantModNull T μ E ↔ μ ((T ⁻¹' E) ∆ E) = 0

def invariantModNull_iff_aeStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X) (E : Set X),
  InvariantModNull T μ E ↔ T ⁻¹' E =ᵐ[μ] E

def isErgodic_iffStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X)
  [IsProbabilityMeasure μ], IsErgodic T μ ↔
    ∀ E : Set X, MeasurableSet E → InvariantModNull T μ E → μ E = 0 ∨ μ E = 1

def isErgodic_iff_zero_oneStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X)
  [IsProbabilityMeasure μ],
  (IsErgodic T μ ↔ ∀ E : Set X, MeasurableSet E →
    μ ((T ⁻¹' E) ∆ E) = 0 → μ E = 0 ∨ μ E = 1)

/-- Native ergodicity includes preservation and permits null-measurable sets. -/
def nativeErgodic_iffStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X)
  [IsProbabilityMeasure μ], Ergodic T μ ↔ PreservesMeasure T μ ∧ IsErgodic T μ

/-- With preservation given separately, the paper and native predicates agree. -/
def isErgodic_iff_nativeStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X)
  [IsProbabilityMeasure μ], PreservesMeasure T μ → (IsErgodic T μ ↔ Ergodic T μ)

def iteratePreimage_eqStatement : Prop :=
  ∀ {X : Type u} (T : X → X) (n : ℕ) (E : Set X),
  iteratePreimage T n E = T^[n] ⁻¹' E

def mem_iteratePreimageStatement : Prop :=
  ∀ {X : Type u} (T : X → X) (n : ℕ) (E : Set X) (x : X),
  x ∈ iteratePreimage T n E ↔ T^[n] x ∈ E

def iteratePreimage_zeroStatement : Prop :=
  ∀ {X : Type u} (T : X → X) (E : Set X), iteratePreimage T 0 E = E

def iteratePreimage_succStatement : Prop :=
  ∀ {X : Type u} (T : X → X) (n : ℕ) (E : Set X),
  iteratePreimage T (n + 1) E = iteratePreimage T n (T ⁻¹' E)

def isMixing_iffStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X),
  IsMixing T μ ↔ ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
    Tendsto (fun n : ℕ => μ (A ∩ (T^[n] ⁻¹' B))) atTop (𝓝 (μ A * μ B))

def preservesMeasure_iterateStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X),
  PreservesMeasure T μ → ∀ n : ℕ, PreservesMeasure T^[n] μ

def measure_iteratePreimageStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X),
  PreservesMeasure T μ → ∀ (n : ℕ) (E : Set X), MeasurableSet E →
    μ (iteratePreimage T n E) = μ E

def ergodicSum_eq_sumStatement : Prop :=
  ∀ {X : Type u} {E : Type v} [AddCommMonoid E]
  (T : X → X) (f : X → E) (n : ℕ) (x : X),
  ergodicSum T f n x = ∑ j ∈ Finset.range n, f (T^[j] x)

def ergodicSum_zeroStatement : Prop :=
  ∀ {X : Type u} {E : Type v} [AddCommMonoid E]
  (T : X → X) (f : X → E) (x : X), ergodicSum T f 0 x = 0

def ergodicSum_succStatement : Prop :=
  ∀ {X : Type u} {E : Type v} [AddCommMonoid E]
  (T : X → X) (f : X → E) (n : ℕ) (x : X),
  ergodicSum T f (n + 1) x = ergodicSum T f n x + f (T^[n] x)

def ergodicAverage_eqStatement : Prop :=
  ∀ {X : Type u} {E : Type v} [AddCommMonoid E] [Module ℝ E]
  (T : X → X) (f : X → E) (n : ℕ) (x : X),
  ergodicAverage T f n x = (n : ℝ)⁻¹ • ergodicSum T f n x

def ergodicAverage_eq_sumStatement : Prop :=
  ∀ {X : Type u} {E : Type v} [AddCommMonoid E] [Module ℝ E]
  (T : X → X) (f : X → E) (n : ℕ) (x : X),
  ergodicAverage T f n x = (n : ℝ)⁻¹ • ∑ j ∈ Finset.range n, f (T^[j] x)

def ergodicAverage_real_eqStatement : Prop :=
  ∀ {X : Type u} (T : X → X) (f : X → ℝ) (n : ℕ), 0 < n →
  ∀ x : X, ergodicAverage T f n x = (∑ j ∈ Finset.range n, f (T^[j] x)) / (n : ℝ)

def ergodicAverage_oneStatement : Prop :=
  ∀ {X : Type u} {E : Type v} [AddCommMonoid E] [Module ℝ E]
  (T : X → X) (f : X → E) (x : X), ergodicAverage T f 1 x = f x

end

end Specs.D13Unified.Ch19.MeasureDefinitions
