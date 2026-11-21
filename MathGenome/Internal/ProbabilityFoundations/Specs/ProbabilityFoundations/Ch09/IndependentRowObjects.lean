import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Lattice.Fold

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace ProbabilityFoundations.Ch09.IndependentRows

/-- Each finite row has its own specified probability space. There is no relation
between different row spaces or any independence hypothesis across rows. -/
structure Row (r : ℕ → ℕ) (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)] where
  μ : ∀ n, Measure (Ω n)
  probability : ∀ n, IsProbabilityMeasure (μ n)
  X : ∀ n, Fin (r n) → Ω n → ℝ
  measurable : ∀ n j, Measurable (X n j)
  independent : ∀ n, iIndepFun (X n) (μ n)
  centered : ∀ n j, ∫ ω, X n j ω ∂μ n = 0
  second_moment : ∀ n j, MemLp (X n j) 2 (μ n)

attribute [instance] Row.probability

end ProbabilityFoundations.Ch09.IndependentRows

namespace Specs.ProbabilityFoundations.Ch09.IndependentRows
open _root_.ProbabilityFoundations.Ch09.IndependentRows

variable {r : ℕ → ℕ} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- Total variance of the centered row, before normalization. -/
def varianceSum (R : Row r Ω) (n : ℕ) : ℝ :=
  ∑ j, ∫ ω, (R.X n j ω) ^ 2 ∂R.μ n

def scale (R : Row r Ω) (n : ℕ) : ℝ := Real.sqrt (varianceSum R n)

def normalized (R : Row r Ω) (n : ℕ) (j : Fin (r n)) (ω : Ω n) : ℝ :=
  R.X n j ω / scale R n

def variance (R : Row r Ω) (n : ℕ) (j : Fin (r n)) : ℝ :=
  ∫ ω, (normalized R n j ω) ^ 2 ∂R.μ n

def sum (R : Row r Ω) (n : ℕ) (ω : Ω n) : ℝ :=
  ∑ j, normalized R n j ω

/-- The strict tail event, with its indicator applied to the squared summand. -/
def lindeberg (R : Row r Ω) (n : ℕ) (ε : ℝ) : ℝ :=
  ∑ j, ∫ ω, Set.indicator {ω | ε < |normalized R n j ω|}
    (fun ω => (normalized R n j ω) ^ 2) ω ∂R.μ n

/-- Finite maximum with zero adjoined. On nonnegative entries this is the
ordinary maximum; it is zero for an empty row. -/
def rowMax {k : ℕ} (a : Fin k → ℝ) : ℝ :=
  ((Finset.univ.sup fun j => (a j).toNNReal : ℝ≥0) : ℝ)

def maxVariance (R : Row r Ω) (n : ℕ) : ℝ := rowMax (variance R n)

universe u

/-- Independent expected types and values of the candidate definitions. -/
def VarianceSumType := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)], Row r Ω → ℕ → ℝ
def VarianceSumValue : VarianceSumType.{u} := fun {_} {_} [_] R n =>
  ∑ j, ∫ ω, (R.X n j ω)^2 ∂R.μ n

def ScaleType := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)], Row r Ω → ℕ → ℝ
def ScaleValue : ScaleType.{u} := fun {_} {_} [_] R n => Real.sqrt (varianceSum R n)

def NormalizedType := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)], (R : Row r Ω) → (n : ℕ) → Fin (r n) → Ω n → ℝ
def NormalizedValue : NormalizedType.{u} :=
  fun {_} {_} [_] R n j ω => R.X n j ω / scale R n

def VarianceType := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)], Row r Ω → (n : ℕ) → Fin (r n) → ℝ
def VarianceValue : VarianceType.{u} :=
  fun {_} {_} [_] R n j => ∫ ω, (normalized R n j ω)^2 ∂R.μ n

def SumType := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)], Row r Ω → (n : ℕ) → Ω n → ℝ
def SumValue : SumType.{u} := fun {_} {_} [_] R n ω => ∑ j, normalized R n j ω

def LindebergType := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)], Row r Ω → ℕ → ℝ → ℝ
def LindebergValue : LindebergType.{u} := fun {_} {_} [_] R n ε =>
  ∑ j, ∫ ω, Set.indicator {ω | ε < |normalized R n j ω|}
    (fun ω => (normalized R n j ω)^2) ω ∂R.μ n

def RowMaxType := {k : ℕ} → (Fin k → ℝ) → ℝ
def RowMaxValue : RowMaxType := fun {_} a =>
  ((Finset.univ.sup fun j => (a j).toNNReal : ℝ≥0) : ℝ)

def MaxVarianceType := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)], Row r Ω → ℕ → ℝ
def MaxVarianceValue : MaxVarianceType.{u} := fun {_} {_} [_] R n => rowMax (variance R n)

/-- These expected propositions use only the canonical data and library notions. -/
def OriginalIntegrable : Prop := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] (R : Row r Ω) n j, Integrable (R.X n j) (R.μ n)
def SecondMomentIff : Prop := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] (R : Row r Ω) n j,
  MemLp (R.X n j) 2 (R.μ n) ↔ Integrable (fun ω => (R.X n j ω)^2) (R.μ n)
def VarianceSumNonneg : Prop := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] (R : Row r Ω) n, 0 ≤ varianceSum R n
def ScalePositive : Prop := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] (R : Row r Ω) n, 0 < varianceSum R n → 0 < scale R n
def ScaleSquared : Prop := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] (R : Row r Ω) n, (scale R n)^2 = varianceSum R n
def RowNonempty : Prop := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] (R : Row r Ω) n, 0 < varianceSum R n → 0 < r n
def NormalizedMeasurable : Prop := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] (R : Row r Ω) n j, Measurable (normalized R n j)
def NormalizedSecondMoment : Prop := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] (R : Row r Ω) n j,
  MemLp (normalized R n j) 2 (R.μ n)
def NormalizedSquareIntegrable : Prop := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] (R : Row r Ω) n j,
  Integrable (fun ω => (normalized R n j ω)^2) (R.μ n)
def NormalizedIntegrable : Prop := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] (R : Row r Ω) n j,
  Integrable (normalized R n j) (R.μ n)
def NormalizedCentered : Prop := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] (R : Row r Ω) n j,
  ∫ ω, normalized R n j ω ∂R.μ n = 0
def NormalizedIndependent : Prop := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] (R : Row r Ω) n,
  iIndepFun (normalized R n) (R.μ n)
def VarianceFormula : Prop := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] (R : Row r Ω) n j,
  variance R n j = (∫ ω, (R.X n j ω)^2 ∂R.μ n) / varianceSum R n
def VarianceNonneg : Prop := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] (R : Row r Ω) n j, 0 ≤ variance R n j
def SumVarianceOne : Prop := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] (R : Row r Ω) n,
  0 < varianceSum R n → ∑ j, variance R n j = 1

def RowMaxNonneg : Prop := ∀ {k : ℕ} (a : Fin k → ℝ), 0 ≤ rowMax a
def RowMaxEmpty : Prop := ∀ (a : Fin 0 → ℝ), rowMax a = 0
def LeRowMax : Prop := ∀ {k : ℕ} (a : Fin k → ℝ) j, a j ≤ rowMax a
def RowMaxLe : Prop := ∀ {k : ℕ} (a : Fin k → ℝ) b,
  0 ≤ b → (∀ j, a j ≤ b) → rowMax a ≤ b

def MaxVarianceNonneg : Prop := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] (R : Row r Ω) n, 0 ≤ maxVariance R n
def VarianceLeMax : Prop := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] (R : Row r Ω) n j, variance R n j ≤ maxVariance R n

def LindebergIntegrable : Prop := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] (R : Row r Ω) n j ε,
  Integrable (Set.indicator {ω | ε < |normalized R n j ω|}
    (fun ω => (normalized R n j ω)^2)) (R.μ n)
def LindebergNonneg : Prop := ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] (R : Row r Ω) n ε, 0 ≤ lindeberg R n ε

end Specs.ProbabilityFoundations.Ch09.IndependentRows
