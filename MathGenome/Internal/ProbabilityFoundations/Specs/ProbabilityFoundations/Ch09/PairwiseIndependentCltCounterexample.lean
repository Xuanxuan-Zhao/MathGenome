import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.UniformIntegrabilityInterfaces
import Mathlib.Combinatorics.Colex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Independent specification of the example in paper.tex:3100–3111.
Coordinates and summands are indexed from zero: coordinate j represents U_{j+1},
and summand k represents X_{k+1}. A binary coefficient vector is represented by
its finite support. The specified product sigma algebra is not completed. -/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Specs.ProbabilityFoundations.Ch09.PairwiseIndependentCltCounterexample

noncomputable section
open Classical

abbrev BitSpace := ℕ → Bool

def fairBitMeasure : Measure Bool :=
  bernoulliMeasure false true ⟨1 / 2, by constructor <;> norm_num⟩

instance : IsProbabilityMeasure fairBitMeasure := by
  unfold fairBitMeasure
  infer_instance

def bitProbability : Measure BitSpace := Measure.infinitePi (fun _ => fairBitMeasure)

instance : IsProbabilityMeasure bitProbability := by
  unfold bitProbability
  infer_instance

/-- The coefficient of coordinate j is one exactly when j belongs to this support. -/
def coefficients (k : ℕ) : Finset ℕ := Finset.equivBitIndices (k + 1)

def character (s : Finset ℕ) (ω : BitSpace) : ℝ :=
  ∏ j ∈ s, if ω j then -1 else 1

def signs (k : ℕ) (ω : BitSpace) : ℝ := character (coefficients k) ω

def partialSum (n : ℕ) (ω : BitSpace) : ℝ := ∑ k ∈ Finset.range n, signs k ω

def blockSize (m : ℕ) : ℕ := 2 ^ m - 1

def zeroPrefix (m : ℕ) : Set BitSpace := {ω | ∀ j < m, ω j = false}

def normalizedSum (n : ℕ) (ω : BitSpace) : ℝ := partialSum n ω / Real.sqrt n

def fairSignMeasure : Measure ℝ :=
  bernoulliMeasure (-1) 1 ⟨1 / 2, by constructor <;> norm_num⟩

instance : IsProbabilityMeasure fairSignMeasure := by
  unfold fairSignMeasure
  infer_instance

/-- An explicit infinite sequence of mutually independent fair bits. -/
def bitConstructionType : Prop :=
  (∀ j, Measurable (fun ω : BitSpace => ω j)) ∧
  iIndepFun (fun j (ω : BitSpace) => ω j) bitProbability ∧
  ∀ j, Measure.map (fun ω : BitSpace => ω j) bitProbability = fairBitMeasure

/-- Exhaustive, nonrepeating enumeration with the required complete initial blocks. -/
def enumerationType : Prop :=
  Function.Injective coefficients ∧
  (∀ k, coefficients k ≠ ∅) ∧
  (∀ s : Finset ℕ, s ≠ ∅ → ∃ k, coefficients k = s) ∧
  ∀ m, (Finset.range (blockSize m)).image coefficients =
    (Finset.range m).powerset.erase ∅

/-- The product notation really is (-1) raised to the binary linear form. -/
def characterFormulaType : Prop :=
  ∀ s ω, character s ω = (-1 : ℝ) ^ (∑ j ∈ s, (ω j).toNat)

def measurabilityType : Prop := ∀ n, Measurable (normalizedSum n)

/-- Identical fair laws and the distinct-indices independence assertion. -/
def signsDistributionType : Prop :=
  (∀ k, Measurable (signs k)) ∧
  (∀ k, Measure.map (signs k) bitProbability = fairSignMeasure) ∧
  Pairwise (fun k l => IndepFun (signs k) (signs l) bitProbability)

def signsMomentsType : Prop :=
  ∀ k, Integrable (signs k) bitProbability ∧
    Integrable (fun ω => (signs k ω) ^ 2) bitProbability ∧
    (∫ ω, signs k ω ∂bitProbability) = 0 ∧
    variance (signs k) bitProbability = 1

/-- Exact identity, also valid for the empty block m=0. -/
def blockSumType : Prop :=
  ∀ m ω, partialSum (blockSize m) ω =
    if ω ∈ zeroPrefix m then (2 : ℝ) ^ m - 1 else -1

/-- The exceptional event and the exceptional value have the specified probabilities. -/
def blockProbabilityType : Prop :=
  (∀ m, MeasurableSet (zeroPrefix m) ∧
    bitProbability (zeroPrefix m) = (1 / 2 : ℝ≥0∞) ^ m) ∧
  ∀ m, 0 < m → bitProbability {ω | partialSum (blockSize m) ω = (2 : ℝ) ^ m - 1} =
    (1 / 2 : ℝ≥0∞) ^ m

def blockConvergenceType : Prop :=
  Specs.ProbabilityFoundations.Ch01.UniformIntegrabilityInterfaces.ConvergesInProbabilityValue
    bitProbability (fun m => normalizedSum (blockSize m)) (fun _ => 0)

/-- Weak convergence is the canonical probability-law topology, whose real tests
are identified with the source convention in the accepted WeakFramework. -/
def noGaussianLimitType : Prop :=
  ¬ Tendsto (fun n => (Measure.map (normalizedSum n) bitProbability).toProbabilityMeasure)
      atTop (𝓝 (gaussianReal 0 1).toProbabilityMeasure)

end
end Specs.ProbabilityFoundations.Ch09.PairwiseIndependentCltCounterexample
