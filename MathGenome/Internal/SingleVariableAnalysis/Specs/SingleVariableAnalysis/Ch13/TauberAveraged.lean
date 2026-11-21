import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Tauber

/-!
Independent statements for the averaged corollary of K03.13.tauber,
paper.tex:1493–1516. Indices include zero; its zero contribution to T_n
makes the range sum exactly ∑_{k=1}^n k a_k. The hypothesis is the
signed/complex average, not an average of magnitudes or a bound on n a_n.
The auxiliary coefficients are fixed explicitly, including b₀=a₀.
-/
namespace Specs.SingleVariableAnalysis.Ch13.TauberAveraged
open Specs.SingleVariableAnalysis.Ch01.SequenceLimit
open Specs.SingleVariableAnalysis.Ch11.PartialSums
open Specs.SingleVariableAnalysis.Ch13.PowerSeries
open scoped BigOperators Topology

noncomputable def weightedTotal {K : Type*} [Semiring K] (a : ℕ → K) (n : ℕ) : K :=
  ∑ k ∈ Finset.range (n + 1), (k : K) * a k

noncomputable def transformed {K : Type*} [Field K] (a : ℕ → K) (n : ℕ) : K :=
  if n = 0 then a 0 else weightedTotal a n / ((n : K) * ((n : K) + 1))

def realFiniteIdentity : Prop :=
  ∀ (a : ℕ → ℝ) (n : ℕ),
    realPartialSumValue a n - realPartialSumValue (transformed a) n =
      weightedTotal a n / ((n : ℝ) + 1)

def complexFiniteIdentity : Prop :=
  ∀ (a : ℕ → ℂ) (n : ℕ),
    complexPartialSumValue a n - complexPartialSumValue (transformed a) n =
      weightedTotal a n / ((n : ℂ) + 1)

def realTransformedCondition : Prop :=
  ∀ a : ℕ → ℝ, realSequenceConvergesValue (fun n => weightedTotal a n / (n : ℝ)) 0 →
    realSequenceConvergesValue (fun n => (n : ℝ) * transformed a n) 0

def complexTransformedCondition : Prop :=
  ∀ a : ℕ → ℂ, complexSequenceConvergesValue (fun n => weightedTotal a n / (n : ℂ)) 0 →
    complexSequenceConvergesValue (fun n => (n : ℂ) * transformed a n) 0

noncomputable def realInterior : Prop :=
  ∀ a : ℕ → ℝ, realSequenceConvergesValue (fun n => weightedTotal a n / (n : ℝ)) 0 →
    ∀ r : ℝ, 0 < r → r < 1 →
      RealPowerSeriesAbsolutelyConvergesValue a 0 r ∧
      RealPowerSeriesHasSumValue a 0 r (∑' n, a n * r ^ n)

noncomputable def complexInterior : Prop :=
  ∀ a : ℕ → ℂ, complexSequenceConvergesValue (fun n => weightedTotal a n / (n : ℂ)) 0 →
    ∀ r : ℝ, 0 < r → r < 1 →
      ComplexPowerSeriesAbsolutelyConvergesValue a 0 (r : ℂ) ∧
      ComplexPowerSeriesHasSumValue a 0 (r : ℂ) (∑' n, a n * (r : ℂ) ^ n)

noncomputable def realTransformedInterior : Prop :=
  ∀ a : ℕ → ℝ, realSequenceConvergesValue (fun n => weightedTotal a n / (n : ℝ)) 0 →
    ∀ r : ℝ, 0 < r → r < 1 →
      RealPowerSeriesAbsolutelyConvergesValue (transformed a) 0 r ∧
      RealPowerSeriesHasSumValue (transformed a) 0 r (∑' n, transformed a n * r ^ n)

noncomputable def complexTransformedInterior : Prop :=
  ∀ a : ℕ → ℂ, complexSequenceConvergesValue (fun n => weightedTotal a n / (n : ℂ)) 0 →
    ∀ r : ℝ, 0 < r → r < 1 →
      ComplexPowerSeriesAbsolutelyConvergesValue (transformed a) 0 (r : ℂ) ∧
      ComplexPowerSeriesHasSumValue (transformed a) 0 (r : ℂ)
        (∑' n, transformed a n * (r : ℂ) ^ n)

noncomputable def realAbelTransfer : Prop :=
  ∀ (a : ℕ → ℝ) (S : ℝ),
    realSequenceConvergesValue (fun n => weightedTotal a n / (n : ℝ)) 0 →
    Filter.Tendsto (fun r : ℝ => ∑' n, a n * r ^ n) (𝓝[<] 1) (𝓝 S) →
    Filter.Tendsto (fun r : ℝ => ∑' n, transformed a n * r ^ n) (𝓝[<] 1) (𝓝 S)

noncomputable def complexAbelTransfer : Prop :=
  ∀ (a : ℕ → ℂ) (S : ℂ),
    complexSequenceConvergesValue (fun n => weightedTotal a n / (n : ℂ)) 0 →
    Filter.Tendsto (fun r : ℝ => ∑' n, a n * (r : ℂ) ^ n) (𝓝[<] 1) (𝓝 S) →
    Filter.Tendsto (fun r : ℝ => ∑' n, transformed a n * (r : ℂ) ^ n) (𝓝[<] 1) (𝓝 S)

noncomputable def realTauber : Prop :=
  ∀ (a : ℕ → ℝ) (S : ℝ),
    realSequenceConvergesValue (fun n => weightedTotal a n / (n : ℝ)) 0 →
    Filter.Tendsto (fun r : ℝ => ∑' n, a n * r ^ n) (𝓝[<] 1) (𝓝 S) →
    realSeriesHasSumValue a S

noncomputable def complexTauber : Prop :=
  ∀ (a : ℕ → ℂ) (S : ℂ),
    complexSequenceConvergesValue (fun n => weightedTotal a n / (n : ℂ)) 0 →
    Filter.Tendsto (fun r : ℝ => ∑' n, a n * (r : ℂ) ^ n) (𝓝[<] 1) (𝓝 S) →
    complexSeriesHasSumValue a S

end Specs.SingleVariableAnalysis.Ch13.TauberAveraged
