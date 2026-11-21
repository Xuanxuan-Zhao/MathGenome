import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.EMetricSpace.Diam

/-!
Independent specification for paper.tex, Chapter 22, diameter-cover content definition.

An at most countable cover is represented by a sequence with empty entries allowed.
The empty entries are unused slots: their cost is zero. Deleting them gives exactly
a cover by nonempty sets, including the empty cover. The diameter is extended
nonnegative-valued; the finite bound `δ` excludes unbounded covering sets. There
are no measurability, separability, or nonemptiness assumptions on the metric space.
The domain includes scale zero as a harmless extension; the paper uses `0 < δ`.
-/

noncomputable section

open Set Metric
open scoped NNReal ENNReal

universe u

namespace Specs.D11.Ch22

def hausdorffScaleContentType : Type (u + 1) :=
  {X : Type u} → [MetricSpace X] → ℝ≥0 → ℝ≥0 → Set X → ℝ≥0∞

/-- Coefficient-one diameter costs over arbitrary countable covers. Infima with
no admissible cover have value `∞`. Nonempty sets cost one at exponent zero. -/
def hausdorffScaleContentValue : hausdorffScaleContentType :=
  fun {X} _ s δ E =>
    ⨅ (U : ℕ → Set X) (_ : E ⊆ ⋃ n, U n)
      (_ : ∀ n, ediam (U n) ≤ (δ : ℝ≥0∞)),
      ∑' n, ⨆ _ : (U n).Nonempty, ediam (U n) ^ (s : ℝ)

def emptyContentStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (s δ : ℝ≥0),
    hausdorffScaleContentValue s δ (∅ : Set X) = 0

def zeroSingletonStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (δ : ℝ≥0) (x : X),
    hausdorffScaleContentValue 0 δ ({x} : Set X) = 1

def positiveSingletonStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (s δ : ℝ≥0), 0 < s → ∀ x : X,
    hausdorffScaleContentValue s δ ({x} : Set X) = 0

def noCoverStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (s δ : ℝ≥0) (E : Set X),
    (¬ ∃ U : ℕ → Set X, E ⊆ ⋃ n, U n ∧
      ∀ n, ediam (U n) ≤ (δ : ℝ≥0∞)) →
    hausdorffScaleContentValue s δ E = ∞

end Specs.D11.Ch22
