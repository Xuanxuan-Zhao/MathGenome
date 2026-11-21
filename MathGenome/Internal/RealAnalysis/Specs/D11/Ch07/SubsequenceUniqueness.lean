import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.ConvergenceDefinitions
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
Independent statements for paper.tex:2157–2175, “Subsequences and uniqueness”.

The conclusions use the shared ordinary a.e. predicates: an exceptional set
has a measurable null envelope in the original sigma-algebra. Convergence in
measure uses the shared global, strict-deviation definition, with ENNReal-valued
measures. There are no finiteness, sigma-finiteness or completeness assumptions.

The assertions hold for any normed additive commutative group, with no function
measurability needed. This stronger form specializes directly to the source's
finite measurable real and complex functions: both fields have the required
group structure, and their norms are absolute value and modulus respectively.
-/

open Filter MeasureTheory
open scoped Topology

universe u v

namespace Specs.D11.Ch07.SubsequenceUniqueness

open Specs.D11.Ch07.ConvergenceDefinitions
open Specs.D11.Ch04.AeCommonException

/-- The strict-deviation definition agrees with the library's non-strict one. -/
def inMeasureConverges_iff_native : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (f : ℕ → X → E) (g : X → E),
    inMeasureConverges_value μ f g ↔ TendstoInMeasure μ f atTop g

/-- A genuine subsequence, with strictly increasing natural indices. -/
def exists_ae_subsequence : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (f : ℕ → X → E) (g : X → E),
    inMeasureConverges_value μ f g →
      ∃ ns : ℕ → ℕ, StrictMono ns ∧
        aeConverges_value μ (fun n => f (ns n)) g

/-- The limit is unique modulo ordinary almost-everywhere equality. -/
def limit_unique : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (f : ℕ → X → E) (g h : X → E),
    inMeasureConverges_value μ f g → inMeasureConverges_value μ f h →
      aeEq_value μ g h

end Specs.D11.Ch07.SubsequenceUniqueness
