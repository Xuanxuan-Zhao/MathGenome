import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonPredicates
import Mathlib.Topology.Compactness.SigmaCompact

/-!
Independent statements for `paper.tex:5382–5391`.

The primary hypothesis concerns every open subset of an LCH Hausdorff space;
it imposes neither second countability nor metrizability. Measures have exactly
the Borel domain. Full regularity includes all three Radon conditions and
compact inner regularity on every Borel set. The primary conclusion also records
sigma-finiteness, since the hypothesis applied to the whole space gives a compact
cover. Empty spaces and zero measures are included.
-/
namespace Specs.D11.Ch18.SecondCountableBorelRegular

open Set MeasureTheory
universe u

/-- The all-open-sigma-compact theorem, in its original generality. -/
def all_open_sigmaCompact_regular : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X],
    (∀ U : Set X, IsOpen U → IsSigmaCompact U) →
    ∀ μ : @Measure X (borel X), RadonPredicates.compactFiniteValue μ →
      SigmaFinite μ ∧ RadonPredicates.isFullyRegularValue μ

/-- Second countability supplies the primary hypothesis and sigma-finiteness. -/
def second_countable_regular : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X],
    ∀ μ : @Measure X (borel X), RadonPredicates.compactFiniteValue μ →
      SigmaFinite μ ∧ RadonPredicates.isFullyRegularValue μ

end Specs.D11.Ch18.SecondCountableBorelRegular
