import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonPredicates

/-!
Independent statements for the finite-Borel-set stage of
paper.tex:5366–5373 (`d11:18:radon-sigmafinite-inner`).

The measurable domain is exactly the Borel sigma-algebra. The only measure
regularity hypothesis is the source's three-condition Radon predicate.
Neither sigma-finiteness, second countability, nonemptiness, nor finite total
mass is assumed. In particular the finite set E may be empty or null.
-/
namespace Specs.D11.Ch18.RadonFiniteInner

open Set MeasureTheory
open scoped ENNReal
universe u

local instance {X : Type u} [TopologicalSpace X] : MeasurableSpace X := borel X

/-- Compact-inner regularity on any finite-measure Borel set. -/
def finite_inner_regular : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)),
    RadonPredicates.isRadonValue μ →
    ∀ (E : Set X), MeasurableSet[borel X] E → μ E < ∞ →
      RadonPredicates.compactInnerRegularOnValue μ E

/-- Every positive error admits a compact subset with smaller omitted mass. -/
def exists_compact_sdiff_lt : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)),
    RadonPredicates.isRadonValue μ →
    ∀ (E : Set X), MeasurableSet[borel X] E → μ E < ∞ →
    ∀ (ε : ℝ≥0∞), 0 < ε →
      ∃ K : Set X, K ⊆ E ∧ IsCompact K ∧ μ (E \ K) < ε

end Specs.D11.Ch18.RadonFiniteInner
