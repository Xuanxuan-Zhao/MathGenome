import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonPredicates

/-!
Independent statements for paper.tex:5366–5380.
The ambient measurable structure is exactly the Borel sigma-algebra.
The local statement only assumes sigma-finiteness of the specified set;
its mass may be infinite. The two corollaries keep the separate global
sigma-finite-measure and sigma-compact-space hypotheses.
-/
namespace Specs.D11.Ch18.RadonSigmaFiniteInner

open Set MeasureTheory
open scoped ENNReal
universe u

local instance {X : Type u} [TopologicalSpace X] : MeasurableSpace X := borel X

/-- The original local-set theorem, with the finite-measure Borel cover explicit. -/
def countable_union_inner_regular : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)),
    RadonPredicates.isRadonValue μ →
    ∀ (E : Set X), MeasurableSet[borel X] E →
    (∃ A : ℕ → Set X,
      (∀ n, MeasurableSet[borel X] (A n) ∧ μ (A n) < ∞) ∧ (⋃ n, A n) = E) →
    RadonPredicates.compactInnerRegularOnValue μ E

/-- The same assertion on the shared sigma-finite-set interface. -/
def sigmaFiniteSet_inner_regular : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)),
    RadonPredicates.isRadonValue μ →
    ∀ (E : Set X), Ch01.MeasureDefinitions.isSigmaFiniteSet_value μ E →
    RadonPredicates.compactInnerRegularOnValue μ E

/-- Sigma-finite Radon measures are compact-inner and outer regular on every Borel set. -/
def sigmaFinite_fully_regular : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)),
    RadonPredicates.isRadonValue μ → SigmaFinite μ →
    RadonPredicates.isFullyRegularValue μ

/-- Sigma-compactness implies sigma-finiteness and the same full regularity. -/
def sigmaCompact_regular : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SigmaCompactSpace X] (μ : @Measure X (borel X)),
    RadonPredicates.isRadonValue μ →
    SigmaFinite μ ∧ RadonPredicates.isFullyRegularValue μ

end Specs.D11.Ch18.RadonSigmaFiniteInner
