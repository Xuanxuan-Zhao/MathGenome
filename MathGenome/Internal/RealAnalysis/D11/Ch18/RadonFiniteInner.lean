import MathGenome.Internal.RealAnalysis.D11.Ch18.RadonPredicates
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonFiniteInner

/-!
# Compact inner approximation of finite-mass Borel sets

This is the finite-measure-set stage of paper.tex:5366–5373.
The upstream bridge identifies exactly the three source Radon conditions
with `Measure.Regular`. Mathlib's `Regular` instance then derives
`InnerRegularCompactLTTop`: its proof takes an open finite-mass superset,
approximates that open set from inside, and removes an open cover of the
excess. Thus inner regularity on E is a conclusion, not an extra hypothesis.

All measures below have exactly the Borel domain; no completion or ambient
measurable structure is implicit. The library statements include E empty
and E null and need no positive lower bound on its mass.
-/
namespace D11.Ch18.RadonFiniteInner

open Set MeasureTheory
open scoped ENNReal
universe u

local instance {X : Type u} [TopologicalSpace X] : MeasurableSpace X := borel X

local instance {X : Type u} [TopologicalSpace X] : BorelSpace X := ⟨rfl⟩

/-- A Radon measure is compact-inner regular on every finite-mass Borel set. -/
theorem finite_inner_regular
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borelSpace X)) (hμ : isRadon μ)
    (E : Set X) (hE : MeasurableSet[borelSpace X] E) (hfin : μ E < ∞) :
    compactInnerRegularOn μ E := by
  let : Measure.Regular μ := (isRadon_iff_regular μ).mp hμ
  exact hE.measure_eq_iSup_isCompact_of_ne_top hfin.ne

/-- The finite-set conclusion with an explicit bound on the omitted mass. -/
theorem exists_compact_sdiff_lt
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borelSpace X)) (hμ : isRadon μ)
    (E : Set X) (hE : MeasurableSet[borelSpace X] E) (hfin : μ E < ∞)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ K : Set X, K ⊆ E ∧ IsCompact K ∧ μ (E \ K) < ε := by
  let : Measure.Regular μ := (isRadon_iff_regular μ).mp hμ
  exact hE.exists_isCompact_sdiff_lt hfin.ne hε.ne'

end D11.Ch18.RadonFiniteInner
