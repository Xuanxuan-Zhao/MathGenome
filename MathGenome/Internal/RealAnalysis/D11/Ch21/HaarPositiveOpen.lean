import MathGenome.Internal.RealAnalysis.D11.Ch21.HaarDefinition
import MathGenome.Internal.RealAnalysis.D11.Ch18.RadonSupport
import MathGenome.Internal.RealAnalysis.D11.Ch19.CcCzero
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.HaarPositiveOpen
import Mathlib.MeasureTheory.Group.Action

/-!
# Haar positivity and full support

The finite-translate compact-cover argument is the native theorem for a
nonzero regular measure invariant under a minimal group action. Left and
right multiplication are transitive actions (the latter by the opposite
group). We bridge the source's Borel image invariance to those actions.
Only compact-inner regularity on opens is required, not all-Borel inner
regularity or any countability hypothesis.
-/
namespace D11.Ch21.HaarPositiveOpen

open MeasureTheory
universe u

local instance {G : Type u} [TopologicalSpace G] : MeasurableSpace G := borel G
local instance {G : Type u} [TopologicalSpace G] : BorelSpace G := ⟨rfl⟩

variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

private theorem openPos (μ : @Measure G (borel G))
    (hμ : isLeftHaarMeasure μ ∨ isRightHaarMeasure μ) :
    Measure.IsOpenPosMeasure μ := by
  rcases hμ with hμ | hμ
  · let : Measure.Regular μ := (D11.Ch18.isRadon_iff_regular μ).mp hμ.2.1
    let : SMulInvariantMeasure G G μ :=
      ((smulInvariantMeasure_tfae G μ).out 3 1).mp (by
        intro a E hE
        change μ ((fun x => a * x) '' E) = μ E
        exact hμ.2.2 a E hE)
    exact ⟨fun U hU hn => (measure_isOpen_pos_of_smulInvariant_of_ne_zero G hμ.1 hU hn).ne'⟩
  · let : Measure.Regular μ := (D11.Ch18.isRadon_iff_regular μ).mp hμ.2.1
    let : SMulInvariantMeasure Gᵐᵒᵖ G μ :=
      ((smulInvariantMeasure_tfae Gᵐᵒᵖ μ).out 3 1).mp (by
        intro a E hE
        change μ ((fun x => x * a.unop) '' E) = μ E
        exact hμ.2.2 a.unop E hE)
    exact ⟨fun U hU hn =>
      (measure_isOpen_pos_of_smulInvariant_of_ne_zero Gᵐᵒᵖ hμ.1 hU hn).ne'⟩

/-- Haar measures give positive mass to every nonempty open set. -/
theorem positive_open (μ : @Measure G (borel G))
    (hμ : isLeftHaarMeasure μ ∨ isRightHaarMeasure μ)
    (U : Set G) (hU : IsOpen U) (hne : U.Nonempty) : 0 < μ U := by
  let := openPos μ hμ
  exact hU.measure_pos μ hne

/-- Nonzero nonnegative Cc functions have a defined, strictly positive integral. -/
theorem integral_pos (μ : @Measure G (borel G))
    (hμ : isLeftHaarMeasure μ ∨ isRightHaarMeasure μ)
    (f : D11.Ch19.Cc G ℝ) (hf : ∀ x, 0 ≤ f x) (hne : f ≠ 0) :
    D11.Ch06.ScalarIntegral.scalarIntegrable μ (fun x => f x) ∧
      0 < ∫ x, f x ∂μ := by
  have hradon : D11.Ch18.isRadon μ := hμ.elim (fun h => h.2.1) (fun h => h.2.1)
  refine ⟨D11.Ch18.RadonSupport.cc_integrable μ hradon f, ?_⟩
  let := openPos μ hμ
  let : IsFiniteMeasureOnCompacts μ := (D11.Ch18.compactFinite_iff μ).mp hradon.1
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (DFunLike.ext _ _ h)
  exact f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    f.hasCompactSupport hf hx

/-- The source's canonical support is the entire group. -/
theorem full_support (μ : @Measure G (borel G))
    (hμ : isLeftHaarMeasure μ ∨ isRightHaarMeasure μ) :
    D11.Ch18.RadonSupport.support μ = Set.univ := by
  let := openPos μ hμ
  rw [D11.Ch18.RadonSupport.support_eq_measureSupport]
  exact Measure.support_eq_univ

end D11.Ch21.HaarPositiveOpen
