import MathGenome.Internal.RealAnalysis.D11.Ch21.CompactContentOuterMeasure
import MathGenome.Internal.RealAnalysis.D11.Ch18.RadonPredicates
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.CompactContentRadonMeasure

/-!
# The compact-content measure is Radon, invariant, and nonzero

This is the regularity and positivity part of the construction in
`paper.tex:5852–5863`. The measure is precisely the Borel restriction of
the outer measure constructed in the preceding goal. Native content
regularity gives finiteness on compacts and the two required approximation
formulas. The content-to-measure inequality supplies positive mass on the
original `K₀`, without assuming equality or performing scalar normalization.
-/
noncomputable section
namespace D11.Ch21.CompactContentRadonMeasure

open Set TopologicalSpace MeasureTheory
open scoped ENNReal
open Specs.D11.Ch21.CompactContentOuterMeasure
universe u

theorem compact_finite : Specs.D11.Ch21.CompactContentRadonMeasure.compact_finite.{u} := by
  intro X _ _ _ c
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  exact (D11.Ch18.compactFinite_iff (borelMeasure_value c)).mpr
    (Content.regular c).toIsFiniteMeasureOnCompacts

theorem outer_regular_borel :
    Specs.D11.Ch21.CompactContentRadonMeasure.outer_regular_borel.{u} := by
  intro X _ _ c
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  exact (D11.Ch18.outerRegularBorel_iff (borelMeasure_value c)).mpr (Content.outerRegular c)

theorem compact_inner_regular_open :
    Specs.D11.Ch21.CompactContentRadonMeasure.compact_inner_regular_open.{u} := by
  intro X _ _ _ c
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  exact (D11.Ch18.compactInnerRegularOpen_iff (borelMeasure_value c)).mpr
    (Content.regular c).innerRegular

theorem content_le_measure :
    Specs.D11.Ch21.CompactContentRadonMeasure.content_le_measure.{u} := by
  intro X _ _ c K
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  rw [CompactContentOuterMeasure.borelMeasure_apply c K K.isCompact.isClosed.measurableSet]
  exact c.le_outerMeasure_compacts K

theorem left_invariant : Specs.D11.Ch21.CompactContentRadonMeasure.left_invariant.{u} := by
  intro G _ _ _ _ c hc a E hE
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  have hImage : MeasurableSet ((fun x => a * x) '' E) :=
    (Homeomorph.mulLeft a).toMeasurableEquiv.measurableSet_image.mpr hE
  rw [CompactContentOuterMeasure.borelMeasure_apply c _ hImage,
    CompactContentOuterMeasure.borelMeasure_apply c _ hE]
  exact CompactContentOuterMeasure.outerMeasure_left_image c hc a E

/-- Radon regularity, left invariance, all compact lower bounds, and positive
finite mass on the same `K₀` used to normalize the content. -/
theorem compact_content_radon_measure :
    Specs.D11.Ch21.CompactContentRadonMeasure.compact_content_radon_measure.{u} := by
  intro G _ _ _ _ _ K₀ h hh
  let c := sourceContent_value K₀ h hh
  let μ := borelMeasure_value c
  have hlaws := CompactContentOuterMeasure.sourceContent_laws K₀ h hh
  have hlower (K : Compacts G) : ENNReal.ofReal (h K) ≤ μ (K : Set G) := by
    rw [← hlaws.1 K]
    exact content_le_measure c K
  have hOne : 1 ≤ μ (K₀ : Set G) := by
    have hK₀ := hlower K₀.toCompacts
    simpa only [hh.2.1, ENNReal.ofReal_one, PositiveCompacts.coe_toCompacts] using hK₀
  refine ⟨⟨compact_finite c, outer_regular_borel c, compact_inner_regular_open c⟩,
    left_invariant c hlaws.2, hlower, ⟨hOne, compact_finite c _ K₀.isCompact⟩, ?_⟩
  intro hzero
  have hmass : μ (K₀ : Set G) = 0 :=
    congrArg (fun ν : @Measure G (borel G) => ν (K₀ : Set G)) hzero
  exact (not_le_of_gt (zero_lt_one : (0 : ℝ≥0∞) < 1)) (hOne.trans hmass.le)

end D11.Ch21.CompactContentRadonMeasure
