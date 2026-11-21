import MathGenome.Internal.RealAnalysis.D11.Ch18.RadonPredicates
import MathGenome.Internal.RealAnalysis.D11.Ch18.CompactCutoff
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonSupport
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Support of an arbitrary Radon measure

The arbitrary union of null opens is null by compact-inner regularity on
opens: every compact subset has a finite null-open subcover. We use the
native support theorem, after identifying its support with the literal
complement of that union. No countable base or sigma-finiteness is used.

Every Cc test is scalar integrable. A nonnegative test positive at a support
point has a positive-measure open positivity set. Conversely the compact
cutoff at a point in a null open neighborhood has zero integral.
-/
namespace D11.Ch18.RadonSupport

open Set MeasureTheory
universe u

local instance {Y : Type u} [TopologicalSpace Y] : MeasurableSpace Y := borel Y
local instance {Y : Type u} [TopologicalSpace Y] : BorelSpace Y := ⟨rfl⟩

/-- The canonical arbitrary union of open null sets. -/
abbrev nullOpenUnion {X : Type u} [TopologicalSpace X]
    (μ : @Measure X (borel X)) : Set X :=
  Specs.D11.Ch18.RadonSupport.nullOpenUnionValue μ

/-- Support as defined in the source, using the shared canonical definition. -/
abbrev support {X : Type u} [TopologicalSpace X]
    (μ : @Measure X (borel X)) : Set X :=
  Specs.D11.Ch18.RadonSupport.supportValue μ

/-- Exact bridge to the native neighborhood definition. -/
theorem support_eq_measureSupport {X : Type u} [TopologicalSpace X]
    (μ : @Measure X (borel X)) : support μ = μ.support := by
  unfold support Specs.D11.Ch18.RadonSupport.supportValue
    Specs.D11.Ch18.RadonSupport.nullOpenUnionValue
  rw [← Measure.compl_support_eq_sUnion, compl_compl]

theorem nullOpenUnion_isOpen {X : Type u} [TopologicalSpace X]
    (μ : @Measure X (borel X)) : IsOpen (nullOpenUnion μ) := by
  rw [nullOpenUnion, Specs.D11.Ch18.RadonSupport.nullOpenUnionValue,
    ← Measure.compl_support_eq_sUnion]
  exact Measure.isOpen_compl_support

theorem nullOpenUnion_null {X : Type u} [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] (μ : @Measure X (borel X))
    (hμ : D11.Ch18.isRadon μ) : μ (nullOpenUnion μ) = 0 := by
  rw [nullOpenUnion, Specs.D11.Ch18.RadonSupport.nullOpenUnionValue,
    ← Measure.compl_support_eq_sUnion]
  exact Measure.measure_compl_support_of_innerRegularWRT_isCompact_isOpen
    ((D11.Ch18.compactInnerRegularOpen_iff μ).mp hμ.2.2)

theorem support_isClosed {X : Type u} [TopologicalSpace X]
    (μ : @Measure X (borel X)) : IsClosed (support μ) := by
  rw [support_eq_measureSupport]
  exact Measure.isClosed_support

/-- Integrability on the original Borel domain, including actual measurability. -/
theorem cc_integrable {X : Type u} [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] (μ : @Measure X (borel X))
    (hμ : D11.Ch18.isRadon μ) (f : D11.Ch19.Cc X ℝ) :
    D11.Ch06.ScalarIntegral.scalarIntegrable μ (fun x => f x) := by
  let : IsFiniteMeasureOnCompacts μ := (D11.Ch18.compactFinite_iff μ).mp hμ.1
  exact (D11.Ch06.ScalarIntegral.scalarIntegrable_iff μ _).mpr
    ⟨f.continuous.measurable, f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport⟩

/-- The exact [0,1]-valued compact-support test characterization. -/
theorem mem_support_iff {X : Type u} [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] (μ : @Measure X (borel X))
    (hμ : D11.Ch18.isRadon μ) (x : X) :
    x ∈ support μ ↔
      ∀ f : D11.Ch19.Cc X ℝ, (∀ y, 0 ≤ f y ∧ f y ≤ 1) →
        0 < f x → 0 < ∫ y, f y ∂μ := by
  constructor
  · intro hx f hf hfx
    have hfi := ((D11.Ch06.ScalarIntegral.scalarIntegrable_iff μ _).mp
      (cc_integrable μ hμ f)).2
    apply (integral_pos_iff_support_of_nonneg (fun y => (hf y).1) hfi).mpr
    have hx' : x ∈ μ.support := (support_eq_measureSupport μ) ▸ hx
    have hpos : 0 < μ {y | 0 < f y} :=
      (Measure.mem_support_iff_forall x).mp hx' _
        ((isOpen_lt continuous_const f.continuous).mem_nhds hfx)
    exact hpos.trans_le (measure_mono (fun y hy => ne_of_gt hy))
  · intro htest
    by_contra hx
    have hxN : x ∈ nullOpenUnion μ := by
      simpa only [support, Specs.D11.Ch18.RadonSupport.supportValue,
        mem_compl_iff, not_not] using hx
    obtain ⟨U, ⟨hU, hμU⟩, hxU⟩ := mem_sUnion.mp hxN
    obtain ⟨f, hf, hfx, _, hsub⟩ :=
      D11.Ch18.compact_cutoff X {x} U isCompact_singleton hU
        (singleton_subset_iff.mpr hxU)
    have hzero : μ (Function.support (fun y => f y)) = 0 :=
      measure_mono_null ((subset_closure : Function.support (fun y => f y) ⊆
        closure (Function.support (fun y => f y))).trans hsub) hμU
    have hfi := ((D11.Ch06.ScalarIntegral.scalarIntegrable_iff μ _).mp
      (cc_integrable μ hμ f)).2
    have hpos := (integral_pos_iff_support_of_nonneg (fun y => (hf y).1) hfi).mp
      (htest f hf (by rw [hfx x (mem_singleton x)]; exact zero_lt_one))
    exact (ne_of_gt hpos) hzero

end D11.Ch18.RadonSupport
