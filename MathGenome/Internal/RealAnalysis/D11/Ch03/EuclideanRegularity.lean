import MathGenome.Internal.RealAnalysis.D11.Ch03.LebesgueMeasures
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.EuclideanRegularity
import Mathlib.MeasureTheory.Measure.Regular

/-! Euclidean regularity for the full Lebesgue measurable domain.

The completed measure and native Borel volume have equal outer evaluations
on every subset: the former lies between the covering outer measure and its
Borel trim. We transfer the open-set regularity of native volume through this
equality. Regularity and sigma-finiteness then give compact inner regularity
on the full Lebesgue domain, using the general regular-measure argument.
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace D11.Ch03.EuclideanRegularity

open LebesgueMeasures

/-- Equality of outer evaluations, including on nonmeasurable subsets. This
does not identify the Borel and Lebesgue measurable spaces. -/
theorem lebesgue_eq_volume (d : ℕ) [NeZero d] (E : Set (Point d)) :
    lebesgue d E = volume E := by
  apply le_antisymm
  · calc
      lebesgue d E ≤ (lebesgue d).trim (native_borel_le d) E :=
        le_trim (native_borel_le d)
      _ = volume E := congrArg (fun μ : Measure (Point d) => μ E)
        (borel_restriction d (native_borel_le d))
  · rw [native_outer_agreement d E]
    exact @le_toMeasure_apply (Point d) (lebesgueSpace d)
      (OuterVolume.outerVolume d) le_rfl E

/-- Open and closed Euclidean sets are measurable in the completed structure. -/
instance opensMeasurable (d : ℕ) [NeZero d] :
    @OpensMeasurableSpace (Point d) _ (lebesgueSpace d) := by
  let : MeasurableSpace (Point d) := lebesgueSpace d
  exact ⟨borel_le_lebesgue d⟩

/-- Transfer only the three defining regularity properties through equality
of outer evaluations; no Borel-space instance is asserted for the completion. -/
instance regular (d : ℕ) [NeZero d] :
    @Measure.Regular (Point d) (lebesgueSpace d) _ (lebesgue d) := by
  have hfinite (K : Set (Point d)) (hK : IsCompact K) :
      volume K < ∞ := hK.measure_lt_top
  have houter (E : Set (Point d)) (r : ℝ≥0∞) (hr : volume E < r) :
      ∃ U, U ⊇ E ∧ IsOpen U ∧ volume U < r :=
    E.exists_isOpen_lt_of_lt r hr
  have hinner (U : Set (Point d)) (hU : IsOpen U) (r : ℝ≥0∞)
      (hr : r < volume U) : ∃ K, K ⊆ U ∧ IsCompact K ∧ r < volume K :=
    Measure.Regular.innerRegular (μ := (volume : Measure (Point d))) hU r hr
  let : MeasurableSpace (Point d) := lebesgueSpace d
  refine { lt_top_of_isCompact := ?_, outerRegular := ?_, innerRegular := ?_ }
  · intro K hK
    rw [lebesgue_eq_volume]
    exact hfinite K hK
  · intro E _ r hr
    rw [lebesgue_eq_volume] at hr
    obtain ⟨U, hEU, hU, hUr⟩ :=
      houter E r hr
    exact ⟨U, hEU, hU, by rwa [lebesgue_eq_volume]⟩
  · intro U hU r hr
    rw [lebesgue_eq_volume] at hr
    obtain ⟨K, hKU, hK, hrK⟩ :=
      hinner U hU r hr
    exact ⟨K, hKU, hK, by rwa [lebesgue_eq_volume]⟩

instance sigmaFinite (d : ℕ) [NeZero d] :
    @SigmaFinite (Point d) (lebesgueSpace d) (lebesgue d) :=
  lebesgue_sigmaFinite d

theorem outer_regularity : Specs.D11.Ch03.EuclideanRegularity.outer_regularity := by
  intro d _ E _
  let : MeasurableSpace (Point d) := lebesgueSpace d
  exact E.measure_eq_iInf_isOpen (lebesgue d)

theorem inner_regularity : Specs.D11.Ch03.EuclideanRegularity.inner_regularity := by
  intro d _ E hE
  let : MeasurableSpace (Point d) := lebesgueSpace d
  change MeasurableSet E at hE
  change lebesgue d E = _
  exact hE.measure_eq_iSup_isCompact (lebesgue d)

theorem compact_open_approximation :
    Specs.D11.Ch03.EuclideanRegularity.compact_open_approximation := by
  intro d _ E hE hfin ε hε
  let : MeasurableSpace (Point d) := lebesgueSpace d
  have hδ : ENNReal.ofReal (ε / 2) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (half_pos hε))
  obtain ⟨U, hEU, hU, _, hUE⟩ :=
    hE.exists_isOpen_sdiff_lt (μ := lebesgue d) hfin.ne hδ
  obtain ⟨K, hKE, hK, hEK⟩ :=
    hE.exists_isCompact_sdiff_lt (μ := lebesgue d) hfin.ne hδ
  refine ⟨K, U, hK, hKE, hEU, hU, ?_⟩
  have hcover : U \ K ⊆ (U \ E) ∪ (E \ K) := by
    intro x hx
    by_cases hxE : x ∈ E
    · exact Or.inr ⟨hxE, hx.2⟩
    · exact Or.inl ⟨hx.1, hxE⟩
  calc
    lebesgue d (U \ K) ≤ lebesgue d (U \ E) + lebesgue d (E \ K) :=
      (measure_mono hcover).trans (measure_union_le _ _)
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      ENNReal.add_lt_add hUE hEK
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
      congr 1
      exact add_halves ε

end D11.Ch03.EuclideanRegularity
