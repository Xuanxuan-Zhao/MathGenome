import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.RNNonSigmaFiniteFailure

open Set MeasureTheory
open scoped ENNReal
noncomputable section

namespace D11.Ch15.RNNonSigmaFiniteFailure

/-- Borel counting reference on the closed unit interval. -/
def intervalCounting : Measure Interval := Measure.count

/-- Borel Lebesgue target, pulled back along the interval inclusion. -/
def intervalLebesgue : Measure Interval :=
  Measure.comap Subtype.val (volume : Measure ℝ)

/-- The reference atom has infinite mass. -/
def pointReference : Measure Point := (∞ : ℝ≥0∞) • Measure.dirac (0 : Point)

/-- The target atom has unit mass. -/
def pointTarget : Measure Point := Measure.dirac (0 : Point)

theorem interval_borel : (inferInstance : MeasurableSpace Interval) = borel Interval :=
  BorelSpace.measurable_eq

theorem interval_counting_null (E : Set Interval) : intervalCounting E = 0 ↔ E = ∅ :=
  Measure.count_eq_zero_iff

theorem interval_lebesgue_values :
    intervalLebesgue univ = 1 ∧ ∀ x : Interval, intervalLebesgue {x} = 0 := by
  have he := MeasurableEmbedding.subtype_coe (measurableSet_Icc :
    MeasurableSet (Set.Icc (0 : ℝ) 1))
  constructor
  · rw [intervalLebesgue, he.comap_apply]
    simp only [Set.image_univ, Subtype.range_coe_subtype, ofPred_mem_eq]
    change volume (Set.Icc (0 : ℝ) 1) = 1
    simp [Real.volume_Icc]
  · intro x
    rw [intervalLebesgue, he.comap_apply]
    simp

theorem interval_absolute_continuity : intervalLebesgue ≪ intervalCounting := by
  intro E hE
  rw [(interval_counting_null E).mp hE]
  exact measure_empty

/-- Singleton tests force a putative density to be zero at every point. -/
theorem interval_no_density :
    ¬ ∃ h : Interval → ℝ≥0∞, Measurable h ∧
      ∀ E : Set Interval, MeasurableSet E →
        intervalLebesgue E = ∫⁻ x in E, h x ∂intervalCounting := by
  rintro ⟨h, _hm, hd⟩
  have hz : h = 0 := by
    funext x
    have hx := hd {x} (measurableSet_singleton x)
    simpa [interval_lebesgue_values.2 x, lintegral_singleton, intervalCounting,
      Measure.count_singleton] using hx.symm
  have htotal := hd univ MeasurableSet.univ
  simp [hz, interval_lebesgue_values.1] at htotal

/-- A finite-counting-mass cover would make the Lebesgue target null. -/
theorem interval_not_sigmaFinite : ¬ SigmaFinite intervalCounting := by
  intro h
  let : SigmaFinite intervalCounting := h
  let : NullSingletonClass intervalLebesgue := ⟨interval_lebesgue_values.2⟩
  have hz : ∀ n, intervalLebesgue (spanningSets intervalCounting n) = 0 := by
    intro n
    have hfin : (spanningSets intervalCounting n).Finite :=
      Measure.count_apply_lt_top.mp (measure_spanningSets_lt_top intervalCounting n)
    exact hfin.measure_zero intervalLebesgue
  have hunion : intervalLebesgue (⋃ n, spanningSets intervalCounting n) = 0 :=
    measure_iUnion_null hz
  rw [iUnion_spanningSets, interval_lebesgue_values.1] at hunion
  exact one_ne_zero hunion

theorem point_values :
    pointReference {(0 : Point)} = ∞ ∧ pointReference univ = ∞ ∧
      pointTarget {(0 : Point)} = 1 ∧ pointTarget univ = 1 := by
  simp [pointReference, pointTarget]

theorem point_absolute_continuity : pointTarget ≪ pointReference :=
  Measure.absolutelyContinuous_smul (by simp)

/-- The only possible nonnegative integral values are zero and infinity. -/
theorem point_integral (h : Point → ℝ≥0∞) :
    (∫⁻ x, h x ∂pointReference) = if h 0 = 0 then 0 else ∞ := by
  rw [pointReference, lintegral_smul_measure, lintegral_dirac]
  change ∞ * h 0 = _
  split_ifs with hz
  · simp [hz]
  · exact ENNReal.top_mul hz

theorem point_no_density :
    ¬ ∃ h : Point → ℝ≥0∞, Measurable h ∧
      ∀ E : Set Point, MeasurableSet E →
        pointTarget E = ∫⁻ x in E, h x ∂pointReference := by
  rintro ⟨h, _hm, hd⟩
  have ht := hd univ MeasurableSet.univ
  rw [point_values.2.2.2, Measure.restrict_univ, point_integral] at ht
  split_ifs at ht <;> simp_all

/-- Every finite-reference-mass set omits the sole point, so a countable
such cover cannot carry the target. This uses the literal source cover. -/
theorem point_no_sigmaFinite_carrier :
    ¬ ∃ S : Set Point,
      Specs.D11.Ch01.MeasureDefinitions.isSigmaFiniteSet_value pointReference S ∧
      pointTarget Sᶜ = 0 := by
  rintro ⟨S, ⟨_hS, E, hE, hcover⟩, hcarry⟩
  have hmem : (0 : Point) ∈ S := by
    by_contra hnot
    simp [pointTarget, hnot] at hcarry
  rw [← hcover, Set.mem_iUnion] at hmem
  obtain ⟨n, hn⟩ := hmem
  have hinf : pointReference (E n) = ∞ := by
    simp [pointReference, Measure.smul_apply, hn]
  have := (hE n).2.2
  rw [hinf] at this
  exact (lt_irrefl _) this

end D11.Ch15.RNNonSigmaFiniteFailure
