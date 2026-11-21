import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.RealKernelQuantile
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.KernelInterfaces
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.RealDistributionFunctions

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace ProbabilityFoundations.Ch04

universe u
variable {S : Type u} [MeasurableSpace S]

/-- Rational upper level set for the CDF of the fiber. -/
def rationalQuantileSet (K : Kernel S ℝ) (s : S) (u : ℝ) : Set ℝ :=
  Specs.ProbabilityFoundations.Ch04.RealKernelQuantile.rationalQuantileSetValue K s u

/-- The rational generalized inverse on (0,1), extended by zero. -/
noncomputable def realKernelQuantile (K : Kernel S ℝ) (s : S) (u : ℝ) : ℝ :=
  Specs.ProbabilityFoundations.Ch04.RealKernelQuantile.realKernelQuantileValue K s u

variable (K : Kernel S ℝ) [IsMarkovKernel K]

private theorem fiber_cdf_properties (s : S) :
    Ch01.IsRealDistributionFunction (fun t => (K s (Iic t)).toReal) :=
  Ch01.realDistributionFunction_properties (K s)

/-- The tail limits ensure that the rational infimum is finite. -/
theorem rationalQuantileSet_finite (s : S) (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    (rationalQuantileSet K s u).Nonempty ∧ BddBelow (rationalQuantileSet K s u) := by
  have hF := fiber_cdf_properties K s
  constructor
  · obtain ⟨x, hx⟩ := (hF.2.2.2.eventually_const_lt hu1).exists
    obtain ⟨q, hq⟩ := exists_rat_gt x
    exact ⟨q, q, (hx.le.trans (hF.1 hq.le)), rfl⟩
  · obtain ⟨x, hx⟩ := (hF.2.2.1.eventually_lt_const hu0).exists
    refine ⟨x, ?_⟩
    rintro y ⟨q, hq, rfl⟩
    by_contra h
    have hmono := hF.1 (le_of_lt (lt_of_not_ge h))
    exact (not_le_of_gt hx) (hq.trans hmono)

omit [IsMarkovKernel K] in
theorem realKernelQuantile_infimum (s : S) (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    realKernelQuantile K s u = sInf (rationalQuantileSet K s u) := by
  simp only [realKernelQuantile,
    Specs.ProbabilityFoundations.Ch04.RealKernelQuantile.realKernelQuantileValue,
    ite_eq_left (show u ∈ Ioo (0 : ℝ) 1 from ⟨hu0, hu1⟩), rationalQuantileSet]

/-- Right continuity retains the weak inequality, including atoms. -/
theorem realKernelQuantile_le_iff (s : S) (u t : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    realKernelQuantile K s u ≤ t ↔ u ≤ (K s (Iic t)).toReal := by
  rw [realKernelQuantile_infimum K s u hu0 hu1]
  obtain ⟨hne, hb⟩ := rationalQuantileSet_finite K s u hu0 hu1
  have hF := fiber_cdf_properties K s
  constructor
  · intro h
    apply ge_of_tendsto ((hF.2.1 t).mono Ioi_subset_Ici_self)
    filter_upwards [self_mem_nhdsWithin] with x hx
    obtain ⟨y, hy, hyx⟩ := (csInf_lt_iff hb hne).mp (h.trans_lt hx)
    obtain ⟨q, hq, rfl⟩ := hy
    exact hq.trans (hF.1 hyx.le)
  · intro h
    apply le_of_forall_gt_imp_ge_of_dense
    intro b htb
    obtain ⟨q, htq, hqb⟩ := exists_rat_btwn htb
    have hq : (q : ℝ) ∈ rationalQuantileSet K s u :=
      ⟨q, h.trans (hF.1 htq.le), rfl⟩
    exact (csInf_le hb hq).trans hqb.le

omit [IsMarkovKernel K] in
/-- In particular the values at 0 and 1 are both zero. -/
theorem realKernelQuantile_outside (s : S) (u : ℝ) (hu : u ∉ Ioo (0 : ℝ) 1) :
    realKernelQuantile K s u = 0 := by
  simp only [realKernelQuantile,
    Specs.ProbabilityFoundations.Ch04.RealKernelQuantile.realKernelQuantileValue, ite_eq_right hu]

/-- Joint measurability uses only measurable evaluation on each fixed half-line. -/
theorem measurable_realKernelQuantile :
    Measurable (fun p : S × ℝ => realKernelQuantile K p.1 p.2) := by
  let D : Set (S × ℝ) := {p | p.2 ∈ Ioo (0 : ℝ) 1}
  have hD : MeasurableSet D := measurable_snd measurableSet_Ioo
  apply measurable_of_Iic
  intro t
  have hA : MeasurableSet {p : S × ℝ | p.2 ≤ (K p.1 (Iic t)).toReal} :=
    measurableSet_le measurable_snd ((K.measurable_coe measurableSet_Iic).ennreal_toReal.comp
      measurable_fst)
  by_cases ht : 0 ≤ t
  · convert (hD.inter hA).union hD.compl using 1
    ext p
    change (realKernelQuantile K p.1 p.2 ≤ t) ↔ _
    by_cases hp : p ∈ D
    · have hp' : 0 < p.2 ∧ p.2 < 1 := hp
      simp only [mem_union, mem_inter_iff, mem_ofPred_eq, mem_compl_iff, hp, true_and,
        not_true_eq_false, or_false]
      exact realKernelQuantile_le_iff K p.1 p.2 t hp'.1 hp'.2
    · rw [realKernelQuantile_outside K p.1 p.2 hp]
      simp only [ht, mem_union, mem_inter_iff, mem_ofPred_eq, mem_compl_iff, hp, false_and,
        not_false_eq_true, or_true]
  · convert hD.inter hA using 1
    ext p
    change (realKernelQuantile K p.1 p.2 ≤ t) ↔ _
    by_cases hp : p ∈ D
    · have hp' : 0 < p.2 ∧ p.2 < 1 := hp
      simp only [mem_inter_iff, mem_ofPred_eq, hp, true_and]
      exact realKernelQuantile_le_iff K p.1 p.2 t hp'.1 hp'.2
    · rw [realKernelQuantile_outside K p.1 p.2 hp]
      simp only [ht, mem_inter_iff, mem_ofPred_eq, hp, false_and]

/-- Restriction of the joint map to the closed interval in the source. -/
theorem measurable_realKernelQuantile_unitInterval :
    Measurable (fun p : S × Icc (0 : ℝ) 1 => realKernelQuantile K p.1 p.2) :=
  (measurable_realKernelQuantile K).comp
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))

/-- Lebesgue measure on the closed unit interval has total mass one. -/
theorem unitInterval_isProbabilityMeasure :
    IsProbabilityMeasure ((volume : Measure ℝ).restrict (Icc 0 1)) := by
  constructor
  simp

/-- Each fiber sends uniform Lebesgue input to precisely the given probability
measure. Endpoint reassignment is harmless because both endpoints are null. -/
theorem realKernelQuantile_map_uniform (s : S) :
    Measure.map (realKernelQuantile K s) ((volume : Measure ℝ).restrict (Icc 0 1)) = K s := by
  have hm : Measurable (realKernelQuantile K s) :=
    (measurable_realKernelQuantile K).comp (measurable_const.prodMk measurable_id)
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply hm measurableSet_Iic]
  have hopen : ∀ᵐ u ∂(volume : Measure ℝ).restrict (Icc 0 1), u ∈ Ioo (0 : ℝ) 1 := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  have he : (realKernelQuantile K s) ⁻¹' Iic t =ᵐ[(volume : Measure ℝ).restrict (Icc 0 1)]
      Iic (K s (Iic t)).toReal := by
    filter_upwards [hopen] with u hu
    exact propext (realKernelQuantile_le_iff K s u t hu.1 hu.2)
  rw [measure_congr he, Measure.restrict_apply measurableSet_Iic]
  have hF1 : (K s (Iic t)).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (measure_ne_top (K s) univ)
      (measure_mono (subset_univ (Iic t)))
  have hset : Iic (K s (Iic t)).toReal ∩ Icc (0 : ℝ) 1 =
      Icc 0 (K s (Iic t)).toReal := by
    ext u
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans hF1⟩⟩
  rw [hset, Real.volume_Icc, sub_zero, ENNReal.ofReal_toReal (measure_ne_top _ _)]

end ProbabilityFoundations.Ch04
