import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.ExtremeProbabilities
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.PositiveRadonRepresentation
import Mathlib.MeasureTheory.Measure.Support

noncomputable section

namespace ExpandedFA.PartV.ExtremeProbabilities

open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology
open ExpandedFA.FunctionSpaces.PositiveRadonRepresentationSpec
open ExpandedFA.FunctionSpaces.PositiveRadonRepresentation
open ExtremeProbabilitiesSpec

universe u

variable {K : Type u} [TopologicalSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K]

/-- A probability concentrated at one point is that point's Dirac measure. -/
theorem eq_dirac_of_compl_singleton_null (μ : Measure K) [IsProbabilityMeasure μ]
    (x : K) (h : μ ({x}ᶜ) = 0) : μ = Measure.dirac x := by
  have hs : μ {x} = 1 := (prob_compl_eq_zero_iff (measurableSet_singleton x)).mp h
  calc
    μ = μ.restrict {x} := (Measure.restrict_eq_self_of_ae_mem h).symm
    _ = μ {x} • Measure.dirac x := Measure.restrict_singleton μ x
    _ = Measure.dirac x := by rw [hs, one_smul]

/-- Regularity makes the support conull, even without a countable base. -/
theorem exists_two_support_points (μ : Measure K) [IsProbabilityMeasure μ]
    [μ.Regular] (h : ∀ x, μ ≠ Measure.dirac x) :
    ∃ x ∈ μ.support, ∃ y ∈ μ.support, x ≠ y := by
  have hn : μ.support.Nonempty := by
    by_contra he
    have hem : μ.support = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    have hz := μ.measure_compl_support_of_regular
    simp [hem] at hz
  obtain ⟨x, hx⟩ := hn
  by_contra he
  have hsub : μ.support ⊆ {x} := by
    intro y hy
    by_contra hxy
    exact he ⟨x, hx, y, hy, fun h => hxy (by simp [h])⟩
  apply h x
  apply eq_dirac_of_compl_singleton_null
  exact measure_mono_null (compl_subset_compl.mpr hsub) μ.measure_compl_support_of_regular

theorem intermediate_mass : IntermediateMass.{u} := by
  intro K _ _ _ _ _ _ μ hμ hn
  have : IsProbabilityMeasure μ := hμ.1
  have : μ.Regular := (positiveRadon_iff_regular μ).mp hμ.2
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_two_support_points μ hn
  obtain ⟨U, V, hU, hV, hxU, hyV, hd⟩ := t2_separation hxy
  have hposU : 0 < μ U := (μ.mem_support_iff_forall x).mp hx U (hU.mem_nhds hxU)
  have hposV : 0 < μ V := (μ.mem_support_iff_forall y).mp hy V (hV.mem_nhds hyV)
  refine ⟨U, hU.measurableSet, hposU, ?_⟩
  have hc : μ Uᶜ ≠ 0 := ne_of_gt (hposV.trans_le (measure_mono hd.subset_compl_left))
  exact lt_of_le_of_ne (prob_le_one) (fun he => hc ((prob_compl_eq_zero_iff hU.measurableSet).mpr he))

/-- Dirac measures are regular on Hausdorff Borel spaces. -/
theorem dirac_regular (x : K) : (Measure.dirac x).Regular := by
  have : (Measure.dirac x).InnerRegular := by
    constructor
    intro U hU r hr
    have hx : x ∈ U := by
      by_contra hn
      simp [Measure.dirac_apply, hn] at hr
    refine ⟨{x}, singleton_subset_iff.mpr hx, isCompact_singleton, ?_⟩
    simpa [Measure.dirac_apply_of_mem hx] using hr
  infer_instance

/-- A normalized restriction retains the full source regularity. -/
theorem cond_regular (μ : Measure K) [IsProbabilityMeasure μ] [μ.Regular]
    {A : Set K} (hA : μ A ≠ 0) : (ProbabilityTheory.cond μ A).Regular := by
  have : (μ.restrict A).Regular := Measure.Regular.restrict_of_measure_ne_top (measure_ne_top μ A)
  exact Measure.Regular.smul (ENNReal.inv_ne_top.mpr hA)

theorem restriction_decomposition : RestrictionDecomposition.{u} := by
  intro K _ _ _ _ _ _ μ hμ A hA hpos hlt
  have : IsProbabilityMeasure μ := hμ.1
  have : μ.Regular := (positiveRadon_iff_regular μ).mp hμ.2
  have hpos' : μ Aᶜ ≠ 0 := fun hz => hlt.ne ((prob_compl_eq_zero_iff hA).mp hz)
  let a : ℝ≥0 := (μ A).toNNReal
  let b : ℝ≥0 := (μ Aᶜ).toNNReal
  have ha : (a : ℝ≥0∞) = μ A := ENNReal.coe_toNNReal (measure_ne_top μ A)
  have hb : (b : ℝ≥0∞) = μ Aᶜ := ENNReal.coe_toNNReal (measure_ne_top μ Aᶜ)
  have hap : 0 < a := by
    apply ENNReal.coe_pos.mp
    rw [ha]
    exact hpos
  have hbp : 0 < b := by
    apply ENNReal.coe_pos.mp
    rw [hb]
    exact pos_iff_ne_zero.mpr hpos'
  have hab : a + b = 1 := by
    apply ENNReal.coe_injective
    rw [ENNReal.coe_add, ha, hb, ENNReal.coe_one]
    exact prob_add_prob_compl hA
  have hν : ProbabilityTheory.cond μ A ∈ regularProbabilities K :=
    ⟨ProbabilityTheory.cond_isProbabilityMeasure hpos.ne',
      (positiveRadon_iff_regular _).mpr (cond_regular μ hpos.ne')⟩
  have hη : ProbabilityTheory.cond μ Aᶜ ∈ regularProbabilities K :=
    ⟨ProbabilityTheory.cond_isProbabilityMeasure hpos',
      (positiveRadon_iff_regular _).mpr (cond_regular μ hpos')⟩
  refine ⟨a, b, hap, hbp, hab, ha, hb, hν, hη, ?_, ?_⟩
  · intro he
    have heA := congrArg (fun ν : Measure K => ν A) he
    rw [ProbabilityTheory.cond_apply_self hpos.ne' (measure_ne_top μ A),
      ProbabilityTheory.cond_apply hA.compl] at heA
    simp at heA
  · have hcancel (B : Set K) (hB : μ B ≠ 0) :
        (μ B) • ProbabilityTheory.cond μ B = μ.restrict B := by
      rw [ProbabilityTheory.cond, smul_smul,
        ENNReal.mul_inv_cancel hB (measure_ne_top μ B), one_smul]
    change μ = (a : ℝ≥0∞) • ProbabilityTheory.cond μ A +
      (b : ℝ≥0∞) • ProbabilityTheory.cond μ Aᶜ
    rw [ha, hb, hcancel A hpos.ne', hcancel Aᶜ hpos']
    exact (Measure.restrict_add_restrict_compl hA).symm

theorem convex_probabilities : ConvexProbabilities.{u} := by
  intro K _ _ _ _ _ _ μ hμ ν hν a b _ _ hab
  have : IsProbabilityMeasure μ := hμ.1
  have : IsProbabilityMeasure ν := hν.1
  have : μ.Regular := (positiveRadon_iff_regular μ).mp hμ.2
  have : ν.Regular := (positiveRadon_iff_regular ν).mp hν.2
  have hp : IsProbabilityMeasure (a • μ + b • ν) := by
    constructor
    simp [Measure.add_apply, Measure.smul_apply, ← ENNReal.coe_add, hab]
  refine ⟨hp, (positiveRadon_iff_regular _).mpr ?_⟩
  have : (a • μ).InnerRegular := by
    change ((a : ℝ≥0∞) • μ).InnerRegular
    infer_instance
  have : (b • ν).InnerRegular := by
    change ((b : ℝ≥0∞) • ν).InnerRegular
    infer_instance
  infer_instance

theorem dirac_extreme : DiracExtreme.{u} := by
  intro K _ _ _ _ _ _ x
  refine ⟨⟨inferInstance, (positiveRadon_iff_regular _).mpr (dirac_regular x)⟩, ?_⟩
  intro ν hν η hη hseg
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
  have : IsProbabilityMeasure ν := hν.1
  have hz : (a : ℝ≥0∞) * ν ({x}ᶜ) + (b : ℝ≥0∞) * η ({x}ᶜ) = 0 := by
    have he := congrArg (fun μ : Measure K => μ ({x}ᶜ)) heq
    simpa [Measure.add_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply] using he
  have hνzero : ν ({x}ᶜ) = 0 :=
    (mul_eq_zero.mp (add_eq_zero.mp hz).1).resolve_left (ENNReal.coe_ne_zero.mpr ha.ne')
  exact eq_dirac_of_compl_singleton_null ν x hνzero

theorem extreme_characterization : ExtremeCharacterization.{u} := by
  intro K _ _ _ _ _ _ μ
  constructor
  · intro hμ
    by_contra hn
    have hndirac : ∀ x, μ ≠ Measure.dirac x := by simpa using hn
    obtain ⟨A, hA, hpos, hlt⟩ := intermediate_mass K μ hμ.1 hndirac
    obtain ⟨a, b, ha, hb, hab, _, _, hν, hη, _, heq⟩ :=
      restriction_decomposition K μ hμ.1 A hA hpos hlt
    have he : ProbabilityTheory.cond μ A = μ :=
      hμ.2 hν hη ⟨a, b, ha, hb, hab, heq.symm⟩
    have : IsProbabilityMeasure μ := hμ.1.1
    apply hlt.ne
    rw [← he]
    exact ProbabilityTheory.cond_apply_self hpos.ne' (measure_ne_top μ A)
  · rintro ⟨x, rfl⟩
    exact dirac_extreme K x

end ExpandedFA.PartV.ExtremeProbabilities
