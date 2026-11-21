import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.ExtremeScalarMeasures
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.ExtremeProbabilities
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.InnerProductSpace.Convex

noncomputable section
namespace ExpandedFA.PartV.ExtremeScalarMeasures
open Set MeasureTheory
open scoped ENNReal NNReal
open ExtremeScalarMeasuresSpec
open ExpandedFA.FunctionSpaces.ScalarRieszMarkovSpec
open ExpandedFA.FunctionSpaces.PositiveRadonRepresentationSpec
open ExpandedFA.FunctionSpaces.PositiveRadonRepresentation
universe u
variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K]
variable {𝕜 : Type*} [RCLike 𝕜]

omit [CompactSpace K] [T2Space K] [BorelSpace K] in
lemma finite_variation (ν : VectorMeasure K 𝕜) (hν : FiniteScalarRadon ν) :
    IsFiniteMeasure ν.variation := ⟨hν.1⟩

omit [CompactSpace K] [T2Space K] [BorelSpace K] in
lemma radon_smul (ν : VectorMeasure K 𝕜) (hν : FiniteScalarRadon ν) (c : ℝ) :
    FiniteScalarRadon (c • ν) := by
  have := finite_variation ν hν
  have : ν.variation.Regular := (positiveRadon_iff_regular _).mp hν.2
  refine ⟨measure_lt_top _ _, (positiveRadon_iff_regular _).mpr ?_⟩
  rw [VectorMeasure.variation_smul]
  infer_instance

omit [CompactSpace K] in
lemma radon_restrict (ν : VectorMeasure K 𝕜) (hν : FiniteScalarRadon ν)
    (A : Set K) (hA : MeasurableSet A) : FiniteScalarRadon (ν.restrict A) := by
  have := finite_variation ν hν
  have : ν.variation.Regular := (positiveRadon_iff_regular _).mp hν.2
  refine ⟨measure_lt_top _ _, (positiveRadon_iff_regular _).mpr ?_⟩
  rw [VectorMeasure.variation_restrict hA]
  exact Measure.Regular.restrict_of_measure_ne_top (measure_ne_top _ _)

omit [CompactSpace K] in
lemma radon_dirac (x : K) (z : 𝕜) : FiniteScalarRadon (VectorMeasure.dirac x z) := by
  have : (Measure.dirac x).Regular := ExtremeProbabilities.dirac_regular x
  refine ⟨measure_lt_top _ _, (positiveRadon_iff_regular _).mpr ?_⟩
  rw [VectorMeasure.variation_dirac, enorm_eq_nnnorm]
  exact Measure.Regular.smul ENNReal.coe_ne_top

omit [CompactSpace K] [T2Space K] [BorelSpace K] in
lemma zero_mem : (0 : VectorMeasure K 𝕜) ∈ measureBall K 𝕜 := by
  refine ⟨⟨by simp, ?_⟩, by simp⟩
  apply (positiveRadon_iff_regular _).mpr
  simp only [VectorMeasure.variation_zero]
  infer_instance

omit [CompactSpace K] in
lemma dirac_mem (x : K) (z : 𝕜) (hz : ‖z‖ = 1) :
    VectorMeasure.dirac x z ∈ measureBall K 𝕜 := by
  refine ⟨radon_dirac x z, ?_⟩
  simp [VectorMeasure.variation_dirac, enorm_eq_nnnorm, show ‖z‖₊ = 1 by exact NNReal.eq hz]

omit [CompactSpace K] in
/-- Null remaining variation, rather than zero scalar mass, forces concentration. -/
lemma eq_dirac_of_compl_variation_zero (ν : VectorMeasure K 𝕜) (x : K)
    (h : ν.variation ({x}ᶜ) = 0) : ν = VectorMeasure.dirac x (ν {x}) := by
  have hr : ν.restrict ({x}ᶜ) = 0 := by
    apply VectorMeasure.variation_eq_zero.mp
    rw [VectorMeasure.variation_restrict (measurableSet_singleton x).compl]
    exact Measure.restrict_eq_zero.mpr h
  have he := VectorMeasure.restrict_add_restrict_compl (v := ν) (measurableSet_singleton x)
  simpa [hr] using he.symm

omit [CompactSpace K] in
lemma singleton_norm_one (ν : VectorMeasure K 𝕜) (hν : ν ∈ measureBall K 𝕜)
    (x : K) (h : ‖ν {x}‖ = 1) : ν = VectorMeasure.dirac x (ν {x}) := by
  apply eq_dirac_of_compl_variation_zero
  have hs : ν.variation {x} = 1 := by
    rw [VectorMeasure.variation_apply_singleton, enorm_eq_nnnorm]
    exact congrArg (fun t : ℝ≥0 => (t : ℝ≥0∞)) (NNReal.eq h)
  have he := measure_add_measure_compl (μ := ν.variation) (measurableSet_singleton x)
  have hh : 1 + ν.variation ({x}ᶜ) ≤ 1 := by rw [← hs, he]; simpa [hs] using hν.2
  have hh' : ν.variation ({x}ᶜ) ≤ 0 :=
    (ENNReal.add_le_add_iff_left (by simp : (1 : ℝ≥0∞) ≠ ∞)).mp (by simpa using hh)
  exact le_zero_iff.mp hh'

omit [CompactSpace K] [T2Space K] [BorelSpace K] in
/-- Evaluation at a singleton lands in the ordinary scalar closed unit ball. -/
lemma singleton_bound (ν : VectorMeasure K 𝕜) (hν : ν ∈ measureBall K 𝕜) (x : K) :
    ‖ν {x}‖ ≤ 1 := by
  have := finite_variation ν hν.1
  calc
    ‖ν {x}‖ ≤ ν.variation.real {x} := VectorMeasure.norm_measure_le_variation
    _ ≤ ν.variation.real univ := measureReal_mono (subset_univ _)
    _ ≤ 1 := by exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using hν.2)

theorem dirac_extreme (x : K) (z : 𝕜) (hz : ‖z‖ = 1) :
    VectorMeasure.dirac x z ∈ (measureBall K 𝕜).extremePoints ℝ := by
  refine ⟨dirac_mem x z hz, ?_⟩
  intro ν hν η hη hseg
  have hscalar : z ∈ (Metric.closedBall (0 : 𝕜) 1).extremePoints ℝ := by
    apply StrictConvexSpace.sphere_subset_extremePoints_closedBall 0 one_ne_zero
    simpa [Metric.mem_sphere, dist_zero_right] using hz
  obtain ⟨a, b, ha, hb, hab, he⟩ := hseg
  have he' : a • ν {x} + b • η {x} = z := by
    have := congrArg (fun μ : VectorMeasure K 𝕜 => μ {x}) he
    simpa using this
  have hn : ν {x} = z := hscalar.2
    (by simpa [Metric.mem_closedBall, dist_zero_right] using singleton_bound ν hν x)
    (by simpa [Metric.mem_closedBall, dist_zero_right] using singleton_bound η hη x)
    ⟨a, b, ha, hb, hab, he'⟩
  simpa [hn] using singleton_norm_one ν hν x (hn ▸ hz)

omit [TopologicalSpace K] [CompactSpace K] [T2Space K] [BorelSpace K] in
lemma variation_real_smul (ν : VectorMeasure K 𝕜) (c : ℝ) (A : Set K) :
    (c • ν).variation.real A = |c| * ν.variation.real A := by
  simp [VectorMeasure.variation_smul, Real.norm_eq_abs]

lemma normalize_mass (ν : VectorMeasure K 𝕜) (hν : FiniteScalarRadon ν)
    (ht : 0 < ν.variation.real univ) :
    ((ν.variation.real univ)⁻¹ • ν).variation univ = 1 := by
  have h := radon_smul ν hν ((ν.variation.real univ)⁻¹)
  have := finite_variation _ h
  apply (ENNReal.toReal_eq_one_iff _).mp
  change ((ν.variation.real univ)⁻¹ • ν).variation.real univ = (1 : ℝ≥0∞).toReal
  rw [variation_real_smul, abs_of_pos (inv_pos.mpr ht), inv_mul_cancel₀ ht.ne']
  simp

lemma normalize_mem (ν : VectorMeasure K 𝕜) (hν : FiniteScalarRadon ν)
    (ht : 0 < ν.variation.real univ) :
    (ν.variation.real univ)⁻¹ • ν ∈ measureBall K 𝕜 :=
  ⟨radon_smul ν hν _, (normalize_mass ν hν ht).le⟩

lemma zero_not_extreme [Nonempty K] :
    (0 : VectorMeasure K 𝕜) ∉ (measureBall K 𝕜).extremePoints ℝ := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty K›
  have he : VectorMeasure.dirac x (1 : 𝕜) = 0 :=
    h.2 (dirac_mem x 1 (by simp)) (dirac_mem x (-1) (by simp))
      ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by
        rw [show VectorMeasure.dirac x (-1 : 𝕜) = -VectorMeasure.dirac x 1 by
          ext A hA; by_cases hx : x ∈ A <;> simp [VectorMeasure.dirac, hA, hx]]
        simp⟩
  have := congrArg (fun μ : VectorMeasure K 𝕜 => μ {x}) he
  simp at this

lemma extreme_mass_one [Nonempty K] (ν : VectorMeasure K 𝕜)
    (hν : ν ∈ (measureBall K 𝕜).extremePoints ℝ) : ν.variation univ = 1 := by
  have := finite_variation ν hν.1.1
  have hne : ν ≠ 0 := fun he => zero_not_extreme (he ▸ hν)
  have hp : 0 < ν.variation univ := by
    apply pos_iff_ne_zero.mpr
    intro he
    exact hne (VectorMeasure.variation_eq_zero.mp (Measure.measure_univ_eq_zero.mp he))
  have ht : 0 < ν.variation.real univ := ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)
  by_contra he
  have hlt : ν.variation univ < 1 := lt_of_le_of_ne hν.1.2 he
  have htlt : ν.variation.real univ < 1 := by
    simpa [Measure.real] using (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (by simp)).mpr hlt
  have hz : (ν.variation.real univ)⁻¹ • ν = ν :=
    hν.2 (normalize_mem ν hν.1.1 ht) (zero_mem (K := K) (𝕜 := 𝕜))
      ⟨ν.variation.real univ, 1 - ν.variation.real univ, ht, by linarith,
        by ring, by
          change ν.variation.real univ • ((ν.variation.real univ)⁻¹ • ν) +
            (1 - ν.variation.real univ) • (0 : VectorMeasure K 𝕜) = ν
          ext B hB
          simp [smul_smul, ht.ne']⟩
  have hm := congrArg (fun μ : VectorMeasure K 𝕜 => μ.variation univ) hz
  rw [normalize_mass ν hν.1.1 ht] at hm
  exact he hm.symm

/-- Splitting variation gives norm-one scalar restrictions. This works directly
with exact variation identities, so no scalar cancellation is involved. -/
theorem restriction_decomposition : RestrictionDecomposition.{u} 𝕜 := by
  intro K _ _ _ _ _ _ ν hν hm A hA hp hlt
  dsimp only
  have := finite_variation ν hν
  have ht : ν.variation.real univ = 1 := by simp [Measure.real, hm]
  have ha : 0 < ν.variation.real A := ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)
  have he := measureReal_add_measureReal_compl (μ := ν.variation) hA
  have halt : ν.variation.real A < 1 := by
    simpa [Measure.real] using (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (by simp)).mpr hlt
  have hb : 0 < ν.variation.real Aᶜ := by linarith
  have hAr : (ν.restrict A).variation.real univ = ν.variation.real A := by
    simp [VectorMeasure.variation_restrict hA, Measure.real]
  have hBr : (ν.restrict Aᶜ).variation.real univ = ν.variation.real Aᶜ := by
    simp [VectorMeasure.variation_restrict hA.compl, Measure.real]
  have hAn : ((ν.variation.real A)⁻¹ • ν.restrict A).variation univ = 1 := by
    rw [← hAr]
    exact normalize_mass _ (radon_restrict ν hν A hA) (hAr ▸ ha)
  have hBn : ((ν.variation.real Aᶜ)⁻¹ • ν.restrict Aᶜ).variation univ = 1 := by
    rw [← hBr]
    exact normalize_mass _ (radon_restrict ν hν Aᶜ hA.compl) (hBr ▸ hb)
  refine ⟨ha, hb, by linarith, ⟨radon_smul _ (radon_restrict ν hν A hA) _, hAn.le⟩,
    ⟨radon_smul _ (radon_restrict ν hν Aᶜ hA.compl) _, hBn.le⟩, hAn, hBn, ?_, ?_⟩
  · intro heq
    have hevar := congrArg (fun μ : VectorMeasure K 𝕜 => μ.variation A) heq
    have hleft : ((ν.variation.real A)⁻¹ • ν.restrict A).variation A = 1 := by
      convert hAn using 1
      simp [VectorMeasure.variation_smul, VectorMeasure.variation_restrict hA,
          Measure.smul_apply, Measure.restrict_apply, hA]
    rw [hleft] at hevar
    simp [VectorMeasure.variation_smul, VectorMeasure.variation_restrict hA.compl,
      Measure.smul_apply, Measure.restrict_apply, hA] at hevar
  · simp only [smul_smul, mul_inv_cancel₀ ha.ne', mul_inv_cancel₀ hb.ne', one_smul]
    exact (VectorMeasure.restrict_add_restrict_compl hA).symm

/-- An extreme scalar measure has a Dirac variation probability. -/
lemma extreme_variation_dirac [Nonempty K] (ν : VectorMeasure K 𝕜)
    (hν : ν ∈ (measureBall K 𝕜).extremePoints ℝ) :
    ∃ x : K, ν.variation = Measure.dirac x := by
  have hm := extreme_mass_one ν hν
  have : IsProbabilityMeasure ν.variation := ⟨hm⟩
  by_contra hn
  have hnd : ∀ x : K, ν.variation ≠ Measure.dirac x := by simpa using hn
  obtain ⟨A, hA, hp, hlt⟩ := ExtremeProbabilities.intermediate_mass K ν.variation
    ⟨inferInstance, hν.1.1.2⟩ hnd
  obtain ⟨ha, hb, hab, h₁, h₂, _, _, hne, hsum⟩ :=
    restriction_decomposition K ν hν.1.1 hm A hA hp hlt
  have hseg : ν ∈ openSegment ℝ
      ((ν.variation.real A)⁻¹ • ν.restrict A)
      ((ν.variation.real Aᶜ)⁻¹ • ν.restrict Aᶜ) :=
    ⟨_, _, ha, hb, hab, hsum.symm⟩
  have hleft := hν.2 h₁ h₂ hseg
  have hright := hν.2 h₂ h₁ (by rwa [openSegment_symm])
  exact hne (hleft.trans hright.symm)

theorem scalar_characterization : ScalarCharacterization.{u} 𝕜 := by
  intro K _ _ _ _ _ _ ν
  constructor
  · intro hν
    obtain ⟨x, hx⟩ := extreme_variation_dirac ν hν
    have hs : ‖ν {x}‖ₑ = 1 := by
      rw [← VectorMeasure.variation_apply_singleton, hx]
      simp
    have hn : ‖ν {x}‖ = 1 := by
      have := congrArg ENNReal.toReal hs
      simpa using this
    refine ⟨x, ν {x}, hn, ?_⟩
    apply eq_dirac_of_compl_variation_zero
    simp [hx]
  · rintro ⟨x, z, hz, rfl⟩
    exact dirac_extreme x z hz

theorem complex_characterization : ComplexCharacterization.{u} :=
  scalar_characterization

theorem real_characterization : RealCharacterization.{u} := by
  intro K _ _ _ _ _ _ ν
  rw [scalar_characterization K ν]
  constructor
  · rintro ⟨x, z, hz, rfl⟩
    have hz' : z = 1 ∨ z = -1 := by
      rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp hz with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases hz' with rfl | rfl
    · exact ⟨x, Or.inl rfl⟩
    · exact ⟨x, Or.inr rfl⟩
  · rintro ⟨x, h | h⟩
    · exact ⟨x, 1, by simp, h⟩
    · exact ⟨x, -1, by simp, h⟩

theorem interior_not_extreme : InteriorNotExtreme.{u} 𝕜 := by
  intro K _ _ _ _ _ _ ν _ hlt he
  exact hlt.ne (extreme_mass_one ν he)

end ExpandedFA.PartV.ExtremeScalarMeasures
