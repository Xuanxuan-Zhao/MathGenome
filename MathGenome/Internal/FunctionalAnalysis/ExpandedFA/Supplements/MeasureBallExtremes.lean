import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.MeasureBallExtremes
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C24Faces
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.InnerProductSpace.Convex

/-! The unit ball is written directly in terms of total variation, so that
its real extreme-point condition is independent of a choice of bundled normed
measure space. All measures and regularity predicates are shared with the
accepted scalar Riesz--Markov interface. The restriction argument works on
nonmetrizable compact Hausdorff spaces as well. -/

noncomputable section
namespace ExpandedFA.Supplements.MeasureBallExtremes

open Set MeasureTheory
open scoped ENNReal
open FunctionSpaces.ScalarRieszMarkovSpec
open MeasureBallExtremesSpec

universe u
variable {K : Type u} [TopologicalSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K]
  {𝕜 : Type*} [RCLike 𝕜]

lemma finiteRadon_zero : FiniteScalarRadon (0 : VectorMeasure K 𝕜) := by
  refine ⟨by simp, ?_⟩
  apply (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr
  simp only [VectorMeasure.variation_zero]
  infer_instance

lemma finiteRadon_dirac (s : K) (c : 𝕜) :
    FiniteScalarRadon (VectorMeasure.dirac s c) := by
  refine ⟨by simp, ?_⟩
  apply (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr
  have : (Measure.dirac s).Regular := by
    apply FunctionSpaces.ScalarRieszMarkov.regular_of_small_compact_complements
    intro A hA ε hε
    by_cases hs : s ∈ A
    · refine ⟨{s}, singleton_subset_iff.mpr hs, isCompact_singleton, ?_⟩
      simpa using (pos_iff_ne_zero.mpr hε)
    · refine ⟨∅, empty_subset _, isCompact_empty, ?_⟩
      simpa [Measure.dirac_apply' _ hA, hs] using (pos_iff_ne_zero.mpr hε)
  rw [VectorMeasure.variation_dirac, enorm_eq_nnnorm, Measure.coe_nnreal_smul]
  infer_instance

lemma finiteRadon_smul (ν : VectorMeasure K 𝕜) (hν : FiniteScalarRadon ν) (r : ℝ) :
    FiniteScalarRadon (r • ν) := by
  have : IsFiniteMeasure ν.variation := ⟨hν.1⟩
  have : ν.variation.Regular :=
    (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hν.2
  refine ⟨measure_lt_top _ _, ?_⟩
  apply (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr
  rw [VectorMeasure.variation_smul]
  infer_instance

lemma finiteRadon_restrict (ν : VectorMeasure K 𝕜) (hν : FiniteScalarRadon ν)
    {A : Set K} (hA : MeasurableSet A) : FiniteScalarRadon (ν.restrict A) := by
  have : IsFiniteMeasure ν.variation := ⟨hν.1⟩
  have : ν.variation.Regular :=
    (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hν.2
  refine ⟨measure_lt_top _ _, ?_⟩
  apply (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr
  rw [VectorMeasure.variation_restrict hA]
  exact FunctionSpaces.ScalarRieszMarkov.regular_of_le Measure.restrict_le_self

lemma variationReal_smul (ν : VectorMeasure K 𝕜) (r : ℝ) (A : Set K) :
    (r • ν).variation.real A = |r| * ν.variation.real A := by
  simp [VectorMeasure.variation_smul, measureReal_def, Real.norm_eq_abs]

lemma variationReal_dirac (s : K) (c : 𝕜) :
    (VectorMeasure.dirac s c).variation.real univ = ‖c‖ := by
  simp [measureReal_def]

lemma dirac_mem_unitBall (s : K) (c : 𝕜) (hc : ‖c‖ ≤ 1) :
    VectorMeasure.dirac s c ∈ UnitBall K 𝕜 :=
  ⟨finiteRadon_dirac s c, by simpa [variationReal_dirac] using hc⟩

lemma zero_mem_unitBall : (0 : VectorMeasure K 𝕜) ∈ UnitBall K 𝕜 :=
  ⟨finiteRadon_zero, by simp⟩

/-- Vanishing variation off a point forces a genuine scalar Dirac measure. -/
lemma eq_dirac_of_variation_compl_singleton_eq_zero (ν : VectorMeasure K 𝕜)
    (s : K) (h : ν.variation {s}ᶜ = 0) : ν = VectorMeasure.dirac s (ν {s}) := by
  ext A hA
  by_cases hs : s ∈ A
  · rw [VectorMeasure.dirac_apply_of_mem hA hs]
    have hz : ν (A \ {s}) = 0 :=
      (VectorMeasure.variation_apply_eq_zero (measurableSet_singleton s).compl).mp h
        _ (sdiff_subset_compl _ _) (hA.diff (measurableSet_singleton s))
    have heq := ν.of_union (disjoint_sdiff_left : Disjoint (A \ {s}) {s})
      (hA.diff (measurableSet_singleton s)) (measurableSet_singleton s)
    simpa [hz, sdiff_union_of_subset (singleton_subset_iff.mpr hs)] using heq
  · rw [VectorMeasure.dirac_apply_of_notMem hs]
    exact (VectorMeasure.variation_apply_eq_zero (measurableSet_singleton s).compl).mp h
      _ (by simpa using hs) hA

/-- A point evaluation of norm one uses up all variation available in the ball. -/
lemma eq_dirac_of_mem_ball_of_norm_singleton (ν : VectorMeasure K 𝕜)
    (hν : ν ∈ UnitBall K 𝕜) (s : K) (hs : ‖ν {s}‖ = 1) :
    ν = VectorMeasure.dirac s (ν {s}) := by
  have : IsFiniteMeasure ν.variation := ⟨hν.1.1⟩
  apply eq_dirac_of_variation_compl_singleton_eq_zero ν s
  have hsingle : ν.variation.real {s} = 1 := by
    simpa [measureReal_def, hs] using congrArg ENNReal.toReal
      (ν.variation_apply_singleton (x := s))
  have hadd : ν.variation.real {s} + ν.variation.real {s}ᶜ = ν.variation.real univ :=
    measureReal_add_measureReal_compl (measurableSet_singleton s)
  have hz : ν.variation.real {s}ᶜ = 0 := by
    linarith [hν.2, measureReal_nonneg (μ := ν.variation) (s := {s}ᶜ)]
  exact (ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right (measure_ne_top _ _)

/-- Strict convexity of the scalar disk proves the converse for all proper
real combinations. -/
lemma dirac_extreme (s : K) (c : 𝕜) (hc : ‖c‖ = 1) :
    VectorMeasure.dirac s c ∈ P1.C24FacesSpec.extremePoints (UnitBall K 𝕜) := by
  refine ⟨dirac_mem_unitBall s c hc.le, ?_⟩
  intro η hη ξ hξ t ht0 ht1 heq
  have : IsFiniteMeasure η.variation := ⟨hη.1.1⟩
  have : IsFiniteMeasure ξ.variation := ⟨hξ.1.1⟩
  have hηnorm : ‖η {s}‖ ≤ 1 := (η.norm_measure_le_variation).trans <|
    (measureReal_mono (subset_univ {s})).trans hη.2
  have hξnorm : ‖ξ {s}‖ ≤ 1 := (ξ.norm_measure_le_variation).trans <|
    (measureReal_mono (subset_univ {s})).trans hξ.2
  have hscalar : c = t • η {s} + (1 - t) • ξ {s} := by
    simpa using congrArg (fun ν : VectorMeasure K 𝕜 => ν {s}) heq
  have hext : c ∈ (Metric.closedBall (0 : 𝕜) 1).extremePoints ℝ := by
    rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere]
    simpa using hc
  have hends := (P1.extremePoints_eq_native (Metric.closedBall (0 : 𝕜) 1)) ▸ hext
  have hends' := hends.2 (η {s}) (by simpa using hηnorm)
    (ξ {s}) (by simpa using hξnorm) t ht0 ht1 hscalar
  constructor
  · rw [eq_dirac_of_mem_ball_of_norm_singleton η hη s (hends'.1 ▸ hc), hends'.1]
  · rw [eq_dirac_of_mem_ball_of_norm_singleton ξ hξ s (hends'.2 ▸ hc), hends'.2]

/-- In a nonzero measure space, zero admits opposite point-mass perturbations. -/
lemma extreme_ne_zero [Nonempty K] (ν : VectorMeasure K 𝕜)
    (hν : ν ∈ P1.C24FacesSpec.extremePoints (UnitBall K 𝕜)) : ν ≠ 0 := by
  intro hz
  subst ν
  obtain ⟨s⟩ := ‹Nonempty K›
  let δ : VectorMeasure K 𝕜 := VectorMeasure.dirac s 1
  have hδ : δ ∈ UnitBall K 𝕜 := dirac_mem_unitBall s 1 (by simp)
  have hnegδ : -δ ∈ UnitBall K 𝕜 := by
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simpa only [VectorMeasure.variation_neg] using hδ.1.1
      · simpa only [VectorMeasure.variation_neg] using hδ.1.2
    · simpa only [VectorMeasure.variation_neg] using hδ.2
  have heq : (0 : VectorMeasure K 𝕜) = (1 / 2 : ℝ) • δ +
      (1 - 1 / 2 : ℝ) • (-δ) := by
    rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num]
    simp
  have he := (hν.2 δ hδ (-δ) hnegδ (1 / 2) (by norm_num) (by norm_num) heq).1
  have hval := congrArg (fun η : VectorMeasure K 𝕜 => η {s}) he
  simpa [δ] using hval

lemma variationReal_univ_pos_of_ne_zero (ν : VectorMeasure K 𝕜)
    (hν : FiniteScalarRadon ν) (hne : ν ≠ 0) : 0 < ν.variation.real univ := by
  have : IsFiniteMeasure ν.variation := ⟨hν.1⟩
  apply ENNReal.toReal_pos _ hν.1.ne
  exact (Measure.measure_univ_ne_zero.mpr (VectorMeasure.variation_eq_zero.not.mpr hne))

/-- A nonzero measure of mass less than one lies strictly between zero and
its normalization, and hence cannot be extreme. -/
lemma extreme_variationReal_univ_eq_one [Nonempty K] (ν : VectorMeasure K 𝕜)
    (hν : ν ∈ P1.C24FacesSpec.extremePoints (UnitBall K 𝕜)) :
    ν.variation.real univ = 1 := by
  have hne := extreme_ne_zero ν hν
  have hm := variationReal_univ_pos_of_ne_zero ν hν.1.1 hne
  apply le_antisymm hν.1.2
  by_contra hn
  have hlt : ν.variation.real univ < 1 := lt_of_not_ge hn
  let m := ν.variation.real univ
  have hmne : m ≠ 0 := hm.ne'
  let η : VectorMeasure K 𝕜 := m⁻¹ • ν
  have hη : η ∈ UnitBall K 𝕜 := by
    refine ⟨finiteRadon_smul ν hν.1.1 _, ?_⟩
    change (m⁻¹ • ν).variation.real univ ≤ 1
    rw [variationReal_smul, abs_of_pos (inv_pos.mpr hm)]
    exact le_of_eq (inv_mul_cancel₀ hm.ne')
  have heq : ν = m • η + (1 - m) • (0 : VectorMeasure K 𝕜) := by
    ext A hA
    change ν A = m • (m⁻¹ • ν A) + (1 - m) • (0 : 𝕜)
    simp only [smul_smul, mul_inv_cancel₀ hmne, one_smul, smul_zero, add_zero]
  have hz := (hν.2 η hη 0 zero_mem_unitBall m hm hlt heq).2
  exact hne hz.symm

/-- Any intermediate-variation Borel set gives a proper restriction
combination inside the ball. -/
lemma extreme_no_intermediate_set (ν : VectorMeasure K 𝕜)
    (hν : ν ∈ P1.C24FacesSpec.extremePoints (UnitBall K 𝕜))
    (hm : ν.variation.real univ = 1) {A : Set K} (hA : MeasurableSet A) :
    ¬ (0 < ν.variation.real A ∧ ν.variation.real A < 1) := by
  rintro ⟨ha, ha1⟩
  have : IsFiniteMeasure ν.variation := ⟨hν.1.1.1⟩
  let a := ν.variation.real A
  have hane : a ≠ 0 := ha.ne'
  let b := ν.variation.real Aᶜ
  have hab : a + b = 1 := by
    simpa [a, b, hm] using (measureReal_add_measureReal_compl (μ := ν.variation) hA)
  have hb : 0 < b := by linarith
  let η : VectorMeasure K 𝕜 := a⁻¹ • ν.restrict A
  let ξ : VectorMeasure K 𝕜 := b⁻¹ • ν.restrict Aᶜ
  have hη : η ∈ UnitBall K 𝕜 := by
    refine ⟨finiteRadon_smul _ (finiteRadon_restrict ν hν.1.1 hA) _, ?_⟩
    change (a⁻¹ • ν.restrict A).variation.real univ ≤ 1
    rw [variationReal_smul, VectorMeasure.variation_restrict hA]
    simp only [measureReal_restrict_apply MeasurableSet.univ, univ_inter]
    rw [abs_of_pos (inv_pos.mpr ha)]
    exact le_of_eq (inv_mul_cancel₀ ha.ne')
  have hξ : ξ ∈ UnitBall K 𝕜 := by
    refine ⟨finiteRadon_smul _ (finiteRadon_restrict ν hν.1.1 hA.compl) _, ?_⟩
    change (b⁻¹ • ν.restrict Aᶜ).variation.real univ ≤ 1
    rw [variationReal_smul, VectorMeasure.variation_restrict hA.compl]
    simp only [measureReal_restrict_apply MeasurableSet.univ, univ_inter]
    rw [abs_of_pos (inv_pos.mpr hb)]
    exact le_of_eq (inv_mul_cancel₀ hb.ne')
  have heq : ν = a • η + (1 - a) • ξ := by
    have hba : 1 - a = b := by linarith
    simp only [η, ξ, hba, smul_smul, mul_inv_cancel₀ hane, mul_inv_cancel₀ hb.ne',
      one_smul]
    exact (ν.restrict_add_restrict_compl hA).symm
  have he := (hν.2 η hη ξ hξ a ha ha1 heq).1
  have hzero : η.variation.real Aᶜ = 0 := by
    change (a⁻¹ • ν.restrict A).variation.real Aᶜ = 0
    rw [variationReal_smul, VectorMeasure.variation_restrict hA, measureReal_restrict_apply hA.compl]
    simp
  rw [he] at hzero
  exact hb.ne' hzero

/-- Regularity makes the support conull even without a countable base. If
there is no intermediate-mass Borel set, it contains just one point. -/
lemma variation_concentrated_at_point (ν : VectorMeasure K 𝕜)
    (hν : FiniteScalarRadon ν) (hm : ν.variation.real univ = 1)
    (hinter : ∀ A : Set K, MeasurableSet A →
      ¬ (0 < ν.variation.real A ∧ ν.variation.real A < 1)) :
    ∃ s : K, ν.variation {s}ᶜ = 0 := by
  have : IsFiniteMeasure ν.variation := ⟨hν.1⟩
  have : ν.variation.Regular :=
    (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hν.2
  have hsupport : ν.variation.support.Nonempty := by
    have hμ : ν.variation ≠ 0 := by
      intro hz
      simp [hz] at hm
    by_contra hn
    have he : ν.variation.support = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hc := ν.variation.measure_compl_support_of_regular
    simp only [he, compl_empty] at hc
    exact hμ (Measure.measure_univ_eq_zero.mp hc)
  obtain ⟨s, hs⟩ := hsupport
  have hsub : ν.variation.support ⊆ {s} := by
    intro x hx
    by_contra hxs
    have hne : s ≠ x := by simpa [eq_comm] using hxs
    obtain ⟨U, V, hU, hV, hsU, hxV, hdisj⟩ := t2_separation hne
    have hposU : 0 < ν.variation.real U :=
      ENNReal.toReal_pos (ne_of_gt ((Measure.mem_support_iff_forall s).mp hs U (hU.mem_nhds hsU)))
        (measure_ne_top _ _)
    have hposV : 0 < ν.variation.real V :=
      ENNReal.toReal_pos (ne_of_gt ((Measure.mem_support_iff_forall x).mp hx V (hV.mem_nhds hxV)))
        (measure_ne_top _ _)
    have hcompl : 0 < ν.variation.real Uᶜ :=
      hposV.trans_le (measureReal_mono hdisj.subset_compl_left)
    have hadd := measureReal_add_measureReal_compl (μ := ν.variation) hU.measurableSet
    exact hinter U hU.measurableSet ⟨hposU, by linarith⟩
  exact ⟨s, measure_mono_null (compl_subset_compl.mpr hsub)
    ν.variation.measure_compl_support_of_regular⟩

/-- Both the real and complex measure balls, with all original hypotheses. -/
theorem classification : Classification.{u} := by
  intro X _ _ _ _ _ _ 𝕜 _ ν
  constructor
  · intro hν
    have hm := extreme_variationReal_univ_eq_one ν hν
    obtain ⟨s, hs⟩ := variation_concentrated_at_point ν hν.1.1 hm
      (fun _ hA => extreme_no_intermediate_set ν hν hm hA)
    have heq := eq_dirac_of_variation_compl_singleton_eq_zero ν s hs
    refine ⟨s, ν {s}, ?_, heq⟩
    rw [heq, variationReal_dirac] at hm
    exact hm
  · rintro ⟨s, c, hc, rfl⟩
    exact dirac_extreme s c hc

/-- The real scalar sphere consists of the two signs. -/
theorem real_signs : RealSigns.{u} := by
  intro X _ _ _ _ _ _ ν
  rw [classification X ℝ ν]
  constructor
  · rintro ⟨s, c, hc, rfl⟩
    refine ⟨s, ?_⟩
    rcases abs_eq (show (0 : ℝ) ≤ 1 by norm_num) |>.mp hc with hc | hc
    · exact Or.inl (hc ▸ rfl)
    · exact Or.inr (hc ▸ rfl)
  · rintro ⟨s, h | h⟩
    · exact ⟨s, 1, by norm_num, h⟩
    · exact ⟨s, -1, by norm_num, h⟩

/-- Boundary case in Banach--Stone: both spaces have only their zero element. -/
theorem empty_spaces : EmptySpaces.{u} := by
  intro X _ _ _ _ 𝕜 _
  constructor
  · intro f
    ext x
    exact isEmptyElim x
  · intro ν
    ext A hA
    have : A = ∅ := Set.eq_empty_of_isEmpty A
    simp [this]

end ExpandedFA.Supplements.MeasureBallExtremes
