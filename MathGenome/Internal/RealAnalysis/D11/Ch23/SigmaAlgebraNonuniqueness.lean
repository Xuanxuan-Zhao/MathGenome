import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.SigmaAlgebraNonuniqueness
import MathGenome.Internal.RealAnalysis.D11.Ch23.CcPositiveElementary
import MathGenome.Internal.RealAnalysis.D11.Ch23.GeneratedRingAlgebra
import MathGenome.Internal.RealAnalysis.D11.Ch16.ProperIntegralEquality
import Mathlib.Topology.UrysohnsLemma

noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace D11.Ch23.SigmaAlgebraNonuniqueness

open Specs.Nonuniqueness

lemma vanishes_off_positive (f : V) {x : ℝ} (hx : x ∉ Ioi (0 : ℝ)) : f.val x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hx (f.property.2 h))

lemma lattice : Specs.IsVectorLattice V := by
  have hcc := (ccFunctions_stone ℝ).1
  constructor
  · intro f hf g hg
    exact ⟨hcc.1 f hf.1 g hg.1,
      (tsupport_binop_subset min (min_self 0) f g).trans (union_subset hf.2 hg.2)⟩
  · intro f hf g hg
    exact ⟨hcc.2 f hf.1 g hg.1,
      (tsupport_binop_subset max (max_self 0) f g).trans (union_subset hf.2 hg.2)⟩

lemma stone : Specs.IsStone V := by
  intro f hf
  exact ⟨(ccFunctions_stone ℝ).2 f hf.1,
    (tsupport_comp_subset (g := fun t : ℝ => min t 1)
      (min_eq_left zero_le_one) f).trans hf.2⟩

lemma elementary : Specs.IsElementaryIntegral V L := by
  refine ⟨?_, ?_⟩
  · intro f hf
    exact integral_nonneg hf
  · intro f hanti hlim
    exact cc_positive_orderContinuous
      (CompactlySupportedContinuousMap.integralPositiveLinearMap
        (volume : Measure ℝ)).toLinearMap
      (fun g hg => integral_nonneg hg) (fun n => toCc (f n)) hanti hlim

/-- Countably many genuine compact cutoffs, with support bounded away from zero. -/
lemma countable_bumps : CountableBumps := by
  classical
  have hc (n : ℕ) : ∃ f : C(ℝ, ℝ),
      EqOn f 1 (Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) ∧
      IsCompact (tsupport f) ∧ tsupport f ⊆ Ioi (0 : ℝ) ∧
      ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
    apply exists_continuousMap_one_of_isCompact_subset_isOpen isCompact_Icc isOpen_Ioi
    intro x hx
    exact lt_of_lt_of_le (by positivity) hx.1
  choose ψ hOne hCompact hSupport hRange using hc
  let φ : ℕ → V := fun n => ⟨ψ n, ⟨(ψ n).continuous, hCompact n⟩, hSupport n⟩
  refine ⟨φ, hRange, hOne, ?_⟩
  ext x
  constructor
  · intro hx
    have hx0 : 0 < x := hx
    obtain ⟨n, hn⟩ := exists_nat_gt (max x (1 / x))
    have hxn : x < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
    have hinv : 1 / x < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
    have hlo : 1 / ((n : ℝ) + 1) ≤ x := by
      apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
      have := (div_lt_iff₀ hx0).mp hinv
      nlinarith
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    change (1 / 2 : ℝ) < ψ n x
    rw [hOne n ⟨hlo, by linarith⟩]
    norm_num
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact (φ n).property.2 (subset_tsupport _ (by
      change (φ n).val x ≠ 0
      change (1 / 2 : ℝ) < (φ n).val x at hn
      linarith))

lemma ring_subset_positive (E : Set ℝ) (hE : E ∈ R) : E ⊆ Ioi (0 : ℝ) := by
  let S : SigmaRing ℝ :=
    { sets := {B | B ⊆ Ioi (0 : ℝ)}
      empty_mem := empty_subset _
      diff_mem := fun {_ _} hB _ => sdiff_subset.trans hB
      iUnion_mem := fun B hB => iUnion_subset hB }
  apply positiveLevelSigmaRing_le V S ?_ hE
  rintro B ⟨f, hf, b, hb, rfl⟩ x hx
  exact hf.2 (subset_tsupport _ (by
    change f x ≠ 0
    change b < f x at hx
    linarith))

lemma positive_mem_ring : Ioi (0 : ℝ) ∈ R := by
  obtain ⟨φ, _, _, hcover⟩ := countable_bumps
  rw [hcover]
  exact R.iUnion_mem _ (fun n => positiveLevel_mem_sigmaRing V
    (φ n).val (φ n).property (1 / 2) (by norm_num))

lemma complement_measurable : MeasurableSet[A] (Iic (0 : ℝ)) := by
  simpa only [compl_Ioi] using (sigmaRing_sets_measurable V _ positive_mem_ring).compl

lemma complement_not_mem_ring : Iic (0 : ℝ) ∉ R := by
  intro h
  have := ring_subset_positive _ h (show (0 : ℝ) ∈ Iic 0 by simp)
  exact (lt_irrefl (0 : ℝ)) this

lemma generated_domains : GeneratedDomains :=
  ⟨positive_mem_ring, ring_subset_positive, A_le_borel,
    complement_measurable, complement_not_mem_ring⟩

lemma original_measurable (f : V) : @Measurable ℝ ℝ A (borel ℝ) f.val :=
  measurable_of_mem V lattice f.val f.property

lemma original_integrable (f : V) : Integrable f.val (volume : Measure ℝ) :=
  f.property.1.1.integrable_of_hasCompactSupport f.property.1.2

lemma L_apply (f : V) : L f = ∫ x, f.val x := rfl

/-- Completion changes neither the integral of an original Borel function nor
its outer measure. We prove the needed trim equality explicitly. -/
lemma integral_completed (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂(volume : Measure ℝ).completion) = ∫ x, f x := by
  let μc : @Measure ℝ (_root_.Specs.D11.Ch02.Completion.completedSpace_value
      (volume : Measure ℝ)) := (volume : Measure ℝ).completion
  change (∫ x, f x ∂μc) = ∫ x, f x
  have hm : (borel ℝ) ≤ _root_.Specs.D11.Ch02.Completion.completedSpace_value (volume : Measure ℝ) :=
    fun _ hs => hs.nullMeasurableSet
  have ht : μc.trim hm = (volume : Measure ℝ) := by
    apply Measure.ext
    intro E hE
    rw [trim_measurableSet_eq hm hE]
    rfl
  have h := integral_trim (μ := μc) hm hf.stronglyMeasurable
  rwa [ht] at h

lemma riemann_on_support_interval (f : V) (a b : ℝ) (hab : a ≤ b)
    (hs : tsupport f.val ⊆ Icc a b) :
    ∃ hR : SingleVariableAnalysis.Riemann.RealIntegrable f.val a b,
      L f = SingleVariableAnalysis.Riemann.realIntegral f.val hR := by
  have hR : SingleVariableAnalysis.Riemann.RealIntegrable f.val a b := by
    apply SingleVariableAnalysis.Riemann.real_continuous_integrable _ hab
    intro x hx
    apply (SingleVariableAnalysis.relativeContinuousAt_within_iff _ _ _).mpr
    exact f.property.1.1.continuousOn x hx
  refine ⟨hR, ?_⟩
  have he := D11.Ch16.ProperIntegralEquality.real_integral_eq f.val hR
  have hi : (Icc a b).indicator f.val = f.val := by
    funext x
    by_cases hx : x ∈ Icc a b
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx]
      exact (image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))).symm
  rw [hi] at he
  exact (L_apply f).trans ((integral_completed f.val f.property.1.1.measurable).symm.trans he.symm)

lemma riemann_identification : RiemannIdentification := by
  intro f
  refine ⟨?_, riemann_on_support_interval f⟩
  obtain ⟨a, ha⟩ := f.property.1.2.bddBelow
  obtain ⟨b, hb⟩ := f.property.1.2.bddAbove
  have hs : tsupport f.val ⊆ Icc (min a b) (max a b) :=
    fun x hx => ⟨(min_le_left _ _).trans (ha hx), (hb hx).trans (le_max_right _ _)⟩
  obtain ⟨hR, he⟩ := riemann_on_support_interval f _ _
    ((min_le_left a b).trans (le_max_left a b)) hs
  exact ⟨_, _, hR, hs, he⟩

lemma lattice_and_integral : LatticeAndIntegral :=
  ⟨lattice, stone, elementary, riemann_identification⟩

lemma representations : Representations := by
  intro f
  have hm := original_measurable f
  have hs := hm.stronglyMeasurable
  have hz : f.val 0 = 0 := vanishes_off_positive f (by simp)
  have hi := original_integrable f
  have hi₀ : Integrable f.val ((volume : Measure ℝ).restrict (Ioi 0)) := hi.restrict
  have hiD : Integrable f.val (Measure.dirac (0 : ℝ)) :=
    integrable_dirac (by simp)
  have heD : f.val =ᵐ[Measure.dirac (0 : ℝ)] (fun _ => (0 : ℝ)) := by
    simp only [Filter.EventuallyEq, ae_dirac_eq, Filter.eventually_pure]
    exact hz
  have heInf : f.val =ᵐ[(∞ : ℝ≥0∞) • Measure.dirac (0 : ℝ)] (fun _ => (0 : ℝ)) :=
    Measure.ae_smul_measure heD ∞
  have hiInf : Integrable f.val ((∞ : ℝ≥0∞) • Measure.dirac (0 : ℝ)) :=
    (integrable_zero _ _ _).congr heInf.symm
  have e₀ : (∫ x in Ioi (0 : ℝ), f.val x) = L f :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun _ hx => vanishes_off_positive f hx)).trans (L_apply f).symm
  have eD : (∫ x, f.val x ∂Measure.dirac (0 : ℝ)) = 0 := by
    rw [integral_dirac, hz]
  have eInf : (∫ x, f.val x ∂((∞ : ℝ≥0∞) • Measure.dirac (0 : ℝ))) = 0 := by
    rw [integral_congr_ae heInf, integral_zero]
  refine ⟨hm, hi₀.trim A_le_borel hs, (hi₀.add_measure hiD).trim A_le_borel hs,
    (hi₀.add_measure hiInf).trim A_le_borel hs, ?_, ?_, ?_⟩
  · exact (integral_trim A_le_borel hs).symm.trans e₀
  · dsimp only [μ₁]
    rw [← integral_trim A_le_borel hs, integral_add_measure hi₀ hiD, e₀, eD, add_zero]
  · dsimp only [μInf]
    rw [← integral_trim A_le_borel hs, integral_add_measure hi₀ hiInf, e₀, eInf, add_zero]

/-- Every generated-measurable set has its positive part in the generated ring. -/
lemma positive_trace_mem_ring (E : Set ℝ) (hE : MeasurableSet[A] E) :
    E ∩ Ioi (0 : ℝ) ∈ R := by
  change MeasurableSpace.GenerateMeasurable (Specs.positiveLevelFamily V) E at hE
  induction hE with
  | basic E hE =>
    have hEr : E ∈ R := subset_generatedSigmaRing _ hE
    rwa [inter_eq_left.mpr (ring_subset_positive E hEr)]
  | empty =>
    rw [empty_inter]
    exact R.empty_mem
  | compl E _ ih =>
    have he : Eᶜ ∩ Ioi (0 : ℝ) = Ioi 0 \ (E ∩ Ioi 0) := by
      ext x
      simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]
      tauto
    rw [he]
    exact R.diff_mem positive_mem_ring ih
  | iUnion E _ ih =>
    rw [iUnion_inter]
    exact R.iUnion_mem _ ih

/-- All points of the nonpositive half-line are indistinguishable in A_V. -/
lemma nonpositive_membership (E : Set ℝ) (hE : MeasurableSet[A] E) :
    ∀ x : ℝ, x ≤ 0 → (x ∈ E ↔ (0 : ℝ) ∈ E) := by
  change MeasurableSpace.GenerateMeasurable (Specs.positiveLevelFamily V) E at hE
  induction hE with
  | basic E hE =>
    have hs := ring_subset_positive E (subset_generatedSigmaRing _ hE)
    intro x hx
    have hxE : x ∉ E := fun h => (not_lt_of_ge hx) (hs h)
    have h0E : (0 : ℝ) ∉ E := fun h => (lt_irrefl (0 : ℝ)) (hs h)
    simp only [hxE, h0E]
  | empty => simp
  | compl E _ ih =>
    intro x hx
    exact not_congr (ih x hx)
  | iUnion E _ ih =>
    intro x hx
    simp only [mem_iUnion]
    exact exists_congr fun n => ih n x hx

lemma outside_ring_contains_zero (E : Set ℝ) (hE : MeasurableSet[A] E)
    (hn : E ∉ R) : (0 : ℝ) ∈ E := by
  by_contra hz
  have hs : E ⊆ Ioi (0 : ℝ) := by
    intro x hx
    by_contra hx0
    exact hz ((nonpositive_membership E hE x (le_of_not_gt hx0)).mp hx)
  have ht := positive_trace_mem_ring E hE
  rw [inter_eq_left.mpr hs] at ht
  exact hn ht

lemma zero_measure_value (E : Set ℝ) (hE : MeasurableSet[A] E) :
    μ₀ E = volume (E ∩ Ioi (0 : ℝ)) := by
  rw [μ₀, trim_measurableSet_eq A_le_borel hE,
    Measure.restrict_apply (A_le_borel E hE)]

attribute [local instance] Classical.propDecidable

lemma one_measure_value (E : Set ℝ) (hE : MeasurableSet[A] E) :
    μ₁ E = μ₀ E + (if (0 : ℝ) ∈ E then 1 else 0) := by
  classical
  rw [μ₁, trim_measurableSet_eq A_le_borel hE, Measure.add_apply,
    Measure.restrict_apply (A_le_borel E hE), zero_measure_value E hE,
    Measure.dirac_apply' _ (A_le_borel E hE)]
  rfl

lemma infinity_measure_value (E : Set ℝ) (hE : MeasurableSet[A] E) :
    μInf E = (if E ∈ R then μ₀ E else ∞) := by
  classical
  rw [μInf, trim_measurableSet_eq A_le_borel hE, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (A_le_borel E hE)]
  by_cases hr : E ∈ R
  · have hz : (0 : ℝ) ∉ E := fun h => (lt_irrefl (0 : ℝ)) (ring_subset_positive E hr h)
    simp only [hr, indicator_of_notMem hz, ite_true, mul_zero, add_zero]
    rw [zero_measure_value E hE, Measure.restrict_apply (A_le_borel E hE)]
  · have hz := outside_ring_contains_zero E hE hr
    simp only [hr, indicator_of_mem hz, Pi.one_apply, ite_false, mul_one, add_top]

lemma measure_values : MeasureValues := by
  classical
  have h₀ : μ₀ (Iic 0) = 0 := by
    rw [zero_measure_value _ complement_measurable]
    rw [inter_comm, Ioi_inter_Iic, Ioc_self, measure_empty]
  have h₁ : μ₁ (Iic 0) = 1 := by
    rw [one_measure_value _ complement_measurable, h₀]
    simp
  have hInf : μInf (Iic 0) = ∞ := by
    rw [infinity_measure_value _ complement_measurable]
    simp only [complement_not_mem_ring, ite_false]
  exact ⟨fun E hE => ⟨zero_measure_value E hE, one_measure_value E hE,
    infinity_measure_value E hE⟩, h₀, h₁, hInf, fun he => by
      have := congrArg (fun μ : @Measure ℝ A => μ (Iic 0)) he
      rw [h₀, h₁] at this
      exact zero_ne_one this⟩

/-- The specific source example, including its Riemann functional, both
generated domains, actual representatives, and the optional infinite extension. -/
theorem nonuniqueness : Specs.Nonuniqueness.Statement :=
  ⟨lattice_and_integral, countable_bumps, generated_domains, representations, measure_values⟩

end D11.Ch23.SigmaAlgebraNonuniqueness
