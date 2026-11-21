import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.MeasureAtomicApproximation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace ExpandedFA.PartIV.MeasureAtomicApproximation

open Set MeasureTheory Filter
open scoped Topology
open ExpandedFA.FunctionSpaces.ScalarRieszMarkovSpec
open ExpandedFA.FunctionSpaces.PositiveRadonRepresentationSpec
open ExpandedFA.FunctionSpaces.ScalarRieszMarkov
open ExpandedFA.FunctionSpaces.PositiveRadonRepresentation
open ExpandedFA.PartIV.MeasureAtomicApproximationSpec

universe u

/-- Quantizing a measure by a simple map puts its variation on a finite set. -/
theorem finiteScalarSupport_map {K 𝕜 : Type*} [MeasurableSpace K]
    [MeasurableSingletonClass K] [RCLike 𝕜] (μ : VectorMeasure K 𝕜)
    (q : SimpleFunc K K) :
    FiniteScalarSupport (μ.map q) := by
  refine ⟨q.range, le_antisymm ?_ zero_le⟩
  calc
    (μ.map q).variation (q.range : Set K)ᶜ ≤
        (μ.variation.map q) (q.range : Set K)ᶜ := (VectorMeasure.variation_map_le (μ := μ) (φ := q)) _
    _ = 0 := by
      rw [Measure.map_apply_of_aemeasurable q.measurable.aemeasurable]
      · have he : q ⁻¹' (q.range : Set K)ᶜ = ∅ := by
          ext x
          simp
        rw [he, measure_empty]
      · simpa only [SimpleFunc.coe_range] using q.finite_range.measurableSet.compl

/-- In the compact metric setting any finite Borel variation is Radon. -/
theorem finiteScalarRadon_of_finite {K 𝕜 : Type*} [MetricSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] [RCLike 𝕜]
    (μ : VectorMeasure K 𝕜) [IsFiniteMeasure μ.variation] : FiniteScalarRadon μ :=
  ⟨measure_lt_top _ _, (positiveRadon_iff_regular _).mpr inferInstance⟩

/-- The uncorrected finite-range pushforwards converge on every continuous test
and have variation bounded by the variation of the original measure. -/
theorem exists_atomic_contractive_approximation {K 𝕜 : Type*}
    [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] [RCLike 𝕜]
    (μ : VectorMeasure K 𝕜) [IsFiniteMeasure μ.variation] :
    ∃ ν : ℕ → VectorMeasure K 𝕜,
      (∀ n, FiniteScalarRadon (ν n) ∧ FiniteScalarSupport (ν n) ∧
        (ν n).variation.real univ ≤ μ.variation.real univ) ∧
      ∀ f : C(K, 𝕜), Tendsto (fun n => scalarIntegral (ν n) f) atTop
        (𝓝 (scalarIntegral μ f)) := by
  obtain ⟨q, hq⟩ := (stronglyMeasurable_id : StronglyMeasurable (id : K → K))
  refine ⟨fun n => μ.map (q n), ?_, ?_⟩
  · intro n
    refine ⟨finiteScalarRadon_of_finite _, finiteScalarSupport_map μ (q n), ?_⟩
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    calc
      (μ.map (q n)).variation univ ≤ (μ.variation.map (q n)) univ :=
        VectorMeasure.variation_map_le _
      _ = μ.variation univ := Measure.map_apply_of_aemeasurable
        (q n).measurable.aemeasurable MeasurableSet.univ
  · intro f
    have hm n : AEStronglyMeasurable (fun x => f (q n x)) μ.variation :=
      (f.continuous.measurable.comp (q n).measurable).aestronglyMeasurable
    have hi n : Integrable (fun x => f (q n x)) μ.variation :=
      (integrable_const ‖f‖).mono' (hm n)
        (Eventually.of_forall fun x => f.norm_coe_le_norm _)
    have heq n : scalarIntegral (μ.map (q n)) f =
        scalarIntegral μ (fun x => f (q n x)) :=
      VectorMeasure.integral_map (q n).measurable
        f.continuous.aestronglyMeasurable (hi n)
    simp_rw [heq]
    exact VectorMeasure.tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
      hm (integrable_const _) (fun n => Eventually.of_forall fun x => f.norm_coe_le_norm _)
      (Eventually.of_forall fun x => (f.continuous.tendsto x).comp (hq x))

/-- Quantization preserves positivity and total mass without normalization. -/
theorem probability_approximation : ProbabilityApproximation.{u} := by
  intro K _ _ _ _ μ _
  obtain ⟨q, hq⟩ := (stronglyMeasurable_id : StronglyMeasurable (id : K → K))
  refine ⟨fun n => μ.map (q n), ?_, ?_⟩
  · intro n
    refine ⟨inferInstance, (positiveRadon_iff_regular _).mpr inferInstance, (q n).range, ?_⟩
    rw [Measure.map_apply (q n).measurable (Finset.measurableSet _).compl]
    have he : q n ⁻¹' ((q n).range : Set K)ᶜ = ∅ := by
      ext x
      simp
    rw [he, measure_empty]
  · intro 𝕜 _ f
    have heq n : (∫ x, f x ∂μ.map (q n)) = ∫ x, f (q n x) ∂μ :=
      integral_map (q n).measurable.aemeasurable f.continuous.aestronglyMeasurable
    simp_rw [heq]
    exact tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
      (fun n => (f.continuous.measurable.comp (q n).measurable).aestronglyMeasurable)
      (integrable_const _) (fun n => Eventually.of_forall fun x => f.norm_coe_le_norm _)
      (Eventually.of_forall fun x => (f.continuous.tendsto x).comp (hq x))

/-- Weak-star convergence together with the contractive variation bound forces
convergence of the variation norms. A single norming test handles each lower
bound; there is no exchange of a supremum with a sequential limit. -/
theorem variation_mass_tendsto {K 𝕜 : Type*}
    [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] [RCLike 𝕜]
    (μ : VectorMeasure K 𝕜) [IsFiniteMeasure μ.variation]
    (ν : ℕ → VectorMeasure K 𝕜) (hν : ∀ n, FiniteScalarRadon (ν n))
    (hle : ∀ n, (ν n).variation.real univ ≤ μ.variation.real univ)
    (hconv : ∀ f : C(K, 𝕜), Tendsto (fun n => scalarIntegral (ν n) f) atTop
      (𝓝 (scalarIntegral μ f))) :
    Tendsto (fun n => (ν n).variation.real univ) atTop (𝓝 (μ.variation.real univ)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    have ha' : a < ‖scalarMeasureFunctional μ‖ := by
      rwa [scalarMeasureFunctional_norm_eq]
    obtain ⟨f, hf, haf⟩ := (scalarMeasureFunctional μ).exists_lt_apply_of_lt_opNorm ha'
    have htest := (tendsto_order.1 (hconv f.toContinuousMap).norm).1 a haf
    filter_upwards [htest] with n hn
    have : IsFiniteMeasure (ν n).variation := ⟨(hν n).1⟩
    apply hn.trans_le
    exact (scalarIntegral_bound (ν n) f).2.trans
      (mul_le_of_le_one_right ENNReal.toReal_nonneg hf.le)
  · intro a ha
    exact Eventually.of_forall fun n => (hle n).trans_lt ha

/-- Scalar rescaling preserves finite support, including a zero scalar. -/
theorem finiteScalarSupport_smul {K 𝕜 : Type*} [MeasurableSpace K] [RCLike 𝕜]
    (μ : VectorMeasure K 𝕜) (hμ : FiniteScalarSupport μ) (c : ℝ) :
    FiniteScalarSupport (c • μ) := by
  obtain ⟨s, hs⟩ := hμ
  refine ⟨s, ?_⟩
  rw [VectorMeasure.variation_smul, Measure.smul_apply, hs, smul_zero]

/-- Exact normalization is possible at every index after discarding a finite
initial segment. The scale tends to one, so all continuous pairings still
converge. Zero measures use the constant zero sequence. -/
theorem scalar_approximation : ScalarApproximation.{u} := by
  intro K _ _ _ _ 𝕜 _ μ hμ
  have : IsFiniteMeasure μ.variation := ⟨hμ.1⟩
  by_cases hzero : μ.variation.real univ = 0
  · have hv : μ.variation = 0 := Measure.measure_univ_eq_zero.mp (by
      have h := congrArg ENNReal.ofReal hzero
      simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _),
        ENNReal.ofReal_zero] using h)
    have hμzero : μ = 0 := VectorMeasure.variation_eq_zero.mp hv
    refine ⟨fun _ => μ, fun n => ⟨hμ, ⟨∅, ?_⟩, rfl⟩,
      fun f => tendsto_const_nhds⟩
    simp [hμzero]
  · have hpos : 0 < μ.variation.real univ :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
    obtain ⟨ν, hν, hconv⟩ := exists_atomic_contractive_approximation μ
    have hmass := variation_mass_tendsto μ ν (fun n => (hν n).1)
      (fun n => (hν n).2.2) hconv
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hmass).1 0 hpos)
    let ρ : ℕ → VectorMeasure K 𝕜 := fun n => ν (n + N)
    let c : ℕ → ℝ := fun n => μ.variation.real univ / (ρ n).variation.real univ
    have hρpos n : 0 < (ρ n).variation.real univ := hN (n + N) (Nat.le_add_left N n)
    have hc n : 0 ≤ c n := le_of_lt (div_pos hpos (hρpos n))
    refine ⟨fun n => c n • ρ n, ?_, ?_⟩
    · intro n
      have : IsFiniteMeasure (ρ n).variation := ⟨(hν (n + N)).1.1⟩
      refine ⟨finiteScalarRadon_of_finite _,
        finiteScalarSupport_smul _ (hν (n + N)).2.1 _, ?_⟩
      rw [VectorMeasure.variation_smul, measureReal_nnreal_smul_apply,
        coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg (hc n)]
      exact div_mul_cancel₀ _ (hρpos n).ne'
    · intro f
      have hscale : Tendsto c atTop (𝓝 1) := by
        have h : Tendsto (fun n => μ.variation.real univ / (ν (n + N)).variation.real univ)
            atTop (𝓝 (μ.variation.real univ / μ.variation.real univ)) :=
          tendsto_const_nhds.div (hmass.comp (tendsto_add_atTop_nat N)) hzero
        simpa only [div_self hzero] using h
      have hpair := (hconv f).comp (tendsto_add_atTop_nat N)
      have h := hscale.smul hpair
      simpa only [scalarIntegral, VectorMeasure.integral_smul_vectorMeasure, one_smul,
        ρ, Function.comp_apply] using h

end ExpandedFA.PartIV.MeasureAtomicApproximation
