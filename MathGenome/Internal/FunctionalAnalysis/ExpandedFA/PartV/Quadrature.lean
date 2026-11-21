import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.Quadrature
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07UniformBoundedness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.MeasureAtomicApproximation
import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Sequences

noncomputable section
namespace ExpandedFA.PartV.Quadrature
open Set MeasureTheory Filter
open scoped Topology ZeroAtInfty
open ExpandedFA.FunctionSpaces.ScalarRieszMarkovSpec
open ExpandedFA.FunctionSpaces.ScalarRieszMarkov
open ExpandedFA.FunctionSpaces.PositiveRadonRepresentation
universe u

/-- A uniformly bounded family of linear functionals is determined in the
pointwise limit by its values on any uniformly dense subset. -/
theorem dense_limit {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (T : ℕ → E →L[𝕜] 𝕜) (L : E →L[𝕜] 𝕜)
    (s : Set E) (hs : Dense s) (M : ℝ) (hM : ∀ n, ‖T n‖ ≤ M)
    (h : ∀ x ∈ s, Tendsto (fun n => T n x) atTop (𝓝 (L x))) :
    ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (L x)) := by
  have he : Equicontinuous (fun n x => T n x) := by
    have hi : (∃ C : ℝ, ∀ n, ‖T n‖ ≤ C) ↔ Equicontinuous (fun n x => T n x) :=
      (NormedSpace.equicontinuous_TFAE T).out 6 2
    exact hi.mp ⟨M, hM⟩
  intro x
  exact (he x).tendsto_of_mem_closure L.continuous.continuousAt.continuousWithinAt h (hs x)

/-- Dense-test characterization for finite real and complex Radon measures. -/
theorem dense_test_criterion : Spec.DenseTestCriterion.{u} := by
  intro K _ _ _ _ _ 𝕜 _ μ hμ D hD L
  letI (n : ℕ) : IsFiniteMeasure (μ n).variation := ⟨(hμ n).1⟩
  letI (n : ℕ) : (μ n).variation.Regular :=
    (positiveRadon_iff_regular _).mp (hμ n).2
  obtain ⟨e, he, he'⟩ := compact_identification K 𝕜
  let T : ℕ → C(K, 𝕜) →L[𝕜] 𝕜 := fun n =>
    (scalarMeasureFunctional (μ n)).comp e.toLinearIsometry.toContinuousLinearMap
  have hT n f : T n f = scalarIntegral (μ n) f := by
    change scalarIntegral (μ n) (e f) = _
    congr 1
    exact funext (he f)
  have hn n : ‖T n‖ = (μ n).variation.real univ := by
    rw [← scalarMeasureFunctional_norm_eq]
    apply le_antisymm
    · exact by
        calc
          ‖T n‖ ≤ ‖scalarMeasureFunctional (μ n)‖ * ‖e.toLinearIsometry.toContinuousLinearMap‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ ‖scalarMeasureFunctional (μ n)‖ * 1 :=
            mul_le_mul_of_nonneg_left e.toLinearIsometry.norm_toContinuousLinearMap_le
              (norm_nonneg (scalarMeasureFunctional (μ n)))
          _ = _ := mul_one _
    · apply (scalarMeasureFunctional (μ n)).opNorm_le_bound (norm_nonneg _)
      intro f
      have h := (T n).le_opNorm (e.symm f)
      change ‖scalarMeasureFunctional (μ n) (e (e.symm f))‖ ≤ _ at h
      simpa only [e.apply_symm_apply, e.symm.norm_map] using h
  constructor
  · intro h
    have hp : ∀ f, ∃ C, ∀ n, ‖T n f‖ ≤ C := by
      intro f
      obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ (h f)).exists_norm_le
      exact ⟨C, fun n => by rw [hT]; exact hC _ (mem_range_self n)⟩
    obtain ⟨M, hM, hb⟩ := ExpandedFA.P1.C07UniformBoundedness.uniform_boundedness
      𝕜 C(K, 𝕜) 𝕜 ℕ T hp
    exact ⟨⟨M, hM, fun n => (hn n) ▸ hb n⟩, fun f _ => h f⟩
  · rintro ⟨⟨M, _, hM⟩, h⟩
    have hh := dense_limit T L (D : Set C(K, 𝕜)) hD M
      (fun n => (hn n).symm ▸ hM n) (fun f hf => by rw [show (fun n => T n f) = _ from funext (fun n => hT n f)]; exact h f hf)
    simpa only [hT] using hh

/-- Mere pointwise scalar convergence already supplies a bounded linear limit. -/
theorem convergence_criterion : Spec.ConvergenceCriterion.{u} := by
  intro K _ _ _ _ _ 𝕜 _ μ hμ D hD
  constructor
  · intro h
    choose a ha using h
    letI (n : ℕ) : IsFiniteMeasure (μ n).variation := ⟨(hμ n).1⟩
    obtain ⟨e, he, _⟩ := compact_identification K 𝕜
    let T : ℕ → C(K, 𝕜) →L[𝕜] 𝕜 := fun n =>
      (scalarMeasureFunctional (μ n)).comp e.toLinearIsometry.toContinuousLinearMap
    have hT n f : T n f = scalarIntegral (μ n) f := by
      change scalarIntegral (μ n) (e f) = _
      congr 1
      exact funext (he f)
    have ht : Tendsto (fun n f => T n f) atTop (𝓝 a) :=
      tendsto_pi_nhds.mpr (fun f => by simpa only [hT] using ha f)
    let L : C(K, 𝕜) →L[𝕜] 𝕜 := continuousLinearMapOfTendsto T ht
    have hall : ∀ f : C(K, 𝕜),
        Tendsto (fun n => scalarIntegral (μ n) f) atTop (𝓝 (L f)) := ha
    obtain ⟨hb, hd⟩ := (dense_test_criterion K 𝕜 μ hμ D hD L).mp hall
    exact ⟨hb, L, hd⟩
  · rintro ⟨hb, L, hd⟩ f
    exact ⟨L f, (dense_test_criterion K 𝕜 μ hμ D hD L).mpr ⟨hb, hd⟩ f⟩

theorem modulus_bdd {K 𝕜 : Type*} [MetricSpace K] [CompactSpace K] [RCLike 𝕜]
    (f : C(K, 𝕜)) (r : ℝ) :
    BddAbove (insert 0 {d : ℝ | ∃ x y : K, dist x y ≤ r ∧ d = dist (f x) (f y)}) := by
  refine ⟨2 * ‖f‖, ?_⟩
  rintro d (rfl | ⟨x, y, _, rfl⟩)
  · positivity
  · exact (dist_le_norm_add_norm _ _).trans (by linarith [f.norm_coe_le_norm x, f.norm_coe_le_norm y])

theorem modulus_nonneg {K 𝕜 : Type*} [MetricSpace K] [CompactSpace K] [RCLike 𝕜]
    (f : C(K, 𝕜)) (r : ℝ) : 0 ≤ Spec.modulus f r :=
  le_csSup (modulus_bdd f r) (mem_insert _ _)

theorem dist_le_modulus {K 𝕜 : Type*} [MetricSpace K] [CompactSpace K] [RCLike 𝕜]
    (f : C(K, 𝕜)) (r : ℝ) (x y : K) (h : dist x y ≤ r) :
    dist (f x) (f y) ≤ Spec.modulus f r :=
  le_csSup (modulus_bdd f r) (mem_insert_of_mem _ ⟨x, y, h, rfl⟩)

/-- Measurable finite tags are the usual partition quadrature weights. -/
theorem quadrature_weights : Spec.QuadratureWeights.{u} := by
  intro K _ _ _ _ 𝕜 _ μ q
  classical
  ext s hs
  rw [VectorMeasure.map_apply _ q.measurable hs]
  have he : q ⁻¹' s = ⋃ y ∈ q.range.filter (fun y => y ∈ s), q ⁻¹' {y} := by
    ext x
    simp only [mem_preimage, mem_iUnion, Finset.mem_filter, SimpleFunc.mem_range,
      mem_singleton_iff]
    constructor
    · intro hx
      exact ⟨q x, ⟨⟨x, rfl⟩, hx⟩, rfl⟩
    · rintro ⟨y, ⟨_, hy⟩, hxy⟩
      simpa only [hxy] using hy
  rw [he, μ.of_biUnion_finset]
  · simp only [Finset.sum_filter, FunLike.coe_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hys : y ∈ s <;> simp [hys, hs]
  · intro a ha b hb hab
    exact Disjoint.preimage q (disjoint_singleton.2 hab)
  · intro y _
    exact q.measurableSet_fiber y

/-- The quantitative error uses the genuine total variation of the scalar measure. -/
theorem quadrature_estimate : Spec.QuadratureEstimate.{u} := by
  intro K _ _ _ _ 𝕜 _ μ hμ q r hr f
  letI : IsFiniteMeasure μ.variation := ⟨hμ.1⟩
  have hif : Integrable (fun x => f (q x)) μ.variation :=
    (integrable_const ‖f‖).mono'
      (f.continuous.measurable.comp q.measurable).aestronglyMeasurable
      (Eventually.of_forall fun x => f.norm_coe_le_norm _)
  have hig : Integrable f μ.variation :=
    (integrable_const ‖f‖).mono' f.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => f.norm_coe_le_norm _)
  rw [scalarIntegral, VectorMeasure.integral_map q.measurable
    f.continuous.aestronglyMeasurable hif, scalarIntegral,
    ← VectorMeasure.integral_sub hif hig]
  calc
    _ ≤ Spec.modulus f r * ‖ContinuousLinearMap.mul ℝ 𝕜‖ * μ.variation.real univ :=
      VectorMeasure.norm_integral_le_of_norm_le_const
        (Eventually.of_forall fun x => by
          simpa only [dist_eq_norm, Pi.sub_apply] using dist_le_modulus f r (q x) x (hr x))
    _ ≤ Spec.modulus f r * 1 * μ.variation.real univ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_mul_le ℝ 𝕜)
          (modulus_nonneg f r)) ENNReal.toReal_nonneg
    _ = _ := by ring

/-- Mesh tending to zero implies convergence of all continuous scalar tests. -/
theorem quadrature_convergence : Spec.QuadratureConvergence.{u} := by
  intro K _ _ _ _ 𝕜 _ μ hμ q r hr hlim
  letI : IsFiniteMeasure μ.variation := ⟨hμ.1⟩
  refine ⟨fun n => ExpandedFA.PartIV.MeasureAtomicApproximation.finiteScalarRadon_of_finite _, ?_⟩
  intro f
  have hi n : Integrable (fun x => f (q n x)) μ.variation :=
    (integrable_const ‖f‖).mono'
      (f.continuous.measurable.comp (q n).measurable).aestronglyMeasurable
      (Eventually.of_forall fun x => f.norm_coe_le_norm _)
  have heq n : scalarIntegral (μ.map (q n)) f =
      scalarIntegral μ (fun x => f (q n x)) :=
    VectorMeasure.integral_map (q n).measurable f.continuous.aestronglyMeasurable (hi n)
  simp_rw [heq]
  apply VectorMeasure.tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
    (fun n => (f.continuous.measurable.comp (q n).measurable).aestronglyMeasurable)
    (integrable_const _) (fun n => Eventually.of_forall fun x => f.norm_coe_le_norm _)
  apply Eventually.of_forall
  intro x
  apply (f.continuous.tendsto x).comp
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun n => dist_nonneg) (fun n => hr n x) hlim

/-- The finite-quantizer result specializes to the masses of the original
partition cells, with precisely the supplied tags. -/
theorem tagged_measure_eq_map {K : Type u} [MetricSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] {𝕜 : Type} [RCLike 𝕜]
    (p : Spec.TaggedPartition K) (μ : VectorMeasure K 𝕜) :
    p.measure μ = μ.map p.quantizer := by
  classical
  have hinj : Function.Injective p.tag := by
    intro i j hij
    simpa only [p.tag_index] using congrArg p.index hij
  have hr : p.quantizer.range = Finset.univ.image p.tag := by
    ext y
    simp only [SimpleFunc.mem_range, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨p.index x, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨p.tag i, by simp [Spec.TaggedPartition.quantizer, p.tag_index]⟩
  have hf i : p.quantizer ⁻¹' {p.tag i} = p.cell i := by
    ext x
    simp [Spec.TaggedPartition.quantizer, Spec.TaggedPartition.cell, hinj.eq_iff]
  rw [quadrature_weights K 𝕜 μ p.quantizer, hr, Finset.sum_image]
  · simp_rw [hf]
    rfl
  · exact fun i _ j _ h => hinj h

theorem tagged_quadrature : Spec.TaggedQuadrature.{u} := by
  intro K _ _ _ _ 𝕜 _ μ hμ p r hr hlim
  have hd n x : dist ((p n).quantizer x) x ≤ r n := by
    apply hr n ((p n).index x) ((p n).tag ((p n).index x))
      ((p n).tag_index ((p n).index x)) x rfl
  obtain ⟨hfinite, hconv⟩ := quadrature_convergence K 𝕜 μ hμ
    (fun n => (p n).quantizer) r hd hlim
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rw [tagged_measure_eq_map]
    exact hfinite n
  · intro n f
    rw [tagged_measure_eq_map]
    exact quadrature_estimate K 𝕜 μ hμ _ _ (hd n) f
  · simpa only [tagged_measure_eq_map] using hconv

/-- Finite sums and differences of atoms have finite genuine variation. -/
theorem dirac_difference_finite {K : Type*} [MeasurableSpace K]
    (a b : K) (c : ℝ) :
    IsFiniteMeasure (VectorMeasure.dirac a c - VectorMeasure.dirac b c).variation :=
  isFiniteMeasure_of_le _ VectorMeasure.variation_sub_le

theorem dirac_difference_mass {K : Type*} [MeasurableSpace K]
    [MeasurableSingletonClass K] (a b : K) (hab : a ≠ b) (c : ℝ) (hc : 0 ≤ c) :
    (VectorMeasure.dirac a c - VectorMeasure.dirac b c).variation.real univ = 2 * c := by
  let ν := VectorMeasure.dirac a c - VectorMeasure.dirac b c
  letI : IsFiniteMeasure ν.variation := dirac_difference_finite a b c
  apply le_antisymm
  · have h := ENNReal.toReal_mono
      (measure_ne_top ((VectorMeasure.dirac a c).variation +
        (VectorMeasure.dirac b c).variation) univ)
      (VectorMeasure.variation_sub_le (μ := VectorMeasure.dirac a c)
        (ν := VectorMeasure.dirac b c) univ)
    simpa [ν, Measure.real, ENNReal.toReal_add, Real.norm_eq_abs, abs_of_nonneg hc,
      two_mul] using h
  · have h := measureReal_mono (μ := ν.variation)
      (s₁ := ({a} : Set K) ∪ {b}) (subset_univ _)
    rw [measureReal_union (disjoint_singleton.2 hab) (measurableSet_singleton b)] at h
    simpa [ν, Measure.real, hab, hab.symm, Real.norm_eq_abs, abs_of_nonneg hc,
      two_mul] using h

theorem counterexample_finite (n : ℕ) :
    FiniteScalarRadon (Spec.counterexampleMeasure n) := by
  letI : IsFiniteMeasure (Spec.counterexampleMeasure n).variation :=
    dirac_difference_finite (Spec.inverseSquareNode n)
    (⟨0, le_rfl, zero_le_one⟩ : Set.Icc (0 : ℝ) 1) (n : ℝ)
  exact ExpandedFA.PartIV.MeasureAtomicApproximation.finiteScalarRadon_of_finite _

theorem counterexample_pairing (n : ℕ) (f : C(Set.Icc (0 : ℝ) 1, ℝ)) :
    scalarIntegral (Spec.counterexampleMeasure n) f =
      (n : ℝ) * (f (Spec.inverseSquareNode n) - f ⟨0, le_rfl, zero_le_one⟩) := by
  have hi (a : Set.Icc (0 : ℝ) 1) :
      Integrable f (VectorMeasure.dirac a (n : ℝ)).variation :=
    (integrable_const ‖f‖).mono' f.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => f.norm_coe_le_norm _)
  rw [Spec.counterexampleMeasure, scalarIntegral,
    VectorMeasure.integral_sub_vectorMeasure (hi _) (hi _)]
  simp only [VectorMeasure.integral_dirac, ContinuousLinearMap.mul_apply']
  ring

theorem counterexample_sqrt (n : ℕ) (hn : 1 ≤ n) :
    scalarIntegral (Spec.counterexampleMeasure n) Spec.sqrtTest = 1 := by
  rw [counterexample_pairing]
  change (n : ℝ) * (Real.sqrt ((n : ℝ)⁻¹ ^ 2) - Real.sqrt 0) = 1
  rw [Real.sqrt_sq (inv_nonneg.mpr (Nat.cast_nonneg n)), Real.sqrt_zero, sub_zero]
  exact mul_inv_cancel₀ (by exact_mod_cast (Nat.ne_zero_of_lt hn))

theorem counterexample_variation (n : ℕ) :
    (Spec.counterexampleMeasure n).variation.real univ = 2 * (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [Spec.counterexampleMeasure, Measure.real]
  · apply dirac_difference_mass _ _ ?_ _ (Nat.cast_nonneg n)
    intro he
    have he' := congrArg Subtype.val he
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    change (n : ℝ)⁻¹ ^ 2 = 0 at he'
    exact (pow_ne_zero 2 (inv_ne_zero hn')) he'

theorem counterexample_polynomial (p : Polynomial ℝ) :
    Tendsto (fun n => scalarIntegral (Spec.counterexampleMeasure n)
      (p.toContinuousMapOn _)) atTop (𝓝 0) := by
  obtain ⟨q, hq⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (p := p) (a := 0)
  have hpoly (x : ℝ) : p.eval x - p.eval 0 = x * q.eval x := by
    have he := congrArg (fun p : Polynomial ℝ => p.eval x) hq
    simpa using he
  have he n : scalarIntegral (Spec.counterexampleMeasure n) (p.toContinuousMapOn _) =
      (n : ℝ)⁻¹ * q.eval ((n : ℝ)⁻¹ ^ 2) := by
    rw [counterexample_pairing]
    change (n : ℝ) * (p.eval ((n : ℝ)⁻¹ ^ 2) - p.eval 0) = _
    rw [hpoly]
    by_cases hn : (n : ℝ) = 0
    · simp [hn]
    · field_simp
  simp_rw [he]
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hs : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ ^ 2) atTop (𝓝 0) := by
    simpa using hi.pow 2
  simpa only [zero_mul, Function.comp_apply] using hi.mul (q.continuous.tendsto 0 |>.comp hs)

/-- The explicit dense polynomial tests do not detect this unbounded-variation
sequence, while its square-root test is constantly one after the initial term. -/
theorem dense_tests_counterexample : Spec.DenseTestsCounterexample := by
  refine ⟨counterexample_finite, ?_, counterexample_polynomial, counterexample_sqrt,
    counterexample_variation, ?_, ?_⟩
  · intro f
    have h := continuousMap_mem_polynomialFunctions_closure 0 1 f
    exact h
  · rintro ⟨M, hM⟩
    obtain ⟨n, hn⟩ := exists_nat_gt M
    have hb := hM n
    rw [counterexample_variation] at hb
    linarith [Nat.cast_nonneg (α := ℝ) n]
  · intro h
    have he : Tendsto (fun n => scalarIntegral (Spec.counterexampleMeasure n) Spec.sqrtTest)
        atTop (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      exact eventually_atTop.mpr ⟨1, fun n hn => (counterexample_sqrt n hn).symm⟩
    have := tendsto_nhds_unique (h Spec.sqrtTest) he
    norm_num at this

end ExpandedFA.PartV.Quadrature
