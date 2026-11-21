import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.LacunarySubspace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.LacunaryNorms
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.PSeries
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyDisk

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory Filter
open scoped Real ENNReal Topology
namespace ExpandedFA.PartIV.LacunarySubspace
open LacunaryNormsSpec LacunarySubspaceSpec

/-- Inclusion of finite coefficient families into ℓ². -/
def finiteCoefficients : (ℕ →₀ ℂ) →ₗ[ℂ] Coeff :=
  Finsupp.lsum ℂ (lp.lsingle 2)

@[simp] theorem finiteCoefficients_single (j : ℕ) (z : ℂ) :
    finiteCoefficients (Finsupp.single j z) = lp.single 2 j z := by
  simp [finiteCoefficients]

theorem finiteCoefficients_dense : DenseRange finiteCoefficients := by
  intro a
  have ht := lp.hasSum_single (by simp : (2 : ℝ≥0∞) ≠ ⊤) a
  apply isClosed_closure.mem_of_tendsto ht
  exact Filter.Eventually.of_forall fun s => subset_closure ⟨∑ j ∈ s, Finsupp.single j (a j), by simp⟩

theorem finiteCoefficients_norm (a : ℕ →₀ ℂ) :
    ‖finiteCoefficients a‖ = coefficientNorm a.support a := by
  have he : finiteCoefficients a = ∑ j ∈ a.support, lp.single 2 j (a j) := by
    simp [finiteCoefficients, Finsupp.lsum_apply, Finsupp.sum]
  have h := lp.norm_sum_single (E := fun _ : ℕ => ℂ)
    (p := 2) (by norm_num) (fun j => a j) a.support
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [he, coefficientNorm, coefficientSq, ← h, Real.sqrt_sq (norm_nonneg _)]

/-- Finite Fourier synthesis with the source's fixed frequencies. -/
def finiteSynthesis (p : ℝ≥0∞) [Fact (1 ≤ p)] : (ℕ →₀ ℂ) →ₗ[ℂ] Space p :=
  Finsupp.linearCombination ℂ (mode p)

@[simp] theorem finiteSynthesis_single (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : ℕ) (z : ℂ) :
    finiteSynthesis p (Finsupp.single j z) = z • mode p j := by
  simp [finiteSynthesis]

theorem finiteSynthesis_norm (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : ℕ →₀ ℂ) :
    ‖finiteSynthesis p a‖ = polynomialNorm p a.support a := by
  rw [LacunaryNorms.polynomialNorm_toLp]
  simp [finiteSynthesis, Finsupp.linearCombination, Finsupp.lsum_apply, Finsupp.sum,
    polynomial, mode, fourierLp]

/-- The continuous extension is specified independently of a choice of bounds. -/
def synthesis (p : ℝ≥0∞) [Fact (1 ≤ p)] : Coeff →L[ℂ] Space p :=
  (finiteSynthesis p).extendOfNorm finiteCoefficients

theorem synthesis_finite (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (a : ℕ →₀ ℂ) :
    synthesis p (finiteCoefficients a) = finiteSynthesis p a := by
  obtain ⟨c, C, hc, hC, h⟩ := LacunaryNorms.norm_equivalence p Fact.out hp
  apply LinearMap.extendOfNorm_eq finiteCoefficients_dense
  exact ⟨C, fun a => by simpa only [finiteCoefficients_norm, finiteSynthesis_norm] using (h a.support a).2⟩

theorem synthesis_bounds (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ a : Coeff,
      c * ‖a‖ ≤ ‖synthesis p a‖ ∧ ‖synthesis p a‖ ≤ C * ‖a‖ := by
  obtain ⟨c, C, hc, hC, h⟩ := LacunaryNorms.norm_equivalence p Fact.out hp
  refine ⟨c, C, hc, hC, ?_⟩
  intro a
  refine finiteCoefficients_dense.induction_on (p := fun a : Coeff =>
    c * ‖a‖ ≤ ‖synthesis p a‖ ∧ ‖synthesis p a‖ ≤ C * ‖a‖) a ?_ ?_
  · exact (isClosed_le (continuous_const.mul continuous_norm) (synthesis p).continuous.norm).inter
      (isClosed_le (synthesis p).continuous.norm (continuous_const.mul continuous_norm))
  · intro b
    simpa only [synthesis_finite p hp, finiteCoefficients_norm, finiteSynthesis_norm]
      using h b.support b

theorem synthesis_single (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (j : ℕ) (z : ℂ) :
    synthesis p (lp.single 2 j z) = z • mode p j := by
  rw [← finiteCoefficients_single, synthesis_finite p hp, finiteSynthesis_single]

theorem synthesis_hasSum (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (a : Coeff) :
    HasSum (fun j => a j • mode p j) (synthesis p a) := by
  simpa only [synthesis_single p hp] using
    (synthesis p).hasSum (lp.hasSum_single (by simp : (2 : ℝ≥0∞) ≠ ⊤) a)

theorem synthesis_antilipschitz (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    ∃ K : NNReal, AntilipschitzWith K (synthesis p) := by
  obtain ⟨c, C, hc, hC, h⟩ := synthesis_bounds p hp
  refine ⟨⟨c⁻¹, (inv_pos.mpr hc).le⟩, (synthesis p).antilipschitz_of_bound ?_⟩
  intro a
  change ‖a‖ ≤ c⁻¹ * ‖synthesis p a‖
  exact (le_inv_mul_iff₀ hc).mpr (h a).1

theorem synthesis_range (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    LinearMap.range (synthesis p).toLinearMap = closedSpan p := by
  obtain ⟨K, hK⟩ := synthesis_antilipschitz p hp
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (synthesis_hasSum p hp a)
    exact Filter.Eventually.of_forall fun s => Submodule.sum_mem _ fun j hj =>
      Submodule.smul_mem _ _ (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨j, rfl⟩))
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact ⟨lp.single 2 j 1, by simp [synthesis_single p hp]⟩
    · exact hK.isClosed_range (synthesis p).uniformContinuous

theorem completion_identification : CompletionIdentification := by
  intro p inst hp
  obtain ⟨K, hK⟩ := synthesis_antilipschitz p hp
  obtain ⟨c, C, hc, hC, hbounds⟩ := synthesis_bounds p hp
  let S := (synthesis p).equivRange hK.injective (hK.isClosed_range (synthesis p).uniformContinuous)
  let T := S.trans ((LinearIsometryEquiv.ofEq _ _ (synthesis_range p hp)).toContinuousLinearEquiv)
  refine ⟨T, c, C, hc, hC, ?_, ?_⟩
  · intro a
    exact hbounds a
  · intro a
    exact synthesis_hasSum p hp a

theorem infinite_dimensional_spans : InfiniteDimensionalSpans := by
  intro p inst hp hfinite
  letI := hfinite
  obtain ⟨S, hS⟩ := completion_identification p hp
  have hv : Orthonormal ℂ (fun j : ℕ => lp.single (E := fun _ : ℕ => ℂ) 2 j (1 : ℂ)) := by
    rw [orthonormal_iff_ite]
    intro i j
    simp [lp.inner_single_left, lp.single_apply, Pi.single_apply, RCLike.inner_apply]
  have hli := hv.linearIndependent.map' S.toLinearMap (LinearMap.ker_eq_bot.mpr S.injective)
  exact Module.Finite.not_linearIndependent_of_infinite _ hli

/-- Synthesis at different exponents represents the same measurable function. -/
theorem synthesis_consistent (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (a : Coeff) :
    (synthesis p a : LacunaryNormsSpec.Circle → ℂ) =ᵐ[μ]
      (synthesis 2 a : LacunaryNormsSpec.Circle → ℂ) := by
  have hfinite (q : ℝ≥0∞) [Fact (1 ≤ q)] (n : ℕ) :
      ((∑ j ∈ Finset.range n, a j • mode q j : Space q) : LacunaryNormsSpec.Circle → ℂ) =ᵐ[μ]
        (polynomial (Finset.range n) a : LacunaryNormsSpec.Circle → ℂ) := by
    have he : (∑ j ∈ Finset.range n, a j • mode q j : Space q) =
        ContinuousMap.toLp q μ ℂ (polynomial (Finset.range n) a) := by
      simp [polynomial, mode, fourierLp]
    rw [he]
    exact ContinuousMap.coeFn_toLp μ _
  have h₁ := tendstoInMeasure_of_tendsto_Lp (synthesis_hasSum p hp a).tendsto_sum_nat
  have h₂ := tendstoInMeasure_of_tendsto_Lp (synthesis_hasSum 2 (by simp) a).tendsto_sum_nat
  exact tendstoInMeasure_ae_unique (h₁.congr_left (hfinite p)) (h₂.congr_left (hfinite 2))

/-- The exact harmonic coefficient family, with the 1/0 term interpreted as zero. -/
def harmonicCoefficients : Coeff := ⟨harmonic, by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
  simpa [harmonic, Complex.norm_natCast, Real.rpow_two, ← inv_pow] using
    (Real.summable_nat_pow_inv.mpr (by omega : 1 < 2))⟩

@[simp] theorem harmonicCoefficients_apply (j : ℕ) : harmonicCoefficients j = harmonic j := rfl

/-- Boundary L² sum, defined by the same synthesis used at all finite p. -/
def harmonicSum : Space 2 := synthesis 2 harmonicCoefficients

theorem harmonicSum_hasSum : HasSum (fun j => harmonic j • mode 2 j) harmonicSum :=
  synthesis_hasSum 2 (by simp) harmonicCoefficients

theorem harmonicSum_common (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    ∃ g : closedSpan p, (g.val : LacunaryNormsSpec.Circle → ℂ) =ᵐ[μ]
      (harmonicSum : LacunaryNormsSpec.Circle → ℂ) := by
  refine ⟨⟨synthesis p harmonicCoefficients, ?_⟩, synthesis_consistent p hp harmonicCoefficients⟩
  rw [← synthesis_range p hp]
  exact LinearMap.mem_range_self _ _

theorem poissonFunctional_natMode (z : HardyDiskSpec.Disk) (n : ℕ) :
    HardyDisk.poissonFunctional z (fourierLp (T := 2 * π) 2 (n : ℤ)) = z.val ^ n := by
  have hb : HardyDiskSpec.boundary (lp.single 2 n (1 : ℂ)) = fourierLp 2 (n : ℤ) := by
    simp [HardyDiskSpec.boundary, HardyDiskSpec.modes]
  rw [← hb, ← HardyDisk.poissonExtension_eq_functional]
  change HardyDiskSpec.poissonExtension _ _ = _
  rw [HardyDisk.poisson_evaluation _ _ z.property, HardyDisk.monomial_evaluation, one_mul]

theorem poissonFunctional_mode (z : HardyDiskSpec.Disk) (j : ℕ) :
    HardyDisk.poissonFunctional z (mode 2 j) = z.val ^ frequency j :=
  poissonFunctional_natMode z (frequency j)

/-- Positive radii on the real axis in the open unit disk. -/
def radiusPoint (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) : HardyDiskSpec.Disk :=
  ⟨(r : ℂ), by simpa [HardyDiskSpec.disk, Metric.mem_ball, Complex.norm_real,
    abs_of_nonneg hr0] using hr1⟩

def poissonValue (r : ℝ) : ℝ := ∑' j : ℕ, r ^ frequency j / (j : ℝ)

theorem poissonValue_hasSum (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun j : ℕ => r ^ frequency j / (j : ℝ)) (poissonValue r) := by
  have h := (HardyDisk.poissonFunctional (radiusPoint r hr0 hr1)).hasSum harmonicSum_hasSum
  have he (j : ℕ) : HardyDisk.poissonFunctional (radiusPoint r hr0 hr1)
      (harmonic j • mode 2 j) = ((r ^ frequency j / (j : ℝ) : ℝ) : ℂ) := by
    rw [map_smul, poissonFunctional_mode]
    simp [radiusPoint, harmonic, div_eq_mul_inv, mul_comm]
  simp_rw [he] at h
  have hreal := Complex.reCLM.hasSum h
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at hreal
  exact hreal.summable.hasSum

theorem poissonValue_integral (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∫ t : LacunaryNormsSpec.Circle,
      ((1 - r ^ 2) / ‖fourier (T := 2 * π) 1 t - (r : ℂ)‖ ^ 2) • harmonicSum t ∂μ) =
        (poissonValue r : ℂ) := by
  have h := (HardyDisk.poissonFunctional (radiusPoint r hr0 hr1)).hasSum harmonicSum_hasSum
  have he (j : ℕ) : HardyDisk.poissonFunctional (radiusPoint r hr0 hr1)
      (harmonic j • mode 2 j) = ((r ^ frequency j / (j : ℝ) : ℝ) : ℂ) := by
    rw [map_smul, poissonFunctional_mode]
    simp [radiusPoint, harmonic, div_eq_mul_inv, mul_comm]
  simp_rw [he] at h
  have heq := h.unique (Complex.hasSum_ofReal.mpr (poissonValue_hasSum r hr0 hr1))
  rw [HardyDisk.poissonFunctional_apply] at heq
  simpa [radiusPoint, Complex.norm_real, abs_of_nonneg hr0] using heq

/-- Finite heads of the positive Poisson series tend to the harmonic heads.
Taking arbitrarily long heads proves divergence without interchanging limits. -/
theorem poissonValue_tendsto : Tendsto poissonValue (𝓝[<] (1 : ℝ)) atTop := by
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun n : ℕ => inv_nonneg.mpr (Nat.cast_nonneg n))).mp Real.not_summable_natCast_inv
  apply tendsto_atTop.mpr
  intro B
  obtain ⟨N, hN⟩ := (hdiv.eventually (eventually_ge_atTop (B + 1))).exists
  have hlim : Tendsto (fun r : ℝ => ∑ j ∈ Finset.range N, r ^ frequency j / (j : ℝ))
      (𝓝[<] (1 : ℝ)) (𝓝 (∑ j ∈ Finset.range N, (j : ℝ)⁻¹)) := by
    have hc : Continuous (fun r : ℝ => ∑ j ∈ Finset.range N, r ^ frequency j / (j : ℝ)) := by fun_prop
    convert (hc.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds using 1
    simp
  have hb : B < ∑ j ∈ Finset.range N, (j : ℝ)⁻¹ := by linarith
  filter_upwards [hlim.eventually (eventually_gt_nhds hb),
    (show ∀ᶠ r : ℝ in 𝓝[<] 1, 0 ≤ r from
      (eventually_ge_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono inf_le_left),
    self_mem_nhdsWithin] with r hr hr0 hr1
  apply hr.le.trans
  exact (poissonValue_hasSum r hr0 hr1).summable.sum_le_tsum _
    (fun j hj => div_nonneg (pow_nonneg hr0 _) (Nat.cast_nonneg j))

/-- The actual real Poisson density, with respect to Haar probability measure. -/
def poissonWeight (z : HardyDiskSpec.Disk) (t : LacunaryNormsSpec.Circle) : ℝ :=
  (1 - ‖z.val‖ ^ 2) / ‖fourier (T := 2 * π) 1 t - z.val‖ ^ 2

theorem poissonWeight_nonneg (z : HardyDiskSpec.Disk) (t : LacunaryNormsSpec.Circle) :
    0 ≤ poissonWeight z t := by
  have hz : ‖z.val‖ < 1 := by simpa only [HardyDiskSpec.disk, Metric.mem_ball, dist_zero_right] using z.property
  apply div_nonneg _ (sq_nonneg _)
  nlinarith [norm_nonneg z.val]

theorem poissonWeight_integrable (z : HardyDiskSpec.Disk) : Integrable (poissonWeight z) μ := by
  have hc : Continuous (poissonWeight z) := Complex.continuous_re.comp (HardyDisk.poissonKernelMap z).continuous
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem poissonWeight_mass (z : HardyDiskSpec.Disk) : (∫ t, poissonWeight z t ∂μ) = 1 := by
  have h := poissonFunctional_natMode z 0
  rw [HardyDisk.poissonFunctional_apply] at h
  have he : (∫ t : LacunaryNormsSpec.Circle, (poissonWeight z t : ℂ) ∂μ) =
      ∫ t : LacunaryNormsSpec.Circle, poissonWeight z t • fourierLp (T := 2 * π) 2 0 t ∂μ := by
    apply integral_congr_ae
    filter_upwards [coeFn_fourierLp (T := 2 * π) 2 0] with t ht
    rw [ht]
    simp
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, he]
  simpa [poissonWeight] using h

/-- Positivity and mass one make every essentially bounded boundary function
uniformly bounded under all its Poisson evaluations. -/
theorem poissonFunctional_bound (z : HardyDiskSpec.Disk) (f : Space 2) (M : ℝ)
    (hM : ∀ᵐ t ∂μ, ‖f t‖ ≤ M) : ‖HardyDisk.poissonFunctional z f‖ ≤ M := by
  rw [HardyDisk.poissonFunctional_apply]
  have hb := norm_integral_le_of_norm_le ((poissonWeight_integrable z).mul_const M)
    (show ∀ᵐ t ∂μ, ‖poissonWeight z t • f t‖ ≤ poissonWeight z t * M by
      filter_upwards [hM] with t ht
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (poissonWeight_nonneg z t)]
      exact mul_le_mul_of_nonneg_left ht (poissonWeight_nonneg z t))
  rw [integral_mul_const, poissonWeight_mass, one_mul] at hb
  exact hb

theorem harmonicSum_unbounded : ¬ ∃ M : ℝ, ∀ᵐ t ∂μ, ‖harmonicSum t‖ ≤ M := by
  rintro ⟨M, hM⟩
  have hlarge := poissonValue_tendsto.eventually (eventually_gt_atTop M)
  have hsmall : ∀ᶠ r : ℝ in 𝓝[<] 1, poissonValue r ≤ M := by
    filter_upwards [(show ∀ᶠ r : ℝ in 𝓝[<] 1, 0 ≤ r from
      (eventually_ge_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono inf_le_left),
      self_mem_nhdsWithin] with r hr0 hr1
    have hb := poissonFunctional_bound (radiusPoint r hr0 hr1) harmonicSum M hM
    have he : HardyDisk.poissonFunctional (radiusPoint r hr0 hr1) harmonicSum =
        (poissonValue r : ℂ) := by
      rw [HardyDisk.poissonFunctional_apply]
      simpa [radiusPoint, Complex.norm_real, abs_of_nonneg hr0] using poissonValue_integral r hr0 hr1
    rw [he, Complex.norm_real, Real.norm_eq_abs] at hb
    exact (le_abs_self _).trans hb
  obtain ⟨r, hr, hr'⟩ := (hlarge.and hsmall).exists
  exact (not_le_of_gt hr) hr'

theorem common_unbounded_member : CommonUnboundedMember :=
  ⟨harmonicSum, harmonicSum_hasSum, harmonicSum_common, harmonicSum_unbounded⟩

theorem positive_poisson_values : PositivePoissonValues :=
  ⟨harmonicSum, harmonicSum_hasSum, poissonValue_integral, poissonValue_tendsto⟩

end ExpandedFA.PartIV.LacunarySubspace
