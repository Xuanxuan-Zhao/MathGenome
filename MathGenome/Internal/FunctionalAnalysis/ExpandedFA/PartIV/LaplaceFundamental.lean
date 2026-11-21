import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.LaplaceFundamental
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.DistributionCalculus
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.ProperSupportConvolution
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped Distributions ContDiff

namespace ExpandedFA.PartIV.LaplaceFundamental
open ExpandedFA.Distributions

theorem euclideanRadius_one (x : Domain 1) : euclideanRadius x = |x 0| := by
  simp [euclideanRadius, EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]

theorem kernel_formulas : Specs.ExpandedFA.PartIV.LaplaceFundamental.formulasType := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simp [kernel, euclideanRadius_one]
  · intro x
    simp [kernel]
  · intro d hd x
    have h1 : d ≠ 1 := by omega
    have h2 : d ≠ 2 := by omega
    simp [kernel, h1, h2]

@[simp] theorem diracZero_apply (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) : diracZero 𝕜 d φ = φ 0 := rfl

/-- The even transpose sign is positive. -/
theorem distributionLaplacian_apply {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    distributionLaplacian u φ = u (testLaplacian φ) := by
  classical
  simp [distributionLaplacian, testLaplacian,
    Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue, map_sum]

/-- The test Laplacian is the sum of the ordinary coordinate second derivatives. -/
theorem testLaplacian_apply {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (x : Domain d) :
    testLaplacian φ x = ∑ i : Fin d, partialFunction [i, i] φ x := by
  classical
  rw [testLaplacian, test_sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (testPartial_formula 𝕜 d ⊤ [i, i] φ) x

/-- Exact distributional pairing once local integrability has been established. -/
theorem kernelDistribution_apply {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (hf : LocallyIntegrable (scalarKernel 𝕜 d) volume)
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    kernelDistribution 𝕜 d φ = ∫ x, scalarKernel 𝕜 d x * φ x := by
  exact regularDistribution_apply volume (scalarKernel 𝕜 d)
    (hf.locallyIntegrableOn _) φ

/-- The analytic integral identity implies the full equality of distributions. -/
theorem fundamentalSolution_of_pairing
    (hloc : Specs.ExpandedFA.PartIV.LaplaceFundamental.localIntegrabilityType)
    (hpair : Specs.ExpandedFA.PartIV.LaplaceFundamental.pairingType) :
    Specs.ExpandedFA.PartIV.LaplaceFundamental.fundamentalSolutionType := by
  intro 𝕜 _ d hd
  ext φ
  rw [distributionLaplacian_apply, kernelDistribution_apply (hloc 𝕜 d hd)]
  exact hpair 𝕜 d hd φ

/-- Euclidean radial powers are locally integrable above the critical exponent. -/
theorem locallyIntegrable_radius_rpow {d : ℕ} (hd : 1 ≤ d) {a : ℝ}
    (ha : -(d : ℝ) < a) :
    LocallyIntegrable (fun x : Domain d => euclideanRadius x ^ a) volume := by
  have h : LocallyIntegrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ a) volume := by
    refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := -a)
      (by simpa using hd) ?_ ?_ ?_
    · simp only [finrank_euclideanSpace, Fintype.card_fin]
      linarith
    · filter_upwards [] with x
      simp [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) a)]
    · exact (measurable_norm.pow_const a).aestronglyMeasurable
  have hm : Measure.map (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) volume = volume :=
    (PiLp.volume_preserving_ofLp (ι := Fin d)).map_eq
  rw [← hm]
  exact (locallyIntegrable_map_homeomorph _).2 (by
    change LocallyIntegrable (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ a) volume
    exact h)

theorem continuous_euclideanRadius (d : ℕ) : Continuous (@euclideanRadius d) := by
  exact (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).symm.continuous.norm

/-- The elementary global bound avoids treating infinity as an integrability
singularity: |log r| ≤ r + r⁻¹ for r ≥ 0. -/
theorem abs_log_le_add_inv {r : ℝ} (hr : 0 ≤ r) : |Real.log r| ≤ r + r⁻¹ := by
  apply abs_le.mpr
  constructor
  · have h := Real.neg_inv_le_log hr
    linarith
  · have h := Real.log_le_self hr
    have hi := inv_nonneg.mpr hr
    linarith

theorem locallyIntegrable_radius_log {d : ℕ} (hd : 2 ≤ d) :
    LocallyIntegrable (fun x : Domain d => Real.log (euclideanRadius x)) volume := by
  have hp : LocallyIntegrable (fun x : Domain d => euclideanRadius x ^ (-1 : ℝ)) volume :=
    locallyIntegrable_radius_rpow (by omega) (by exact_mod_cast (show -(d : ℤ) < -1 by omega))
  have hi : LocallyIntegrable (fun x : Domain d => (euclideanRadius x)⁻¹) volume := by
    simpa only [Real.rpow_neg_one] using hp
  have hb := (continuous_euclideanRadius d).locallyIntegrable.add hi
  apply hb.mono
  · exact (Real.measurable_log.comp (continuous_euclideanRadius d).measurable).aestronglyMeasurable
  · filter_upwards [] with x
    change |Real.log (euclideanRadius x)| ≤ |euclideanRadius x + (euclideanRadius x)⁻¹|
    rw [abs_of_nonneg (add_nonneg (show 0 ≤ euclideanRadius x from norm_nonneg _)
      (inv_nonneg.mpr (show 0 ≤ euclideanRadius x from norm_nonneg _))) ]
    exact abs_log_le_add_inv (norm_nonneg _)

theorem locallyIntegrable_kernel {d : ℕ} (hd : 1 ≤ d) :
    LocallyIntegrable (kernel d) volume := by
  by_cases h1 : d = 1
  · subst d
    change LocallyIntegrable (fun x : Domain 1 => euclideanRadius x / 2) volume
    simpa only [Pi.smul_def, smul_eq_mul, mul_comm, div_eq_mul_inv] using
      ((continuous_euclideanRadius 1).locallyIntegrable (μ := volume)).smul (2 : ℝ)⁻¹
  by_cases h2 : d = 2
  · subst d
    change LocallyIntegrable (fun x : Domain 2 => Real.log (euclideanRadius x) / (2 * Real.pi)) volume
    simpa only [Pi.smul_def, smul_eq_mul, mul_comm, div_eq_mul_inv] using
      (locallyIntegrable_radius_log (d := 2) (by omega)).smul (2 * Real.pi)⁻¹
  · have hd3 : 3 ≤ d := by omega
    have hp : LocallyIntegrable (fun x : Domain d => euclideanRadius x ^ (2 - (d : ℝ))) volume :=
      locallyIntegrable_radius_rpow hd (by linarith)
    have heq : kernel d = fun x => euclideanRadius x ^ (2 - (d : ℝ)) /
        ((2 - (d : ℝ)) * sphereArea d) := by
      funext x
      simp only [kernel, ite_eq_right h1, ite_eq_right h2]
    rw [heq]
    simpa only [Pi.smul_def, smul_eq_mul, mul_comm, div_eq_mul_inv] using
      hp.smul (((2 - (d : ℝ)) * sphereArea d)⁻¹)

theorem local_integrability :
    Specs.ExpandedFA.PartIV.LaplaceFundamental.localIntegrabilityType := by
  intro 𝕜 _ d hd
  apply (locallyIntegrable_kernel hd).mono
  · exact RCLike.continuous_ofReal.comp_aestronglyMeasurable
      (locallyIntegrable_kernel hd).aestronglyMeasurable
  · filter_upwards [] with x
    simp [scalarKernel, RCLike.algebraMap_eq_ofReal]

/-- The full PDE conclusion for convolution with compact distribution data.
The auxiliary cutoff covers {0} as well as the support of the fundamental
solution, so no unproved formula for the support of delta is needed. -/
theorem laplacian_convolution_solution {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (E v u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (hv : IsCompact (distributionSupport v)) (hconv : IsProperConvolution E v u)
    (hE : distributionLaplacian E = diracZero 𝕜 d) : distributionLaplacian u = v := by
  classical
  let S : Set (Domain d) := distributionSupport E ∪ {0}
  have hS : IsClosed S := (ProperSupportConvolution.support_closed 𝕜 d E).union isClosed_singleton
  have hproper : AdditionProper S (distributionSupport v) :=
    ProperSupportConvolution.compact_support_suffices d S _ hS hv.isClosed (Or.inr hv)
  ext φ
  obtain ⟨χ, V, hV, hSV, hχ⟩ := ProperSupportConvolution.compact_product_cutoff _
    (hproper (tsupport φ) φ.hasCompactSupport)
  have had (w : List (Fin d)) : AdmissibleConvolutionCutoff
      (distributionDerivative 𝕜 d ⊤ w E) v φ χ := by
    refine ⟨V, hV, ?_, hχ⟩
    intro p hp
    exact hSV ⟨⟨Or.inl (ProperSupportConvolution.derivative_support 𝕜 d E w hp.1.1),
      hp.1.2⟩, hp.2⟩
  have hpair (i : Fin d) : distributionDerivative 𝕜 d ⊤ [i, i] u φ =
      distributionDerivative 𝕜 d ⊤ [i, i] E
        (ProperSupportConvolution.kernelActionTest v (cutoffAdditionTest χ φ)) := by
    have hc := (ProperSupportConvolution.convolution_derivatives 𝕜 d E v u [i, i] hconv).1
    exact hc.2.2 _
      (ProperSupportConvolution.iteratedTensor_isTensorProduct
        (distributionDerivative 𝕜 d ⊤ [i, i] E) v) φ χ (had [i, i])
  have heval : distributionLaplacian u φ =
      v (ProperSupportConvolution.kernelSection (cutoffAdditionTest χ φ) 0) := by
    calc
      _ = ∑ i : Fin d, distributionDerivative 𝕜 d ⊤ [i, i] u φ := by
        simp [distributionLaplacian, distributionDerivative]
      _ = ∑ i : Fin d, distributionDerivative 𝕜 d ⊤ [i, i] E
          (ProperSupportConvolution.kernelActionTest v (cutoffAdditionTest χ φ)) :=
        Finset.sum_congr rfl (fun i _ => hpair i)
      _ = distributionLaplacian E
          (ProperSupportConvolution.kernelActionTest v (cutoffAdditionTest χ φ)) := by
        simp [distributionLaplacian, distributionDerivative]
      _ = _ := by rw [hE]; rfl
  rw [heval]
  let W : Set (Domain d) := (fun y : Domain d => ((0 : Domain d), y)) ⁻¹' V ∪ (tsupport φ)ᶜ
  apply pairing_locality 𝕜 d ⊤ v _ φ W
  · exact (hV.preimage (continuous_const.prodMk continuous_id)).union isClosed_closure.isOpen_compl
  · intro y hy
    by_cases hφ : y ∈ tsupport φ
    · exact Or.inl (hSV ⟨⟨Or.inr (by simp), hy⟩, by simpa using hφ⟩)
    · exact Or.inr hφ
  · intro y hy
    change χ (0, y) • φ (0 + y) = φ y
    rw [zero_add]
    rcases hy with hy | hy
    · simp only [hχ hy, Pi.one_apply, one_smul]
    · rw [image_eq_zero_of_notMem_tsupport hy, smul_zero]

/-- Assembly of the convolution conclusion from the fundamental-solution identity. -/
theorem convolutionSolution_of_fundamentalSolution
    (hfund : Specs.ExpandedFA.PartIV.LaplaceFundamental.fundamentalSolutionType) :
    Specs.ExpandedFA.PartIV.LaplaceFundamental.convolutionSolutionType := by
  intro 𝕜 _ d hd v hv
  have hc := ProperSupportConvolution.compact_distribution_suffices 𝕜 d
    (kernelDistribution 𝕜 d) v (Or.inr hv)
  obtain ⟨u, hu, _⟩ := ProperSupportConvolution.convolution_existence 𝕜 d _ _ hc
  exact ⟨u, hu, laplacian_convolution_solution _ _ _ hv hu (hfund 𝕜 d hd)⟩

lemma line_fundamental_pairing {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (f : ℝ → F) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    ∫ t : ℝ, (|t| / 2) • deriv (deriv f) t = f 0 := by
  have hf' : ContDiff ℝ ∞ (deriv f) := ContDiff.deriv' (n := ∞) (by simpa using hf)
  have hf'' : ContDiff ℝ ∞ (deriv (deriv f)) := ContDiff.deriv' (n := ∞) (by simpa using hf')
  let g : ℝ → F := fun t => t • deriv f t - f t
  have hg : ContDiff ℝ ∞ g := (contDiff_id.smul hf').sub hf
  have hgs : HasCompactSupport g := hs.deriv.smul_left.sub hs
  have hg' : deriv g = fun t => t • deriv (deriv f) t := by
    funext t
    have h1 := (hf.differentiable (by simp) t).hasDerivAt
    have h2 := (hf'.differentiable (by simp) t).hasDerivAt
    have h := ((hasDerivAt_id t).smul h2).sub h1
    have heq : (id : ℝ → ℝ) • deriv f - f = g := by funext x; rfl
    rw [heq] at h
    simpa only [id_eq, one_smul, add_sub_cancel_right] using h.deriv
  have hpos : ∫ t in Ioi (0 : ℝ), t • deriv (deriv f) t = f 0 := by
    have h := HasCompactSupport.integral_Ioi_deriv_eq (hg.of_le (by simp)) hgs 0
    simpa [hg', g] using h
  have hneg : ∫ t in Iic (0 : ℝ), t • deriv (deriv f) t = - f 0 := by
    have h := HasCompactSupport.integral_Iic_deriv_eq (hg.of_le (by simp)) hgs 0
    simpa [hg', g] using h
  have hint : Integrable (fun t : ℝ => (|t| / 2) • deriv (deriv f) t) :=
    (continuous_abs.div_const 2 |>.smul hf''.continuous).integrable_of_hasCompactSupport
      hs.deriv.deriv.smul_left
  rw [← integral_add_compl measurableSet_Iic hint]
  have hn : ∫ t in Iic (0 : ℝ), (|t| / 2) • deriv (deriv f) t = (1 / 2 : ℝ) • f 0 := by
    calc
      _ = ∫ t in Iic (0 : ℝ), (-1 / 2 : ℝ) • (t • deriv (deriv f) t) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro t ht
        change (|t| / 2) • deriv (deriv f) t = (-1 / 2 : ℝ) • (t • deriv (deriv f) t)
        rw [abs_of_nonpos ht, smul_smul]
        congr 1
        ring
      _ = (-1 / 2 : ℝ) • (-f 0) := by rw [integral_smul, hneg]
      _ = _ := by rw [smul_neg, ← neg_smul]; norm_num
  have hp : ∫ t in Ioi (0 : ℝ), (|t| / 2) • deriv (deriv f) t = (1 / 2 : ℝ) • f 0 := by
    calc
      _ = ∫ t in Ioi (0 : ℝ), (1 / 2 : ℝ) • (t • deriv (deriv f) t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change (|t| / 2) • deriv (deriv f) t = (1 / 2 : ℝ) • (t • deriv (deriv f) t)
        rw [abs_of_pos ht, smul_smul]
        congr 1
        ring
      _ = _ := by rw [integral_smul, hpos]
  rw [compl_Iic, hn, hp, ← add_smul]
  norm_num

/-- The isometric coordinate identification ℝ ≃ ℝ¹. -/
def lineCoordinate : ℝ ≃L[ℝ] Domain 1 :=
  (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ)).symm

@[simp] theorem lineCoordinate_apply (t : ℝ) (i : Fin 1) : lineCoordinate t i = t := rfl

lemma lineCoordinate_one : lineCoordinate 1 = coordinateVector (0 : Fin 1) := by
  ext i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  simp [coordinateVector]

/-- Chain rule under the single Euclidean coordinate. -/
lemma deriv_lineCoordinate {𝕜 : Type} [RCLike 𝕜] (f : Domain 1 → 𝕜)
    (hf : Differentiable ℝ f) (t : ℝ) :
    deriv (f ∘ lineCoordinate) t =
      fderiv ℝ f (lineCoordinate t) (coordinateVector (0 : Fin 1)) := by
  have h := (hf (lineCoordinate t)).hasFDerivAt.comp_hasDerivAt t
    (lineCoordinate.toContinuousLinearMap.hasDerivAt (x := t))
  have hder := h.deriv
  change deriv (f ∘ lineCoordinate) t = fderiv ℝ f (lineCoordinate t) (lineCoordinate 1) at hder
  rwa [lineCoordinate_one] at hder

/-- Exact one-dimensional jump calculation, including the scalar-linear delta. -/
theorem pairing_one (𝕜 : Type) [RCLike 𝕜]
    (φ : Tests 𝕜 (⊤ : Opens (Domain 1))) :
    ∫ x, scalarKernel 𝕜 1 x * testLaplacian φ x = φ 0 := by
  let f : ℝ → 𝕜 := φ ∘ lineCoordinate
  have hf : ContDiff ℝ ∞ f := φ.contDiff.comp lineCoordinate.contDiff
  have hs : HasCompactSupport f := φ.hasCompactSupport.comp_homeomorph lineCoordinate.toHomeomorph
  have hfirst : deriv f = (testPartialCLM [0] φ) ∘ lineCoordinate := by
    funext t
    rw [deriv_lineCoordinate φ (φ.contDiff.differentiable (by simp))]
    rw [testPartial_formula 𝕜 1 ⊤ [0] φ]
    rfl
  have hsecond (t : ℝ) : deriv (deriv f) t = testLaplacian φ (lineCoordinate t) := by
    rw [hfirst, deriv_lineCoordinate _
      ((testPartialCLM [0] φ).contDiff.differentiable (by simp))]
    rw [testPartial_formula 𝕜 1 ⊤ [0] φ, testLaplacian_apply]
    simp only [Fin.sum_univ_one]
    rfl
  have hchange := (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)).symm.integral_comp
    (MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)).symm.measurableEmbedding
    (fun x => scalarKernel 𝕜 1 x * testLaplacian φ x)
  rw [← hchange]
  have hzero : f 0 = φ 0 := by simp [f]
  rw [← hzero, ← line_fundamental_pairing f hf hs]
  apply integral_congr_ae
  filter_upwards [] with t
  change scalarKernel 𝕜 1 (lineCoordinate t) * testLaplacian φ (lineCoordinate t) = _
  rw [scalarKernel, kernel_formulas.1, lineCoordinate_apply, hsecond,
    Algebra.smul_def]

theorem fundamental_solution_one :
    Specs.ExpandedFA.PartIV.LaplaceFundamental.fundamentalSolutionOneType := by
  intro 𝕜 _
  ext φ
  rw [distributionLaplacian_apply, kernelDistribution_apply (local_integrability 𝕜 1 (by omega))]
  exact pairing_one 𝕜 φ

theorem convolution_solution_one :
    Specs.ExpandedFA.PartIV.LaplaceFundamental.convolutionSolutionOneType := by
  intro 𝕜 _ v hv
  have hc := ProperSupportConvolution.compact_distribution_suffices 𝕜 1
    (kernelDistribution 𝕜 1) v (Or.inr hv)
  obtain ⟨u, hu, _⟩ := ProperSupportConvolution.convolution_existence 𝕜 1 _ _ hc
  exact ⟨u, hu, laplacian_convolution_solution _ _ _ hv hu (fundamental_solution_one 𝕜)⟩

/-- Integration by parts across an isolated singularity in dimension at least two.
A transverse coordinate hyperplane is null; setting the density to zero there
makes its restriction to every coordinate line differentiable. -/
lemma integral_smul_lineDeriv_off_origin {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {d : ℕ} (hd : 2 ≤ d) (i : Fin d)
    (f f' : Domain d → ℝ) (g g' : Domain d → F)
    (hfg : Integrable (fun x => f x • g x))
    (hf'g : Integrable (fun x => f' x • g x))
    (hfg' : Integrable (fun x => f x • g' x))
    (hf : ∀ x ≠ 0, HasLineDerivAt ℝ f (f' x) x (coordinateVector i))
    (hg : ∀ x, HasLineDerivAt ℝ g (g' x) x (coordinateVector i)) :
    ∫ x, f x • g' x = - ∫ x, f' x • g x := by
  classical
  obtain ⟨j, hji⟩ : ∃ j : Fin d, j ≠ i := by
    have : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
    exact exists_ne i
  let fm : Domain d → ℝ := fun x => if x j = 0 then 0 else f x
  let fm' : Domain d → ℝ := fun x => if x j = 0 then 0 else f' x
  have hae : ∀ᵐ x : Domain d, x j ≠ 0 := Measure.ae_eval_ne (fun _ => volume) j 0
  have heq : fm =ᵐ[volume] f := hae.mono (fun x hx => ite_eq_right hx)
  have heq' : fm' =ᵐ[volume] f' := hae.mono (fun x hx => ite_eq_right hx)
  have hm : ∀ x, HasLineDerivAt ℝ fm (fm' x) x (coordinateVector i) := by
    intro x
    have hline (t : ℝ) : (x + t • coordinateVector i) j = x j := by
      simp [coordinateVector, Pi.single_eq_of_ne hji]
    by_cases hx : x j = 0
    · change HasDerivAt (fun t : ℝ => fm (x + t • coordinateVector i)) (fm' x) 0
      simpa [fm, fm', hline, hx] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    · have hx0 : x ≠ 0 := by intro h; apply hx; simp [h]
      have h := hf x hx0
      change HasDerivAt (fun t : ℝ => fm (x + t • coordinateVector i)) (fm' x) 0
      simpa [fm, fm', hline, hx, HasLineDerivAt] using h
  have h := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := volume) (B := ContinuousLinearMap.lsmul ℝ ℝ)
    (hf'g.congr (heq'.symm.mono (fun x hx => congrArg (fun a => a • g x) hx)))
    (hfg'.congr (heq.symm.mono (fun x hx => congrArg (fun a => a • g' x) hx)))
    (hfg.congr (heq.symm.mono (fun x hx => congrArg (fun a => a • g x) hx)))
    (fun x _ => hm x) (fun x _ => hg x)
  change (∫ x, fm x • g' x) = - ∫ x, fm' x • g x at h
  rw [integral_congr_ae (heq.mono (fun x hx => congrArg (fun a => a • g' x) hx)),
    integral_congr_ae (heq'.mono (fun x hx => congrArg (fun a => a • g x) hx))] at h
  exact h

@[simp] theorem euclideanRadius_eq_zero {d : ℕ} (x : Domain d) :
    euclideanRadius x = 0 ↔ x = 0 := by
  rw [euclideanRadius, norm_eq_zero]
  constructor
  · intro h
    exact congrArg WithLp.ofLp h
  · rintro rfl
    rfl

lemma euclideanRadius_pos {d : ℕ} {x : Domain d} (hx : x ≠ 0) :
    0 < euclideanRadius x :=
  lt_of_le_of_ne (norm_nonneg _) (Ne.symm (mt (euclideanRadius_eq_zero x).mp hx))

lemma coordinate_le_euclideanRadius {d : ℕ} (x : Domain d) (i : Fin d) :
    |x i| ≤ euclideanRadius x := by
  exact PiLp.norm_apply_le (WithLp.toLp 2 x) i

lemma radius_hasLineDerivAt {d : ℕ} (x : Domain d) (hx : x ≠ 0) (i : Fin d) :
    HasLineDerivAt ℝ euclideanRadius (x i / euclideanRadius x) x (coordinateVector i) := by
  classical
  have hs (j : Fin d) : HasDerivAt
      (fun t : ℝ => (x j + t * coordinateVector i j) ^ 2)
      (2 * x j * coordinateVector i j) 0 := by
    convert! (((hasDerivAt_id (0 : ℝ)).mul_const (coordinateVector i j)).const_add (x j)).pow 2 using 1
    simp
  have hs' : HasDerivAt (fun t : ℝ => euclideanRadius (x + t • coordinateVector i) ^ 2)
      (2 * x i) 0 := by
    simpa [euclideanRadius, EuclideanSpace.real_norm_sq_eq, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, coordinateVector, Pi.single_apply] using
      (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hs j))
  have h := hs'.sqrt (by simpa using (pow_ne_zero 2 (euclideanRadius_pos hx).ne'))
  change HasDerivAt (fun t : ℝ => euclideanRadius (x + t • coordinateVector i)) _ 0
  have hsqrt (y : Domain d) : √(euclideanRadius y ^ 2) = euclideanRadius y :=
    Real.sqrt_sq (norm_nonneg _)
  simpa [hsqrt, mul_div_mul_left _ _ (show (2 : ℝ) ≠ 0 by norm_num)] using h

lemma sphereArea_pos {d : ℕ} (hd : 1 ≤ d) : 0 < sphereArea d := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have : NeZero ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) :=
    ⟨Measure.toSphere_ne_zero _⟩
  exact measureReal_univ_pos

lemma sphereArea_two : sphereArea 2 = 2 * Real.pi := by
  simp [sphereArea, EuclideanSpace.volume_ball_fin_two,
    measureReal_def, ENNReal.toReal_ofReal Real.pi_pos.le]

/-- The (locally integrable) coordinate components of the kernel gradient. -/
def kernelGradient (d : ℕ) (i : Fin d) (x : Domain d) : ℝ :=
  x i * euclideanRadius x ^ (-(d : ℝ)) / sphereArea d

lemma kernel_hasLineDerivAt {d : ℕ} (hd : 2 ≤ d) (x : Domain d) (hx : x ≠ 0)
    (i : Fin d) :
    HasLineDerivAt ℝ (kernel d) (kernelGradient d i x) x (coordinateVector i) := by
  have hr := radius_hasLineDerivAt x hx i
  have hpos := euclideanRadius_pos hx
  have h1 : d ≠ 1 := by omega
  by_cases h2 : d = 2
  · subst d
    have h := (hr.log (by simpa using hpos.ne')).div_const (2 * Real.pi)
    change HasDerivAt (fun t : ℝ => kernel 2 (x + t • coordinateVector i)) _ 0
    convert h using 1
    · funext t
      simp [kernel]
    · simp only [zero_smul, add_zero, kernelGradient, sphereArea_two, Nat.cast_ofNat]
      rw [show -(2 : ℝ) = (-2 : ℝ) by norm_num, Real.rpow_neg hpos.le, Real.rpow_two]
      field_simp
  · have hdne : (2 - (d : ℝ)) ≠ 0 := by
      have : (3 : ℝ) ≤ d := by exact_mod_cast (show 3 ≤ d by omega)
      linarith
    have h := (hr.rpow_const (p := 2 - (d : ℝ)) (Or.inl (by simpa using hpos.ne'))).div_const
      ((2 - (d : ℝ)) * sphereArea d)
    change HasDerivAt (fun t : ℝ => kernel d (x + t • coordinateVector i)) _ 0
    convert h using 1
    · funext t
      simp [kernel, h1, h2]
    · dsimp [kernelGradient]
      have hp : euclideanRadius x ^ (2 - (d : ℝ) - 1) =
          euclideanRadius x * euclideanRadius x ^ (-(d : ℝ)) := by
        calc
          _ = euclideanRadius x ^ ((1 : ℝ) + -(d : ℝ)) := by congr 1; ring
          _ = _ := by rw [Real.rpow_add hpos, Real.rpow_one]
      simp only [zero_smul, add_zero]
      rw [hp]
      field_simp [hpos.ne', hdne]

lemma locallyIntegrable_kernelGradient {d : ℕ} (hd : 1 ≤ d) (i : Fin d) :
    LocallyIntegrable (kernelGradient d i) volume := by
  have hp : LocallyIntegrable (fun x : Domain d => euclideanRadius x ^ (1 - (d : ℝ))) volume :=
    locallyIntegrable_radius_rpow hd (by linarith)
  have hg : LocallyIntegrable (fun x : Domain d => x i * euclideanRadius x ^ (-(d : ℝ))) volume := by
    apply hp.mono
    · exact ((measurable_pi_apply i).mul
        ((continuous_euclideanRadius d).measurable.pow_const _)).aestronglyMeasurable
    · filter_upwards [] with x
      by_cases hx : x = 0
      · subst x
        simp
      · have hpos := euclideanRadius_pos hx
        simp only [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg hpos.le _)]
        calc
          _ ≤ euclideanRadius x * euclideanRadius x ^ (-(d : ℝ)) :=
            mul_le_mul_of_nonneg_right (coordinate_le_euclideanRadius x i) (by positivity)
          _ = _ := by
            conv_lhs => lhs; rw [← Real.rpow_one (euclideanRadius x)]
            rw [← Real.rpow_add hpos]
            congr 1
  unfold kernelGradient
  simpa only [Pi.smul_def, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    hg.smul (sphereArea d)⁻¹

/-- The first weak integration by parts, valid through the singularity at zero. -/
lemma pairing_kernel_gradient {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (hd : 2 ≤ d)
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (i : Fin d) :
    ∫ x, kernel d x • testPartialCLM [i, i] φ x =
      - ∫ x, kernelGradient d i x • testPartialCLM [i] φ x := by
  let g := testPartialCLM [i] φ
  have hg : ∀ x, HasLineDerivAt ℝ g (testPartialCLM [i, i] φ x) x (coordinateVector i) := by
    intro x
    have h := (g.contDiff.differentiable (by simp) x).hasFDerivAt.hasLineDerivAt (coordinateVector i)
    convert h using 1
    rw [testPartial_formula 𝕜 d ⊤ [i, i] φ]
    simp only [partialFunction]
    change _ = fderiv ℝ (testPartialCLM [i] φ) x (coordinateVector i)
    rw [testPartial_formula 𝕜 d ⊤ [i] φ]
    rfl
  exact integral_smul_lineDeriv_off_origin hd i (kernel d) (kernelGradient d i) g _
    ((locallyIntegrable_kernel (by omega)).integrable_smul_right_of_hasCompactSupport
      g.continuous g.hasCompactSupport)
    ((locallyIntegrable_kernelGradient (by omega) i).integrable_smul_right_of_hasCompactSupport
      g.continuous g.hasCompactSupport)
    ((locallyIntegrable_kernel (by omega)).integrable_smul_right_of_hasCompactSupport
      (testPartialCLM [i, i] φ).continuous (testPartialCLM [i, i] φ).hasCompactSupport)
    (fun x hx => kernel_hasLineDerivAt hd x hx i) hg

/-- Polar integration for a general integrable function, with the actual
surface measure and the unnormalized radial Jacobian. -/
lemma integral_polar_coordinates {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {d : ℕ} (hd : 1 ≤ d) (f : EuclideanSpace ℝ (Fin d) → F)
    (hf : Integrable f) :
    ∫ x, f x = ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      (∫ r in Ioi (0 : ℝ), r ^ (d - 1) • f (r • θ.1))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let E := EuclideanSpace ℝ (Fin d)
  let G := fun p : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ) => f ((homeomorphUnitSphereProd E).symm p).1
  have hsub : Integrable (fun x : ({0}ᶜ : Set E) => f x.1) (volume.comap Subtype.val) := by
    exact (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mp hf.integrableOn
  have hG : Integrable G ((volume : Measure E).toSphere.prod (Measure.volumeIoiPow (d - 1))) := by
    have h := ((volume : Measure E).measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
      (homeomorphUnitSphereProd E).measurableEmbedding (g := G)).mp (by simpa only [G, Function.comp_def, Homeomorph.symm_apply_apply] using hsub)
    simpa [E] using h
  calc
    _ = ∫ x : ({0}ᶜ : Set E), f x.1 ∂(volume.comap Subtype.val) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
    _ = ∫ p, G p ∂(volume : Measure E).toSphere.prod (Measure.volumeIoiPow (d - 1)) := by
      have h := (volume : Measure E).measurePreserving_homeomorphUnitSphereProd.integral_comp
        (homeomorphUnitSphereProd E).measurableEmbedding G
      simpa only [G, Function.comp_def, Homeomorph.symm_apply_apply, E, finrank_euclideanSpace, Fintype.card_fin] using h
    _ = _ := by
      rw [integral_prod _ hG]
      apply integral_congr_ae
      filter_upwards [] with θ
      simp only [G, homeomorphUnitSphereProd_symm_apply_coe, Measure.volumeIoiPow, ENNReal.ofReal]
      rw [integral_withDensity_eq_integral_smul,
        integral_subtype_comap measurableSet_Ioi
          (fun r : ℝ => Real.toNNReal (r ^ (d - 1)) • f (r • θ.1))]
      · apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        dsimp only
        rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hr.le _)]
      · exact (measurable_subtype_coe.pow_const _).real_toNNReal

/-- The ray restriction of a compact test has the usual endpoint identity. -/
lemma integral_ray_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {d : ℕ} (f : Domain d → F) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (θ : Domain d) (hθ : θ ≠ 0) :
    ∫ r in Ioi (0 : ℝ), fderiv ℝ f (r • θ) θ = -f 0 := by
  let ray : ℝ → Domain d := fun r => r • θ
  have hc : ContDiff ℝ ∞ (f ∘ ray) := hf.comp (contDiff_id.smul contDiff_const)
  have hcs : HasCompactSupport (f ∘ ray) := hs.comp_isClosedEmbedding (isClosedEmbedding_smul_left hθ)
  have heq : deriv (f ∘ ray) = fun r => fderiv ℝ f (r • θ) θ := by
    funext r
    simpa [ray] using ((hf.differentiable (by simp) (r • θ)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).smul_const θ)).deriv
  simpa [heq, ray] using HasCompactSupport.integral_Ioi_deriv_eq (hc.of_le (by simp)) hcs 0

lemma sum_kernelGradient_partial {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (x : Domain d) :
    (∑ i : Fin d, kernelGradient d i x • testPartialCLM [i] φ x) =
      (euclideanRadius x ^ (-(d : ℝ)) / sphereArea d) • fderiv ℝ φ x x := by
  classical
  have hx : ∑ i : Fin d, x i • coordinateVector i = x := by
    ext j
    simp [coordinateVector, Pi.single_apply]
  have hgrad (i : Fin d) : kernelGradient d i x =
      (euclideanRadius x ^ (-(d : ℝ)) / sphereArea d) * x i := by
    unfold kernelGradient
    ring
  have hpartial (i : Fin d) : testPartialCLM [i] φ x = fderiv ℝ φ x (coordinateVector i) := by
    exact congrFun (testPartial_formula 𝕜 d ⊤ [i] φ) x
  simp_rw [hgrad, mul_smul, hpartial]
  rw [← Finset.smul_sum]
  congr 1
  calc
    _ = fderiv ℝ φ x (∑ i : Fin d, x i • coordinateVector i) := by simp [map_sum, map_smul]
    _ = _ := by rw [hx]

/-- Polar integration of the weak gradient gives exactly one point mass. -/
lemma integral_kernelGradient {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (hd : 1 ≤ d)
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    ∫ x, (∑ i : Fin d, kernelGradient d i x • testPartialCLM [i] φ x) = -φ 0 := by
  classical
  let f : Domain d → 𝕜 := fun x => ∑ i : Fin d, kernelGradient d i x • testPartialCLM [i] φ x
  have hf : Integrable f := integrable_finsetSum _ (fun i _ =>
    (locallyIntegrable_kernelGradient hd i).integrable_smul_right_of_hasCompactSupport
      (testPartialCLM [i] φ).continuous (testPartialCLM [i] φ).hasCompactSupport)
  let g : EuclideanSpace ℝ (Fin d) → 𝕜 := f ∘ WithLp.ofLp
  have hg : Integrable g := (PiLp.volume_preserving_ofLp (ι := Fin d)).integrable_comp_of_integrable hf
  have hchange := (PiLp.volume_preserving_ofLp (ι := Fin d)).integral_comp
    (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).measurableEmbedding f
  change (∫ x, f x) = -φ 0
  rw [← hchange]
  change (∫ x, g x) = -φ 0
  rw [integral_polar_coordinates hd g hg]
  have hinner (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
      (∫ r in Ioi (0 : ℝ), r ^ (d - 1) • g (r • θ.1)) =
        (sphereArea d)⁻¹ • (-φ 0) := by
    have hnorm : ‖θ.1‖ = 1 := by simp
    have hθ : WithLp.ofLp θ.1 ≠ (0 : Domain d) := by
      intro h
      have h' : θ.1 = 0 := congrArg (WithLp.toLp 2) h
      simp [h'] at hnorm
    calc
      _ = ∫ r in Ioi (0 : ℝ), (sphereArea d)⁻¹ •
          fderiv ℝ φ (r • WithLp.ofLp θ.1) (WithLp.ofLp θ.1) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        have hrpos : 0 < r := hr
        change r ^ (d - 1) • (∑ i : Fin d,
          kernelGradient d i (WithLp.ofLp (r • θ.1)) •
            testPartialCLM [i] φ (WithLp.ofLp (r • θ.1))) = _
        rw [sum_kernelGradient_partial]
        have hradius : euclideanRadius (r • WithLp.ofLp θ.1) = r := by
          simp [euclideanRadius, norm_smul, abs_of_pos hrpos, hnorm]
        simp only [WithLp.ofLp_smul, hradius, map_smul, smul_smul]
        congr 1
        rw [Real.rpow_neg hrpos.le, Real.rpow_natCast]
        have hrne := ne_of_gt hrpos
        have hpow : r ^ (d - 1) * r = r ^ d := by
          rw [← pow_succ, Nat.sub_add_cancel hd]
        field_simp [hrne]
        rw [hpow]
      _ = (sphereArea d)⁻¹ •
          ∫ r in Ioi (0 : ℝ), fderiv ℝ φ (r • WithLp.ofLp θ.1) (WithLp.ofLp θ.1) := integral_smul _ _
      _ = _ := by rw [integral_ray_deriv φ φ.contDiff φ.hasCompactSupport _ hθ]
  simp_rw [hinner]
  rw [integral_const]
  change sphereArea d • ((sphereArea d)⁻¹ • (-φ 0)) = -φ 0
  rw [smul_smul, mul_inv_cancel₀ (sphereArea_pos hd).ne', one_smul]

/-- The complete scalar-linear pairing, including the mass at the origin. -/
theorem pairing_identity : Specs.ExpandedFA.PartIV.LaplaceFundamental.pairingType := by
  intro 𝕜 _ d hd φ
  by_cases h1 : d = 1
  · subst d
    exact pairing_one 𝕜 φ
  have hd2 : 2 ≤ d := by omega
  classical
  have hmul (x : Domain d) : scalarKernel 𝕜 d x * testLaplacian φ x =
      ∑ i : Fin d, kernel d x • testPartialCLM [i, i] φ x := by
    rw [scalarKernel, ← Algebra.smul_def, testLaplacian, test_sum_apply, Finset.smul_sum]
  have hint (i : Fin d) : Integrable
      (fun x => kernel d x • testPartialCLM [i, i] φ x) :=
    (locallyIntegrable_kernel hd).integrable_smul_right_of_hasCompactSupport
      (testPartialCLM [i, i] φ).continuous (testPartialCLM [i, i] φ).hasCompactSupport
  have hgrad (i : Fin d) : Integrable
      (fun x => kernelGradient d i x • testPartialCLM [i] φ x) :=
    (locallyIntegrable_kernelGradient hd i).integrable_smul_right_of_hasCompactSupport
      (testPartialCLM [i] φ).continuous (testPartialCLM [i] φ).hasCompactSupport
  calc
    _ = ∑ i : Fin d, ∫ x, kernel d x • testPartialCLM [i, i] φ x := by
      simp_rw [hmul]
      exact integral_finsetSum _ (fun i _ => hint i)
    _ = - ∑ i : Fin d, ∫ x, kernelGradient d i x • testPartialCLM [i] φ x := by
      simp_rw [pairing_kernel_gradient hd2 φ]
      rw [Finset.sum_neg_distrib]
    _ = - ∫ x, ∑ i : Fin d, kernelGradient d i x • testPartialCLM [i] φ x := by
      rw [integral_finsetSum _ (fun i _ => hgrad i)]
    _ = φ 0 := by rw [integral_kernelGradient hd φ, neg_neg]

/-- Each displayed kernel is a fundamental solution for Δ, with its exact sign. -/
theorem fundamental_solution :
    Specs.ExpandedFA.PartIV.LaplaceFundamental.fundamentalSolutionType :=
  fundamentalSolution_of_pairing local_integrability pairing_identity

/-- Convolution with every compactly supported scalar distribution solves Δu = v. -/
theorem convolution_solution :
    Specs.ExpandedFA.PartIV.LaplaceFundamental.convolutionSolutionType :=
  convolutionSolution_of_fundamentalSolution fundamental_solution

end ExpandedFA.PartIV.LaplaceFundamental
