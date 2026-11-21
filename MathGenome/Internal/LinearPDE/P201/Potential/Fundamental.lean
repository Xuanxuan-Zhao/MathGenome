import MathGenome.Internal.LinearPDE.P201Specs.Potential.Fundamental
import MathGenome.Internal.LinearPDE.P201.Common.SpatialInterfaces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.LaplaceFundamental
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.Norm

noncomputable section
open Set TopologicalSpace MeasureTheory Metric
open scoped ContDiff
namespace P201
abbrev fundamentalKernel : P201Specs.fundamentalKernelType := P201Specs.fundamentalKernel
abbrev fundamentalProfile : P201Specs.fundamentalProfileType := P201Specs.fundamentalProfile
abbrev originDirac : P201Specs.originDiracType := P201Specs.originDirac

private abbrev coordEquiv (n : ℕ) : (Fin n → ℝ) ≃L[ℝ] Space n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm

private theorem omega_eq_sphereArea {n : ℕ} (hn : n ≠ 1) :
    omega n = ExpandedFA.PartIV.LaplaceFundamental.sphereArea n := by
  simp only [omega, P201Specs.omega, P201Specs.unitSurface, ite_eq_right hn,
    ExpandedFA.PartIV.LaplaceFundamental.sphereArea]
  rw [Measure.real, Measure.map_apply_of_aemeasurable (by fun_prop) MeasurableSet.univ]
  rfl

private theorem kernel_bridge (n : ℕ) (x : Fin n → ℝ) :
    fundamentalKernel n (coordEquiv n x) =
      -ExpandedFA.PartIV.LaplaceFundamental.kernel n x := by
  unfold fundamentalKernel P201Specs.fundamentalKernel P201Specs.fundamentalProfile
  unfold ExpandedFA.PartIV.LaplaceFundamental.kernel
  by_cases h1 : n = 1
  · simp [h1, ExpandedFA.PartIV.LaplaceFundamental.euclideanRadius, coordEquiv, neg_div]
  by_cases h2 : n = 2
  · simp [h2, ExpandedFA.PartIV.LaplaceFundamental.euclideanRadius, coordEquiv]
    ring
  · simp only [ite_eq_right h1, ite_eq_right h2]
    rw [show (n : ℝ) - 2 = -(2 - (n : ℝ)) by ring]
    rw [show P201Specs.omega n = _ from omega_eq_sphereArea h1, neg_mul, div_neg]
    rfl

private def coordinateTest {n : ℕ} (φ : Test ℝ (⊤ : Domain n)) :
    ExpandedFA.Distributions.Tests ℝ (⊤ : Opens (Fin n → ℝ)) :=
  ⟨φ ∘ coordEquiv n, φ.contDiff.comp (coordEquiv n).contDiff,
    φ.hasCompactSupport.comp_isClosedEmbedding (coordEquiv n).toHomeomorph.isClosedEmbedding,
    subset_univ _⟩

private theorem coordinate_vector {n : ℕ} (i : Fin n) :
    coordEquiv n (ExpandedFA.Distributions.coordinateVector i) = coordinate n i := by
  ext j
  simp [coordEquiv, ExpandedFA.Distributions.coordinateVector, coordinate,
    P201Specs.coordinate, P102.U4.coordinateVector, EuclideanSpace.basisFun_apply]

private theorem partial_bridge {n : ℕ} (φ : Test ℝ (⊤ : Domain n)) (w : List (Fin n)) :
    ExpandedFA.Distributions.partialFunction w (coordinateTest φ) =
      P102.U4.partialWord φ w ∘ coordEquiv n := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    simp only [ExpandedFA.Distributions.partialFunction, ih, P102.U4.partialWord,
      Function.comp_apply]
    rw [fderiv_comp x (P102.U4.partialWord_contDiff φ.contDiff w |>.differentiable (by simp) _)
      (coordEquiv n).differentiableAt]
    simp only [ContinuousLinearEquiv.fderiv, ContinuousLinearMap.comp_apply]
    congr 1
    exact coordinate_vector i

private theorem coordinate_laplacian {n : ℕ} (φ : Test ℝ (⊤ : Domain n))
    (x : Fin n → ℝ) :
    ExpandedFA.PartIV.LaplaceFundamental.testLaplacian (coordinateTest φ) x =
      laplacian φ (coordEquiv n x) := by
  rw [ExpandedFA.PartIV.LaplaceFundamental.testLaplacian_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [partial_bridge]
  change P102.U4.partialWord φ [i, i] (coordEquiv n x) =
    P102.U4.partialWord φ (({i, i} : MultiIndex n).sort (· ≤ ·)) (coordEquiv n x)
  congr 2
  simp [Multiset.sort_cons]

theorem fundamentalLocalIntegrability : P201Specs.fundamentalLocalIntegrabilityStatement := by
  intro n hn
  have h := (ExpandedFA.PartIV.LaplaceFundamental.locallyIntegrable_kernel hn).neg
  have hm : Measure.map (coordEquiv n).toHomeomorph volume = volume :=
    (PiLp.volume_preserving_toLp (ι := Fin n)).map_eq
  rw [← hm]
  apply (locallyIntegrable_map_homeomorph (coordEquiv n).toHomeomorph).2
  change LocallyIntegrable (fun x => fundamentalKernel n (coordEquiv n x)) volume
  have heq : (fun x => fundamentalKernel n (coordEquiv n x)) =
      -ExpandedFA.PartIV.LaplaceFundamental.kernel n := by
    funext x
    exact kernel_bridge n x
  rw [heq]
  exact h

/-- Analytic pairing on the canonical Euclidean space. -/
theorem fundamental_pairing {n : ℕ} (hn : 1 ≤ n) (φ : Test ℝ (⊤ : Domain n)) :
    ∫ x, fundamentalKernel n x * laplacian φ x = -φ 0 := by
  have h := ExpandedFA.PartIV.LaplaceFundamental.pairing_identity ℝ n hn (coordinateTest φ)
  have hc := (PiLp.volume_preserving_toLp (ι := Fin n)).integral_comp
    (coordEquiv n).toHomeomorph.measurableEmbedding
    (fun x => fundamentalKernel n x * laplacian φ x)
  change (∫ x, fundamentalKernel n x * laplacian φ x) = _
  rw [← hc]
  calc
    _ = -(∫ x, ExpandedFA.PartIV.LaplaceFundamental.scalarKernel ℝ n x *
        ExpandedFA.PartIV.LaplaceFundamental.testLaplacian (coordinateTest φ) x) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with x
      change fundamentalKernel n (coordEquiv n x) * laplacian φ (coordEquiv n x) = _
      rw [← coordinate_laplacian, kernel_bridge]
      simp [ExpandedFA.PartIV.LaplaceFundamental.scalarKernel]
    _ = _ := by rw [h]; rfl

private theorem distribution_laplacian_apply {n : ℕ} (u : Distribution ℝ (⊤ : Domain n))
    (φ : Test ℝ (⊤ : Domain n)) :
    distributionLaplacian u φ = ∑ i : Fin n, u (P102.U4.testPartialWord ⊤ [i, i] φ) := by
  simp [distributionLaplacian, P201Specs.distributionLaplacian,
    P201Specs.distributionDerivative, P102.U4.distributionPartial,
    Multiset.sort_cons]

theorem fundamentalSolution : P201Specs.fundamentalSolutionStatement := by
  intro n hn
  ext φ
  change -distributionLaplacian (regularDistribution ⊤ (fundamentalKernel n)) φ = φ 0
  rw [distribution_laplacian_apply]
  have hloc := (fundamentalLocalIntegrability n hn).locallyIntegrableOn (univ : Set (Space n))
  simp_rw [show ∀ ψ : Test ℝ (⊤ : Domain n),
      regularDistribution ⊤ (fundamentalKernel n) ψ = ∫ x, fundamentalKernel n x * ψ x from
    fun ψ => by simpa using P102.U4.regular_pairing n ℝ ⊤ (fundamentalKernel n) hloc ψ]
  have hint (i : Fin n) : Integrable (fun x => fundamentalKernel n x *
      P102.U4.testPartialWord (⊤ : Domain n) [i, i] φ x) := by
    exact (fundamentalLocalIntegrability n hn).integrable_smul_right_of_hasCompactSupport
      (P102.U4.testPartialWord (⊤ : Domain n) [i, i] φ).continuous
      (P102.U4.testPartialWord (⊤ : Domain n) [i, i] φ).hasCompactSupport
  rw [← integral_finsetSum _ (fun i _ => hint i)]
  have heq : (fun x => ∑ i : Fin n, fundamentalKernel n x *
      P102.U4.testPartialWord ⊤ [i, i] φ x) = fun x => fundamentalKernel n x * laplacian φ x := by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [P102.U4.testPartialWord_coe]
    congr 1
    simp [P201Specs.multiPartial,
      P102.U4.multiPartial, Multiset.sort_cons]
  rw [heq, fundamental_pairing hn, neg_neg]

private theorem omega_one : omega 1 = 2 := by
  change (P201Specs.unitSurface 1).real univ = 2
  rw [unitSurfaceDimensionOne]
  norm_num [Measure.real]

private theorem omega_two : omega 2 = 2 * Real.pi := by
  rw [omega_eq_sphereArea (by norm_num)]
  exact ExpandedFA.PartIV.LaplaceFundamental.sphereArea_two

private theorem omega_pos {n : ℕ} (hn : 1 ≤ n) : 0 < omega n := by
  by_cases h1 : n = 1
  · subst n; rw [omega_one]; norm_num
  · rw [omega_eq_sphereArea h1]
    exact ExpandedFA.PartIV.LaplaceFundamental.sphereArea_pos hn

private theorem profile_derivative {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fundamentalProfile n) (-1 / (omega n * r ^ (n - 1))) r := by
  by_cases h1 : n = 1
  · subst n
    change HasDerivAt (fun s : ℝ => -s / 2) (-1 / (omega 1 * r ^ (1 - 1))) r
    simpa only [omega_one, Nat.sub_self, pow_zero, mul_one, Pi.neg_apply, id_eq] using
      ((hasDerivAt_id r).neg.div_const 2)
  by_cases h2 : n = 2
  · subst n
    convert ((Real.hasDerivAt_log hr.ne').const_mul (-(1 / (2 * Real.pi)))) using 1
    · ext s
      simp [fundamentalProfile, P201Specs.fundamentalProfile]
    · rw [omega_two]
      norm_num
      ring
  · have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
    have hne : (n : ℝ) - 2 ≠ 0 := by linarith
    convert (Real.hasDerivAt_rpow_const (x := r) (p := 2 - (n : ℝ)) (Or.inl hr.ne')).div_const
      (((n : ℝ) - 2) * omega n) using 1
    · ext s
      simp [fundamentalProfile, P201Specs.fundamentalProfile, h1, h2]
    · have hexp : 2 - (n : ℝ) - 1 = -((n - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hn]
        push_cast
        ring
      rw [hexp, Real.rpow_neg hr.le, Real.rpow_natCast]
      field_simp
      ring

theorem fundamentalFlux : P201Specs.fundamentalFluxStatement := by
  intro n hn r hr
  have hd := profile_derivative hn hr
  refine ⟨hd, ?_⟩
  rw [hd.deriv, sphereSurfaceMass 0 r hr.le]
  exact div_mul_cancel₀ (-1) (mul_ne_zero (omega_pos hn).ne' (pow_ne_zero _ hr.ne'))

theorem fundamentalJump : P201Specs.fundamentalJumpStatement := by
  refine ⟨?_, ?_, by norm_num⟩
  · intro t ht
    simpa using (hasDerivAt_abs_neg ht).neg.div_const 2
  · intro t ht
    simpa using (hasDerivAt_abs_pos ht).neg.div_const 2

theorem fundamentalRepresentative : P201Specs.fundamentalRepresentativeStatement := by
  intro n hn c
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hae : Function.update (fundamentalKernel n) 0 c =ᵐ[volume] fundamentalKernel n := by
    filter_upwards [Measure.ae_ne (volume : Measure (Space n)) (0 : Space n)] with x hx
    exact Function.update_of_ne hx _ _
  refine ⟨(fundamentalLocalIntegrability n hn).congr hae.symm, ?_⟩
  have heq : regularDistribution (⊤ : Domain n) (Function.update (fundamentalKernel n) 0 c) =
      regularDistribution (⊤ : Domain n) (fundamentalKernel n) := by
    ext φ
    rw [P102.U4.regular_pairing n ℝ ⊤ _
      (((fundamentalLocalIntegrability n hn).congr hae.symm).locallyIntegrableOn _),
      P102.U4.regular_pairing n ℝ ⊤ _ ((fundamentalLocalIntegrability n hn).locallyIntegrableOn _)]
    simp only [Opens.coe_top, Measure.restrict_univ]
    exact integral_congr_ae (hae.mono fun x hx => congrArg (fun a => a * φ x) hx)
  change -distributionLaplacian (regularDistribution (⊤ : Domain n)
    (Function.update (fundamentalKernel n) 0 c)) = originDirac n
  rw [heq]
  exact fundamentalSolution n hn

private theorem unitSurface_norm_ae (n : ℕ) : ∀ᵐ x ∂unitSurface n, ‖x‖ = 1 := by
  by_cases h1 : n = 1
  · subst n
    rw [show unitSurface 1 = _ from unitSurfaceDimensionOne]
    simp [ae_add_measure_iff, P102.Trace.Ordinary.linePoint,
      EuclideanSpace.norm_eq]
  · simp only [unitSurface, P201Specs.unitSurface, ite_eq_right h1]
    change ∀ᵐ x ∂Measure.map
      (fun θ : sphere (0 : Space n) 1 => (θ : Space n))
        (volume : Measure (Space n)).toSphere, ‖x‖ = 1
    apply (ae_map_iff (by fun_prop)
      (isClosed_eq continuous_norm continuous_const).measurableSet).2
    exact Filter.Eventually.of_forall (fun θ => by simpa using θ.property)

private theorem sphereSurface_norm_ae (n : ℕ) (r : ℝ) (hr : 0 < r) :
    ∀ᵐ x ∂sphereSurface (0 : Space n) r, ‖x‖ = r := by
  apply Measure.ae_smul_measure
  apply (ae_map_iff (by fun_prop)
    (isClosed_eq continuous_norm continuous_const).measurableSet).2
  filter_upwards [unitSurface_norm_ae n] with θ hθ
  simp [norm_smul, abs_of_pos hr, hθ]

theorem fundamentalOutwardFlux : P201Specs.fundamentalOutwardFluxStatement := by
  intro n hn r hr
  have heq (x : Space n) (hx : ‖x‖ = r) :
      fderiv ℝ (fundamentalKernel n) x (r⁻¹ • x) = -1 / (omega n * r ^ (n - 1)) := by
    have hx0 : x ≠ 0 := by intro hz; simp [hz] at hx; linarith
    have hnorm : DifferentiableAt ℝ (fun y : Space n => ‖y‖) x :=
      differentiableAt_id.norm ℝ hx0
    have hd := (profile_derivative hn (show 0 < ‖x‖ by rwa [hx])).comp_hasFDerivAt x
      hnorm.hasFDerivAt
    change fderiv ℝ (fundamentalProfile n ∘ (fun y : Space n => ‖y‖)) x (r⁻¹ • x) = _
    rw [hd.fderiv]
    simp only [smul_apply, map_smul, smul_eq_mul,
      hnorm.fderiv_norm_self, hx]
    rw [mul_left_comm, inv_mul_cancel₀ hr.ne', mul_one]
  refine ⟨heq, ?_⟩
  rw [integral_congr_ae ((sphereSurface_norm_ae n r hr).mono fun x hx => heq x hx), integral_const]
  change (sphereSurface (0 : Space n) r).real univ *
    (-1 / (omega n * r ^ (n - 1))) = -1
  rw [sphereSurfaceMass 0 r hr.le, mul_comm]
  exact div_mul_cancel₀ (-1) (mul_ne_zero (omega_pos hn).ne' (pow_ne_zero _ hr.ne'))

end P201
