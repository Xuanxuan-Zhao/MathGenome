import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.TorusFourierBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

noncomputable section
open MeasureTheory Filter
open scoped Real ENNReal NNReal Topology

namespace ExpandedFA.Fourier.TorusFourierBasis
open TorusFourierBasisSpec

theorem complete_orthonormal : CompleteOrthonormal := by
  intro T hT
  exact ⟨orthonormal_fourier, span_fourierLp_closure_eq_top (by simp)⟩

theorem basis : Basis := by
  intro T hT
  exact ⟨fourierBasis, fun n => congrFun coe_fourierBasis n⟩

theorem expansion : Expansion := by
  intro T hT f
  exact hasSum_fourier_series_L2 f

theorem parseval : Parseval := by
  intro T hT f
  have h := lp.hasSum_norm (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (fourierBasis.repr f)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, fourierBasis_repr,
    LinearIsometryEquiv.norm_map] using h

theorem coefficient_surjective : CoefficientSurjective := by
  intro T hT a
  refine ⟨fourierBasis.repr.symm a, fun n => ?_⟩
  rw [← fourierBasis_repr, LinearIsometryEquiv.apply_symm_apply]

theorem coefficient_unitary : CoefficientUnitary := by
  intro T hT
  exact ⟨fourierBasis.repr, fourierBasis_repr⟩

theorem trigonometric_density : TrigonometricDensity := by
  intro T hT
  exact span_fourier_closure_eq_top

theorem modes : Modes := by
  constructor
  · intro n θ
    rw [fourier_coe_apply]
    congr 1
    push_cast
    field_simp
  · intro n x
    rw [fourier_coe_apply]
    simp

theorem normalized_integral : NormalizedIntegral := by
  intro T hT f a
  rw [AddCircle.integral_haarAddCircle]
  congr 1
  exact (AddCircle.intervalIntegral_preimage T a f).symm

theorem coordinate_map : CoordinateMap := by
  constructor
  · intro x
    simp only [angleChange, AddCircle.equivAddCircle_apply_mk, inv_one, one_mul]
    congr 1
    ring
  · intro θ
    simp [angleChange, div_eq_mul_inv]

theorem coordinate_measurePreserving : CoordinateMeasurePreserving := by
  constructor
  · exact angleChange.toAddMonoidHom.measurePreserving
      (AddCircle.continuous_equivAddCircle _ _ _ _) angleChange.surjective (by simp)
  · exact angleChange.symm.toAddMonoidHom.measurePreserving
      (AddCircle.homeomorphAddCircle 1 (2 * π) one_ne_zero (by positivity)).symm.continuous
      angleChange.symm.surjective (by simp)

theorem coordinate_modes : CoordinateModes := by
  intro n x
  induction x using QuotientAddGroup.induction_on with | H x =>
  rw [coordinate_map.1, fourier_coe_apply, fourier_coe_apply]
  congr 1
  push_cast
  field_simp

theorem coordinate_derivative : CoordinateDerivative := by
  intro f f' x hf
  convert hf.scomp x ((hasDerivAt_id x).const_mul (2 * π)) using 1 <;>
    simp [Function.comp_def, mul_comm]

theorem circle_coordinate_derivative : CircleCoordinateDerivative := by
  intro f f' x hf
  simpa only [coordinate_map.1] using
    coordinate_derivative (fun θ : ℝ => f (θ : AddCircle (2 * π))) f' x hf

theorem sobolev_weight : SobolevWeight := by
  intro n
  rw [← Complex.ofReal_intCast]
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one, mul_pow, sq_abs]
  ring

theorem mode_derivatives : ModeDerivatives := by
  constructor
  · intro n θ
    convert hasDerivAt_fourier (2 * π) n θ using 1
    push_cast
    field_simp
  · intro n x
    simpa using hasDerivAt_fourier 1 n x

/-- Pair an L¹ function with a continuous test function. The operator norm is
bounded by the L¹ norm; this allows uniform trigonometric density to be used. -/
private def integralTest {T : ℝ} [Fact (0 < T)] (f : AddCircle T → ℂ)
    (hf : Integrable f AddCircle.haarAddCircle) : C(AddCircle T, ℂ) →L[ℂ] ℂ := by
  have hi (g : C(AddCircle T, ℂ)) :
      Integrable (fun x => g x * f x) AddCircle.haarAddCircle :=
    hf.bdd_mul g.continuous.aestronglyMeasurable
      (ae_of_all _ fun x => g.norm_coe_le_norm x)
  let L : C(AddCircle T, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => ∫ x, g x * f x ∂AddCircle.haarAddCircle
      map_add' := by
        intro g h
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (hi g) (hi h)
      map_smul' := by
        intro c g
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc,
          integral_const_mul] }
  refine L.mkContinuous (∫ x, ‖f x‖ ∂AddCircle.haarAddCircle) fun g => ?_
  change ‖∫ x, g x * f x ∂AddCircle.haarAddCircle‖ ≤ _
  calc
    _ ≤ ∫ x, ‖g‖ * ‖f x‖ ∂AddCircle.haarAddCircle :=
      norm_integral_le_of_norm_le (hf.norm.const_mul ‖g‖) (ae_of_all _ fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm x) (norm_nonneg _))
    _ = _ := by rw [integral_const_mul, mul_comm]

private theorem integral_test_zero {T : ℝ} [Fact (0 < T)] (f : AddCircle T → ℂ)
    (hf : Integrable f AddCircle.haarAddCircle) (h : ∀ n, fourierCoeff f n = 0)
    (g : C(AddCircle T, ℂ)) : ∫ x, g x * f x ∂AddCircle.haarAddCircle = 0 := by
  let L := integralTest f hf
  have hs : Submodule.span ℂ (Set.range (fourier (T := T))) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    change ∫ x, fourier n x * f x ∂AddCircle.haarAddCircle = 0
    simpa only [fourierCoeff, neg_neg, smul_eq_mul] using h (-n)
  have hc := Submodule.topologicalClosure_minimal _ hs L.isClosed_ker
  rw [span_fourier_closure_eq_top] at hc
  exact hc (Submodule.mem_top : g ∈ (⊤ : Submodule ℂ C(AddCircle T, ℂ)))

/-- Closed-set indicators can be approximated by continuous functions between
zero and one. Dominated convergence upgrades continuous tests to measurable tests. -/
private theorem l1_zero_of_coeff_zero {T : ℝ} [Fact (0 < T)] (f : AddCircle T → ℂ)
    (hf : Integrable f AddCircle.haarAddCircle) (h : ∀ n, fourierCoeff f n = 0) :
    f =ᵐ[AddCircle.haarAddCircle] 0 := by
  apply ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero hf
  intro s hs
  let g (n : ℕ) : C(AddCircle T, ℂ) :=
    ⟨fun x => ((hs.apprSeq n x : ℝ) : ℂ), by fun_prop⟩
  have hz (n : ℕ) : ∫ x, g n x * f x ∂AddCircle.haarAddCircle = 0 :=
    integral_test_zero f hf h (g n)
  have hlim : ∀ x, Tendsto (fun n => g n x) atTop
      (𝓝 (((s.indicator (fun _ => (1 : ℝ≥0)) x : ℝ≥0) : ℝ) : ℂ)) := by
    intro x
    exact (Complex.continuous_ofReal.tendsto _).comp
      ((NNReal.continuous_coe.tendsto _).comp
        (tendsto_pi_nhds.mp (HasOuterApproxClosed.tendsto_apprSeq hs) x))
  have H : Tendsto (fun n => ∫ x, g n x * f x ∂AddCircle.haarAddCircle)
      atTop (𝓝 (∫ x in s, f x ∂AddCircle.haarAddCircle)) := by
    rw [← integral_indicator hs.measurableSet]
    apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    · intro n
      exact (g n).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable
    · exact hf.norm
    · intro n
      apply ae_of_all
      intro x
      simp only [g, ContinuousMap.coe_mk, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (by
        exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hs n x)
    · apply ae_of_all
      intro x
      convert (hlim x).mul_const (f x) using 1
      by_cases hx : x ∈ s <;> simp [hx]
  exact (tendsto_nhds_unique (by simpa only [hz] using H) tendsto_const_nhds)

theorem l1_unique : L1Unique := by
  intro T hT f g hf hg h
  have hsub (n : ℤ) : fourierCoeff (f - g) n = 0 := by
    simp only [fourierCoeff, Pi.sub_apply, smul_sub]
    rw [integral_sub (hf.fourier_smul _) (hg.fourier_smul _)]
    exact sub_eq_zero.mpr (h n)
  filter_upwards [l1_zero_of_coeff_zero (f - g) (hf.sub hg) hsub] with x hx
  exact sub_eq_zero.mp hx

theorem continuous_unique : ContinuousUnique := by
  intro T hT f g h
  apply ContinuousMap.coe_injective
  exact (f.continuous.ae_eq_iff_eq AddCircle.haarAddCircle g.continuous).mp
    (l1_unique T f g (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) h)

theorem periodic_unique : PeriodicUnique := by
  intro T hT f g hf hg hfp hgp a h
  let F : C(AddCircle T, ℂ) := ⟨hfp.lift, continuous_coinduced_dom.mpr hf⟩
  let G : C(AddCircle T, ℂ) := ⟨hgp.lift, continuous_coinduced_dom.mpr hg⟩
  have hF (n : ℤ) : fourierCoeff F n =
      fourierCoeffOn (lt_add_of_pos_right a hT.out) f n := by
    rw [fourierCoeff_eq_intervalIntegral F n a, fourierCoeffOn_eq_integral]
    simp only [fourier_coe_apply, add_sub_cancel_left, F, ContinuousMap.coe_mk,
      Function.Periodic.lift_coe]
  have hG (n : ℤ) : fourierCoeff G n =
      fourierCoeffOn (lt_add_of_pos_right a hT.out) g n := by
    rw [fourierCoeff_eq_intervalIntegral G n a, fourierCoeffOn_eq_integral]
    simp only [fourier_coe_apply, add_sub_cancel_left, G, ContinuousMap.coe_mk,
      Function.Periodic.lift_coe]
  have H := continuous_unique T F G (fun n => (hF n).trans ((h n).trans (hG n).symm))
  funext x
  exact congrArg (fun k : C(AddCircle T, ℂ) => k (x : AddCircle T)) H

/-- Composition with the inverse rescaling gives the inverse on the a.e. quotients. -/
private theorem comp_angle_surjective : Function.Surjective
    (Lp.compMeasurePreservingₗᵢ ℂ angleChange coordinate_measurePreserving.1 :
      Lp ℂ 2 (AddCircle.haarAddCircle (T := 2 * π)) →ₗᵢ[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) := by
  intro f
  refine ⟨Lp.compMeasurePreserving angleChange.symm coordinate_measurePreserving.2 f, ?_⟩
  change Lp.compMeasurePreserving angleChange coordinate_measurePreserving.1
    (Lp.compMeasurePreserving angleChange.symm coordinate_measurePreserving.2 f) = f
  rw [← Lp.compMeasurePreserving_comp_apply]
  have h : (angleChange.symm ∘ angleChange) = id := funext angleChange.symm_apply_apply
  simp only [h, Lp.compMeasurePreserving_id_apply]

theorem coordinate_unitary : CoordinateUnitary := by
  let U : Lp ℂ 2 (AddCircle.haarAddCircle (T := 2 * π)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) := LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ angleChange coordinate_measurePreserving.1)
    comp_angle_surjective
  have hU (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 2 * π))) :
      U f =ᵐ[AddCircle.haarAddCircle] f ∘ angleChange :=
    Lp.coeFn_compMeasurePreserving f coordinate_measurePreserving.1
  refine ⟨U, hU, ?_, ?_⟩
  · intro n
    apply Lp.ext
    filter_upwards [hU (fourierLp (T := 2 * π) 2 n),
      coordinate_measurePreserving.1.quasiMeasurePreserving.ae (coeFn_fourierLp (T := 2 * π) 2 n),
      coeFn_fourierLp (T := 1) 2 n] with x hx ha hb
    simpa only [Function.comp_apply, hx, ha, hb] using coordinate_modes n x
  · intro f n
    calc
      fourierCoeff (U f) n =
          ∫ x : AddCircle (1 : ℝ), fourier (-n) (angleChange x) •
            f (angleChange x) ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        filter_upwards [hU f] with x hx
        rw [hx, Function.comp_apply, coordinate_modes]
      _ = fourierCoeff f n :=
        coordinate_measurePreserving.1.integral_comp
          (AddCircle.homeomorphAddCircle 1 (2 * π) one_ne_zero (by positivity)).measurableEmbedding
          (fun y : AddCircle (2 * π) => fourier (-n) y • f y)

end ExpandedFA.Fourier.TorusFourierBasis
