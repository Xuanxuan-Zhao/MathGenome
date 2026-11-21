import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Weyl.SchrodingerGaussianCorner
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Weyl.GaussianCorner

noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate

namespace ExpandedFA.Weyl
open RegularWeylRepresentationSpec GaussianCornerSpec SchrodingerGaussianCornerSpec

theorem vacuum_representative (d : ℕ) :
    vacuum d =ᵐ[volume] vacuumFunction d := (vacuumFunction_memLp d).coeFn_toLp

theorem vacuumFunction_pos (d : ℕ) (t : Configuration d) :
    0 < (vacuumFunction d t).re := by
  change 0 < vacuumNormalization d * Real.exp _
  exact mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.exp_pos _)

/-- Completing the square after translating by half the position parameter. -/
theorem vacuum_coefficient_integrand {d : ℕ} (z : PhaseSpace d) (t : Configuration d) :
    conj (vacuumFunction d (t + (1 / 2 : ℝ) • z.1)) *
        (multiplier z (t + (1 / 2 : ℝ) • z.1) *
          vacuumFunction d (t + (1 / 2 : ℝ) • z.1 - z.1)) =
      (vacuumNormalization d : ℂ) ^ 2 *
        Complex.exp ((-configurationSquare z.1 / 4 : ℝ) : ℂ) *
        Complex.exp (-(1 : ℂ) * ∑ j, (t j : ℂ) ^ 2 +
          ∑ j, (Complex.I * (z.2 j : ℂ)) * t j) := by
  rw [show conj (vacuumFunction d (t + (1 / 2 : ℝ) • z.1)) =
    vacuumFunction d (t + (1 / 2 : ℝ) • z.1) from Complex.conj_ofReal _]
  unfold vacuumFunction multiplier
  simp only [Complex.ofReal_mul, Complex.ofReal_exp]
  calc
    _ = (vacuumNormalization d : ℂ) ^ 2 *
        Complex.exp (((-configurationSquare (t + (1 / 2 : ℝ) • z.1) / 2 : ℝ) : ℂ) +
          (((∑ j, z.2 j * ((t + (1 / 2 : ℝ) • z.1) j - z.1 j / 2)) : ℝ) : ℂ) * Complex.I +
          ((-configurationSquare (t + (1 / 2 : ℝ) • z.1 - z.1) / 2 : ℝ) : ℂ)) := by
      simp only [Complex.exp_add]
      ring
    _ = _ := by
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      unfold configurationSquare
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      simp only [← Finset.sum_neg_distrib, Finset.sum_div, Finset.sum_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem vacuumNormalization_cancel (d : ℕ) :
    (vacuumNormalization d : ℂ) ^ 2 * (Real.pi : ℂ) ^ ((d : ℂ) / 2) = 1 := by
  have he : ((d : ℂ) / 2) = (((d : ℝ) / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [he, ← Complex.ofReal_cpow Real.pi_pos.le]
  norm_cast
  unfold vacuumNormalization
  rw [← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le, ← Real.rpow_add Real.pi_pos]
  have he : -(d : ℝ) / 4 * (2 : ℕ) + (d : ℝ) / 2 = 0 := by push_cast; ring
  rw [he, Real.rpow_zero]

theorem vacuum_coefficient_all {d : ℕ} (z : PhaseSpace d) :
    inner ℂ (vacuum d) (SchrodingerActionValue z (vacuum d)) = (gaussianWeight z : ℂ) := by
  rw [L2.inner_def]
  have hi : (∫ t : Configuration d, conj (vacuumFunction d t) *
      (multiplier z t * vacuumFunction d (t - z.1))) = (gaussianWeight z : ℂ) := by
    rw [← integral_add_right_eq_self (fun t : Configuration d =>
      conj (vacuumFunction d t) * (multiplier z t * vacuumFunction d (t - z.1)))
      ((1 / 2 : ℝ) • z.1)]
    simp_rw [vacuum_coefficient_integrand]
    rw [integral_const_mul,
      GaussianFourier.integral_cexp_neg_mul_sum_add (by norm_num : 0 < (1 : ℂ).re)]
    simp only [div_one, Fintype.card_fin]
    have he : (∑ j, (Complex.I * (z.2 j : ℂ)) ^ 2) =
        -((configurationSquare z.2 : ℝ) : ℂ) := by
      simp [configurationSquare, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
        ← Complex.ofReal_sum, Finset.sum_neg_distrib]
    rw [he]
    calc
      _ = ((vacuumNormalization d : ℂ) ^ 2 * (Real.pi : ℂ) ^ ((d : ℂ) / 2)) *
          Complex.exp (((-configurationSquare z.1 / 4 : ℝ) : ℂ) +
            -((configurationSquare z.2 : ℝ) : ℂ) / (4 * 1)) := by
        rw [Complex.exp_add]
        ring
      _ = (gaussianWeight z : ℂ) := by
        rw [vacuumNormalization_cancel, one_mul]
        simp only [gaussianWeight, phaseSquare, configurationSquare, Complex.ofReal_exp]
        congr 1
        push_cast
        ring
  calc
    _ = ∫ t : Configuration d, conj (vacuumFunction d t) *
        (multiplier z t * vacuumFunction d (t - z.1)) := by
      apply integral_congr_ae
      have ht := (measurePreserving_sub_right (volume : Measure (Configuration d)) z.1).quasiMeasurePreserving.ae (vacuum_representative d)
      filter_upwards [vacuum_representative d, schrodinger_representative z (vacuum d), ht]
        with t hv hw ht
      simp only [RCLike.inner_apply, hw, hv, ht]
      ring
    _ = _ := hi

theorem vacuum_coefficient : VacuumCoefficient := by
  intro d _ z
  exact vacuum_coefficient_all z

theorem vacuum_norm : VacuumNorm := by
  intro d _
  have h := vacuum_coefficient_all (0 : PhaseSpace d)
  rw [schrodinger_zero, gaussianWeight_zero, Complex.ofReal_one] at h
  have hn : ‖vacuum d‖ ^ 2 = 1 := by
    rw [@norm_sq_eq_re_inner ℂ, h]
    rfl
  nlinarith [norm_nonneg (vacuum d)]

/-- Angular Fourier uniqueness transported to the original Pi coordinates. -/
theorem configuration_angular_uniqueness {d : ℕ} (g : Configuration d → ℂ)
    (hg : Integrable g) (hz : ∀ p : Configuration d,
      (∫ t, Complex.exp (((∑ j, p j * t j : ℝ) : ℂ) * Complex.I) * g t) = 0) :
    g =ᵐ[volume] 0 := by
  let e : Configuration d ≃L[ℝ] Fourier.Euclidean d :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let em := e.toHomeomorph.toMeasurableEquiv
  let μ := Measure.map em (volume : Measure (Configuration d))
  have : SigmaFinite μ := em.sigmaFinite_map
  have hi : Integrable (fun v => g (em.symm v)) μ := by
    rw [integrable_map_equiv]
    simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply] using hg
  have hzero : ∀ ξ, Fourier.weightedIntegralFourier μ (fun v => g (em.symm v)) ξ = 0 := by
    intro ξ
    unfold Fourier.weightedIntegralFourier
    rw [integral_map_equiv]
    convert hz (fun j => -2 * Real.pi * ξ j) using 1
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [MeasurableEquiv.symm_apply_apply]
    congr 2
    change -2 * (Real.pi : ℂ) * Complex.I * (inner ℝ (WithLp.toLp 2 t) ξ : ℝ) = _
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h := Fourier.Uniqueness.weighted_uniqueness d μ (fun v => g (em.symm v)) hi hzero
  have hh := em.measurableEmbedding.ae_map_iff.mp h
  filter_upwards [hh] with t ht
  simpa only [MeasurableEquiv.symm_apply_apply, Pi.zero_apply] using ht

/-- Pure momentum vectors already test every Fourier coefficient. -/
theorem vacuum_modulations_total {d : ℕ} (f : SchrodingerSpace d)
    (hf : ∀ p : Configuration d,
      inner ℂ f (SchrodingerActionValue (0, p) (vacuum d)) = 0) : f = 0 := by
  let g : Configuration d → ℂ := fun t => conj (f t) * vacuumFunction d t
  have hg : Integrable g := (L2.integrable_inner (𝕜 := ℂ) f (vacuum d)).congr (by
    filter_upwards [vacuum_representative d] with t ht
    simp only [g, RCLike.inner_apply, ht]
    ring)
  have hz (p : Configuration d) :
      (∫ t, Complex.exp (((∑ j, p j * t j : ℝ) : ℂ) * Complex.I) * g t) = 0 := by
    rw [← hf p, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [schrodinger_representative (0, p) (vacuum d), vacuum_representative d]
      with t hw hv
    simp only [sub_zero, hw, multiplier, Pi.zero_apply, zero_div,
      hv, RCLike.inner_apply, g]
    ring
  have hzero := configuration_angular_uniqueness g hg hz
  apply Lp.ext
  filter_upwards [hzero, Lp.coeFn_zero (ℂ) 2 (volume : Measure (Configuration d))] with t ht h0
  change conj (f t) * vacuumFunction d t = 0 at ht
  have hn : vacuumFunction d t ≠ 0 := by
    intro hn
    have hp := vacuumFunction_pos d t
    rw [hn, Complex.zero_re] at hp
    exact lt_irrefl _ hp
  have hc : conj (f t) = 0 := (mul_eq_zero.mp ht).resolve_right hn
  have hft : f t = 0 := by simpa only [map_eq_zero] using hc
  exact hft.trans h0.symm

theorem vacuum_orbit_dense : VacuumOrbitDense := by
  intro d _
  let K := Submodule.span ℂ (Set.range (fun z : PhaseSpace d =>
    SchrodingerActionValue z (vacuum d)))
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  change f = 0
  apply vacuum_modulations_total
  intro p
  exact (K.topologicalClosure.mem_orthogonal' f).mp hf _
    (K.le_topologicalClosure (Submodule.subset_span ⟨(0, p), rfl⟩))

/-- The coefficient normalization forces the Gaussian projection to fix h. -/
theorem gaussianProjection_vacuum {d : ℕ}
    (R : RegularRepresentation d (SchrodingerSpace d))
    (hR : ∀ z f, R.W z f = SchrodingerActionValue z f) :
    gaussianProjection R (vacuum d) = vacuum d := by
  have hm : (∫ z : PhaseSpace d, (gaussianWeight z : ℂ) * (gaussianWeight z : ℂ)) =
      (((2 * Real.pi) ^ d : ℝ) : ℂ) := by
    have h := gaussianCornerKernel_integral (0 : PhaseSpace d) 0
    simpa [gaussianCornerKernel, SymplecticFormValue, gaussianWeight_zero] using h
  have hip : inner ℂ (vacuum d) (gaussianProjection R (vacuum d)) = 1 := by
    rw [gaussianProjection_apply, gaussianVectorIntegral]
    erw [inner_smul_right_eq_smul (𝕜 := ℂ) (vacuum d)
      (∫ z : PhaseSpace d, gaussianWeight z • R.W z (vacuum d)) (gaussianNormalization d)]
    erw [← integral_inner (gaussianOrbit_integrable R (vacuum d))]
    change (gaussianNormalization d : ℂ) * (∫ z : PhaseSpace d,
      inner ℂ (vacuum d) (gaussianWeight z • R.W z (vacuum d))) = 1
    calc
      _ = (gaussianNormalization d : ℂ) *
          (∫ z : PhaseSpace d, (gaussianWeight z : ℂ) * (gaussianWeight z : ℂ)) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with z
        erw [inner_smul_right_eq_smul (𝕜 := ℂ) (vacuum d) (R.W z (vacuum d)) (gaussianWeight z)]
        rw [hR, vacuum_coefficient_all]
        rfl
      _ = 1 := by
        rw [hm, gaussianNormalization_eq_inv, Complex.ofReal_inv, inv_mul_cancel₀]
        exact Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have hhh : inner ℂ (vacuum d) (vacuum d) = 1 := by
    have h := vacuum_coefficient_all (0 : PhaseSpace d)
    rw [schrodinger_zero, gaussianWeight_zero, Complex.ofReal_one] at h
    exact h
  have hid : gaussianProjection R (gaussianProjection R (vacuum d)) =
      gaussianProjection R (vacuum d) :=
    congrArg (fun T : SchrodingerSpace d →L[ℂ] SchrodingerSpace d => T (vacuum d))
      (gaussianProjection_idempotent R)
  have hs (x y : SchrodingerSpace d) :
      inner ℂ (gaussianProjection R x) y = inner ℂ x (gaussianProjection R y) :=
    gaussianIntegral_symmetric R x y
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [inner_sub_left, inner_sub_right, inner_sub_right,
    hs, hs, hid, hip, hhh]
  ring

/-- The corner identity on the dense orbit determines the entire operator. -/
theorem concrete_gaussian_projection : ConcreteGaussianProjection := by
  intro d hd R hR f
  let Q : SchrodingerSpace d →L[ℂ] SchrodingerSpace d :=
    (innerSL ℂ (vacuum d)).smulRight (vacuum d)
  have hfix := gaussianProjection_vacuum R hR
  have heq : gaussianProjection R = Q := by
    apply ContinuousLinearMap.ext_on (s := Set.range (fun z : PhaseSpace d =>
      SchrodingerActionValue z (vacuum d)))
    · exact dense_iff_closure_eq.mpr (congrArg (fun S : Submodule ℂ (SchrodingerSpace d) =>
        (S : Set (SchrodingerSpace d))) (vacuum_orbit_dense d hd))
    · rintro _ ⟨z, rfl⟩
      have hc := congrArg (fun T : SchrodingerSpace d →L[ℂ] SchrodingerSpace d =>
        T (vacuum d)) (gaussianProjection_sandwich R z)
      change gaussianProjection R (R.W z (gaussianProjection R (vacuum d))) =
        (gaussianWeight z : ℂ) • gaussianProjection R (vacuum d) at hc
      simp only [hfix, hR] at hc
      change gaussianProjection R (SchrodingerActionValue z (vacuum d)) =
        inner ℂ (vacuum d) (SchrodingerActionValue z (vacuum d)) • vacuum d
      rw [vacuum_coefficient_all]
      exact hc
  change gaussianProjection R f = _
  rw [heq]
  rfl

end ExpandedFA.Weyl
