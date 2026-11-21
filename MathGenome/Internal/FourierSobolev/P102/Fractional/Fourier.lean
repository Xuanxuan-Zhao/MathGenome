import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.Fourier
import MathGenome.Internal.FourierSobolev.P102.Fractional.Space
import MathGenome.Internal.FourierSobolev.P102.Fractional.Density
import MathGenome.Internal.FourierSobolev.P102.U3.Plancherel
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal Topology
namespace P102.Fractional

/-- The map used before Plancherel is the canonical scalar embedding. -/
theorem complexifyL2_ae {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (u : Lp 𝕜 2 (volume : Measure (Domain d))) :
    complexifyL2 u =ᵐ[volume] fun x => RCLike.map 𝕜 ℂ (u x) :=
  ContinuousLinearMap.coeFn_compLp _ _

theorem complexifyL2_norm_pointwise {𝕜 : Type*} [RCLike 𝕜] (x : 𝕜) :
    ‖RCLike.map 𝕜 ℂ x‖ = ‖x‖ := by
  exact RCLike.norm_to_complex x

theorem complexifyL2_norm {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (u : Lp 𝕜 2 (volume : Measure (Domain d))) : ‖complexifyL2 u‖ = ‖u‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [complexifyL2_ae u] with x hx
  rw [hx, complexifyL2_norm_pointwise]

theorem fourierRepresentative_aestronglyMeasurable {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (u : Lp 𝕜 2 (volume : Measure (Domain d))) :
    AEStronglyMeasurable (fourierRepresentative u) volume := Lp.aestronglyMeasurable _

/-- The unweighted Fourier mass equals the squared original L² norm,
also for real inputs. -/
theorem fourierRepresentative_mass {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (u : Lp 𝕜 2 (volume : Measure (Domain d))) :
    (∫⁻ ξ, ‖fourierRepresentative u ξ‖ₑ ^ (2 : ℕ)) = ‖u‖ₑ ^ (2 : ℕ) := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
    (fourierRepresentative_aestronglyMeasurable u)
  simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat] at h
  rw [← h]
  change eLpNorm (P102.Specs.U3.Plancherel.fourierL2_value (Domain d) ℂ
    (complexifyL2 u)) 2 volume ^ (2 : ℕ) = _
  rw [← Lp.enorm_def]
  simp only [← ofReal_norm]
  rw [(P102.Specs.U3.Plancherel.fourierL2_value (Domain d) ℂ).norm_map,
    complexifyL2_norm]

/-- Transport of the underlying graph class preserves its representative a.e. -/
theorem wholeSpaceL2_ae {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (u : Lp 𝕜 2 (domainMeasure (Set.univ : Set (Domain d)))) :
    wholeSpaceL2 u =ᵐ[volume] (u : Domain d → 𝕜) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem wholeSpaceL2_norm {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (u : Lp 𝕜 2 (domainMeasure (Set.univ : Set (Domain d)))) :
    ‖wholeSpaceL2 u‖ = ‖u‖ := Lp.norm_compMeasurePreserving _ _

/-- The inner integral is identically zero at ξ = 0, including h = 0. -/
theorem directionalIntegral_zero : Specs.P102.Fractional.Fourier.ZeroFrequency := by
  intro d s
  simp [directionalIntegral]

/-- A real-valued version of the first-coordinate kernel. -/
def constantDensity {d : ℕ} (hd : 0 < d) (s : ℝ) (h : Domain d) : ℝ :=
  if h = 0 then 0 else
    ‖Complex.exp ((2 * Real.pi * h ⟨0, hd⟩ : ℝ) * Complex.I) - 1‖ ^ (2 : ℕ) /
      ‖h‖ ^ ((d : ℝ) + 2 * s)

theorem constantDensity_nonneg {d : ℕ} (hd : 0 < d) (s : ℝ) (h : Domain d) :
    0 ≤ constantDensity hd s h := by
  unfold constantDensity
  split_ifs <;> positivity

theorem constantDensity_measurable {d : ℕ} (hd : 0 < d) (s : ℝ) :
    Measurable (constantDensity hd s) := by
  unfold constantDensity
  apply Measurable.ite (measurableSet_singleton 0) measurable_const
  fun_prop

theorem fourierConstant_eq_lintegral_ofReal {d : ℕ} (hd : 0 < d) (s : ℝ) :
    fourierConstant d hd s = ∫⁻ h, ENNReal.ofReal (constantDensity hd s h) := by
  apply lintegral_congr
  intro h
  by_cases hh : h = 0
  · simp [constantDensity, hh]
  · rw [ite_eq_right hh, constantDensity, ite_eq_right hh,
      ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr hh) _),
      ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr hh),
      ofReal_norm]

/-- The oscillation is both bounded and at most linear at the origin. -/
theorem coordinate_phase_bounds {d : ℕ} (hd : 0 < d) (h : Domain d) :
    ‖Complex.exp ((2 * Real.pi * h ⟨0, hd⟩ : ℝ) * Complex.I) - 1‖ ≤
      2 * Real.pi * ‖h‖ ∧
    ‖Complex.exp ((2 * Real.pi * h ⟨0, hd⟩ : ℝ) * Complex.I) - 1‖ ≤ 2 := by
  constructor
  · calc
      _ ≤ ‖2 * Real.pi * h ⟨0, hd⟩‖ := by
        simpa only [mul_comm Complex.I] using
          (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * h ⟨0, hd⟩))
      _ = (2 * Real.pi) * ‖h ⟨0, hd⟩‖ := by
        rw [norm_mul, Real.norm_of_nonneg (by positivity)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact PiLp.norm_apply_le h ⟨0, hd⟩) (by positivity)
  · calc
      _ ≤ ‖Complex.exp ((2 * Real.pi * h ⟨0, hd⟩ : ℝ) * Complex.I)‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
      _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I]; norm_num

/-- A radial integrable majorant captures both ends of the singular kernel. -/
theorem constantDensity_le_radialMajorant {d : ℕ} (hd : 0 < d) (s : ℝ) (h : Domain d) :
    constantDensity hd s h ≤ (2 * Real.pi) ^ (2 : ℕ) *
      ExpandedFA.PartIV.FractionalSobolev.MultiplierEstimates.radialMajorant d s 2 ‖h‖ := by
  by_cases hh : h = 0
  · simp only [constantDensity, ite_eq_left hh]
    apply mul_nonneg (sq_nonneg _)
    unfold ExpandedFA.PartIV.FractionalSobolev.MultiplierEstimates.radialMajorant
    split_ifs <;> exact Real.rpow_nonneg (norm_nonneg _) _
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hh
  rw [constantDensity, ite_eq_right hh]
  unfold ExpandedFA.PartIV.FractionalSobolev.MultiplierEstimates.radialMajorant
  have hb := coordinate_phase_bounds hd h
  split_ifs with hr
  · calc
      _ ≤ (2 * Real.pi * ‖h‖) ^ (2 : ℕ) / ‖h‖ ^ ((d : ℝ) + 2 * s) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact pow_le_pow_left₀ (norm_nonneg _) hb.1 2
      _ = _ := by
        rw [mul_pow, mul_div_assoc, ← Real.rpow_natCast ‖h‖ 2,
          ← Real.rpow_sub hn]
        congr 2
        ring
  · calc
      _ ≤ 4 / ‖h‖ ^ ((d : ℝ) + 2 * s) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [norm_nonneg (Complex.exp ((2 * Real.pi * h ⟨0, hd⟩ : ℝ) * Complex.I) - 1)]
      _ ≤ (2 * Real.pi) ^ (2 : ℕ) / ‖h‖ ^ ((d : ℝ) + 2 * s) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [Real.pi_gt_three]
      _ = _ := by rw [div_eq_mul_inv, ← Real.rpow_neg hn.le]; congr 2; ring

theorem constantDensity_integrable {d : ℕ} (hd : 0 < d) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) : Integrable (constantDensity hd s) := by
  apply Integrable.mono'
    ((ExpandedFA.PartIV.FractionalSobolev.MultiplierEstimates.radialMajorant_integrable
      d hd s 2 hs0 hs1 (by norm_num)).const_mul ((2 * Real.pi) ^ (2 : ℕ)))
    (constantDensity_measurable hd s).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun h => by
    rw [Real.norm_of_nonneg (constantDensity_nonneg hd s h)]
    exact constantDensity_le_radialMajorant hd s h

theorem fourierConstant_lt_top {d : ℕ} (hd : 0 < d) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) : fourierConstant d hd s < ∞ := by
  rw [fourierConstant_eq_lintegral_ofReal]
  exact (constantDensity_integrable hd hs0 hs1).lintegral_lt_top

/-- Positivity comes from a nonempty open set where the oscillation is nonzero. -/
theorem fourierConstant_pos {d : ℕ} (hd : 0 < d) (s : ℝ) :
    0 < fourierConstant d hd s := by
  rw [fourierConstant_eq_lintegral_ofReal,
    lintegral_pos_iff_support (constantDensity_measurable hd s).ennreal_ofReal]
  let U : Set (Domain d) := {h | h ≠ 0 ∧
    Complex.exp ((2 * Real.pi * h ⟨0, hd⟩ : ℝ) * Complex.I) ≠ 1}
  have hU : IsOpen U := by
    apply IsOpen.inter
    · exact isOpen_ne_fun continuous_id continuous_const
    · apply isOpen_ne_fun _ continuous_const
      fun_prop
  have hUne : U.Nonempty := by
    refine ⟨EuclideanSpace.single ⟨0, hd⟩ (1 / 2 : ℝ), ?_, ?_⟩
    · intro he
      have hh := congrArg (fun h : Domain d => h ⟨0, hd⟩) he
      norm_num [PiLp.single_apply] at hh
    · dsimp only
      simp only [PiLp.single_apply, ite_true]
      rw [show 2 * Real.pi * (1 / 2) = Real.pi by ring, Complex.exp_pi_mul_I]
      norm_num
  apply (hU.measure_pos volume hUne).trans_le
  apply measure_mono
  intro h hh
  change ENNReal.ofReal (constantDensity hd s h) ≠ 0
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  rw [constantDensity, ite_eq_right hh.1]
  exact div_pos (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hh.2)) 2)
    (Real.rpow_pos_of_pos (norm_pos_iff.mpr hh.1) _)

/-- The source constant is strictly positive and finite throughout 0 < s < 1. -/
theorem fourierConstant_bounds : Specs.P102.Fractional.Fourier.ConstantBounds := by
  intro d hd s hs0 hs1
  exact ⟨fourierConstant_pos hd s, fourierConstant_lt_top hd hs0 hs1⟩

/-- Pointwise directional kernel, with the diagonal value retained. -/
def directionalKernel {d : ℕ} (s : ℝ) (ξ h : Domain d) : ℝ≥0∞ :=
  if h = 0 then 0 else
    ‖Complex.exp ((2 * Real.pi * inner ℝ h ξ : ℝ) * Complex.I) - 1‖ₑ ^ (2 : ℕ) /
      ENNReal.ofReal ‖h‖ ^ ((d : ℝ) + 2 * s)

theorem directionalKernel_measurable {d : ℕ} (s : ℝ) (ξ : Domain d) :
    Measurable (directionalKernel s ξ) := by
  unfold directionalKernel
  apply Measurable.ite (measurableSet_singleton 0) measurable_const
  fun_prop

/-- Orthogonal coordinate changes preserve the directional integral. -/
theorem directionalIntegral_isometry {d : ℕ} (s : ℝ) (ξ : Domain d)
    (e : Domain d ≃ₗᵢ[ℝ] Domain d) :
    directionalIntegral s (e ξ) = directionalIntegral s ξ := by
  change (∫⁻ h, directionalKernel s (e ξ) h) = _
  rw [← e.measurePreserving.lintegral_comp_emb e.toHomeomorph.measurableEmbedding]
  apply lintegral_congr
  intro h
  simp only [directionalKernel, e.map_eq_zero_iff, e.inner_map_map, e.norm_map]

/-- The Jacobian of a positive scalar dilation, for arbitrary extended integrals. -/
theorem lintegral_positive_dilation {d : ℕ} (f : Domain d → ℝ≥0∞) {r : ℝ}
    (hr : 0 < r) :
    (∫⁻ h, f (r • h)) = ENNReal.ofReal r ^ (-(d : ℝ)) * ∫⁻ h, f h := by
  let e := (Homeomorph.smul (Units.mk0 r hr.ne') : Domain d ≃ₜ Domain d).toMeasurableEquiv
  have he : (e : Domain d → Domain d) = (fun h => r • h) := by
    ext h
    simp [e, Units.smul_def]
  have hm := lintegral_map_equiv (μ := (volume : Measure (Domain d))) f e
  rw [he, Measure.map_addHaar_smul volume hr.ne', lintegral_smul_measure] at hm
  rw [← hm]
  congr 1
  simp only [finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos hr _)),
    ENNReal.ofReal_inv_of_pos (pow_pos hr _), ENNReal.ofReal_pow hr.le,
    ENNReal.rpow_neg, ENNReal.rpow_natCast]

/-- Rescale the pointwise kernel without discarding the value at zero. -/
theorem directionalKernel_dilation {d : ℕ} (s : ℝ) (ξ h : Domain d) {r : ℝ}
    (hr : 0 < r) :
    directionalKernel s (r • ξ) h = ENNReal.ofReal r ^ ((d : ℝ) + 2 * s) *
      directionalKernel s ξ (r • h) := by
  by_cases hh : h = 0
  · simp [directionalKernel, hh]
  have hr0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hrp0 : ENNReal.ofReal r ^ ((d : ℝ) + 2 * s) ≠ 0 := by
    simp [ENNReal.rpow_eq_zero_iff, hr0, ENNReal.ofReal_ne_top]
  have hrpt : ENNReal.ofReal r ^ ((d : ℝ) + 2 * s) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero hr0 ENNReal.ofReal_ne_top
  have hrh : r • h ≠ 0 := smul_ne_zero hr.ne' hh
  simp only [directionalKernel, ite_eq_right hh, ite_eq_right hrh, inner_smul_left,
    inner_smul_right, RCLike.conj_to_real, norm_smul, Real.norm_of_nonneg hr.le,
    ENNReal.ofReal_mul hr.le, ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top, div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl hrp0) (Or.inl hrpt)]
  rw [mul_left_comm (ENNReal.ofReal r ^ ((d : ℝ) + 2 * s)), ← mul_assoc (ENNReal.ofReal r ^ ((d : ℝ) + 2 * s))
      (ENNReal.ofReal r ^ ((d : ℝ) + 2 * s))⁻¹,
    ENNReal.mul_inv_cancel hrp0 hrpt, one_mul]

/-- The directional multiplier is homogeneous of degree 2s. -/
theorem directionalIntegral_dilation {d : ℕ} (s : ℝ) (ξ : Domain d) {r : ℝ}
    (hr : 0 < r) :
    directionalIntegral s (r • ξ) =
      ENNReal.ofReal r ^ (2 * s) * directionalIntegral s ξ := by
  change (∫⁻ h, directionalKernel s (r • ξ) h) = _
  simp_rw [directionalKernel_dilation s ξ _ hr]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero
    (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top),
    lintegral_positive_dilation _ hr, ← mul_assoc,
    ← ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top]
  congr 2
  ring

/-- Rotation to the first axis and positive dilation evaluate every frequency. -/
theorem directionalIntegral_scaling : Specs.P102.Fractional.Fourier.DirectionalScaling := by
  intro d hd s hs0 _ ξ
  by_cases hξ : ξ = 0
  · simp [hξ, directionalIntegral_zero d s, ENNReal.zero_rpow_of_pos (by positivity : 0 < 2 * s)]
  let e₁ : Domain d := EuclideanSpace.single ⟨0, hd⟩ 1
  have he₁ : ‖e₁‖ = 1 := by simp [e₁, EuclideanSpace.single, PiLp.norm_single]
  have hn : ‖‖ξ‖ • e₁‖ = ‖ξ‖ := by simp [norm_smul, he₁]
  let R : Domain d ≃ₗᵢ[ℝ] Domain d := (ℝ ∙ (‖ξ‖ • e₁ - ξ))ᗮ.reflection
  have hR : R (‖ξ‖ • e₁) = ξ := Submodule.reflection_sub hn
  conv_lhs => rw [← hR, directionalIntegral_isometry,
    directionalIntegral_dilation s e₁ (norm_pos_iff.mpr hξ)]
  rw [mul_comm]
  congr 1
  unfold directionalIntegral fourierConstant
  apply lintegral_congr
  intro h
  simp only [e₁, EuclideanSpace.inner_single_right, one_mul, RCLike.conj_to_real]

open FourierTransform
open scoped FourierTransform SchwartzMap

/-- Translation on the original Euclidean L² space. -/
def translateL2 {d : ℕ} (h : Domain d) :
    Lp ℂ 2 (volume : Measure (Domain d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Domain d)) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x => x + h)
    (measurePreserving_add_right volume h)).toContinuousLinearMap

theorem translateL2_ae {d : ℕ} (h : Domain d) (u : Lp ℂ 2 (volume : Measure (Domain d))) :
    translateL2 h u =ᵐ[volume] fun x => u (x + h) :=
  Lp.coeFn_compMeasurePreserving _ _

/-- The phase is a bounded measurable multiplier of norm one. -/
def translationPhase {d : ℕ} (h ξ : Domain d) : ℂ :=
  Complex.exp ((2 * Real.pi * inner ℝ h ξ : ℝ) * Complex.I)

theorem translationPhase_memLp {d : ℕ} (h : Domain d) :
    MemLp (translationPhase h) ∞ volume := by
  apply memLp_top_of_bound (by unfold translationPhase; fun_prop) 1
  exact Filter.Eventually.of_forall fun ξ => by
    unfold translationPhase
    rw [Complex.norm_exp_ofReal_mul_I]

def modulateL2 {d : ℕ} (h : Domain d) :
    Lp ℂ 2 (volume : Measure (Domain d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Domain d)) :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2
    ((translationPhase_memLp h).toLp (translationPhase h))

theorem modulateL2_ae {d : ℕ} (h : Domain d) (u : Lp ℂ 2 (volume : Measure (Domain d))) :
    modulateL2 h u =ᵐ[volume] fun ξ => translationPhase h ξ * u ξ := by
  have hm := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    ((translationPhase_memLp h).toLp (translationPhase h)) u (r := 2)
  filter_upwards [hm, (translationPhase_memLp h).coeFn_toLp] with ξ hξ hphase
  exact hξ.trans (congrArg (fun z : ℂ => z * u ξ) hphase)

set_option maxHeartbeats 1200000 in
/-- The integral translation formula extends by density to every L² class. -/
theorem fourier_translateL2 {d : ℕ} (h : Domain d)
    (u : Lp ℂ 2 (volume : Measure (Domain d))) :
    𝓕 (translateL2 h u) = modulateL2 h (𝓕 u) := by
  apply DenseRange.induction_on (p := fun u : Lp ℂ 2 (volume : Measure (Domain d)) =>
    𝓕 (translateL2 h u) = modulateL2 h (𝓕 u))
    (SchwartzMap.denseRange_toLpCLM (p := 2) (by norm_num)) u
  · exact isClosed_eq ((fourierCLM ℂ _).continuous.comp (translateL2 h).continuous)
      ((modulateL2 h).continuous.comp (fourierCLM ℂ _).continuous)
  intro φ
  change 𝓕 (translateL2 h (φ.toLp 2)) = modulateL2 h (𝓕 (φ.toLp 2))
  have hφ : (φ.toLp 2 : Domain d → ℂ) =ᵐ[volume] φ := φ.coeFn_toLp 2
  have htr : translateL2 h (φ.toLp 2) =ᵐ[volume] fun x => φ (x + h) :=
    (translateL2_ae h _).trans
      ((measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp hφ)
  have hi : Integrable (translateL2 h (φ.toLp 2) : Domain d → ℂ) :=
    (φ.integrable.comp_add_right h).congr htr.symm
  apply Lp.ext
  have hleft := P102.U3.Plancherel.fourier_ae_integral _ hi
  have hright := modulateL2_ae h (𝓕 (φ.toLp 2))
  have hFφ : ((𝓕 (φ.toLp 2) : Lp ℂ 2 volume) : Domain d → ℂ) =ᵐ[volume]
      ((𝓕 φ : SchwartzMap (Domain d) ℂ) : Domain d → ℂ) := by
    rw [SchwartzMap.toLp_fourier_eq]
    exact (𝓕 φ).coeFn_toLp 2
  filter_upwards [hleft, hright, hFφ] with ξ hL hR hφξ
  rw [hL, hR, hφξ, Real.fourier_congr_ae htr]
  have ht := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
    (volume : Measure (Domain d)) (innerₗ (Domain d)) (φ : Domain d → ℂ) h) ξ
  rw [SchwartzMap.fourier_coe]
  change 𝓕 (fun x => φ (x + h)) ξ = translationPhase h ξ * 𝓕 (φ : Domain d → ℂ) ξ
  change 𝓕 (fun x => φ (x + h)) ξ =
    Real.fourierChar (inner ℝ h ξ) • 𝓕 (φ : Domain d → ℂ) ξ at ht
  simpa only [translationPhase, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul] using ht

/-- The squared L² norm is the nonnegative integral of the squared norm. -/
theorem lp_sq_mass {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (u : Lp 𝕜 2 (volume : Measure (Domain d))) :
    (∫⁻ x, ‖u x‖ₑ ^ (2 : ℕ)) = ‖u‖ₑ ^ (2 : ℕ) := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
    (Lp.aestronglyMeasurable u)
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat, Lp.enorm_def] using h.symm

/-- Plancherel for one translation difference, without any fractional-energy assumption. -/
theorem translation_difference_plancherel {d : ℕ}
    (u : Lp ℂ 2 (volume : Measure (Domain d))) (h : Domain d) :
    (∫⁻ x, ‖u (x + h) - u x‖ₑ ^ (2 : ℕ)) =
      ∫⁻ ξ, ‖translationPhase h ξ - 1‖ₑ ^ (2 : ℕ) * ‖(𝓕 u : Lp ℂ 2 volume) ξ‖ₑ ^ (2 : ℕ) := by
  let v := translateL2 h u - u
  have hv : v =ᵐ[volume] fun x => u (x + h) - u x := by
    filter_upwards [Lp.coeFn_sub (translateL2 h u) u, translateL2_ae h u] with x hx htx
    simp only [v, hx, Pi.sub_apply, htx]
  have hFv : (𝓕 v : Lp ℂ 2 volume) =ᵐ[volume]
      fun ξ => (translationPhase h ξ - 1) * (𝓕 u : Lp ℂ 2 volume) ξ := by
    have heq : (𝓕 v : Lp ℂ 2 volume) = modulateL2 h (𝓕 u) - 𝓕 u := by
      change (Lp.fourierTransformₗᵢ (Domain d) ℂ) (translateL2 h u - u) = _
      rw [map_sub]
      exact congrArg (fun z => z - 𝓕 u) (fourier_translateL2 h u)
    rw [heq]
    filter_upwards [Lp.coeFn_sub (modulateL2 h (𝓕 u)) (𝓕 u), modulateL2_ae h (𝓕 u)] with ξ hx hm
    simp only [hx, Pi.sub_apply, hm, sub_mul, one_mul]
  calc
    _ = ∫⁻ x, ‖v x‖ₑ ^ (2 : ℕ) := lintegral_congr_ae (hv.mono fun x hx => by rw [hx]) |>.symm
    _ = ‖v‖ₑ ^ (2 : ℕ) := lp_sq_mass v
    _ = ‖(𝓕 v : Lp ℂ 2 volume)‖ₑ ^ (2 : ℕ) := by
      simp only [← ofReal_norm, Lp.norm_fourier_eq]
    _ = ∫⁻ ξ, ‖(𝓕 v : Lp ℂ 2 volume) ξ‖ₑ ^ (2 : ℕ) := (lp_sq_mass _).symm
    _ = _ := lintegral_congr_ae (hFv.mono fun ξ hξ => by simp only [hξ, enorm_mul, mul_pow])


/-- The radial weight with the prescribed value at the diagonal. -/
def fractionalRadialWeight (d : ℕ) (s : ℝ) (h : Domain d) : ℝ≥0∞ :=
  if h = 0 then 0 else (ENNReal.ofReal ‖h‖ ^ ((d : ℝ) + 2 * s))⁻¹

theorem fractionalRadialWeight_measurable (d : ℕ) (s : ℝ) :
    Measurable (fractionalRadialWeight d s) := by
  unfold fractionalRadialWeight
  apply Measurable.ite (measurableSet_singleton 0) measurable_const
  fun_prop

theorem energy_eq_translation_integral {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (s : ℝ) (u : Lp 𝕜 2 (volume : Measure (Domain d))) :
    energy Set.univ s 2 u = ∫⁻ h,
      fractionalRadialWeight d s h * ∫⁻ x, ‖u (x + h) - u x‖ₑ ^ (2 : ℕ) := by
  have hu : Measurable (u : Domain d → 𝕜) := (Lp.stronglyMeasurable u).measurable
  have hm : Measurable (fun z : Domain d × Domain d =>
      fractionalRadialWeight d s z.2 * ‖u (z.1 + z.2) - u z.1‖ₑ ^ (2 : ℕ)) := by
    exact ((fractionalRadialWeight_measurable d s).comp measurable_snd).mul
      (((hu.comp (measurable_fst.add measurable_snd)).sub
        (hu.comp measurable_fst)).enorm.pow_const _)
  unfold energy
  simp only [domainMeasure, Measure.restrict_univ, ENNReal.toReal_ofNat,
    ENNReal.rpow_ofNat, mul_comm s (2 : ℝ)]
  calc
    _ = ∫⁻ x, ∫⁻ h, fractionalRadialWeight d s h *
        ‖u (x + h) - u x‖ₑ ^ (2 : ℕ) := by
      apply lintegral_congr
      intro x
      have hmx : Measurable (fun y : Domain d => if x = y then (0 : ℝ≥0∞) else
          ‖u x - u y‖ₑ ^ (2 : ℕ) / ENNReal.ofReal ‖x - y‖ ^ ((d : ℝ) + 2 * s)) := by
        apply Measurable.ite (measurableSet_eq_fun measurable_const measurable_id) measurable_const
        fun_prop
      rw [← (measurePreserving_add_left volume x).lintegral_comp hmx]
      apply lintegral_congr
      intro h
      by_cases hh : h = 0
      · simp [fractionalRadialWeight, hh]
      · have hx : x ≠ x + h := by
          intro heq
          apply hh
          have heq' : x + 0 = x + h := by simpa only [add_zero] using heq
          exact (add_left_cancel heq').symm
        simp only [hx, ite_false, fractionalRadialWeight, hh, sub_add_eq_sub_sub,
          sub_self, zero_sub, enorm_sub_rev (u x), norm_neg, div_eq_mul_inv]
        exact mul_comm _ _
    _ = ∫⁻ h, ∫⁻ x, fractionalRadialWeight d s h *
        ‖u (x + h) - u x‖ₑ ^ (2 : ℕ) := lintegral_lintegral_swap hm.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro h
      exact lintegral_const_mul _ (((hu.comp (measurable_id.add_const h)).sub hu).enorm.pow_const _)

theorem energy_complexifyL2 {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (s : ℝ) (u : Lp 𝕜 2 (volume : Measure (Domain d))) :
    energy Set.univ s 2 (complexifyL2 u) = energy Set.univ s 2 u := by
  have hc : (complexifyL2 u : Domain d → ℂ) =ᵐ[domainMeasure Set.univ]
      fun x => RCLike.map 𝕜 ℂ (u x) := by
    simpa only [domainMeasure, Measure.restrict_univ] using complexifyL2_ae u
  rw [energy_congr hc]
  unfold energy
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro y
  congr 1
  rw [← map_sub, ← ofReal_norm, complexifyL2_norm_pointwise, ofReal_norm]

theorem directionalKernel_eq_radialWeight {d : ℕ} (s : ℝ) (ξ h : Domain d) :
    directionalKernel s ξ h = fractionalRadialWeight d s h *
      ‖translationPhase h ξ - 1‖ₑ ^ (2 : ℕ) := by
  by_cases hh : h = 0
  · simp [directionalKernel, fractionalRadialWeight, hh]
  · simp [directionalKernel, fractionalRadialWeight, translationPhase, hh,
      div_eq_mul_inv, mul_comm]

theorem directionalKernel_joint_measurable {d : ℕ} (s : ℝ) :
    Measurable (fun z : Domain d × Domain d => directionalKernel s z.2 z.1) := by
  unfold directionalKernel
  apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const) measurable_const
  fun_prop

theorem directional_plancherel_identity :
    Specs.P102.Fractional.Fourier.DirectionalPlancherelIdentity := by
  intro d hd 𝕜 _ s hs0 hs1 u
  have hu : Measurable (fourierRepresentative u) :=
    (Lp.stronglyMeasurable _).measurable
  have hm : Measurable (fun z : Domain d × Domain d =>
      directionalKernel s z.2 z.1 * ‖fourierRepresentative u z.2‖ₑ ^ (2 : ℕ)) :=
    (directionalKernel_joint_measurable s).mul ((hu.comp measurable_snd).enorm.pow_const _)
  rw [← energy_complexifyL2 s u, energy_eq_translation_integral]
  simp_rw [translation_difference_plancherel]
  calc
    _ = ∫⁻ h, ∫⁻ ξ, directionalKernel s ξ h *
        ‖fourierRepresentative u ξ‖ₑ ^ (2 : ℕ) := by
      apply lintegral_congr
      intro h
      rw [← lintegral_const_mul _ (by unfold translationPhase; fun_prop : Measurable (fun ξ =>
        ‖translationPhase h ξ - 1‖ₑ ^ (2 : ℕ) *
          ‖(𝓕 (complexifyL2 u) : Lp ℂ 2 volume) ξ‖ₑ ^ (2 : ℕ)))]
      apply lintegral_congr
      intro ξ
      rw [directionalKernel_eq_radialWeight, mul_assoc]
      rfl
    _ = ∫⁻ ξ, ∫⁻ h, directionalKernel s ξ h *
        ‖fourierRepresentative u ξ‖ₑ ^ (2 : ℕ) := lintegral_lintegral_swap hm.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro ξ
      exact lintegral_mul_const _ (directionalKernel_measurable s ξ)


/-- Comparison using max(1,r²), valid for every nonnegative order. -/
theorem bessel_weight_comparison : Specs.P102.Fractional.Fourier.WeightComparison := by
  intro s r hs hr
  have hrpow : r ^ (2 * s) = (r ^ (2 : ℕ)) ^ s :=
    Real.rpow_natCast_mul hr 2 s
  rw [hrpow]
  have ht : 0 ≤ r ^ (2 : ℕ) := sq_nonneg r
  constructor
  · have h1 : (1 : ℝ) ≤ (1 + r ^ (2 : ℕ)) ^ s := by
      simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
        (by linarith : (1 : ℝ) ≤ 1 + r ^ (2 : ℕ)) hs
    have h2 : (r ^ (2 : ℕ)) ^ s ≤ (1 + r ^ (2 : ℕ)) ^ s :=
      Real.rpow_le_rpow ht (by linarith) hs
    linarith
  · by_cases ht1 : r ^ (2 : ℕ) ≤ 1
    · calc
        (1 + r ^ (2 : ℕ)) ^ s ≤ (2 : ℝ) ^ s :=
          Real.rpow_le_rpow (by positivity) (by linarith) hs
        _ ≤ (2 : ℝ) ^ s * (1 + (r ^ (2 : ℕ)) ^ s) := by
          nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) s,
            Real.rpow_nonneg ht s]
    · have ht1' : 1 ≤ r ^ (2 : ℕ) := le_of_lt (lt_of_not_ge ht1)
      calc
        (1 + r ^ (2 : ℕ)) ^ s ≤ (2 * r ^ (2 : ℕ)) ^ s :=
          Real.rpow_le_rpow (by positivity) (by linarith) hs
        _ = (2 : ℝ) ^ s * (r ^ (2 : ℕ)) ^ s := Real.mul_rpow (by norm_num) ht
        _ ≤ (2 : ℝ) ^ s * (1 + (r ^ (2 : ℕ)) ^ s) := by
          nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) s]

/-- Changing the frequency scale changes only the comparison constant. -/
theorem bessel_weight_scale {c s r : ℝ} (hc : 1 ≤ c) (hs : 0 ≤ s) :
    (1 + r ^ (2 : ℕ)) ^ s ≤ (1 + c * r ^ (2 : ℕ)) ^ s ∧
    (1 + c * r ^ (2 : ℕ)) ^ s ≤ c ^ s * (1 + r ^ (2 : ℕ)) ^ s := by
  have ht := sq_nonneg r
  constructor
  · apply Real.rpow_le_rpow (by positivity) _ hs
    nlinarith
  · calc
      (1 + c * r ^ (2 : ℕ)) ^ s ≤ (c * (1 + r ^ (2 : ℕ))) ^ s :=
        Real.rpow_le_rpow (by positivity) (by nlinarith) hs
      _ = c ^ s * (1 + r ^ (2 : ℕ)) ^ s := Real.mul_rpow (by linarith) (by positivity)

theorem four_pi_sq_ge_one : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by
  have hp := Real.pi_gt_three
  nlinarith

theorem bessel_normalization_comparison :
    Specs.P102.Fractional.Fourier.NormalizationComparison := by
  intro s r hs _
  exact bessel_weight_scale four_pi_sq_ge_one hs

/-- Normalization bridge for extended integrals; finiteness is not assumed. -/
theorem bessel_energy_comparison : Specs.P102.Fractional.Fourier.BesselEnergyComparison := by
  intro d 𝕜 _ s hs u
  constructor
  · apply lintegral_mono
    intro ξ
    dsimp only
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    simpa only [one_mul] using (bessel_weight_scale (r := ‖ξ‖) four_pi_sq_ge_one hs).1
  · unfold besselEnergy
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro ξ
    dsimp only
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    simpa only [one_mul] using (bessel_weight_scale (r := ‖ξ‖) four_pi_sq_ge_one hs).2

/-- The integral with weight 1+|ξ|^(2s) splits into the L² mass and moment. -/
theorem fourier_total_energy {d : ℕ} {𝕜 : Type*} [RCLike 𝕜] (s : ℝ)
    (u : Lp 𝕜 2 (volume : Measure (Domain d))) :
    (∫⁻ ξ, (1 + ENNReal.ofReal ‖ξ‖ ^ (2 * s)) *
      ‖fourierRepresentative u ξ‖ₑ ^ (2 : ℕ)) = ‖u‖ₑ ^ (2 : ℕ) + fourierMoment s u := by
  simp_rw [add_mul, one_mul]
  rw [lintegral_add_left' ((fourierRepresentative_aestronglyMeasurable u).enorm.pow_const 2),
    fourierRepresentative_mass]
  rfl

/-- Comparison of the unit-scale squared Bessel norm with the full homogeneous
Fourier mass, with no integrability assumption. -/
theorem bessel_energy_moment_comparison {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {s : ℝ} (hs : 0 ≤ s) (u : Lp 𝕜 2 (volume : Measure (Domain d))) :
    ‖u‖ₑ ^ (2 : ℕ) + fourierMoment s u ≤ 2 * besselEnergy 1 s u ∧
    besselEnergy 1 s u ≤ ENNReal.ofReal ((2 : ℝ) ^ s) *
      (‖u‖ₑ ^ (2 : ℕ) + fourierMoment s u) := by
  rw [← fourier_total_energy s u]
  unfold besselEnergy
  constructor
  · rw [← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    apply lintegral_mono
    intro ξ
    dsimp only
    rw [← mul_assoc]
    apply mul_le_mul' _ le_rfl
    have h := ENNReal.ofReal_le_ofReal
      (bessel_weight_comparison s ‖ξ‖ hs (norm_nonneg _)).1
    rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
      (Real.rpow_nonneg (norm_nonneg ξ) (2 * s)), ENNReal.ofReal_one,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg ξ) (by positivity)] at h
    simpa only [one_mul] using h

  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro ξ
    dsimp only
    rw [← mul_assoc]
    apply mul_le_mul' _ le_rfl
    have h := ENNReal.ofReal_le_ofReal
      (bessel_weight_comparison s ‖ξ‖ hs (norm_nonneg _)).2
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) s),
      ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
        (Real.rpow_nonneg (norm_nonneg ξ) (2 * s)), ENNReal.ofReal_one,
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg ξ) (by positivity)] at h
    simpa only [one_mul] using h


/-- Either of the standard frequency normalizations defines the same class. -/
theorem memHs_iff_unit_scale {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {s : ℝ}
    (hs : 0 ≤ s) (u : Lp 𝕜 2 (volume : Measure (Domain d))) :
    MemHs s u ↔ besselEnergy 1 s u < ∞ := by
  constructor
  · intro hu
    exact lt_of_le_of_lt (bessel_energy_comparison d 𝕜 s hs u).1 hu
  · intro hu
    apply lt_of_le_of_lt (bessel_energy_comparison d 𝕜 s hs u).2
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu

/-- The inhomogeneous Hˢ condition is exactly finiteness of the homogeneous
Fourier moment, since the input already belongs to L². -/
theorem memHs_iff_fourierMoment {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {s : ℝ}
    (hs : 0 ≤ s) (u : Lp 𝕜 2 (volume : Measure (Domain d))) :
    MemHs s u ↔ fourierMoment s u < ∞ := by
  rw [memHs_iff_unit_scale hs]
  have hmass : ‖u‖ₑ ^ (2 : ℕ) < ∞ := by finiteness
  constructor
  · intro hu
    have htotal : ‖u‖ₑ ^ (2 : ℕ) + fourierMoment s u < ∞ :=
      lt_of_le_of_lt (bessel_energy_moment_comparison hs u).1
        (ENNReal.mul_lt_top (by norm_num) hu)
    exact lt_of_le_of_lt (le_add_self) htotal
  · intro hu
    exact lt_of_le_of_lt (bessel_energy_moment_comparison hs u).2
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨hmass, hu⟩))

/-- A regular L² distribution multiplied by a temperate function has the
expected product pairing whenever that product is in L². -/
theorem regular_multiplier_of_memLp {d : ℕ} {a : Domain d → ℂ}
    (ha : a.HasTemperateGrowth) (f : Lp ℂ 2 (volume : Measure (Domain d)))
    (hf : MemLp (fun x => a x * f x) 2 volume) :
    TemperedDistribution.smulLeftCLM ℂ a (Lp.toTemperedDistribution f) =
      Lp.toTemperedDistribution (hf.toLp _) := by
  ext φ
  rw [TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [SchwartzMap.smulLeftCLM_apply_apply ha, hx]
  simp only [smul_eq_mul]
  ring

/-- For a multiplier with a bounded temperate inverse, being represented by an
L² distribution is equivalent to actual L² integrability of the product. -/
theorem multiplier_memLp_iff {d : ℕ} {a b : Domain d → ℂ}
    (ha : a.HasTemperateGrowth) (hb : b.HasTemperateGrowth)
    (hb2 : MemLp b ∞ (volume : Measure (Domain d))) (hab : ∀ x, a x * b x = 1)
    (f : Lp ℂ 2 (volume : Measure (Domain d))) :
    MemLp (fun x => a x * f x) 2 volume ↔
      ∃ g : Lp ℂ 2 (volume : Measure (Domain d)),
        TemperedDistribution.smulLeftCLM ℂ a (Lp.toTemperedDistribution f) =
          Lp.toTemperedDistribution g := by
  constructor
  · intro hf
    exact ⟨hf.toLp _, regular_multiplier_of_memLp ha f hf⟩
  · rintro ⟨g, hg⟩
    have hab' : a * b = (fun _ => 1) := funext hab
    have hbg : Lp.toTemperedDistribution ((hb2.toLp _) • g : Lp ℂ 2 volume) =
        Lp.toTemperedDistribution f := by
      rw [Lp.toTemperedDistribution_smul_eq hb hb2, ← hg,
        TemperedDistribution.smulLeftCLM_smulLeftCLM_apply ha hb, hab',
        TemperedDistribution.smulLeftCLM_const, one_smul]
    have hfg : ((hb2.toLp _) • g : Lp ℂ 2 volume) = f := by
      apply LinearMap.ker_eq_bot.mp
        (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume) (p := 2))
      exact hbg
    have hae : (fun x => a x * f x) =ᵐ[volume] (g : Domain d → ℂ) := by
      have h := Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) (hb2.toLp _) g
      rw [hfg] at h
      filter_upwards [h, hb2.coeFn_toLp] with x hx hb'
      change f x = (hb2.toLp b) x * g x at hx
      rw [hx, hb']
      simp only [← mul_assoc, hab x, one_mul]
    exact (Lp.memLp g).ae_eq hae.symm

/-- The complex unit-scale Bessel multiplier. -/
def unitBesselWeight {d : ℕ} (s : ℝ) (ξ : Domain d) : ℂ :=
  ((1 + ‖ξ‖ ^ (2 : ℕ)) ^ (s / 2) : ℝ)

theorem unitBesselWeight_temperate {d : ℕ} (s : ℝ) :
    (unitBesselWeight (d := d) s).HasTemperateGrowth := by
  unfold unitBesselWeight
  fun_prop

theorem unitBesselWeight_inverse {d : ℕ} (s : ℝ) (ξ : Domain d) :
    unitBesselWeight s ξ * unitBesselWeight (-s) ξ = 1 := by
  unfold unitBesselWeight
  rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity)]
  rw [show s / 2 + -s / 2 = 0 by ring, Real.rpow_zero, Complex.ofReal_one]

theorem unitBesselWeight_neg_memLp_top {d : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    MemLp (unitBesselWeight (d := d) (-s)) ∞ volume := by
  apply memLp_top_of_bound (unitBesselWeight_temperate (-s)).1.continuous.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro ξ
  simp only [unitBesselWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 1 + ‖ξ‖ ^ (2 : ℕ)) _)]
  calc
    (1 + ‖ξ‖ ^ (2 : ℕ)) ^ (-s / 2) ≤ (1 + ‖ξ‖ ^ (2 : ℕ)) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖ξ‖]) (by linarith)
    _ = 1 := Real.rpow_zero _

/-- The squared multiplier has exactly the unit-scale Bessel energy weight. -/
theorem unitBesselWeight_enorm_sq {d : ℕ} (s : ℝ) (ξ : Domain d) :
    ‖unitBesselWeight s ξ‖ₑ ^ (2 : ℕ) =
      ENNReal.ofReal ((1 + ‖ξ‖ ^ (2 : ℕ)) ^ s) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  congr 1
  simp only [unitBesselWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 1 + ‖ξ‖ ^ (2 : ℕ)) _)]
  rw [← Real.rpow_mul_natCast (by positivity) (s / 2) 2]
  congr 1
  ring

theorem bessel_energy_eq_multiplier_integral {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (s : ℝ) (u : Lp 𝕜 2 (volume : Measure (Domain d))) :
    besselEnergy 1 s u =
      ∫⁻ ξ, ‖unitBesselWeight s ξ * fourierRepresentative u ξ‖ₑ ^ (2 : ℕ) := by
  apply lintegral_congr
  intro ξ
  simp only [one_mul, enorm_mul, mul_pow, unitBesselWeight_enorm_sq]

/-- The spectral integral characterizes an actual L² multiplier product. -/
theorem bessel_energy_lt_top_iff {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (s : ℝ) (u : Lp 𝕜 2 (volume : Measure (Domain d))) :
    besselEnergy 1 s u < ∞ ↔
      MemLp (fun ξ => unitBesselWeight s ξ * fourierRepresentative u ξ) 2 volume := by
  rw [bessel_energy_eq_multiplier_integral, memLp_iff]
  have hm : AEStronglyMeasurable
      (fun ξ : Domain d => unitBesselWeight s ξ * fourierRepresentative u ξ) volume :=
    (unitBesselWeight_temperate (d := d) s).1.continuous.aestronglyMeasurable.mul
      (fourierRepresentative_aestronglyMeasurable u)
  have h := eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hm
  simpa only [Pi.mul_apply, ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] using h.symm

/-- Identification with the library Bessel-potential condition, including the
explicit bridge between its unit frequency scale and the manuscript scale. -/
theorem library_bessel_identification :
    Specs.P102.Fractional.Fourier.LibraryBesselIdentification := by
  intro d 𝕜 _ s hs u
  rw [memHs_iff_unit_scale hs, bessel_energy_lt_top_iff,
    TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier,
    Lp.fourier_toTemperedDistribution_eq]
  exact multiplier_memLp_iff (unitBesselWeight_temperate s)
    (unitBesselWeight_temperate (-s)) (unitBesselWeight_neg_memLp_top hs)
    (unitBesselWeight_inverse s) _

/-- Assembly after the two independent analytic ingredients are proved.
The hypotheses are explicit proof interfaces, not certificates used to state
the unconditional source theorem. -/
theorem fourier_identity_of_directional
    (hconstant : Specs.P102.Fractional.Fourier.ConstantBounds)
    (hscaling : Specs.P102.Fractional.Fourier.DirectionalScaling)
    (hplancherel : Specs.P102.Fractional.Fourier.DirectionalPlancherelIdentity) :
    Specs.P102.Fractional.Fourier.FourierIdentity := by
  intro d hd 𝕜 _ s hs0 hs1 u
  rw [hplancherel d hd 𝕜 s hs0 hs1 u, fourierMoment,
    ← lintegral_const_mul' _ _ (hconstant d hd s hs0 hs1).2.ne]
  apply lintegral_congr
  intro ξ
  rw [hscaling d hd s hs0 hs1 ξ]
  exact mul_assoc _ _ _

/-- Finiteness can be cancelled through a positive finite ENNReal constant. -/
theorem constant_mul_lt_top_iff {a b : ℝ≥0∞} (ha0 : 0 < a) (hat : a < ∞) :
    a * b < ∞ ↔ b < ∞ := by
  constructor
  · intro h
    by_contra hb
    have hb' : b = ∞ := top_le_iff.mp (le_of_not_gt hb)
    simp [hb', ha0.ne'] at h
  · exact ENNReal.mul_lt_top hat

/-- Once the identity is available, space identification uses precisely the
upstream range theorem and the proved spectral characterization. -/
theorem space_identification_of_fourier_identity
    (hconstant : Specs.P102.Fractional.Fourier.ConstantBounds)
    (hidentity : Specs.P102.Fractional.Fourier.FourierIdentity) :
    Specs.P102.Fractional.Fourier.SpaceIdentification := by
  intro d hd 𝕜 _ s hs0 hs1 u
  rw [firstProjection_range (by norm_num), memHs_iff_fourierMoment hs0.le]
  have hu : (u : Domain d → 𝕜) =ᵐ[domainMeasure Set.univ] wholeSpaceL2 u := by
    simpa only [domainMeasure, Measure.restrict_univ] using (wholeSpaceL2_ae u).symm
  rw [energy_congr hu, hidentity d hd 𝕜 s hs0 hs1]
  exact constant_mul_lt_top_iff (hconstant d hd s hs0 hs1).1 (hconstant d hd s hs0 hs1).2

/-- The upstream extended seminorm really squares back to the energy at p=2. -/
theorem seminorm_two_sq {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (s : ℝ) (u : Domain d → 𝕜) :
    seminorm Set.univ s 2 u ^ (2 : ℕ) = energy Set.univ s 2 u := by
  simp only [seminorm, ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_ofNat, ← ENNReal.rpow_mul]
  norm_num

/-- Fully quantified forms for independent binding inspection. -/
theorem fourier_mass : Specs.P102.Fractional.Fourier.FourierMass := by
  intro d 𝕜 _ u
  exact fourierRepresentative_mass u

theorem moment_energy_comparison : Specs.P102.Fractional.Fourier.MomentEnergyComparison := by
  intro d 𝕜 _ s hs u
  exact bessel_energy_moment_comparison hs u

theorem moment_finiteness : Specs.P102.Fractional.Fourier.MomentFiniteness := by
  intro d 𝕜 _ s hs u
  exact memHs_iff_fourierMoment hs u

/-- Completeness retained from the original unnumbered proposition. -/
theorem fractional_banach : Specs.P102.Fractional.banach := by
  intro d 𝕜 _ G s p _
  infer_instance

/-- The density conclusion is in the full Gagliardo sum norm. -/
theorem fractional_smoothCompact_dense :
    Specs.P102.Fractional.Density.SmoothCompactDensity := smoothCompact_dense

theorem fractional_smoothCompact_memLp :
    Specs.P102.Fractional.Density.SmoothCompactMembership := smoothCompact_memLp


/-- The exact nonnegative extended Fourier identity for every real or complex L² input. -/
theorem fractional_fourier_identity : Specs.P102.Fractional.Fourier.FourierIdentity :=
  fourier_identity_of_directional fourierConstant_bounds directionalIntegral_scaling
    directional_plancherel_identity

/-- Equality of the Gagliardo and Bessel-potential spaces as original L² classes. -/
theorem fractional_space_identification : Specs.P102.Fractional.Fourier.SpaceIdentification :=
  space_identification_of_fourier_identity fourierConstant_bounds fractional_fourier_identity

/-- The source's seminorm formulation, also when either side is infinite. -/
theorem gagliardo_seminorm_fourier {d : ℕ} (hd : 0 < d) {𝕜 : Type} [RCLike 𝕜]
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (u : Lp 𝕜 2 (volume : Measure (Domain d))) :
    seminorm Set.univ s 2 u ^ (2 : ℕ) = fourierConstant d hd s * fourierMoment s u := by
  rw [seminorm_two_sq]
  exact fractional_fourier_identity d hd 𝕜 s hs0 hs1 u


private theorem real_norm_comparison (L S M H q C : ℝ)
    (hL : 0 ≤ L) (hS : 0 ≤ S) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hq : 0 < q) (hC : 0 < C) (hSq : S ^ 2 = q * M)
    (hlo : L ^ 2 + M ≤ 2 * H ^ 2) (hhi : H ^ 2 ≤ C * (L ^ 2 + M)) :
    (1 / (q + 2)) * (L + S) ≤ H ∧
      H ≤ (C * (1 + q⁻¹) + 1) * (L + S) := by
  have hN : 0 ≤ L + S := add_nonneg hL hS
  have hq0 : 0 ≤ q := hq.le
  have hw : L ^ 2 + S ^ 2 ≤ (1 + q) * (L ^ 2 + M) := by
    nlinarith [mul_nonneg hq0 (sq_nonneg L)]
  have hw' := mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ 1 + q)
  have hlower : (L + S) ^ 2 ≤ ((q + 2) * H) ^ 2 := by
    nlinarith [sq_nonneg (L - S), sq_nonneg (q * H)]
  have hlower' : L + S ≤ (q + 2) * H := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ q + 2) hH]
  have hqinv : 0 < q⁻¹ := inv_pos.mpr hq
  have hM' : M = q⁻¹ * S ^ 2 := by
    rw [hSq, ← mul_assoc, inv_mul_cancel₀ hq.ne', one_mul]
  have hLS : L ^ 2 ≤ (L + S) ^ 2 := by nlinarith
  have hSS : S ^ 2 ≤ (L + S) ^ 2 := by nlinarith
  have hMM : M ≤ q⁻¹ * (L + S) ^ 2 := by
    rw [hM']
    exact mul_le_mul_of_nonneg_left hSS hqinv.le
  have hupper : H ^ 2 ≤ C * (1 + q⁻¹) * (L + S) ^ 2 := by
    have hsum : L ^ 2 + M ≤ (1 + q⁻¹) * (L + S) ^ 2 := by nlinarith
    exact hhi.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsum hC.le)
  have hD : 0 < C * (1 + q⁻¹) := by positivity
  have hN2 : 0 ≤ (L + S) ^ 2 := sq_nonneg _
  have hupper' : H ^ 2 ≤ ((C * (1 + q⁻¹) + 1) * (L + S)) ^ 2 := by
    nlinarith [mul_nonneg hD.le hN2,
      sq_nonneg (C * (1 + q⁻¹) * (L + S))]
  constructor
  · have hdiv : (L + S) / (q + 2) ≤ H := (div_le_iff₀ (by positivity)).2 (by simpa only [mul_comm] using hlower')
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hdiv
  · nlinarith [mul_nonneg (by positivity : 0 ≤ C * (1 + q⁻¹) + 1) hN]

/-- Norm equivalence with explicit constants, for the exact Gagliardo sum norm. -/
theorem norm_equivalence_of_fourier_identity
    (hconstant : Specs.P102.Fractional.Fourier.ConstantBounds)
    (hidentity : Specs.P102.Fractional.Fourier.FourierIdentity) :
    Specs.P102.Fractional.Fourier.NormEquivalence := by
  intro d hd 𝕜 _ s hs0 hs1
  let q : ℝ := (fourierConstant d hd s).toReal
  let C : ℝ := (4 * Real.pi ^ 2) ^ s * (2 : ℝ) ^ s
  have hq : 0 < q := ENNReal.toReal_pos (hconstant d hd s hs0 hs1).1.ne'
    (hconstant d hd s hs0 hs1).2.ne
  have hscale : 0 < (4 * Real.pi ^ 2) ^ s := Real.rpow_pos_of_pos (by positivity) _
  have htwo : 0 < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by positivity) _
  have hC : 0 < C := mul_pos hscale htwo
  refine ⟨1 / (q + 2), C * (1 + q⁻¹) + 1, by positivity, by positivity, ?_⟩
  intro v
  let u := wholeSpaceL2 (firstProjection v)
  have hHs : besselEnergy (4 * Real.pi ^ 2) s u < ∞ :=
    (space_identification_of_fourier_identity hconstant hidentity
      d hd 𝕜 s hs0 hs1 (firstProjection v)).mp ⟨v, rfl⟩
  have hM : fourierMoment s u < ∞ := (memHs_iff_fourierMoment hs0.le u).mp hHs
  have hmass : ‖u‖ₑ ^ (2 : ℕ) ≠ ∞ := by finiteness
  have hHsq : hsNorm s u ^ 2 = (besselEnergy (4 * Real.pi ^ 2) s u).toReal :=
    Real.sq_sqrt ENNReal.toReal_nonneg
  have hu : (firstProjection v : Domain d → 𝕜) =ᵐ[domainMeasure Set.univ] u := by
    simpa only [u, domainMeasure, Measure.restrict_univ] using (wholeSpaceL2_ae (firstProjection v)).symm
  have he : energy Set.univ s 2 (firstProjection v) =
      fourierConstant d hd s * fourierMoment s u :=
    (energy_congr hu).trans (hidentity d hd 𝕜 s hs0 hs1 u)
  have hSq : (seminorm Set.univ s 2 (firstProjection v)).toReal ^ 2 =
      q * (fourierMoment s u).toReal := by
    rw [← ENNReal.toReal_pow, seminorm_two_sq, he, ENNReal.toReal_mul]
  have hmcomp := bessel_energy_moment_comparison hs0.le u
  have hbcomp := bessel_energy_comparison d 𝕜 s hs0.le u
  have hloE : ‖u‖ₑ ^ (2 : ℕ) + fourierMoment s u ≤
      2 * besselEnergy (4 * Real.pi ^ 2) s u :=
    hmcomp.1.trans (mul_le_mul' le_rfl hbcomp.1)
  have hlo : ‖firstProjection v‖ ^ 2 + (fourierMoment s u).toReal ≤
      2 * hsNorm s u ^ 2 := by
    have hr := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (by norm_num) hHs.ne) hloE
    simpa only [ENNReal.toReal_add hmass hM.ne, ENNReal.toReal_pow,
      toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ← hHsq, u, wholeSpaceL2_norm] using hr
  have hhiE : besselEnergy (4 * Real.pi ^ 2) s u ≤
      ENNReal.ofReal ((4 * Real.pi ^ 2) ^ s) *
        (ENNReal.ofReal ((2 : ℝ) ^ s) * (‖u‖ₑ ^ (2 : ℕ) + fourierMoment s u)) :=
    hbcomp.2.trans (mul_le_mul' le_rfl hmcomp.2)
  have hhi : hsNorm s u ^ 2 ≤
      C * (‖firstProjection v‖ ^ 2 + (fourierMoment s u).toReal) := by
    have hr := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.add_ne_top.mpr ⟨hmass, hM.ne⟩))) hhiE
    simpa only [ENNReal.toReal_add hmass hM.ne, ENNReal.toReal_pow,
      toReal_enorm, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hscale.le, ENNReal.toReal_ofReal htwo.le,
      ← hHsq, u, wholeSpaceL2_norm, C, mul_assoc] using hr
  have h := real_norm_comparison ‖firstProjection v‖
    (seminorm Set.univ s 2 (firstProjection v)).toReal (fourierMoment s u).toReal
    (hsNorm s u) q C (norm_nonneg _) ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    (Real.sqrt_nonneg _) hq hC hSq hlo hhi
  simpa only [space_norm (by norm_num) v] using h


/-- Equivalence of the source's full Gagliardo norm and the Bessel-potential norm. -/
theorem fractional_norm_equivalence : Specs.P102.Fractional.Fourier.NormEquivalence :=
  norm_equivalence_of_fourier_identity fourierConstant_bounds fractional_fourier_identity

/-- The complete proposition following the definition of fractional Sobolev spaces. -/
theorem fractional_complete_proposition : Specs.P102.Fractional.Fourier.CompleteProposition :=
  ⟨fractional_banach, fractional_smoothCompact_memLp, fractional_smoothCompact_dense,
    fourierConstant_bounds, fractional_fourier_identity, library_bessel_identification,
    fractional_space_identification, fractional_norm_equivalence⟩

end P102.Fractional
