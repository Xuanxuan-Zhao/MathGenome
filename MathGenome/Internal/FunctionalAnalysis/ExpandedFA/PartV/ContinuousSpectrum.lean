import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.ContinuousSpectrum
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.FourierHilbertScale
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Multiplication.RealAndContinuousMultiplierSpectra

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology ComplexInnerProductSpace FourierTransform

namespace ExpandedFA.PartV.ContinuousSpectrum
open ExpandedFA.Fourier ExpandedFA.Sobolev.FourierScale

lemma realSymbol_pos (ξ : Line) : 0 < realSymbol ξ :=
  inv_pos.mpr (frequencyWeight_pos ξ)

lemma realSymbol_le_one (ξ : Line) : realSymbol ξ ≤ 1 :=
  inv_le_one_of_one_le₀ (frequencyWeight_one_le ξ)

lemma realSymbol_continuous : Continuous realSymbol := by
  unfold realSymbol frequencyWeight
  exact (continuous_const.add (continuous_const.mul (continuous_norm.pow 2))).inv₀
    (fun ξ => ne_of_gt (frequencyWeight_pos ξ))

lemma symbol_continuous : Continuous symbol :=
  Complex.continuous_ofReal.comp realSymbol_continuous

lemma symbol_eq_weight : symbol = complexWeight (-2) := by
  funext ξ
  simp [symbol, realSymbol, complexWeight, weight, Real.rpow_neg_one]

lemma symbol_norm_le_one (ξ : Line) : ‖symbol ξ‖ ≤ 1 := by
  simpa [symbol, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (realSymbol_pos ξ)]
    using realSymbol_le_one ξ

/-- Multiplication by m in frequency space. -/
def multiplier : Space →L[ℂ] Space :=
  multiplierL2CLM symbol
    (symbol_eq_weight ▸ complexWeight_hasTemperateGrowth (-2)) symbol_norm_le_one

lemma multiplier_coe (f : Space) :
    (multiplier f : Line → ℂ) =ᵐ[volume] fun ξ => symbol ξ * f ξ :=
  multiplierL2_coe symbol
    (symbol_eq_weight ▸ complexWeight_hasTemperateGrowth (-2)) symbol_norm_le_one f

/-- The bounded inverse in physical variables. -/
def inverse : Space →L[ℂ] Space :=
  (l2Fourier 1).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (multiplier.comp (l2Fourier 1).toContinuousLinearEquiv.toContinuousLinearMap)

lemma inverse_fourier : FourierFormula inverse := by
  intro f
  change (l2Fourier 1 ((l2Fourier 1).symm (multiplier (l2Fourier 1 f))) : Line → ℂ) =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact multiplier_coe _

lemma norm_sq_coordinate (ξ : Line) : ‖ξ‖ ^ 2 = (ξ 0) ^ 2 := by
  simpa using EuclideanSpace.real_norm_sq_eq ξ

lemma frequencyWeight_coordinate (ξ : Line) :
    frequencyWeight ξ = 1 + 4 * Real.pi ^ 2 * (ξ 0) ^ 2 := by
  rw [frequencyWeight, norm_sq_coordinate]

lemma realSymbol_single (t : ℝ) :
    realSymbol (EuclideanSpace.single (0 : Fin 1) t) =
      (1 + 4 * Real.pi ^ 2 * t ^ 2)⁻¹ := by
  simp [realSymbol, frequencyWeight_coordinate]

lemma realSymbol_zero : realSymbol 0 = 1 := by
  simp [realSymbol, frequencyWeight]

theorem symbol_range : Specs.ExpandedFA.PartV.ContinuousSpectrum.SymbolRange := by
  apply Set.Subset.antisymm
  · rintro _ ⟨ξ, rfl⟩
    exact ⟨realSymbol_pos ξ, realSymbol_le_one ξ⟩
  · intro y hy
    have hp : 0 < 4 * Real.pi ^ 2 := by positivity
    let t := Real.sqrt ((y⁻¹ - 1) / (4 * Real.pi ^ 2))
    have ht : t ^ 2 = (y⁻¹ - 1) / (4 * Real.pi ^ 2) := by
      apply Real.sq_sqrt
      exact div_nonneg (by have := one_le_inv₀ hy.1; exact this.mpr hy.2 |> sub_nonneg.mpr) hp.le
    refine ⟨EuclideanSpace.single (0 : Fin 1) t, ?_⟩
    rw [realSymbol_single, ht, mul_div_cancel₀ _ (ne_of_gt hp)]
    simp

theorem essential_range : Specs.ExpandedFA.PartV.ContinuousSpectrum.EssentialRange := by
  unfold Specs.ExpandedFA.PartV.ContinuousSpectrum.EssentialRange
  rw [ExpandedFA.Multiplication.continuous_essentialRange symbol symbol_continuous]
  change closure (Set.range (Complex.ofReal ∘ realSymbol)) = _
  rw [Set.range_comp, symbol_range,
    Complex.isometry_ofReal.isClosedEmbedding.closure_image_eq,
    closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)]

/-- The accepted Sobolev inclusion, with its actual distribution realization. -/
def inclusion : H2 →L[ℂ] Space := underlyingL2 1 2 (by norm_num)

/-- I - ∂² is unweighting the H² coordinate into physical L². -/
def operator : H2 →L[ℂ] Space :=
  (l2Fourier 1).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (coordinates 1 2).toContinuousLinearEquiv.toContinuousLinearMap

lemma inclusion_realization (u : H2) :
    realization u = Lp.toTemperedDistribution (inclusion u) :=
  realization_underlyingL2 (by norm_num) u

lemma inclusion_injective : Function.Injective inclusion :=
  underlyingL2_injective (by norm_num)

lemma inclusion_image (f : Space) :
    (∃ u, inclusion u = f) ↔ MemHs 2 (Lp.toTemperedDistribution f) := by
  rw [← realization_image 1 2]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, inclusion_realization u⟩
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    apply (LinearMap.ker_eq_bot.mp
      (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume) (p := 2)))
    exact (inclusion_realization u).symm.trans hu

lemma inclusion_fourier (u : H2) : l2Fourier 1 (inclusion u) = multiplier (coordinates 1 2 u) := by
  change l2Fourier 1 ((l2Fourier 1).symm (fourierDensityL2 (by norm_num) u)) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  filter_upwards [fourierDensityL2_coe (by norm_num) u, multiplier_coe (coordinates 1 2 u)] with ξ hξ hη
  rw [hξ, hη]
  simp only [fourierDensity, symbol_eq_weight]

lemma inverse_lands_in_H2 (f : Space) :
    ∃ u : H2, inclusion u = inverse f ∧ operator u = f := by
  refine ⟨(coordinates 1 2).symm (l2Fourier 1 f), ?_, ?_⟩
  · apply (l2Fourier 1).injective
    rw [inclusion_fourier, LinearIsometryEquiv.apply_symm_apply]
    change _ = l2Fourier 1 ((l2Fourier 1).symm (multiplier (l2Fourier 1 f)))
    rw [LinearIsometryEquiv.apply_symm_apply]
  · change (l2Fourier 1).symm (coordinates 1 2 ((coordinates 1 2).symm (l2Fourier 1 f))) = _
    simp

lemma inverse_left (u : H2) : inverse (operator u) = inclusion u := by
  apply (l2Fourier 1).injective
  rw [inclusion_fourier]
  change l2Fourier 1 ((l2Fourier 1).symm
    (multiplier (l2Fourier 1 ((l2Fourier 1).symm (coordinates 1 2 u))))) = _
  simp

lemma coordinate_eq_or_neg_of_symbol_eq {ξ η : Line} (h : symbol ξ = symbol η) :
    ξ 0 = η 0 ∨ ξ 0 = -(η 0) := by
  have hi : frequencyWeight ξ = frequencyWeight η := by
    apply inv_injective
    exact Complex.ofReal_injective h
  rw [frequencyWeight_coordinate, frequencyWeight_coordinate] at hi
  have hp : 0 < 4 * Real.pi ^ 2 := by positivity
  have he : (ξ 0) ^ 2 = (η 0) ^ 2 := by nlinarith
  exact (sq_eq_sq_iff_eq_or_eq_neg).mp he

lemma line_eq_or_neg_of_symbol_eq {ξ η : Line} (h : symbol ξ = symbol η) :
    ξ = η ∨ ξ = -η := by
  rcases coordinate_eq_or_neg_of_symbol_eq h with h | h
  · left
    ext i
    have : i = 0 := Subsingleton.elim _ _
    simpa [this] using h
  · right
    ext i
    have : i = 0 := Subsingleton.elim _ _
    simpa [this] using h

theorem null_levels : Specs.ExpandedFA.PartV.ContinuousSpectrum.NullLevels := by
  intro z
  by_cases h : {ξ : Line | symbol ξ = z}.Nonempty
  · obtain ⟨η, hη⟩ := h
    apply measure_mono_null (t := ({η, -η} : Set Line))
    · intro ξ hξ
      rcases line_eq_or_neg_of_symbol_eq (hξ.trans hη.symm) with he | he
      · simp [he]
      · simp [he]
    · exact ((Set.finite_singleton (-η)).insert η).measure_zero volume
  · rw [Set.not_nonempty_iff_eq_empty.mp h, measure_empty]

lemma multiplier_no_eigenvalues (z : ℂ) (f : Space) (h : multiplier f = z • f) : f = 0 := by
  apply Lp.ext
  have hnull : ∀ᵐ ξ : Line ∂volume, symbol ξ ≠ z := by
    simpa only [ae_iff, not_not] using null_levels z
  filter_upwards [multiplier_coe f, Lp.coeFn_smul z f, Lp.coeFn_zero ℂ 2 (volume : Measure Line), hnull]
    with ξ hm hs hzero hne
  rw [h, hs] at hm
  change z * f ξ = symbol ξ * f ξ at hm
  rw [hzero]
  have he : (symbol ξ - z) * f ξ = 0 := by
    rw [sub_mul, hm, sub_self]
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hne)

lemma inverse_no_eigenvalues (z : ℂ) (f : Space) (h : inverse f = z • f) : f = 0 := by
  apply (l2Fourier 1).injective
  rw [map_zero]
  apply multiplier_no_eigenvalues z
  have he := congrArg (l2Fourier 1) h
  change l2Fourier 1 ((l2Fourier 1).symm (multiplier (l2Fourier 1 f))) = _ at he
  rw [LinearIsometryEquiv.apply_symm_apply] at he
  simpa only [map_smul] using he

lemma inverse_norm_le_one : ‖inverse‖ ≤ 1 := by
  apply inverse.opNorm_le_bound (by norm_num : (0 : ℝ) ≤ 1)
  intro f
  change ‖(l2Fourier 1).symm (multiplier (l2Fourier 1 f))‖ ≤ 1 * ‖f‖
  rw [LinearIsometryEquiv.norm_map, one_mul]
  calc
    ‖multiplier (l2Fourier 1 f)‖ ≤ 1 * ‖l2Fourier 1 f‖ :=
      multiplierL2_norm_le symbol
        (symbol_eq_weight ▸ complexWeight_hasTemperateGrowth (-2)) symbol_norm_le_one _
    _ = ‖f‖ := by simp

lemma multiplier_selfAdjoint : IsSelfAdjoint multiplier := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℂ (multiplier f) g = inner ℂ f (multiplier g)
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplier_coe f, multiplier_coe g] with ξ hf hg
  simp only [hf, hg, RCLike.inner_apply, map_mul, symbol, Complex.conj_ofReal]
  ring

lemma inverse_selfAdjoint : IsSelfAdjoint inverse := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℂ (inverse f) g = inner ℂ f (inverse g)
  rw [← (l2Fourier 1).inner_map_map (inverse f) g,
    ← (l2Fourier 1).inner_map_map f (inverse g)]
  change inner ℂ (l2Fourier 1 ((l2Fourier 1).symm (multiplier (l2Fourier 1 f)))) _ =
    inner ℂ _ (l2Fourier 1 ((l2Fourier 1).symm (multiplier (l2Fourier 1 g))))
  simp only [LinearIsometryEquiv.apply_symm_apply]
  exact multiplier_selfAdjoint.isSymmetric _ _

lemma bessel_symbol : complexWeight (d := 1) 2 =
    fun ξ : Line => 1 - ((2 * Real.pi * Complex.I) * (ξ 0 : ℂ)) *
      ((2 * Real.pi * Complex.I) * (ξ 0 : ℂ)) := by
  funext ξ
  simp only [complexWeight, weight, show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one,
    frequencyWeight_coordinate, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_ofNat]
  linear_combination (4 * (Real.pi : ℂ) ^ 2 * (ξ 0 : ℂ) ^ 2) * Complex.I_sq

lemma differential_fourier (T : Tempered ℂ 1) :
    temperedFourier (differential T) =
      TemperedDistribution.smulLeftCLM ℂ (complexWeight 2) (temperedFourier T) := by
  have hp : (fun ξ : Line => (2 * Real.pi * Complex.I) * (ξ 0 : ℂ)).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).mul (coordinate_growth (𝕜 := ℂ) 0)
  have hsub : temperedFourier (differential T) =
      temperedFourier T - temperedFourier (temperedPartial 0 (temperedPartial 0 T)) := by
    ext φ
    rfl
  rw [hsub]
  rw [fourier_temperedPartial_symbol, fourier_temperedPartial_symbol,
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hp hp, bessel_symbol]
  have hs := TemperedDistribution.smulLeftCLM_sub (F := ℂ)
    (Function.HasTemperateGrowth.const (1 : ℂ)) (hp.mul hp)
  change _ = TemperedDistribution.smulLeftCLM ℂ
    ((fun _ : Line => (1 : ℂ)) -
      (fun ξ : Line => (2 * Real.pi * Complex.I) * (ξ 0 : ℂ)) *
      (fun ξ : Line => (2 * Real.pi * Complex.I) * (ξ 0 : ℂ))) (temperedFourier T)
  rw [hs]
  simp only [sub_apply, TemperedDistribution.smulLeftCLM_const, one_smul]

lemma operator_distribution (u : H2) :
    Lp.toTemperedDistribution (operator u) = differential (realization u) := by
  apply (FourierTransform.fourierEquiv ℂ (TemperedDistribution Line ℂ)).injective
  change 𝓕 (Lp.toTemperedDistribution (operator u)) = temperedFourier (differential (realization u))
  rw [differential_fourier, weighted_fourier_realization, Lp.fourier_toTemperedDistribution_eq]
  change Lp.toTemperedDistribution
    (l2Fourier 1 ((l2Fourier 1).symm (coordinates 1 2 u))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]

lemma domain_and_inverse : DomainAndInverse inclusion operator inverse :=
  ⟨inclusion_injective, inclusion_realization, inclusion_image, operator_distribution,
    inverse_lands_in_H2, inverse_left⟩

open ExpandedFA.Multiplication ExpandedFA.Unbounded

lemma multiplier_domain_full : (maximalMultiplier (volume : Measure Line) 2 symbol).domain = ⊤ := by
  apply full_domain_of_memLp_top symbol symbol_continuous.measurable
  exact memLp_top_of_bound symbol_continuous.aestronglyMeasurable 1
    (Eventually.of_forall symbol_norm_le_one)

lemma maximal_apply_eq (f : (maximalMultiplier (volume : Measure Line) 2 symbol).domain) :
    maximalMultiplier volume 2 symbol f = multiplier f := by
  apply Lp.ext
  exact (maximalLpMultiplier_apply volume 2 symbol f).trans (multiplier_coe f).symm

/-- The native Banach-algebra spectrum agrees with the accepted exact-domain
multiplier spectrum. Both directions explicitly preserve the inverse equations. -/
lemma spectrum_multiplier_eq : spectrum ℂ multiplier =
    multiplierSpectrum (volume : Measure Line) 2 symbol := by
  ext z
  change (¬ IsUnit (algebraMap ℂ (Space →L[ℂ] Space) z - multiplier)) ↔
    ¬ Nonempty (ResolventInverse (maximalMultiplier (volume : Measure Line) 2 symbol) z)
  apply not_congr
  rw [isUnit_iff_exists]
  constructor
  · rintro ⟨B, hright, hleft⟩
    have hmem : ∀ f : Space, B f ∈ (maximalMultiplier (volume : Measure Line) 2 symbol).domain := by
      intro f
      rw [multiplier_domain_full]
      trivial
    refine ⟨⟨B, hmem, ?_, ?_⟩⟩
    · intro f
      rw [maximal_apply_eq]
      exact congrArg (fun T : Space →L[ℂ] Space => T f) hright
    · intro f
      rw [maximal_apply_eq]
      exact congrArg (fun T : Space →L[ℂ] Space => T (f : Space)) hleft
  · rintro ⟨R⟩
    refine ⟨R.inverse, ?_, ?_⟩
    · apply ContinuousLinearMap.ext
      intro f
      change z • R.inverse f - multiplier (R.inverse f) = f
      rw [← maximal_apply_eq ⟨R.inverse f, R.mem_domain f⟩]
      exact R.right_inverse f
    · apply ContinuousLinearMap.ext
      intro f
      change R.inverse (z • f - multiplier f) = f
      have hf : f ∈ (maximalMultiplier (volume : Measure Line) 2 symbol).domain := by
        rw [multiplier_domain_full]
        trivial
      rw [← maximal_apply_eq ⟨f, hf⟩]
      exact R.left_inverse ⟨f, hf⟩

lemma multiplier_spectrum_interval : spectrum ℂ multiplier =
    Complex.ofReal '' Set.Icc (0 : ℝ) 1 := by
  rw [spectrum_multiplier_eq, multiplier_spectrum volume (semifinite_of_sigmaFinite volume)
    2 (by norm_num) (by norm_num) symbol symbol_continuous.measurable, essential_range]

lemma inverse_spectrum : spectrum ℂ inverse = Complex.ofReal '' Set.Icc (0 : ℝ) 1 := by
  have he : inverse = (l2Fourier 1).symm.toContinuousLinearEquiv.conjContinuousAlgEquiv multiplier := rfl
  rw [he, AlgEquiv.spectrum_eq, multiplier_spectrum_interval]

lemma inverse_norm : ‖inverse‖ = 1 := by
  apply le_antisymm inverse_norm_le_one
  have h : (1 : ℂ) ∈ spectrum ℂ inverse := by
    rw [inverse_spectrum]
    exact ⟨1, ⟨zero_le_one, le_rfl⟩, by simp⟩
  have hm := spectrum.norm_le_norm_mul_of_mem h
  have hid : ‖(1 : Space →L[ℂ] Space)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hmul := mul_le_mul_of_nonneg_left hid (norm_nonneg inverse)
  simpa using hm.trans hmul

/-- All frequency intervals lie where the reciprocal symbol is at least 1/2. -/
def cutoff : ℝ := (2 * Real.pi)⁻¹

def intervalEndpoint (n : ℕ) : ℝ := cutoff / (n + 1 : ℝ)

def frequencyInterval (n : ℕ) : Set Line :=
  {ξ | intervalEndpoint (n + 1) < ξ 0 ∧ ξ 0 < intervalEndpoint n}

lemma cutoff_pos : 0 < cutoff := by unfold cutoff; positivity

lemma intervalEndpoint_pos (n : ℕ) : 0 < intervalEndpoint n := by
  exact div_pos cutoff_pos (by positivity)

lemma intervalEndpoint_strictAnti : StrictAnti intervalEndpoint := by
  apply strictAnti_nat_of_succ_lt
  intro n
  unfold intervalEndpoint
  exact div_lt_div_of_pos_left cutoff_pos (by positivity) (by push_cast; linarith)

lemma frequencyInterval_open (n : ℕ) : IsOpen (frequencyInterval n) := by
  change IsOpen ({ξ : Line | intervalEndpoint (n+1) < ξ 0} ∩
    {ξ : Line | ξ 0 < intervalEndpoint n})
  exact (isOpen_lt continuous_const (by fun_prop)).inter
    (isOpen_lt (by fun_prop) continuous_const)

lemma frequencyInterval_nonempty (n : ℕ) : (frequencyInterval n).Nonempty := by
  obtain ⟨t, ht⟩ := exists_between (intervalEndpoint_strictAnti (Nat.lt_succ_self n))
  refine ⟨EuclideanSpace.single (0 : Fin 1) t, ?_⟩
  simpa [frequencyInterval] using ht

lemma frequencyIntervals_disjoint : Pairwise (fun n k => Disjoint (frequencyInterval n) (frequencyInterval k)) := by
  intro n k hnk
  apply Set.disjoint_left.mpr
  intro ξ hn hk
  change intervalEndpoint (n+1) < ξ 0 ∧ ξ 0 < intervalEndpoint n at hn
  change intervalEndpoint (k+1) < ξ 0 ∧ ξ 0 < intervalEndpoint k at hk
  rcases lt_or_gt_of_ne hnk with h | h
  · have he := intervalEndpoint_strictAnti.antitone (Nat.succ_le_of_lt h)
    linarith
  · have he := intervalEndpoint_strictAnti.antitone (Nat.succ_le_of_lt h)
    linarith

lemma frequencyInterval_coordinate_bound {n : ℕ} {ξ : Line} (hξ : ξ ∈ frequencyInterval n) :
    0 < ξ 0 ∧ ξ 0 < cutoff := by
  change intervalEndpoint (n+1) < ξ 0 ∧ ξ 0 < intervalEndpoint n at hξ
  refine ⟨(intervalEndpoint_pos _).trans hξ.1, hξ.2.trans_le ?_⟩
  have := intervalEndpoint_strictAnti.antitone (Nat.zero_le n)
  simpa [intervalEndpoint] using this

lemma frequencyInterval_bounded (n : ℕ) :
    frequencyInterval n ⊆ Metric.closedBall (0 : Line) cutoff := by
  intro ξ hξ
  rw [Metric.mem_closedBall, dist_zero_right]
  have h := frequencyInterval_coordinate_bound hξ
  have hs := norm_sq_coordinate ξ
  nlinarith [norm_nonneg ξ, cutoff_pos]

lemma frequencyInterval_measure (n : ℕ) :
    0 < volume (frequencyInterval n) ∧ volume (frequencyInterval n) < ∞ := by
  refine ⟨(frequencyInterval_open n).measure_pos volume (frequencyInterval_nonempty n), ?_⟩
  exact (measure_mono (frequencyInterval_bounded n)).trans_lt
    (isCompact_closedBall (0 : Line) cutoff).measure_lt_top

lemma symbol_lower_on_interval {n : ℕ} {ξ : Line} (hξ : ξ ∈ frequencyInterval n) :
    (1 / 2 : ℝ) ≤ ‖symbol ξ‖ := by
  rw [symbol, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (realSymbol_pos ξ)]
  have hc := frequencyInterval_coordinate_bound hξ
  have hp : 0 < 4 * Real.pi ^ 2 := by positivity
  have he : 4 * Real.pi ^ 2 * cutoff ^ 2 = 1 := by
    unfold cutoff
    field_simp
    ring
  have hsq : (ξ 0) ^ 2 ≤ cutoff ^ 2 := by nlinarith [cutoff_pos]
  have hw : frequencyWeight ξ ≤ 2 := by
    rw [frequencyWeight_coordinate]
    nlinarith
  unfold realSymbol
  simpa only [one_div] using one_div_le_one_div_of_le (frequencyWeight_pos ξ) hw

def intervalIndicator (n : ℕ) : Space :=
  indicatorConstLp 2 (frequencyInterval_open n).measurableSet
    (frequencyInterval_measure n).2.ne (1 : ℂ)

lemma intervalIndicator_norm_pos (n : ℕ) : 0 < ‖intervalIndicator n‖ :=
  indicator_norm_pos (by norm_num) (frequencyInterval_open n).measurableSet
    (frequencyInterval_measure n).1 (frequencyInterval_measure n).2

lemma intervalIndicator_coe (n : ℕ) :
    (intervalIndicator n : Line → ℂ) =ᵐ[volume]
      (frequencyInterval n).indicator (fun _ => (1 : ℂ)) :=
  indicatorConstLp_coeFn

def normalizedIndicator (n : ℕ) : Space :=
  ((‖intervalIndicator n‖⁻¹ : ℝ) : ℂ) • intervalIndicator n

lemma normalizedIndicator_norm (n : ℕ) : ‖normalizedIndicator n‖ = 1 := by
  rw [normalizedIndicator, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (intervalIndicator_norm_pos n))]
  exact inv_mul_cancel₀ (ne_of_gt (intervalIndicator_norm_pos n))

lemma normalizedIndicator_coe (n : ℕ) :
    (normalizedIndicator n : Line → ℂ) =ᵐ[volume]
      (frequencyInterval n).indicator (fun _ => ((‖intervalIndicator n‖⁻¹ : ℝ) : ℂ)) := by
  filter_upwards [Lp.coeFn_smul (((‖intervalIndicator n‖⁻¹ : ℝ) : ℂ)) (intervalIndicator n),
    intervalIndicator_coe n] with ξ hs hi
  rw [normalizedIndicator, hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hi]
  by_cases hξ : ξ ∈ frequencyInterval n <;> simp [hξ]

lemma intervalIndicator_inner {n k : ℕ} (hnk : n ≠ k) :
    inner ℂ (intervalIndicator n) (intervalIndicator k) = 0 := by
  rw [intervalIndicator, intervalIndicator, L2.inner_indicatorConstLp_one_indicatorConstLp_one
    (frequencyInterval_open n).measurableSet (frequencyInterval_open k).measurableSet
    (frequencyInterval_measure n).2.ne (frequencyInterval_measure k).2.ne,
    Set.disjoint_iff_inter_eq_empty.mp (frequencyIntervals_disjoint hnk)]
  simp

lemma normalizedIndicator_inner {n k : ℕ} (hnk : n ≠ k) :
    inner ℂ (normalizedIndicator n) (normalizedIndicator k) = 0 := by
  simp [normalizedIndicator, inner_smul_left, inner_smul_right, intervalIndicator_inner hnk]

lemma indicator_images_separated {n k : ℕ} (hnk : n ≠ k) :
    (1 / 2 : ℝ) ≤ ‖multiplier (normalizedIndicator n) - multiplier (normalizedIndicator k)‖ := by
  have h : ‖normalizedIndicator n‖ ≤ 2 *
      ‖multiplier (normalizedIndicator n) - multiplier (normalizedIndicator k)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [normalizedIndicator_coe n, normalizedIndicator_coe k,
      multiplier_coe (normalizedIndicator n), multiplier_coe (normalizedIndicator k),
      Lp.coeFn_sub (multiplier (normalizedIndicator n)) (multiplier (normalizedIndicator k))]
      with ξ hn hk hmn hmk hsub
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hmn, hmk]
    by_cases hξ : ξ ∈ frequencyInterval n
    · have hξk : ξ ∉ frequencyInterval k := fun h =>
        Set.disjoint_left.mp (frequencyIntervals_disjoint hnk) hξ h
      have hk0 : normalizedIndicator k ξ = 0 := by rw [hk]; simp [hξk]
      rw [hk0, mul_zero, sub_zero, norm_mul]
      have hlow := symbol_lower_on_interval hξ
      nlinarith [norm_nonneg ((normalizedIndicator n) ξ)]
    · have hn0 : normalizedIndicator n ξ = 0 := by rw [hn]; simp [hξ]
      rw [hn0, norm_zero]
      positivity
  rw [normalizedIndicator_norm] at h
  linarith

lemma inverse_indicator_images_separated {n k : ℕ} (hnk : n ≠ k) :
    (1 / 2 : ℝ) ≤ ‖inverse ((l2Fourier 1).symm (normalizedIndicator n)) -
      inverse ((l2Fourier 1).symm (normalizedIndicator k))‖ := by
  rw [← (l2Fourier 1).norm_map, map_sub]
  change (1 / 2 : ℝ) ≤ ‖l2Fourier 1 ((l2Fourier 1).symm
    (multiplier (l2Fourier 1 ((l2Fourier 1).symm (normalizedIndicator n))))) -
    l2Fourier 1 ((l2Fourier 1).symm
    (multiplier (l2Fourier 1 ((l2Fourier 1).symm (normalizedIndicator k)))))‖
  simp only [LinearIsometryEquiv.apply_symm_apply]
  exact indicator_images_separated hnk

lemma separated_indicators : SeparatedIndicators inverse := by
  refine ⟨frequencyInterval, normalizedIndicator, frequencyIntervals_disjoint, ?_, ?_,
    normalizedIndicator_norm, ?_, ?_⟩
  · intro n
    exact ⟨(frequencyInterval_open n).measurableSet, frequencyInterval_measure n⟩
  · intro n
    exact ⟨‖intervalIndicator n‖⁻¹, inv_pos.mpr (intervalIndicator_norm_pos n), normalizedIndicator_coe n⟩
  · intro n k hnk
    exact normalizedIndicator_inner hnk
  · intro n k hnk
    exact inverse_indicator_images_separated hnk

lemma inverse_not_compact : ¬ IsCompactOperator inverse := by
  intro hc
  obtain ⟨K, hK, hsub⟩ := hc.image_closedBall_subset_compact (f := inverse.toLinearMap) 1
  have hmem (n : ℕ) : inverse ((l2Fourier 1).symm (normalizedIndicator n)) ∈ K := by
    apply hsub
    refine ⟨(l2Fourier 1).symm (normalizedIndicator n), ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map, normalizedIndicator_norm]
  obtain ⟨a, _ha, φ, hφ, ht⟩ := hK.tendsto_subseq hmem
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp ht.cauchySeq (1 / 2) (by norm_num)
  have hlt := hN N le_rfl (N + 1) (by omega)
  have hlow := inverse_indicator_images_separated
    (hφ.injective.ne (show N ≠ N + 1 by omega))
  change dist (inverse ((l2Fourier 1).symm (normalizedIndicator (φ N))))
    (inverse ((l2Fourier 1).symm (normalizedIndicator (φ (N+1))))) < 1 / 2 at hlt
  rw [dist_eq_norm] at hlt
  exact (not_lt_of_ge hlow) hlt

theorem real_line_model : Specs.ExpandedFA.PartV.ContinuousSpectrum.RealLineModel := by
  let e : Line ≃ₗᵢ[ℝ] ℝ := (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm
  refine ⟨e, ?_, e.measurePreserving⟩
  intro ξ
  have h := congrArg (fun v : Line => v 0)
    ((OrthonormalBasis.singleton (Fin 1) ℝ).repr.apply_symm_apply ξ)
  simpa only [OrthonormalBasis.singleton_repr] using h

/-- The complete source example, with the Sobolev domain checked. -/
theorem continuous_spectrum_example : Specs.ExpandedFA.PartV.ContinuousSpectrum.Result := by
  exact ⟨real_line_model, inclusion, operator, inverse, domain_and_inverse, inverse_fourier,
    inverse_selfAdjoint, inverse_norm, inverse_spectrum, inverse_no_eigenvalues,
    inverse_not_compact, separated_indicators⟩


/- The real scalar restriction and its physical realization. -/
namespace RealVersion

lemma embedding_coe (f : RealSpace) :
    complexEmbedding f =ᵐ[volume] fun x => (f x : ℂ) :=
  Complex.ofRealCLM.coeFn_compLp f

lemma re_coe (f : Space) : physicalRealPart f =ᵐ[volume] fun x => (f x).re :=
  Complex.reCLM.coeFn_compLp f

lemma im_coe (f : Space) : physicalImagPart f =ᵐ[volume] fun x => (f x).im :=
  Complex.imCLM.coeFn_compLp f

lemma re_embedding (f : RealSpace) : physicalRealPart (complexEmbedding f) = f := by
  apply Lp.ext
  filter_upwards [re_coe (complexEmbedding f), embedding_coe f] with x hr he
  simp [hr, he]

lemma embedding_injective : Function.Injective complexEmbedding :=
  Function.LeftInverse.injective re_embedding

lemma embedding_norm (f : RealSpace) : ‖complexEmbedding f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [embedding_coe f] with x hx
  simp [hx]

lemma decompose (f : Space) : f = complexEmbedding (physicalRealPart f) +
    Complex.I • complexEmbedding (physicalImagPart f) := by
  apply Lp.ext
  filter_upwards [embedding_coe (physicalRealPart f), embedding_coe (physicalImagPart f),
    re_coe f, im_coe f, Lp.coeFn_add (complexEmbedding (physicalRealPart f))
      (Complex.I • complexEmbedding (physicalImagPart f)),
    Lp.coeFn_smul Complex.I (complexEmbedding (physicalImagPart f))] with x hr hi hre him ha hs
  rw [ha]
  simp only [Pi.add_apply]
  rw [hs]
  simp only [Pi.smul_apply, smul_eq_mul, hr, hi, hre, him]
  simpa only [mul_comm] using (Complex.re_add_im (f x)).symm

lemma realRegular_apply (f : RealSpace) (φ : Schwartz ℝ 1) :
    realRegularL2 f φ = ∫ x, φ x * f x := by
  change (Lp.toTemperedDistribution (complexEmbedding f) (complexifySchwartz φ)).re = _
  rw [Lp.toTemperedDistribution_apply]
  have he : (∫ x, (complexifySchwartz φ) x • complexEmbedding f x) =
      ((∫ x, φ x * f x : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [embedding_coe f] with x hx
    simp [hx, complexifySchwartz]
  rw [he, Complex.ofReal_re]

lemma embedding_distribution (f : RealSpace) :
    complexifyTempered (realRegularL2 f) =
      Lp.toTemperedDistribution (complexEmbedding f) := by
  apply complexify_restrict_of_real
  intro φ
  rw [Lp.toTemperedDistribution_apply]
  have he : (∫ x, (complexifySchwartz φ) x • complexEmbedding f x) =
      ((∫ x, φ x * f x : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [embedding_coe f] with x hx
    simp [hx, complexifySchwartz]
  rw [he, Complex.ofReal_im]

lemma restrict_distribution (f : Space) :
    restrictTempered (Lp.toTemperedDistribution f) =
      realRegularL2 (physicalRealPart f) := by
  ext φ
  change (Lp.toTemperedDistribution f (complexifySchwartz φ)).re = _
  rw [Lp.toTemperedDistribution_apply, realRegular_apply]
  have hi := integral_re (𝕜 := ℂ)
    (((complexifySchwartz φ).memLp 2 volume).integrable_mul (Lp.memLp f))
  change (∫ x, ((complexifySchwartz φ) x * f x).re) =
    (∫ x, (complexifySchwartz φ) x * f x).re at hi
  change (∫ x, (complexifySchwartz φ) x * f x).re = _
  rw [← hi]
  apply integral_congr_ae
  filter_upwards [re_coe f] with x hx
  simp [hx, complexifySchwartz]

lemma realConjugation_coe (f : Space) :
    realConjugationL2 1 f =ᵐ[volume] fun x => star (f x) :=
  Complex.conjCLE.toContinuousLinearMap.coeFn_compLp f

lemma conjugate_distribution (f : Space) (φ : Schwartz ℂ 1) :
    Lp.toTemperedDistribution (realConjugationL2 1 f) φ =
      star (Lp.toTemperedDistribution f (conjSchwartz φ)) := by
  rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply]
  change _ = (starRingEnd ℂ) _
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [realConjugation_coe f]
    with x hx
  simp [hx]

lemma invFourier_conjugateReflection (f : Space) :
    (l2Fourier 1).symm (realConjugateReflectionL2 1 f) =
      realConjugationL2 1 ((l2Fourier 1).symm f) := by
  apply (LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume) (p := 2)))
  ext φ
  change Lp.toTemperedDistribution ((l2Fourier 1).symm (realConjugateReflectionL2 1 f)) φ =
    Lp.toTemperedDistribution (realConjugationL2 1 ((l2Fourier 1).symm f)) φ
  rw [conjugate_distribution]
  have h := realization_conjugateReflection (s := 0) f φ
  rw [realization_zero, realization_zero] at h
  exact h

lemma embedding_re_iff (f : Space) :
    complexEmbedding (physicalRealPart f) = f ↔ realConjugationL2 1 f = f := by
  constructor
  · intro hf
    apply Lp.ext
    filter_upwards [embedding_coe (physicalRealPart f), re_coe f,
      realConjugation_coe f] with x he hr hc
    have hh := congrArg (fun g : Space => g x) hf
    rw [he, hr] at hh
    rw [hc, ← hh]
    simp
  · intro hf
    apply Lp.ext
    filter_upwards [embedding_coe (physicalRealPart f), re_coe f,
      realConjugation_coe f] with x he hr hc
    have hh := congrArg (fun g : Space => g x) hf
    rw [hc] at hh
    rw [he, hr]
    exact Complex.ext (by simp) (by have := congrArg Complex.im hh; simp at this; simp; linarith)

lemma invFourier_real (f : Space) (hf : f ∈ hermitianL2 1) :
    complexEmbedding (physicalRealPart ((l2Fourier 1).symm f)) = (l2Fourier 1).symm f := by
  apply (embedding_re_iff _).mpr
  rw [← invFourier_conjugateReflection, (hermitianL2_mem_iff 1 f).mp hf]

lemma fourier_embedding_hermitian (f : RealSpace) :
    l2Fourier 1 (complexEmbedding f) ∈ hermitianL2 1 := by
  apply (hermitianL2_mem_iff 1 _).mpr
  apply (l2Fourier 1).symm.injective
  rw [invFourier_conjugateReflection, LinearIsometryEquiv.symm_apply_apply]
  apply (embedding_re_iff _).mp
  rw [re_embedding]

lemma multiplier_hermitian (f : Space) (hf : f ∈ hermitianL2 1) :
    multiplier f ∈ hermitianL2 1 := by
  apply (hermitianL2_mem_iff_ae 1 _).mpr
  have hneg := (Measure.measurePreserving_neg (volume : Measure Line)).quasiMeasurePreserving.ae
    (multiplier_coe f)
  filter_upwards [multiplier_coe f, hneg, (hermitianL2_mem_iff_ae 1 f).mp hf]
    with x hx hn hf
  change multiplier f (-x) = symbol (-x) * f (-x) at hn
  rw [hn, hf, hx]
  simp [symbol, realSymbol, frequencyWeight]

def inverse : RealSpace →L[ℝ] RealSpace :=
  physicalRealPart.comp
    ((ContinuousSpectrum.inverse.restrictScalars ℝ).comp complexEmbedding)

def inclusion : RealH2 →L[ℝ] RealSpace :=
  physicalRealPart.comp ((ContinuousSpectrum.inclusion.restrictScalars ℝ).comp
    (realCoordinates 1 2).toContinuousLinearMap)

def operator : RealH2 →L[ℝ] RealSpace :=
  physicalRealPart.comp ((ContinuousSpectrum.operator.restrictScalars ℝ).comp
    (realCoordinates 1 2).toContinuousLinearMap)

lemma inverse_complexify (f : RealSpace) :
    complexEmbedding (inverse f) = ContinuousSpectrum.inverse (complexEmbedding f) :=
  invFourier_real _ (multiplier_hermitian _ (fourier_embedding_hermitian f))

lemma inverse_fourier : RealFourierFormula inverse := by
  intro f
  rw [inverse_complexify]
  exact ContinuousSpectrum.inverse_fourier (complexEmbedding f)

lemma operator_complexify (u : RealH2) :
    complexEmbedding (operator u) = ContinuousSpectrum.operator (realCoordinates 1 2 u) :=
  invFourier_real _ u.property

lemma inclusion_complexify (u : RealH2) :
    complexEmbedding (inclusion u) = ContinuousSpectrum.inclusion (realCoordinates 1 2 u) := by
  have he : ContinuousSpectrum.inclusion (realCoordinates 1 2 u) =
      (l2Fourier 1).symm (multiplier (realCoordinates 1 2 u)) := by
    apply (l2Fourier 1).injective
    rw [inclusion_fourier, LinearIsometryEquiv.apply_symm_apply]
    rfl
  change complexEmbedding (physicalRealPart (ContinuousSpectrum.inclusion (realCoordinates 1 2 u))) =
    ContinuousSpectrum.inclusion (realCoordinates 1 2 u)
  rw [he]
  exact invFourier_real _ (multiplier_hermitian _ u.property)

lemma inclusion_injective : Function.Injective inclusion := by
  intro u v h
  apply Subtype.ext
  apply ContinuousSpectrum.inclusion_injective
  exact (inclusion_complexify u).symm.trans
    ((congrArg complexEmbedding h).trans (inclusion_complexify v))

lemma inclusion_realization (u : RealH2) :
    realRealization u = realRegularL2 (inclusion u) := by
  apply complexifyTempered_injective 1
  rw [complexify_realRealization, embedding_distribution, inclusion_complexify,
    ContinuousSpectrum.inclusion_realization]

lemma inclusion_image (f : RealSpace) :
    (∃ u, inclusion u = f) ↔ realMemHs 2 (realRegularL2 f) := by
  unfold realMemHs
  rw [embedding_distribution, ← ContinuousSpectrum.inclusion_image]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨realCoordinates 1 2 u, (inclusion_complexify u).symm⟩
  · rintro ⟨u, hu⟩
    have hreal : u ∈ hermitianL2 1 := by
      apply (realization_real_iff (s := 2) u).mpr
      intro φ
      rw [ContinuousSpectrum.inclusion_realization, hu, ← embedding_distribution,
        complexifyTempered_apply_complexifySchwartz, Complex.ofReal_im]
    refine ⟨⟨u, hreal⟩, embedding_injective ?_⟩
    exact (inclusion_complexify ⟨u, hreal⟩).trans hu

lemma operator_distribution (u : RealH2) :
    Lp.toTemperedDistribution (complexEmbedding (operator u)) =
      differential (complexifyTempered (realRealization u)) := by
  rw [operator_complexify, complexify_realRealization,
    ContinuousSpectrum.operator_distribution]

lemma inverse_lands_in_H2 (f : RealSpace) :
    ∃ u : RealH2, inclusion u = inverse f ∧ operator u = f := by
  let u : RealH2 := ⟨l2Fourier 1 (complexEmbedding f), fourier_embedding_hermitian f⟩
  have hA : ContinuousSpectrum.operator (realCoordinates 1 2 u) = complexEmbedding f := by
    change (l2Fourier 1).symm (l2Fourier 1 (complexEmbedding f)) = _
    simp
  refine ⟨u, embedding_injective ?_, embedding_injective ?_⟩
  · rw [inclusion_complexify, inverse_complexify, ← hA, ContinuousSpectrum.inverse_left]
  · rw [operator_complexify, hA]

lemma inverse_left (u : RealH2) : inverse (operator u) = inclusion u := by
  apply embedding_injective
  rw [inverse_complexify, operator_complexify, inclusion_complexify,
    ContinuousSpectrum.inverse_left]

lemma domain_and_inverse : RealDomainAndInverse inclusion operator inverse :=
  ⟨inclusion_injective, inclusion_realization, inclusion_image, operator_distribution,
    inverse_lands_in_H2, inverse_left⟩

lemma inverse_decompose (f : Space) : ContinuousSpectrum.inverse f =
    complexEmbedding (inverse (physicalRealPart f)) +
      Complex.I • complexEmbedding (inverse (physicalImagPart f)) := by
  rw [inverse_complexify, inverse_complexify, ← map_smul, ← map_add, ← decompose]

lemma compatibility : RealCompatibility ContinuousSpectrum.inclusion ContinuousSpectrum.operator
    ContinuousSpectrum.inverse inclusion operator inverse :=
  ⟨inclusion_complexify, operator_complexify, inverse_complexify, decompose, inverse_decompose⟩

def embeddingIsometry : RealSpace →ₗᵢ[ℝ] Space :=
  ⟨complexEmbedding.toLinearMap, embedding_norm⟩

lemma embedding_inner (f g : RealSpace) :
    inner ℝ f g = (inner ℂ (complexEmbedding f) (complexEmbedding g)).re := by
  rw [L2.inner_def, L2.inner_def]
  have hi := integral_re (𝕜 := ℂ)
    (L2.integrable_inner (𝕜 := ℂ) (complexEmbedding f) (complexEmbedding g))
  change (∫ x, (inner ℂ (complexEmbedding f x) (complexEmbedding g x)).re) = _ at hi
  refine (integral_congr_ae ?_).trans hi
  filter_upwards [embedding_coe f, embedding_coe g] with x hf hg
  simp [hf, hg, RCLike.inner_apply]

lemma inverse_selfAdjoint : IsSelfAdjoint inverse := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℝ (inverse f) g = inner ℝ f (inverse g)
  rw [embedding_inner, embedding_inner, inverse_complexify, inverse_complexify]
  exact congrArg Complex.re (ContinuousSpectrum.inverse_selfAdjoint.isSymmetric _ _)

lemma inverse_no_eigenvalues (z : ℝ) (f : RealSpace) (h : inverse f = z • f) : f = 0 := by
  apply embedding_injective
  rw [map_zero]
  apply ContinuousSpectrum.inverse_no_eigenvalues (z : ℂ)
  rw [← inverse_complexify, h, map_smul]
  exact RCLike.real_smul_eq_coe_smul z (complexEmbedding f)

lemma real_norm_sq (f : RealSpace) : ‖f‖ ^ 2 = ∫ x, (f x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [pow_two]

lemma norm_complex_sum (f g : RealSpace) :
    ‖complexEmbedding f + Complex.I • complexEmbedding g‖ ^ 2 = ‖f‖ ^ 2 + ‖g‖ ^ 2 := by
  rw [l2_norm_sq, real_norm_sq, real_norm_sq,
    ← integral_add (Lp.memLp f).integrable_sq (Lp.memLp g).integrable_sq]
  apply integral_congr_ae
  filter_upwards [embedding_coe f, embedding_coe g,
    Lp.coeFn_add (complexEmbedding f) (Complex.I • complexEmbedding g),
    Lp.coeFn_smul Complex.I (complexEmbedding g)] with x hf hg ha hs
  rw [ha]
  simp only [Pi.add_apply]
  rw [hs]
  simp only [Pi.smul_apply, smul_eq_mul, hf, hg]
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring

lemma inverse_norm_eq_complex : ‖inverse‖ = ‖ContinuousSpectrum.inverse‖ := by
  apply le_antisymm
  · apply inverse.opNorm_le_bound (norm_nonneg _)
    intro f
    rw [← embedding_norm (inverse f), inverse_complexify, ← embedding_norm f]
    exact ContinuousSpectrum.inverse.le_opNorm _
  · apply ContinuousSpectrum.inverse.opNorm_le_bound (norm_nonneg _)
    intro f
    have hs : ‖f‖ ^ 2 = ‖physicalRealPart f‖ ^ 2 + ‖physicalImagPart f‖ ^ 2 := by
      conv_lhs => rw [decompose f]
      exact norm_complex_sum _ _
    have ht : ‖ContinuousSpectrum.inverse f‖ ^ 2 =
        ‖inverse (physicalRealPart f)‖ ^ 2 + ‖inverse (physicalImagPart f)‖ ^ 2 := by
      rw [inverse_decompose, norm_complex_sum]
    have hr := pow_le_pow_left₀ (norm_nonneg (inverse (physicalRealPart f)))
      (inverse.le_opNorm (physicalRealPart f)) 2
    have hi := pow_le_pow_left₀ (norm_nonneg (inverse (physicalImagPart f)))
      (inverse.le_opNorm (physicalImagPart f)) 2
    simp only [mul_pow] at hr hi
    nlinarith [norm_nonneg (ContinuousSpectrum.inverse f), norm_nonneg inverse,
      norm_nonneg f, mul_nonneg (norm_nonneg inverse) (norm_nonneg f)]

lemma inverse_norm : ‖inverse‖ = 1 := by
  rw [inverse_norm_eq_complex, ContinuousSpectrum.inverse_norm]

lemma inverse_not_compact : ¬ IsCompactOperator inverse := by
  intro hc
  apply ContinuousSpectrum.inverse_not_compact
  have hr := (hc.comp_clm physicalRealPart).clm_comp complexEmbedding
  have hi := ((hc.comp_clm physicalImagPart).clm_comp complexEmbedding).smul Complex.I
  have he : (ContinuousSpectrum.inverse : Space → Space) =
      (fun f => complexEmbedding (inverse (physicalRealPart f)) +
        Complex.I • complexEmbedding (inverse (physicalImagPart f))) :=
    funext inverse_decompose
  rw [he]
  exact hr.add hi

end RealVersion

/-- The real L² restriction, with exact real H² domain and natural complexification. -/
theorem real_continuous_spectrum_example :
    Specs.ExpandedFA.PartV.ContinuousSpectrum.RealResult := by
  exact ⟨inclusion, operator, inverse, RealVersion.inclusion, RealVersion.operator,
    RealVersion.inverse, domain_and_inverse, inverse_fourier, RealVersion.domain_and_inverse,
    RealVersion.inverse_fourier, RealVersion.compatibility, RealVersion.inverse_selfAdjoint, RealVersion.inverse_norm,
    inverse_spectrum, RealVersion.inverse_no_eigenvalues, RealVersion.inverse_not_compact⟩

end ExpandedFA.PartV.ContinuousSpectrum
