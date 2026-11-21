import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.PointSpectralMapping
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.SemigroupGrowthAndGenerator
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.TorusFourierBasis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Point spectral mapping for arbitrary complex Banach C₀ semigroups.
Exponential twisting reduces the weighted integral argument to the already
proved integrated-orbit generator identity. -/
noncomputable section
open Filter Topology MeasureTheory Set
open scoped NNReal Real

namespace ExpandedFA.Semigroups.PointSpectralMapping
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

local instance : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ ℂ X
local instance : IsScalarTower ℝ ℂ X := IsScalarTower.restrictScalars ℝ ℂ X

/-- Multiplication by an exponential preserves exactly the C₀ axioms. -/
def twist (T : C0Semigroup ℂ X) (μ : ℂ) : C0Semigroup ℂ X where
  operators t := Complex.exp (μ * (t : ℂ)) • T.operators t
  at_zero := by simp [T.at_zero]
  add_time t s := by
    ext x
    simp only [smul_apply, NNReal.coe_add, Complex.ofReal_add,
      mul_add, Complex.exp_add, ContinuousLinearMap.comp_apply, T.add_apply,
      map_smul, smul_smul]
    rw [mul_comm]
  strong_zero x := by
    have hc : Continuous (fun h : ℝ => Complex.exp (μ * (h.toNNReal : ℂ))) := by
      fun_prop
    simpa using (hc.tendsto 0 |>.mono_left nhdsWithin_le_nhds).smul (T.strong_zero x)

@[simp] theorem twist_apply (T : C0Semigroup ℂ X) (μ : ℂ) (t : ℝ≥0) (x : X) :
    (twist T μ).operators t x = Complex.exp (μ * (t : ℂ)) • T.operators t x := rfl

/-- The scalar factor in the twist has derivative μ at zero. -/
theorem exp_mul_hasDerivAt (μ : ℂ) (r : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (μ * s))
      (μ * Complex.exp (μ * r)) r := by
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one, mul_comm] using
    ((Complex.ofRealCLM.hasDerivAt (x := r)).const_mul μ).cexp

/-- Right generator limits transform by A ↦ A + μI. -/
theorem hasGeneratorLimit_twist (T : C0Semigroup ℂ X) (μ : ℂ) {x y : X}
    (h : HasGeneratorLimit T x y) :
    HasGeneratorLimit (twist T μ) x (y + μ • x) := by
  change Tendsto (fun h => differenceQuotient (twist T μ) h x) _ _
  have he := (exp_mul_hasDerivAt μ 0).tendsto_slope_zero_right
  have hc : Tendsto (fun h : ℝ => Complex.exp (μ * h)) (𝓝[>] 0) (𝓝 (1 : ℂ)) := by
    simpa using (exp_mul_hasDerivAt μ 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  change Tendsto (fun h => differenceQuotient T h x) _ _ at h
  have he' : Tendsto (fun h : ℝ => h⁻¹ • (Complex.exp (μ * h) - 1))
      (𝓝[>] 0) (𝓝 μ) := by
    simpa using he
  have H := (hc.smul h).add (he'.smul_const x)
  simp only [one_smul] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [(twist T μ).differenceQuotient_real, T.differenceQuotient_real]
  simp only [twist_apply, Real.coe_toNNReal _ (le_of_lt hr)]
  simp only [smul_assoc, smul_sub, sub_smul, one_smul,
    smul_comm (Complex.exp (μ * r)) (r⁻¹ : ℝ)]
  abel

/-- Fourier uniqueness extends to arbitrary complex Banach spaces by testing
with a continuous complex-linear functional that detects the initial value. -/
theorem exists_nonzero_fourierCoeff {τ : ℝ} [Fact (0 < τ)]
    (f : C(AddCircle τ, X)) (hx : f 0 ≠ 0) :
    ∃ n : ℤ, fourierCoeff f n ≠ 0 := by
  classical
  by_contra! h
  obtain ⟨L, _, hL⟩ := exists_dual_vector ℂ (f 0) (norm_ne_zero_iff.mpr hx)
  let g : C(AddCircle τ, ℂ) := ⟨fun s => L (f s), L.continuous.comp f.continuous⟩
  have hg (n : ℤ) : fourierCoeff g n = fourierCoeff (0 : C(AddCircle τ, ℂ)) n := by
    have hi := (f.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).fourier_smul (-n)
    change (∫ s, fourier (-n) s • L (f s) ∂AddCircle.haarAddCircle) = _
    simp_rw [← L.map_smul]
    rw [L.integral_comp_comm hi]
    change L (fourierCoeff f n) = _
    rw [h n]
    simp [fourierCoeff]
  have heq := Fourier.TorusFourierBasis.continuous_unique τ g 0 hg
  have hz : L (f 0) = 0 := congrArg (fun k : C(AddCircle τ, ℂ) => k 0) heq
  rw [hL] at hz
  exact hx (norm_eq_zero.mp (Complex.ofReal_eq_zero.mp hz))

@[simp] theorem twist_neg_twist_apply (T : C0Semigroup ℂ X) (μ : ℂ)
    (t : ℝ≥0) (x : X) : (twist (twist T μ) (-μ)).operators t x = T.operators t x := by
  rw [twist_apply, twist_apply, smul_smul, ← Complex.exp_add]
  simp

/-- Undoing an exponential twist also recovers the exact generator limit. -/
theorem hasGeneratorLimit_untwist (T : C0Semigroup ℂ X) (μ : ℂ) {x y : X}
    (h : HasGeneratorLimit (twist T μ) x y) :
    HasGeneratorLimit T x (y - μ • x) := by
  have H := hasGeneratorLimit_twist (twist T μ) (-μ) h
  change Tendsto (fun h => differenceQuotient (twist (twist T μ) (-μ)) h x) _ _ at H
  change Tendsto (fun h => differenceQuotient T h x) _ _
  simp only [neg_smul, ← sub_eq_add_neg] at H
  apply H.congr'
  filter_upwards [] with r
  rw [(twist (twist T μ) (-μ)).differenceQuotient_real,
    T.differenceQuotient_real, twist_neg_twist_apply]

/-- A generator eigenvector evolves by the corresponding scalar exponential,
without any uniqueness assumption on vectors outside the generator domain. -/
theorem eigenvector_orbit (T : C0Semigroup ℂ X) (ζ : ℂ)
    (x : (generator T).domain) (hx : generator T x = ζ • (x : X)) (t : ℝ≥0) :
    T.operators t x = Complex.exp ((t : ℂ) * ζ) • (x : X) := by
  have h : HasGeneratorLimit (twist T (-ζ)) x (generator T x + (-ζ) • (x : X)) :=
    hasGeneratorLimit_twist T (-ζ) (generator_has_limit T x)
  rw [hx, neg_smul, add_neg_cancel] at h
  let S := twist T (-ζ)
  have hd : (x : X) ∈ (generator S).domain := ⟨0, h⟩
  have hz : generator S ⟨x, hd⟩ = 0 :=
    generator_limit_unique S _ _ _ (generator_has_limit S ⟨x, hd⟩) h
  have heq := S.orbit_integral_identity ⟨x, hd⟩ t
  simp only [hz, map_zero, intervalIntegral.integral_zero] at heq
  have hh : Complex.exp (-ζ * (t : ℂ)) • T.operators t x = (x : X) :=
    sub_eq_zero.mp heq
  calc
    T.operators t x = Complex.exp (ζ * (t : ℂ)) •
        (Complex.exp (-ζ * (t : ℂ)) • T.operators t x) := by
      rw [smul_smul, ← Complex.exp_add]
      simp
    _ = Complex.exp (ζ * (t : ℂ)) • (x : X) := by rw [hh]
    _ = _ := by rw [mul_comm]

/-- The k-th angular frequency for a positive period τ. -/
def frequency (τ : ℝ) (n : ℤ) : ℂ := 2 * π * Complex.I * n / τ

theorem exp_frequency_period {τ : ℝ} (hτ : τ ≠ 0) (n : ℤ) :
    Complex.exp (frequency τ n * τ) = 1 := by
  rw [frequency, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hτ)]
  rw [mul_comm]
  exact Complex.exp_int_mul_two_pi_mul_I n

/-- A nonzero fixed vector of a positive-time operator supplies a nonzero
Fourier coefficient; that coefficient is a generator eigenvector. -/
theorem fixed_vector_eigenvalue (T : C0Semigroup ℂ X) (t : ℝ≥0) (ht : 0 < t)
    (x : X) (hx : x ≠ 0) (hfix : T.operators t x = x) :
    ∃ (n : ℤ) (y : X), y ≠ 0 ∧ HasGeneratorLimit T y (frequency t n • y) := by
  haveI : Fact (0 < (t : ℝ)) := ⟨ht⟩
  let f : C(AddCircle (t : ℝ), X) :=
    ⟨AddCircle.liftIco (t : ℝ) 0 (fun s : ℝ => T.operators s.toNNReal x),
      AddCircle.liftIco_zero_continuous (by simpa using hfix.symm)
        (T.continuous_real_orbit x).continuousOn⟩
  have hf0 : f 0 = x := by
    change AddCircle.liftIco (t : ℝ) 0 (fun s : ℝ => T.operators s.toNNReal x)
      (0 : AddCircle (t : ℝ)) = x
    rw [← AddCircle.coe_zero, AddCircle.liftIco_zero_coe_apply ⟨le_rfl, ht⟩]
    simp
  obtain ⟨n, hn⟩ := exists_nonzero_fourierCoeff f (by rwa [hf0])
  let S := twist T (-frequency t n)
  let y := S.integratedOperator t x
  have hc : fourierCoeff f n = (1 / (t : ℝ)) • y := by
    rw [fourierCoeff_eq_intervalIntegral f n 0, zero_add]
    congr 1
    change (∫ s in (0 : ℝ)..(t : ℝ), fourier (-n) (s : AddCircle (t : ℝ)) • f s) =
      ∫ s in (0 : ℝ)..(t : ℝ), S.operators s.toNNReal x
    apply intervalIntegral.integral_congr_Ioo_of_le t.coe_nonneg
    intro s hs
    have hf : f (s : AddCircle (t : ℝ)) = T.operators s.toNNReal x :=
      AddCircle.liftIco_zero_coe_apply (f := fun s : ℝ => T.operators s.toNNReal x)
        ⟨hs.1.le, hs.2⟩
    change fourier (-n) (s : AddCircle (t : ℝ)) • f (s : AddCircle (t : ℝ)) =
      S.operators s.toNNReal x
    rw [hf, fourier_coe_apply]
    change Complex.exp (2 * π * Complex.I * (-n : ℤ) * s / (t : ℝ)) •
      T.operators s.toNNReal x =
      Complex.exp (-frequency t n * (s.toNNReal : ℂ)) • T.operators s.toNNReal x
    rw [Real.coe_toNNReal s hs.1.le]
    congr 2
    push_cast
    simp only [frequency]
    ring
  have hy : y ≠ 0 := by
    intro hz
    apply hn
    rw [hc, hz, smul_zero]
  have hSfix : S.operators t x = x := by
    change Complex.exp (-frequency t n * (t : ℂ)) • T.operators t x = x
    rw [hfix, neg_mul, Complex.exp_neg,
      exp_frequency_period (show (t : ℝ) ≠ 0 from ne_of_gt ht)]
    simp
  have hS : HasGeneratorLimit S y 0 := by
    simpa only [hSfix, sub_self] using S.integratedOperator_hasGeneratorLimit t x
  have hT := hasGeneratorLimit_untwist T (-frequency t n) hS
  refine ⟨n, y, hy, ?_⟩
  simpa using hT

/-- Every nonzero eigenvalue at positive time lifts to a genuine eigenvalue
of the generator, possibly with a different eigenvector. -/
theorem time_eigenvalue_lifts (T : C0Semigroup ℂ X) (t : ℝ≥0) (ht : 0 < t)
    (z : ℂ) (hz : z ≠ 0) (x : X) (hx : x ≠ 0) (hTx : T.operators t x = z • x) :
    ∃ ζ : ℂ, Complex.exp ((t : ℂ) * ζ) = z ∧
      ∃ y : (generator T).domain, (y : X) ≠ 0 ∧ generator T y = ζ • (y : X) := by
  have htR : (t : ℝ) ≠ 0 := ne_of_gt ht
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr htR
  let α : ℂ := Complex.log z / (t : ℂ)
  have hα : Complex.exp (α * (t : ℂ)) = z := by
    dsimp only [α]
    rw [div_mul_cancel₀ _ htC, Complex.exp_log hz]
  let S := twist T (-α)
  have hfix : S.operators t x = x := by
    change Complex.exp (-α * (t : ℂ)) • T.operators t x = x
    rw [hTx, smul_smul, neg_mul, Complex.exp_neg, hα, inv_mul_cancel₀ hz, one_smul]
  obtain ⟨n, y, hy, hSy⟩ := fixed_vector_eigenvalue S t ht x hx hfix
  have hTy : HasGeneratorLimit T y ((frequency t n + α) • y) := by
    have H := hasGeneratorLimit_untwist T (-α) hSy
    simpa only [neg_smul, sub_neg_eq_add, ← add_smul] using H
  have hd : y ∈ (generator T).domain := ⟨_, hTy⟩
  refine ⟨frequency t n + α, ?_, ⟨y, hd⟩, hy, ?_⟩
  · rw [mul_add, Complex.exp_add, mul_comm (t : ℂ) (frequency t n),
      exp_frequency_period htR, one_mul, mul_comm, hα]
  · exact generator_limit_unique T _ _ _ (generator_has_limit T ⟨y, hd⟩) hTy

/-- Point spectral mapping with both inclusions, for every positive time on
every complex Banach space, including the zero space. -/
theorem point_spectral_mapping : PointSpectralMappingSpec.PointSpectralMapping := by
  intro X _ _ _ T t ht
  ext z
  constructor
  · rintro ⟨⟨x, hx, hTx⟩, hz⟩
    have hz' : z ≠ 0 := by simpa using hz
    obtain ⟨ζ, hζ, y, hy, hAy⟩ := time_eigenvalue_lifts T t ht z hz' x hx hTx
    exact ⟨ζ, ⟨y, hy, hAy⟩, hζ⟩
  · rintro ⟨ζ, ⟨x, hx, hAx⟩, rfl⟩
    refine ⟨⟨x, hx, eigenvector_orbit T ζ x hAx t⟩, ?_⟩
    simp

end ExpandedFA.Semigroups.PointSpectralMapping
