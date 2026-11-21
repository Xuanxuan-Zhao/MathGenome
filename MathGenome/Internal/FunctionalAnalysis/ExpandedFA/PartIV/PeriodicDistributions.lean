import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.PeriodicDistributions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.PeriodicDistributionInterface
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Tactic.LinearCombination

open Set Filter Function MeasureTheory Topology
open scoped Topology ContDiff NNReal

namespace ExpandedFA.PartIV.Periodic
open ExpandedFA.Distributions

variable {d : ℕ}

@[simp] theorem character_apply (n : Lattice d) (q : Torus d) :
    (character n).val q = UnitAddTorus.mFourier n q := rfl

/-- The Euclidean frequency length is nonnegative, also on the zero lattice. -/
theorem frequencyNorm_nonneg (n : Lattice d) : 0 ≤ frequencyNorm n := norm_nonneg _

/-- Finite order follows from continuity for the actual smooth Fréchet topology. -/
theorem distribution_finite_order (U : TorusDistribution ℂ d) :
    ∃ (C : ℝ≥0) (N : ℕ), ∀ φ : Smooth ℂ d,
      ‖U φ‖ ≤ C * smoothPartialSeminorm ℂ d N φ := by
  classical
  let q : Seminorm ℂ (Smooth ℂ d) := (normSeminorm ℂ ℂ).comp U.toLinearMap
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous (smooth_partial_topology ℂ d)
    q (continuous_norm.comp U.continuous)
  refine ⟨C, s.sup id, fun φ => (hC φ).trans ?_⟩
  change C * (s.sup (smoothPartialSeminorm ℂ d)) φ ≤ _
  gcongr
  apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
  intro m hm
  unfold smoothPartialSeminorm
  apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
  intro k hk
  apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
  intro a _
  apply coordinateJet_le_partial a
  exact (Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans (Finset.le_sup (f := id) hm)

/-- The linear phase in the Euclidean lift of a torus character. -/
noncomputable def phase (n : Lattice d) : Domain d →L[ℝ] ℂ :=
  ∑ i, (2 * (Real.pi : ℂ) * Complex.I * (n i : ℂ)) •
    (Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))

@[simp] theorem phase_apply (n : Lattice d) (x : Domain d) :
    phase n x = ∑ i, 2 * (Real.pi : ℂ) * Complex.I * (n i : ℂ) * (x i : ℂ) := by
  simp [phase, smul_eq_mul]

/-- This identity fixes both the sign and the 2π normalization. -/
theorem lift_character (n : Lattice d) :
    lift (character n) = fun x => Complex.exp (phase n x) := by
  funext x
  simp only [lift, character_apply, UnitAddTorus.mFourier, ContinuousMap.coe_mk, quotient,
    fourier_coe_apply, Complex.ofReal_one, div_one, phase_apply]
  exact (Complex.exp_sum _ _).symm

/-- Tensor power of a scalar-valued real-linear map. -/
noncomputable def phaseTensor (L : Domain d →L[ℝ] ℂ) (m : ℕ) :
    (Domain d) [×m]→L[ℝ] ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ m ℂ).compContinuousLinearMap (fun _ => L)

@[simp] theorem phaseTensor_apply (L : Domain d →L[ℝ] ℂ) (m : ℕ)
    (v : Fin m → Domain d) : phaseTensor L m v = ∏ j, L (v j) := by
  simp [phaseTensor, ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.prod_ofFn]

/-- All derivatives of an exponential of a linear phase. -/
theorem iteratedFDeriv_exp_linear (L : Domain d →L[ℝ] ℂ) (m : ℕ) :
    iteratedFDeriv ℝ m (fun x => Complex.exp (L x)) =
      fun x => Complex.exp (L x) • phaseTensor L m := by
  induction m with
  | zero =>
    funext x
    ext v
    simp
  | succ m ih =>
    funext x
    ext v
    rw [iteratedFDeriv_succ_apply_left, ih]
    rw [((L.hasFDerivAt.cexp).smul_const (phaseTensor L m)).fderiv]
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply, phaseTensor_apply, smul_eq_mul]
    rw [Fin.prod_univ_succ]
    simp only [Fin.tail_def]
    ring

@[simp] theorem norm_character (n : Lattice d) (q : Torus d) :
    ‖(character n).val q‖ = 1 := by
  simp [character_apply, UnitAddTorus.mFourier, fourier_apply, norm_prod]

@[simp] theorem phase_coordinate (n : Lattice d) (i : Fin d) :
    phase n (coordinateVector i) = 2 * (Real.pi : ℂ) * Complex.I * (n i : ℂ) := by
  classical
  simp [phase_apply, coordinateVector, Pi.single_apply, apply_ite Complex.ofReal, mul_ite]

/-- A coordinate frequency is bounded by the Euclidean lattice length. -/
theorem norm_frequency_coordinate_le (n : Lattice d) (i : Fin d) :
    ‖(n i : ℝ)‖ ≤ frequencyNorm n :=
  PiLp.norm_apply_le (WithLp.toLp 2 (integerVector n) : EuclideanSpace ℝ (Fin d)) i

@[simp] theorem norm_phase_coordinate (n : Lattice d) (i : Fin d) :
    ‖phase n (coordinateVector i)‖ = (2 * Real.pi) * ‖(n i : ℝ)‖ := by
  rw [phase_coordinate]
  simp [← Complex.ofReal_intCast, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]

/-- Uniform control of every coordinate partial of a character. -/
theorem character_partial_bound (n : Lattice d) (m : ℕ) :
    smoothPartialSeminorm ℂ d m (character n) ≤
      ((1 + 2 * Real.pi) * (1 + frequencyNorm n)) ^ m := by
  let B := (1 + 2 * Real.pi) * (1 + frequencyNorm n)
  have hB : 1 ≤ B := by
    dsimp [B]
    nlinarith [Real.pi_pos, frequencyNorm_nonneg n]
  apply (smooth_partial_formula ℂ d m (character n) _ (by positivity)).mpr
  intro k hk a x _
  rw [lift_character, iteratedFDeriv_exp_linear]
  simp only [smul_apply, phaseTensor_apply, smul_eq_mul, norm_mul]
  have hexp : ‖Complex.exp (phase n x)‖ = 1 := by
    rw [← congrFun (lift_character n) x]
    exact norm_character n (quotient x)
  rw [hexp, one_mul, norm_prod]
  calc
    _ ≤ ∏ _j : Fin k, B := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro j _
      rw [norm_phase_coordinate]
      have hcoord := norm_frequency_coordinate_le n (a j)
      have hmul := mul_le_mul_of_nonneg_left hcoord
        (by positivity : 0 ≤ 2 * Real.pi)
      simp only [Real.norm_eq_abs] at hmul
      have hnorm := frequencyNorm_nonneg n
      dsimp [B]
      nlinarith [Real.pi_pos]
    _ = B ^ k := by simp
    _ ≤ B ^ m := pow_le_pow_right₀ hB hk

@[simp] theorem frequencyNorm_neg (n : Lattice d) : frequencyNorm (-n) = frequencyNorm n := by
  unfold frequencyNorm
  rw [integerVector_neg, WithLp.toLp_neg, norm_neg]

/-- Every continuous complex-linear torus distribution has polynomial-growth
Fourier coefficients, with no prescribed cap on the degree. -/
theorem polynomial_growth :
    Specs.ExpandedFA.PartIV.PeriodicDistributions.polynomialGrowthType := by
  intro d U
  obtain ⟨C, N, hC⟩ := distribution_finite_order U
  refine ⟨C * (1 + 2 * Real.pi) ^ N, by positivity, N, fun n => ?_⟩
  calc
    ‖distributionCoeff U n‖ ≤ C * smoothPartialSeminorm ℂ d N (character (-n)) := hC _
    _ ≤ C * (((1 + 2 * Real.pi) * (1 + frequencyNorm (-n))) ^ N) :=
      mul_le_mul_of_nonneg_left (character_partial_bound (-n) N) C.coe_nonneg
    _ = _ := by rw [frequencyNorm_neg, mul_pow]; ring

/-- Smooth quotient functions are continuous for the genuine quotient topology. -/
theorem continuous_smooth (φ : Smooth ℂ d) : Continuous φ.val := by
  have hq : IsQuotientMap (@quotient d) :=
    (IsOpenQuotientMap.piMap fun _ : Fin d =>
      (QuotientAddGroup.isOpenQuotientMap_mk :
        IsOpenQuotientMap (QuotientAddGroup.mk : ℝ → UnitAddCircle))).isQuotientMap
  exact hq.continuous_iff.mpr (contDiff_lift φ).continuous

instance torusHaarProbability (d : ℕ) : IsProbabilityMeasure (torusHaar d) := by
  unfold torusHaar
  infer_instance

/-- Point evaluations are bounded by the zeroth smooth seminorm. -/
theorem norm_smooth_apply_le (φ : Smooth ℂ d) (q : Torus d) :
    ‖φ.val q‖ ≤ smoothPartialSeminorm ℂ d 0 φ := by
  have h := (smooth_partial_formula ℂ d 0 φ _ (apply_nonneg _ _)).mp le_rfl
    0 le_rfl (fun i => Fin.elim0 i) (representative q) (representative_mem_cube q)
  simpa only [iteratedFDeriv_zero_apply, lift, quotient_representative] using h

/-- No measurability assumption on a smooth test is left implicit. -/
theorem integrable_fourier_test (φ : Smooth ℂ d) (n : Lattice d) :
    Integrable (fun x => UnitAddTorus.mFourier (-n) x * φ.val x) (torusHaar d) :=
  ((UnitAddTorus.mFourier (-n)).continuous.mul (continuous_smooth φ)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Each ordinary Fourier coefficient is bounded by the uniform norm. -/
theorem norm_testFourierCoeff_le (φ : Smooth ℂ d) (n : Lattice d) :
    ‖testFourierCoeff φ n‖ ≤ smoothPartialSeminorm ℂ d 0 φ := by
  have h := norm_integral_le_of_norm_le_const (μ := torusHaar d)
    (f := fun x => UnitAddTorus.mFourier (-n) x * φ.val x)
    (C := smoothPartialSeminorm ℂ d 0 φ)
    (Filter.Eventually.of_forall fun q => ?_)
  · simpa only [testFourierCoeff, probReal_univ, mul_one] using h
  · rw [norm_mul, show ‖UnitAddTorus.mFourier (-n) q‖ = 1 from norm_character (-n) q, one_mul]
    exact norm_smooth_apply_le φ q

/-- Fourier coefficient extraction is complex linear. -/
noncomputable def testFourierCoeffLM (n : Lattice d) : Smooth ℂ d →ₗ[ℂ] ℂ where
  toFun φ := testFourierCoeff φ n
  map_add' φ ψ := by
    change (∫ x, UnitAddTorus.mFourier (-n) x * (φ.val x + ψ.val x) ∂torusHaar d) = _
    simp_rw [mul_add]
    exact integral_add (integrable_fourier_test φ n) (integrable_fourier_test ψ n)
  map_smul' c φ := by
    change (∫ x, UnitAddTorus.mFourier (-n) x * (c * φ.val x) ∂torusHaar d) = _
    simp_rw [mul_left_comm (UnitAddTorus.mFourier (-n) _) c]
    exact integral_const_mul c _

/-- Continuity is for the full smooth topology, not a sequential surrogate. -/
noncomputable def testFourierCoeffCLM (n : Lattice d) : TorusDistribution ℂ d :=
  ⟨testFourierCoeffLM n, by
    apply WithSeminorms.continuous_normedSpace_rng ℂ (smooth_partial_topology ℂ d)
    refine ⟨{0}, 1, ?_⟩
    intro φ
    change ‖testFourierCoeff φ n‖ ≤ _
    simpa only [Finset.sup_singleton, one_smul] using norm_testFourierCoeff_le φ n⟩

/-- Every finite Fourier sum is an actual continuous complex-linear distribution. -/
noncomputable def finiteFourierDistribution (c : Lattice d → ℂ) (s : Finset (Lattice d)) :
    TorusDistribution ℂ d := ∑ n ∈ s, c n • testFourierCoeffCLM (-n)

@[simp] theorem finiteFourierDistribution_apply (c : Lattice d → ℂ)
    (s : Finset (Lattice d)) (φ : Smooth ℂ d) :
    finiteFourierDistribution c s φ = finiteFourierPairing c s φ := by
  simp [finiteFourierDistribution, finiteFourierPairing, testFourierCoeffCLM,
    testFourierCoeffLM, smul_eq_mul]

@[simp] theorem testFourierCoeffCLM_apply (n : Lattice d) (φ : Smooth ℂ d) :
    testFourierCoeffCLM n φ = testFourierCoeff φ n := rfl

/-- Orthogonality has precisely the ordinary (nonconjugated) coefficient convention. -/
theorem testFourierCoeff_character (m n : Lattice d) :
    testFourierCoeff (character m) n = if n = m then 1 else 0 := by
  classical
  have h := (orthonormal_iff_ite.mp
    (UnitAddTorus.orthonormal_mFourier (d := Fin d))) n m
  simp only [UnitAddTorus.mFourierLp, ContinuousMap.inner_toLp,
    ← UnitAddTorus.mFourier_neg, volume_pi, MeasureSpace.volume] at h
  simpa only [testFourierCoeff, torusHaar, character_apply, mul_comm] using h

/-- Once absolute convergence and a uniform smooth seminorm bound are supplied,
the Fourier pairing is a continuous complex-linear functional. -/
noncomputable def distributionOfSummable (c : Lattice d → ℂ)
    (hsum : ∀ φ : Smooth ℂ d, Summable (fun n => c n * testFourierCoeff φ (-n)))
    (A : ℝ≥0) (m : ℕ)
    (hbound : ∀ φ : Smooth ℂ d,
      ‖∑' n, c n * testFourierCoeff φ (-n)‖ ≤ A * smoothPartialSeminorm ℂ d m φ) :
    TorusDistribution ℂ d :=
  ⟨{ toFun := fun φ => ∑' n, c n * testFourierCoeff φ (-n)
     map_add' := by
       intro φ ψ
       change (∑' n, c n * testFourierCoeffCLM (-n) (φ + ψ)) = _
       simp only [map_add, mul_add]
       exact (hsum φ).tsum_add (hsum ψ)
     map_smul' := by
       intro a φ
       change (∑' n, c n * testFourierCoeffCLM (-n) (a • φ)) = _
       simp only [map_smul, smul_eq_mul, mul_left_comm (c _) a]
       exact tsum_mul_left }, by
    apply WithSeminorms.continuous_normedSpace_rng ℂ (smooth_partial_topology ℂ d)
    refine ⟨{m}, A, ?_⟩
    intro φ
    change ‖∑' n, c n * testFourierCoeff φ (-n)‖ ≤ _
    simpa only [Finset.sup_singleton, smul_apply, NNReal.smul_def, smul_eq_mul] using hbound φ⟩

@[simp] theorem distributionOfSummable_apply (c : Lattice d → ℂ)
    (hsum : ∀ φ : Smooth ℂ d, Summable (fun n => c n * testFourierCoeff φ (-n)))
    (A : ℝ≥0) (m : ℕ)
    (hbound : ∀ φ : Smooth ℂ d,
      ‖∑' n, c n * testFourierCoeff φ (-n)‖ ≤ A * smoothPartialSeminorm ℂ d m φ)
    (φ : Smooth ℂ d) :
    distributionOfSummable c hsum A m hbound φ =
      ∑' n, c n * testFourierCoeff φ (-n) := rfl

/-- Coefficient recovery is unconditional once the summable functional is built. -/
theorem distributionOfSummable_coeff (c : Lattice d → ℂ)
    (hsum : ∀ φ : Smooth ℂ d, Summable (fun n => c n * testFourierCoeff φ (-n)))
    (A : ℝ≥0) (m : ℕ)
    (hbound : ∀ φ : Smooth ℂ d,
      ‖∑' n, c n * testFourierCoeff φ (-n)‖ ≤ A * smoothPartialSeminorm ℂ d m φ)
    (n : Lattice d) :
    distributionCoeff (distributionOfSummable c hsum A m hbound) n = c n := by
  classical
  simp [distributionCoeff, testFourierCoeff_character]

/-- The finite Fourier distributions converge on every test when the absolute
pairing and seminorm estimate have been established. -/
theorem finite_sums_tendsto_of_bound (c : Lattice d → ℂ)
    (hsum : ∀ φ : Smooth ℂ d, Summable (fun n => c n * testFourierCoeff φ (-n)))
    (A : ℝ≥0) (m : ℕ)
    (hbound : ∀ φ : Smooth ℂ d,
      ‖∑' n, c n * testFourierCoeff φ (-n)‖ ≤ A * smoothPartialSeminorm ℂ d m φ)
    (φ : Smooth ℂ d) :
    Tendsto (fun s : Finset (Lattice d) => finiteFourierDistribution c s φ) atTop
      (𝓝 (distributionOfSummable c hsum A m hbound φ)) := by
  simp only [finiteFourierDistribution_apply, finiteFourierPairing,
    distributionOfSummable_apply]
  change HasSum (fun n => c n * testFourierCoeff φ (-n)) _
  exact (hsum φ).hasSum

/-- Smooth Fourier convergence implies uniqueness, with the exact sign in the
source pairing, using convergence in the full smooth topology. -/
theorem uniqueness_of_smooth_expansion
    (hexp : ∀ φ : Smooth ℂ d,
      HasSum (fun n => testFourierCoeff φ (-n) • character (-n)) φ)
    (U V : TorusDistribution ℂ d)
    (h : distributionCoeff U = distributionCoeff V) : U = V := by
  apply ContinuousLinearMap.ext
  intro φ
  apply HasSum.unique (U.hasSum (hexp φ))
  convert V.hasSum (hexp φ) using 1
  ext n
  simp only [map_smul, smul_eq_mul]
  exact congrArg (testFourierCoeff φ (-n) * ·) (congrFun h n)

/-- Point evaluation as a continuous linear functional on the smooth topology. -/
noncomputable def smoothEvalCLM (q : Torus d) : TorusDistribution ℂ d :=
  ⟨{ toFun := fun φ => φ.val q
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl }, by
    apply WithSeminorms.continuous_normedSpace_rng ℂ (smooth_partial_topology ℂ d)
    refine ⟨{0}, 1, ?_⟩
    intro φ
    change ‖φ.val q‖ ≤ _
    simpa only [Finset.sup_singleton, one_smul] using norm_smooth_apply_le φ q⟩

/-- Match Mathlib's normalized product-Haar coefficient exactly. -/
theorem testFourierCoeff_eq_native (φ : Smooth ℂ d) (n : Lattice d) :
    testFourierCoeff φ n = UnitAddTorus.mFourierCoeff φ.val n := by
  simp only [testFourierCoeff, UnitAddTorus.mFourierCoeff, torusHaar,
    smul_eq_mul, MeasureSpace.volume]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Weighted absolute summability implies convergence in the original smooth
Fréchet topology, using its complete jet embedding. -/
theorem smooth_expansion_of_weighted
    (hw : ∀ (φ : Smooth ℂ d) (N : ℕ),
      Summable (fun n => (1 + frequencyNorm n) ^ N * ‖testFourierCoeff φ n‖))
    (φ : Smooth ℂ d) :
    HasSum (fun n => testFourierCoeff φ (-n) • character (-n)) φ := by
  let f : Lattice d → Smooth ℂ d := fun n => testFourierCoeff φ (-n) • character (-n)
  have hj (k : ℕ) : Summable (fun n => jetLM ℂ d k (f n)) := by
    have hneg := (hw φ k).comp_injective (neg_injective (G := Lattice d))
    refine Summable.of_norm_bounded
      (E := C(cube d, (Domain d) [×k]→L[ℝ] ℂ))
      (g := fun n : Lattice d => ((d : ℝ) ^ k * (1 + 2 * Real.pi) ^ k) *
        ((1 + frequencyNorm (-n)) ^ k * ‖testFourierCoeff φ (-n)‖))
      (hneg.mul_left ((d : ℝ) ^ k * (1 + 2 * Real.pi) ^ k)) ?_
    intro n
    change ‖jetLM ℂ d k (testFourierCoeff φ (-n) • character (-n))‖ ≤ _
    rw [map_smul]
    refine (norm_smul_le (testFourierCoeff φ (-n))
      (jetLM ℂ d k (character (-n)))).trans ?_
    change ‖testFourierCoeff φ (-n)‖ * derivativeSeminorm ℂ d k (character (-n)) ≤ _
    have hderiv := derivativeSeminorm_le_partial (𝕜 := ℂ) (d := d) k (character (-n))
    have hpartial := character_partial_bound (-n) k
    change derivativeSeminorm ℂ d k (character (-n)) ≤
      ((d : ℝ) ^ k) * smoothPartialSeminorm ℂ d k (character (-n)) at hderiv
    have hbound := hderiv.trans (mul_le_mul_of_nonneg_left hpartial (by positivity))
    have h := mul_le_mul_of_nonneg_left hbound (norm_nonneg (testFourierCoeff φ (-n)))
    simp only [mul_pow] at h
    convert h using 1; ring
  have hs : Summable f := by
    rw [summable_iff_cauchySeq_finset]
    apply (isUniformEmbedding_jets (𝕜 := ℂ) (d := d)).toIsUniformInducing.cauchy_map_iff.mp
    apply (cauchy_pi_iff _).mpr
    intro k
    have h := (summable_iff_cauchySeq_finset
      (α := C(cube d, (Domain d) [×k]→L[ℝ] ℂ))).mp (hj k)
    simpa only [CauchySeq, Filter.map_map, Function.comp_def, map_sum] using h
  have hcoeff : Summable (UnitAddTorus.mFourierCoeff φ.val) := by
    apply Summable.of_norm
    simpa only [pow_zero, one_mul, testFourierCoeff_eq_native] using hw φ 0
  have hpoint (q : Torus d) : HasSum (fun n => testFourierCoeff φ (-n) *
      (character (-n)).val q) (φ.val q) := by
    have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
      (f := ⟨φ.val, continuous_smooth φ⟩) hcoeff q
    have hn := (Equiv.neg (Lattice d)).hasSum_iff.mpr h
    simpa only [Function.comp_def, Equiv.neg_apply, testFourierCoeff_eq_native,
      character_apply, smul_eq_mul, ContinuousMap.coe_mk] using hn
  have heq : ∑' n, f n = φ := by
    apply Subtype.ext
    funext q
    apply HasSum.unique
      ((smoothEvalCLM q).hasSum hs.hasSum)
    convert hpoint q using 1
    ext n
    rfl
  change HasSum f φ
  convert hs.hasSum using 1
  exact heq.symm

/-- The uniform weighted Fourier estimate suffices for every polynomial-growth
pairing, with all growth degrees and Euclidean dimensions retained. -/
theorem pairing_estimate_of_weighted
    (hw : Specs.ExpandedFA.PartIV.PeriodicDistributions.weightedEstimateType)
    (c : Lattice d → ℂ) (hc : PolynomialGrowth c) :
    ∃ (A : ℝ≥0) (L : ℕ), ∀ φ : Smooth ℂ d,
      Summable (fun n => ‖c n * testFourierCoeff φ (-n)‖) ∧
      ‖∑' n, c n * testFourierCoeff φ (-n)‖ ≤ A * smoothPartialSeminorm ℂ d L φ := by
  obtain ⟨C, hC, N, hcn⟩ := hc
  obtain ⟨A, L, hwc⟩ := hw d N
  let C0 : NNReal := ⟨C, hC⟩
  refine ⟨C0 * A, L, fun φ => ?_⟩
  let w : Lattice d → ℝ := fun n => (1 + frequencyNorm n) ^ N * ‖testFourierCoeff φ n‖
  have hw0 : Summable w := (hwc φ).1
  have hwneg : Summable (fun n : Lattice d => w (-n)) :=
    hw0.comp_injective (neg_injective (G := Lattice d))
  have hdom (n : Lattice d) : ‖c n * testFourierCoeff φ (-n)‖ ≤ C * w (-n) := by
    rw [norm_mul]
    dsimp [w]
    rw [frequencyNorm_neg]
    calc
      _ ≤ (C * (1 + frequencyNorm n) ^ N) * ‖testFourierCoeff φ (-n)‖ :=
        mul_le_mul_of_nonneg_right (hcn n) (norm_nonneg _)
      _ = _ := by ring
  have ha : Summable (fun n => ‖c n * testFourierCoeff φ (-n)‖) :=
    (hwneg.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _) hdom
  refine ⟨ha, (norm_tsum_le_tsum_norm ha).trans ?_⟩
  calc
    _ ≤ ∑' n, C * w (-n) := ha.tsum_le_tsum hdom (hwneg.mul_left C)
    _ = C * ∑' n, w n := by
      rw [tsum_mul_left]
      exact congrArg (C * ·) ((Equiv.neg (Lattice d)).tsum_eq w)
    _ ≤ C * (A * smoothPartialSeminorm ℂ d L φ) := mul_le_mul_of_nonneg_left (hwc φ).2 hC
    _ = _ := by
      rw [NNReal.coe_mul]
      change C * ((A : ℝ) * smoothPartialSeminorm ℂ d L φ) =
        (C * (A : ℝ)) * smoothPartialSeminorm ℂ d L φ
      ring

/-- The finite sums part already has actual continuous distributions, without
a polynomial-growth assumption. -/
theorem finite_distribution_exists :
    Specs.ExpandedFA.PartIV.PeriodicDistributions.finiteDistributionExistsType := by
  intro d c s
  exact ⟨finiteFourierDistribution c s, finiteFourierDistribution_apply c s⟩

/-- Assembly of the converse from the uniform weighted estimate. -/
theorem converse_of_weighted_estimate
    (hw : Specs.ExpandedFA.PartIV.PeriodicDistributions.weightedEstimateType) :
    Specs.ExpandedFA.PartIV.PeriodicDistributions.converseType := by
  intro d c hc
  obtain ⟨A, L, he⟩ := pairing_estimate_of_weighted hw c hc
  let hs := fun φ => Summable.of_norm (he φ).1
  let hb := fun φ => (he φ).2
  let U := distributionOfSummable c hs A L hb
  refine ⟨U, ⟨fun n => distributionOfSummable_coeff c hs A L hb n,
    fun φ => ⟨(he φ).1, (hs φ).hasSum⟩⟩, ?_⟩
  intro V hV
  apply ContinuousLinearMap.ext
  intro φ
  exact (hV.2 φ).2.unique (hs φ).hasSum

/-- Applying a continuous functional to the smooth Fourier series gives exactly
the source's reconstruction formula from the weighted estimate. -/
theorem reconstruction_of_weighted_estimate
    (hw : Specs.ExpandedFA.PartIV.PeriodicDistributions.weightedEstimateType) :
    Specs.ExpandedFA.PartIV.PeriodicDistributions.reconstructionType := by
  intro d U φ
  obtain ⟨A, L, he⟩ := pairing_estimate_of_weighted hw (distributionCoeff U) (polynomial_growth d U)
  refine ⟨(he φ).1, ?_⟩
  have hsmooth := smooth_expansion_of_weighted (d := d)
    (fun ψ N => by obtain ⟨B, M, h⟩ := hw d N; exact (h ψ).1) φ
  apply (U.hasSum hsmooth).congr_fun
  intro n
  simp only [map_smul, smul_eq_mul, distributionCoeff, mul_comm]

/-- Coefficient uniqueness is reduced to the same analytic estimate. -/
theorem uniqueness_of_weighted_estimate
    (hw : Specs.ExpandedFA.PartIV.PeriodicDistributions.weightedEstimateType) :
    Specs.ExpandedFA.PartIV.PeriodicDistributions.uniquenessType := by
  intro d U V h
  apply uniqueness_of_smooth_expansion (d := d) ?_ U V h
  exact smooth_expansion_of_weighted
    (fun ψ N => by obtain ⟨B, M, h⟩ := hw d N; exact (h ψ).1)

/-- The final distributional convergence statement follows from the same
absolutely convergent formula and the already constructed finite distributions. -/
theorem finite_sums_of_weighted_estimate
    (hw : Specs.ExpandedFA.PartIV.PeriodicDistributions.weightedEstimateType) :
    Specs.ExpandedFA.PartIV.PeriodicDistributions.finiteSumsType := by
  intro d c hc
  obtain ⟨U, hU, _⟩ := converse_of_weighted_estimate hw d c hc
  refine ⟨U, hU.1, finite_distribution_exists d c, fun φ => ?_⟩
  change HasSum (fun n => c n * testFourierCoeff φ (-n)) (U φ)
  exact (hU.2 φ).2


/-! Quantitative smooth Fourier decay via Haar integration by parts. -/

namespace FourierDecay
variable {d : ℕ}

noncomputable def jet (φ : Smooth ℂ d) {k : ℕ} (a : Fin k → Fin d) : Smooth ℂ d :=
  ⟨fun q => iteratedFDeriv ℝ k (lift φ) (representative q)
      (fun j => coordinateVector (a j)), by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x : Domain d =>
      iteratedFDeriv ℝ k (lift φ) (representative (quotient x))
        (fun j => coordinateVector (a j)))
    simp_rw [representative_quotient, iteratedFDeriv_lift_add_integer]
    exact ((coordinateEvaluation ℂ a).restrictScalars ℝ).contDiff.comp
      ((contDiff_lift φ).iteratedFDeriv_right (by simp))⟩

@[simp] theorem lift_jet (φ : Smooth ℂ d) {k : ℕ} (a : Fin k → Fin d)
    (x : Domain d) :
    lift (jet φ a) x = iteratedFDeriv ℝ k (lift φ) x (fun j => coordinateVector (a j)) := by
  change iteratedFDeriv ℝ k (lift φ) (representative (quotient x)) _ = _
  rw [representative_quotient, iteratedFDeriv_lift_add_integer]


@[simp] theorem quotient_add (x y : Domain d) : quotient (x + y) = quotient x + quotient y := by
  ext i
  simp [quotient, Pi.add_apply]

@[simp] theorem quotient_zero : quotient (0 : Domain d) = 0 := by
  ext i
  simp [quotient]

@[simp] theorem lift_jet_one (φ : Smooth ℂ d) (i : Fin d) (x : Domain d) :
    lift (jet φ (fun _ : Fin 1 => i)) x = fderiv ℝ (lift φ) x (coordinateVector i) := by
  rw [lift_jet, iteratedFDeriv_one_apply]

lemma hasDerivAt_shift (φ : Smooth ℂ d) (i : Fin d) (q : Torus d) (t : ℝ) :
    HasDerivAt (fun u : ℝ => φ.val (q + quotient (u • coordinateVector i)))
      ((jet φ (fun _ : Fin 1 => i)).val (q + quotient (t • coordinateVector i))) t := by
  have h := ((contDiff_lift φ).differentiable (by simp) |>.differentiableAt
      (x := representative q + t • coordinateVector i)).hasFDerivAt.comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const (coordinateVector i)).const_add (representative q))
  simp only [Function.comp_def] at h
  have heq (u : ℝ) : quotient (representative q + u • coordinateVector i) =
      q + quotient (u • coordinateVector i) := by
    rw [quotient_add, quotient_representative]
  have hval : (jet φ (fun _ : Fin 1 => i)).val
      (q + quotient (t • coordinateVector i)) =
      fderiv ℝ (lift φ) (representative q + t • coordinateVector i) (coordinateVector i) := by
    rw [← heq, ← lift, lift_jet_one]
  simpa only [lift, heq, one_smul, hval, id_eq] using h

instance torusHaarRightInvariant : (torusHaar d).IsAddRightInvariant := by
  unfold torusHaar
  infer_instance

lemma integral_jet_one_zero (φ : Smooth ℂ d) (i : Fin d) :
    (∫ q, (jet φ (fun _ : Fin 1 => i)).val q ∂torusHaar d) = 0 := by
  let ψ := jet φ (fun _ : Fin 1 => i)
  let F : ℝ → Torus d → ℂ := fun t q => φ.val (q + quotient (t • coordinateVector i))
  let F' : ℝ → Torus d → ℂ := fun t q => ψ.val (q + quotient (t • coordinateVector i))
  have hF (t : ℝ) : Continuous (F t) :=
    (continuous_smooth φ).comp (continuous_id.add continuous_const)
  have hF' (t : ℝ) : Continuous (F' t) :=
    (continuous_smooth ψ).comp (continuous_id.add continuous_const)
  obtain ⟨_, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := torusHaar d) (F := F) (F' := F') (x₀ := 0) (s := Set.univ)
    (bound := fun _ => smoothPartialSeminorm ℂ d 0 ψ) (Filter.univ_mem)
    (Filter.Eventually.of_forall fun t => (hF t).aestronglyMeasurable)
    ((hF 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hF' 0).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun q t _ => norm_smooth_apply_le ψ _)
    (integrable_const _)
    (Filter.Eventually.of_forall fun q t _ => hasDerivAt_shift φ i q t)
  have heq (t : ℝ) : (∫ q, F t q ∂torusHaar d) = ∫ q, φ.val q ∂torusHaar d :=
    integral_add_right_eq_self φ.val (quotient (t • coordinateVector i))
  simp only [heq] at hd
  have hz := hd.unique (hasDerivAt_const (0 : ℝ) (∫ q, φ.val q ∂torusHaar d))
  simpa [F', ψ] using hz

lemma jet_one_jet (φ : Smooth ℂ d) {k : ℕ} (a : Fin k → Fin d) (i : Fin d) :
    jet (jet φ a) (fun _ : Fin 1 => i) = jet φ (Fin.cons i a) := by
  apply lift_injective
  funext x
  rw [lift_jet_one]
  rw [show lift (jet φ a) = (fun y => iteratedFDeriv ℝ k (lift φ) y (fun j => coordinateVector (a j))) from funext (lift_jet φ a), lift_jet]
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k (lift φ)) x :=
    ((contDiff_lift φ).iteratedFDeriv_right (m := 1) (by simp)).differentiable (by simp) |>.differentiableAt
  simpa only [Fin.tail_def, Fin.cons_succ, Fin.cons_zero, Function.comp_def] using
    (hd.iteratedFDeriv_succ_apply_left' (m := fun j => coordinateVector ((Fin.cons i a : Fin (k + 1) → Fin d) j))).symm

lemma jet_zero (φ : Smooth ℂ d) : jet φ (fun i : Fin 0 => Fin.elim0 i) = φ := by
  apply lift_injective
  funext x
  simp only [lift_jet, iteratedFDeriv_zero_apply]

lemma norm_jet_apply_le (φ : Smooth ℂ d) {k : ℕ} (a : Fin k → Fin d) (q : Torus d) :
    ‖(jet φ a).val q‖ ≤ smoothPartialSeminorm ℂ d k φ := by
  exact ((coordinateJetLM ℂ d a φ).norm_coe_le_norm
    ⟨representative q, representative_mem_cube q⟩).trans (coordinateJet_le_partial a le_rfl φ)

lemma norm_coeff_jet_le (φ : Smooth ℂ d) {k : ℕ} (a : Fin k → Fin d) (n : Lattice d) :
    ‖testFourierCoeff (jet φ a) n‖ ≤ smoothPartialSeminorm ℂ d k φ := by
  have h := norm_integral_le_of_norm_le_const (μ := torusHaar d)
    (f := fun x => UnitAddTorus.mFourier (-n) x * (jet φ a).val x)
    (C := smoothPartialSeminorm ℂ d k φ)
    (Filter.Eventually.of_forall fun q => ?_)
  · simpa only [testFourierCoeff, probReal_univ, mul_one] using h
  · rw [norm_mul, show ‖UnitAddTorus.mFourier (-n) q‖ = 1 from norm_character (-n) q, one_mul]
    exact norm_jet_apply_le φ a q

lemma coeff_jet_constant_of_multiplier
    (hm : ∀ (ψ : Smooth ℂ d) (i : Fin d) (n : Lattice d),
      testFourierCoeff (jet ψ (fun _ : Fin 1 => i)) n =
        phase n (coordinateVector i) * testFourierCoeff ψ n)
    (φ : Smooth ℂ d) (i : Fin d) (n : Lattice d) (k : ℕ) :
    testFourierCoeff (jet φ (fun _ : Fin k => i)) n =
      phase n (coordinateVector i) ^ k * testFourierCoeff φ n := by
  induction k with
  | zero =>
    have heq : (fun _ : Fin 0 => i) = (fun j : Fin 0 => Fin.elim0 j) := Subsingleton.elim _ _
    rw [heq, jet_zero]
    simp
  | succ k ih =>
    have heq : (fun _ : Fin (k + 1) => i) = Fin.cons i (fun _ : Fin k => i) := by
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    rw [heq, ← jet_one_jet, hm, ih, pow_succ]
    ring

lemma coordinate_decay_of_multiplier
    (hm : ∀ (ψ : Smooth ℂ d) (i : Fin d) (n : Lattice d),
      testFourierCoeff (jet ψ (fun _ : Fin 1 => i)) n =
        phase n (coordinateVector i) * testFourierCoeff ψ n)
    (φ : Smooth ℂ d) (i : Fin d) (n : Lattice d) (k : ℕ) :
    ((2 * Real.pi) * ‖(n i : ℝ)‖) ^ k * ‖testFourierCoeff φ n‖ ≤
      smoothPartialSeminorm ℂ d k φ := by
  have hb := norm_coeff_jet_le φ (fun _ : Fin k => i) n
  rw [coeff_jet_constant_of_multiplier hm, norm_mul, norm_pow, norm_phase_coordinate] at hb
  exact hb

lemma coordinate_decay_without_pi_of_multiplier
    (hm : ∀ (ψ : Smooth ℂ d) (i : Fin d) (n : Lattice d),
      testFourierCoeff (jet ψ (fun _ : Fin 1 => i)) n =
        phase n (coordinateVector i) * testFourierCoeff ψ n)
    (φ : Smooth ℂ d) (i : Fin d) (n : Lattice d) (k : ℕ) :
    ‖(n i : ℝ)‖ ^ k * ‖testFourierCoeff φ n‖ ≤
      smoothPartialSeminorm ℂ d k φ := by
  calc
    _ ≤ ((2 * Real.pi) * ‖(n i : ℝ)‖) ^ k * ‖testFourierCoeff φ n‖ := by
      gcongr
      nlinarith [Real.pi_gt_three, norm_nonneg (n i : ℝ)]
    _ ≤ _ := coordinate_decay_of_multiplier hm φ i n k


noncomputable def smoothMul (φ ψ : Smooth ℂ d) : Smooth ℂ d :=
  ⟨fun q => φ.val q * ψ.val q, (contDiff_lift φ).mul (contDiff_lift ψ)⟩

@[simp] theorem lift_smoothMul (φ ψ : Smooth ℂ d) :
    lift (smoothMul φ ψ) = lift φ * lift ψ := rfl

lemma jet_mul_one (φ ψ : Smooth ℂ d) (i : Fin d) (q : Torus d) :
    (jet (smoothMul φ ψ) (fun _ : Fin 1 => i)).val q =
      (jet φ (fun _ : Fin 1 => i)).val q * ψ.val q +
        φ.val q * (jet ψ (fun _ : Fin 1 => i)).val q := by
  have h1 := hasDerivAt_shift (smoothMul φ ψ) i q 0
  have h2 := (hasDerivAt_shift φ i q 0).mul (hasDerivAt_shift ψ i q 0)
  have heq : (fun u : ℝ => (smoothMul φ ψ).val (q + quotient (u • coordinateVector i))) =
      (fun u : ℝ => φ.val (q + quotient (u • coordinateVector i)) *
        ψ.val (q + quotient (u • coordinateVector i))) := rfl
  rw [heq] at h1
  simpa using h1.unique h2

lemma jet_character_one (n : Lattice d) (i : Fin d) (q : Torus d) :
    (jet (character n) (fun _ : Fin 1 => i)).val q =
      phase n (coordinateVector i) * UnitAddTorus.mFourier n q := by
  have h := lift_jet_one (character n) i (representative q)
  simp only [lift, quotient_representative] at h
  rw [h, lift_character, ((phase n).hasFDerivAt.cexp).fderiv]
  have he := congrFun (lift_character n) (representative q)
  simp only [lift, quotient_representative, character_apply] at he
  rw [← he]
  simp only [smul_apply, smul_eq_mul]
  ring

lemma fourierCoeff_jet_one (φ : Smooth ℂ d) (i : Fin d) (n : Lattice d) :
    testFourierCoeff (jet φ (fun _ : Fin 1 => i)) n =
      phase n (coordinateVector i) * testFourierCoeff φ n := by
  have hz := integral_jet_one_zero (smoothMul (character (-n)) φ) i
  simp_rw [jet_mul_one, jet_character_one, character_apply] at hz
  have hint1 : Integrable (fun q => phase (-n) (coordinateVector i) *
      UnitAddTorus.mFourier (-n) q * φ.val q) (torusHaar d) := by
    simpa [mul_assoc] using (integrable_fourier_test φ n).const_mul
      (phase (-n) (coordinateVector i))
  rw [integral_add hint1 (integrable_fourier_test (jet φ (fun _ : Fin 1 => i)) n)] at hz
  simp_rw [mul_assoc (phase (-n) (coordinateVector i))] at hz
  rw [integral_const_mul] at hz
  change phase (-n) (coordinateVector i) * testFourierCoeff φ n +
      testFourierCoeff (jet φ (fun _ : Fin 1 => i)) n = 0 at hz
  simp only [phase_coordinate, Pi.neg_apply, Int.cast_neg, mul_neg] at hz ⊢
  linear_combination hz

end FourierDecay

/-- Coordinate bounds control the Euclidean frequency length. -/
theorem frequencyNorm_le_card_mul {d : ℕ} (n : Lattice d) (a : ℝ) (ha : ∀ i, ‖(n i : ℝ)‖ ≤ a) :
    frequencyNorm n ≤ (d : ℝ) * a := by
  classical
  let x : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (integerVector n)
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  change ‖x‖ ≤ _
  calc
    ‖x‖ = ‖∑ i, (b.repr x).ofLp i • b i‖ := congrArg norm (b.sum_repr x).symm
    _ ≤ ∑ i, ‖(b.repr x).ofLp i • b i‖ := norm_sum_le _ _
    _ = ∑ i, ‖(n i : ℝ)‖ := by
      congr 1
      funext i
      rw [norm_smul, b.norm_eq_one, mul_one]
      simp [b, x, integerVector]
    _ ≤ ∑ _i : Fin d, a := Finset.sum_le_sum fun i _ => ha i
    _ = (d : ℝ) * a := by simp



/-- Coordinate decay controls a polynomial weight in the Euclidean length. -/
theorem polynomial_weight_bound_of_coordinates {d M : ℕ} (f : Lattice d → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hz : ‖f 0‖ ≤ B)
    (hc : ∀ n (i : Fin d), ‖(n i : ℝ)‖ ^ M * ‖f n‖ ≤ B) (n : Lattice d) :
    (1 + frequencyNorm n) ^ M * ‖f n‖ ≤ (2 * (d + 1 : ℝ)) ^ M * B := by
  classical
  by_cases hn : n = 0
  · subst n
    have hC : 1 ≤ (2 * (d + 1 : ℝ)) ^ M := one_le_pow₀ (by nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
    have hzero : frequencyNorm (0 : Lattice d) = 0 := by simp [frequencyNorm]
    rw [hzero, add_zero, one_pow, one_mul]
    exact hz.trans (le_mul_of_one_le_left hB hC)
  · have hex : ∃ i : Fin d, n i ≠ 0 := by
      by_contra! hh
      exact hn (funext hh)
    obtain ⟨j, hj⟩ := hex
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
      (fun i : Fin d => ‖(n i : ℝ)‖) ⟨j, Finset.mem_univ _⟩
    have hj1 : 1 ≤ ‖(n j : ℝ)‖ := by
      rw [Real.norm_eq_abs, ← Int.cast_abs]
      exact_mod_cast (Int.one_le_abs hj)
    have hi1 : 1 ≤ ‖(n i : ℝ)‖ := hj1.trans (hi j (Finset.mem_univ _))
    have hr : frequencyNorm n ≤ (d : ℝ) * ‖(n i : ℝ)‖ :=
      frequencyNorm_le_card_mul n _ (fun j => hi j (Finset.mem_univ _))
    have hw : 1 + frequencyNorm n ≤ 2 * (d + 1 : ℝ) * ‖(n i : ℝ)‖ := by
      nlinarith [norm_nonneg (n i : ℝ)]
    calc
      _ ≤ (2 * (d + 1 : ℝ) * ‖(n i : ℝ)‖) ^ M * ‖f n‖ := by
        gcongr
        exact add_nonneg zero_le_one (frequencyNorm_nonneg n)
      _ = (2 * (d + 1 : ℝ)) ^ M * (‖(n i : ℝ)‖ ^ M * ‖f n‖) := by rw [mul_pow]; ring
      _ ≤ (2 * (d + 1 : ℝ)) ^ M * B := mul_le_mul_of_nonneg_left (hc n i) (by positivity)

/-- Natural inverse powers are summable beyond the lattice dimension. -/
theorem lattice_norm_inv_pow_summable (d p : ℕ) (hp : d < p) :
    Summable (fun n : Lattice d => (frequencyNorm n)⁻¹ ^ p) := by
  classical
  let b := PiLp.basisFun 2 ℝ (Fin d)
  let L : Submodule ℤ (EuclideanSpace ℝ (Fin d)) := Submodule.span ℤ (Set.range b)
  let f : Lattice d → L := fun n => ⟨WithLp.toLp 2 (integerVector n), by
    apply (b.mem_span_iff_repr_mem ℤ _).mpr
    intro i
    exact ⟨n i, by simp [b, PiLp.basisFun_repr, integerVector]⟩⟩
  have hfin : Module.finrank ℤ L = d := by
    rw [ZLattice.rank ℝ L]
    simp
  have hf : Function.Injective f := by
    intro n m h
    have he : WithLp.toLp 2 (integerVector n) = WithLp.toLp 2 (integerVector m) :=
      congrArg Subtype.val h
    ext i
    have hi := congrFun (congrArg WithLp.ofLp he) i
    change (n i : ℝ) = (m i : ℝ) at hi
    exact_mod_cast hi
  simpa [Function.comp_def, f, frequencyNorm] using (ZLattice.summable_norm_pow_inv L p (by simpa only [hfin] using hp)).comp_injective hf

/-- The weight shifted by one also includes the zero frequency. -/
theorem lattice_weight_inv_pow_summable (d p : ℕ) (hp : d < p) :
    Summable (fun n : Lattice d => ((1 + frequencyNorm n) ^ p)⁻¹) := by
  apply (lattice_norm_inv_pow_summable d p hp).of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0 : Lattice d)] with n hn
  have hpos : 0 < frequencyNorm n := by
    apply norm_pos_iff.mpr
    intro h
    apply hn
    ext i
    have hi := congrFun (congrArg WithLp.ofLp h) i
    change (n i : ℝ) = 0 at hi
    exact_mod_cast hi
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← inv_pow]
  gcongr
  linarith



/-- Pointwise rapid decay implies weighted absolute summability. -/
theorem weighted_estimate_of_pointwise
    (hc : ∀ (d M : ℕ), ∃ C : ℝ≥0, ∀ (φ : Smooth ℂ d) (n : Lattice d),
      (1 + frequencyNorm n) ^ M * ‖testFourierCoeff φ n‖ ≤
        C * smoothPartialSeminorm ℂ d M φ) :
    Specs.ExpandedFA.PartIV.PeriodicDistributions.weightedEstimateType := by
  intro d N
  let p := d + 1
  let M := N + p
  obtain ⟨C, hC⟩ := hc d M
  let w : Lattice d → ℝ := fun n => ((1 + frequencyNorm n) ^ p)⁻¹
  have hw : Summable w := lattice_weight_inv_pow_summable d p (by omega)
  let W : ℝ≥0 := ⟨∑' n, w n, tsum_nonneg (fun n => by
    exact inv_nonneg.mpr (pow_nonneg (by linarith [frequencyNorm_nonneg n]) _))⟩
  refine ⟨C * W, M, fun φ => ?_⟩
  have hdom (n : Lattice d) :
      (1 + frequencyNorm n) ^ N * ‖testFourierCoeff φ n‖ ≤
        (C * smoothPartialSeminorm ℂ d M φ) * w n := by
    have hb : 0 < 1 + frequencyNorm n := by linarith [frequencyNorm_nonneg n]
    dsimp [w]
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos hb p)).mpr
    convert hC φ n using 1
    dsimp [M]
    rw [pow_add]
    ring
  have hs : Summable (fun n => (1 + frequencyNorm n) ^ N * ‖testFourierCoeff φ n‖) :=
    (hw.mul_left (C * smoothPartialSeminorm ℂ d M φ)).of_nonneg_of_le
      (fun n => mul_nonneg (pow_nonneg (by linarith [frequencyNorm_nonneg n]) _) (norm_nonneg _)) hdom
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' n, (C * smoothPartialSeminorm ℂ d M φ) * w n :=
      hs.tsum_le_tsum hdom (hw.mul_left _)
    _ = (C * smoothPartialSeminorm ℂ d M φ) * ∑' n, w n := tsum_mul_left
    _ = _ := by rw [NNReal.coe_mul]; change _ = ((C : ℝ) * ∑' n, w n) * _; ring

/-- Higher partial seminorms include every lower-order partial. -/
theorem smoothPartialSeminorm_mono {k m : ℕ} (hkm : k ≤ m) :
    smoothPartialSeminorm ℂ d k ≤ smoothPartialSeminorm ℂ d m := by
  unfold smoothPartialSeminorm
  exact Finset.sup_mono (Finset.range_mono (Nat.add_le_add_right hkm 1))

/-- Uniform rapid decay, expressed with the source's Euclidean lattice norm. -/
theorem testFourierCoeff_rapid_decay (d M : ℕ) :
    ∃ C : ℝ≥0, ∀ (φ : Smooth ℂ d) (n : Lattice d),
      (1 + frequencyNorm n) ^ M * ‖testFourierCoeff φ n‖ ≤
        C * smoothPartialSeminorm ℂ d M φ := by
  refine ⟨⟨(2 * (d + 1 : ℝ)) ^ M, by positivity⟩, fun φ n => ?_⟩
  apply polynomial_weight_bound_of_coordinates (fun n => testFourierCoeff φ n)
    (smoothPartialSeminorm ℂ d M φ) (apply_nonneg _ _)
  · exact (norm_testFourierCoeff_le φ 0).trans
      (smoothPartialSeminorm_mono (Nat.zero_le M) φ)
  · intro m i
    exact FourierDecay.coordinate_decay_without_pi_of_multiplier
      FourierDecay.fourierCoeff_jet_one φ i m M

/-- Every polynomial weight is absolutely summable with a uniform smooth bound. -/
theorem weighted_estimate :
    Specs.ExpandedFA.PartIV.PeriodicDistributions.weightedEstimateType :=
  weighted_estimate_of_pointwise testFourierCoeff_rapid_decay

/-- The distribution is the absolutely convergent Fourier pairing on every test. -/
theorem reconstruction :
    Specs.ExpandedFA.PartIV.PeriodicDistributions.reconstructionType :=
  reconstruction_of_weighted_estimate weighted_estimate

/-- Polynomial-growth sequences are exactly the Fourier coefficients of torus
 distributions, with the scalar-linear pairing and its absolute convergence. -/
theorem converse :
    Specs.ExpandedFA.PartIV.PeriodicDistributions.converseType :=
  converse_of_weighted_estimate weighted_estimate

/-- All Fourier coefficients together determine a torus distribution. -/
theorem uniqueness :
    Specs.ExpandedFA.PartIV.PeriodicDistributions.uniquenessType :=
  uniqueness_of_weighted_estimate weighted_estimate

/-- Finite Fourier distributions converge on every smooth test. -/
theorem finite_sums :
    Specs.ExpandedFA.PartIV.PeriodicDistributions.finiteSumsType :=
  finite_sums_of_weighted_estimate weighted_estimate

end ExpandedFA.PartIV.Periodic
