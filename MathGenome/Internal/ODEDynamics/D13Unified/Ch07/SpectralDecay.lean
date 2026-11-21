import MathGenome.Internal.ODEDynamics.D13Unified.Ch07.JordanSolutions
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.SpectralDecay
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.Compact

noncomputable section
open scoped Matrix.Norms.Operator Topology
open Filter
set_option backward.isDefEq.respectTransparency false

namespace D13Unified.Ch07

/-- The polynomial factors of generalized eigenvectors are dominated by any
 strictly faster exponential. -/
lemma exponential_polynomial_decay (p : Polynomial ℂ) (μ : ℂ) (b : ℝ)
    (hμ : μ.re + b < 0) :
    Tendsto (fun t : ℝ => Real.exp (b * t) •
      (p.eval (t : ℂ) * Complex.exp (μ * (t : ℂ)))) atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [Polynomial.eval_add, add_mul, smul_add, add_zero] using hp.add hq
  | monomial j c =>
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hpow : Tendsto (fun t : ℝ => t ^ j * Real.exp ((μ.re + b) * t))
        atTop (𝓝 0) := by
      simpa only [Real.rpow_natCast, neg_neg] using
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (j : ℝ) (-(μ.re + b))
          (neg_pos.mpr hμ)
    have h := (tendsto_const_nhds (x := ‖c‖)).mul hpow
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simp only [Polynomial.eval_monomial, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht, Complex.norm_exp,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [add_mul, Real.exp_add]
    ring

/-- Decay on the whole space follows by finite generalized-eigenspace
 decomposition, including the case of zero-dimensional state space. -/
lemma matrixExp_weighted_orbit_tendsto_zero {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (b : ℝ)
    (hspec : ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLinAlgEquiv' A) μ →
      μ.re + b < 0) (v : n → ℂ) (k : n) :
    Tendsto (fun t : ℝ => Real.exp (b * t) • (matrixExp A t).mulVec v k)
      atTop (𝓝 0) := by
  classical
  let T : Module.End ℂ (n → ℂ) := Matrix.toLinAlgEquiv' A
  obtain ⟨f, hf, heq⟩ :=
    (Submodule.mem_iSup_iff_exists_finsupp (fun μ => T.maxGenEigenspace μ) v).mp
      ((Module.End.iSup_maxGenEigenspace_eq_top T).symm ▸ Submodule.mem_top)
  have hpart (μ : ℂ) :
      Tendsto (fun t : ℝ => Real.exp (b * t) • (matrixExp A t).mulVec (f μ) k)
        atTop (𝓝 0) := by
    by_cases hz : f μ = 0
    · simpa only [hz, Matrix.mulVec_zero, Pi.zero_apply, smul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))
    have hne : T.maxGenEigenspace μ ≠ ⊥ := by
      intro hbot
      exact hz ((Submodule.mem_bot ℂ).mp (hbot ▸ hf μ))
    have hev : T.HasEigenvalue μ :=
      Module.End.HasUnifEigenvalue.lt zero_lt_one hne
    obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace T μ (f μ)).mp (hf μ)
    have hm' : ((A - μ • (1 : Matrix n n ℂ)) ^ m).mulVec (f μ) = 0 := by
      simpa only [← Matrix.toLinAlgEquiv'_apply, map_pow, map_sub, map_smul, map_one]
        using hm
    obtain ⟨p, hp⟩ := matrixExp_generalized_eigenvector A μ (f μ) m hm'
    simpa only [hp] using exponential_polynomial_decay (p k) μ b (hspec μ hev)
  have hsum := tendsto_finsetSum f.support (fun μ _ => hpart μ)
  simp only [Finset.sum_const_zero] at hsum
  convert hsum using 1
  funext t
  rw [← heq]
  change Real.exp (b * t) • (matrixExp A t).mulVec (∑ μ ∈ f.support, f μ) k = _
  rw [Matrix.mulVec_sum, Finset.sum_apply, Finset.smul_sum]

/-- Entrywise convergence is convergence in the finite-dimensional matrix topology. -/
lemma matrixExp_weighted_tendsto_zero {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (b : ℝ)
    (hspec : ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLinAlgEquiv' A) μ →
      μ.re + b < 0) :
    Tendsto (fun t : ℝ => Real.exp (b * t) • matrixExp A t) atTop (𝓝 0) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.zero_apply, Pi.zero_apply] using
      matrixExp_weighted_orbit_tendsto_zero A b hspec (Pi.single j 1) i

/-- A continuous path tending to zero has a finite bound on the forward half-line. -/
lemma norm_bounded_on_nonnegative {F : Type*} [NormedAddCommGroup F]
    (f : ℝ → F) (hf : Continuous f) (hlim : Tendsto f atTop (𝓝 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ C := by
  have hnormlim : Tendsto (fun t => ‖f t‖) atTop (𝓝 0) := by simpa using hlim.norm
  have hevent : ∀ᶠ t in atTop, ‖f t‖ ≤ (1 : ℝ) :=
    hnormlim.eventually (eventually_le_nhds zero_lt_one)
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) T)).bddAbove_image
    hf.norm.continuousOn
  refine ⟨max 0 (max 1 M), le_max_left _ _, fun t ht => ?_⟩
  by_cases h : t ≤ T
  · exact (hM (Set.mem_image_of_mem _ ⟨ht, h⟩)).trans
      ((le_max_right 1 M).trans (le_max_right _ _))
  · exact (hT t (le_of_lt (lt_of_not_ge h))).trans
      ((le_max_left 1 M).trans (le_max_right _ _))

/-- Transfer the weighted matrix limit to the norm induced by any fixed state norm. -/
lemma matrixExp_decay_of_weighted_limit {𝕂 n E : Type*} [RCLike 𝕂]
    [Fintype n] [DecidableEq n] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    [FiniteDimensional 𝕂 E] (basis : Module.Basis n 𝕂 E)
    (A : Matrix n n 𝕂) (b : ℝ)
    (hlim : Tendsto (fun t : ℝ => Real.exp (b * t) • matrixExp A t)
      atTop (𝓝 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      matrixOperatorNorm basis (matrixExp A t) ≤ C * Real.exp (-b * t) := by
  let L := matrixOperatorEquiv basis
  have hL : Continuous L := L.toLinearMap.continuous_of_finiteDimensional
  have hlim' := (hL.tendsto 0).comp hlim
  rw [map_zero] at hlim'
  have hcont : Continuous (fun t : ℝ => L (Real.exp (b * t) • matrixExp A t)) := by
    apply hL.comp
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      (matrixExp_smooth A).continuous
  obtain ⟨C, hC, hbound⟩ := norm_bounded_on_nonnegative _ hcont hlim'
  refine ⟨C, hC, fun t ht => ?_⟩
  have h := hbound t ht
  have hmap : L (Real.exp (b * t) • matrixExp A t) =
      (algebraMap ℝ 𝕂 (Real.exp (b * t))) • L (matrixExp A t) := by
    rw [← algebraMap_smul 𝕂 (Real.exp (b * t)), map_smul]
  rw [hmap, norm_smul, norm_algebraMap' 𝕂, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h
  change ‖L (matrixExp A t)‖ ≤ _
  have hh := mul_le_mul_of_nonneg_right h (Real.exp_nonneg (-b * t))
  have he : Real.exp (-b * t) * Real.exp (b * t) = 1 := by
    rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
  calc
    ‖L (matrixExp A t)‖ =
        (Real.exp (b * t) * ‖L (matrixExp A t)‖) * Real.exp (-b * t) := by
      calc
        _ = (Real.exp (-b * t) * Real.exp (b * t)) * ‖L (matrixExp A t)‖ := by
          rw [he, one_mul]
        _ = _ := by ring
    _ ≤ C * Real.exp (-b * t) := hh

/-- The full complex spectral decay estimate, including all generalized eigenspaces. -/
theorem matrixExp_spectral_decay_complex :
    Specs.D13Unified.Ch07.SpectralDecay.complexDecayType := by
  intro n _ _ E _ _ _ basis A a _ha hspec b _hb hba
  apply matrixExp_decay_of_weighted_limit basis A b
  apply matrixExp_weighted_tendsto_zero A b
  intro μ hμ
  have := hspec μ hμ
  linarith

/-- Complexification commutes with the same matrix exponential used throughout
 the chapter. -/
lemma matrixExp_complexify {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (t : ℝ) :
    (matrixExp A t).map Complex.ofReal = matrixExp (A.map Complex.ofReal) t := by
  let φ : Matrix n n ℝ →+* Matrix n n ℂ := Complex.ofRealHom.mapMatrix
  have hφ : Continuous φ := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact Complex.continuous_ofReal.comp ((continuous_apply j).comp (continuous_apply i))
  have h := NormedSpace.map_exp φ hφ (t • A)
  change φ (NormedSpace.exp (t • A)) = NormedSpace.exp (t • A.map Complex.ofReal)
  rw [h]
  congr 1
  ext i j
  simp [φ, Matrix.smul_apply, smul_eq_mul, RCLike.real_smul_eq_coe_mul]

/-- The real weighted matrix limit is obtained from the complex limit by taking
 real parts, so no restriction to real eigenvalues is made. -/
lemma matrixExp_weighted_tendsto_zero_real {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (b : ℝ)
    (hspec : ∀ μ : ℂ,
      Module.End.HasEigenvalue (Matrix.toLinAlgEquiv' (A.map Complex.ofReal)) μ →
      μ.re + b < 0) :
    Tendsto (fun t : ℝ => Real.exp (b * t) • matrixExp A t) atTop (𝓝 0) := by
  have h := matrixExp_weighted_tendsto_zero (A.map Complex.ofReal) b hspec
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hij := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h i) j
  have hre := (Complex.continuous_re.tendsto (0 : ℂ)).comp hij
  simpa only [Function.comp_def, ← matrixExp_complexify, Matrix.smul_apply, Matrix.map_apply,
    Complex.smul_re, Complex.ofReal_re, smul_eq_mul, Complex.zero_re, Matrix.zero_apply] using hre

/-- Spectral decay for a real matrix, with its full complex spectrum and any
 compatible operator norm induced by the fixed real state norm. -/
theorem matrixExp_spectral_decay_real :
    Specs.D13Unified.Ch07.SpectralDecay.realDecayType := by
  intro n _ _ E _ _ _ basis A a _ha hspec b _hb hba
  apply matrixExp_decay_of_weighted_limit basis A b
  apply matrixExp_weighted_tendsto_zero_real A b
  intro μ hμ
  have := hspec μ hμ
  linarith

end D13Unified.Ch07
