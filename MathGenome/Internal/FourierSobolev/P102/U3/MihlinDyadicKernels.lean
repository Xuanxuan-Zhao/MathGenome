import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import MathGenome.Internal.FourierSobolev.P102.U3.SchwartzFourier
import MathGenome.Internal.FourierSobolev.Specs.P102.U3.MihlinDyadicKernels
import MathGenome.Internal.FourierSobolev.P102.U3.Plancherel
import MathGenome.Internal.FourierSobolev.P102.U3.FourierConvolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section
open MeasureTheory
open scoped FourierTransform ContDiff Topology
namespace P102.U3.Mihlin
open P102.Specs.U3 (Euclidean)

/-- A fixed radial smooth cutoff; its choice is independent of m and A. -/
def cutoff (d : ℕ) (x : Euclidean d) : ℝ :=
  Real.smoothTransition ((4 - ‖x‖ ^ 2) / 3)

theorem cutoff_isCutoff (d : ℕ) : IsCutoff (cutoff d) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Real.smoothTransition.contDiff.comp
      ((contDiff_const.sub (contDiff_norm_sq ℝ)).div_const 3)
  · intro x y h
    simp only [cutoff, h]
  · intro x
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro x hx
    apply Real.smoothTransition.one_of_one_le
    have hn := norm_nonneg x
    nlinarith
  · intro x hx
    apply Real.smoothTransition.zero_of_nonpos
    nlinarith [norm_nonneg x]

theorem cutoff_exists : P102.Specs.U3.MihlinDyadicKernels.cutoffExistenceType :=
  fun d => ⟨cutoff d, cutoff_isCutoff d⟩

theorem order_gt_half (d : ℕ) : (d : ℝ) / 2 < order d := by
  have h := Nat.mod_lt d (by decide : 0 < 2)
  have he := Nat.mod_add_div d 2
  unfold order
  have he' : (d : ℝ) = (d % 2 : ℕ) + 2 * (d / 2 : ℕ) := by exact_mod_cast he.symm
  have h' : ((d % 2 : ℕ) : ℝ) < 2 := by exact_mod_cast h
  push_cast
  linarith

@[simp] theorem scale_pos (j : ℤ) : 0 < scale j := zpow_pos (by norm_num) j
@[simp] theorem scale_ne_zero (j : ℤ) : scale j ≠ 0 := (scale_pos j).ne'
@[simp] theorem scale_zero : scale 0 = 1 := by simp [scale]
@[simp] theorem scale_one : scale 1 = 2 := by simp [scale]

theorem scale_add (j k : ℤ) : scale (j + k) = scale j * scale k := by
  exact zpow_add₀ (by norm_num) j k

@[simp] theorem scale_neg (j : ℤ) : scale (-j) = (scale j)⁻¹ := by
  simp [scale]

theorem annulus_eq_zero_of_small {d : ℕ} {χ : Euclidean d → ℝ}
    (hχ : IsCutoff χ) {x : Euclidean d} (hx : ‖x‖ ≤ 1 / 2) :
    annulus χ x = 0 := by
  have hx' : ‖(2 : ℝ) • x‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  rw [annulus, hχ.2.2.2.1 x (by linarith), hχ.2.2.2.1 _ hx', sub_self]

theorem annulus_eq_zero_of_large {d : ℕ} {χ : Euclidean d → ℝ}
    (hχ : IsCutoff χ) {x : Euclidean d} (hx : 2 ≤ ‖x‖) :
    annulus χ x = 0 := by
  have hx' : 2 ≤ ‖(2 : ℝ) • x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  rw [annulus, hχ.2.2.2.2 x hx, hχ.2.2.2.2 _ hx', sub_self]

theorem annulus_support {d : ℕ} {χ : Euclidean d → ℝ}
    (hχ : IsCutoff χ) (x : Euclidean d) (hx : annulus χ x ≠ 0) :
    (1 / 2 : ℝ) < ‖x‖ ∧ ‖x‖ < 2 := by
  constructor
  · by_contra h
    exact hx (annulus_eq_zero_of_small hχ (le_of_not_gt h))
  · by_contra h
    exact hx (annulus_eq_zero_of_large hχ (le_of_not_gt h))

@[simp] theorem block_zero_frequency {d : ℕ} (χ : Euclidean d → ℝ) (j : ℤ) :
    block χ j 0 = 0 := by simp [block, annulus]

/-- The cancellation identity responsible for telescoping the partition. -/
theorem block_eq_sub {d : ℕ} (χ : Euclidean d → ℝ) (j : ℤ) (x : Euclidean d) :
    block χ j x = χ (scale (-j) • x) - χ (scale (-(j - 1)) • x) := by
  unfold block annulus
  congr 2
  rw [← mul_smul]
  congr 1
  rw [show -(j - 1) = 1 + -j by omega, scale_add, scale_one]

/-- Smoothness of the annular cutoff. -/
theorem annulus_contDiff {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ) :
    ContDiff ℝ ∞ (annulus χ) := by
  exact hχ.1.sub (hχ.1.comp (contDiff_id.const_smul (2 : ℝ)))

/-- The rescaled and original frequency blocks agree after dilation. -/
theorem annularSymbol_rescale {d : ℕ} (χ : Euclidean d → ℝ)
    (m : Euclidean d → ℂ) (j : ℤ) (ξ : Euclidean d) :
    annularSymbol χ m j (scale (-j) • ξ) = m ξ * (block χ j ξ : ℂ) := by
  simp [annularSymbol, block, smul_smul]

theorem scale_mono : Monotone scale :=
  (zpow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).monotone

@[simp] theorem norm_scale_neg {d : ℕ} (j : ℤ) (x : Euclidean d) :
    ‖scale (-j) • x‖ = ‖x‖ / scale j := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (scale_pos _), scale_neg, div_eq_mul_inv,
    mul_comm]

theorem block_eq_zero_below {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ)
    (j : ℤ) (x : Euclidean d) (hx : ‖x‖ ≤ scale (j - 1)) : block χ j x = 0 := by
  apply annulus_eq_zero_of_small hχ
  rw [norm_scale_neg, div_le_iff₀ (scale_pos j)]
  have he : scale j = scale (j - 1) * 2 := by
    rw [← scale_one, ← scale_add]
    congr 1
    omega
  rw [he]
  linarith

theorem block_eq_zero_above {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ)
    (j : ℤ) (x : Euclidean d) (hx : scale (j + 1) ≤ ‖x‖) : block χ j x = 0 := by
  apply annulus_eq_zero_of_large hχ
  rw [norm_scale_neg, le_div_iff₀ (scale_pos j)]
  rw [scale_add, scale_one] at hx
  linarith

/-- Each nonzero frequency lies between two adjacent dyadic radii. Only the
corresponding two blocks can contribute. -/
theorem block_support_pair {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ)
    (x : Euclidean d) (hx : x ≠ 0) : ∃ k : ℤ,
    scale k ≤ ‖x‖ ∧ ‖x‖ < scale (k + 1) ∧
    Function.support (fun j : ℤ => block χ j x) ⊆ ({k, k + 1} : Set ℤ) := by
  obtain ⟨k, hk, hk'⟩ := exists_mem_Ico_zpow (norm_pos_iff.mpr hx)
    (by norm_num : (1 : ℝ) < 2)
  refine ⟨k, hk, hk', ?_⟩
  intro j hj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  by_contra h
  have hne : j ≠ k ∧ j ≠ k + 1 := by tauto
  rcases lt_or_gt_of_ne hne.1 with hlt | hgt
  · exact hj (block_eq_zero_above hχ j x ((scale_mono (by omega)).trans hk))
  · exact hj (block_eq_zero_below hχ j x (hk'.le.trans (scale_mono (by omega))))

theorem block_finite_support {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ)
    (x : Euclidean d) : (Function.support (fun j : ℤ => block χ j x)).Finite := by
  by_cases hx : x = 0
  · subst x
    simp
  · obtain ⟨k, _, _, hk⟩ := block_support_pair hχ x hx
    exact (Set.toFinite ({k, k + 1} : Set ℤ)).subset hk

theorem block_hasSum {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ)
    (x : Euclidean d) (hx : x ≠ 0) : HasSum (fun j : ℤ => block χ j x) 1 := by
  classical
  obtain ⟨k, hk, hk', hs⟩ := block_support_pair hχ x hx
  have hsum : HasSum (fun j : ℤ => block χ j x)
      (∑ j ∈ ({k, k + 1} : Finset ℤ), block χ j x) :=
    hasSum_sum_of_ne_finset_zero (s := {k, k + 1})
    (f := fun j : ℤ => block χ j x) (fun j hj => by
      by_contra hne
      have hmem := hs hne
      exact hj (by simpa using hmem))
  have hsmall : χ (scale (-(k + 1)) • x) = 1 := by
    apply hχ.2.2.2.1
    rw [norm_scale_neg, div_le_one (scale_pos _)]
    exact hk'.le
  have hlarge : χ (scale (-(k - 1)) • x) = 0 := by
    apply hχ.2.2.2.2
    rw [norm_scale_neg, le_div_iff₀ (scale_pos _)]
    have he : scale k = scale (k - 1) * 2 := by
      rw [← scale_one, ← scale_add]
      congr 1
      omega
    linarith
  have heq : (∑ j ∈ ({k, k + 1} : Finset ℤ), block χ j x) = 1 := by
    rw [Finset.sum_pair (by omega)]
    rw [block_eq_sub, block_eq_sub]
    simp only [show k + 1 - 1 = k by omega, hsmall, hlarge]
    ring
  rwa [heq] at hsum

theorem block_overlap {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ)
    (x : Euclidean d) (J : Finset ℤ) :
    (J.filter (fun j => block χ j x ≠ 0)).card ≤ 2 := by
  classical
  by_cases hx : x = 0
  · subst x
    simp
  · obtain ⟨k, _, _, hk⟩ := block_support_pair hχ x hx
    have hs : J.filter (fun j => block χ j x ≠ 0) ⊆ ({k, k + 1} : Finset ℤ) := by
      intro j hj
      simpa using hk (Finset.mem_filter.mp hj).2
    calc
      _ ≤ ({k, k + 1} : Finset ℤ).card := Finset.card_le_card hs
      _ ≤ 2 := by simp

theorem cutoff_isPartition (d : ℕ) : IsPartition (cutoff d) :=
  ⟨annulus_support (cutoff_isCutoff d),
    block_hasSum (cutoff_isCutoff d), block_finite_support (cutoff_isCutoff d),
    ⟨2, block_overlap (cutoff_isCutoff d)⟩⟩

theorem annulus_abs_le_one {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ)
    (x : Euclidean d) : |annulus χ x| ≤ 1 := by
  have h1 := hχ.2.2.1 x
  have h2 := hχ.2.2.1 ((2 : ℝ) • x)
  apply abs_le.mpr
  constructor <;> dsimp [annulus] <;> linarith

theorem block_abs_le_one {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ)
    (j : ℤ) (x : Euclidean d) : |block χ j x| ≤ 1 :=
  annulus_abs_le_one hχ _

theorem finite_block_abs_le_two {d : ℕ} {χ : Euclidean d → ℝ}
    (hχ : IsCutoff χ) (J : Finset ℤ) (x : Euclidean d) :
    |∑ j ∈ J, block χ j x| ≤ 2 := by
  classical
  calc
    _ ≤ ∑ j ∈ J, |block χ j x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ J.filter (fun j => block χ j x ≠ 0), |block χ j x| := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hj'
      have he : block χ j x = 0 := by
        simpa only [Finset.mem_filter, hj, true_and, not_not] using hj'
      simp [he]
    _ ≤ ∑ j ∈ J.filter (fun j => block χ j x ≠ 0), (1 : ℝ) :=
      Finset.sum_le_sum (fun j _ => block_abs_le_one hχ j x)
    _ = ((J.filter (fun j => block χ j x ≠ 0)).card : ℝ) := by simp
    _ ≤ 2 := by exact_mod_cast block_overlap hχ x J

theorem symbol_norm_le {d : ℕ} {m : Euclidean d → ℂ} {A : ℝ}
    (hm : SymbolBound m A) (ξ : Euclidean d) (hξ : ξ ≠ 0) : ‖m ξ‖ ≤ A := by
  simpa using hm.2 0 (Nat.zero_le _) Fin.elim0 ξ hξ

theorem symbol_bound_nonneg {d : ℕ} (hd : 1 ≤ d) {m : Euclidean d → ℂ} {A : ℝ}
    (hm : SymbolBound m A) : 0 ≤ A := by
  let i : Fin d := ⟨0, by omega⟩
  let x : Euclidean d := EuclideanSpace.basisFun (Fin d) ℝ i
  have hx : x ≠ 0 := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.ne_zero i
  exact (norm_nonneg (m x)).trans (symbol_norm_le hm x hx)

/-- Uniform pointwise bound, including the irrelevant value at the origin. -/
theorem finiteSymbol_norm_le {d : ℕ} (hd : 1 ≤ d) {χ : Euclidean d → ℝ}
    (hχ : IsCutoff χ) {m : Euclidean d → ℂ} {A : ℝ} (hm : SymbolBound m A)
    (J : Finset ℤ) (ξ : Euclidean d) : ‖finiteSymbol χ m J ξ‖ ≤ 2 * A := by
  have hA := symbol_bound_nonneg hd hm
  by_cases hξ : ξ = 0
  · subst ξ
    simp only [finiteSymbol, block_zero_frequency, Finset.sum_const_zero,
      Complex.ofReal_zero, mul_zero, norm_zero]
    linarith
  · rw [finiteSymbol, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ A * 2 := mul_le_mul (symbol_norm_le hm ξ hξ)
        (finite_block_abs_le_two hχ J ξ) (abs_nonneg _) hA
      _ = 2 * A := by ring

theorem annulus_hasCompactSupport {d : ℕ} {χ : Euclidean d → ℝ}
    (hχ : IsCutoff χ) : HasCompactSupport (annulus χ) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean d) 2)
  intro x hx
  apply annulus_eq_zero_of_large hχ
  have : 2 < ‖x‖ := by simpa using hx
  exact this.le

theorem annularSymbol_hasCompactSupport {d : ℕ} {χ : Euclidean d → ℝ}
    (hχ : IsCutoff χ) (m : Euclidean d → ℂ) (j : ℤ) :
    HasCompactSupport (annularSymbol χ m j) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean d) 2)
  intro x hx
  have hr : 2 ≤ ‖x‖ := le_of_lt (by simpa using hx)
  simp [annularSymbol, annulus_eq_zero_of_large hχ hr]

/-- Multiplication by the annular cutoff removes any value or irregularity at zero. -/
theorem annularSymbol_contDiff {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ)
    {m : Euclidean d → ℂ} {A : ℝ} (hm : SymbolBound m A) (j : ℤ) :
    ContDiff ℝ (order d) (annularSymbol χ m j) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : Euclidean d) (by norm_num : (0 : ℝ) < 1 / 2)]
      with y hy
    have hr : ‖y‖ ≤ 1 / 2 := le_of_lt (by simpa using hy)
    simp [annularSymbol, annulus_eq_zero_of_small hχ hr]
  · have hx' : scale j • x ≠ 0 := smul_ne_zero (scale_ne_zero j) hx
    have hmc := hm.1.contDiffAt (isOpen_compl_singleton.mem_nhds hx')
    have hc : ContDiffAt ℝ (order d) (fun x : Euclidean d => scale j • x) x :=
      (contDiff_id.const_smul (scale j)).contDiffAt
    have hη : ContDiff ℝ ∞ (fun x : Euclidean d => (annulus χ x : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (annulus_contDiff hχ)
    exact (hmc.comp x hc).mul (hη.of_le (by simp)).contDiffAt

theorem annularSymbol_integrable {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ)
    {m : Euclidean d → ℂ} {A : ℝ} (hm : SymbolBound m A) (j : ℤ) :
    Integrable (annularSymbol χ m j) :=
  (annularSymbol_contDiff hχ hm j).continuous.integrable_of_hasCompactSupport
    (annularSymbol_hasCompactSupport hχ m j)

/-- All physical-space derivatives exist despite only C^N regularity of the symbol:
compact frequency support supplies moments of every order. -/
theorem inverseKernel_contDiff {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ)
    {m : Euclidean d → ℂ} {A : ℝ} (hm : SymbolBound m A) (j : ℤ) :
    ContDiff ℝ ∞ (inverseKernel χ m j) := by
  have hc := (annularSymbol_contDiff hχ hm j).continuous
  have hs := annularSymbol_hasCompactSupport hχ m j
  have hf : ContDiff ℝ ∞ (𝓕 (annularSymbol χ m j)) := by
    apply Real.contDiff_fourier
    intro n _
    exact ((continuous_norm.pow n).mul hc.norm).integrable_of_hasCompactSupport
      hs.norm.mul_left
  have he : inverseKernel χ m j = fun x => 𝓕 (annularSymbol χ m j) (-x) := by
    funext x
    exact Real.fourierInv_eq_fourier_neg _ x
  rw [he]
  exact hf.comp contDiff_neg

/-- Integral and L² Fourier transforms agree on their common domain. -/
theorem memLp_fourier {d : ℕ} {a : Euclidean d → ℂ}
    (ha : MemLp a 2) (ha1 : Integrable a) : MemLp (𝓕 a) 2 := by
  exact (memLp_congr_ae
    (P102.U3.Plancherel.integral_compatibility a ha ha1)).mp
      (Lp.memLp (𝓕 ha.toLp : Lp (α := Euclidean d) ℂ 2 volume))

theorem eLpNorm_fourier_eq {d : ℕ} {a : Euclidean d → ℂ}
    (ha : MemLp a 2) (ha1 : Integrable a) :
    (eLpNorm (𝓕 a) 2 volume).toReal = (eLpNorm a 2 volume).toReal := by
  have he := P102.U3.Plancherel.integral_compatibility a ha ha1
  rw [← eLpNorm_congr_ae he]
  change ‖(𝓕 ha.toLp : Lp (α := Euclidean d) ℂ 2 volume)‖ = _
  rw [Lp.norm_fourier_eq, Lp.norm_toLp]

/-- Finite regularity suffices for all integrations by parts up to that order. -/
theorem compactSymbol_derivative_integrable {d N : ℕ} {a : Euclidean d → ℂ}
    (ha : ContDiff ℝ N a) (hs : HasCompactSupport a) {n : ℕ} (hn : n ≤ N) :
    Integrable (iteratedFDeriv ℝ n a) :=
  (ha.continuous_iteratedFDeriv (by exact_mod_cast hn)).integrable_of_hasCompactSupport
    (hs.iteratedFDeriv n)

/-- A scalar evaluation of each compactly supported frequency derivative belongs to L². -/
theorem compactSymbol_derivative_memLp {d N : ℕ} {a : Euclidean d → ℂ}
    (ha : ContDiff ℝ N a) (hs : HasCompactSupport a) {n : ℕ} (hn : n ≤ N)
    (v : Fin n → Euclidean d) :
    MemLp (fun ξ => iteratedFDeriv ℝ n a ξ v) 2 := by
  exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euclidean d) ℂ v).continuous.comp
    (ha.continuous_iteratedFDeriv (by exact_mod_cast hn))).memLp_of_hasCompactSupport
      ((hs.iteratedFDeriv n).comp_left (by simp))

/-- Integration by parts followed by Plancherel, with the full Fourier constant.
No Schwartz regularity of the compact symbol is used. -/
theorem compactSymbol_fourier_monomial_memLp {d N : ℕ} {a : Euclidean d → ℂ}
    (ha : ContDiff ℝ N a) (hs : HasCompactSupport a) {n : ℕ} (hn : n ≤ N)
    (v : Fin n → Euclidean d) :
    MemLp (fun x => (∏ i, -inner ℝ x (v i)) • 𝓕 a x) 2 := by
  have hdi := compactSymbol_derivative_integrable ha hs hn
  have hdv : Integrable (fun ξ => iteratedFDeriv ℝ n a ξ v) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euclidean d) ℂ v).integrable_comp hdi
  have hF := memLp_fourier (compactSymbol_derivative_memLp ha hs hn v) hdv
  have he : 𝓕 (fun ξ => iteratedFDeriv ℝ n a ξ v) =
      fun x => (-(2 * (Real.pi : ℂ) * Complex.I)) ^ n •
        (∏ i, -inner ℝ x (v i)) • 𝓕 a x := by
    funext x
    rw [← Real.fourier_continuousMultilinearMap_apply hdi,
      Real.fourier_iteratedFDeriv (N := (N : ℕ∞)) ha
        (fun k hk => compactSymbol_derivative_integrable ha hs (by exact_mod_cast hk))
        (by exact_mod_cast hn)]
    simp only [VectorFourier.fourierPowSMulRight_apply, neg_apply]
    rfl
  rw [he] at hF
  have hc : (-(2 * (Real.pi : ℂ) * Complex.I)) ^ n ≠ 0 := by
    exact pow_ne_zero _ (neg_ne_zero.mpr (mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero))
  simpa only [Pi.smul_def, smul_smul, inv_mul_cancel₀ hc, one_smul] using
    hF.const_smul ((-(2 * (Real.pi : ℂ) * Complex.I)) ^ n)⁻¹

/-- A finite-dimensional norm is bounded by the sum of its orthonormal coordinates. -/
theorem norm_le_sum_coordinates {d : ℕ} (x : Euclidean d) :
    ‖x‖ ≤ ∑ k : Fin d, ‖inner ℝ x (P102.U3.coordinateVector k)‖ := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  calc
    ‖x‖ = ‖∑ k, inner ℝ (b k) x • b k‖ := congrArg norm (b.sum_repr' x).symm
    _ ≤ ∑ k, ‖inner ℝ (b k) x • b k‖ := norm_sum_le _ _
    _ = _ := by simp [norm_smul, real_inner_comm,
      P102.U3.coordinateVector, b]

/-- The monomial bounds imply the radial power bound, without any loss of derivatives. -/
theorem compactSymbol_fourier_norm_pow_memLp {d N : ℕ} {a : Euclidean d → ℂ}
    (ha : ContDiff ℝ N a) (hs : HasCompactSupport a) {n : ℕ} (hn : n ≤ N) :
    MemLp (fun x => ‖x‖ ^ n * ‖𝓕 a x‖) 2 := by
  have hc : Continuous (𝓕 a) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂
    (ha.continuous.integrable_of_hasCompactSupport hs)
  have hsum : MemLp (fun x : Euclidean d =>
      (∑ k : Fin d, ‖inner ℝ x (P102.U3.coordinateVector k)‖) ^ n * ‖𝓕 a x‖) 2 := by
    have h := memLp_finsetSum (μ := volume) (p := (2 : ENNReal))
      (s := (Finset.univ : Finset (Fin n → Fin d)))
      (fun β _ => (compactSymbol_fourier_monomial_memLp ha hs hn
        (P102.U3.coordinateVector ∘ β)).norm)
    simp_rw [Fintype.sum_pow, Finset.sum_mul]
    simpa only [Function.comp_apply, norm_smul, norm_prod, norm_neg] using h
  apply hsum.mono' (((continuous_norm.pow n).mul hc.norm).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  change ‖‖x‖ ^ n * ‖𝓕 a x‖‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg x) n) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg x) (norm_le_sum_coordinates x) n) (norm_nonneg _)

/-- Qualitative weighted Plancherel for compact C^N symbols. Quantitative estimates
will additionally use the uniform derivative bounds for the dyadic family. -/
theorem compactSymbol_fourier_weighted_memLp {d N : ℕ} {a : Euclidean d → ℂ}
    (ha : ContDiff ℝ N a) (hs : HasCompactSupport a) :
    MemLp (fun x => ((1 + ‖x‖) ^ N : ℝ) • 𝓕 a x) 2 := by
  have h0 := memLp_fourier (ha.continuous.memLp_of_hasCompactSupport hs)
    (ha.continuous.integrable_of_hasCompactSupport hs)
  have hp := compactSymbol_fourier_norm_pow_memLp ha hs (le_refl N)
  have hc : Continuous (𝓕 a) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂
    (ha.continuous.integrable_of_hasCompactSupport hs)
  have hb := (h0.norm.add hp).const_smul ((2 : ℝ) ^ (N - 1))
  apply hb.mono' ((((continuous_const.add continuous_norm).pow N).smul hc).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  change ‖((1 + ‖x‖) ^ N : ℝ) • 𝓕 a x‖ ≤
    2 ^ (N - 1) * (‖𝓕 a x‖ + ‖x‖ ^ N * ‖𝓕 a x‖)
  rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (by positivity) N)]
  calc
    (1 + ‖x‖) ^ N * ‖𝓕 a x‖ ≤
        (2 ^ (N - 1) * (1 ^ N + ‖x‖ ^ N)) * ‖𝓕 a x‖ :=
      mul_le_mul_of_nonneg_right (add_pow_le (by norm_num) (norm_nonneg x) N) (norm_nonneg _)
    _ = _ := by rw [one_pow]; ring

/-- Reflection transfers the weighted Plancherel statement to the source's
positive-sign inverse integral. -/
theorem compactSymbol_inverse_weighted_memLp {d N : ℕ} {a : Euclidean d → ℂ}
    (ha : ContDiff ℝ N a) (hs : HasCompactSupport a) :
    MemLp (fun x => ((1 + ‖x‖) ^ N : ℝ) • 𝓕⁻ a x) 2 := by
  have h := (compactSymbol_fourier_weighted_memLp ha hs).comp_measurePreserving
    (Measure.measurePreserving_neg (volume : Measure (Euclidean d)))
  simpa only [Function.comp_def, norm_neg, Real.fourierInv_eq_fourier_neg] using h

/-- In particular every individual dyadic kernel has the required weighted L²
membership, while the uniform norm bound is still a quantitative obligation. -/
theorem inverseKernel_weighted_memLp {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ)
    {m : Euclidean d → ℂ} {A : ℝ} (hm : SymbolBound m A) (j : ℤ) :
    MemLp (fun x => ((1 + ‖x‖) ^ order d : ℝ) • inverseKernel χ m j x) 2 :=
  compactSymbol_inverse_weighted_memLp (annularSymbol_contDiff hχ hm j)
    (annularSymbol_hasCompactSupport hχ m j)

/-- Differentiating the inverse integral inserts the frequency coordinate and
exactly the positive Fourier constant fixed in the manuscript. -/
theorem compactSymbol_inverse_fderiv_apply {d : ℕ} {a : Euclidean d → ℂ}
    (ha : Continuous a) (hs : HasCompactSupport a) (x v : Euclidean d) :
    fderiv ℝ (𝓕⁻ a) x v =
      𝓕⁻ (fun ξ => (2 * (Real.pi : ℂ) * Complex.I) • (inner ℝ ξ v) • a ξ) x := by
  have ha1 : Integrable a := ha.integrable_of_hasCompactSupport hs
  have hmom : Integrable (fun ξ => ‖ξ‖ * ‖a ξ‖) :=
    (continuous_norm.mul ha.norm).integrable_of_hasCompactSupport hs.norm.mul_left
  let L : Euclidean d →L[ℝ] Euclidean d →L[ℝ] ℝ := -innerSL ℝ
  let g := VectorFourier.fourierSMulRight L a
  have hg : Integrable g := by
    apply (hmom.const_mul (2 * Real.pi * ‖L‖)).mono' ha1.1.fourierSMulRight
    apply Filter.Eventually.of_forall
    intro ξ
    simpa only [mul_assoc] using VectorFourier.norm_fourierSMulRight_le L a ξ
  have hfd : fderiv ℝ (𝓕⁻ a) = 𝓕⁻ g :=
    VectorFourier.fderiv_fourierIntegral L ha1 hmom
  rw [congrFun hfd x, Real.fourierInv_eq_fourier_neg,
    Real.fourier_continuousLinearMap_apply hg, ← Real.fourierInv_eq_fourier_neg]
  apply congrArg (fun b : Euclidean d → ℂ => 𝓕⁻ b x)
  funext ξ
  simp only [g, L, VectorFourier.fourierSMulRight_apply, neg_apply,
    neg_smul, smul_neg, neg_neg]
  rfl

/-- Every fixed physical directional derivative has the same weighted L² membership. -/
theorem compactSymbol_inverse_fderiv_weighted_memLp {d N : ℕ} {a : Euclidean d → ℂ}
    (ha : ContDiff ℝ N a) (hs : HasCompactSupport a) (v : Euclidean d) :
    MemLp (fun x => ((1 + ‖x‖) ^ N : ℝ) • fderiv ℝ (𝓕⁻ a) x v) 2 := by
  let b : Euclidean d → ℂ :=
    fun ξ => (2 * (Real.pi : ℂ) * Complex.I) • (inner ℝ ξ v) • a ξ
  have hb : ContDiff ℝ N b :=
    ((contDiff_id.inner ℝ contDiff_const).smul ha).const_smul _
  have hbs₀ : HasCompactSupport (fun ξ => (inner ℝ ξ v) • a ξ) :=
    HasCompactSupport.smul_left (f := fun ξ => inner ℝ ξ v) hs
  have hbs : HasCompactSupport b :=
    HasCompactSupport.smul_left (f := fun _ => (2 * (Real.pi : ℂ) * Complex.I)) hbs₀
  have h := compactSymbol_inverse_weighted_memLp hb hbs
  convert h using 1
  funext x
  rw [compactSymbol_inverse_fderiv_apply ha.continuous hs]

/-- The bundled Euclidean gradient also has weighted L² membership. -/
theorem inverseKernel_gradient_weighted_memLp {d : ℕ} {χ : Euclidean d → ℝ}
    (hχ : IsCutoff χ) {m : Euclidean d → ℂ} {A : ℝ} (hm : SymbolBound m A) (j : ℤ) :
    MemLp (fun x => ((1 + ‖x‖) ^ order d : ℝ) • gradient (inverseKernel χ m j) x) 2 := by
  apply MemLp.of_eval_piLp
  intro k
  simpa only [gradient, inverseKernel, PiLp.smul_apply, PiLp.toLp_apply] using
    compactSymbol_inverse_fderiv_weighted_memLp (annularSymbol_contDiff hχ hm j)
      (annularSymbol_hasCompactSupport hχ m j) (P102.U3.coordinateVector k)

/-- The reciprocal weight is square integrable precisely in the range used here. -/
theorem inverse_weight_memLp {d N : ℕ} (hN : (d : ℝ) / 2 < N) :
    MemLp (fun x : Euclidean d => ((1 + ‖x‖) ^ N)⁻¹) 2 := by
  have hc : Continuous (fun x : Euclidean d => ((1 + ‖x‖) ^ N)⁻¹) :=
    ((continuous_const.add continuous_norm).pow N).inv₀
      (fun x => pow_ne_zero _ (show 1 + ‖x‖ ≠ 0 by positivity))
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
  have hi : Integrable (fun x : Euclidean d => (1 + ‖x‖) ^ (-(2 * (N : ℝ)))) :=
    integrable_one_add_norm (by simpa using (show (d : ℝ) < 2 * N by linarith))
  convert hi using 1
  funext x
  rw [show -(2 * (N : ℝ)) = -((N * 2 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_neg_natCast, zpow_neg, zpow_natCast, pow_mul, inv_pow]

/-- Cauchy--Schwarz converts weighted L² membership into genuine L¹ integrability. -/
theorem integrable_of_weighted_memLp {d N : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : Euclidean d → E} (hN : (d : ℝ) / 2 < N)
    (hf : MemLp (fun x => ((1 + ‖x‖) ^ N : ℝ) • f x) 2) : Integrable f := by
  have hi : Integrable (fun x : Euclidean d =>
      ((1 + ‖x‖) ^ N)⁻¹ • (((1 + ‖x‖) ^ N : ℝ) • f x)) :=
    memLp_one_iff_integrable.mp ((inverse_weight_memLp hN).smul hf)
  convert hi using 1
  funext x
  rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (by positivity)), one_smul]

/-- The kernels and their gradients are integrable for every individual dyadic scale. -/
theorem inverseKernel_integrable {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ)
    {m : Euclidean d → ℂ} {A : ℝ} (hm : SymbolBound m A) (j : ℤ) :
    Integrable (inverseKernel χ m j) ∧ Integrable (gradient (inverseKernel χ m j)) := by
  exact ⟨integrable_of_weighted_memLp (order_gt_half d) (inverseKernel_weighted_memLp hχ hm j),
    integrable_of_weighted_memLp (order_gt_half d) (inverseKernel_gradient_weighted_memLp hχ hm j)⟩

/-- Fourier inversion identifies the individual integral kernels pointwise. -/
theorem inverseKernel_fourier {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ)
    {m : Euclidean d → ℂ} {A : ℝ} (hm : SymbolBound m A) (j : ℤ) :
    𝓕 (inverseKernel χ m j) = annularSymbol χ m j := by
  have hF : Integrable (𝓕 (annularSymbol χ m j)) := by
    have h := (inverseKernel_integrable hχ hm j).1.comp_smul (by norm_num : (-1 : ℝ) ≠ 0)
    simpa only [neg_one_smul, inverseKernel, Real.fourierInv_eq_fourier_neg, neg_neg] using h
  exact (annularSymbol_contDiff hχ hm j).continuous.fourier_fourierInv_eq
    (annularSymbol_integrable hχ hm j) hF

/-- Normalized positive dilation transports the Fourier integral to the reciprocal
frequency dilation. This identity holds even for totalized integrals. -/
theorem fourier_normalized_dilation {d : ℕ} (f : Euclidean d → ℂ)
    {s : ℝ} (hs : 0 < s) (ξ : Euclidean d) :
    𝓕 (fun x => (s ^ d : ℝ) • f (s • x)) ξ = 𝓕 f (s⁻¹ • ξ) := by
  have he (x : Euclidean d) : inner ℝ (s • x) (s⁻¹ • ξ) = inner ℝ x ξ := by
    rw [real_inner_smul_left, real_inner_smul_right]
    simp [hs.ne']
  simp only [Real.fourier_eq]
  calc
    (∫ x, Real.fourierChar (-inner ℝ x ξ) • ((s ^ d : ℝ) • f (s • x))) =
        (s ^ d : ℝ) • ∫ x, Real.fourierChar (-inner ℝ (s • x) (s⁻¹ • ξ)) • f (s • x) := by
      rw [← integral_smul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [he, smul_comm]
    _ = (s ^ d : ℝ) • ((s ^ d)⁻¹ •
        ∫ x, Real.fourierChar (-inner ℝ x (s⁻¹ • ξ)) • f x) := by
      congr 1
      simpa using Measure.integral_comp_smul_of_nonneg volume
        (fun x : Euclidean d => Real.fourierChar (-inner ℝ x (s⁻¹ • ξ)) • f x) s (hR := hs.le)
    _ = _ := by rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hs.ne'), one_smul]

theorem dilatedKernel_integrable {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ)
    {m : Euclidean d → ℂ} {A : ℝ} (hm : SymbolBound m A) (j : ℤ) :
    Integrable (dilatedKernel χ m j) :=
  ((inverseKernel_integrable hχ hm j).1.comp_smul (scale_ne_zero j)).smul (scale j ^ d)

theorem dilatedKernel_fourier {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ)
    {m : Euclidean d → ℂ} {A : ℝ} (hm : SymbolBound m A) (j : ℤ) (ξ : Euclidean d) :
    𝓕 (dilatedKernel χ m j) ξ = m ξ * (block χ j ξ : ℂ) := by
  change 𝓕 (fun x => (scale j ^ d : ℝ) • inverseKernel χ m j (scale j • x)) ξ = _
  rw [fourier_normalized_dilation _ (scale_pos j), inverseKernel_fourier hχ hm j,
    ← scale_neg, annularSymbol_rescale]

/-- The apparent singularity of the finite symbol at zero is removed by each block. -/
theorem finiteSymbol_eq_sum {d : ℕ} (χ : Euclidean d → ℝ)
    (m : Euclidean d → ℂ) (J : Finset ℤ) :
    finiteSymbol χ m J = fun ξ =>
      ∑ j ∈ J, annularSymbol χ m j (scale (-j) • ξ) := by
  funext ξ
  simp only [finiteSymbol, Complex.ofReal_sum, Finset.mul_sum, annularSymbol_rescale]

/-- In particular the finite multiplier is measurable without any hypothesis on m(0). -/
theorem finiteSymbol_contDiff {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ)
    {m : Euclidean d → ℂ} {A : ℝ} (hm : SymbolBound m A) (J : Finset ℤ) :
    ContDiff ℝ (order d) (finiteSymbol χ m J) := by
  classical
  rw [finiteSymbol_eq_sum]
  exact ContDiff.sum fun j _ => (annularSymbol_contDiff hχ hm j).comp
    (contDiff_id.const_smul (scale (-j)))

theorem finiteKernel_integrable {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ)
    {m : Euclidean d → ℂ} {A : ℝ} (hm : SymbolBound m A) (J : Finset ℤ) :
    Integrable (finiteKernel χ m J) := by
  exact integrable_finsetSum J fun j _ => dilatedKernel_integrable hχ hm j

/-- Every finite sum has exactly the prescribed continuous Fourier representative. -/
theorem finiteKernel_fourier {d : ℕ} {χ : Euclidean d → ℝ} (hχ : IsCutoff χ)
    {m : Euclidean d → ℂ} {A : ℝ} (hm : SymbolBound m A) (J : Finset ℤ) (ξ : Euclidean d) :
    𝓕 (finiteKernel χ m J) ξ = finiteSymbol χ m J ξ := by
  have hsum : 𝓕 (finiteKernel χ m J) ξ = ∑ j ∈ J, 𝓕 (dilatedKernel χ m j) ξ := by
    simp only [Real.fourier_eq, finiteKernel, Finset.smul_sum]
    apply integral_finsetSum
    intro j _
    exact (Real.fourierIntegral_convergent_iff ξ).mpr (dilatedKernel_integrable hχ hm j)
  rw [hsum, finiteSymbol, Complex.ofReal_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => dilatedKernel_fourier hχ hm j ξ

/-- Multiplication by a bounded measurable symbol on L². The norm estimate below
uses the actual representative, so it does not totalize an infinite norm. -/
def boundedMultiplication {d : ℕ} (b : Euclidean d → ℂ) (B : ℝ)
    (hb : AEStronglyMeasurable b volume) (hB : ∀ ξ, ‖b ξ‖ ≤ B) :
    Lp (α := Euclidean d) ℂ 2 volume →L[ℂ] Lp (α := Euclidean d) ℂ 2 volume :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume (⊤ : ENNReal) 2 2
    ((memLp_top_of_bound hb B (Filter.Eventually.of_forall hB)).toLp b)

theorem boundedMultiplication_apply {d : ℕ} (b : Euclidean d → ℂ) (B : ℝ)
    (hb : AEStronglyMeasurable b volume) (hB : ∀ ξ, ‖b ξ‖ ≤ B)
    (f : Lp (α := Euclidean d) ℂ 2 volume) :
    (boundedMultiplication b B hb hB f : Euclidean d → ℂ) =ᵐ[volume]
      fun ξ => b ξ * f ξ := by
  have hc := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    ((memLp_top_of_bound hb B (Filter.Eventually.of_forall hB)).toLp b) f (r := 2)
  filter_upwards [hc, (memLp_top_of_bound hb B
    (Filter.Eventually.of_forall hB)).coeFn_toLp] with ξ hξ hbξ
  simpa only [boundedMultiplication, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.mul_apply', hbξ] using hξ

theorem boundedMultiplication_norm_le {d : ℕ} (b : Euclidean d → ℂ) (B : ℝ)
    (hB0 : 0 ≤ B) (hb : AEStronglyMeasurable b volume) (hB : ∀ ξ, ‖b ξ‖ ≤ B) :
    ‖boundedMultiplication b B hb hB‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB0
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedMultiplication_apply b B hb hB f] with ξ hξ
  rw [hξ, norm_mul]
  exact mul_le_mul_of_nonneg_right (hB ξ) (norm_nonneg _)

/-- The finite dyadic symbols already define uniformly bounded L² multipliers;
identifying their convolution kernels is a separate analytic step. -/
theorem finiteL2Multiplier_exists {d : ℕ} (hd : 1 ≤ d) {χ : Euclidean d → ℝ}
    (hχ : IsCutoff χ) {m : Euclidean d → ℂ} {A : ℝ} (hm : SymbolBound m A)
    (J : Finset ℤ) :
    ∃ T : Lp (α := Euclidean d) ℂ 2 volume →L[ℂ] Lp (α := Euclidean d) ℂ 2 volume,
      ‖T‖ ≤ 2 * A ∧ ∀ f : Lp (α := Euclidean d) ℂ 2 volume,
        ((𝓕 (T f) : Lp (α := Euclidean d) ℂ 2 volume) : Euclidean d → ℂ)
          =ᵐ[volume] (fun ξ => finiteSymbol χ m J ξ *
            (𝓕 f : Lp (α := Euclidean d) ℂ 2 volume) ξ) := by
  let F := Lp.fourierTransformₗᵢ (Euclidean d) ℂ
  have hb : AEStronglyMeasurable (finiteSymbol χ m J) volume :=
    (finiteSymbol_contDiff hχ hm J).continuous.aestronglyMeasurable
  have hB := finiteSymbol_norm_le hd hχ hm J
  have hA : 0 ≤ 2 * A := mul_nonneg (by norm_num) (symbol_bound_nonneg hd hm)
  let M := boundedMultiplication (finiteSymbol χ m J) (2 * A) hb hB
  let T := F.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    M ∘L F.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨T, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ hA
    intro f
    change ‖F.symm (M (F f))‖ ≤ 2 * A * ‖f‖
    rw [F.symm.norm_map]
    calc
      ‖M (F f)‖ ≤ ‖M‖ * ‖F f‖ := M.le_opNorm _
      _ ≤ (2 * A) * ‖F f‖ := mul_le_mul_of_nonneg_right
        (boundedMultiplication_norm_le _ _ hA hb hB)
        (norm_nonneg _)
      _ = (2 * A) * ‖f‖ := by rw [F.norm_map]
  · intro f
    change (F (F.symm (M (F f))) : Euclidean d → ℂ) =ᵐ[volume] _
    rw [F.apply_symm_apply]
    exact boundedMultiplication_apply _ _ hb hB (F f)

private theorem convYoung {d : ℕ} {K : Euclidean d → ℂ} (hK : Integrable K)
    (f : Lp (α := Euclidean d) ℂ 2 volume) :
    P102.U2.YoungExpected.Result volume 1 2 2 K f := by
  exact P102.U2.Young.young volume (by norm_num) (by norm_num) (by norm_num)
    (by simp) (memLp_one_iff_integrable.mpr hK) (Lp.memLp f)

private def convL2 {d : ℕ} {K : Euclidean d → ℂ} (hK : Integrable K)
    (f : Lp (α := Euclidean d) ℂ 2 volume) : Lp (α := Euclidean d) ℂ 2 volume :=
  (convYoung hK f).2.1.toLp (fun x => ∫ y, K (x-y) * f y)

private theorem convL2_ae {d : ℕ} {K : Euclidean d → ℂ} (hK : Integrable K)
    (f : Lp (α := Euclidean d) ℂ 2 volume) :
    (convL2 hK f : Euclidean d → ℂ) =ᵐ[volume] fun x => ∫ y, K (x-y) * f y :=
  (convYoung hK f).2.1.coeFn_toLp

private theorem convL2_add {d : ℕ} {K : Euclidean d → ℂ} (hK : Integrable K)
    (f g : Lp (α := Euclidean d) ℂ 2 volume) :
    convL2 hK (f+g) = convL2 hK f + convL2 hK g := by
  apply Lp.ext
  have hrep := P102.U2.Young.integralConvolution_congr volume
    (Filter.EventuallyEq.rfl : K =ᵐ[volume] K) (Lp.coeFn_add f g)
  filter_upwards [convL2_ae hK (f+g), convL2_ae hK f, convL2_ae hK g,
    Lp.coeFn_add (convL2 hK f) (convL2 hK g), (convYoung hK f).1,
    (convYoung hK g).1] with x hfg hf hg ha hif hig
  rw [hfg, ha]
  simp only [Pi.add_apply]
  rw [hf, hg]
  change P102.U2.Young.integralConvolution volume K (⇑(f+g)) x = _
  rw [hrep]
  change (∫ y, K (x-y) * (f y + g y)) = _
  simp_rw [mul_add]
  exact integral_add hif hig

private theorem convL2_smul {d : ℕ} {K : Euclidean d → ℂ} (hK : Integrable K)
    (c : ℂ) (f : Lp (α := Euclidean d) ℂ 2 volume) :
    convL2 hK (c • f) = c • convL2 hK f := by
  apply Lp.ext
  have hrep := P102.U2.Young.integralConvolution_congr volume
    (Filter.EventuallyEq.rfl : K =ᵐ[volume] K) (Lp.coeFn_smul c f)
  filter_upwards [convL2_ae hK (c • f), convL2_ae hK f,
    Lp.coeFn_smul c (convL2 hK f)] with x hcf hf hs
  rw [hcf, hs]
  simp only [Pi.smul_apply]
  rw [hf]
  change P102.U2.Young.integralConvolution volume K (⇑(c • f)) x = _
  rw [hrep]
  change (∫ y, K (x-y) * (c * f y)) = c * ∫ y, K (x-y) * f y
  simp_rw [← mul_assoc, mul_comm (K _ : ℂ) c, mul_assoc]
  exact integral_const_mul c _

private def convolutionL2 {d : ℕ} {K : Euclidean d → ℂ} (hK : Integrable K) :
    Lp (α := Euclidean d) ℂ 2 volume →L[ℂ] Lp (α := Euclidean d) ℂ 2 volume :=
  LinearMap.mkContinuous
    { toFun := convL2 hK
      map_add' := convL2_add hK
      map_smul' := convL2_smul hK }
    (eLpNorm K 1 volume).toReal (by
      intro f
      change ‖(convYoung hK f).2.1.toLp _‖ ≤ _
      rw [Lp.norm_toLp, Lp.norm_def]
      rw [← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top (memLp_one_iff_integrable.mpr hK).eLpNorm_ne_top (Lp.memLp f).eLpNorm_ne_top) (convYoung hK f).2.2.1)

private theorem convolutionL2_fourier {d : ℕ} {K : Euclidean d → ℂ} (hK : Integrable K)
    (f : Lp (α := Euclidean d) ℂ 2 volume) (hf : Integrable (f : Euclidean d → ℂ)) :
    ((𝓕 (convolutionL2 hK f) : Lp (α := Euclidean d) ℂ 2 volume) : Euclidean d → ℂ)
      =ᵐ[volume] fun ξ => 𝓕 K ξ * (𝓕 f : Lp (α := Euclidean d) ℂ 2 volume) ξ := by
  have hc := P102.U3.FourierConvolution.fourier_convolution (Euclidean d) K f hK hf
  have hc1 : Integrable (convolutionL2 hK f : Euclidean d → ℂ) :=
    hc.2.1.congr (convL2_ae hK f).symm
  have hFc := P102.U3.Plancherel.fourier_ae_integral (convolutionL2 hK f) hc1
  have hFf := P102.U3.Plancherel.fourier_ae_integral f hf
  have hpoint := (hc.2.2.2.2.1 (convolutionL2 hK f) (convL2_ae hK f)).2
  simp only [P102.U3.FourierConvolution.transform_eq_fourier] at hpoint
  filter_upwards [hFc, hFf] with ξ hcξ hfξ
  rw [hcξ, hpoint, hfξ]

/-- An L² Fourier multiplier whose symbol is the Fourier transform of an L¹
kernel has the actual integral-convolution representative for every L² input. -/
theorem convolution_representation_of_multiplier {d : ℕ}
    {K : Euclidean d → ℂ} (hK : Integrable K)
    {b : Euclidean d → ℂ} (hb : ∀ ξ, 𝓕 K ξ = b ξ)
    (T : Lp (α := Euclidean d) ℂ 2 volume →L[ℂ] Lp (α := Euclidean d) ℂ 2 volume)
    (hT : ∀ f : Lp (α := Euclidean d) ℂ 2 volume,
      ((𝓕 (T f) : Lp (α := Euclidean d) ℂ 2 volume) : Euclidean d → ℂ)
        =ᵐ[volume] fun ξ => b ξ * (𝓕 f : Lp (α := Euclidean d) ℂ 2 volume) ξ)
    (f : Lp (α := Euclidean d) ℂ 2 volume) :
    (∀ᵐ x, Integrable (fun y => K (x-y) * f y)) ∧
    (T f : Euclidean d → ℂ) =ᵐ[volume] (fun x => ∫ y, K (x-y) * f y) := by
  have heq : (convolutionL2 hK : Lp (α := Euclidean d) ℂ 2 volume →
      Lp (α := Euclidean d) ℂ 2 volume) = T := by
    apply (SchwartzMap.denseRange_toLpCLM (E := Euclidean d) (F := ℂ)
      (p := 2) ENNReal.ofNat_ne_top).equalizer (convolutionL2 hK).continuous T.continuous
    funext ψ
    change convolutionL2 hK (ψ.toLp 2) = T (ψ.toLp 2)
    apply (Lp.fourierTransformₗᵢ (Euclidean d) ℂ).injective
    apply Lp.ext
    have hψ1 : Integrable (ψ.toLp 2 volume : Euclidean d → ℂ) :=
      ψ.integrable.congr (ψ.coeFn_toLp 2 volume).symm
    filter_upwards [convolutionL2_fourier hK (ψ.toLp 2) hψ1, hT (ψ.toLp 2)] with ξ hC hTξ
    change (𝓕 (convolutionL2 hK (ψ.toLp 2)) : Lp (α := Euclidean d) ℂ 2 volume) ξ =
      (𝓕 (T (ψ.toLp 2)) : Lp (α := Euclidean d) ℂ 2 volume) ξ
    rw [hC, hTξ, hb]
  refine ⟨(convYoung hK f).1, ?_⟩
  rw [← congrFun heq f]
  exact convL2_ae hK f


/-- Finite kernel multipliers act by their absolutely existing convolution integrals. -/
theorem finiteL2Multiplier_convolution_exists {d : ℕ} (hd : 1 ≤ d) {χ : Euclidean d → ℝ}
    (hχ : IsCutoff χ) {m : Euclidean d → ℂ} {A : ℝ} (hm : SymbolBound m A)
    (J : Finset ℤ) :
    ∃ T : Lp (α := Euclidean d) ℂ 2 volume →L[ℂ] Lp (α := Euclidean d) ℂ 2 volume,
      ‖T‖ ≤ 2 * A ∧ ∀ f : Lp (α := Euclidean d) ℂ 2 volume,
        ((𝓕 (T f) : Lp (α := Euclidean d) ℂ 2 volume) : Euclidean d → ℂ)
          =ᵐ[volume] (fun ξ => finiteSymbol χ m J ξ *
            (𝓕 f : Lp (α := Euclidean d) ℂ 2 volume) ξ) ∧
        (∀ᵐ x, Integrable (fun y => finiteKernel χ m J (x-y) * f y)) ∧
        (T f : Euclidean d → ℂ) =ᵐ[volume]
          (fun x => ∫ y, finiteKernel χ m J (x-y) * f y) := by
  obtain ⟨T, hnorm, hT⟩ := finiteL2Multiplier_exists hd hχ hm J
  exact ⟨T, hnorm, fun f => ⟨hT f, convolution_representation_of_multiplier
    (finiteKernel_integrable hχ hm J) (finiteKernel_fourier hχ hm J) T hT f⟩⟩



/-- The integration by parts identity for finite C^N compact symbols. -/
theorem compactSymbol_fourier_derivative_apply_eq {d N : ℕ} {a : Euclidean d → ℂ}
    (ha : ContDiff ℝ N a) (hs : HasCompactSupport a) {n : ℕ} (hn : n ≤ N)
    (v : Fin n → Euclidean d) :
    𝓕 (fun ξ => iteratedFDeriv ℝ n a ξ v) =
      fun x => (-(2 * (Real.pi : ℂ) * Complex.I)) ^ n •
        (∏ i, -inner ℝ x (v i)) • 𝓕 a x := by
  funext x
  rw [← Real.fourier_continuousMultilinearMap_apply
    (compactSymbol_derivative_integrable ha hs hn),
    Real.fourier_iteratedFDeriv (N := (N : ℕ∞)) ha
      (fun k hk => compactSymbol_derivative_integrable ha hs (by exact_mod_cast hk))
      (by exact_mod_cast hn)]
  simp only [VectorFourier.fourierPowSMulRight_apply, neg_apply]
  rfl

/-- Quantitative Plancherel for every ordered monomial; signs disappear in the norm. -/
theorem compactSymbol_fourier_monomial_lpNorm_eq {d N : ℕ} {a : Euclidean d → ℂ}
    (ha : ContDiff ℝ N a) (hs : HasCompactSupport a) {n : ℕ} (hn : n ≤ N)
    (v : Fin n → Euclidean d) :
    (2 * Real.pi) ^ n * lpNorm (fun x => (∏ i, -inner ℝ x (v i)) • 𝓕 a x) 2 volume =
      lpNorm (fun ξ => iteratedFDeriv ℝ n a ξ v) 2 volume := by
  have hdi := compactSymbol_derivative_integrable ha hs hn
  have hdv : Integrable (fun ξ => iteratedFDeriv ℝ n a ξ v) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euclidean d) ℂ v).integrable_comp hdi
  have he := eLpNorm_fourier_eq (compactSymbol_derivative_memLp ha hs hn v) hdv
  rw [compactSymbol_fourier_derivative_apply_eq ha hs hn v] at he
  change lpNorm ((-(2 * (Real.pi : ℂ) * Complex.I)) ^ n •
      (fun x => (∏ i, -inner ℝ x (v i)) • 𝓕 a x)) 2 volume = _ at he
  rw [lpNorm_const_smul] at he
  simpa only [toReal_eLpNorm, NNReal.coe_mk, coe_nnnorm, norm_pow, norm_neg, norm_mul,
    Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le,
    Complex.norm_I, mul_one] using he

/-- The Fourier constant has modulus at least one, giving a convenient weaker bound. -/
theorem compactSymbol_fourier_monomial_lpNorm_le {d N : ℕ} {a : Euclidean d → ℂ}
    (ha : ContDiff ℝ N a) (hs : HasCompactSupport a) {n : ℕ} (hn : n ≤ N)
    (v : Fin n → Euclidean d) :
    lpNorm (fun x => (∏ i, -inner ℝ x (v i)) • 𝓕 a x) 2 volume ≤
      lpNorm (fun ξ => iteratedFDeriv ℝ n a ξ v) 2 volume := by
  rw [← compactSymbol_fourier_monomial_lpNorm_eq ha hs hn v]
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
  exact le_mul_of_one_le_left lpNorm_nonneg (one_le_pow₀ hpi)

/-- Radial weighted L² is controlled by the ordered coordinate derivatives. -/
theorem compactSymbol_fourier_norm_pow_lpNorm_le {d N : ℕ} {a : Euclidean d → ℂ}
    (ha : ContDiff ℝ N a) (hs : HasCompactSupport a) {n : ℕ} (hn : n ≤ N) :
    lpNorm (fun x => ‖x‖ ^ n * ‖𝓕 a x‖) 2 volume ≤
      ∑ β : Fin n → Fin d,
        lpNorm (fun ξ => iteratedFDeriv ℝ n a ξ (P102.U3.coordinateVector ∘ β)) 2 volume := by
  let g : (Fin n → Fin d) → Euclidean d → ℝ := fun β x =>
    ‖(∏ i, -inner ℝ x (P102.U3.coordinateVector (β i))) • 𝓕 a x‖
  have hg (β : Fin n → Fin d) : MemLp (g β) 2 :=
    (compactSymbol_fourier_monomial_memLp ha hs hn
      (P102.U3.coordinateVector ∘ β)).norm
  have hgs : MemLp (∑ β, g β) 2 := by
    simpa only [Finset.sum_fn] using
      memLp_finsetSum (Finset.univ : Finset (Fin n → Fin d)) (fun β _ => hg β)
  calc
    lpNorm (fun x => ‖x‖ ^ n * ‖𝓕 a x‖) 2 volume ≤ lpNorm (∑ β, g β) 2 volume := by
      apply lpNorm_mono_real hgs
      intro x
      simp only [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg x) n) (norm_nonneg _))]
      simp only [Finset.sum_apply]
      change ‖x‖ ^ n * ‖𝓕 a x‖ ≤ ∑ β, g β x
      have he : ∑ β, g β x =
          (∑ k : Fin d, ‖inner ℝ x (P102.U3.coordinateVector k)‖) ^ n * ‖𝓕 a x‖ := by
        simp only [g, norm_smul, norm_prod, norm_neg]
        rw [Fintype.sum_pow, Finset.sum_mul]
      rw [he]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg x) (norm_le_sum_coordinates x) n) (norm_nonneg _)
    _ ≤ ∑ β, lpNorm (g β) 2 volume := lpNorm_sum_le (fun β _ => hg β) (by norm_num)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro β _
      dsimp only [g]
      have hnorm := lpNorm_norm (compactSymbol_fourier_monomial_memLp ha hs hn
        (P102.U3.coordinateVector ∘ β)).aestronglyMeasurable (2 : ENNReal)
      simp only [Function.comp_apply] at hnorm
      rw [hnorm]
      exact compactSymbol_fourier_monomial_lpNorm_le ha hs hn
        (P102.U3.coordinateVector ∘ β)

/-- A quantitative weighted estimate in terms of just the zeroth and Nth derivatives. -/
theorem compactSymbol_fourier_weighted_lpNorm_le {d N : ℕ} {a : Euclidean d → ℂ}
    (ha : ContDiff ℝ N a) (hs : HasCompactSupport a) :
    lpNorm (fun x => ((1 + ‖x‖) ^ N : ℝ) • 𝓕 a x) 2 volume ≤
      2 ^ (N - 1) * (lpNorm a 2 volume +
        ∑ β : Fin N → Fin d,
          lpNorm (fun ξ => iteratedFDeriv ℝ N a ξ (P102.U3.coordinateVector ∘ β)) 2 volume) := by
  have h0 := memLp_fourier (ha.continuous.memLp_of_hasCompactSupport hs)
    (ha.continuous.integrable_of_hasCompactSupport hs)
  have hp := compactSymbol_fourier_norm_pow_memLp ha hs (le_refl N)
  have hc : 0 ≤ (2 : ℝ) ^ (N - 1) := by positivity
  calc
    lpNorm (fun x => ((1 + ‖x‖) ^ N : ℝ) • 𝓕 a x) 2 volume ≤
        lpNorm (((2 : ℝ) ^ (N - 1)) •
          ((fun x => ‖𝓕 a x‖) + fun x => ‖x‖ ^ N * ‖𝓕 a x‖)) 2 volume := by
      apply lpNorm_mono_real ((h0.norm.add hp).const_smul _)
      intro x
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, norm_smul,
        Real.norm_of_nonneg (pow_nonneg (by positivity : 0 ≤ 1 + ‖x‖) N)]
      calc
        (1 + ‖x‖) ^ N * ‖𝓕 a x‖ ≤
            (2 ^ (N - 1) * (1 ^ N + ‖x‖ ^ N)) * ‖𝓕 a x‖ :=
          mul_le_mul_of_nonneg_right (add_pow_le (by norm_num) (norm_nonneg x) N) (norm_nonneg _)
        _ = _ := by rw [one_pow]; ring
    _ = (2 : ℝ) ^ (N - 1) *
        lpNorm ((fun x => ‖𝓕 a x‖) + fun x => ‖x‖ ^ N * ‖𝓕 a x‖) 2 volume := by
      rw [lpNorm_const_smul, coe_nnnorm, Real.norm_of_nonneg hc]
    _ ≤ (2 : ℝ) ^ (N - 1) * (lpNorm (fun x => ‖𝓕 a x‖) 2 volume +
        lpNorm (fun x => ‖x‖ ^ N * ‖𝓕 a x‖) 2 volume) :=
      mul_le_mul_of_nonneg_left (lpNorm_add_le h0.norm (by norm_num)) hc
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hc
      apply add_le_add
      · rw [lpNorm_norm h0.aestronglyMeasurable]
        exact le_of_eq (eLpNorm_fourier_eq (ha.continuous.memLp_of_hasCompactSupport hs)
          (ha.continuous.integrable_of_hasCompactSupport hs))
      · exact compactSymbol_fourier_norm_pow_lpNorm_le ha hs (le_refl N)

/-- Reflection preserves the radial weighted L² norm for the positive inverse integral. -/
theorem compactSymbol_inverse_weighted_lpNorm_le {d N : ℕ} {a : Euclidean d → ℂ}
    (ha : ContDiff ℝ N a) (hs : HasCompactSupport a) :
    lpNorm (fun x => ((1 + ‖x‖) ^ N : ℝ) • 𝓕⁻ a x) 2 volume ≤
      2 ^ (N - 1) * (lpNorm a 2 volume +
        ∑ β : Fin N → Fin d,
          lpNorm (fun ξ => iteratedFDeriv ℝ N a ξ (P102.U3.coordinateVector ∘ β)) 2 volume) := by
  have h := eLpNorm_comp_measurePreserving
    (compactSymbol_fourier_weighted_memLp ha hs).aestronglyMeasurable
    (Measure.measurePreserving_neg (volume : Measure (Euclidean d))) (p := (2 : ENNReal))
  have he := congrArg ENNReal.toReal h
  simp only [Function.comp_def, norm_neg, ← Real.fourierInv_eq_fourier_neg, toReal_eLpNorm] at he
  rw [he]
  exact compactSymbol_fourier_weighted_lpNorm_le ha hs

/-- Uniform frequency derivative L² bounds give an explicit common weighted bound. -/
theorem compactSymbol_inverse_weighted_lpNorm_le_of_derivative_bound
    {d N : ℕ} {a : Euclidean d → ℂ} (ha : ContDiff ℝ N a)
    (hs : HasCompactSupport a) {B : ℝ}
    (h0 : lpNorm a 2 volume ≤ B)
    (hN : ∀ β : Fin N → Fin d,
      lpNorm (fun ξ => iteratedFDeriv ℝ N a ξ (P102.U3.coordinateVector ∘ β)) 2 volume ≤ B) :
    lpNorm (fun x => ((1 + ‖x‖) ^ N : ℝ) • 𝓕⁻ a x) 2 volume ≤
      2 ^ (N - 1) * (1 + (d : ℝ) ^ N) * B := by
  calc
    _ ≤ 2 ^ (N - 1) * (lpNorm a 2 volume +
        ∑ β : Fin N → Fin d,
          lpNorm (fun ξ => iteratedFDeriv ℝ N a ξ (P102.U3.coordinateVector ∘ β)) 2 volume) :=
      compactSymbol_inverse_weighted_lpNorm_le ha hs
    _ ≤ 2 ^ (N - 1) * (B + ∑ _β : Fin N → Fin d, B) := by
      exact mul_le_mul_of_nonneg_left (add_le_add h0 (Finset.sum_le_sum (fun β _ => hN β)))
        (by positivity)
    _ = _ := by simp; ring

/-- The Euclidean norm of a complex vector is bounded by the sum of coordinate norms. -/
theorem euclidean_complex_norm_le_sum {d : ℕ} (z : EuclideanSpace ℂ (Fin d)) :
    ‖z‖ ≤ ∑ k : Fin d, ‖z k‖ := by
  classical
  have hz : ∑ k : Fin d, PiLp.single 2 k (z k) = z := by ext i; simp
  calc
    ‖z‖ = ‖∑ k : Fin d, PiLp.single 2 k (z k)‖ := congrArg norm hz.symm
    _ ≤ ∑ k : Fin d, ‖(PiLp.single 2 k (z k) : EuclideanSpace ℂ (Fin d))‖ := norm_sum_le _ _
    _ = _ := by simp only [PiLp.norm_single]

/-- A direction derivative of the inverse integral has an explicit weighted bound. -/
theorem compactSymbol_inverse_fderiv_weighted_lpNorm_le_of_derivative_bound
    {d N : ℕ} {a : Euclidean d → ℂ} (ha : ContDiff ℝ N a)
    (hs : HasCompactSupport a) (v : Euclidean d) {B : ℝ}
    (h0 : lpNorm (fun ξ => (2 * (Real.pi : ℂ) * Complex.I) • (inner ℝ ξ v) • a ξ) 2 volume ≤ B)
    (hN : ∀ β : Fin N → Fin d,
      lpNorm (fun ξ => iteratedFDeriv ℝ N
        (fun ξ => (2 * (Real.pi : ℂ) * Complex.I) • (inner ℝ ξ v) • a ξ)
        ξ (P102.U3.coordinateVector ∘ β)) 2 volume ≤ B) :
    lpNorm (fun x => ((1 + ‖x‖) ^ N : ℝ) • fderiv ℝ (𝓕⁻ a) x v) 2 volume ≤
      2 ^ (N - 1) * (1 + (d : ℝ) ^ N) * B := by
  let b : Euclidean d → ℂ :=
    fun ξ => (2 * (Real.pi : ℂ) * Complex.I) • (inner ℝ ξ v) • a ξ
  have hb : ContDiff ℝ N b :=
    ((contDiff_id.inner ℝ contDiff_const).smul ha).const_smul _
  have hbs₀ : HasCompactSupport (fun ξ => (inner ℝ ξ v) • a ξ) :=
    HasCompactSupport.smul_left (f := fun ξ => inner ℝ ξ v) hs
  have hbs : HasCompactSupport b :=
    HasCompactSupport.smul_left (f := fun _ => (2 * (Real.pi : ℂ) * Complex.I)) hbs₀
  have h := compactSymbol_inverse_weighted_lpNorm_le_of_derivative_bound hb hbs h0 hN
  have he : (fun x => ((1 + ‖x‖) ^ N : ℝ) • fderiv ℝ (𝓕⁻ a) x v) =
      fun x => ((1 + ‖x‖) ^ N : ℝ) • 𝓕⁻ b x := by
    funext x
    rw [compactSymbol_inverse_fderiv_apply ha.continuous hs]
  rw [he]
  exact h

/-- A finite support envelope gives a uniform L² bound without evaluating its volume. -/
theorem lpNorm_le_of_support_subset_bound {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {f : Euclidean d → E} {s : Set (Euclidean d)} (hsm : MeasurableSet s)
    (hsv : volume s ≠ (⊤ : ENNReal)) (hf : AEStronglyMeasurable f volume)
    (hs : Function.support f ⊆ s) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, ‖f x‖ ≤ B) :
    lpNorm f 2 volume ≤ B * lpNorm (s.indicator (fun _ => (1 : ℝ))) 2 volume := by
  have hg : MemLp (s.indicator (fun _ => (1 : ℝ))) 2 volume :=
    memLp_indicator_const 2 hsm.nullMeasurableSet 1 (Or.inr hsv)
  calc
    lpNorm f 2 volume ≤ lpNorm (B • s.indicator (fun _ => (1 : ℝ))) 2 volume := by
      apply lpNorm_mono_real (hg.const_smul B)
      intro x
      by_cases hx : x ∈ s
      · simpa only [Pi.smul_apply, Set.indicator_of_mem hx, smul_eq_mul, mul_one] using hb x
      · have hx0 : f x = 0 := by
          by_contra hf
          exact hx (hs hf)
        simp [hx, hx0]
    _ = _ := by rw [lpNorm_const_smul, coe_nnnorm, Real.norm_of_nonneg hB]

/-- Fixed compact frequency support bounds every ordered coordinate derivative in L². -/
theorem compactSymbol_derivative_lpNorm_le_of_bound {d N : ℕ} {a : Euclidean d → ℂ}
    (ha : ContDiff ℝ N a) (hs : tsupport a ⊆ Metric.closedBall 0 2)
    {n : ℕ} (hn : n ≤ N) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ξ, ‖iteratedFDeriv ℝ n a ξ‖ ≤ B)
    (β : Fin n → Fin d) :
    lpNorm (fun ξ => iteratedFDeriv ℝ n a ξ (P102.U3.coordinateVector ∘ β)) 2 volume ≤
      B * lpNorm ((Metric.closedBall (0 : Euclidean d) 2).indicator (fun _ => (1 : ℝ))) 2 volume := by
  have hc := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euclidean d) ℂ
      (P102.U3.coordinateVector ∘ β)).continuous.comp
    (ha.continuous_iteratedFDeriv (by exact_mod_cast hn))
  apply lpNorm_le_of_support_subset_bound measurableSet_closedBall
    (measure_closedBall_lt_top.ne) hc.aestronglyMeasurable
  · intro ξ hξ
    apply hs
    apply support_iteratedFDeriv_subset (𝕜 := ℝ) (f := a) n
    intro h0
    apply hξ
    change iteratedFDeriv ℝ n a ξ (P102.U3.coordinateVector ∘ β) = 0
    rw [h0]
    simp
  · exact hB
  · intro ξ
    calc
      ‖iteratedFDeriv ℝ n a ξ (P102.U3.coordinateVector ∘ β)‖ ≤
          ‖iteratedFDeriv ℝ n a ξ‖ * ∏ i, ‖P102.U3.coordinateVector (β i)‖ :=
        (iteratedFDeriv ℝ n a ξ).le_opNorm _
      _ = ‖iteratedFDeriv ℝ n a ξ‖ := by
        simp [P102.U3.coordinateVector, EuclideanSpace.basisFun]
      _ ≤ B := hb ξ

/-- The Euclidean gradient's weighted norm is controlled by its coordinate norms. -/
theorem weighted_gradient_lpNorm_le {d N : ℕ} {f : Euclidean d → ℂ}
    (hf : ∀ k : Fin d,
      MemLp (fun x => ((1 + ‖x‖) ^ N : ℝ) • fderiv ℝ f x (P102.U3.coordinateVector k)) 2) :
    lpNorm (fun x => ((1 + ‖x‖) ^ N : ℝ) • gradient f x) 2 volume ≤
      ∑ k : Fin d,
        lpNorm (fun x => ((1 + ‖x‖) ^ N : ℝ) • fderiv ℝ f x (P102.U3.coordinateVector k)) 2 volume := by
  let g : Fin d → Euclidean d → ℝ := fun k x =>
    ‖((1 + ‖x‖) ^ N : ℝ) • fderiv ℝ f x (P102.U3.coordinateVector k)‖
  have hg (k : Fin d) : MemLp (g k) 2 := (hf k).norm
  have hgs : MemLp (∑ k, g k) 2 := by
    simpa only [Finset.sum_fn] using
      memLp_finsetSum (Finset.univ : Finset (Fin d)) (fun k _ => hg k)
  calc
    _ ≤ lpNorm (∑ k, g k) 2 volume := by
      apply lpNorm_mono_real hgs
      intro x
      simpa only [Finset.sum_apply, gradient, PiLp.smul_apply, PiLp.toLp_apply, g] using
        euclidean_complex_norm_le_sum (((1 + ‖x‖) ^ N : ℝ) • gradient f x)
    _ ≤ ∑ k, lpNorm (g k) 2 volume := lpNorm_sum_le (fun k _ => hg k) (by norm_num)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      exact lpNorm_norm (hf k).aestronglyMeasurable 2

/-- A single bound for all directional components gives a dimension-only loss. -/
theorem weighted_gradient_lpNorm_le_of_bound {d N : ℕ} {f : Euclidean d → ℂ}
    (hf : ∀ k : Fin d,
      MemLp (fun x => ((1 + ‖x‖) ^ N : ℝ) • fderiv ℝ f x (P102.U3.coordinateVector k)) 2)
    {B : ℝ} (hb : ∀ k : Fin d,
      lpNorm (fun x => ((1 + ‖x‖) ^ N : ℝ) • fderiv ℝ f x (P102.U3.coordinateVector k)) 2 volume ≤ B) :
    lpNorm (fun x => ((1 + ‖x‖) ^ N : ℝ) • gradient f x) 2 volume ≤ d * B := by
  calc
    _ ≤ ∑ k : Fin d,
        lpNorm (fun x => ((1 + ‖x‖) ^ N : ℝ) • fderiv ℝ f x (P102.U3.coordinateVector k)) 2 volume :=
      weighted_gradient_lpNorm_le hf
    _ ≤ ∑ _k : Fin d, B := Finset.sum_le_sum (fun k _ => hb k)
    _ = _ := by simp

/-- A common operator norm bound for the frequency derivatives yields the weighted
inverse bound with constants depending only on d and N. -/
theorem compactSymbol_inverse_weighted_lpNorm_le_of_opNorm_bound
    {d N : ℕ} {a : Euclidean d → ℂ} (ha : ContDiff ℝ N a)
    (hs : tsupport a ⊆ Metric.closedBall 0 2) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ n : ℕ, n ≤ N → ∀ ξ, ‖iteratedFDeriv ℝ n a ξ‖ ≤ B) :
    lpNorm (fun x => ((1 + ‖x‖) ^ N : ℝ) • 𝓕⁻ a x) 2 volume ≤
      2 ^ (N - 1) * (1 + (d : ℝ) ^ N) *
        (B * lpNorm ((Metric.closedBall (0 : Euclidean d) 2).indicator (fun _ => (1 : ℝ))) 2 volume) := by
  have hcs : HasCompactSupport a :=
    (isCompact_closedBall (0 : Euclidean d) 2).of_isClosed_subset isClosed_closure hs
  apply compactSymbol_inverse_weighted_lpNorm_le_of_derivative_bound ha hcs
  · have h := compactSymbol_derivative_lpNorm_le_of_bound ha hs
      (n := 0) (Nat.zero_le N) hB (hb 0 (Nat.zero_le N)) (fun i => Fin.elim0 i)
    simpa only [iteratedFDeriv_zero_apply] using h
  · intro β
    exact compactSymbol_derivative_lpNorm_le_of_bound ha hs (le_refl N) hB (hb N (le_refl N)) β

/-- Coordinate frequency symbols bound the full weighted inverse gradient. -/
theorem compactSymbol_inverse_gradient_weighted_lpNorm_le_of_opNorm_bound
    {d N : ℕ} {a : Euclidean d → ℂ} (ha : ContDiff ℝ N a)
    (hs : tsupport a ⊆ Metric.closedBall 0 2) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ (k : Fin d) (n : ℕ), n ≤ N → ∀ ξ,
      ‖iteratedFDeriv ℝ n
        (fun ξ => (2 * (Real.pi : ℂ) * Complex.I) •
          (inner ℝ ξ (P102.U3.coordinateVector k)) • a ξ) ξ‖ ≤ B) :
    lpNorm (fun x => ((1 + ‖x‖) ^ N : ℝ) • gradient (𝓕⁻ a) x) 2 volume ≤
      d * (2 ^ (N - 1) * (1 + (d : ℝ) ^ N) *
        (B * lpNorm ((Metric.closedBall (0 : Euclidean d) 2).indicator (fun _ => (1 : ℝ))) 2 volume)) := by
  have hcs : HasCompactSupport a :=
    (isCompact_closedBall (0 : Euclidean d) 2).of_isClosed_subset isClosed_closure hs
  apply weighted_gradient_lpNorm_le_of_bound
    (fun k => compactSymbol_inverse_fderiv_weighted_memLp ha hcs (P102.U3.coordinateVector k))
  intro k
  let b : Euclidean d → ℂ :=
    fun ξ => (2 * (Real.pi : ℂ) * Complex.I) •
      (inner ℝ ξ (P102.U3.coordinateVector k)) • a ξ
  have hbc : ContDiff ℝ N b :=
    ((contDiff_id.inner ℝ contDiff_const).smul ha).const_smul _
  have hbs : tsupport b ⊆ Metric.closedBall 0 2 := by
    apply Set.Subset.trans _ hs
    apply closure_mono
    intro ξ hξ
    change a ξ ≠ 0
    intro h0
    apply hξ
    simp only [b, h0, smul_zero]
  have h := compactSymbol_inverse_weighted_lpNorm_le_of_opNorm_bound hbc hbs hB (hb k)
  have he : (fun x => ((1 + ‖x‖) ^ N : ℝ) • fderiv ℝ (𝓕⁻ a) x (P102.U3.coordinateVector k)) =
      fun x => ((1 + ‖x‖) ^ N : ℝ) • 𝓕⁻ b x := by
    funext x
    rw [compactSymbol_inverse_fderiv_apply ha.continuous hcs]
  rw [he]
  exact h




theorem memLp_two_comp_inv_smul {d : ℕ} {f : Euclidean d → ℝ}
    (hf : MemLp f 2) {R : ℝ} (hR : R ≠ 0) :
    MemLp (fun x => f (R⁻¹ • x)) 2 := by
  have hm := hf.aestronglyMeasurable.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hR))
  exact (memLp_two_iff_integrable_sq hm).mpr
    (((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf).comp_smul
      (inv_ne_zero hR))

theorem eLpNorm_two_comp_inv_smul {d : ℕ} {f : Euclidean d → ℝ}
    (hf : MemLp f 2) {R : ℝ} (hR : 0 < R) :
    (eLpNorm (fun x => f (R⁻¹ • x)) 2 volume).toReal =
      R ^ ((d : ℝ) / 2) * (eLpNorm f 2 volume).toReal := by
  have hg := memLp_two_comp_inv_smul hf hR.ne'
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hg,
    MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat]
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
  have hscale : (∫ a, ‖f (R⁻¹ • a)‖ ^ (2 : ℝ)) = R ^ d * ∫ a, ‖f a‖ ^ (2 : ℝ) := by
    simpa using Measure.integral_comp_inv_smul_of_nonneg volume
      (fun a => ‖f a‖ ^ (2 : ℝ)) hR.le
  rw [hscale]
  rw [Real.mul_rpow (pow_nonneg hR.le _) (integral_nonneg (fun x => by positivity)),
    ← Real.rpow_natCast R d, ← Real.rpow_mul hR.le]
  congr 2

theorem integral_norm_smul_le_two_norms {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : Euclidean d → ℝ} {f : Euclidean d → E}
    (hg : MemLp g 2) (hf : MemLp f 2) :
    (∫ x, ‖g x • f x‖) ≤
      (eLpNorm g 2 volume).toReal * (eLpNorm f 2 volume).toReal := by
  have hprod : MemLp (g • f) 1 := hg.smul hf
  have heq : (eLpNorm (g • f) 1 volume).toReal = ∫ x, ‖g x • f x‖ := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hprod]
    simp only [ENNReal.toReal_one, Real.rpow_one, inv_one]
    exact ENNReal.toReal_ofReal (integral_nonneg (fun x => norm_nonneg (g x • f x)))
  rw [← heq, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hg.eLpNorm_ne_top hf.eLpNorm_ne_top)
    (eLpNorm_smul_le_mul_eLpNorm hg.aestronglyMeasurable hf.aestronglyMeasurable)


theorem inverse_weight_tail_pointwise {d N : ℕ} {R : ℝ} (hR : 0 < R)
    (x : Euclidean d) (hx : R < ‖x‖) :
    ((1 + ‖x‖) ^ N)⁻¹ ≤ (2 / R) ^ N * ((1 + ‖R⁻¹ • x‖) ^ N)⁻¹ := by
  have hn : ‖R⁻¹ • x‖ = ‖x‖ / R := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    ring
  have hb : 1 + ‖R⁻¹ • x‖ ≤ (2 / R) * (1 + ‖x‖) := by
    rw [hn, div_mul_eq_mul_div, le_div_iff₀ hR]
    have he : (1 + ‖x‖ / R) * R = R + ‖x‖ := by field_simp
    rw [he]
    linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖R⁻¹ • x‖) hb N
  rw [mul_pow] at hp
  have ht : 1 / (1 + ‖x‖) ^ N ≤ (2 / R) ^ N / (1 + ‖R⁻¹ • x‖) ^ N :=
    (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hp)
  simpa only [div_eq_mul_inv, one_mul] using ht


/-- Cauchy--Schwarz and dilation give the sharp power of the tail radius. -/
theorem integral_norm_tail_le_weighted_norm {d N : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Euclidean d → E} (hN : (d : ℝ) / 2 < N)
    (hf : MemLp (fun x => ((1 + ‖x‖) ^ N : ℝ) • f x) 2)
    {R : ℝ} (hR : 0 < R) :
    (∫ x in {x | R < ‖x‖}, ‖f x‖) ≤
      ((2 : ℝ) ^ N *
        (eLpNorm (fun x : Euclidean d => ((1 + ‖x‖) ^ N)⁻¹) 2 volume).toReal) *
      (eLpNorm (fun x => ((1 + ‖x‖) ^ N : ℝ) • f x) 2 volume).toReal *
      R ^ (-((N : ℝ) - (d : ℝ) / 2)) := by
  let b : Euclidean d → ℝ := fun x => ((1 + ‖x‖) ^ N)⁻¹
  let g : Euclidean d → ℝ := fun x => b (R⁻¹ • x)
  let wf : Euclidean d → E := fun x => ((1 + ‖x‖) ^ N : ℝ) • f x
  have hb : MemLp b 2 := inverse_weight_memLp hN
  have hg : MemLp g 2 := memLp_two_comp_inv_smul hb hR.ne'
  have hprod : Integrable (g • wf) := memLp_one_iff_integrable.mp (hg.smul hf)
  have hi : Integrable f := integrable_of_weighted_memLp hN hf
  have hc : 0 ≤ (2 / R) ^ N := by positivity
  have hs : MeasurableSet {x : Euclidean d | R < ‖x‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  have hbound : (∫ x in {x | R < ‖x‖}, ‖f x‖) ≤
      (2 / R) ^ N * (∫ x, ‖g x • wf x‖) := by
    calc
      _ ≤ ∫ x in {x | R < ‖x‖}, (2 / R) ^ N * ‖g x • wf x‖ := by
        apply setIntegral_mono_on hi.norm.integrableOn
          (hprod.norm.const_mul ((2 / R) ^ N)).integrableOn hs
        intro x hx
        have heq : ‖f x‖ = b x * ‖wf x‖ := by
          dsimp only [b, wf]
          rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (by positivity) N),
            ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (by positivity)), one_mul]
        rw [heq]
        calc
          _ ≤ ((2 / R) ^ N * g x) * ‖wf x‖ :=
            mul_le_mul_of_nonneg_right (inverse_weight_tail_pointwise hR x hx) (norm_nonneg _)
          _ = _ := by
            change ((2 / R) ^ N * g x) * ‖wf x‖ = (2 / R) ^ N * ‖g x • wf x‖
            have hg0 : 0 ≤ g x := by
              change 0 ≤ ((1 + ‖R⁻¹ • x‖) ^ N)⁻¹
              positivity
            rw [norm_smul (g x) (wf x), Real.norm_of_nonneg hg0]
            ring
      _ = (2 / R) ^ N * (∫ x in {x | R < ‖x‖}, ‖g x • wf x‖) := by
        rw [integral_const_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (integral_mono_measure Measure.restrict_le_self
          (Filter.Eventually.of_forall fun x => norm_nonneg (g x • wf x)) hprod.norm) hc
  calc
    _ ≤ (2 / R) ^ N *
        ((eLpNorm g 2 volume).toReal * (eLpNorm wf 2 volume).toReal) :=
      hbound.trans (mul_le_mul_of_nonneg_left (integral_norm_smul_le_two_norms hg hf) hc)
    _ = _ := by
      rw [eLpNorm_two_comp_inv_smul hb hR]
      rw [div_pow, div_eq_mul_inv, ← Real.rpow_natCast R N, ← Real.rpow_neg hR.le,
        show -((N : ℝ) - (d : ℝ) / 2) = -(N : ℝ) + (d : ℝ) / 2 by ring,
        Real.rpow_add hR]
      dsimp only [b, wf]
      ring


/-- Cauchy--Schwarz quantitatively controls L¹ by the weighted L² norm. -/
theorem integral_norm_le_weighted_norm {d N : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Euclidean d → E} (hN : (d : ℝ) / 2 < N)
    (hf : MemLp (fun x => ((1 + ‖x‖) ^ N : ℝ) • f x) 2) :
    (∫ x, ‖f x‖) ≤
      (eLpNorm (fun x : Euclidean d => ((1 + ‖x‖) ^ N)⁻¹) 2 volume).toReal *
      (eLpNorm (fun x => ((1 + ‖x‖) ^ N : ℝ) • f x) 2 volume).toReal := by
  have h := integral_norm_smul_le_two_norms (inverse_weight_memLp hN) hf
  convert h using 1
  congr 1
  funext x
  rw [smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ (by positivity)), one_smul]




/-- Translation estimate in terms of the integrable Fréchet derivative norm. -/
theorem translation_integral_le_fderiv {d : ℕ} {L : Euclidean d → ℂ}
    (hL : ContDiff ℝ 1 L) (hLi : Integrable L)
    (hDi : Integrable (fun x => ‖fderiv ℝ L x‖)) (h : Euclidean d) :
    (∫ x, ‖L (x-h) - L x‖) ≤ ‖h‖ * ∫ x, ‖fderiv ℝ L x‖ := by
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 1)
  let D : ℝ × Euclidean d → ℝ := fun p => ‖fderiv ℝ L (p.2 - p.1 • h)‖
  have hDc : Continuous (fderiv ℝ L) := hL.continuous_fderiv one_ne_zero
  have hDcont : Continuous D := hDc.norm.comp (continuous_snd.sub (continuous_fst.smul continuous_const))
  have hDint (t : ℝ) : Integrable (fun x => D (t,x)) := by
    exact (measurePreserving_sub_right volume (t • h)).integrable_comp_of_integrable hDi
  have hDnorm (t : ℝ) : (∫ x, ‖D (t,x)‖) = ∫ x, ‖fderiv ℝ L x‖ := by
    simp only [D, norm_norm]
    exact integral_sub_right_eq_self (μ := (volume : Measure (Euclidean d))) (fun x => ‖fderiv ℝ L x‖) (t • h)
  have hDj : Integrable D (ν.prod volume) := by
    apply (integrable_prod_iff hDcont.aestronglyMeasurable).2
    refine ⟨Filter.Eventually.of_forall hDint, ?_⟩
    simp_rw [hDnorm]
    exact integrable_const _
  have hB (x : Euclidean d) : ‖L (x-h) - L x‖ ≤ ∫ t in (0 : ℝ)..1, D (t,x) * ‖h‖ := by
    have hpath (t : ℝ) : HasDerivAt (fun t : ℝ => L (x-t • h))
        (fderiv ℝ L (x-t • h) (-h)) t :=
      (hL.differentiable one_ne_zero (x-t • h)).hasFDerivAt.comp_hasDerivAt t
        (by simpa using (((hasDerivAt_id t).smul_const h).const_sub x))
    have hc : Continuous (fun t : ℝ => L (x-t • h)) :=
      hL.continuous.comp (continuous_const.sub (continuous_id.smul continuous_const))
    have hbcont : Continuous (fun t : ℝ => D (t,x) * ‖h‖) :=
      (hDcont.comp (continuous_id.prodMk continuous_const)).mul continuous_const
    have hi := norm_sub_le_integral_of_norm_deriv_le_of_le
      (B := fun t : ℝ => D (t,x) * ‖h‖) (by norm_num : (0:ℝ) ≤ 1)
      hc.continuousOn (fun t _ => (hpath t).differentiableAt.differentiableWithinAt)
      (Filter.Eventually.of_forall (fun t _ => by
        rw [(hpath t).deriv]
        simpa only [D, norm_neg] using (fderiv ℝ L (x-t • h)).le_opNorm (-h)))
      (hbcont.intervalIntegrable 0 1)
    simpa only [one_smul, zero_smul, sub_zero] using hi
  have hdiff : Integrable (fun x => ‖L (x-h)-L x‖) :=
    ((measurePreserving_sub_right volume h).integrable_comp_of_integrable hLi).sub hLi |>.norm
  have hmajor : Integrable (fun x => ∫ t, D (t,x) * ‖h‖ ∂ν) :=
    (hDj.mul_const ‖h‖).integral_prod_right
  calc
    (∫ x, ‖L (x-h)-L x‖) ≤ ∫ x, ∫ t, D (t,x) * ‖h‖ ∂ν := by
      apply integral_mono hdiff hmajor
      intro x
      simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)] using hB x
    _ = ∫ t, (∫ x, D (t,x) * ‖h‖) ∂ν :=
      integral_integral_swap (hDj.mul_const ‖h‖).swap
    _ = ‖h‖ * ∫ x, ‖fderiv ℝ L x‖ := by
      simp only [integral_mul_const]
      have hi (t : ℝ) : (∫ x, D (t,x)) = ∫ x, ‖fderiv ℝ L x‖ :=
        by
          simpa only [D] using integral_sub_right_eq_self
            (μ := (volume : Measure (Euclidean d))) (fun x => ‖fderiv ℝ L x‖) (t • h)
      simp_rw [hi]
      simp [ν, mul_comm]

/-- The coordinate Euclidean gradient controls the operator norm of the real derivative. -/
theorem fderiv_norm_le_gradient {d : ℕ} (L : Euclidean d → ℂ) (x : Euclidean d) :
    ‖fderiv ℝ L x‖ ≤ (d : ℝ) * ‖gradient L x‖ := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  let F := fderiv ℝ L x
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg d) (norm_nonneg _))
  intro v
  have hcoord (k : Fin d) : ‖F (b k)‖ ≤ ‖gradient L x‖ := by
    simpa only [F, b, gradient, P102.U3.coordinateVector, WithLp.ofLp_toLp] using
      PiLp.norm_apply_le (gradient L x) k
  calc
    ‖F v‖ = ‖F (∑ k, inner ℝ (b k) v • b k)‖ :=
      congrArg (fun w => ‖F w‖) (b.sum_repr' v).symm
    _ = ‖∑ k, inner ℝ (b k) v • F (b k)‖ := by simp only [map_sum, map_smul]
    _ ≤ ∑ k, ‖inner ℝ (b k) v • F (b k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin d, ‖v‖ * ‖gradient L x‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul]
      apply mul_le_mul _ (hcoord k) (norm_nonneg _) (norm_nonneg _)
      simpa [b] using
        norm_inner_le_norm (𝕜 := ℝ) (b k) v
    _ = (d : ℝ) * ‖gradient L x‖ * ‖v‖ := by simp; ring

/-- The L¹ translation estimate needed for the small dyadic scales. -/
theorem translation_integral_le_gradient {d : ℕ} {L : Euclidean d → ℂ}
    (hL : ContDiff ℝ 1 L) (hLi : Integrable L) (hGi : Integrable (gradient L))
    (h : Euclidean d) :
    (∫ x, ‖L (x-h) - L x‖) ≤ (d : ℝ) * ‖h‖ * ∫ x, ‖gradient L x‖ := by
  have hDi : Integrable (fun x => ‖fderiv ℝ L x‖) := by
    apply (hGi.norm.const_mul (d : ℝ)).mono'
      (hL.continuous_fderiv one_ne_zero).norm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      simpa only [norm_norm] using fderiv_norm_le_gradient L x
  calc
    (∫ x, ‖L (x-h) - L x‖) ≤ ‖h‖ * ∫ x, ‖fderiv ℝ L x‖ :=
      translation_integral_le_fderiv hL hLi hDi h
    _ ≤ ‖h‖ * ∫ x, (d : ℝ) * ‖gradient L x‖ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact integral_mono hDi (hGi.norm.const_mul _) (fderiv_norm_le_gradient L)
    _ = (d : ℝ) * ‖h‖ * ∫ x, ‖gradient L x‖ := by rw [integral_const_mul]; ring




theorem finite_sum_geometric_zpow_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (J : Finset ℤ) (n : ℤ → ℤ) (hnj : Function.Injective n)
    (hn : ∀ j ∈ J, 0 ≤ n j) :
    (∑ j ∈ J, q ^ n j) ≤ (1 - q)⁻¹ := by
  classical
  have hinj : Set.InjOn (fun j => (n j).toNat) (J : Set ℤ) := by
    intro i hi j hj he
    apply hnj
    have ht := congrArg (fun a : ℕ => (a : ℤ)) he
    simpa only [Int.toNat_of_nonneg (hn i hi), Int.toNat_of_nonneg (hn j hj)] using ht
  calc
    _ = ∑ j ∈ J, q ^ (n j).toNat := by
      apply Finset.sum_congr rfl
      intro j hj
      conv_lhs => rw [← Int.toNat_of_nonneg (hn j hj), zpow_natCast]
    _ = ∑ i ∈ J.image (fun j => (n j).toNat), q ^ i := (Finset.sum_image hinj).symm
    _ ≤ ∑' i : ℕ, q ^ i :=
      (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _ (fun i _ => pow_nonneg hq0 i)
    _ = _ := tsum_geometric_of_lt_one hq0 hq1


theorem scale_small_ratio (j k : ℤ) :
    scale j = (1 / 2 : ℝ) ^ (k - j) * scale k := by
  rw [one_div, inv_zpow, ← zpow_neg]
  unfold scale
  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  omega


theorem finite_dyadic_small_sum_le {t : ℝ} (ht : 0 < t) (J : Finset ℤ)
    (hJ : ∀ j ∈ J, scale j * t ≤ 1) :
    (∑ j ∈ J, scale j * t) ≤ 2 := by
  obtain ⟨k, hk, hk'⟩ := exists_mem_Ico_zpow (inv_pos.mpr ht) (by norm_num : (1 : ℝ) < 2)
  change scale k ≤ t⁻¹ at hk
  change t⁻¹ < scale (k + 1) at hk'
  have hkt : scale k * t ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hk ht.le
    simpa only [inv_mul_cancel₀ ht.ne'] using h
  have hkt' : 1 < scale (k + 1) * t := by
    have h := mul_lt_mul_of_pos_right hk' ht
    simpa only [inv_mul_cancel₀ ht.ne'] using h
  have hjk : ∀ j ∈ J, j ≤ k := by
    intro j hj
    by_contra hn
    have hs : scale (k + 1) ≤ scale j := scale_mono (by omega)
    have hm := mul_le_mul_of_nonneg_right hs ht.le
    linarith [hJ j hj]
  calc
    _ ≤ ∑ j ∈ J, (1 / 2 : ℝ) ^ (k - j) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [scale_small_ratio j k, mul_assoc]
      exact (mul_le_mul_of_nonneg_left hkt (zpow_nonneg (by norm_num) _)).trans_eq (mul_one _)
    _ ≤ (1 - (1 / 2 : ℝ))⁻¹ :=
      finite_sum_geometric_zpow_le (by norm_num) (by norm_num) J (fun j => k - j)
        (by intro i j h; change k - i = k - j at h; omega) (fun j hj => sub_nonneg.mpr (hjk j hj))
    _ = 2 := by norm_num


theorem finite_dyadic_large_sum_le {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ)
    (J : Finset ℤ) (hJ : ∀ j ∈ J, 1 < scale j * t) :
    (∑ j ∈ J, (scale j * t) ^ (-δ)) ≤ (1 - (2 : ℝ) ^ (-δ))⁻¹ := by
  obtain ⟨k, hk, hk'⟩ := exists_mem_Ico_zpow (inv_pos.mpr ht) (by norm_num : (1 : ℝ) < 2)
  change scale k ≤ t⁻¹ at hk
  change t⁻¹ < scale (k + 1) at hk'
  have hkt : scale k * t ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hk ht.le
    simpa only [inv_mul_cancel₀ ht.ne'] using h
  have hkt' : 1 < scale (k + 1) * t := by
    have h := mul_lt_mul_of_pos_right hk' ht
    simpa only [inv_mul_cancel₀ ht.ne'] using h
  have hjk : ∀ j ∈ J, k + 1 ≤ j := by
    intro j hj
    by_contra hn
    have hs : scale j ≤ scale k := scale_mono (by omega)
    have hm := mul_le_mul_of_nonneg_right hs ht.le
    linarith [hJ j hj]
  have he (j : ℤ) : (scale (j - (k + 1))) ^ (-δ) =
      ((2 : ℝ) ^ (-δ)) ^ (j - (k + 1)) := by
    unfold scale
    rw [← Real.rpow_intCast_mul (by norm_num), ← Real.rpow_mul_intCast (by norm_num)]
    congr 1
    ring
  calc
    _ ≤ ∑ j ∈ J, ((2 : ℝ) ^ (-δ)) ^ (j - (k + 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← he j]
      apply Real.rpow_le_rpow_of_nonpos (scale_pos _) _ (neg_nonpos.mpr hδ.le)
      calc
        scale (j - (k + 1)) = scale (j - (k + 1)) * 1 := (mul_one _).symm
        _ ≤ scale (j - (k + 1)) * (scale (k + 1) * t) :=
          mul_le_mul_of_nonneg_left hkt'.le (scale_pos _).le
        _ = scale j * t := by
          rw [← mul_assoc, ← scale_add]
          congr 2
          omega
    _ ≤ _ := finite_sum_geometric_zpow_le (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hδ))
      J (fun j => j - (k + 1))
      (by intro i j h; change i - (k + 1) = j - (k + 1) at h; omega)
      (fun j hj => sub_nonneg.mpr (hjk j hj))


/-- The low- and high-scale Hörmander contributions have a uniform finite sum. -/
theorem finite_dyadic_difference_sum_le {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ)
    (J : Finset ℤ) :
    (∑ j ∈ J, if scale j * t ≤ 1 then scale j * t else (scale j * t) ^ (-δ)) ≤
      2 + (1 - (2 : ℝ) ^ (-δ))⁻¹ := by
  classical
  rw [Finset.sum_ite]
  exact add_le_add
    (finite_dyadic_small_sum_le ht _ (fun j hj => (Finset.mem_filter.mp hj).2))
    (finite_dyadic_large_sum_le ht hδ _ (fun j hj => lt_of_not_ge (Finset.mem_filter.mp hj).2))


theorem symbol_derivative_norm_le {d : ℕ} {m : Euclidean d → ℂ} {A : ℝ}
    (hm : SymbolBound m A) {n : ℕ} (hn : n ≤ order d) (ξ : Euclidean d) (hξ : ξ ≠ 0) :
    ‖iteratedFDeriv ℝ n m ξ‖ ≤ (d : ℝ) ^ n * (A * ‖ξ‖ ^ (-(n : ℤ))) :=
  P102.U3.multilinear_norm_le_coordinate_bound _ (fun β => hm.2 n hn β ξ hξ)

/-- Scaling cancels exactly the homogeneous Mihlin derivative loss. -/
theorem scaled_symbol_derivative_norm_le {d : ℕ} {m : Euclidean d → ℂ} {A : ℝ}
    (hm : SymbolBound m A) {n : ℕ} (hn : n ≤ order d) (j : ℤ)
    (ξ : Euclidean d) (hξ : ξ ≠ 0) :
    ‖iteratedFDeriv ℝ n (fun x => m (scale j • x)) ξ‖ ≤
      (d : ℝ) ^ n * (A * ‖ξ‖ ^ (-(n : ℤ))) := by
  let S : Euclidean d →L[ℝ] Euclidean d := scale j • ContinuousLinearMap.id ℝ _
  let U : Set (Euclidean d) := {0}ᶜ
  have hU : IsOpen U := isOpen_compl_singleton
  have hS : S ⁻¹' U = U := by
    ext x
    simp [S, U, smul_eq_zero]
  have hx : ξ ∈ U := hξ
  have hsx : S ξ ∈ U := by simpa [S, U] using smul_ne_zero (scale_ne_zero j) hξ
  have he := S.iteratedFDerivWithin_comp_right hm.1 hU.uniqueDiffOn
    ((hU.preimage S.continuous).uniqueDiffOn) hsx (i := n) (by exact_mod_cast hn)
  rw [hS, iteratedFDerivWithin_of_isOpen n hU hx,
    iteratedFDerivWithin_of_isOpen n hU hsx] at he
  have hnorm : ‖iteratedFDeriv ℝ n (fun x => m (scale j • x)) ξ‖ =
      scale j ^ n * ‖iteratedFDeriv ℝ n m (scale j • ξ)‖ := by
    have he' : iteratedFDeriv ℝ n (fun x => m (scale j • x)) ξ =
        scale j ^ n • iteratedFDeriv ℝ n m (scale j • ξ) := by
      rw [show (fun x => m (scale j • x)) = m ∘ S from rfl, he]
      ext v
      simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        smul_apply, S,
        ContinuousLinearMap.id_apply]
      rw [ContinuousMultilinearMap.map_smul_univ]
      simp
    rw [he', norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos (scale_pos j) n)]
  rw [hnorm]
  calc
    _ ≤ scale j ^ n * ((d : ℝ) ^ n * (A * ‖scale j • ξ‖ ^ (-(n : ℤ)))) :=
      mul_le_mul_of_nonneg_left (symbol_derivative_norm_le hm hn _
        (smul_ne_zero (scale_ne_zero j) hξ)) (pow_nonneg (scale_pos j).le n)
    _ = _ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (scale_pos j), mul_zpow,
        zpow_neg, zpow_natCast]
      field_simp



theorem scaled_symbol_derivative_norm_le_annulus {d : ℕ} (hd : 1 ≤ d)
    {m : Euclidean d → ℂ} {A : ℝ} (hm : SymbolBound m A) {n : ℕ}
    (hn : n ≤ order d) (j : ℤ) (ξ : Euclidean d) (hξ : (1 / 2 : ℝ) ≤ ‖ξ‖) :
    ‖iteratedFDeriv ℝ n (fun x => m (scale j • x)) ξ‖ ≤
      (d : ℝ) ^ n * (A * (2 : ℝ) ^ n) := by
  have hx : ξ ≠ 0 := by intro h; norm_num [h] at hξ
  apply (scaled_symbol_derivative_norm_le hm hn j ξ hx).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (symbol_bound_nonneg hd hm)
  rw [zpow_neg, zpow_natCast]
  calc
    (‖ξ‖ ^ n)⁻¹ ≤ (((1 / 2 : ℝ) ^ n))⁻¹ :=
      (inv_le_inv₀ (pow_pos (norm_pos_iff.mpr hx) n)
        (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)).mpr
        (pow_le_pow_left₀ (by norm_num) hξ n)
    _ = _ := by simp

/-- Compact support supplies fixed bounds for every cutoff derivative. -/
theorem compactSmooth_derivative_bounds {d : ℕ} {g : Euclidean d → ℂ}
    (hc : ContDiff ℝ ∞ g) (hs : HasCompactSupport g) :
    ∃ D : ℕ → ℝ, (∀ n, 0 ≤ D n) ∧ ∀ (n : ℕ) (x : Euclidean d),
      ‖iteratedFDeriv ℝ n g x‖ ≤ D n := by
  choose D hD using fun n : ℕ => (hs.iteratedFDeriv n).exists_bound_of_continuous
    (hc.continuous_iteratedFDeriv (by simp))
  exact ⟨D, fun n => (norm_nonneg _).trans (hD n 0), hD⟩

/-- All rescaled annular symbols have bounded derivatives uniformly in scale.
The constant is chosen using only the dimension, cutoff, and derivative order. -/
theorem scaledSymbol_mul_derivative_bound {d : ℕ} (hd : 1 ≤ d)
    {g : Euclidean d → ℂ} (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g)
    (hz : ∀ x, ‖x‖ ≤ (1 / 2 : ℝ) → g x = 0) {n : ℕ} (hn : n ≤ order d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : Euclidean d → ℂ) (A : ℝ), SymbolBound m A →
      ∀ (j : ℤ) (ξ : Euclidean d), ‖iteratedFDeriv ℝ n (fun x => m (scale j • x) * g x) ξ‖ ≤ C * A := by
  obtain ⟨D, hD0, hD⟩ := compactSmooth_derivative_bounds hg hs
  let C : ℝ := ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * (d : ℝ) ^ i * (2 : ℝ) ^ i * D (n-i)
  refine ⟨C, ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hD0 _)
  · intro m A hm j ξ
    have hA := symbol_bound_nonneg hd hm
    by_cases hx : ‖ξ‖ < 1 / 2
    · have he : (fun x => m (scale j • x) * g x) =ᶠ[𝓝 ξ] (fun _ => (0 : ℂ)) := by
        filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
        simp [hz y hy.le]
      rw [(he.iteratedFDeriv ℝ n).self_of_nhds]
      simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      exact mul_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hD0 _)) hA
    · have hr : (1 / 2 : ℝ) ≤ ‖ξ‖ := le_of_not_gt hx
      have hx0 : ξ ≠ 0 := by intro h; norm_num [h] at hr
      let U : Set (Euclidean d) := {0}ᶜ
      have hU : IsOpen U := isOpen_compl_singleton
      have hξU : ξ ∈ U := hx0
      have hf : ContDiffOn ℝ (order d) (fun x => m (scale j • x)) U := by
        apply hm.1.comp (contDiff_id.const_smul (scale j)).contDiffOn
        intro x hx
        exact smul_ne_zero (scale_ne_zero j) hx
      have hgN : ContDiff ℝ (order d) g := hg.of_le (by simp)
      have hb := norm_iteratedFDerivWithin_mul_le hf hgN.contDiffOn hU.uniqueDiffOn
        hξU (n := n) (by exact_mod_cast hn)
      simp_rw [iteratedFDerivWithin_of_isOpen _ hU hξU] at hb
      apply hb.trans
      change (∑ i ∈ Finset.range (n + 1), _) ≤ C * A
      dsimp only [C]
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ order d := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hn
      have hsi := scaled_symbol_derivative_norm_le_annulus hd hm hi' j ξ hr
      calc
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun x => m (scale j • x)) ξ‖ *
            ‖iteratedFDeriv ℝ (n-i) g ξ‖ ≤
            (n.choose i : ℝ) * ((d : ℝ) ^ i * (A * (2 : ℝ) ^ i)) * D (n-i) := by
              exact mul_le_mul (mul_le_mul_of_nonneg_left hsi (by positivity))
                (hD _ _) (norm_nonneg _) (by positivity)
        _ = _ := by ring


/-- The frequency derivative estimates in the source hold uniformly in the dyadic index. -/
theorem annularSymbol_derivative_bound {d : ℕ} (hd : 1 ≤ d)
    {χ : Euclidean d → ℝ} (hχ : IsCutoff χ) {n : ℕ} (hn : n ≤ order d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : Euclidean d → ℂ) (A : ℝ), SymbolBound m A →
      ∀ (j : ℤ) (ξ : Euclidean d), ‖iteratedFDeriv ℝ n (annularSymbol χ m j) ξ‖ ≤ C * A := by
  have hg : ContDiff ℝ ∞ (fun y => (annulus χ y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (annulus_contDiff hχ)
  have hs : HasCompactSupport (fun y => (annulus χ y : ℂ)) :=
    (annulus_hasCompactSupport hχ).comp_left (g := Complex.ofReal) (by simp)
  exact scaledSymbol_mul_derivative_bound hd hg hs
    (fun x hx => by simp [annulus_eq_zero_of_small hχ hx]) hn


/-- The same uniform frequency bounds hold for the symbol of a physical derivative. -/
theorem annularSymbol_physical_derivative_bound {d : ℕ} (hd : 1 ≤ d)
    {χ : Euclidean d → ℝ} (hχ : IsCutoff χ) (v : Euclidean d)
    {n : ℕ} (hn : n ≤ order d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : Euclidean d → ℂ) (A : ℝ), SymbolBound m A →
      ∀ (j : ℤ) (ξ : Euclidean d),
        ‖iteratedFDeriv ℝ n
          (fun y => (2 * (Real.pi : ℂ) * Complex.I) • (inner ℝ y v) • annularSymbol χ m j y) ξ‖
          ≤ C * A := by
  let g : Euclidean d → ℂ := fun y =>
    (2 * (Real.pi : ℂ) * Complex.I) • (inner ℝ y v) • (annulus χ y : ℂ)
  have hη : ContDiff ℝ ∞ (fun y => (annulus χ y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (annulus_contDiff hχ)
  have hηs : HasCompactSupport (fun y => (annulus χ y : ℂ)) :=
    (annulus_hasCompactSupport hχ).comp_left (g := Complex.ofReal) (by simp)
  have hg : ContDiff ℝ ∞ g :=
    ((contDiff_id.inner ℝ contDiff_const).smul hη).const_smul _
  have hgs₀ : HasCompactSupport (fun y => (inner ℝ y v) • (annulus χ y : ℂ)) :=
    HasCompactSupport.smul_left (f := fun y => inner ℝ y v) hηs
  have hgs : HasCompactSupport g :=
    HasCompactSupport.smul_left (f := fun _ => (2 * (Real.pi : ℂ) * Complex.I)) hgs₀
  obtain ⟨C, hC0, hC⟩ := scaledSymbol_mul_derivative_bound hd hg hgs
    (fun y hy => by simp [g, annulus_eq_zero_of_small hχ hy]) hn
  refine ⟨C, hC0, ?_⟩
  intro m A hm j ξ
  have he : (fun y => m (scale j • y) * g y) =
      (fun y => (2 * (Real.pi : ℂ) * Complex.I) • (inner ℝ y v) • annularSymbol χ m j y) := by
    funext y
    simp only [g, annularSymbol, smul_eq_mul, Complex.real_smul]
    ring
  rw [← he]
  exact hC m A hm j ξ




/-- The closed frequency support stays in the same ball for every dyadic symbol. -/
theorem annularSymbol_tsupport_subset_ball {d : ℕ} {χ : Euclidean d → ℝ}
    (hχ : IsCutoff χ) (m : Euclidean d → ℂ) (j : ℤ) :
    tsupport (annularSymbol χ m j) ⊆ Metric.closedBall 0 2 := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro ξ hξ
  have hη : annulus χ ξ ≠ 0 := by
    intro hz
    apply hξ
    simp [annularSymbol, hz]
  have hn := (annulus_support hχ ξ hη).2.le
  simpa only [Metric.mem_closedBall, dist_zero_right] using hn

/-- Finitely many derivative orders admit one common constant, independent of the
symbol, its size and the dyadic index. -/
theorem annularSymbol_all_derivative_bounds {d : ℕ} (hd : 1 ≤ d)
    {χ : Euclidean d → ℝ} (hχ : IsCutoff χ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (m : Euclidean d → ℂ) (A : ℝ), SymbolBound m A →
      ∀ (j : ℤ) (n : ℕ), n ≤ order d → ∀ ξ,
        ‖iteratedFDeriv ℝ n (annularSymbol χ m j) ξ‖ ≤ D * A ∧
        ∀ k : Fin d, ‖iteratedFDeriv ℝ n
          (fun y => (2 * (Real.pi : ℂ) * Complex.I) •
            (inner ℝ y (P102.U3.coordinateVector k)) • annularSymbol χ m j y) ξ‖ ≤ D * A := by
  choose c hc0 hc using fun n : Fin (order d + 1) =>
    annularSymbol_derivative_bound hd hχ (Nat.le_of_lt_succ n.isLt)
  choose g hg0 hg using fun p : Fin d × Fin (order d + 1) =>
    annularSymbol_physical_derivative_bound hd hχ (P102.U3.coordinateVector p.1)
      (Nat.le_of_lt_succ p.2.isLt)
  let D : ℝ := (∑ n, c n) + ∑ p, g p
  have hcS : 0 ≤ ∑ n, c n := Finset.sum_nonneg (fun n _ => hc0 n)
  have hgS : 0 ≤ ∑ p, g p := Finset.sum_nonneg (fun p _ => hg0 p)
  refine ⟨D, add_nonneg hcS hgS, ?_⟩
  intro m A hm j n hn ξ
  have hA := symbol_bound_nonneg hd hm
  let i : Fin (order d + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
  constructor
  · apply (hc i m A hm j ξ).trans
    apply mul_le_mul_of_nonneg_right _ hA
    exact (Finset.single_le_sum (fun a _ => hc0 a) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_right hgS)
  · intro k
    apply (hg (k, i) m A hm j ξ).trans
    apply mul_le_mul_of_nonneg_right _ hA
    exact (Finset.single_le_sum (fun a _ => hg0 a) (Finset.mem_univ (k, i))).trans
      (le_add_of_nonneg_left hcS)

/-- The full weighted norm bound claimed in the manuscript is uniform in j. -/
theorem inverseKernel_uniform_weighted_bound {d : ℕ} (hd : 1 ≤ d)
    {χ : Euclidean d → ℝ} (hχ : IsCutoff χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : Euclidean d → ℂ) (A : ℝ), SymbolBound m A →
      ∀ j : ℤ,
        lpNorm (fun x => ((1 + ‖x‖) ^ order d : ℝ) • inverseKernel χ m j x) 2 volume +
        lpNorm (fun x => ((1 + ‖x‖) ^ order d : ℝ) • gradient (inverseKernel χ m j) x) 2 volume ≤ C * A := by
  obtain ⟨D, hD0, hD⟩ := annularSymbol_all_derivative_bounds hd hχ
  let V : ℝ := lpNorm ((Metric.closedBall (0 : Euclidean d) 2).indicator (fun _ => (1 : ℝ))) 2 volume
  let H : ℝ := 2 ^ (order d - 1) * (1 + (d : ℝ) ^ order d)
  refine ⟨(1 + d) * H * V * D, mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by dsimp [H]; positivity)) lpNorm_nonneg) hD0, ?_⟩
  intro m A hm j
  have hDA : 0 ≤ D * A := mul_nonneg hD0 (symbol_bound_nonneg hd hm)
  have h0 := compactSymbol_inverse_weighted_lpNorm_le_of_opNorm_bound
    (annularSymbol_contDiff hχ hm j) (annularSymbol_tsupport_subset_ball hχ m j)
    hDA (fun n hn ξ => (hD m A hm j n hn ξ).1)
  have h1 := compactSymbol_inverse_gradient_weighted_lpNorm_le_of_opNorm_bound
    (annularSymbol_contDiff hχ hm j) (annularSymbol_tsupport_subset_ball hχ m j)
    hDA (fun k n hn ξ => (hD m A hm j n hn ξ).2 k)
  change lpNorm (fun x => ((1 + ‖x‖) ^ order d : ℝ) • 𝓕⁻ (annularSymbol χ m j) x) 2 volume +
    lpNorm (fun x => ((1 + ‖x‖) ^ order d : ℝ) • gradient (𝓕⁻ (annularSymbol χ m j)) x) 2 volume ≤ _
  calc
    _ ≤ H * (D * A * V) + d * (H * (D * A * V)) := add_le_add h0 h1
    _ = _ := by dsimp only [H, V]; ring

/-- Weighted Plancherel, Cauchy--Schwarz and dilation provide all
uniform estimates for the individual dyadic kernels. -/
theorem kernelEstimates_exists {d : ℕ} (hd : 1 ≤ d)
    {χ : Euclidean d → ℝ} (hχ : IsCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : Euclidean d → ℂ) (A : ℝ), SymbolBound m A →
      KernelEstimates χ m A C := by
  obtain ⟨C, hC0, hC⟩ := inverseKernel_uniform_weighted_bound hd hχ
  let W : ℝ := (eLpNorm (fun x : Euclidean d => ((1 + ‖x‖) ^ order d)⁻¹) 2 volume).toReal
  let H : ℝ := 1 + W + 2 ^ order d * W
  have hW0 : 0 ≤ W := ENNReal.toReal_nonneg
  have hH : 0 < H := by dsimp [H]; positivity
  have hH1 : 1 ≤ H := by dsimp [H]; nlinarith [show (0 : ℝ) ≤ 2 ^ order d * W by positivity]
  have hHW : W ≤ H := by dsimp [H]; nlinarith [show (0 : ℝ) ≤ 2 ^ order d * W by positivity]
  have hHT : 2 ^ order d * W ≤ H := by dsimp [H]; linarith
  refine ⟨H * (C + 1), mul_pos hH (by positivity), ?_⟩
  intro m A hm j
  have hA := symbol_bound_nonneg hd hm
  have hw := inverseKernel_weighted_memLp hχ hm j
  have hg := inverseKernel_gradient_weighted_memLp hχ hm j
  have hi := inverseKernel_integrable hχ hm j
  have hsum : (eLpNorm (fun x => ((1 + ‖x‖) ^ order d : ℝ) • inverseKernel χ m j x) 2 volume).toReal +
      (eLpNorm (fun x => ((1 + ‖x‖) ^ order d : ℝ) • gradient (inverseKernel χ m j) x) 2 volume).toReal ≤ C * A :=
    hC m A hm j
  have hscalar : (eLpNorm (fun x => ((1 + ‖x‖) ^ order d : ℝ) • inverseKernel χ m j x) 2 volume).toReal ≤ C * A :=
    le_trans (le_add_of_nonneg_right ENNReal.toReal_nonneg) hsum
  refine ⟨inverseKernel_contDiff hχ hm j, hw, hg, ?_, hi.1, hi.2, ?_, ?_⟩
  · apply hsum.trans
    apply mul_le_mul_of_nonneg_right _ hA
    nlinarith
  · have h0 := integral_norm_le_weighted_norm (order_gt_half d) hw
    have h1 := integral_norm_le_weighted_norm (order_gt_half d) hg
    calc
      _ ≤ W * ((eLpNorm (fun x => ((1 + ‖x‖) ^ order d : ℝ) • inverseKernel χ m j x) 2 volume).toReal +
          (eLpNorm (fun x => ((1 + ‖x‖) ^ order d : ℝ) • gradient (inverseKernel χ m j) x) 2 volume).toReal) := by
        dsimp only [W]
        nlinarith
      _ ≤ W * (C * A) := mul_le_mul_of_nonneg_left hsum hW0
      _ ≤ (H * (C + 1)) * A := by
        rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_right _ hA
        nlinarith
  · intro R hR
    have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR
    have ht := integral_norm_tail_le_weighted_norm (order_gt_half d) hw hR0
    apply ht.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hR0.le _)
    calc
      (2 : ℝ) ^ order d * W *
          (eLpNorm (fun x => ((1 + ‖x‖) ^ order d : ℝ) • inverseKernel χ m j x) 2 volume).toReal ≤
          (2 : ℝ) ^ order d * W * (C * A) :=
        mul_le_mul_of_nonneg_left hscalar (by positivity)
      _ ≤ (H * (C + 1)) * A := by
        rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_right _ hA
        nlinarith




/-- Enlarging the dimension-only constant preserves all three kernel bounds. -/
theorem kernelEstimates_mono {d : ℕ} {χ : Euclidean d → ℝ} {m : Euclidean d → ℂ}
    {A C D : ℝ} (hA : 0 ≤ A) (hCD : C ≤ D) (h : KernelEstimates χ m A C) :
    KernelEstimates χ m A D := by
  intro j
  rcases h j with ⟨hc, hm, hgm, hnorm, hi, hgi, hL1, htail⟩
  have hb : C * A ≤ D * A := mul_le_mul_of_nonneg_right hCD hA
  refine ⟨hc, hm, hgm, hnorm.trans hb, hi, hgi, hL1.trans hb, ?_⟩
  intro R hR
  exact (htail R hR).trans (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (by linarith) _))




/-- The L¹ norm is invariant under positive normalized dilation. -/
theorem normalizedDilation_integral_norm {d : ℕ} (L : Euclidean d → ℂ)
    {s : ℝ} (hs : 0 < s) :
    (∫ x, ‖(s ^ d : ℝ) • L (s • x)‖) = ∫ x, ‖L x‖ := by
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hs d)]
  rw [integral_const_mul]
  have he := Measure.integral_comp_smul_of_nonneg volume (fun x : Euclidean d => ‖L x‖) s (hR := hs.le)
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at he
  rw [he, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero d hs.ne'), one_mul]

/-- Tail integrals are transported exactly by normalized dilation. -/
theorem normalizedDilation_tail {d : ℕ} (L : Euclidean d → ℂ)
    {s : ℝ} (hs : 0 < s) (R : ℝ) :
    (∫ x in {x | R < ‖x‖}, ‖(s ^ d : ℝ) • L (s • x)‖) =
      ∫ x in {x | s * R < ‖x‖}, ‖L x‖ := by
  have hmeas (r : ℝ) : MeasurableSet {x : Euclidean d | r < ‖x‖} := measurableSet_lt measurable_const continuous_norm.measurable
  rw [← integral_indicator (hmeas R), ← integral_indicator (hmeas (s*R))]
  have he (x : Euclidean d) :
      {x : Euclidean d | R < ‖x‖}.indicator (fun x => ‖(s ^ d : ℝ) • L (s • x)‖) x =
      s ^ d * ({x : Euclidean d | s*R < ‖x‖}.indicator (fun x => ‖L x‖) (s • x)) := by
    have hi : s * R < ‖s • x‖ ↔ R < ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
      exact mul_lt_mul_iff_right₀ hs
    by_cases hx : R < ‖x‖
    · rw [Set.indicator_of_mem (show x ∈ {x : Euclidean d | R < ‖x‖} from hx), Set.indicator_of_mem (show s • x ∈ {x : Euclidean d | s*R < ‖x‖} from hi.mpr hx)]
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hs d)]
    · rw [Set.indicator_of_notMem (show x ∉ {x : Euclidean d | R < ‖x‖} from hx), Set.indicator_of_notMem (show s • x ∉ {x : Euclidean d | s*R < ‖x‖} from mt hi.mp hx), mul_zero]
  simp_rw [he]
  rw [integral_const_mul]
  have hc := Measure.integral_comp_smul_of_nonneg volume
    ({x : Euclidean d | s*R < ‖x‖}.indicator (fun x => ‖L x‖)) s (hR := hs.le)
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hc
  rw [hc, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero d hs.ne'), one_mul]

/-- Small shifts of normalized dilates are controlled by the L¹ gradient. -/
theorem normalizedDilation_translation_le {d : ℕ} {L : Euclidean d → ℂ}
    (hL : ContDiff ℝ 1 L) (hLi : Integrable L) (hGi : Integrable (gradient L))
    {s : ℝ} (hs : 0 < s) (h : Euclidean d) :
    (∫ x, ‖(s ^ d : ℝ) • L (s • (x-h)) - (s ^ d : ℝ) • L (s • x)‖) ≤
      (d : ℝ) * (s * ‖h‖) * ∫ x, ‖gradient L x‖ := by
  have he (x : Euclidean d) :
      (s ^ d : ℝ) • L (s • (x-h)) - (s ^ d : ℝ) • L (s • x) =
      (s ^ d : ℝ) • (L (s • x - s • h) - L (s • x)) := by rw [smul_sub, smul_sub]
  simp_rw [he]
  rw [normalizedDilation_integral_norm (fun x => L (x - s • h) - L x) hs]
  have hi := translation_integral_le_gradient hL hLi hGi (s • h)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hs] using hi

theorem kernelEstimates_dilated_integrable {d : ℕ} {χ : Euclidean d → ℝ}
    {m : Euclidean d → ℂ} {A C : ℝ} (hE : KernelEstimates χ m A C) (j : ℤ) :
    Integrable (dilatedKernel χ m j) := by
  rcases hE j with ⟨_, _, _, _, hLi, _, _, _⟩
  exact (hLi.comp_smul (scale_ne_zero j)).smul (scale j ^ d)

theorem kernelEstimates_small_translation {d : ℕ} {χ : Euclidean d → ℝ}
    {m : Euclidean d → ℂ} {A C : ℝ} (hE : KernelEstimates χ m A C)
    (j : ℤ) (h : Euclidean d) :
    (∫ x in {x | 2*‖h‖ < ‖x‖}, ‖dilatedKernel χ m j (x-h) - dilatedKernel χ m j x‖) ≤
      (d : ℝ) * C * A * (scale j * ‖h‖) := by
  rcases hE j with ⟨hL, _, _, _, hLi, hGi, hsum, _⟩
  have hKi := kernelEstimates_dilated_integrable hE j
  have hdiff : Integrable (fun x => ‖dilatedKernel χ m j (x-h) - dilatedKernel χ m j x‖) :=
    ((measurePreserving_sub_right volume h).integrable_comp_of_integrable hKi).sub hKi |>.norm
  have hG : (∫ x, ‖gradient (inverseKernel χ m j) x‖) ≤ C*A :=
    (le_add_of_nonneg_left (integral_nonneg (fun x => norm_nonneg (inverseKernel χ m j x)))).trans hsum
  calc
    _ ≤ ∫ x, ‖dilatedKernel χ m j (x-h) - dilatedKernel χ m j x‖ :=
      setIntegral_le_integral hdiff (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    _ ≤ (d : ℝ) * (scale j * ‖h‖) * ∫ x, ‖gradient (inverseKernel χ m j) x‖ :=
      normalizedDilation_translation_le (hL.of_le (by simp)) hLi hGi (scale_pos j) h
    _ ≤ (d : ℝ) * (scale j * ‖h‖) * (C*A) :=
      mul_le_mul_of_nonneg_left hG (mul_nonneg (Nat.cast_nonneg d) (mul_nonneg (scale_pos j).le (norm_nonneg h)))
    _ = (d : ℝ) * C * A * (scale j * ‖h‖) := by ring

theorem kernelEstimates_finite_difference_le_sum {d : ℕ} {χ : Euclidean d → ℝ}
    {m : Euclidean d → ℂ} {A C : ℝ} (hE : KernelEstimates χ m A C)
    (J : Finset ℤ) (h : Euclidean d) :
    IntegrableOn (fun x => ‖finiteKernel χ m J (x-h) - finiteKernel χ m J x‖) {x | 2*‖h‖ < ‖x‖} ∧
    (∫ x in {x | 2*‖h‖ < ‖x‖}, ‖finiteKernel χ m J (x-h) - finiteKernel χ m J x‖) ≤
      ∑ j ∈ J, ∫ x in {x | 2*‖h‖ < ‖x‖}, ‖dilatedKernel χ m j (x-h) - dilatedKernel χ m j x‖ := by
  have hKi : Integrable (finiteKernel χ m J) :=
    integrable_finsetSum J (fun j _ => kernelEstimates_dilated_integrable hE j)
  have hdiff : Integrable (fun x => ‖finiteKernel χ m J (x-h) - finiteKernel χ m J x‖) :=
    ((measurePreserving_sub_right volume h).integrable_comp_of_integrable hKi).sub hKi |>.norm
  have hji (j : ℤ) : Integrable (fun x => ‖dilatedKernel χ m j (x-h) - dilatedKernel χ m j x‖) := by
    have hj := kernelEstimates_dilated_integrable hE j
    exact ((measurePreserving_sub_right volume h).integrable_comp_of_integrable hj).sub hj |>.norm
  refine ⟨hdiff.integrableOn, ?_⟩
  calc
    _ ≤ ∫ x in {x | 2*‖h‖ < ‖x‖},
        ∑ j ∈ J, ‖dilatedKernel χ m j (x-h) - dilatedKernel χ m j x‖ := by
      apply integral_mono hdiff.integrableOn
        (integrable_finsetSum J (fun j _ => (hji j).integrableOn))
      intro x
      simp only [finiteKernel, ← Finset.sum_sub_distrib]
      exact norm_sum_le _ _
    _ = _ := integral_finsetSum J (fun j _ => (hji j).integrableOn)

/-- Far from the shift, both kernel terms are controlled by the unshifted tail. -/
theorem translation_tail_integral_le {d : ℕ} {K : Euclidean d → ℂ}
    (hK : Integrable K) (h : Euclidean d) :
    (∫ x in {x | 2 * ‖h‖ < ‖x‖}, ‖K (x - h) - K x‖) ≤
      2 * (∫ x in {x | ‖h‖ < ‖x‖}, ‖K x‖) := by
  have hi : Integrable (fun x => K (x - h)) :=
    (measurePreserving_sub_right volume h).integrable_comp_of_integrable hK
  have hs : MeasurableSet {x : Euclidean d | 2 * ‖h‖ < ‖x‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  have hshift : (∫ x in {x | ‖h‖ < ‖x - h‖}, ‖K (x - h)‖) =
      ∫ x in {x | ‖h‖ < ‖x‖}, ‖K x‖ := by
    exact (measurePreserving_sub_right volume h).setIntegral_preimage_emb
      (MeasurableEquiv.subRight h).measurableEmbedding
      (fun x => ‖K x‖) {x | ‖h‖ < ‖x‖}
  calc
    _ ≤ ∫ x in {x | 2 * ‖h‖ < ‖x‖}, (‖K (x - h)‖ + ‖K x‖) :=
      setIntegral_mono_on (hi.sub hK).norm.integrableOn
        (hi.norm.add hK.norm).integrableOn hs (fun x _ => norm_sub_le _ _)
    _ = (∫ x in {x | 2 * ‖h‖ < ‖x‖}, ‖K (x - h)‖) +
        (∫ x in {x | 2 * ‖h‖ < ‖x‖}, ‖K x‖) :=
      integral_add hi.norm.integrableOn hK.norm.integrableOn
    _ ≤ (∫ x in {x | ‖h‖ < ‖x - h‖}, ‖K (x - h)‖) +
        (∫ x in {x | ‖h‖ < ‖x‖}, ‖K x‖) := by
      apply add_le_add
      · apply setIntegral_mono_set hi.norm.integrableOn
          (Filter.Eventually.of_forall fun x => norm_nonneg (K (x - h)))
        apply Filter.Eventually.of_forall
        intro x hx
        have ht := norm_sub_norm_le x h
        change 2 * ‖h‖ < ‖x‖ at hx
        change ‖h‖ < ‖x - h‖
        linarith
      · apply setIntegral_mono_set hK.norm.integrableOn
          (Filter.Eventually.of_forall fun x => norm_nonneg (K x))
        apply Filter.Eventually.of_forall
        intro x hx
        change 2 * ‖h‖ < ‖x‖ at hx
        change ‖h‖ < ‖x‖
        linarith [norm_nonneg h]
    _ = _ := by rw [hshift]; ring

/-- A large dyadic shift is bounded by twice the single-kernel tail estimate. -/
theorem dilatedKernel_large_translation_tail_le {d : ℕ} {χ : Euclidean d → ℝ}
    {m : Euclidean d → ℂ} {A C : ℝ} (hKE : KernelEstimates χ m A C)
    (j : ℤ) (h : Euclidean d) (hlarge : 1 < scale j * ‖h‖) :
    (∫ x in {x | 2 * ‖h‖ < ‖x‖},
      ‖dilatedKernel χ m j (x - h) - dilatedKernel χ m j x‖) ≤
      2 * C * A * (scale j * ‖h‖) ^ (-((order d : ℝ) - (d : ℝ) / 2)) := by
  rcases hKE j with ⟨_hcont, _hw, _hgw, _hwb, hi, _hgi, _hL1, htail⟩
  have hKi : Integrable (dilatedKernel χ m j) :=
    (hi.comp_smul (scale_ne_zero j)).smul (scale j ^ d)
  have htailK : (∫ x in {x | ‖h‖ < ‖x‖}, ‖dilatedKernel χ m j x‖) ≤
      C * A * (scale j * ‖h‖) ^ (-((order d : ℝ) - (d : ℝ) / 2)) := by
    change (∫ x in {x | ‖h‖ < ‖x‖}, ‖(scale j ^ d : ℝ) • inverseKernel χ m j (scale j • x)‖) ≤ _
    rw [normalizedDilation_tail _ (scale_pos j)]
    exact htail (scale j * ‖h‖) hlarge.le
  calc
    _ ≤ 2 * (∫ x in {x | ‖h‖ < ‖x‖}, ‖dilatedKernel χ m j x‖) :=
      translation_tail_integral_le hKi h
    _ ≤ 2 * (C * A * (scale j * ‖h‖) ^ (-((order d : ℝ) - (d : ℝ) / 2))) :=
      mul_le_mul_of_nonneg_left htailK (by norm_num)
    _ = _ := by ring

/-- Uniform Hörmander control for finite dyadic sums, conditional only on the
single-kernel estimates. Its coefficient depends on d and the kernel constant. -/
theorem kernelEstimates_hormander {d : ℕ} {χ : Euclidean d → ℝ}
    {m : Euclidean d → ℂ} {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hE : KernelEstimates χ m A C) (J : Finset ℤ) (h : Euclidean d) (hh : h ≠ 0) :
    IntegrableOn (fun x => ‖finiteKernel χ m J (x-h) - finiteKernel χ m J x‖) {x | 2*‖h‖ < ‖x‖} ∧
    (∫ x in {x | 2*‖h‖ < ‖x‖}, ‖finiteKernel χ m J (x-h) - finiteKernel χ m J x‖) ≤
      (((d : ℝ) + 2) * C * (2 + (1 - (2 : ℝ) ^ (-((order d : ℝ) - (d : ℝ) / 2)))⁻¹)) * A := by
  classical
  let δ : ℝ := (order d : ℝ) - (d : ℝ)/2
  let w : ℤ → ℝ := fun j => if scale j * ‖h‖ ≤ 1 then scale j * ‖h‖ else (scale j * ‖h‖) ^ (-δ)
  have hδ : 0 < δ := sub_pos.mpr (order_gt_half d)
  have hcommon : 0 ≤ C*A := mul_nonneg hC hA
  have hw (j : ℤ) : 0 ≤ w j := by
    dsimp only [w]
    split_ifs
    · exact mul_nonneg (scale_pos j).le (norm_nonneg h)
    · exact Real.rpow_nonneg (mul_nonneg (scale_pos j).le (norm_nonneg h)) _
  have hjbound (j : ℤ) :
      (∫ x in {x | 2*‖h‖ < ‖x‖}, ‖dilatedKernel χ m j (x-h) - dilatedKernel χ m j x‖) ≤
      (((d : ℝ)+2) * C * A) * w j := by
    by_cases hj : scale j * ‖h‖ ≤ 1
    · dsimp only [w]
      rw [ite_eq_left hj]
      calc
        _ ≤ (d : ℝ)*C*A*(scale j*‖h‖) := kernelEstimates_small_translation hE j h
        _ ≤ (((d : ℝ)+2)*C*A)*(scale j*‖h‖) := by
          have ht : 0 ≤ scale j*‖h‖ := mul_nonneg (scale_pos j).le (norm_nonneg h)
          nlinarith [mul_nonneg hcommon ht]
    · dsimp only [w]
      rw [ite_eq_right hj]
      calc
        _ ≤ 2*C*A*(scale j*‖h‖)^(-δ) :=
          dilatedKernel_large_translation_tail_le hE j h (lt_of_not_ge hj)
        _ ≤ (((d : ℝ)+2)*C*A)*(scale j*‖h‖)^(-δ) := by
          have ht : 0 ≤ (scale j*‖h‖)^(-δ) := Real.rpow_nonneg (mul_nonneg (scale_pos j).le (norm_nonneg h)) _
          have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
          nlinarith [mul_nonneg (mul_nonneg hd hcommon) ht]
  obtain ⟨hInt, hsum⟩ := kernelEstimates_finite_difference_le_sum hE J h
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∑ j ∈ J, ∫ x in {x | 2*‖h‖ < ‖x‖}, ‖dilatedKernel χ m j (x-h) - dilatedKernel χ m j x‖ := hsum
    _ ≤ ∑ j ∈ J, (((d : ℝ)+2)*C*A)*w j := Finset.sum_le_sum (fun j _ => hjbound j)
    _ = (((d : ℝ)+2)*C*A) * ∑ j ∈ J, w j := by rw [Finset.mul_sum]
    _ ≤ (((d : ℝ)+2)*C*A) * (2 + (1 - (2 : ℝ)^(-δ))⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact finite_dyadic_difference_sum_le (norm_pos_iff.mpr hh) hδ J
    _ = _ := by dsimp only [δ]; ring




/-- The Fourier and convolution conclusions combine with any uniform Hörmander bound. -/
theorem finiteSumEstimates_of_hormander {d : ℕ} (hd : 1 ≤ d)
    {χ : Euclidean d → ℝ} (hχ : IsCutoff χ) {m : Euclidean d → ℂ}
    {A C : ℝ} (hm : SymbolBound m A) (hC : 2 ≤ C)
    (hH : ∀ (J : Finset ℤ) (h : Euclidean d), h ≠ 0 →
      IntegrableOn (fun x => ‖finiteKernel χ m J (x-h) - finiteKernel χ m J x‖)
        {x | 2*‖h‖ < ‖x‖} ∧
      (∫ x in {x | 2*‖h‖ < ‖x‖}, ‖finiteKernel χ m J (x-h) - finiteKernel χ m J x‖) ≤ C*A) :
    FiniteSumEstimates χ m A C := by
  intro J
  obtain ⟨T, hT, hrep⟩ := finiteL2Multiplier_convolution_exists hd hχ hm J
  exact ⟨finiteKernel_integrable hχ hm J, finiteKernel_fourier hχ hm J,
    ⟨T, hT.trans (mul_le_mul_of_nonneg_right hC (symbol_bound_nonneg hd hm)), hrep⟩, hH J⟩


theorem cutoff_partition : P102.Specs.U3.MihlinDyadicKernels.cutoffPartitionType :=
  fun d => ⟨cutoff d, cutoff_isCutoff d, cutoff_isPartition d⟩

theorem annular_symbol_properties :
    P102.Specs.U3.MihlinDyadicKernels.annularSymbolPropertiesType := by
  intro d χ hχ m A hm j
  exact ⟨annularSymbol_contDiff hχ hm j, annularSymbol_hasCompactSupport hχ m j,
    annularSymbol_integrable hχ hm j, inverseKernel_contDiff hχ hm j⟩

theorem finite_symbol_bound : P102.Specs.U3.MihlinDyadicKernels.finiteSymbolBoundType := by
  intro d hd χ hχ m A hm J ξ
  exact finiteSymbol_norm_le hd hχ hm J ξ

/-- The source's dyadic kernels, with one constant uniform in the symbol,
its bound, the dyadic index, and every finite collection of scales. -/
theorem dyadic_kernels : P102.Specs.U3.MihlinDyadicKernels.theoremType := by
  intro d hd
  obtain ⟨C, hCpos, hC⟩ := kernelEstimates_exists hd (cutoff_isCutoff d)
  let H : ℝ := ((d : ℝ) + 2) * C *
    (2 + (1 - (2 : ℝ) ^ (-((order d : ℝ) - (d : ℝ) / 2)))⁻¹)
  let D : ℝ := max C (max 2 H)
  have hCD : C ≤ D := le_max_left _ _
  have h2D : 2 ≤ D := (le_max_left 2 H).trans (le_max_right C (max 2 H))
  have hHD : H ≤ D := (le_max_right 2 H).trans (le_max_right C (max 2 H))
  refine ⟨cutoff d, D, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) h2D,
    cutoff_isCutoff d, cutoff_isPartition d, ?_⟩
  intro m A hm
  have hA := symbol_bound_nonneg hd hm
  have hE := hC m A hm
  refine ⟨kernelEstimates_mono hA hCD hE,
    finiteSumEstimates_of_hormander hd (cutoff_isCutoff d) hm h2D ?_⟩
  intro J h hh
  obtain ⟨hI, hH⟩ := kernelEstimates_hormander hA hCpos.le hE J h hh
  exact ⟨hI, hH.trans (mul_le_mul_of_nonneg_right hHD hA)⟩

end P102.U3.Mihlin
