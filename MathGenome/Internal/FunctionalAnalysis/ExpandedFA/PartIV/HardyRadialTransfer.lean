import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyRadialTransfer
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyCompactTransfer
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyMaximalInterfaces
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Filter Metric
open scoped ENNReal Topology ContDiff

namespace ExpandedFA.PartIV.HardyRadialTransfer
open ExpandedFA.Fourier HardyMaximalSpec HardyLowpassSpec
  HardyCompactTransferSpec HardyRadialTransferSpec

lemma norm_basisVector {d : ℕ} (i : Fin d) : ‖basisVector i‖ = 1 := by
  simp [basisVector]

lemma coordinatePartial_const_smul {𝕜 : Type} [RCLike 𝕜] {d k : ℕ}
    (a : Fin k → Fin d) (u : Euclidean d → 𝕜) (hu : ContDiff ℝ ∞ u)
    (c : ℝ) (x : Euclidean d) :
    coordinatePartial a (c • u) x = c • coordinatePartial a u x := by
  unfold coordinatePartial
  rw [iteratedFDeriv_const_smul_apply (hu.of_le (by simp)).contDiffAt]
  rfl

lemma coordinatePartial_comp_smul {𝕜 : Type} [RCLike 𝕜] {d k : ℕ}
    (a : Fin k → Fin d) (u : Euclidean d → 𝕜) (hu : ContDiff ℝ ∞ u)
    (c : ℝ) (x : Euclidean d) :
    coordinatePartial a (fun y => u (c • y)) x =
      c ^ k • coordinatePartial a u (c • x) := by
  unfold coordinatePartial
  rw [iteratedFDeriv_comp_const_smul c (hu.of_le (by simp))]
  rfl

lemma coordinatePartial_le_norm {𝕜 : Type} [RCLike 𝕜] {d k : ℕ}
    (a : Fin k → Fin d) (u : Euclidean d → 𝕜) (x : Euclidean d) :
    ‖coordinatePartial a u x‖ ≤ ‖iteratedFDeriv ℝ k u x‖ := by
  simpa [coordinatePartial, norm_basisVector] using
    (iteratedFDeriv ℝ k u x).le_opNorm (fun i => basisVector (a i))

lemma norm_multilinear_le_sum_coordinates {𝕜 : Type} [RCLike 𝕜] {d k : ℕ}
    (T : (Euclidean d [×k]→L[ℝ] 𝕜)) :
    ‖T‖ ≤ ∑ a : Fin k → Fin d, ‖T (fun i => basisVector (a i))‖ := by
  classical
  apply T.opNorm_le_bound (by positivity)
  intro v
  have hv (i : Fin k) : ∑ j : Fin d, v i j • basisVector j = v i := by
    simpa [basisVector] using (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (v i)
  calc
    ‖T v‖ = ‖T (fun i => ∑ j : Fin d, v i j • basisVector j)‖ := by simp_rw [hv]
    _ = ‖∑ a : Fin k → Fin d, (∏ i, v i (a i)) •
        T (fun i => basisVector (a i))‖ := by
      congr 1
      change T.toMultilinearMap (fun i => ∑ j : Fin d, v i j • basisVector j) = _
      rw [T.toMultilinearMap.map_sum]
      simp only [ContinuousMultilinearMap.coe_coe,
        ContinuousMultilinearMap.map_smul_univ]
    _ ≤ ∑ a : Fin k → Fin d,
        ‖(∏ i, v i (a i)) • T (fun i => basisVector (a i))‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin k → Fin d,
        ‖T (fun i => basisVector (a i))‖ * ∏ i, ‖v i‖ := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul, norm_prod, mul_comm]
      gcongr with i
      exact PiLp.norm_apply_le (v i) (a i)
    _ = (∑ a : Fin k → Fin d, ‖T (fun i => basisVector (a i))‖) * ∏ i, ‖v i‖ :=
      (Finset.sum_mul _ _ _).symm

/-- Coordinate decay implies the operator-norm decay needed for the
bilinear derivative estimate. The finite sum retains all coordinate words. -/
lemma fixed_kernel_derivative_decay {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Euclidean d → 𝕜) (hΦ : IsFixedKernel Φ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ‖iteratedFDeriv ℝ k Φ x‖ ≤ C / (1 + ‖x‖) ^ (d + 1 + k) := by
  classical
  choose C hC h using hΦ.2.2 k
  refine ⟨∑ a : Fin k → Fin d, C a, Finset.sum_nonneg (fun a _ => hC a), ?_⟩
  intro x
  apply (norm_multilinear_le_sum_coordinates _).trans
  calc
    _ ≤ ∑ a : Fin k → Fin d, C a / (1 + ‖x‖) ^ (d + 1 + k) := by
      apply Finset.sum_le_sum
      intro a _
      exact h a x
    _ = _ := (Finset.sum_div _ _ _).symm

/-- Amplitude-normalized dilations used on a fixed annulus. -/
def rescaledKernel {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (Φ : Euclidean d → 𝕜) (y : Euclidean d) : 𝕜 :=
  s ^ (d + 1) • Φ (s • y)

lemma rescaledKernel_contDiff {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (Φ : Euclidean d → 𝕜) (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (rescaledKernel s Φ) := by
  unfold rescaledKernel
  exact (hΦ.comp (contDiff_id.const_smul s)).const_smul _

lemma rescaledKernel_derivative_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Euclidean d → 𝕜) (hΦ : IsFixedKernel Φ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → ∀ y : Euclidean d,
      (1 / 2 : ℝ) ≤ ‖y‖ → ‖iteratedFDeriv ℝ k (rescaledKernel s Φ) y‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := fixed_kernel_derivative_decay Φ hΦ k
  refine ⟨2 ^ (d + 1 + k) * C, by positivity, ?_⟩
  intro s hs y hy
  have hp : 0 < (1 + ‖s • y‖) ^ (d + 1 + k) := by positivity
  have hpow : s ^ (d + 1 + k) ≤
      2 ^ (d + 1 + k) * (1 + ‖s • y‖) ^ (d + 1 + k) := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ hs.le
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    nlinarith
  unfold rescaledKernel
  rw [iteratedFDeriv_const_smul_apply' (f := fun z => Φ (s • z))
    (by simpa [Function.comp_def] using
      ((hΦ.1.comp (contDiff_id.const_smul s)).of_le (by simp : (k : ℕ∞ω) ≤ (∞ : ℕ∞ω))).contDiffAt)]
  rw [iteratedFDeriv_comp_const_smul s (hΦ.1.of_le (by simp))]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hs.le _)]
  calc
    _ = s ^ (d + 1 + k) * ‖iteratedFDeriv ℝ k Φ (s • y)‖ := by rw [pow_add]; ring
    _ ≤ s ^ (d + 1 + k) * (C / (1 + ‖s • y‖) ^ (d + 1 + k)) :=
      mul_le_mul_of_nonneg_left (h _) (by positivity)
    _ ≤ _ := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hp).mpr
      nlinarith [mul_le_mul_of_nonneg_right hpow hC]

/-- The fixed radial cutoff: one on the unit ball, zero outside the ball of radius two. -/
def cutoff (d : ℕ) : ContDiffBump (0 : Euclidean d) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def annularCutoff (d : ℕ) (y : Euclidean d) : ℝ :=
  cutoff d y - cutoff d ((2 : ℝ) • y)

lemma annularCutoff_smooth (d : ℕ) : ContDiff ℝ ∞ (annularCutoff d) :=
  (cutoff d).contDiff.sub ((cutoff d).contDiff.comp (contDiff_id.const_smul 2))

lemma annularCutoff_support (d : ℕ) :
    tsupport (annularCutoff d) ⊆ Metric.closedBall 0 2 := by
  apply closure_minimal _ isClosed_closedBall
  intro y hy
  by_contra h
  have hy' : 2 < ‖y‖ := by simpa using h
  have h₁ : cutoff d y = 0 := (cutoff d).zero_of_le_dist (by simpa [cutoff] using hy'.le)
  have h₂ : cutoff d ((2 : ℝ) • y) = 0 := by
    apply (cutoff d).zero_of_le_dist
    simp only [cutoff, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  exact hy (by simp [annularCutoff, h₁, h₂])

lemma annularCutoff_compact (d : ℕ) : HasCompactSupport (annularCutoff d) :=
  (isCompact_closedBall (0 : Euclidean d) 2).of_isClosed_subset isClosed_closure (annularCutoff_support d)

lemma annularCutoff_zero {d : ℕ} {y : Euclidean d} (hy : ‖y‖ < 1 / 2) :
    annularCutoff d y = 0 := by
  have h₁ : cutoff d y = 1 := (cutoff d).one_of_mem_closedBall (by
    simp only [cutoff, Metric.mem_closedBall, dist_zero_right]
    linarith)
  have h₂ : cutoff d ((2 : ℝ) • y) = 1 := (cutoff d).one_of_mem_closedBall (by
    simp only [cutoff, Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith)
  simp [annularCutoff, h₁, h₂]

lemma annular_family_derivative_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Euclidean d → 𝕜) (hΦ : IsFixedKernel Φ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → ∀ y : Euclidean d,
      ‖iteratedFDeriv ℝ k (fun z => annularCutoff d z • rescaledKernel s Φ z) y‖ ≤ C := by
  classical
  obtain ⟨D, hD, hDb⟩ := (annularCutoff_compact d).exists_bound_iteratedFDeriv
    (annularCutoff_smooth d) k
  choose C hC hCb using rescaledKernel_derivative_bound Φ hΦ
  have hsum : 0 ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * D * C (k - i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hD) (hC _)
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * D * C (k - i), hsum, ?_⟩
  intro s hs y
  by_cases hy : ‖y‖ < 1 / 2
  · have heq : (fun z => annularCutoff d z • rescaledKernel s Φ z) =ᶠ[𝓝 y]
        (fun _ => (0 : 𝕜)) := by
      filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hy] with z hz
      simp [annularCutoff_zero hz]
    rw [heq.iteratedFDeriv (𝕜 := ℝ) k |>.eq_of_nhds]
    simpa using hsum
  · apply (norm_iteratedFDeriv_smul_le (annularCutoff_smooth d)
      (rescaledKernel_contDiff s Φ hΦ.1) y (by simp : (k : ℕ∞ω) ≤ (∞ : ℕ∞ω))).trans
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i ≤ k := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hDb i hi' y) (by positivity))
      (hCb (k - i) s hs y (le_of_not_gt hy)) (norm_nonneg _) (by positivity)

/-- Literal compact pieces of the annular expansion. -/
def tailTests {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Euclidean d → 𝕜) : ℕ → Euclidean d → 𝕜
  | 0 => fun y => cutoff d y • Φ y
  | m + 1 => fun y => annularCutoff d y • rescaledKernel ((2 : ℝ) ^ (m + 1)) Φ y

lemma tailTests_smooth {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Euclidean d → 𝕜) (hΦ : IsFixedKernel Φ) (m : ℕ) :
    ContDiff ℝ ∞ (tailTests Φ m) := by
  cases m with
  | zero => exact (cutoff d).contDiff.smul hΦ.1
  | succ m =>
    exact (annularCutoff_smooth d).smul
      (rescaledKernel_contDiff _ Φ hΦ.1)

lemma tailTests_support {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Euclidean d → 𝕜) (m : ℕ) :
    tsupport (tailTests Φ m) ⊆ closedBall 0 2 := by
  cases m with
  | zero => exact (tsupport_smul_subset_left _ _).trans (by
      simpa [cutoff] using (cutoff d).tsupport_eq.subset)
  | succ m => exact (tsupport_smul_subset_left _ _).trans (annularCutoff_support d)

lemma tailTests_uniform {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Euclidean d → 𝕜) (hΦ : IsFixedKernel Φ) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m, IsUniformTest N 3 B (tailTests Φ m) := by
  classical
  choose C hC hb using annular_family_derivative_bound Φ hΦ
  have hc : HasCompactSupport (tailTests Φ 0) :=
    (isCompact_closedBall (0 : Euclidean d) 2).of_isClosed_subset
      isClosed_closure (tailTests_support Φ 0)
  obtain ⟨D, hD, hd⟩ := hc.exists_bound_iteratedFDeriv (tailTests_smooth Φ hΦ 0) N
  have hsum : 0 ≤ ∑ i ∈ Finset.range (N + 1), C i :=
    Finset.sum_nonneg fun i _ => hC i
  refine ⟨(∑ i ∈ Finset.range (N + 1), C i) + D, add_nonneg hsum hD, ?_⟩
  intro m
  refine ⟨tailTests_smooth Φ hΦ m, (tailTests_support Φ m).trans ?_, ?_⟩
  · exact closedBall_subset_ball (by norm_num)
  · intro k hk a x
    apply (coordinatePartial_le_norm a _ x).trans
    cases m with
    | zero => exact (hd k hk x).trans (le_add_of_nonneg_left hsum)
    | succ m =>
      apply (hb k ((2 : ℝ) ^ (m + 1)) (by positivity) x).trans
      exact (Finset.single_le_sum (fun i _ => hC i)
        (Finset.mem_range.mpr (by omega))).trans (le_add_of_nonneg_right hD)

lemma integrable_dilate {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u : Euclidean d → 𝕜) (hu : Integrable u) {t : ℝ} (ht : t ≠ 0) :
    Integrable (dilate t u) := by
  change Integrable (fun x => (t ^ d)⁻¹ • u (t⁻¹ • x))
  exact (hu.comp_smul (inv_ne_zero ht)).smul ((t ^ d)⁻¹)

lemma tailTests_integrable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Euclidean d → 𝕜) (hΦ : IsFixedKernel Φ) (m : ℕ) :
    Integrable (tailPiece (tailTests Φ) m) := by
  have hu : Integrable (tailTests Φ m) := (tailTests_smooth Φ hΦ m).continuous.integrable_of_hasCompactSupport
    ((isCompact_closedBall (0 : Euclidean d) 2).of_isClosed_subset
      isClosed_closure (tailTests_support Φ m))
  exact (integrable_dilate _ hu (by positivity : (2 : ℝ) ^ m ≠ 0)).smul _

lemma tailPiece_zero {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Euclidean d → 𝕜) (x : Euclidean d) :
    tailPiece (tailTests Φ) 0 x = cutoff d x • Φ x := by
  simp [tailPiece, tailTests, dilate]

lemma tailPiece_succ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Euclidean d → 𝕜) (m : ℕ) (x : Euclidean d) :
    tailPiece (tailTests Φ) (m + 1) x =
      (cutoff d (((2 : ℝ) ^ (m + 1))⁻¹ • x) -
        cutoff d (((2 : ℝ) ^ m)⁻¹ • x)) • Φ x := by
  have hpow : ((2 : ℝ) ^ (m + 1)) ≠ 0 := by positivity
  have hscale : (2 : ℝ) * ((2 : ℝ) ^ (m + 1))⁻¹ = ((2 : ℝ) ^ m)⁻¹ := by
    rw [pow_succ]
    field_simp
  simp only [tailPiece, Pi.smul_apply, tailTests, dilate, annularCutoff,
    rescaledKernel, smul_smul, mul_inv_cancel₀ hpow, one_smul, hscale]
  congr 1
  simp only [one_div, inv_pow, pow_succ]
  field_simp

lemma tailSum_succ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Euclidean d → 𝕜) (n : ℕ) (x : Euclidean d) :
    tailSum (tailTests Φ) (n + 1) x = cutoff d (((2 : ℝ) ^ n)⁻¹ • x) • Φ x := by
  induction n with
  | zero => simp [tailSum, tailPiece_zero]
  | succ n hn =>
    simp only [tailSum, Finset.sum_apply] at hn ⊢
    rw [Finset.sum_range_succ, hn, tailPiece_succ]
    rw [sub_smul]
    abel

lemma cutoff_error_le {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Euclidean d → 𝕜) (n : ℕ) (x : Euclidean d) :
    ‖Φ x - tailSum (tailTests Φ) (n + 1) x‖ ≤ ‖Φ x‖ := by
  rw [tailSum_succ, show Φ x - cutoff d (((2 : ℝ) ^ n)⁻¹ • x) • Φ x =
      (1 - cutoff d (((2 : ℝ) ^ n)⁻¹ • x)) • Φ x by module, norm_smul]
  have h₀ := (cutoff d).nonneg (x := ((2 : ℝ) ^ n)⁻¹ • x)
  have h₁ := (cutoff d).le_one (x := ((2 : ℝ) ^ n)⁻¹ • x)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  nlinarith [norm_nonneg (Φ x)]

lemma tailSum_uniform_error {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Euclidean d → 𝕜) (hΦ : IsFixedKernel Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : Euclidean d),
      ‖Φ x - tailSum (tailTests Φ) (n + 1) x‖ ≤ C * (1 / 2 : ℝ) ^ n := by
  obtain ⟨C, hC, hb⟩ := hΦ.2.2 0 Fin.elim0
  refine ⟨C, hC, ?_⟩
  intro n x
  by_cases hx : ‖x‖ ≤ (2 : ℝ) ^ n
  · have hone : cutoff d (((2 : ℝ) ^ n)⁻¹ • x) = 1 := by
      apply (cutoff d).one_of_mem_closedBall
      simp only [cutoff, mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _)]
      exact (inv_mul_le_iff₀ (by positivity)).mpr (by simpa using hx)
    rw [tailSum_succ, hone, one_smul, sub_self, norm_zero]
    positivity
  · have hb' : ‖Φ x‖ ≤ C / (1 + ‖x‖) ^ (d + 1) := by
      simpa only [coordinatePartial, iteratedFDeriv_zero_apply, add_zero] using hb x
    have hp : (2 : ℝ) ^ n ≤ (1 + ‖x‖) ^ (d + 1) :=
      (le_of_lt (by linarith : (2 : ℝ) ^ n < 1 + ‖x‖)).trans
        (le_self_pow₀ (by linarith [norm_nonneg x]) (by omega : d + 1 ≠ 0))
    apply (cutoff_error_le Φ n x).trans (hb'.trans ?_)
    simpa only [one_div, inv_pow, div_eq_mul_inv, one_mul] using
      div_le_div_of_nonneg_left hC (by positivity : (0 : ℝ) < 2 ^ n) hp

lemma tailTests_uniform_convergence {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Euclidean d → 𝕜) (hΦ : IsFixedKernel Φ) :
    TendstoUniformly (tailSum (tailTests Φ)) Φ atTop := by
  obtain ⟨C, hC, hb⟩ := tailSum_uniform_error Φ hΦ
  have hg : Tendsto (fun n : ℕ => C * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul C
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have he : ∀ᶠ n : ℕ in atTop, ∀ x,
      dist (Φ x) (tailSum (tailTests Φ) (n + 1) x) < ε := by
    filter_upwards [hg.eventually (gt_mem_nhds hε)] with n hn x
    simpa only [dist_eq_norm] using (hb n x).trans_lt hn
  have hm : ∀ᶠ n in Filter.map (fun n : ℕ => n + 1) atTop,
      ∀ x, dist (Φ x) (tailSum (tailTests Φ) n x) < ε := he
  simpa only [map_add_atTop_eq_nat] using hm

lemma tailTests_L1_convergence {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Euclidean d → 𝕜) (hΦ : IsFixedKernel Φ) :
    Tendsto (fun n => ∫ x, ‖Φ x - tailSum (tailTests Φ) n x‖) atTop (𝓝 0) := by
  have hi : Integrable Φ := (HardyLowpass.fixed_kernel_integrable Φ hΦ).1
  have hu := tailTests_uniform_convergence Φ hΦ
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hc (n : ℕ) : Continuous (tailSum (tailTests Φ) (n + 1)) := by
    simp_rw [show tailSum (tailTests Φ) (n + 1) =
      (fun x => cutoff d (((2 : ℝ) ^ n)⁻¹ • x) • Φ x) from funext (tailSum_succ Φ n)]
    exact ((cutoff d).continuous.comp (continuous_id.const_smul (((2 : ℝ) ^ n)⁻¹))).smul hΦ.1.continuous
  have ht := tendsto_integral_of_dominated_convergence
    (F := fun n x => ‖Φ x - tailSum (tailTests Φ) (n + 1) x‖)
    (f := fun _ => (0 : ℝ)) (fun x => ‖Φ x‖)
    (fun n => (hΦ.1.continuous.sub (hc n)).norm.aestronglyMeasurable) hi.norm
    (fun n => Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs, abs_norm] using cutoff_error_le Φ n x))
    (Filter.Eventually.of_forall (fun x => by
      have hx : Tendsto (fun n => Φ x - tailSum (tailTests Φ) n x)
          atTop (𝓝 (Φ x - Φ x)) := tendsto_const_nhds.sub (hu.tendsto_at x)
      simpa only [sub_self, norm_zero, Function.comp_def] using hx.norm.comp (tendsto_add_atTop_nat 1)))
  simpa only [integral_zero] using ht

lemma tailTests_expansion {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Euclidean d → 𝕜) (hΦ : IsFixedKernel Φ) (N : ℕ) :
    ∃ B : ℝ, IsTailExpansion N Φ (tailTests Φ) 3 B := by
  obtain ⟨B, hB, hb⟩ := tailTests_uniform Φ hΦ N
  exact ⟨B, by norm_num, hB, hb, tailTests_integrable Φ hΦ,
    tailTests_uniform_convergence Φ hΦ, tailTests_L1_convergence Φ hΦ⟩

theorem tail_bumps : TailBumps := by
  intro 𝕜 _ d _ N Φ hΦ
  obtain ⟨B, hb⟩ := tailTests_expansion Φ hΦ N
  exact ⟨tailTests Φ, 3, B, hb⟩

lemma dilate_dilate {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s t : ℝ) (u : Euclidean d → 𝕜) :
    dilate s (dilate t u) = dilate (s * t) u := by
  funext x
  simp only [HardyMaximalSpec.dilate, mul_pow, mul_inv, smul_smul, mul_comm]

lemma dilate_smul {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (t c : ℝ) (u : Euclidean d → 𝕜) : dilate t (c • u) = c • dilate t u := by
  funext x
  simp only [HardyMaximalSpec.dilate, Pi.smul_apply, smul_smul]
  congr 1
  ring

lemma convolve_smul_left {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (c : ℝ) (u f : Euclidean d → 𝕜) : convolve (c • u) f = c • convolve u f := by
  funext z
  change (∫ y, (c • u y) * f (z - y)) = c • (∫ y, u y * f (z - y))
  simp_rw [smul_mul_assoc]
  exact integral_smul c _

/-- Normalization uses only the finite derivative bounds, with constants
independent of the chosen test. -/
lemma normalize_uniform_test {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    {a B : ℝ} (ha : 1 ≤ a) (hB : 0 ≤ B)
    (ψ : Euclidean d → 𝕜) (hψ : IsUniformTest N a B ψ) :
    ∃ θ : Tests 𝕜 d N, ψ = ((B * a ^ N + 1) * a ^ d) • dilate a θ.val := by
  have hap : 0 < a := lt_of_lt_of_le zero_lt_one ha
  let b : ℝ := B * a ^ N + 1
  have hbp : 0 < b := by dsimp [b]; positivity
  let θ : Euclidean d → 𝕜 := fun y => b⁻¹ • ψ (a • y)
  have hs : ContDiff ℝ ∞ θ :=
    (hψ.1.comp (contDiff_id.const_smul a)).const_smul _
  have ht : IsTest N θ := by
    refine ⟨hs, ?_, ?_⟩
    · intro y hy
      have hy' := (tsupport_smul_subset_right (fun _ => b⁻¹)
        (fun y => ψ (a • y))) hy
      have hy'' := tsupport_comp_subset_preimage ψ (continuous_id.const_smul a) hy'
      have hn := hψ.2.1 hy''
      simp only [mem_ball, dist_zero_right, Pi.smul_apply, id_eq, norm_smul, Real.norm_eq_abs,
        abs_of_pos hap] at hn ⊢
      nlinarith
    · intro k hk v y
      change ‖coordinatePartial v (b⁻¹ • (fun z => ψ (a • z))) y‖ ≤ 1
      have hcomp : ContDiff ℝ ∞ (fun z => ψ (a • z)) :=
        hψ.1.comp (contDiff_id.const_smul a)
      rw [coordinatePartial_const_smul v (fun z => ψ (a • z)) hcomp,
        coordinatePartial_comp_smul v ψ hψ.1]
      simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hbp,
        abs_of_nonneg (pow_nonneg hap.le _)]
      have hpow : a ^ k ≤ a ^ N := pow_le_pow_right₀ ha hk
      have hn := hψ.2.2 k hk v (a • y)
      have hmul : a ^ k * ‖coordinatePartial v ψ (a • y)‖ ≤ b := by
        calc
          _ ≤ a ^ k * B := mul_le_mul_of_nonneg_left hn (by positivity)
          _ ≤ a ^ N * B := mul_le_mul_of_nonneg_right hpow hB
          _ ≤ b := by dsimp [b]; nlinarith
      exact (inv_mul_le_iff₀ hbp).mpr (by simpa using hmul)
  refine ⟨⟨θ, ht⟩, ?_⟩
  funext x
  change ψ x = (b * a ^ d) • ((a ^ d)⁻¹ • (b⁻¹ • ψ (a • (a⁻¹ • x))))
  simp only [smul_smul, mul_inv_cancel₀ hap.ne', one_smul]
  have he : b * a ^ d * ((a ^ d)⁻¹ * b⁻¹) = 1 := by field_simp
  rw [he, one_smul]

lemma uniform_test_grand_bound {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    {a B : ℝ} (ha : 1 ≤ a) (hB : 0 ≤ B)
    (ψ : Euclidean d → 𝕜) (hψ : IsUniformTest N a B ψ)
    (f : Euclidean d → 𝕜) (t : ℝ) (ht : 0 < t) (x : Euclidean d) :
    ENNReal.ofReal ‖convolve (dilate t ψ) f x‖ ≤
      ENNReal.ofReal ((B * a ^ N + 1) * a ^ d) * grand N f x := by
  obtain ⟨θ, hθ⟩ := normalize_uniform_test ha hB ψ hψ
  have hap : 0 < a := lt_of_lt_of_le zero_lt_one ha
  rw [hθ, dilate_smul, dilate_dilate, convolve_smul_left, Pi.smul_apply,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    ENNReal.ofReal_mul (by positivity)]
  apply mul_le_mul' le_rfl
  exact (le_iSup_of_le (⟨t * a, mul_pos ht hap⟩ : Scale)
    (le_iSup_of_le θ le_rfl))

lemma convolve_eq_integral_swap {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u f : Euclidean d → 𝕜) (z : Euclidean d) :
    convolve u f z = ∫ y, u (z - y) * f y := by
  rw [HardyLowpass.convolve_comm u f]
  change (∫ y, f y * u (z - y)) = _
  simp_rw [mul_comm]

lemma integrable_kernel_mul {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u f : Euclidean d → 𝕜) (hu : Continuous u) (hf : Integrable f)
    {C : ℝ} (hb : ∀ x, ‖u x‖ ≤ C) (z : Euclidean d) :
    Integrable (fun y => u (z - y) * f y) := by
  apply (hf.norm.const_mul C).mono'
    (((hu.comp (continuous_const.sub continuous_id)).aestronglyMeasurable).mul
      hf.aestronglyMeasurable)
  filter_upwards [] with y
  change ‖u (z - y) * f y‖ ≤ C * ‖f y‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hb (z - y)) (norm_nonneg (f y))

lemma continuous_dilate {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u : Euclidean d → 𝕜) (hu : Continuous u) (t : ℝ) : Continuous (dilate t u) := by
  exact (hu.comp (continuous_id.const_smul t⁻¹)).const_smul _

lemma norm_dilate_le {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u : Euclidean d → 𝕜) {C : ℝ} (hb : ∀ x, ‖u x‖ ≤ C)
    (t : ℝ) (x : Euclidean d) : ‖dilate t u x‖ ≤ ‖(t ^ d)⁻¹‖ * C := by
  rw [HardyMaximalSpec.dilate, norm_smul]
  exact mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)

lemma convolve_finset_sum {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (F : ℕ → Euclidean d → 𝕜) (hc : ∀ m, Continuous (F m))
    (hb : ∀ m, ∃ C : ℝ, ∀ x, ‖F m x‖ ≤ C)
    (f : Euclidean d → 𝕜) (hf : Integrable f) (n : ℕ) (z : Euclidean d) :
    convolve (∑ m ∈ Finset.range n, F m) f z =
      ∑ m ∈ Finset.range n, convolve (F m) f z := by
  simp_rw [convolve_eq_integral_swap, Finset.sum_apply, Finset.sum_mul]
  apply integral_finsetSum
  intro m _
  obtain ⟨C, hC⟩ := hb m
  exact integrable_kernel_mul (F m) f (hc m) hf hC z

lemma dilate_finset_sum {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (F : ℕ → Euclidean d → 𝕜) (n : ℕ) (t : ℝ) :
    dilate t (∑ m ∈ Finset.range n, F m) =
      ∑ m ∈ Finset.range n, dilate t (F m) := by
  ext x
  simp only [HardyMaximalSpec.dilate, Finset.sum_apply, Finset.smul_sum]

lemma uniform_test_norm_bound {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    {a B : ℝ} (u : Euclidean d → 𝕜) (hu : IsUniformTest N a B u)
    (x : Euclidean d) : ‖u x‖ ≤ B := by
  simpa only [coordinatePartial, iteratedFDeriv_zero_apply] using
    hu.2.2 0 (Nat.zero_le N) Fin.elim0 x

lemma tail_convolve_sum {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Euclidean d → 𝕜) (hΦ : IsFixedKernel Φ)
    (f : Euclidean d → 𝕜) (hf : Integrable f) (t : ℝ) (n : ℕ) (z : Euclidean d) :
    convolve (dilate t (tailSum (tailTests Φ) n)) f z =
      ∑ m ∈ Finset.range n, (1 / 2 : ℝ) ^ m •
        convolve (dilate (t * (2 : ℝ) ^ m) (tailTests Φ m)) f z := by
  obtain ⟨B, _, hB⟩ := tailTests_uniform Φ hΦ 0
  have hbound m : ∃ C : ℝ, ∀ x, ‖dilate t (tailPiece (tailTests Φ) m) x‖ ≤ C := by
    refine ⟨‖(t ^ d)⁻¹‖ *
      (‖(1 / 2 : ℝ) ^ m‖ * (‖(((2 : ℝ) ^ m) ^ d)⁻¹‖ * B)), ?_⟩
    apply norm_dilate_le
    intro x
    exact (norm_smul _ _).le.trans
      (mul_le_mul_of_nonneg_left
        (norm_dilate_le _ (uniform_test_norm_bound _ (hB m)) _ x) (norm_nonneg _))
  unfold tailSum
  rw [dilate_finset_sum, convolve_finset_sum _ (fun m => ?_) hbound f hf]
  · apply Finset.sum_congr rfl
    intro m _
    rw [tailPiece, dilate_smul, dilate_dilate, convolve_smul_left, Pi.smul_apply]
  · exact continuous_dilate _ ((continuous_dilate _ (tailTests_smooth Φ hΦ m).continuous _).const_smul _) _

lemma tail_convolve_tendsto {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Euclidean d → 𝕜) (hΦ : IsFixedKernel Φ)
    (f : Euclidean d → 𝕜) (hf : Integrable f) (t : ℝ) (z : Euclidean d) :
    Tendsto (fun n => convolve (dilate t (tailSum (tailTests Φ) n)) f z)
      atTop (𝓝 (convolve (dilate t Φ) f z)) := by
  obtain ⟨C, hC⟩ := HardyMaximal.kernel_bounded Φ hΦ
  have hΦb (y : Euclidean d) : ‖Φ y‖ ≤ C := hC (Set.mem_range_self y)
  have hpart (n : ℕ) (y : Euclidean d) : ‖tailSum (tailTests Φ) (n + 1) y‖ ≤ C := by
    rw [tailSum_succ, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (cutoff d).nonneg]
    exact (mul_le_of_le_one_left (norm_nonneg _) (cutoff d).le_one).trans (hΦb y)
  have hcont n : Continuous (tailSum (tailTests Φ) (n + 1)) := by
    have he := funext (tailSum_succ Φ n)
    rw [he]
    exact ((cutoff d).continuous.comp
      (continuous_id.const_smul (((2 : ℝ) ^ n)⁻¹))).smul hΦ.1.continuous
  have hlim := tailTests_uniform_convergence Φ hΦ
  apply (tendsto_add_atTop_iff_nat 1).mp
  simp_rw [convolve_eq_integral_swap]
  apply tendsto_integral_of_dominated_convergence
    (fun y => (‖(t ^ d)⁻¹‖ * C) * ‖f y‖)
  · intro n
    exact ((continuous_dilate _ (hcont n) t).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hf.aestronglyMeasurable
  · exact hf.norm.const_mul _
  · intro n
    filter_upwards [] with y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_dilate_le _ (hpart n) t _) (norm_nonneg _)
  · filter_upwards [] with y
    have hx := (hlim.tendsto_at (t⁻¹ • (z - y))).comp (tendsto_add_atTop_nat 1)
    exact (hx.const_smul ((t ^ d)⁻¹)).mul_const (f y)

lemma half_geometric_sum_le_two (n : ℕ) :
    ∑ m ∈ Finset.range n, (1 / 2 : ℝ) ^ m ≤ 2 := by
  have hg := geom_sum_mul_neg (1 / 2 : ℝ) n
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]

/-- The summable coefficients allow a single estimate for all compact
pieces to pass to the original, noncompact kernel. -/
lemma tail_convolve_norm_le {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Φ : Euclidean d → 𝕜) (hΦ : IsFixedKernel Φ)
    (f : Euclidean d → 𝕜) (hf : Integrable f) (t : ℝ) (z : Euclidean d)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ m, ‖convolve (dilate (t * (2 : ℝ) ^ m) (tailTests Φ m)) f z‖ ≤ M) :
    ‖convolve (dilate t Φ) f z‖ ≤ 2 * M := by
  apply le_of_tendsto (tail_convolve_tendsto Φ hΦ f hf t z).norm
  filter_upwards [] with n
  rw [tail_convolve_sum Φ hΦ f hf]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ m ∈ Finset.range n, (1 / 2 : ℝ) ^ m * M := by
      apply Finset.sum_le_sum
      intro m _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hb m) (by positivity)
    _ = (∑ m ∈ Finset.range n, (1 / 2 : ℝ) ^ m) * M := (Finset.sum_mul _ _ _).symm
    _ ≤ 2 * M := mul_le_mul_of_nonneg_right (half_geometric_sum_le_two n) hM

lemma uniform_test_grand_bound_real {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    {a B : ℝ} (ha : 1 ≤ a) (hB : 0 ≤ B)
    (ψ : Euclidean d → 𝕜) (hψ : IsUniformTest N a B ψ)
    (f : Euclidean d → 𝕜) (t : ℝ) (ht : 0 < t) (x : Euclidean d)
    (hG : grand N f x < ⊤) :
    ‖convolve (dilate t ψ) f x‖ ≤ ((B * a ^ N + 1) * a ^ d) * (grand N f x).toReal := by
  have h := uniform_test_grand_bound ha hB ψ hψ f t ht x
  have hK : 0 ≤ (B * a ^ N + 1) * a ^ d := by positivity
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK ENNReal.toReal_nonneg)).mp
  rwa [ENNReal.ofReal_mul hK, ENNReal.ofReal_toReal hG.ne]

theorem radial_grand : RadialGrand := by
  intro 𝕜 _ d _ N _ Φ hΦ
  obtain ⟨B, hB, hb⟩ := tailTests_uniform Φ hΦ N
  let K : ℝ := (B * 3 ^ N + 1) * 3 ^ d
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨2 * K, by positivity, ?_⟩
  intro f hf x
  by_cases hG : grand N f x < ⊤
  · apply iSup_le
    intro t
    have hm : 0 ≤ K * (grand N f x).toReal := by positivity
    have ht := tail_convolve_norm_le Φ hΦ f hf t.val x hm (fun m =>
      uniform_test_grand_bound_real (by norm_num : (1 : ℝ) ≤ 3) hB
        _ (hb m) f _ (mul_pos t.property (by positivity)) x hG)
    have hh : ENNReal.ofReal ‖convolve (dilate t.val Φ) f x‖ ≤
        ENNReal.ofReal ((2 * K) * (grand N f x).toReal) := by
      apply ENNReal.ofReal_le_ofReal
      convert ht using 1; ring
    rwa [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hG.ne] at hh
  · have he : grand N f x = ⊤ := eq_top_iff.mpr (le_of_not_gt hG)
    rw [he, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))]
    exact le_top

/-- Pass a uniform compact-test estimate through the annular expansion. -/
lemma dyadic_transfer_of_uniform_transfer (hU : UniformTransfer) : DyadicTransfer := by
  intro 𝕜 _ d hd N hN Φ hΦ η R hη
  obtain ⟨B, hB, hb⟩ := tailTests_uniform Φ hΦ N
  obtain ⟨D, hD, hDb⟩ := hU hd N hN η R hη 3 B (by norm_num) hB
  refine ⟨2 * D, by positivity, ?_⟩
  intro f hf x hP j z
  let t : ℝ := (2 : ℝ) ^ (-j)
  have ht : 0 < t := by dsimp [t]; positivity
  have hw : (1 + ‖x - z‖ / t) ^ peetreExponent d =
      (1 + (2 : ℝ) ^ j * ‖x - z‖) ^ peetreExponent d := by
    congr 2
    dsimp [t]
    rw [zpow_neg, div_inv_eq_mul]
    ring
  have hbound (m : ℕ) :
      ‖convolve (dilate (t * (2 : ℝ) ^ m) (tailTests Φ m)) f z‖ ≤
        D * (peetre η f x).toReal * (1 + ‖x - z‖ / t) ^ peetreExponent d := by
    apply (hDb f hf x hP _ (hb m) _ (mul_pos ht (by positivity)) z).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_left (norm_nonneg _) ht
    exact le_mul_of_one_le_right ht.le (one_le_pow₀ (by norm_num))
  have hh := tail_convolve_norm_le Φ hΦ f hf t z (by positivity) hbound
  rw [hw] at hh
  convert hh using 1; ring

/-- The dyadic radial estimate, with one constant before all data f, x, j and z. -/
theorem dyadic_transfer : DyadicTransfer :=
  dyadic_transfer_of_uniform_transfer HardyCompactTransfer.uniform_transfer

end ExpandedFA.PartIV.HardyRadialTransfer
