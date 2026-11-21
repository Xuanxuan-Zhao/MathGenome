import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Spectral.HermitianResidualGap
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.MatrixData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
open scoped BigOperators
namespace NumAnalysis206.HermitianResidualGap
open MatrixDefinitions
variable {K : Type*} [RCLike K] {n : ℕ}

lemma residual_inner (A : Mat K n n) (hA : A.IsHermitian) (v : Vec K n)
    (μ : ℝ) (i : Fin n) :
    inner K (eigenbasis A hA i) (A.toEuclideanLin v - (μ : K) • v) =
      ((eigenvalue A hA i - μ : ℝ) : K) * inner K (eigenbasis A hA i) v := by
  rw [inner_sub_right, ← (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) _ _,
    MatrixData.eigenbasis_action A hA i, inner_smul_left, inner_smul_right]
  simp [map_sub, sub_mul]

lemma residual_norm_sq (A : Mat K n n) (hA : A.IsHermitian) (v : Vec K n) (μ : ℝ) :
    ‖A.toEuclideanLin v - (μ : K) • v‖ ^ 2 =
      ∑ i, |eigenvalue A hA i - μ| ^ 2 * ‖inner K (eigenbasis A hA i) v‖ ^ 2 := by
  rw [← (eigenbasis A hA).sum_sq_norm_inner_right]
  apply Finset.sum_congr rfl
  intro i _
  rw [residual_inner, norm_mul, mul_pow, RCLike.norm_ofReal]

lemma lower_bound (A : Mat K n n) (hA : A.IsHermitian) (v : Vec K n)
    (μ δ : ℝ) (hδ : 0 ≤ δ) (hg : ∀ i, δ ≤ |eigenvalue A hA i - μ|) :
    δ * ‖v‖ ≤ ‖A.toEuclideanLin v - (μ : K) • v‖ := by
  have hs : (δ * ‖v‖) ^ 2 ≤ ‖A.toEuclideanLin v - (μ : K) • v‖ ^ 2 := by
    rw [mul_pow, ← (eigenbasis A hA).sum_sq_norm_inner_right, Finset.mul_sum,
      residual_norm_sq A hA v μ]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hδ (hg i) 2) (sq_nonneg _))
  nlinarith [norm_nonneg v, norm_nonneg (A.toEuclideanLin v - (μ : K) • v)]

lemma eigenbasis_mem (A : Mat K n n) (hA : A.IsHermitian) (s : Set ℝ)
    (i : Fin n) (hi : eigenvalue A hA i ∈ s) :
    eigenbasis A hA i ∈ spectralSubspace A s := by
  exact Submodule.mem_iSup_of_mem ⟨eigenvalue A hA i, hi⟩
    (Module.End.mem_eigenspace_iff.mpr (MatrixData.eigenbasis_action A hA i))

lemma inner_projection_eq_zero (A : Mat K n n) (hA : A.IsHermitian) (s : Set ℝ)
    (v : Vec K n) (i : Fin n) (hi : eigenvalue A hA i ∉ s) :
    inner K (eigenbasis A hA i) (spectralProjection A hA s v) = 0 := by
  have hp := (MatrixData.spectralProjection_characterization A hA s v).1
  change spectralProjection A hA s v ∈ ⨆ μ : s, _ at hp
  refine Submodule.iSup_induction _ (motive := fun x => inner K (eigenbasis A hA i) x = 0) hp ?_ ?_ ?_
  · intro μ x hx
    have hne : (eigenvalue A hA i : K) ≠ (μ.val : K) := by
      intro he
      have he' := RCLike.ofReal_injective he
      exact hi (he' ▸ μ.property)
    exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).orthogonalFamily_eigenspaces
      hne ⟨eigenbasis A hA i, Module.End.mem_eigenspace_iff.mpr
        (MatrixData.eigenbasis_action A hA i)⟩ ⟨x, hx⟩
  · simp
  · intro x y hx hy
    simp [inner_add_right, hx, hy]

theorem residual_certificate : Specs.NumAnalysis206.HermitianResidualGap.residual_certificate := by
  intro K _ n A hA v μ hv
  classical
  have hn : Nonempty (Fin n) := by
    by_contra h
    have hs := (eigenbasis A hA).sum_sq_norm_inner_right v
    have : IsEmpty (Fin n) := not_nonempty_iff.mp h
    simp [hv] at hs
  obtain ⟨i, hi⟩ := Finite.exists_min (fun i : Fin n => |eigenvalue A hA i - μ|)
  refine ⟨i, hi, ?_⟩
  simpa [hv] using lower_bound A hA v μ |eigenvalue A hA i - μ| (abs_nonneg _) hi

theorem residual_distance : Specs.NumAnalysis206.HermitianResidualGap.residual_distance := by
  intro K _ n A hA v μ hv
  obtain ⟨i, _, hi⟩ := residual_certificate A hA v μ hv
  have hm : eigenvalue A hA i ∈ spectrum ℝ A := by
    apply spectrum.of_algebraMap_mem K
    rw [← Matrix.spectrum_toLpLin 2]
    exact ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).hasEigenvalue_eigenvalues
      (finrank_euclideanSpace_fin (𝕜 := K)) i.rev).mem_spectrum
  calc
    Metric.infDist μ (spectrum ℝ A) ≤ dist μ (eigenvalue A hA i) :=
      Metric.infDist_le_dist_of_mem hm
    _ = |eigenvalue A hA i - μ| := by rw [Real.dist_eq, abs_sub_comm]
    _ ≤ _ := hi

theorem residual_gap : Specs.NumAnalysis206.HermitianResidualGap.residual_gap := by
  intro K _ n A hA v μ s δ hδ hg
  have hchar := MatrixData.spectralProjection_characterization A hA s v
  have hs : (δ * ‖v - spectralProjection A hA s v‖) ^ 2 ≤
      ‖A.toEuclideanLin v - (μ : K) • v‖ ^ 2 := by
    rw [mul_pow, ← (eigenbasis A hA).sum_sq_norm_inner_right,
      Finset.mul_sum, residual_norm_sq A hA v μ]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : eigenvalue A hA i ∈ s
    · have hz := (spectralSubspace A s).inner_right_of_mem_orthogonal
        (eigenbasis_mem A hA s i hi) hchar.2
      rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
      positivity
    · rw [inner_sub_right, inner_projection_eq_zero A hA s v i hi, sub_zero]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hδ.le (hg i hi) 2) (sq_nonneg _)
  apply (le_div_iff₀ hδ).mpr
  nlinarith [norm_nonneg (v - spectralProjection A hA s v),
    norm_nonneg (A.toEuclideanLin v - (μ : K) • v)]

end NumAnalysis206.HermitianResidualGap
