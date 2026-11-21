import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.DiagonalLpSpectrum

noncomputable section
open scoped ENNReal
namespace ExpandedFA.Models
open DiagonalLpSpectrumSpec

def diagonalLp : DiagonalType := diagonalValue

theorem diagonalLp_apply : DiagonalApply := by
  intro p hp a x n
  rfl

theorem diagonalLp_norm_le : DiagonalNormBound := by
  intro p hp a
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (diagonalLinear_bound p a)

/-- Outside the closed set of diagonal values the scalar reciprocals are bounded. -/
lemma diagonal_reciprocal_mem (a : Sequence ∞) {z : ℂ}
    (hz : z ∉ closure (Set.range fun n => a n)) :
    Memℓp (fun n => (z - a n)⁻¹) ∞ := by
  rw [Metric.mem_closure_range_iff] at hz
  push Not at hz
  obtain ⟨ε, hε, hn⟩ := hz
  apply memℓp_infty
  refine ⟨ε⁻¹, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hb : ‖z - a n‖⁻¹ ≤ ε⁻¹ :=
    inv_anti₀ hε (by simpa only [dist_eq_norm] using hn n)
  simpa only [norm_inv] using hb

/-- Every diagonal entry is an eigenvalue, including on ℓ∞. -/
lemma diagonal_entry_mem_spectrum (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : Sequence ∞) (n : ℕ) : a n ∈ spectrum ℂ (diagonalLp p a) := by
  apply spectrum.mem_iff.mpr
  rintro ⟨u, hu⟩
  let e : Sequence p := lp.single p n 1
  have he : (algebraMap ℂ (Sequence p →L[ℂ] Sequence p) (a n) - diagonalLp p a) e = 0 := by
    apply lp.ext
    funext k
    change a n * e k - a k * e k = 0
    by_cases hk : k = n
    · subst k
      exact sub_self _
    · have hek : e k = 0 := lp.single_apply_ne p n 1 hk
      rw [hek]
      simp
  have he' : (u : Sequence p →L[ℂ] Sequence p) e =
      (u : Sequence p →L[ℂ] Sequence p) 0 := by
    rw [hu, map_zero]
    exact he
  have he0 : e = 0 := (ContinuousLinearEquiv.ofUnit u).injective he'
  have h := congrArg (fun x : Sequence p => x n) he0
  simp [e] at h

/-- The reciprocal diagonal is a two-sided bounded inverse off the closure. -/
lemma diagonal_isUnit_of_not_mem_closure (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : Sequence ∞) {z : ℂ} (hz : z ∉ closure (Set.range fun n => a n)) :
    IsUnit (algebraMap ℂ (Sequence p →L[ℂ] Sequence p) z - diagonalLp p a) := by
  let b : Sequence ∞ := ⟨fun n => (z - a n)⁻¹, diagonal_reciprocal_mem a hz⟩
  have hn : ∀ n, z - a n ≠ 0 := by
    intro n
    apply sub_ne_zero.mpr
    intro he
    apply hz
    exact subset_closure ⟨n, he.symm⟩
  refine ⟨{
    val := algebraMap ℂ (Sequence p →L[ℂ] Sequence p) z - diagonalLp p a
    inv := diagonalLp p b
    val_inv := ?_
    inv_val := ?_ }, rfl⟩
  · apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext n
    change z * ((z - a n)⁻¹ * x n) - a n * ((z - a n)⁻¹ * x n) = x n
    rw [← sub_mul, ← mul_assoc, mul_inv_cancel₀ (hn n), one_mul]
  · apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext n
    change (z - a n)⁻¹ * (z * x n - a n * x n) = x n
    rw [← sub_mul, ← mul_assoc, inv_mul_cancel₀ (hn n), one_mul]

/-- Spectrum of every bounded complex diagonal, with the ℓ∞ endpoint included. -/
theorem diagonalLp_spectrum : SpectrumLaw := by
  intro p hp a
  apply Set.Subset.antisymm
  · intro z hz
    by_contra hc
    exact (spectrum.mem_iff.mp hz) (diagonal_isUnit_of_not_mem_closure p a hc)
  · apply closure_minimal
    · rintro z ⟨n, rfl⟩
      exact diagonal_entry_mem_spectrum p a n
    · exact spectrum.isClosed (diagonalLp p a)

/-- Raw-sequence form: boundedness is the sole condition on the entries. -/
theorem boundedSequence_diagonalLp_spectrum : BoundedSequenceSpectrumLaw := by
  intro p hp a ha
  exact diagonalLp_spectrum p ⟨a, memℓp_infty ha⟩

end ExpandedFA.Models
