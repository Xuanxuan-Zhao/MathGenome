import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.PeriodicConvolutionIdeals
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Models.PeriodicConvolution
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.HilbertSchmidtBasis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.TraceClassDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.TraceNormIdeal

noncomputable section
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace

namespace ExpandedFA.Models.PeriodicConvolutionIdeals
open PeriodicConvolutionSpec PeriodicConvolution
open TraceIdeals.HilbertSchmidtDefinitions
open TraceIdeals.HilbertSchmidtBasis

lemma column_norm (T : ℝ) [Fact (0 < T)] (k : Kernel T) (j : ℕ) :
    ‖operatorValue k (enumeratedBasis T j)‖ = ‖fourierCoeff k (frequency j)‖ := by
  rw [enumeratedBasis_apply, fourier_diagonal, norm_smul,
    orthonormal_fourier.norm_eq_one, mul_one]

lemma hilbertSchmidt_coefficients (T : ℝ) [Fact (0 < T)] (k : Kernel T) :
    IsHilbertSchmidt (operatorValue k) ↔
      Summable (fun j : ℕ => ‖fourierCoeff k (frequency j)‖ ^ 2) := by
  simpa only [column_norm] using
    finiteness_in_basis (operatorValue k) (enumeratedBasis T)
      (hilbertBasis_isBasis (enumeratedBasis T))

lemma coefficients_l2_iff (T : ℝ) [Fact (0 < T)] (k : Kernel T) :
    Summable (fun j : ℕ => ‖fourierCoeff k (frequency j)‖ ^ 2) ↔
      MemLp (k : Circle T → ℂ) 2 (Haar T) := by
  constructor
  · intro hs
    let a : lp (fun _ : ℕ => ℂ) 2 := ⟨fun j => fourierCoeff k (frequency j),
      memℓp_gen (by simpa using hs)⟩
    let f : Space T := (enumeratedBasis T).repr.symm a
    have he : (f : Circle T → ℂ) =ᵐ[Haar T] k := by
      apply ExpandedFA.Fourier.TorusFourierBasis.l1_unique T
      · exact MemLp.integrable (by norm_num) (Lp.memLp f)
      · exact memLp_one_iff_integrable.mp (Lp.memLp k)
      · intro n
        obtain ⟨j, rfl⟩ := frequency.surjective n
        rw [← enumeratedBasis_repr]
        exact congrArg (fun b : lp (fun _ : ℕ => ℂ) 2 => b j)
          ((enumeratedBasis T).repr.apply_symm_apply a)
    exact (Lp.memLp f).ae_eq he
  · intro hk
    let f : Space T := hk.toLp k
    have he : fourierCoeff f = fourierCoeff k := fourierCoeff_congr_ae hk.coeFn_toLp
    have hs := lp_hasSum_sq ((enumeratedBasis T).repr f)
    simpa only [enumeratedBasis_repr, he] using hs.summable

theorem hilbertSchmidt_criterion : PeriodicConvolutionIdealsSpec.HilbertSchmidtCriterion := by
  intro T hT k
  exact (hilbertSchmidt_coefficients T k).trans (coefficients_l2_iff T k)

theorem hilbertSchmidt_norm : PeriodicConvolutionIdealsSpec.HilbertSchmidtNorm := by
  intro T hT k hk hK
  have hn := normSquare_in_basis ⟨operatorValue k, hK⟩ (enumeratedBasis T)
    (hilbertBasis_isBasis (enumeratedBasis T))
  have he : fourierCoeff (hk.toLp k) = fourierCoeff k :=
    fourierCoeff_congr_ae hk.coeFn_toLp
  have hp := lp_hasSum_sq ((enumeratedBasis T).repr (hk.toLp k))
  rw [LinearIsometryEquiv.norm_map] at hp
  have hs : hilbertSchmidtNorm ⟨operatorValue k, hK⟩ ^ 2 = ‖hk.toLp k‖ ^ 2 := by
    calc
      _ = ∑' j : ℕ, ‖fourierCoeff k (frequency j)‖ ^ 2 := by
        simpa only [column_norm] using hn.2
      _ = _ := by simpa only [enumeratedBasis_repr, he] using hp.tsum_eq
  exact (sq_eq_sq₀ hn.1 (norm_nonneg _)).mp hs

/-- A unit phase, with phase one at zero. This retains zero Fourier modes. -/
private def phase (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

private lemma phase_norm (z : ℂ) : ‖phase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [phase, hz]
  · simp [phase, hz, Complex.norm_real, norm_ne_zero_iff.mpr hz]

private lemma norm_mul_phase (z : ℂ) : (‖z‖ : ℂ) * phase z = z := by
  by_cases hz : z = 0
  · simp [phase, hz]
  · rw [phase, ite_eq_right hz]
    have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    field_simp

lemma diagonal_inner (T : ℝ) [Fact (0 < T)] (k : Kernel T) (j : ℕ) :
    inner ℂ (enumeratedBasis T j) (operatorValue k (enumeratedBasis T j)) =
      fourierCoeff k (frequency j) := by
  rw [enumeratedBasis_apply, fourier_diagonal, inner_smul_right]
  have he := orthonormal_iff_ite.mp (orthonormal_fourier (T := T)) (frequency j) (frequency j)
  simp only [ite_true, he, mul_one]

/-- Rewrite the actual Fourier expansion as a nonnegative-coefficient expansion
with unit left and right vectors, as required by the trace norm estimate. -/
lemma phase_expansion (T : ℝ) [Fact (0 < T)] (k : Kernel T) (x : Space T) :
    HasSum (fun j : ℕ =>
      ((‖fourierCoeff k (frequency j)‖ : ℂ) * inner ℂ (enumeratedBasis T j) x) •
        (phase (fourierCoeff k (frequency j)) • enumeratedBasis T j))
      (operatorValue k x) := by
  convert (operatorValue k).hasSum ((enumeratedBasis T).hasSum_repr x) using 1
  funext j
  rw [map_smul, enumeratedBasis_apply, fourier_diagonal,
    smul_smul, smul_smul, HilbertBasis.repr_apply_apply]
  congr 1
  rw [mul_right_comm, norm_mul_phase, enumeratedBasis_apply, mul_comm]

theorem traceClass_criterion : PeriodicConvolutionIdealsSpec.TraceClassCriterion := by
  intro T hT k
  have heq := frequency.summable_iff (f := fun n : ℤ => ‖fourierCoeff k n‖)
  constructor
  · intro hK
    apply heq.mp
    have hs := (TraceIdeals.TraceClassDefinitions.diagonal_trace ℂ (Space T)
      (operatorValue k) hK ℕ (enumeratedBasis T)).1
    simpa only [Function.comp_def, diagonal_inner] using hs
  · intro hs
    have hs' := heq.mpr hs
    have hc := (TraceIdeals.TraceNormIdeal.compact_iff_native (operatorValue k)).mpr
      (PeriodicConvolution.compactness T k)
    apply (TraceIdeals.TraceNormIdeal.traceClass_of_finite_family_bound
      (operatorValue k) hc (∑' j : ℕ, ‖fourierCoeff k (frequency j)‖) ?_).1
    intro n a b ha hb
    apply TraceIdeals.TraceNormIdeal.finite_family_bound_of_expansion
      (operatorValue k) (fun j : ℕ => ‖fourierCoeff k (frequency j)‖)
      (fun j => phase (fourierCoeff k (frequency j)) • enumeratedBasis T j)
      (enumeratedBasis T) (fun j => norm_nonneg _) hs'
      (fun j => by rw [norm_smul, phase_norm, (enumeratedBasis T).orthonormal.norm_eq_one, mul_one])
      ((enumeratedBasis T).orthonormal.norm_eq_one) (phase_expansion T k) a b ha hb

end ExpandedFA.Models.PeriodicConvolutionIdeals
