import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.NormalSpectralTests
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.BorelNormSpectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary

/-!
The complex normal-operator assertions of `fa2:p2:spectral-corollaries`.
The spectral tests use the actual spectrum in the bounded operator algebra.
For the singleton assertion, a general zero-set/kernel identity is applied to
z ↦ z - ζ on the spectrum. This works for every resolving PVM, every complex
ζ, and arbitrary Hilbert spaces, including the zero space.
-/

noncomputable section
open scoped InnerProductSpace
open MeasureTheory Set Filter
open Classical
namespace ExpandedFA.SpectralMeasure.NormalSpectralTests
universe u v

theorem selfAdjoint_iff_real_spectrum : Spec.SelfAdjointSpectrum.{v} := by
  intro H _ _ _ N hN
  rw [isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts,
    QuasispectrumRestricts.real_iff, and_iff_right hN, quasispectrum_eq_spectrum_union_zero]
  constructor
  · intro h z hz
    have he := h z (Or.inl hz)
    exact congrArg Complex.im he |>.trans (by simp)
  · intro h z hz
    rcases hz with hz | hz
    · exact (Complex.ext (by simp) (by simpa using h z hz))
    · have hz0 : z = 0 := hz
      subst z
      simp

theorem unitary_iff_circle_spectrum : Spec.UnitarySpectrum.{v} := by
  intro H _ _ _ N hN
  rw [unitary_iff_isStarNormal_and_spectrum_subset_unitary, and_iff_right hN]
  constructor
  · intro h z hz
    exact CStarRing.norm_of_mem_unitary (h hz)
  · intro h z hz
    change z ∈ unitary ℂ
    rw [Unitary.mem_iff_star_mul_self]
    simp only [Complex.star_def, Complex.conj_mul', h z hz, one_pow,
      Complex.ofReal_one]

variable {S : Type u} {H : Type v} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The norm-square identity detects the null vectors of the integral. -/
lemma integral_apply_eq_zero_iff (E : ProjectionValuedMeasure S H) (f : S → ℂ)
    (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) (x : H) :
    E.spectralIntegral f x = 0 ↔ ∀ᵐ s ∂E.diagonalMeasure x, f s = 0 := by
  obtain ⟨C, hC, hb⟩ := hf.nonneg_bound
  have hi : Integrable (fun s => ‖f s‖ ^ 2) (E.diagonalMeasure x) := by
    apply Integrable.of_bound ((hf.1.norm.pow_const 2).stronglyMeasurable.aestronglyMeasurable) (C ^ 2)
    exact Eventually.of_forall (fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb s) 2)
  have hz := integral_eq_zero_iff_of_nonneg (fun s => sq_nonneg ‖f s‖) hi
  rw [← E.spectralIntegral_norm_sq_integral f hf x] at hz
  simpa only [sq_eq_zero_iff, norm_eq_zero, Filter.EventuallyEq, Pi.zero_apply] using hz

/-- The projection onto the zero set of a bounded Borel symbol is exactly
its integral's kernel. This uses the diagonal measure of each vector. -/
lemma range_zeroSet_eq_ker (E : ProjectionValuedMeasure S H) (f : S → ℂ)
    (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) :
    LinearMap.range (E {s | f s = 0}).toLinearMap =
      LinearMap.ker (E.spectralIntegral f).toLinearMap := by
  let B := {s | f s = 0}
  have hB : MeasurableSet B := hf.1 (measurableSet_singleton 0)
  have hz : E.spectralIntegral (fun _ : S => (0 : ℂ)) = 0 := by
    simpa using BorelNormSpectrum.integral_const E 0
  have hsum : E B + E Bᶜ = 1 := by
    rw [← BorelNormSpectrum.integral_indicator_one E B hB,
      ← BorelNormSpectrum.integral_indicator_one E Bᶜ hB.compl,
      ← E.spectralIntegral_add _ _
        (BorelNormSpectrum.bounded_indicator B hB (BorelNormSpectrum.bounded_const 1))
        (BorelNormSpectrum.bounded_indicator Bᶜ hB.compl (BorelNormSpectrum.bounded_const 1))]
    have he : B.indicator (fun _ : S => (1 : ℂ)) +
        Bᶜ.indicator (fun _ : S => (1 : ℂ)) = (fun _ => 1) := by
      ext s
      by_cases hs : s ∈ B <;> simp [hs]
    rw [he]
    exact E.spectralIntegral_one
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change E.spectralIntegral f (E B y) = 0
    have he : B.indicator f = (fun _ => 0) := by
      ext s
      by_cases hs : s ∈ B
      · simp [hs, show f s = 0 from hs]
      · simp [hs]
    have hh := BorelNormSpectrum.integral_indicator E B hB hf
    rw [he, hz] at hh
    exact congrArg (fun T : H →L[ℂ] H => T y) hh.symm
  · intro hx
    have hae := (integral_apply_eq_zero_iff E f hf x).mp hx
    have hm : E.diagonalMeasure x Bᶜ = 0 := ae_iff.mp hae
    have hn : E Bᶜ x = 0 := by
      rw [E.diagonalMeasure_apply x Bᶜ hB.compl, ENNReal.ofReal_eq_zero] at hm
      exact norm_eq_zero.mp (by nlinarith [sq_nonneg ‖E Bᶜ x‖, norm_nonneg (E Bᶜ x)])
    refine ⟨x, ?_⟩
    have hh := congrArg (fun T : H →L[ℂ] H => T x) hsum
    simpa [hn] using hh

theorem eigenprojection : Spec.Eigenprojection.{v} := by
  intro H _ _ _ N hN E hE ζ
  let c : spectrum ℂ N → ℂ := fun z => (z : ℂ)
  have hc : SpectralMeasure.Spec.IsBoundedMeasurable c :=
    NormalPVM.continuous_bounded ((ContinuousMap.id ℂ).restrict (spectrum ℂ N))
  have hf := BorelNormSpectrum.bounded_sub hc (BorelNormSpectrum.bounded_const ζ)
  have hi : E.spectralIntegral (c - (fun _ => ζ)) = N - ζ • (1 : H →L[ℂ] H) := by
    rw [BorelNormSpectrum.integral_sub E hc (BorelNormSpectrum.bounded_const ζ),
      BorelNormSpectrum.integral_const]
    exact congrArg (fun T : H →L[ℂ] H => T - ζ • 1)
      (show E.spectralIntegral c = N from NormalPVM.continuousIntegral_coordinate E hE)
  have hh := range_zeroSet_eq_ker E (c - (fun _ => ζ)) hf
  rw [hi] at hh
  simpa only [Pi.sub_apply, sub_eq_zero] using hh

theorem zero_space : Spec.ZeroSpace.{v} := by
  intro H _ _ _ _ N
  refine ⟨Subsingleton.elim _ _, ?_, ?_, ?_, ?_⟩
  · exact spectrum.of_subsingleton (R := ℂ) N
  · change star N = N
    exact Subsingleton.elim _ _
  · rw [Unitary.mem_iff]
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  · intro E ζ
    exact Subsingleton.elim _ _

end ExpandedFA.SpectralMeasure.NormalSpectralTests
