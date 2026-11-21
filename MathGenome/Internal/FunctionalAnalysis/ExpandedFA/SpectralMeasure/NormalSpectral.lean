import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.NormalSpectral
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.BorelNormSpectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

noncomputable section
open scoped InnerProductSpace
open MeasureTheory Set Filter
open Classical
namespace ExpandedFA.SpectralMeasure.NormalSpectral
universe u v
variable {S : Type u} {H : Type v} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Spectral null sets are null for each finite diagonal measure. -/
lemma diagonal_almostEverywhere (E : ProjectionValuedMeasure S H) {p : S → Prop}
    (hp : Spec.AlmostEverywhere E p) (x : H) : ∀ᵐ s ∂E.diagonalMeasure x, p s := by
  obtain ⟨Z, hZ, hnull, hp⟩ := hp
  have hz : E.diagonalMeasure x Z = 0 := by
    rw [E.diagonalMeasure_apply x Z hZ, hnull]
    simp
  exact (ae_iff.mpr (measure_mono_null (by
    intro s hs
    by_contra hn
    exact hs (hp s hn)) hz))

/-- The norm-square identity and scalar dominated convergence give strong
convergence without any separability assumption. -/
theorem strong_convergence (E : ProjectionValuedMeasure S H) :
    Spec.StrongConvergence E E.spectralIntegral := by
  intro f a hf ha hbound hlim x
  obtain ⟨C, hC⟩ := hbound
  obtain ⟨D, hD0, hD⟩ := hf.nonneg_bound
  let K := max C 0 + D
  have hK : 0 ≤ K := add_nonneg (le_max_right _ _) hD0
  have hdiff (n : ℕ) : SpectralMeasure.Spec.IsBoundedMeasurable (a n - f) :=
    BorelNormSpectrum.bounded_sub (ha n) hf
  have hb (n : ℕ) (s : S) : ‖a n s - f s‖ ≤ K :=
    (norm_sub_le _ _).trans (add_le_add ((hC n s).trans (le_max_left _ _)) (hD s))
  have hi : Tendsto (fun n => ∫ s, ‖a n s - f s‖ ^ 2 ∂E.diagonalMeasure x)
      atTop (nhds (0 : ℝ)) := by
    have hh : Tendsto (fun n => ∫ s, ‖a n s - f s‖ ^ 2 ∂E.diagonalMeasure x)
        atTop (nhds (∫ _ : S, (0 : ℝ) ∂E.diagonalMeasure x)) := by
      apply tendsto_integral_filter_of_norm_le_const
      · exact Eventually.of_forall (fun n =>
          (((ha n).1.sub hf.1).norm.pow_const 2).stronglyMeasurable.aestronglyMeasurable)
      · refine ⟨K ^ 2, Eventually.of_forall (fun n => Eventually.of_forall (fun s => ?_))⟩
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hb n s) 2
      · filter_upwards [diagonal_almostEverywhere E hlim x] with s hs
        simpa using (hs.sub (tendsto_const_nhds (x := f s))).norm.pow 2
    simpa using hh
  have hsquare : Tendsto (fun n => ‖E.spectralIntegral (a n) x - E.spectralIntegral f x‖ ^ 2)
      atTop (nhds (0 : ℝ)) := by
    have heq (n : ℕ) : ‖E.spectralIntegral (a n) x - E.spectralIntegral f x‖ ^ 2 =
        ∫ s, ‖a n s - f s‖ ^ 2 ∂E.diagonalMeasure x := by
      rw [← sub_apply, ← BorelNormSpectrum.integral_sub E (ha n) hf]
      exact E.spectralIntegral_norm_sq_integral _ (hdiff n) x
    simpa only [heq] using hi
  have hn := (Real.continuous_sqrt.tendsto 0).comp hsquare
  have hn' : Tendsto (fun n => ‖E.spectralIntegral (a n) x - E.spectralIntegral f x‖)
      atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn'

/-- Regular coefficient measures extend commutation from continuous tests to
all Borel projections. Only two scalar measures are involved for each x,y. -/
theorem spectral_commutation {N : H →L[ℂ] H} (hN : IsStarNormal N)
    (E : ProjectionValuedMeasure (spectrum ℂ N) H)
    (hE : NormalPVM.Spec.Resolves N E) : Spec.SpectralCommutation N E := by
  let π : C(spectrum ℂ N, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) := cfcHom hN
  have hrep := NormalPVM.resolves_represents hN π
    (isometry_cfcHom N hN).continuous (cfcHom_id hN) E hE
  obtain ⟨μ, hreg, hcoeff, hcont⟩ := hrep
  intro T hTN hTNstar B hB
  have hc (f : C(spectrum ℂ N, ℂ)) : Commute (π f) T :=
    hTN.symm.cfcHom hN hTNstar.symm f
  have hmeasure (x y : H) : μ (ContinuousLinearMap.adjoint T x) y = μ x (T y) := by
    obtain ⟨η, hηreg, hηcont, _, huniq⟩ :=
      RepresentationBorelExtension.coefficient_measure_exists π x (T y)
    have hleft : μ (ContinuousLinearMap.adjoint T x) y = η := by
      apply huniq _ (hreg _ _)
      intro f
      refine ⟨(hcont _ _ f).1, ?_⟩
      rw [← (hcont _ _ f).2, ContinuousLinearMap.adjoint_inner_left]
      have heq := congrArg (fun A : H →L[ℂ] H => A y) (hc f).eq
      exact congrArg (fun z => ⟪x, z⟫_ℂ) heq
    have hright : μ x (T y) = η := huniq _ (hreg _ _) (hcont _ _)
    exact hleft.trans hright.symm
  change T * E B = E B * T
  ext y
  apply ext_inner_left ℂ
  intro x
  change ⟪x, T (E B y)⟫_ℂ = ⟪x, E B (T y)⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_left, ← hcoeff _ _ B hB,
    ← hcoeff _ _ B hB, hmeasure x y]

/-- The complete theorem, assembled for a single regular spectral resolution
and its actual bounded Borel integral. -/
theorem normal_spectral_theorem : Spec.NormalSpectralTheorem.{v} := by
  intro H _ _ _ N hN
  obtain ⟨E, hE, huniq⟩ := NormalPVM.normal_spectral_theorem H N hN
  refine ⟨E, E.spectralIntegral, hE, huniq, BorelNormSpectrum.borel_calculus E,
    NormalPVM.continuousIntegral_coordinate E hE, ?_, strong_convergence E,
    spectral_commutation hN E hE⟩
  intro f hf
  exact ⟨BorelNormSpectrum.norm_eq_essentialSup E hf,
    BorelNormSpectrum.spectrum_eq_essentialRange E hf⟩

end ExpandedFA.SpectralMeasure.NormalSpectral
