import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.Plancherel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.SchwartzFourierConvention

open MeasureTheory
open scoped SchwartzMap FourierTransform ComplexInnerProductSpace ContDiff

noncomputable section
namespace ExpandedFA.Fourier.Plancherel

def unitary : Specs.ExpandedFA.Fourier.Plancherel.unitaryType := l2Fourier

theorem extension : Specs.ExpandedFA.Fourier.Plancherel.extensionType := by
  intro d f
  exact SchwartzMap.toLp_fourier_eq f

theorem uniqueness : Specs.ExpandedFA.Fourier.Plancherel.uniquenessType := by
  intro d T h f
  have heq := (SchwartzMap.denseRange_toLpCLM (E := Euclidean d)
    (F := ℂ) (p := 2) ENNReal.ofNat_ne_top).equalizer T.continuous (l2Fourier d).continuous
      (funext (fun φ => (h φ).trans (extension d φ).symm))
  exact congrFun heq f

theorem surjective : Specs.ExpandedFA.Fourier.Plancherel.surjectiveType := by
  intro d
  exact (l2Fourier d).surjective

theorem parseval : Specs.ExpandedFA.Fourier.Plancherel.parsevalType := by
  intro d f g
  exact (l2Fourier d).inner_map_map f g

theorem norm : Specs.ExpandedFA.Fourier.Plancherel.normType := by
  intro d f
  exact (l2Fourier d).norm_map f

/-- Fubini gives the bilinear Fourier pairing also for an L¹ function. -/
lemma integral_fourier_pair {d : ℕ} (f : Euclidean d → ℂ) (hf : Integrable f)
    (φ : Schwartz ℂ d) :
    (∫ x, (𝓕 f) x * φ x) = ∫ x, f x * (𝓕 φ) x := by
  simpa only [SchwartzMap.fourier_coe, ContinuousLinearMap.mul_apply', flip_innerₗ] using!
    (VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ (Euclidean d))
    Real.continuous_fourierChar continuous_inner hf φ.integrable)

lemma integral_agreement_native {d : ℕ} (f : Euclidean d → ℂ)
    (h1 : Integrable f) (h2 : MemLp f 2) :
    (l2Fourier d (h2.toLp f) : Euclidean d → ℂ) =ᵐ[volume] 𝓕 f := by
  have hc : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h1
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (l2Fourier d (h2.toLp f))).locallyIntegrable (by norm_num))
    hc.locallyIntegrable
  intro g hg hs
  have hs' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hs.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let φ : Schwartz ℂ d := hs'.toSchwartzMap hg'
  have hd := congrArg (fun u : TemperedDistribution (Euclidean d) ℂ => u φ)
    (Lp.fourier_toTemperedDistribution_eq (h2.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hd
  have hp : (∫ x, (𝓕 φ) x * (h2.toLp f) x) = ∫ x, (𝓕 φ) x * f x := by
    apply integral_congr_ae
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hx]
  exact calc
    (∫ x, g x • (l2Fourier d (h2.toLp f)) x) =
        ∫ x, φ x * (l2Fourier d (h2.toLp f)) x := by
          simp [φ, Complex.real_smul]
    _ = ∫ x, (𝓕 φ) x * (h2.toLp f) x := by
      simpa only [smul_eq_mul, l2Fourier] using! hd.symm
    _ = ∫ x, (𝓕 φ) x * f x := hp
    _ = ∫ x, (𝓕 f) x * φ x := by
      simpa only [mul_comm] using (integral_fourier_pair f h1 φ).symm
    _ = ∫ x, g x • (𝓕 f) x := by simp [φ, Complex.real_smul, mul_comm]

theorem integral_agreement : Specs.ExpandedFA.Fourier.Plancherel.integralAgreementType := by
  intro d f h1 h2
  exact (integral_agreement_native f h1 h2).trans
    (Filter.Eventually.of_forall (fun x => (integralFourier_eq_native f x).symm))

theorem integral_memLp : Specs.ExpandedFA.Fourier.Plancherel.integralMemLpType := by
  intro d f h1 h2
  exact (memLp_congr_ae (integral_agreement d f h1 h2)).mp (Lp.memLp _)

theorem integral_parseval : Specs.ExpandedFA.Fourier.Plancherel.integralParsevalType := by
  intro d f g
  have h := parseval d g f
  simpa only [L2.inner_def, RCLike.inner_apply, mul_comm] using! h

theorem classical_parseval : Specs.ExpandedFA.Fourier.Plancherel.classicalParsevalType := by
  intro d f g hf hg h2f h2g
  calc
    (∫ x, integralFourier f x * star (integralFourier g x)) =
        ∫ x, (l2Fourier d (h2f.toLp f)) x * star ((l2Fourier d (h2g.toLp g)) x) := by
      apply integral_congr_ae
      filter_upwards [integral_agreement d f hf h2f, integral_agreement d g hg h2g] with x hx hy
      rw [hx, hy]
    _ = ∫ x, (h2f.toLp f) x * star ((h2g.toLp g) x) :=
      integral_parseval d _ _
    _ = ∫ x, f x * star (g x) := by
      apply integral_congr_ae
      filter_upwards [h2f.coeFn_toLp, h2g.coeFn_toLp] with x hx hy
      rw [hx, hy]

/-- A real-valued version of Parseval, extracted from the self inner product. -/
lemma integral_norm_sq (d : ℕ) (f : L2 d) :
    (∫ x, ‖(l2Fourier d f) x‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 := by
  have h := parseval d f f
  have hnorm (g : L2 d) :
      (inner ℂ g g).re = ∫ x, ‖g x‖ ^ 2 := by
    change RCLike.re (inner ℂ g g) = _
    rw [L2.inner_def, ← integral_re (𝕜 := ℂ) (L2.integrable_inner (𝕜 := ℂ) g g)]
    simp only [inner_self_eq_norm_sq]
  have h' := congrArg Complex.re h
  simpa only [hnorm] using h'

theorem classical_norm : Specs.ExpandedFA.Fourier.Plancherel.classicalNormType := by
  intro d f hf h2
  calc
    (∫ x, ‖integralFourier f x‖ ^ 2) =
        ∫ x, ‖(l2Fourier d (h2.toLp f)) x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [integral_agreement d f hf h2] with x hx
      rw [hx]
    _ = ∫ x, ‖(h2.toLp f) x‖ ^ 2 := integral_norm_sq d _
    _ = ∫ x, ‖f x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [h2.coeFn_toLp] with x hx
      rw [hx]

end ExpandedFA.Fourier.Plancherel
