import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarLpDuality
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarLpIntegralPairing
import MathGenome.RealAnalysis.Topics.D11.Ch20

/-!
Scalar Lp duality, `fa2:p4:lp-duality`, paper.tex:16788–16825.

The fixed MathGenome library proves scalar Lp dual representation using
Radon–Nikodym on finite pieces, exhaustion on sigma-finite measures, and a
functional-visible sigma-finite support for arbitrary measures at p>1.
Its native ordinary Lp spaces, continuous scalar-linear dual, and bilinear
multiplication/integration pairing are definitionally the same as our upstream
objects. In particular, interior duality imposes no semifiniteness and uses
no Lp-reflexivity assumption. The p=1 endpoint retains sigma-finiteness.
-/

open MeasureTheory
open scoped ENNReal

universe u
noncomputable section

namespace ExpandedFA.FunctionSpaces

theorem lp_duality_sigmaFinite : ScalarLpDualitySpec.SigmaFiniteRepresentation.{u} :=
  D11.Ch20.LpDualSigmafiniteLocal.sigmaFinite_duality

theorem lp_duality_arbitrary_measure :
    ScalarLpDualitySpec.ArbitraryMeasureRepresentation.{u} :=
  D11.Ch20.LpDualArbitraryMeasure.representation

/-- The map is the previously fixed continuous scalar-linear integral map. -/
theorem lp_pairing_sigmaFinite_isometric_bijective :
    ScalarLpDualitySpec.SigmaFiniteIsometricBijection.{u} := by
  intro X 𝕜 _ _ μ _ p q _ _ _ hp
  have hnorm (g : Lp 𝕜 q μ) : ‖lpIntegralPairing μ p q g‖ = ‖g‖ :=
    D11.Ch20.LpDualSigmafiniteLocal.pairing_norm μ p q g
  have hi : Isometry (lpIntegralPairing (𝕜 := 𝕜) μ p q) :=
    AddMonoidHomClass.isometry_of_norm _ hnorm
  refine ⟨hi, hi.injective, ?_⟩
  intro L
  obtain ⟨g, hg, _⟩ := lp_duality_sigmaFinite μ p q hp L
  refine ⟨g, ?_⟩
  ext f
  exact (lp_pairing_integral μ p q g f).2.trans ((hg.1 f).2.symm)

theorem lp_pairing_arbitrary_isometric_bijective :
    ScalarLpDualitySpec.ArbitraryMeasureIsometricBijection.{u} :=
  D11.Ch20.LpDualArbitraryMeasure.lp_dual_arbitrary_measure

/-- Integral tests determine the ordinary a.e. density, including at p=1
under sigma-finiteness. Competing densities need no extra norm hypothesis. -/
theorem lp_density_ae_unique : ScalarLpDualitySpec.OrdinaryAeUniqueness.{u} := by
  intro X 𝕜 _ _ μ p q _ _ _ hp hμ g h
  constructor
  · intro heq
    have hinj : Function.Injective (lpIntegralPairing (𝕜 := 𝕜) μ p q) := by
      rcases hμ with hσ | hp1
      · have : SigmaFinite μ := hσ
        exact (lp_pairing_sigmaFinite_isometric_bijective μ p q hp).2.1
      · exact (lp_pairing_arbitrary_isometric_bijective μ p q hp1 hp).2.1
    have hgh : g = h := hinj (by
      ext f
      exact (lp_pairing_integral μ p q g f).2.trans
        ((heq f).trans (lp_pairing_integral μ p q h f).2.symm))
    subst h
    exact Filter.EventuallyEq.rfl
  · intro hgh f
    exact integral_congr_ae (Filter.EventuallyEq.rfl.mul hgh)

theorem lp_one_infinity_duality_sigmaFinite :
    ScalarLpDualitySpec.OneInfinityRepresentation.{u} := by
  intro X 𝕜 _ _ μ _ L
  exact lp_duality_sigmaFinite μ 1 ∞ (by simp) L

/-- Exact norm for every density, under precisely the duality hypotheses. -/
theorem lp_pairing_exact_norm : ScalarLpDualitySpec.PairingExactNorm.{u} := by
  intro X 𝕜 _ _ μ p q _ _ _ hp hμ g
  rcases hμ with hσ | hp1
  · have : SigmaFinite μ := hσ
    exact D11.Ch20.LpDualSigmafiniteLocal.pairing_norm μ p q g
  · have hq : q ≠ ∞ :=
      (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp1.ne'
    exact D11.Ch20.PairingNormFiniteQ.norm_pairing μ p q hq g

/-- Representation at the level of ordinary measurable functions, with
unconditional a.e. uniqueness among all Lq representatives. -/
theorem lp_duality_measurable_density :
    ScalarLpDualitySpec.MeasurableDensityRepresentation.{u} := by
  intro X 𝕜 _ _ μ p q _ _ _ hp hμ L
  have hrep : ∃! g : Lp 𝕜 q μ,
      (∀ f : Lp 𝕜 p μ, Integrable (fun x => f x * g x) μ ∧
        L f = ∫ x, f x * g x ∂μ) ∧ ‖g‖ = ‖L‖ := by
    rcases hμ with hσ | hp1
    · have : SigmaFinite μ := hσ
      exact lp_duality_sigmaFinite μ p q hp L
    · exact lp_duality_arbitrary_measure μ p q hp1 hp L
  obtain ⟨g, hg, _⟩ := hrep
  refine ⟨g, (Lp.stronglyMeasurable g).measurable, Lp.memLp g, hg.1,
    ?_, ?_⟩
  · exact (Lp.norm_def g).symm.trans hg.2
  · intro h hh hL
    have heq : (hh.toLp h : X → 𝕜) =ᵐ[μ] (g : X → 𝕜) := by
      apply (lp_density_ae_unique μ p q hp hμ (hh.toLp h) g).mp
      intro f
      calc
        (∫ x, f x * (hh.toLp h) x ∂μ) = ∫ x, f x * h x ∂μ :=
          integral_congr_ae (Filter.EventuallyEq.rfl.mul hh.coeFn_toLp)
        _ = L f := (hL f).symm
        _ = ∫ x, f x * g x ∂μ := (hg.1 f).2
    exact hh.coeFn_toLp.symm.trans heq

end ExpandedFA.FunctionSpaces
