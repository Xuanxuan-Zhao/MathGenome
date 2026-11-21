import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.RNChainRule
import MathGenome.Internal.RealAnalysis.D11.Ch15.RNPositiveSigmaFinite

/-! The Radon–Nikodym chain and reciprocal rules, paper.tex:4965–4982.
Reconstruction on measurable sets identifies the density measures. The
nonnegative change-of-density theorem `withDensity_mul` reconstructs the
product measure, and upstream sigma-finite density uniqueness gives the a.e.
identity. In ENNReal the product is zero where its second factor is zero,
even if the first factor is infinite. Existence uses the upstream finite
everywhere representatives, so the selected product is also finite everywhere.
-/
open MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace D11.Ch15.RNChainRule
open D11.Ch05.NonnegativeIntegral

variable {X : Type u} [MeasurableSpace X]

/-- Convert the shared source set-integral identity into equality of measures. -/
theorem withDensity_eq_of_set_integrals (μ ν : Measure X) (h : X → ℝ≥0∞)
    (hr : ∀ E, MeasurableSet E → ν E = nonnegativeIntegral (μ.restrict E) h) :
    μ.withDensity h = ν := by
  ext E hE
  rw [withDensity_apply _ hE, hr E hE, integral_eq_lintegral]

/-- Composition of densities is the iterated nonnegative change of measure. -/
theorem product_set_integrals (ρ μ ν : Measure X) (h k : X → ℝ≥0∞)
    (hh : Measurable h) (hk : Measurable k)
    (hr : ∀ E, MeasurableSet E → ν E = nonnegativeIntegral (μ.restrict E) h)
    (kr : ∀ E, MeasurableSet E → μ E = nonnegativeIntegral (ρ.restrict E) k) :
    ∀ E, MeasurableSet E →
      ν E = nonnegativeIntegral (ρ.restrict E) (fun x => h x * k x) := by
  have hm := withDensity_eq_of_set_integrals ρ μ k kr
  have hn := withDensity_eq_of_set_integrals μ ν h hr
  have hp : ρ.withDensity (fun x => h x * k x) = ν := by
    calc
      ρ.withDensity (fun x => h x * k x) = ρ.withDensity (k * h) := by
        congr 1
        funext x
        exact mul_comm _ _
      _ = (ρ.withDensity k).withDensity h := withDensity_mul ρ hk hh
      _ = ν := by rw [hm, hn]
  intro E hE
  rw [integral_eq_lintegral, ← withDensity_apply _ hE, hp]

theorem chain_rule : Specs.D11.Ch15.RNChainRule.chain_rule := by
  intro X _ ρ μ ν _ _ _ _ _ h k l hh hk hl hr kr lr
  have pr := product_set_integrals ρ μ ν h k hh hk hr kr
  exact ⟨pr, RNPositiveSigmaFinite.density_unique ρ ν l _ hl (hh.mul hk) lr pr⟩

theorem chain_rule_finite_representatives :
    Specs.D11.Ch15.RNChainRule.chain_rule_finite_representatives := by
  intro X _ ρ μ ν _ _ _ hνμ hμρ
  obtain ⟨h, hh, hf, hr⟩ :=
    RNPositiveSigmaFinite.rn_positive_sigmafinite_finite_everywhere μ ν hνμ
  obtain ⟨k, hk, kf, kr⟩ :=
    RNPositiveSigmaFinite.rn_positive_sigmafinite_finite_everywhere ρ μ hμρ
  obtain ⟨l, hl, lf, lr⟩ :=
    RNPositiveSigmaFinite.rn_positive_sigmafinite_finite_everywhere ρ ν (hνμ.trans hμρ)
  refine ⟨h, k, l, hh, hk, hl, hf, kf, lf, hr, kr, lr, hh.mul hk,
    fun x => ENNReal.mul_lt_top (hf x) (kf x), fun x hx => by rw [hx, mul_zero], ?_⟩
  exact (chain_rule ρ μ ν hνμ hμρ h k l hh hk hl hr kr lr).2

theorem reciprocal_rule : Specs.D11.Ch15.RNChainRule.reciprocal_rule := by
  intro X _ ρ μ _ _ hμρ hρμ h k hh hk hr kr
  have one_rep : ∀ E, MeasurableSet E →
      ρ E = nonnegativeIntegral (ρ.restrict E) (fun _ => 1) := by
    intro E hE
    rw [integral_eq_lintegral, lintegral_one, Measure.restrict_apply MeasurableSet.univ]
    simp
  have H := (chain_rule ρ μ ρ hρμ hμρ h k (fun _ => 1)
    hh hk measurable_const hr kr one_rep).2.symm
  exact ⟨H, Measure.AbsolutelyContinuous.ae_eq hμρ H⟩

theorem reciprocal_finite_representatives :
    Specs.D11.Ch15.RNChainRule.reciprocal_finite_representatives := by
  intro X _ ρ μ _ _ hμρ hρμ
  obtain ⟨h, hh, hf, hr⟩ :=
    RNPositiveSigmaFinite.rn_positive_sigmafinite_finite_everywhere μ ρ hρμ
  obtain ⟨k, hk, kf, kr⟩ :=
    RNPositiveSigmaFinite.rn_positive_sigmafinite_finite_everywhere ρ μ hμρ
  exact ⟨h, k, hh, hk, hf, kf, hr, kr, reciprocal_rule ρ μ hμρ hρμ h k hh hk hr kr⟩

end D11.Ch15.RNChainRule
