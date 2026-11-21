import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.CaratheodoryIntegrands
import Mathlib.Analysis.Convex.Continuous
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace VariationalNotes.Flux

variable {S E : Type*} [MeasurableSpace S] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure S} {p : ℝ≥0∞} {F : S → E → ℝ}

/-- The two growth inequalities hold for every fiber value off one null set. -/
def TwoSidedPGrowth (μ : Measure S) (p : ℝ≥0∞) (F : S → E → ℝ) : Prop :=
  ∃ (a₀ a₁ : ℝ) (a : S → ℝ), 0 < a₀ ∧ 0 ≤ a₁ ∧ Integrable a μ ∧
    (∀ᵐ x ∂μ, 0 ≤ a x) ∧
    ∀ᵐ x ∂μ, ∀ z, a₀ * ‖z‖ ^ p.toReal - a x ≤ F x z ∧
      F x z ≤ a x + a₁ * ‖z‖ ^ p.toReal

/-- The finite integral on the canonical a.e. classes. Its finiteness is proved below. -/
def integralFunctional (μ : Measure S) (F : S → E → ℝ) (v : Lp E p μ) : ℝ :=
  ∫ x, F x (v x) ∂μ

private theorem abs_growth {a₀ a₁ a t r : ℝ} (h₀ : 0 ≤ a₀) (h₁ : 0 ≤ a₁)
    (hr : 0 ≤ r) (hl : a₀ * r - a ≤ t) (hu : t ≤ a + a₁ * r) :
    |t| ≤ a + a₁ * r := by
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg h₀ hr, mul_nonneg h₁ hr]
  · exact hu

omit [NormedSpace ℝ E] in
/-- Growth implies genuine Bochner integrability, not merely a totalized integral value. -/
theorem integrable_substitution (hp₀ : p ≠ 0) (hp : p ≠ ∞)
    (hF : Sobolev.Caratheodory μ F) (hg : TwoSidedPGrowth μ p F)
    {v : S → E} (hv : MemLp v p μ) : Integrable (fun x => F x (v x)) μ := by
  obtain ⟨a₀, a₁, a, h₀, h₁, ha, _, hg⟩ := hg
  apply (ha.add ((hv.integrable_norm_rpow hp₀ hp).const_mul a₁)).mono'
    (hF.aemeasurable_substitution hv.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  filter_upwards [hg] with x hx
  exact abs_growth h₀.le h₁ (Real.rpow_nonneg (norm_nonneg _) _) (hx (v x)).1 (hx (v x)).2

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Descent agrees with every `MemLp` representative. -/
theorem integralFunctional_toLp {v : S → E} (hv : MemLp v p μ) :
    integralFunctional μ F (hv.toLp v) = ∫ x, F x (v x) ∂μ := by
  apply integral_congr_ae
  filter_upwards [hv.coeFn_toLp] with x hx
  rw [hx]

omit [NormedSpace ℝ E] in
/-- Agreement with the upstream extended energy proves in particular that it is finite. -/
theorem lpIntegralEnergy_eq (hp₀ : p ≠ 0) (hp : p ≠ ∞)
    (hF : Sobolev.Caratheodory μ F) (hg : TwoSidedPGrowth μ p F) (v : Lp E p μ) :
    Sobolev.lpIntegralEnergy μ F v = (integralFunctional μ F v : EReal) :=
  Sobolev.extendedIntegral_eq_integral (integrable_substitution hp₀ hp hF hg (Lp.memLp v))

section Normed
variable [Fact (1 ≤ p)]

theorem convex_integralFunctional (hp : p ≠ ∞) (hF : Sobolev.Caratheodory μ F)
    (hg : TwoSidedPGrowth μ p F) (hc : ∀ᵐ x ∂μ, ConvexOn ℝ univ (F x)) :
    ConvexOn ℝ univ (integralFunctional (p := p) μ F) := by
  have hp₀ : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  have hi (w : Lp E p μ) := integrable_substitution hp₀ hp hF hg (Lp.memLp w)
  calc
    integralFunctional μ F (a • u + b • v) ≤
        ∫ x, a * F x (u x) + b * F x (v x) ∂μ := by
      apply integral_mono_ae (hi _) ((hi u).const_mul a |>.add ((hi v).const_mul b))
      filter_upwards [hc, Lp.coeFn_add (a • u) (b • v), Lp.coeFn_smul a u,
        Lp.coeFn_smul b v] with x hx hadd hu hv
      simp only [hadd, hu, hv, Pi.add_apply, Pi.smul_apply]
      exact hx.2 (mem_univ _) (mem_univ _) ha hb hab
    _ = a • integralFunctional μ F u + b • integralFunctional μ F v := by
      rw [integral_add ((hi u).const_mul a) ((hi v).const_mul b), integral_const_mul,
        integral_const_mul]
      rfl

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fact (1 ≤ p)] in
/-- The integral of the pointwise power is the power of the canonical `Lp` norm. -/
theorem integral_norm_rpow (hp₀ : p ≠ 0) (hp : p ≠ ∞) (v : Lp E p μ) :
    (∫ x, ‖v x‖ ^ p.toReal ∂μ) = ‖v‖ ^ p.toReal := by
  have h := lpNorm_eq_integral_norm_rpow_toReal hp₀ hp (Lp.aestronglyMeasurable v)
  change ‖v‖ = _ at h
  rw [h, Real.rpow_inv_rpow]
  · exact integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)
  · exact ENNReal.toReal_ne_zero.mpr ⟨hp₀, hp⟩

/-- Convexity and the growth bound give norm continuity, with no derivative hypothesis. -/
theorem continuous_integralFunctional (hp : p ≠ ∞) (hF : Sobolev.Caratheodory μ F)
    (hg : TwoSidedPGrowth μ p F) (hc : ∀ᵐ x ∂μ, ConvexOn ℝ univ (F x)) :
    Continuous (integralFunctional (p := p) μ F) := by
  have hp₀ : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hconv := convex_integralFunctional hp hF hg hc
  obtain ⟨a₀, a₁, a, h₀, h₁, ha, hapos, hbound⟩ := hg
  have hlocal : ∃ v ∈ (univ : Set (Lp E p μ)),
      (𝓝 v).IsBoundedUnder (· ≤ ·) (integralFunctional μ F) := by
    refine ⟨0, mem_univ _, (∫ x, a x ∂μ) + a₁, ?_⟩
    change ∀ᶠ v in 𝓝 (0 : Lp E p μ), integralFunctional μ F v ≤ (∫ x, a x ∂μ) + a₁
    filter_upwards [Metric.ball_mem_nhds (0 : Lp E p μ) zero_lt_one] with v hv
    have hin := (Lp.memLp v).integrable_norm_rpow hp₀ hp
    calc
      integralFunctional μ F v ≤ ∫ x, a x + a₁ * ‖v x‖ ^ p.toReal ∂μ := by
        apply integral_mono_ae (integrable_substitution hp₀ hp hF
          ⟨a₀, a₁, a, h₀, h₁, ha, hapos, hbound⟩ (Lp.memLp v))
          (ha.add (hin.const_mul a₁))
        exact hbound.mono (fun x hx => (hx (v x)).2)
      _ = (∫ x, a x ∂μ) + a₁ * ‖v‖ ^ p.toReal := by
        rw [integral_add ha (hin.const_mul a₁), integral_const_mul, integral_norm_rpow hp₀ hp]
      _ ≤ (∫ x, a x ∂μ) + a₁ := by
        have hv' : ‖v‖ ≤ 1 := (show ‖v‖ < 1 by simpa [Metric.mem_ball, dist_zero_right] using hv).le
        have hw := mul_le_mul_of_nonneg_left
          (Real.rpow_le_one (z := p.toReal) (norm_nonneg v) hv' ENNReal.toReal_nonneg) h₁
        simpa only [mul_one, add_comm] using add_le_add_left hw (∫ x, a x ∂μ)
  exact continuousOn_univ.mp
    (((hconv.continuousOn_tfae isOpen_univ ⟨0, mem_univ _⟩).out 4 2).mp hlocal)

end Normed
end VariationalNotes.Flux

namespace VariationalNotes.Flux

/-- The manuscript's Euclidean-domain statement. The base is the actual subtype `Ω`,
with induced Lebesgue measure, and the norm in the growth bound is Euclidean.
No boundary regularity, nonemptiness, or positivity of the measure is required. -/
theorem euclidean_integral_regularity {d : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (_hΩ : volume Ω < ∞)
    (p : ℝ) (hp : 1 < p)
    (F : Ω → EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : Sobolev.Caratheodory (volume.comap Subtype.val) F)
    (a₀ a₁ : ℝ) (a : Ω → ℝ) (h₀ : 0 < a₀) (h₁ : 0 ≤ a₁)
    (ha : Integrable a (volume.comap Subtype.val))
    (hapos : ∀ᵐ x ∂(volume.comap Subtype.val), 0 ≤ a x)
    (hg : ∀ᵐ x ∂(volume.comap Subtype.val), ∀ z,
      a₀ * ‖z‖ ^ p - a x ≤ F x z ∧ F x z ≤ a x + a₁ * ‖z‖ ^ p)
    (hc : ∀ᵐ x ∂(volume.comap Subtype.val), ConvexOn ℝ univ (F x)) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    (∀ v : Lp (EuclideanSpace ℝ (Fin d)) (ENNReal.ofReal p) (volume.comap Subtype.val),
      Integrable (fun x => F x (v x)) (volume.comap Subtype.val) ∧
      Sobolev.lpIntegralEnergy (volume.comap Subtype.val) F v =
        (integralFunctional (volume.comap Subtype.val) F v : EReal)) ∧
    ConvexOn ℝ univ (integralFunctional (p := ENNReal.ofReal p)
      (volume.comap Subtype.val) F) ∧
    Continuous (integralFunctional (p := ENNReal.ofReal p) (volume.comap Subtype.val) F) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have hp₀ : ENNReal.ofReal p ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (lt_trans zero_lt_one hp))
  have hg' : TwoSidedPGrowth (volume.comap Subtype.val) (ENNReal.ofReal p) F := by
    refine ⟨a₀, a₁, a, h₀, h₁, ha, hapos, ?_⟩
    simpa only [ENNReal.toReal_ofReal (le_of_lt (lt_trans zero_lt_one hp))] using hg
  exact ⟨fun v => ⟨integrable_substitution hp₀ ENNReal.ofReal_ne_top hF hg' (Lp.memLp v),
    lpIntegralEnergy_eq hp₀ ENNReal.ofReal_ne_top hF hg' v⟩,
    convex_integralFunctional ENNReal.ofReal_ne_top hF hg' hc,
    continuous_integralFunctional ENNReal.ofReal_ne_top hF hg' hc⟩

end VariationalNotes.Flux
