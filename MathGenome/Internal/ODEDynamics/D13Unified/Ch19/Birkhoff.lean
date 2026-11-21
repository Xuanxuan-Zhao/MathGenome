import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.Birkhoff
import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.BirkhoffConvergence
import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.CompositionIsometry
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Abel

namespace D13Unified.Ch19.Birkhoff
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators symmDiff
universe u
variable {X : Type u} [MeasurableSpace X] {μ : Measure X}
variable {𝕜 : Type} [RCLike 𝕜] (T : X → X)

omit [MeasurableSpace X] in
/-- Removing the first summand does not change a convergent Cesàro limit. -/
lemma average_shift (f : X → 𝕜) {n : ℕ} (hn : n ≠ 0) (x : X) :
    MeasureDefinitions.ergodicAverage T f n (T x) =
      (1 + (n : ℝ)⁻¹) • MeasureDefinitions.ergodicAverage T f (n+1) x -
        (n : ℝ)⁻¹ • f x := by
  change (n : ℝ)⁻¹ • birkhoffSum T f n (T x) =
    (1 + (n : ℝ)⁻¹) • ((n+1 : ℕ) : ℝ)⁻¹ • birkhoffSum T f (n+1) x - _
  rw [birkhoffSum_succ_apply', smul_smul]
  have he : (1 + (n : ℝ)⁻¹) * ((n+1 : ℕ) : ℝ)⁻¹ = (n : ℝ)⁻¹ := by
    push_cast
    field_simp
  rw [he, smul_add]
  abel

/-- The common a.e. convergence set and its preimage suffice for invariance. -/
lemma invariant_limit (hT : MeasurePreserving T μ μ) (f g : X → 𝕜)
    (hg : ∀ᵐ x ∂μ, Tendsto (fun n => MeasureDefinitions.ergodicAverage T f n x)
      atTop (𝓝 (g x))) : g ∘ T =ᵐ[μ] g := by
  have hgT := hT.quasiMeasurePreserving.ae hg
  filter_upwards [hg, hgT] with x hx hTx
  have hs := hx.comp (tendsto_add_atTop_nat 1)
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hr : Tendsto (fun n : ℕ => 1 + (n : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hinv
  have hz : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • f x) atTop (𝓝 0) := by
    simpa using hinv.smul_const (f x)
  have hl := (hr.smul hs).sub hz
  have hl' : Tendsto (fun n => MeasureDefinitions.ergodicAverage T f n (T x))
      atTop (𝓝 (g x)) := by
    simpa only [one_smul, sub_zero] using hl.congr' (by
      filter_upwards [eventually_ne_atTop 0] with n hn
      exact (average_shift T f hn x).symm)
  exact tendsto_nhds_unique hTx hl'

/-- Change of variables for arbitrary integrable functions, without injectivity. -/
lemma integral_preserved (hT : MeasurePreserving T μ μ) (f : X → 𝕜)
    (hf : Integrable f μ) : (∫ x, f (T x) ∂μ) = ∫ x, f x ∂μ := by
  have hm : AEStronglyMeasurable f (Measure.map T μ) :=
    hT.map_eq.symm ▸ hf.aestronglyMeasurable
  exact (hT.map_eq ▸ integral_map hT.aemeasurable hm).symm

lemma integral_average (hT : MeasurePreserving T μ μ) (f : X → 𝕜)
    (hf : Integrable f μ) {n : ℕ} (hn : n ≠ 0) :
    (∫ x, MeasureDefinitions.ergodicAverage T f n x ∂μ) = ∫ x, f x ∂μ := by
  change (∫ x, (n : ℝ)⁻¹ • ∑ j ∈ Finset.range n, f (T^[j] x) ∂μ) = _
  rw [integral_smul, integral_finsetSum (f := fun j x => f (T^[j] x)) _ (fun j _ =>
    (hT.iterate j).integrable_comp_of_integrable hf)]
  simp only [integral_preserved _ (hT.iterate _) f hf, Finset.sum_const, Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_smul]

/-- A measurable set invariant modulo null sets carries a preserved restricted measure. -/
lemma restrict_preserving (hT : MeasurePreserving T μ μ) {E : Set X}
    (hE : MeasurableSet E) (hi : MeasureDefinitions.InvariantModNull T μ E) :
    MeasurePreserving T (μ.restrict E) (μ.restrict E) := by
  have he := (MeasureDefinitions.invariantModNull_iff_ae T μ E).mp hi
  have hr := hT.restrict_preimage hE
  rw [Measure.restrict_congr_set he] at hr
  exact hr

/-- Strong L¹ convergence controls integrals on every measurable subset. -/
lemma setIntegral_tendsto_of_l1 (F : ℕ → X → 𝕜) (g : X → 𝕜)
    (hF : ∀ n, Integrable (F n) μ) (hg : Integrable g μ)
    (hl : Tendsto (fun n => ∫ x, ‖F n x - g x‖ ∂μ) atTop (𝓝 0)) (E : Set X) :
    Tendsto (fun n => ∫ x in E, F n x ∂μ) atTop (𝓝 (∫ x in E, g x ∂μ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hl
  intro n
  rw [← integral_sub (hF n).integrableOn hg.integrableOn]
  exact (norm_integral_le_integral_norm _).trans
    (setIntegral_le_integral ((hF n).sub hg).norm
      (Eventually.of_forall fun x => norm_nonneg _))

/-- The same limiting representative has the source's invariant-set integral identity. -/
lemma limit_setIntegral (hT : MeasurePreserving T μ μ) (f g : X → 𝕜)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hl : Tendsto (fun n => ∫ x, ‖MeasureDefinitions.ergodicAverage T f n x - g x‖ ∂μ)
      atTop (𝓝 0)) {E : Set X} (hE : MeasurableSet E)
    (hi : MeasureDefinitions.InvariantModNull T μ E) :
    (∫ x in E, g x ∂μ) = ∫ x in E, f x ∂μ := by
  have ht := setIntegral_tendsto_of_l1 (MeasureDefinitions.ergodicAverage T f) g
    (BirkhoffConvergence.integrable_average T hT f hf) hg hl E
  have hc : Tendsto (fun n => ∫ x in E, MeasureDefinitions.ergodicAverage T f n x ∂μ)
      atTop (𝓝 (∫ x in E, f x ∂μ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact (integral_average T (restrict_preserving T hT hE hi) f hf.integrableOn hn).symm
  exact tendsto_nhds_unique ht hc

/-- In an ergodic probability space the invariant limit equals its integral. -/
lemma ergodic_limit [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    (f g : X → 𝕜) (hg : Integrable g μ) (hi : g ∘ T =ᵐ[μ] g)
    (hint : (∫ x, g x ∂μ) = ∫ x, f x ∂μ) (he : MeasureDefinitions.IsErgodic T μ) :
    g =ᵐ[μ] fun _ => ∫ x, f x ∂μ := by
  have he' : Ergodic T μ := (MeasureDefinitions.isErgodic_iff_native T μ hT).mp he
  obtain ⟨c, hc⟩ := he'.ae_eq_const_of_ae_eq_comp_ae hg.aestronglyMeasurable hi
  have hgc : (∫ x, g x ∂μ) = c := by
    rw [integral_congr_ae hc]
    simp
  have hc' : c = ∫ x, f x ∂μ := hgc.symm.trans hint
  simpa only [Function.const_def, hc'] using hc

/-- Add invariance and all integral conclusions to a common convergent limit. -/
lemma complete_limit [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    (f g : X → 𝕜) (hf : Integrable f μ) (hg : Integrable g μ)
    (ha : ∀ᵐ x ∂μ, Tendsto (fun n => MeasureDefinitions.ergodicAverage T f n x)
      atTop (𝓝 (g x)))
    (hl : Tendsto (fun n => ∫ x, ‖MeasureDefinitions.ergodicAverage T f n x - g x‖ ∂μ)
      atTop (𝓝 0)) :
    (g ∘ T =ᵐ[μ] g) ∧
      (∀ E : Set X, MeasurableSet E → MeasureDefinitions.InvariantModNull T μ E →
        (∫ x in E, g x ∂μ) = ∫ x in E, f x ∂μ) ∧
      ((∫ x, g x ∂μ) = ∫ x, f x ∂μ) ∧
      (MeasureDefinitions.IsErgodic T μ → g =ᵐ[μ] fun _ => ∫ x, f x ∂μ) := by
  have hi := invariant_limit T hT f g ha
  have hs : ∀ E : Set X, MeasurableSet E → MeasureDefinitions.InvariantModNull T μ E →
      (∫ x in E, g x ∂μ) = ∫ x in E, f x ∂μ :=
    fun _ hE hi => limit_setIntegral T hT f g hf hg hl hE hi
  have hall : (∫ x, g x ∂μ) = ∫ x, f x ∂μ := by
    have hu : MeasureDefinitions.InvariantModNull T μ univ := by
      change μ ((T ⁻¹' univ) ∆ univ) = 0
      simp
    simpa only [Measure.restrict_univ] using hs univ MeasurableSet.univ hu
  exact ⟨hi, hs, hall, ergodic_limit T hT f g hg hi hall⟩

/-- Full real pointwise and L¹ ergodic theorem. -/
theorem real_birkhoff : Specs.D13Unified.Ch19.Birkhoff.real_birkhoffStatement.{u} := by
  intro X _ T μ _ hT f hf
  obtain ⟨g, hg, ha, hl⟩ := BirkhoffConvergence.real_convergence T μ hT f hf
  exact ⟨g, hg, ha, hl, complete_limit T hT f g hf hg ha hl⟩

/-- Full complex theorem, using the componentwise convergence already proved upstream. -/
theorem complex_birkhoff : Specs.D13Unified.Ch19.Birkhoff.complex_birkhoffStatement.{u} := by
  intro X _ T μ _ hT f hf
  obtain ⟨g, hg, ha, hl⟩ := BirkhoffConvergence.complex_convergence T μ hT f hf
  exact ⟨g, hg, ha, hl, complete_limit T hT f g hf hg ha hl⟩

end
end D13Unified.Ch19.Birkhoff
