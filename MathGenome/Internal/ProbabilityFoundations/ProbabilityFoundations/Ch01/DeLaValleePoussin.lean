import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.DeLaValleePoussin
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.UniformIntegrabilityInterfaces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.DeLaValleePoussin

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

universe u v

namespace ProbabilityFoundations.Ch01

variable {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
  {μ : Measure S} {H : Set (S → E)}

private lemma indicator_norm_tail (f : S → E) (hf : AEStronglyMeasurable f μ)
    (C : ℝ≥0) :
    eLpNorm ({x | C ≤ ‖f x‖₊}.indicator f) 1 μ =
      ∫⁻ x in {x | (C : ℝ) ≤ ‖f x‖}, ‖f x‖ₑ ∂μ := by
  have hm : NullMeasurableSet {x | C ≤ ‖f x‖₊} μ :=
    nullMeasurableSet_le aemeasurable_const hf.nnnorm.aemeasurable
  rw [eLpNorm_one_eq_lintegral_enorm (hf.indicator₀ hm)]
  simp_rw [enorm_indicator_eq_indicator_enorm]
  rw [lintegral_indicator₀ hm]
  rfl

/-- The strict-tail source definition supplies the canonical tail criterion. -/
private theorem uniformIntegrable_of_source [IsFiniteMeasure μ]
    (h : SourceUniformIntegrable μ H) :
    UniformIntegrable (fun f : H => (f : S → E)) 1 μ := by
  refine MeasureTheory.uniformIntegrable_of
    (f := fun f : H => (f : S → E)) (p := 1) le_rfl ENNReal.one_ne_top
    (fun f => (h.1 f.1 f.2).aestronglyMeasurable) ?_
  intro ε hε
  have hev := (ENNReal.tendsto_nhds_zero.mp h.2) ε hε
  obtain ⟨r, hr⟩ := eventually_atTop.mp hev
  let C : ℝ≥0 := ⟨max 0 (r + 1), le_max_left _ _⟩
  refine ⟨C, fun f => ?_⟩
  rw [indicator_norm_tail _ (h.1 f.1 f.2).aestronglyMeasurable C]
  calc
    (∫⁻ x in {x | (C : ℝ) ≤ ‖f.1 x‖}, ‖f.1 x‖ₑ ∂μ) ≤ tailIntegral μ f.1 r := by
      apply lintegral_mono_set
      intro x hx
      exact lt_of_lt_of_le (lt_of_lt_of_le (lt_add_one r) (le_max_right _ _)) hx
    _ ≤ uniformTailIntegral μ H r := by
      unfold uniformTailIntegral
      exact le_iSup₂ (f := fun f (_ : f ∈ H) => tailIntegral μ f r) f.1 f.2
    _ ≤ ε := hr r le_rfl

/-- A common superlinear integral bound controls the source's strict tails.
No continuity or strict positivity of the measure is used. -/
private theorem source_of_superlinear_bound
    (hf : ∀ f ∈ H, Integrable f μ) (Φ : ℝ → ℝ)
    (hΦ : Tendsto (fun t => Φ t / t) atTop atTop)
    (hbound : (⨆ f ∈ H, ∫⁻ x, ENNReal.ofReal (Φ ‖f x‖) ∂μ) < ∞) :
    SourceUniformIntegrable μ H := by
  refine ⟨hf, ENNReal.tendsto_atTop_zero.mpr ?_⟩
  intro ε hε
  obtain ⟨η, hη0, hηε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  let B := ⨆ f ∈ H, ∫⁻ x, ENNReal.ofReal (Φ ‖f x‖) ∂μ
  let δ : ℝ := (η : ℝ) / (B.toReal + 1)
  have hη : 0 < (η : ℝ) := by exact_mod_cast hη0
  have hδ : 0 < δ := div_pos hη (by positivity)
  obtain ⟨r, hr⟩ := eventually_atTop.mp (hΦ.eventually (eventually_ge_atTop δ⁻¹))
  refine ⟨max 1 r, fun R hR => ?_⟩
  apply iSup₂_le
  intro f hfH
  have htail : tailIntegral μ f R ≤ ENNReal.ofReal δ * B := by
    calc
      tailIntegral μ f R ≤
          ∫⁻ x in {x | R < ‖f x‖}, ENNReal.ofReal (δ * Φ ‖f x‖) ∂μ := by
        apply lintegral_mono_ae
        have hm : NullMeasurableSet {x | R < ‖f x‖} μ :=
          nullMeasurableSet_lt aemeasurable_const (hf f hfH).aestronglyMeasurable.norm.aemeasurable
        filter_upwards [ae_restrict_mem₀ hm] with x hx
        rw [← ofReal_norm]
        apply ENNReal.ofReal_le_ofReal
        have hxR : R < ‖f x‖ := hx
        have hp : 0 < ‖f x‖ := lt_of_lt_of_le zero_lt_one
          (((le_max_left _ _).trans hR).trans hxR.le)
        have hg := (le_div_iff₀ hp).mp
          (hr ‖f x‖ (((le_max_right _ _).trans hR).trans hxR.le))
        calc
          ‖f x‖ = δ * (δ⁻¹ * ‖f x‖) := by
            rw [← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul]
          _ ≤ δ * Φ ‖f x‖ := mul_le_mul_of_nonneg_left hg hδ.le
      _ ≤ ∫⁻ x, ENNReal.ofReal (δ * Φ ‖f x‖) ∂μ := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal δ * ∫⁻ x, ENNReal.ofReal (Φ ‖f x‖) ∂μ := by
        simp_rw [ENNReal.ofReal_mul hδ.le]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal δ * B := by
        have hi : (∫⁻ x, ENNReal.ofReal (Φ ‖f x‖) ∂μ) ≤ B := by
          dsimp only [B]
          exact le_iSup₂
            (f := fun f (_ : f ∈ H) => ∫⁻ x, ENNReal.ofReal (Φ ‖f x‖) ∂μ) f hfH
        exact mul_le_mul_right hi _
  apply htail.trans
  apply le_trans _ hηε.le
  have hB : B ≠ ∞ := hbound.ne
  rw [← ENNReal.ofReal_toReal hB, ← ENNReal.ofReal_mul hδ.le]
  change ENNReal.ofReal (δ * B.toReal) ≤ (η : ℝ≥0∞)
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  dsimp [δ]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < B.toReal + 1)).mpr
  nlinarith [ENNReal.toReal_nonneg (a := B)]

/-- The de la Vallée–Poussin criterion on the original family of functions.
The general normed-group statement includes real and complex scalar functions. -/
theorem de_la_vallee_poussin [IsFiniteMeasure μ]
    (H : Set (S → E)) (hf : ∀ f ∈ H, Integrable f μ) :
    SourceUniformIntegrable μ H ↔
      ∃ Φ : ℝ → ℝ,
        MonotoneOn Φ (Ici 0) ∧ ConvexOn ℝ (Ici 0) Φ ∧
        (∀ t, 0 ≤ t → 0 ≤ Φ t) ∧ Φ 0 = 0 ∧
        Tendsto (fun t => Φ t / t) atTop atTop ∧
        (⨆ f ∈ H, ∫⁻ x, ENNReal.ofReal (Φ ‖f x‖) ∂μ) < ∞ := by
  constructor
  · intro h
    obtain ⟨G, hG, C, hC⟩ :=
      ExpandedFA.PartIV.DeLaValleePoussin.growth_bound_of_uniformIntegrable
        (uniformIntegrable_of_source h)
    rcases hG with ⟨_, hmono, hconv, hnonneg, hsuper⟩
    refine ⟨fun t => G t - G 0, ?_, ?_, ?_, sub_self _, ?_, ?_⟩
    · intro x hx y hy hxy
      exact sub_le_sub_right (hmono hx hy hxy) _
    · refine ⟨hconv.1, ?_⟩
      intro x hx y hy a b ha hb hab
      have hh := hconv.2 hx hy ha hb hab
      change G (a * x + b * y) - G 0 ≤ a * (G x - G 0) + b * (G y - G 0)
      change G (a * x + b * y) ≤ a * G x + b * G y at hh
      nlinarith [congrArg (fun z : ℝ => z * G 0) hab]
    · intro t ht
      exact sub_nonneg.mpr (hmono (by simp) ht ht)
    · apply tendsto_atTop.mpr
      intro c
      filter_upwards [hsuper.eventually (eventually_ge_atTop (c + G 0)),
        eventually_ge_atTop (1 : ℝ)] with t ht ht1
      rw [sub_div]
      have : G 0 / t ≤ G 0 := div_le_self (hnonneg 0 le_rfl) ht1
      linarith
    · apply lt_of_le_of_lt (b := (C : ℝ≥0∞)) _ ENNReal.coe_lt_top
      apply iSup₂_le
      intro f hfH
      apply le_trans _ (hC ⟨f, hfH⟩)
      apply lintegral_mono
      intro x
      apply ENNReal.ofReal_le_ofReal
      exact sub_le_self _ (hnonneg 0 le_rfl)
  · rintro ⟨Φ, _, _, _, _, hsuper, hbound⟩
    exact source_of_superlinear_bound hf Φ hsuper hbound

end ProbabilityFoundations.Ch01
