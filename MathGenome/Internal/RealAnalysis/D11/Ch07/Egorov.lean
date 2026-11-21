import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.Egorov
import MathGenome.Internal.RealAnalysis.D11.Ch07.ConvergenceDefinitions
import Mathlib.MeasureTheory.Function.Egorov
import Mathlib.MeasureTheory.Measure.Regular

/-! Egorov's theorem and its closed retained-set form (paper.tex:2244–2269).
The abstract theorem is applied with half the requested error to retain the
strict inequality in the source. On the real line we work on the completed
trace space, then approximate the retained measurable set from inside.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

universe u v
noncomputable section

namespace D11.Ch07.Egorov

open D11.Ch07.ConvergenceDefinitions
open D11.Ch04.AeCommonException

/-- Conversion to the source's norm-and-index definition of uniformity. -/
theorem uniformConvergesOn_iff_tendstoUniformlyOn
    {X : Type u} {E : Type v} [NormedAddCommGroup E]
    (f : ℕ → X → E) (g : X → E) (A : Set X) :
    uniformConvergesOn f g A ↔ TendstoUniformlyOn f g atTop A := by
  simp only [uniformConvergesOn, Metric.tendstoUniformlyOn_iff,
    eventually_atTop, dist_comm (g _) (f _ _), dist_eq_norm]

theorem egorov {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (f : ℕ → X → 𝕜) (g : X → 𝕜)
    (hfinite : μ univ < ∞) (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hfg : aeConverges μ f g) : almostUniformConverges μ f g := by
  intro ε hε
  have hfg' : ∀ᵐ x ∂μ, x ∈ (univ : Set X) →
      Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
    have h := (almostEverywhere_iff_native μ _).mp hfg
    filter_upwards [h] with x hx using fun _ => hx
  obtain ⟨A, _, hA, hμA, hU⟩ :=
    tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist
      (fun n => (hf n).edist hg) MeasurableSet.univ hfinite.ne hfg'
      (ENNReal.ofReal_pos.mpr (half_pos hε))
  refine ⟨A, hA, hμA.trans_lt ?_, ?_⟩
  · exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr (half_lt_self hε)
  · apply (uniformConvergesOn_iff_tendstoUniformlyOn f g Aᶜ).mpr
    rwa [compl_eq_univ_sdiff]

/-- Inner closed approximation applies to the full Lebesgue domain: first
choose a Borel subset with null loss, then use Borel regularity. -/
private theorem closed_subset_of_nullMeasurable {B : Set ℝ}
    (hB : NullMeasurableSet B (volume : Measure ℝ))
    (hfinite : (volume : Measure ℝ) B < ∞)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ F : Set ℝ, IsClosed F ∧ F ⊆ B ∧ (volume : Measure ℝ) (B \ F) < δ := by
  obtain ⟨C, hCB, hC, hCBae⟩ := hB.exists_measurable_subset_ae_eq
  obtain ⟨F, hFC, hF, herror⟩ :=
    hC.exists_isCompact_sdiff_lt ((measure_mono hCB).trans_lt hfinite).ne hδ
  refine ⟨F, hF.isClosed, hFC.trans hCB, ?_⟩
  have heq : B \ F =ᵐ[volume] C \ F := by
    filter_upwards [hCBae] with x hx
    simp only [Set.mem_sdiff, hx]
  exact (measure_congr heq).trans_lt herror

theorem egorov_closed : Specs.D11.Ch07.Egorov.egorov_closed := by
  classical
  let μB : Measure ℝ := volume
  let : MeasurableSpace ℝ :=
    inferInstanceAs (MeasurableSpace (NullMeasurableSpace ℝ μB))
  let μ : Measure ℝ := μB.completion
  intro 𝕜 _ _ _ E₀ hE₀ hfinite f g hf hg hfg ε hε
  change MeasurableSet E₀ at hE₀
  change μ E₀ < ∞ at hfinite
  change aeConverges (μ.comap (Subtype.val : E₀ → ℝ)) f g at hfg
  change ∃ F : Set ℝ, IsClosed F ∧ F ⊆ E₀ ∧ μ (E₀ \ F) < ENNReal.ofReal ε ∧
    uniformConvergesOn f g {x : E₀ | (x : ℝ) ∈ F}
  let ν : Measure E₀ := μ.comap (Subtype.val : E₀ → ℝ)
  have hνfinite : ν univ < ∞ := by
    rw [comap_subtype_coe_apply hE₀, image_univ, Subtype.range_coe]
    exact hfinite
  obtain ⟨A, hA, hνA, hU⟩ := egorov ν f g hνfinite hf hg hfg (ε / 2) (half_pos hε)
  let B : Set ℝ := (Subtype.val : E₀ → ℝ) '' Aᶜ
  have hB : MeasurableSet B := (MeasurableEmbedding.subtype_coe hE₀).measurableSet_image' hA.compl
  have hBE₀ : B ⊆ E₀ := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hloss : μ (E₀ \ B) < ENNReal.ofReal (ε / 2) := by
    have heq : E₀ \ B = (Subtype.val : E₀ → ℝ) '' A := by
      ext x
      constructor
      · rintro ⟨hxE₀, hxB⟩
        refine ⟨⟨x, hxE₀⟩, ?_, rfl⟩
        by_contra hxA
        exact hxB ⟨⟨x, hxE₀⟩, hxA, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y.property, ?_⟩
        rintro ⟨z, hz, hzy⟩
        have hzy' : z = y := Subtype.ext hzy
        exact hz (hzy'.symm ▸ hy)
    rw [heq, ← comap_subtype_coe_apply hE₀]
    exact hνA
  have hBfinite : μ B < ∞ := (measure_mono hBE₀).trans_lt hfinite
  obtain ⟨F, hF, hFB, hBF⟩ := closed_subset_of_nullMeasurable hB hBfinite
    (ne_of_gt (ENNReal.ofReal_pos.mpr (half_pos hε)))
  refine ⟨F, hF, hFB.trans hBE₀, ?_, ?_⟩
  · have hcover : E₀ \ F ⊆ (E₀ \ B) ∪ (B \ F) := by
      intro x hx
      by_cases hxB : x ∈ B
      · exact Or.inr ⟨hxB, hx.2⟩
      · exact Or.inl ⟨hx.1, hxB⟩
    calc
      μ (E₀ \ F) ≤ μ (E₀ \ B) + μ (B \ F) :=
        (measure_mono hcover).trans (measure_union_le _ _)
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        ENNReal.add_lt_add hloss hBF
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]
  · intro δ hδ
    obtain ⟨N, hN⟩ := hU δ hδ
    refine ⟨N, fun n hn x hx => hN n hn x ?_⟩
    have hxB := hFB hx
    obtain ⟨y, hy, hxy⟩ := hxB
    have : y = x := Subtype.ext hxy
    simpa only [this] using hy

end D11.Ch07.Egorov
