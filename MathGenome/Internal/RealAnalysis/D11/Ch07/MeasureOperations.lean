import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.MeasureOperations
import MathGenome.Internal.RealAnalysis.D11.Ch07.ConvergenceDefinitions
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Operations on global limits in measure (paper.tex:2405–2435).
Addition and uniformly continuous composition follow by deviation-set bounds on
arbitrary measures. For products we use the finite-measure subsequence criterion:
every subsequence admits a common further subsequence with pointwise a.e. limits,
whose products converge. A bridge below checks strict versus non-strict thresholds
before applying the library criterion. No local convergence predicate is used. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u v w
namespace D11.Ch07.MeasureOperations
open D11.Ch07.ConvergenceDefinitions

variable {X : Type u} [MeasurableSpace X] {μ : Measure X}

/-- Strict source thresholds and non-strict library thresholds define the same
convergence, even for infinite measures. -/
theorem inMeasureConverges_iff_tendstoInMeasure {E : Type v} [NormedAddCommGroup E]
    {f : ℕ → X → E} {F : X → E} :
    inMeasureConverges μ f F ↔ TendstoInMeasure μ f atTop F := by
  rw [tendstoInMeasure_iff_norm]
  constructor
  · intro h ε hε
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h (ε / 2) (by positivity)) (fun _ => bot_le)
      (fun n => measure_mono (by
        intro x hx
        change ε ≤ ‖f n x - F x‖ at hx
        change ε / 2 < ‖f n x - F x‖
        linarith))
  · intro h ε hε
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h ε hε) (fun _ => bot_le) (fun n => measure_mono (by
        intro x hx
        change ε < ‖f n x - F x‖ at hx
        change ε ≤ ‖f n x - F x‖
        exact hx.le))

/-- The arbitrary-measure composition argument needs only uniform continuity,
and it does not need measurable input to obtain the deviation bound. -/
theorem inMeasureConverges_uniformContinuous_comp
    {E : Type v} {H : Type w} [NormedAddCommGroup E] [NormedAddCommGroup H]
    {f : ℕ → X → E} {F : X → E} (h : inMeasureConverges μ f F)
    {φ : E → H} (hφ : UniformContinuous φ) :
    inMeasureConverges μ (fun n => φ ∘ f n) (φ ∘ F) := by
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := Metric.uniformContinuous_iff.mp hφ ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h (δ / 2) (by positivity)) (fun _ => bot_le) ?_
  intro n
  apply measure_mono
  intro x hx
  change δ / 2 < ‖f n x - F x‖
  by_contra hn
  have hsmall : dist (f n x) (F x) < δ := by
    rw [dist_eq_norm_sub]
    linarith [not_lt.mp hn]
  have := hbound hsmall
  rw [dist_eq_norm_sub] at this
  exact (not_lt_of_ge this.le) hx

/-- A union of two fixed-threshold deviation sets bounds each sum deviation. -/
theorem inMeasureConverges_add {E : Type v} [NormedAddCommGroup E]
    {f g : ℕ → X → E} {F G : X → E}
    (hf : inMeasureConverges μ f F) (hg : inMeasureConverges μ g G) :
    inMeasureConverges μ (fun n x => f n x + g n x) (fun x => F x + G x) := by
  intro ε hε
  have hsum := (hf (ε / 2) (by positivity)).add (hg (ε / 2) (by positivity))
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) ?_
  intro n
  calc
    μ (deviationSet (fun x => f n x + g n x) (fun x => F x + G x) ε) ≤
        μ (deviationSet (f n) F (ε / 2) ∪ deviationSet (g n) G (ε / 2)) := by
      apply measure_mono
      intro x hx
      by_contra hn
      simp only [mem_union, deviationSet, mem_ofPred_eq, not_or, not_lt] at hn
      have hnorm := norm_add_le (f n x - F x) (g n x - G x)
      have heq : f n x + g n x - (F x + G x) = (f n x - F x) + (g n x - G x) := by
        abel
      change ε < ‖f n x + g n x - (F x + G x)‖ at hx
      rw [heq] at hx
      linarith
    _ ≤ μ (deviationSet (f n) F (ε / 2)) + μ (deviationSet (g n) G (ε / 2)) :=
      measure_union_le _ _

theorem linear_combination : Specs.D11.Ch07.MeasureOperations.linear_combination := by
  intro X 𝕜 _ _ _ _ μ f g F G a b hf hg hF hG hconvF hconvG
  refine ⟨fun n => ((hf n).const_mul a).add ((hg n).const_mul b),
    (hF.const_mul a).add (hG.const_mul b), ?_⟩
  exact inMeasureConverges_add
    (inMeasureConverges_uniformContinuous_comp hconvF
      (show UniformContinuous (fun z : 𝕜 => a * z) from
        uniformContinuous_const_smul a))
    (inMeasureConverges_uniformContinuous_comp hconvG
      (show UniformContinuous (fun z : 𝕜 => b * z) from
        uniformContinuous_const_smul b))

theorem uniformlyContinuous_composition :
    Specs.D11.Ch07.MeasureOperations.uniformlyContinuous_composition := by
  intro X 𝕜 _ _ _ _ μ f F φ hf hF hφ hconv
  exact ⟨fun n => hφ.continuous.measurable.comp (hf n),
    hφ.continuous.measurable.comp hF,
    inMeasureConverges_uniformContinuous_comp hconv hφ⟩

theorem product : Specs.D11.Ch07.MeasureOperations.product := by
  intro X 𝕜 _ _ _ _ μ f g F G hfin hf hg hF hG hconvF hconvG
  refine ⟨fun n => (hf n).mul (hg n), hF.mul hG, ?_⟩
  let : IsFiniteMeasure μ := ⟨hfin⟩
  apply inMeasureConverges_iff_tendstoInMeasure.mpr
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n => ((hf n).mul (hg n)).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨ms, hms, hmsF⟩ :=
    ((inMeasureConverges_iff_tendstoInMeasure.mp hconvF).comp
      hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ks, hks, hksG⟩ :=
    ((inMeasureConverges_iff_tendstoInMeasure.mp hconvG).comp
      (hns.comp hms).tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms ∘ ks, hms.comp hks, ?_⟩
  filter_upwards [hmsF, hksG] with x hxF hxG
  exact (hxF.comp hks.tendsto_atTop).mul hxG

end D11.Ch07.MeasureOperations
