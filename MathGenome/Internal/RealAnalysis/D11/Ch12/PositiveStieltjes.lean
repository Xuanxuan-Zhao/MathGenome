import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.PositiveStieltjes
import MathGenome.Internal.RealAnalysis.D11.Ch12.BvOneSided

/-! Positive normalized Stieltjes correspondence, paper.tex:3915–3929.
The construction is the Borel Stieltjes measure, obtained from interval covering
costs. The converse below uses only continuity of finite positive measures;
neither Radon–Nikodym nor differentiation is involved. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace D11.Ch12.PositiveStieltjes

def PositiveGenerator : (ℝ → ℝ) → Prop :=
  Specs.D11.Ch12.PositiveStieltjes.positiveGenerator_value

noncomputable def stieltjesMeasure (F : ℝ → ℝ) (h : PositiveGenerator F) : Measure ℝ :=
  (StieltjesFunction.mk F h.1 h.2.1).measure

noncomputable def cumulative (μ : Measure ℝ) (x : ℝ) : ℝ := μ.real (Iic x)

theorem stieltjesMeasure_finite (F : ℝ → ℝ) (h : PositiveGenerator F) :
    IsFiniteMeasure (stieltjesMeasure F h) := by
  obtain ⟨C, hC⟩ := h.2.2.2
  exact (StieltjesFunction.mk F h.1 h.2.1).isFiniteMeasure_of_forall_abs_le hC

theorem stieltjesMeasure_Ioc (F : ℝ → ℝ) (h : PositiveGenerator F)
    {a b : ℝ} (_hab : a < b) :
    stieltjesMeasure F h (Ioc a b) = ENNReal.ofReal (F b - F a) :=
  (StieltjesFunction.mk F h.1 h.2.1).measure_Ioc a b

theorem generator_nonneg (F : ℝ → ℝ) (h : PositiveGenerator F) (x : ℝ) : 0 ≤ F x :=
  h.1.le_of_tendsto h.2.2.1 x

theorem stieltjesMeasure_Iic (F : ℝ → ℝ) (h : PositiveGenerator F) (x : ℝ) :
    stieltjesMeasure F h (Iic x) = ENNReal.ofReal (F x) := by
  simpa [stieltjesMeasure] using
    (StieltjesFunction.mk F h.1 h.2.1).measure_Iic h.2.2.1 x

theorem cumulative_stieltjesMeasure (F : ℝ → ℝ) (h : PositiveGenerator F) (x : ℝ) :
    cumulative (stieltjesMeasure F h) x = F x := by
  simp only [cumulative, measureReal_def, stieltjesMeasure_Iic]
  exact ENNReal.toReal_ofReal (generator_nonneg F h x)

theorem stieltjesMeasure_singleton (F : ℝ → ℝ) (h : PositiveGenerator F) (x : ℝ) :
    stieltjesMeasure F h {x} = ENNReal.ofReal (F x - Function.leftLim F x) :=
  (StieltjesFunction.mk F h.1 h.2.1).measure_singleton x

theorem stieltjesMeasure_real_singleton (F : ℝ → ℝ) (h : PositiveGenerator F) (x : ℝ) :
    (stieltjesMeasure F h).real {x} = F x - Function.leftLim F x := by
  rw [measureReal_def, stieltjesMeasure_singleton]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr (h.1.leftLim_le le_rfl))

theorem generator_left_limit (F : ℝ → ℝ) (h : PositiveGenerator F) (x : ℝ) :
    Tendsto F (𝓝[<] x) (𝓝 (Function.leftLim F x)) := h.1.tendsto_leftLim x

theorem stieltjesMeasure_unique (F : ℝ → ℝ) (h : PositiveGenerator F)
    (ν : Measure ℝ) (_hν : IsFiniteMeasure ν)
    (hν : ∀ a b : ℝ, a < b → ν (Ioc a b) = ENNReal.ofReal (F b - F a)) :
    ν = stieltjesMeasure F h := by
  haveI := stieltjesMeasure_finite F h
  exact (Measure.ext_of_Ioc (stieltjesMeasure F h) ν
    (fun a b hab => (stieltjesMeasure_Ioc F h hab).trans (hν a b hab).symm)).symm

theorem generator_globallyBV (F : ℝ → ℝ) (h : PositiveGenerator F) :
    D11.Ch12.GloballyBV F := by
  apply (D11.Ch12.globallyBV_iff_boundedVariationOn F).mpr
  obtain ⟨C, hC⟩ := h.2.2.2
  exact (h.1.monotoneOn univ).boundedVariationOn (fun x _ => hC x)

theorem cumulative_monotone (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Monotone (cumulative μ) := by
  intro a b hab
  exact measureReal_mono (Iic_subset_Iic.mpr hab)

/-- The intersection of all right neighborhoods of an initial interval is that
initial interval. Continuity from above therefore gives right continuity. -/
theorem cumulative_right_continuous (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    ContinuousWithinAt (cumulative μ) (Ici x) x := by
  have hi : (⋂ r > x, Iic r) = Iic x := by
    ext y
    simp only [mem_iInter, mem_Iic]
    constructor
    · intro hy
      exact le_of_forall_gt_imp_ge_of_dense (fun r hr => hy r hr)
    · exact fun hy r hr => hy.trans hr.le
  have ht : Tendsto (fun r : ℝ => μ (Iic r)) (𝓝[>] x) (𝓝 (μ (Iic x))) := by
    simpa only [hi, Function.comp_def] using
      (tendsto_measure_biInter_gt (μ := μ) (s := fun r : ℝ => Iic r) (a := x)
        (fun _ _ => measurableSet_Iic.nullMeasurableSet)
        (fun _ _ _ hij => Iic_subset_Iic.mpr hij)
        ⟨x + 1, lt_add_one x, measure_ne_top μ _⟩)
  apply continuousWithinAt_Ioi_iff_Ici.mp
  exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp ht

theorem cumulative_tendsto_atBot (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto (cumulative μ) atBot (𝓝 0) := by
  change Tendsto (fun r : ℝ => (μ (Iic r)).toReal) atBot (𝓝 0)
  have hi : (⋂ r : ℝ, Iic r) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hh : x ≤ x - 1 := mem_iInter.mp hx (x - 1)
    linarith
  have ht : Tendsto (fun r : ℝ => μ (Iic r)) atBot (𝓝 0) := by
    simpa only [hi, measure_empty, Function.comp_def] using
      (tendsto_measure_iInter_atBot (μ := μ) (s := fun r : ℝ => Iic r)
        (fun _ => measurableSet_Iic.nullMeasurableSet) monotone_Iic
        ⟨0, measure_ne_top μ _⟩)
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht

theorem cumulative_properties (μ : Measure ℝ) (hμ : IsFiniteMeasure μ) :
    PositiveGenerator (cumulative μ) := by
  letI := hμ
  refine ⟨cumulative_monotone μ, cumulative_right_continuous μ,
    cumulative_tendsto_atBot μ, μ.real univ, ?_⟩
  intro x
  rw [abs_of_nonneg (show 0 ≤ cumulative μ x from measureReal_nonneg)]
  exact measureReal_mono (subset_univ _)

theorem stieltjesMeasure_cumulative (μ : Measure ℝ) (hμ : IsFiniteMeasure μ)
    (h : PositiveGenerator (cumulative μ)) :
    stieltjesMeasure (cumulative μ) h = μ := by
  letI := hμ
  apply (Measure.ext_of_Iic μ (stieltjesMeasure (cumulative μ) h) ?_).symm
  intro x
  rw [stieltjesMeasure_Iic, cumulative, ofReal_measureReal]

theorem positive_stieltjes_exists_unique (F : ℝ → ℝ) (h : PositiveGenerator F) :
    ∃! ν : Measure ℝ, IsFiniteMeasure ν ∧
      ∀ a b : ℝ, a < b → ν (Ioc a b) = ENNReal.ofReal (F b - F a) := by
  refine ⟨stieltjesMeasure F h, ⟨stieltjesMeasure_finite F h,
    fun _ _ hab => stieltjesMeasure_Ioc F h hab⟩, ?_⟩
  intro ν hν
  exact stieltjesMeasure_unique F h ν hν.1 hν.2

end D11.Ch12.PositiveStieltjes
