import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.Portmanteau
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.MeasureContinuity
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.ConvergingTogether

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace ProbabilityFoundations.Ch06
universe u v
noncomputable section

private lemma coe_limsup_ennreal (f : ℕ → ℝ≥0∞) :
    ((limsup f atTop : ℝ≥0∞) : EReal) = limsup (fun n => (f n : EReal)) atTop :=
  (show Monotone ((↑) : ℝ≥0∞ → EReal) from
    fun _ _ h => EReal.coe_ennreal_le_coe_ennreal_iff.mpr h).map_limsup_of_continuousAt
      f continuous_coe_ennreal_ereal.continuousAt

private lemma limsup_add_ennreal (f g : ℕ → ℝ≥0∞) :
    limsup (fun n => f n + g n) atTop ≤ limsup f atTop + limsup g atTop := by
  apply EReal.coe_ennreal_le_coe_ennreal_iff.mp
  rw [EReal.coe_ennreal_add, coe_limsup_ennreal, coe_limsup_ennreal,
    coe_limsup_ennreal]
  simp only [EReal.coe_ennreal_add]
  exact EReal.limsup_add_le (by rw [← coe_limsup_ennreal]; exact .inl (by simp))
    (.inr (by rw [← coe_limsup_ennreal g]; simp))

/-- A coupling bounds a closed-set probability by a thickened-set probability
and the probability that the coupling distance exceeds its radius. -/
lemma law_le_thickening_add_error
    {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → S) (hX : Measurable X) (hY : Measurable Y)
    (F : Set S) (hF : IsClosed F) (ε : ℝ) :
    (probabilityLaw P X hX : Measure S) F ≤
      (probabilityLaw P Y hY : Measure S) (Metric.cthickening ε F) +
        P {ω | ε < dist (X ω) (Y ω)} := by
  simp only [probabilityLaw_toMeasure, Measure.map_apply hX hF.measurableSet,
    Measure.map_apply hY Metric.isClosed_cthickening.measurableSet]
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  by_cases hd : ε < dist (X ω) (Y ω)
  · exact Or.inr hd
  · exact Or.inl (Metric.mem_cthickening_of_dist_le (Y ω) (X ω) ε F hω
      (by simpa [dist_comm] using le_of_not_gt hd))

/-- Converging together with index-dependent coupling spaces. -/
theorem converging_together :
    Specs.ProbabilityFoundations.Ch06.ConvergingTogether.convergingTogetherType.{u,v} := by
  intro S _ _ _ Ω _ P _ X Y hX hY ν η μ hLaw _hdist hYlim hη herr
  apply (weaklyConverges_iff_closed ν μ).mpr
  intro F hF
  have hε (ε : ℝ) (hε : 0 < ε) :
      limsup (fun n => (ν n : Measure S) F) atTop ≤
        (μ : Measure S) (Metric.cthickening ε F) := by
    let e : ℕ → ℕ → ℝ≥0∞ := fun m n =>
      P m n {ω | ε < dist (X m n ω) (Y m n ω)}
    have hm (m : ℕ) : limsup (fun n => (ν n : Measure S) F) atTop ≤
        (η m : Measure S) (Metric.cthickening ε F) + limsup (e m) atTop := by
      calc
        _ ≤ limsup (fun n =>
            (probabilityLaw (P m n) (Y m n) (hY m n) : Measure S)
              (Metric.cthickening ε F) + e m n) atTop := by
          apply limsup_le_limsup (Eventually.of_forall (fun n => ?_))
          rw [← hLaw m n]
          exact law_le_thickening_add_error (P m n) (X m n) (Y m n)
            (hX m n) (hY m n) F hF ε
        _ ≤ _ := (limsup_add_ennreal _ _).trans (add_le_add
          (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto (hYlim m)
            Metric.isClosed_cthickening) le_rfl)
    have hb := limsup_le_limsup (f := atTop) (Eventually.of_forall hm)
    rw [limsup_const] at hb
    have he : Tendsto (fun m => limsup (e m) atTop) atTop (𝓝 0) := herr ε hε
    have heq := ENNReal.limsup_add_of_right_tendsto_zero he
      (fun m => (η m : Measure S) (Metric.cthickening ε F))
    exact (hb.trans_eq heq).trans
      (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hη Metric.isClosed_cthickening)
  apply ge_of_tendsto' ((tendsto_measure_cthickening_of_isClosed
    (μ := (μ : Measure S)) ⟨1, zero_lt_one, measure_ne_top _ _⟩ hF).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  intro n
  exact hε _ (by positivity)

/-- An error tending to zero in probability preserves a weak limit. -/
theorem weak_limit_of_perturbation :
    Specs.ProbabilityFoundations.Ch06.ConvergingTogether.perturbationType.{u,v} := by
  intro S _ _ _ Ω _ P _ X Y hX hY μ hdist hYlim herr
  apply converging_together (Ω := fun _ n => Ω n) (fun _ n => P n)
    (fun _ n => X n) (fun _ n => Y n) (fun _ n => hX n) (fun _ n => hY n)
    (fun n => Specs.ProbabilityFoundations.Ch06.WeakFramework.probabilityLawValue
      (P n) (X n) (hX n)) (fun _ => μ) μ
  · intro m n; rfl
  · exact fun _ n => hdist n
  · exact fun _ => hYlim
  · exact tendsto_const_nhds
  · intro ε hε
    simp only [(herr ε hε).limsup_eq]
    exact tendsto_const_nhds

/-- In a separable metric target, coordinate measurability suffices. -/
theorem measurable_distance :
    Specs.ProbabilityFoundations.Ch06.ConvergingTogether.measurableDistanceType.{u,v} := by
  intro S _ _ _ _ Ω _ X Y hX hY
  exact hX.dist hY

end
end ProbabilityFoundations.Ch06
