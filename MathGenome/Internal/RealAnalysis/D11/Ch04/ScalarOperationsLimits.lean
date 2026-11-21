import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.ScalarOperationsLimits
import MathGenome.Internal.RealAnalysis.D11.Ch04.MeasurableMapTests
import MathGenome.Internal.RealAnalysis.D11.Ch04.CompositionCoordinates

/-! Algebra, comparisons, and countable limits of Borel measurable scalars.
The source is arbitrary, including an empty space. Division is stated on
the trace of the measurable nonzero-denominator set. -/

open Set Filter MeasurableSpace
open scoped Topology MeasureTheory ENNReal NNReal
universe u
namespace D11.Ch04.ScalarOperationsLimits

/-- Points at which the extended-real sequence converges to a finite value. -/
def finiteLimitSet {X : Type u} (f : ℕ → X → EReal) : Set X :=
  {x | ∃ l : ℝ, Tendsto (fun n => f n x) atTop (𝓝 (l : EReal))}

/-- The finite pointwise limit, assigned zero at all other points. -/
noncomputable def finiteLimit {X : Type u} (f : ℕ → X → EReal) (x : X) : ℝ := by
  classical
  exact if x ∈ finiteLimitSet f then (limsup (fun n => f n x) atTop).toReal else 0


theorem real_linear_combination : Specs.D11.Ch04.ScalarOperationsLimits.real_linear_combination := by
  intro X m f g a b hf hg
  let : MeasurableSpace X := m
  exact (hf.const_mul a).add (hg.const_mul b)

theorem real_product : Specs.D11.Ch04.ScalarOperationsLimits.real_product := by
  intro X m f g hf hg
  let : MeasurableSpace X := m
  exact hf.mul hg

theorem real_nonzero_domain : Specs.D11.Ch04.ScalarOperationsLimits.real_nonzero_domain := by
  intro X m g hg
  let : MeasurableSpace X := m
  exact (hg (measurableSet_singleton 0)).compl

theorem real_quotient_on : Specs.D11.Ch04.ScalarOperationsLimits.real_quotient_on := by
  intro X m f g hf hg
  let : MeasurableSpace X := m
  exact (hf.comp measurable_subtype_coe).div (hg.comp measurable_subtype_coe)

theorem complex_linear_combination : Specs.D11.Ch04.ScalarOperationsLimits.complex_linear_combination := by
  intro X m f g a b hf hg
  let : MeasurableSpace X := m
  exact (hf.const_mul a).add (hg.const_mul b)

theorem complex_product : Specs.D11.Ch04.ScalarOperationsLimits.complex_product := by
  intro X m f g hf hg
  let : MeasurableSpace X := m
  exact hf.mul hg

theorem complex_nonzero_domain : Specs.D11.Ch04.ScalarOperationsLimits.complex_nonzero_domain := by
  intro X m g hg
  let : MeasurableSpace X := m
  exact (hg (measurableSet_singleton 0)).compl

theorem complex_quotient_on : Specs.D11.Ch04.ScalarOperationsLimits.complex_quotient_on := by
  intro X m f g hf hg
  let : MeasurableSpace X := m
  exact (hf.comp measurable_subtype_coe).div (hg.comp measurable_subtype_coe)

theorem ereal_lt_set : Specs.D11.Ch04.ScalarOperationsLimits.ereal_lt_set := by
  intro X m f g hf hg
  let : MeasurableSpace X := m
  exact measurableSet_lt hf hg

theorem ereal_le_set : Specs.D11.Ch04.ScalarOperationsLimits.ereal_le_set := by
  intro X m f g hf hg
  let : MeasurableSpace X := m
  exact measurableSet_le hf hg

theorem ereal_eq_set : Specs.D11.Ch04.ScalarOperationsLimits.ereal_eq_set := by
  intro X m f g hf hg
  let : MeasurableSpace X := m
  exact measurableSet_eq_fun hf hg

theorem ereal_max : Specs.D11.Ch04.ScalarOperationsLimits.ereal_max := by
  intro X m f g hf hg
  let : MeasurableSpace X := m
  exact hf.max hg

theorem ereal_min : Specs.D11.Ch04.ScalarOperationsLimits.ereal_min := by
  intro X m f g hf hg
  let : MeasurableSpace X := m
  exact hf.min hg

theorem nonnegative_add : Specs.D11.Ch04.ScalarOperationsLimits.nonnegative_add := by
  intro X m f g hf hg
  let : MeasurableSpace X := m
  exact hf.add hg

theorem nonnegative_mul : Specs.D11.Ch04.ScalarOperationsLimits.nonnegative_mul := by
  intro X m f g hf hg
  let : MeasurableSpace X := m
  exact hf.mul hg

theorem nonnegative_const_mul : Specs.D11.Ch04.ScalarOperationsLimits.nonnegative_const_mul := by
  intro X m a f hf
  let : MeasurableSpace X := m
  exact hf.const_mul (a : ℝ≥0∞)

theorem ereal_nonnegative_add : Specs.D11.Ch04.ScalarOperationsLimits.ereal_nonnegative_add := by
  intro X m f g hf hg hf0 hg0
  let : MeasurableSpace X := m
  exact ⟨hf.add hg, fun x => add_nonneg (hf0 x) (hg0 x)⟩

theorem ereal_nonnegative_mul : Specs.D11.Ch04.ScalarOperationsLimits.ereal_nonnegative_mul := by
  intro X m f g hf hg hf0 hg0
  let : MeasurableSpace X := m
  exact ⟨hf.mul hg, fun x => mul_nonneg (hf0 x) (hg0 x)⟩

theorem ereal_nonnegative_const_mul : Specs.D11.Ch04.ScalarOperationsLimits.ereal_nonnegative_const_mul := by
  intro X m a f ha hf hf0
  let : MeasurableSpace X := m
  exact ⟨hf.const_mul (a : EReal), fun x => mul_nonneg (by exact_mod_cast ha) (hf0 x)⟩

theorem zero_times_infinity : Specs.D11.Ch04.ScalarOperationsLimits.zero_times_infinity := by
  exact ⟨zero_mul _, mul_zero _, zero_mul _, mul_zero _⟩

theorem countable_sup : Specs.D11.Ch04.ScalarOperationsLimits.countable_sup := by
  intro X m f hf
  let : MeasurableSpace X := m
  exact Measurable.iSup hf

theorem countable_inf : Specs.D11.Ch04.ScalarOperationsLimits.countable_inf := by
  intro X m f hf
  let : MeasurableSpace X := m
  exact Measurable.iInf hf

theorem countable_limsup : Specs.D11.Ch04.ScalarOperationsLimits.countable_limsup := by
  intro X m f hf
  let : MeasurableSpace X := m
  exact Measurable.limsup hf

theorem countable_liminf : Specs.D11.Ch04.ScalarOperationsLimits.countable_liminf := by
  intro X m f hf
  let : MeasurableSpace X := m
  exact Measurable.liminf hf

theorem strict_comparison_formula :
    Specs.D11.Ch04.ScalarOperationsLimits.strict_comparison_formula := by
  intro X f g
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
  constructor
  · intro hx
    obtain ⟨q, hfq, hqg⟩ := EReal.exists_rat_btwn_of_lt hx
    exact ⟨q, hfq, hqg⟩
  · rintro ⟨q, hfq, hqg⟩
    exact hfq.trans hqg

theorem sup_upper_level : Specs.D11.Ch04.ScalarOperationsLimits.sup_upper_level := by
  intro X f a
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, lt_iSup_iff]

theorem inf_lower_level : Specs.D11.Ch04.ScalarOperationsLimits.inf_lower_level := by
  intro X f a
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, iInf_lt_iff]

theorem limsup_tail_formula : Specs.D11.Ch04.ScalarOperationsLimits.limsup_tail_formula := by
  intro X f x
  exact limsup_eq_iInf_iSup_of_nat

theorem liminf_tail_formula : Specs.D11.Ch04.ScalarOperationsLimits.liminf_tail_formula := by
  intro X f x
  exact liminf_eq_iSup_iInf_of_nat

/-- Equality of liminf and limsup characterizes convergence in the compact
order interval EReal. The additional strict bounds characterize finite limits. -/
theorem finite_limit_set_formula :
    Specs.D11.Ch04.ScalarOperationsLimits.finite_limit_set_formula := by
  intro X f
  ext x
  change (∃ l : ℝ, Tendsto (fun n => f n x) atTop (𝓝 (l : EReal))) ↔ _
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨hl.limsup_eq.trans hl.liminf_eq.symm, ?_⟩
    change ⊥ < limsup (fun n => f n x) atTop ∧ limsup (fun n => f n x) atTop < ⊤
    rw [hl.limsup_eq]
    exact ⟨EReal.bot_lt_coe l, EReal.coe_lt_top l⟩
  · rintro ⟨heq, hlo, hhi⟩
    have hfinite : ((limsup (fun n => f n x) atTop).toReal : EReal) =
        limsup (fun n => f n x) atTop := EReal.coe_toReal hhi.ne hlo.ne'
    refine ⟨(limsup (fun n => f n x) atTop).toReal, ?_⟩
    rw [hfinite]
    exact tendsto_of_liminf_eq_limsup heq.symm rfl

theorem finite_limit_set_measurable : Specs.D11.Ch04.ScalarOperationsLimits.finite_limit_set_measurable := by
  intro X m f hf
  let : MeasurableSpace X := m
  rw [finite_limit_set_formula]
  have hs := countable_limsup m f hf
  have hi := countable_liminf m f hf
  exact (measurableSet_eq_fun hs hi).inter
    ((measurableSet_lt measurable_const hs).inter (measurableSet_lt hs measurable_const))

theorem finite_limit_measurable : Specs.D11.Ch04.ScalarOperationsLimits.finite_limit_measurable := by
  intro X m f hf
  let : MeasurableSpace X := m
  exact ((countable_limsup m f hf).ereal_toReal).piecewise
    (finite_limit_set_measurable m f hf) measurable_const

theorem finite_limit_ereal_measurable :
    Specs.D11.Ch04.ScalarOperationsLimits.finite_limit_ereal_measurable := by
  intro X m f hf
  let : MeasurableSpace X := m
  exact (finite_limit_measurable m f hf).coe_real_ereal

theorem finite_limit_eq : Specs.D11.Ch04.ScalarOperationsLimits.finite_limit_eq := by
  intro X f x l hl
  classical
  change finiteLimit f x = l
  have hx : x ∈ finiteLimitSet f := ⟨l, hl⟩
  simp only [finiteLimit, ite_eq_left hx, hl.limsup_eq, EReal.toReal_coe]

theorem finite_limit_tendsto : Specs.D11.Ch04.ScalarOperationsLimits.finite_limit_tendsto := by
  intro X f x hx
  classical
  change Tendsto (fun n => f n x) atTop (𝓝 (finiteLimit f x : EReal))
  obtain ⟨l, hl⟩ := hx
  have hx' : x ∈ finiteLimitSet f := ⟨l, hl⟩
  simpa only [finiteLimit, ite_eq_left hx', hl.limsup_eq, EReal.toReal_coe] using hl

theorem finite_limit_zero_off : Specs.D11.Ch04.ScalarOperationsLimits.finite_limit_zero_off := by
  intro X f x hx
  classical
  exact ite_eq_right hx

theorem real_pointwise_limit : Specs.D11.Ch04.ScalarOperationsLimits.real_pointwise_limit := by
  intro X m f g hf hg
  let : MeasurableSpace X := m
  exact measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.mpr hg)

theorem complex_pointwise_limit : Specs.D11.Ch04.ScalarOperationsLimits.complex_pointwise_limit := by
  intro X m f g hf hg
  let : MeasurableSpace X := m
  exact measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.mpr hg)

end D11.Ch04.ScalarOperationsLimits
