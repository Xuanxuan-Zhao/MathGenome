import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch08.MZFiniteLimitMoment
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.PairwiseBorelCantelliRatio

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

noncomputable section
namespace ProbabilityFoundations.Ch08
namespace MZ

/-- Consecutive normalized partial sums have vanishing normalized increments,
even when their finite limit is nonzero. -/
lemma increment_tendsto_zero (x : ℕ → ℝ) (p c z : ℝ) (hp : 0 < p)
    (h : Tendsto (fun n => ((∑ k ∈ Finset.range n, x k) - (n : ℝ) * c) /
      weight p n) atTop (𝓝 z)) :
    Tendsto (fun k => x k / weight p (k + 1)) atTop (𝓝 0) := by
  have hb : Tendsto (weight p) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 1 / p)).comp tendsto_natCast_atTop_atTop
  have hrbase : Tendsto (fun k : ℕ => (k : ℝ) / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).sub
      (tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)) :
        Tendsto (fun k : ℕ => (1 : ℝ) / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 0))
    convert hh using 1
    · ext k
      push_cast
      field_simp
      ring
    · norm_num
  have hr : Tendsto (fun k => weight p k / weight p (k + 1)) atTop (𝓝 1) := by
    have hh := hrbase.rpow_const (p := 1 / p) (Or.inl one_ne_zero)
    simp only [Real.one_rpow] at hh
    convert hh using 1
    ext k
    exact (Real.div_rpow (Nat.cast_nonneg k) (Nat.cast_nonneg (k+1)) (1 / p)).symm
  have hi : Tendsto (fun k => c / weight p (k + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hb.comp (tendsto_add_atTop_nat 1))
  have hh := ((h.comp (tendsto_add_atTop_nat 1)).sub (hr.mul h)).add hi
  simp only [one_mul, sub_self, zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk0 : weight p k ≠ 0 :=
    (Real.rpow_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)) _).ne'
  have hk1 : weight p (k + 1) ≠ 0 :=
    (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < (k+1 : ℕ)) _).ne'
  dsimp only [Function.comp_apply]
  rw [Finset.sum_range_succ]
  push_cast
  field_simp [hk0, hk1]
  ring

/-- A discrete tail bound for a nonnegative measurable function. The comparison
uses the first `ceil (f ω)` indicators, all of which equal one. -/
lemma integrable_of_integer_tails {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (hf : Measurable f) (hpos : ∀ ω, 0 ≤ f ω)
    (htail : (∑' k : ℕ, P {ω | (k : ℝ) < f ω}) < ∞) : Integrable f P := by
  classical
  let g : ℕ → Ω → ℝ≥0∞ := fun k => {ω | (k : ℝ) < f ω}.indicator (fun _ => 1)
  have hg (k : ℕ) : Measurable (g k) :=
    measurable_const.indicator (measurableSet_lt measurable_const hf)
  refine ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall hpos)).mpr ?_⟩
  calc
    (∫⁻ ω, ENNReal.ofReal (f ω) ∂P) ≤ ∫⁻ ω, ∑' k, g k ω ∂P := by
      apply lintegral_mono
      intro ω
      calc
        ENNReal.ofReal (f ω) ≤ (⌈f ω⌉₊ : ℝ≥0∞) := by
          exact_mod_cast (Nat.le_ceil (f ω))
        _ = ∑ k ∈ Finset.range ⌈f ω⌉₊, g k ω := by
          have heq (k : ℕ) (hk : k ∈ Finset.range ⌈f ω⌉₊) : g k ω = 1 := by
            apply Set.indicator_of_mem
            exact Nat.lt_ceil.mp (Finset.mem_range.mp hk)
          simp only [Finset.sum_congr rfl heq, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul, mul_one]
        _ ≤ ∑' k, g k ω := ENNReal.sum_le_tsum _
    _ = ∑' k : ℕ, P {ω | (k : ℝ) < f ω} := by
      rw [lintegral_tsum (fun k => (hg k).aemeasurable)]
      congr 1
      ext k
      exact lintegral_indicator_one (measurableSet_lt measurable_const hf)
    _ < ∞ := htail

end MZ

/-- Necessity of the p-th absolute moment from an arbitrary finite almost sure
limit of centered normalized partial sums. -/
theorem mz_finite_limit_moment :
    Specs.ProbabilityFoundations.Ch08.MZFiniteLimitMoment.finiteLimitMomentType := by
  intro Ω mΩ P hP X p c Z hX hI hd hp _hp2 hlim
  let Y : ℕ → Ω → ℝ := fun k ω => |X k ω| ^ p
  have hY (k : ℕ) : Measurable (Y k) := by dsimp [Y]; fun_prop
  let A : ℕ → Set Ω := fun k => {ω | ((k + 1 : ℕ) : ℝ) < Y k ω}
  have hA (k : ℕ) : MeasurableSet (A k) :=
    measurableSet_lt measurable_const (hY k)
  have hi : iIndepFun X P := (Ch02.independentRandomElements_iff_iIndepFun P X).mp hI
  have hYi : iIndepFun Y P :=
    hi.comp (fun _ => fun x : ℝ => |x| ^ p) (fun _ => by fun_prop)
  have hAi : Ch02.PairwiseIndependentEvents P A := by
    apply (Ch02.pairwiseIndependentEvents_iff_intersections P A hA).mpr
    intro i j hij
    exact (hYi.indepFun hij).measure_inter_preimage_eq_mul
      (Ioi ((i + 1 : ℕ) : ℝ)) (Ioi ((j + 1 : ℕ) : ℝ)) measurableSet_Ioi measurableSet_Ioi
  have hfinite : ∀ᵐ ω ∂P, {k : ℕ | ω ∈ A k}.Finite := by
    filter_upwards [hlim] with ω hω
    have hx := MZ.increment_tendsto_zero (fun k => X k ω) p c (Z ω) hp hω
    have habs : Tendsto (fun k => |X k ω / MZ.weight p (k + 1)|) atTop (𝓝 0) := by
      simpa only [abs_zero] using hx.abs
    have hnot : ∀ᶠ k in atTop, ω ∉ A k := by
      filter_upwards [habs.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with k hk
      have hb : 0 < MZ.weight p (k + 1) := Real.rpow_pos_of_pos (by positivity) _
      have hle : |X k ω| ≤ MZ.weight p (k + 1) := by
        rw [abs_div, abs_of_pos hb] at hk
        exact ((div_lt_one hb).mp hk).le
      have heq : |X k ω| ≤ MZ.weight p (k + 1) ↔ |X k ω| ^ p ≤ (k + 1 : ℕ) := by
        simpa only [MZ.weight,
          Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation.weight, one_div]
          using Real.le_rpow_inv_iff_of_pos (abs_nonneg (X k ω)) (Nat.cast_nonneg (k+1)) hp
      exact not_lt_of_ge (heq.mp hle)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hnot
    apply (Set.finite_Iio N).subset
    intro k hk
    change k < N
    by_contra h
    exact hN k (le_of_not_gt h) hk
  have hsum : (∑' k, P (A k)) < ∞ := by
    by_contra h
    have htop : (∑' k, P (A k)) = ∞ := top_unique (le_of_not_gt h)
    have hone := Ch02.second_borel_cantelli P A hA hAi htop
    have hzero := (Ch02.infinitelyOften_null_iff_ae_finite P A).mpr hfinite
    exact zero_ne_one (hzero.symm.trans hone)
  have hdY (k : ℕ) : IdentDistrib (Y k) (Y 0) P P :=
    (hd k).comp (show Measurable (fun x : ℝ => |x| ^ p) by fun_prop)
  have htail : (∑' k : ℕ, P {ω | ((k + 1 : ℕ) : ℝ) < Y 0 ω}) < ∞ := by
    convert hsum using 1
    congr 1
    ext k
    exact ((hdY k).measure_mem_eq measurableSet_Ioi).symm
  apply MZ.integrable_of_integer_tails P (Y 0) (hY 0)
    (fun ω => Real.rpow_nonneg (abs_nonneg _) _)
  rw [tsum_eq_zero_add' ENNReal.summable]
  exact ENNReal.add_lt_top.mpr ⟨measure_lt_top P _, htail⟩

end ProbabilityFoundations.Ch08
