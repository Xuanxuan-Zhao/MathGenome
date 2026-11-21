import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch08.EtemadiFiniteLimitConverse
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch08.EtemadiStrongLaw
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.PairwiseBorelCantelliRatio
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The converse direction of Theorem 8.3 (`thm:etemadi`).
Convergent averages imply vanishing normalized increments. Pairwise
Borel–Cantelli then makes the integer tail probabilities summable.
Tonelli applied to integer-level indicators gives the finite first
absolute moment. The forward law and uniqueness of limits identify Z.
All events and measures use the original sigma algebra. -/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace ProbabilityFoundations.Ch08

universe u

/-- The discrete tail criterion, with no moment assumption. -/
lemma integrable_abs_of_tail_tsum_ne_top {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ) (hf : Measurable f)
    (htail : (∑' n : ℕ, P {ω | (n + 1 : ℝ) ≤ |f ω|}) ≠ ∞) :
    Integrable (fun ω => |f ω|) P := by
  classical
  have hfabs : Measurable (fun ω => |f ω|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  let g : ℕ → Ω → ℝ≥0∞ := fun n =>
    {ω | (n + 1 : ℝ) ≤ |f ω|}.indicator (fun _ => 1)
  have hg (n : ℕ) : Measurable (g n) :=
    measurable_const.indicator (measurableSet_le measurable_const hfabs)
  have hbound (ω : Ω) : ENNReal.ofReal |f ω| ≤ 1 + ∑' n, g n ω := by
    have hsum : ∑ n ∈ Finset.range ⌊|f ω|⌋₊, g n ω = (⌊|f ω|⌋₊ : ℝ≥0∞) := by
      have heq (n : ℕ) (hn : n ∈ Finset.range ⌊|f ω|⌋₊) : g n ω = 1 := by
        apply Set.indicator_of_mem
        exact (show (n + 1 : ℝ) ≤ (⌊|f ω|⌋₊ : ℝ) by
          exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hn)).trans
            (Nat.floor_le (abs_nonneg _))
      simp only [Finset.sum_congr rfl heq, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one]
    calc
      ENNReal.ofReal |f ω| ≤ ENNReal.ofReal ((⌊|f ω|⌋₊ : ℝ) + 1) :=
        ENNReal.ofReal_le_ofReal (Nat.lt_floor_add_one _).le
      _ = 1 + (⌊|f ω|⌋₊ : ℝ≥0∞) := by
        rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one]
        simp [add_comm]
      _ ≤ 1 + ∑' n, g n ω := by
        rw [← hsum]
        exact add_le_add le_rfl (ENNReal.sum_le_tsum _)
  have hb : (∫⁻ ω, ENNReal.ofReal |f ω| ∂P) ≤
      1 + ∑' n : ℕ, P {ω | (n + 1 : ℝ) ≤ |f ω|} := by
    calc
      _ ≤ ∫⁻ ω, 1 + ∑' n, g n ω ∂P := lintegral_mono hbound
      _ = _ := by
        rw [lintegral_add_left measurable_const, lintegral_tsum (fun n => (hg n).aemeasurable)]
        simp [g, lintegral_indicator, measurableSet_le measurable_const hfabs]
  refine ⟨hfabs.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun ω => abs_nonneg (f ω)))]
  exact lt_of_le_of_lt hb (ENNReal.add_lt_top.mpr ⟨by simp, lt_top_iff_ne_top.mpr htail⟩)

/-- Convergence of averages to any finite real number forces the normalized
individual terms to tend to zero. -/
lemma normalized_terms_tendsto_zero (a : ℕ → ℝ) (z : ℝ)
    (h : Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, a k) / (n : ℝ))
      atTop (𝓝 z)) :
    Tendsto (fun n : ℕ => a n / (n + 1 : ℝ)) atTop (𝓝 0) := by
  have hnext := h.comp (tendsto_add_atTop_nat 1)
  have hmul := (tendsto_natCast_div_add_atTop (1 : ℝ)).mul h
  have hsub := hnext.sub hmul
  simp only [one_mul, sub_self] at hsub
  apply hsub.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, Finset.sum_range_succ]
  field_simp
  ring

/-- Etemadi's converse, for a finite random limit and pairwise independence.
The unused zeroth coordinate is excluded from all hypotheses and sums. -/
theorem etemadi_finite_limit_converse {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ k : ℕ, Measurable (X (k + 1)))
    (hindep : Ch02.PairwiseIndependentRandomElements P (fun k : ℕ => X (k + 1)))
    (hident : ∀ k : ℕ, ProbabilityTheory.IdentDistrib (X (k + 1)) (X 1) P P)
    (Z : Ω → ℝ) (_hZ : Measurable Z)
    (hlim : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, X k ω) / (n : ℝ))
      atTop (𝓝 (Z ω))) :
    Integrable (fun ω => |X 1 ω|) P ∧
      ∀ᵐ ω ∂P, Z ω = ∫ ω, X 1 ω ∂P := by
  classical
  have hsum (n : ℕ) (ω : Ω) :
      (∑ k ∈ Finset.Icc 1 n, X k ω) = ∑ k ∈ Finset.range n, X (k + 1) ω := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, Nat.add_comm]
  have hterms : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => X (n + 1) ω / (n + 1 : ℝ)) atTop (𝓝 0) := by
    filter_upwards [hlim] with ω hω
    apply normalized_terms_tendsto_zero (fun k => X (k + 1) ω) (Z ω)
    simpa only [hsum] using hω
  let A : ℕ → Set Ω := fun n => {ω | (n + 1 : ℝ) ≤ |X (n + 1) ω|}
  have hA (n : ℕ) : MeasurableSet (A n) := by
    have hm : Measurable (fun ω => |X (n + 1) ω|) := by
      simpa only [Real.norm_eq_abs] using (hX n).norm
    exact measurableSet_le measurable_const hm
  have hfinite : ∀ᵐ ω ∂P, {n : ℕ | ω ∈ A n}.Finite := by
    filter_upwards [hterms] with ω hω
    have hsmall : ∀ᶠ n : ℕ in atTop, |X (n + 1) ω / (n + 1 : ℝ)| < 1 := by
      simpa only [Real.norm_eq_abs, norm_zero] using
        hω.norm.eventually (gt_mem_nhds (show ‖(0 : ℝ)‖ < 1 by norm_num))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
    apply (Set.finite_Iio N).subset
    intro n hn
    change n < N
    by_contra hnot
    have hlt := hN n (le_of_not_gt hnot)
    have hpos : (0 : ℝ) < n + 1 := by positivity
    rw [abs_div, abs_of_pos hpos, div_lt_iff₀ hpos, one_mul] at hlt
    exact (not_lt_of_ge hn) hlt
  have hi := (Ch02.pairwiseIndependentRandomElements_iff P
    (fun k : ℕ => X (k + 1))).mp hindep
  have hindA : Ch02.PairwiseIndependentEvents P A := by
    apply (Ch02.pairwiseIndependentEvents_iff_intersections P A hA).mpr
    intro i j hij
    have hmi : MeasurableSet {x : ℝ | (i + 1 : ℝ) ≤ |x|} := by
      simpa only [Real.norm_eq_abs] using
        (measurableSet_le measurable_const measurable_id.norm :
          MeasurableSet {x : ℝ | (i + 1 : ℝ) ≤ ‖x‖})
    have hmj : MeasurableSet {x : ℝ | (j + 1 : ℝ) ≤ |x|} := by
      simpa only [Real.norm_eq_abs] using
        (measurableSet_le measurable_const measurable_id.norm :
          MeasurableSet {x : ℝ | (j + 1 : ℝ) ≤ ‖x‖})
    exact (hi hij).measure_inter_preimage_eq_mul _ _ hmi hmj
  have htailA : (∑' n, P (A n)) ≠ ∞ := by
    intro htop
    have hone := Ch02.second_borel_cantelli P A hA hindA htop
    have hzero := (Ch02.infinitelyOften_null_iff_ae_finite P A).mpr hfinite
    exact zero_ne_one (hzero.symm.trans hone)
  have htail : (∑' n : ℕ, P {ω | (n + 1 : ℝ) ≤ |X 1 ω|}) ≠ ∞ := by
    convert htailA using 2
    funext n
    exact ((hident n).measure_mem_eq (s := {x : ℝ | (n + 1 : ℝ) ≤ |x|}) (by
      simpa only [Real.norm_eq_abs] using
        (measurableSet_le measurable_const measurable_id.norm :
          MeasurableSet {x : ℝ | (n + 1 : ℝ) ≤ ‖x‖}))).symm
  have hmoment := integrable_abs_of_tail_tsum_ne_top P (X 1) (hX 0) htail
  refine ⟨hmoment, ?_⟩
  have hmean := etemadi_strong_law P X hX hindep hident hmoment
  filter_upwards [hlim, hmean] with ω hz hm
  exact tendsto_nhds_unique hz hm

end ProbabilityFoundations.Ch08
