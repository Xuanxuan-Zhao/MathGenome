import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.IndependenceInterfaces
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.ProbabilityBounds
import Mathlib.Probability.Independence.Integration
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch08.SummableVarianceSeries
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Tactic.Linarith

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityFoundations.Ch08

universe u

namespace VarianceSeries
variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- The first n variables, in their given order. -/
noncomputable def partialSum (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, X k ω

lemma partialSum_measurable (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) (n : ℕ) :
    Measurable (partialSum X n) :=
  Finset.measurable_sum _ (fun k _ => hX k)

lemma partialSum_memLp (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (h2 : ∀ k, MemLp (X k) 2 P) (n : ℕ) : MemLp (partialSum X n) 2 P :=
  memLp_finsetSum _ (fun k _ => h2 k)

/-- Information available before drawing variable n. -/
noncomputable def past (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) : Filtration ℕ mΩ where
  seq n := ⨆ k : ℕ, ⨆ (_ : k < n), (inferInstance : MeasurableSpace ℝ).comap (X k)
  mono' _ _ hnm := iSup₂_le fun k hk =>
    le_iSup_of_le k (le_iSup_of_le (lt_of_lt_of_le hk hnm) le_rfl)
  le' _ := iSup₂_le fun k _ => (hX k).comap_le

lemma partialSum_adapted (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) :
    StronglyAdapted (past X hX) (partialSum X) := by
  intro n
  apply Measurable.stronglyMeasurable
  apply Finset.measurable_sum
  intro k hk
  apply Measurable.mono (comap_measurable _ :
    Measurable[(inferInstance : MeasurableSpace ℝ).comap (X k)] (X k))
  · exact le_iSup_of_le k (le_iSup_of_le (Finset.mem_range.mp hk) le_rfl)
  · exact le_rfl

lemma partialSum_martingale (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) (hI : iIndepFun X P)
    (h2 : ∀ k, MemLp (X k) 2 P) (hmean : ∀ k, (∫ ω, X k ω ∂P) = 0) :
    Martingale (partialSum X) (past X hX) P := by
  apply martingale_of_condExp_sub_eq_zero_nat (partialSum_adapted X hX)
    (fun n => (partialSum_memLp P X h2 n).integrable (by norm_num))
  intro n
  have he : partialSum X (n + 1) - partialSum X n = X n := by
    ext ω
    simp [partialSum, Finset.sum_range_succ]
  rw [he]
  have hi : Indep ((inferInstance : MeasurableSpace ℝ).comap (X n)) (past X hX n) P := by
    have hd : Disjoint ({n} : Set ℕ) {k : ℕ | k < n} := by
      exact Set.disjoint_left.mpr (by intro k hk hn; subst k; exact (lt_irrefl n) hn)
    have h := indep_iSup_of_disjoint (fun k => (hX k).comap_le) hI.iIndep hd
    simpa [past] using h
  simpa only [hmean, Pi.zero_apply, Pi.zero_def] using
    (condExp_indep_eq (hX n).comap_le ((past X hX).le n)
      (comap_measurable (X n)).stronglyMeasurable hi)

lemma second_moment_sum (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) (hI : iIndepFun X P)
    (h2 : ∀ k, MemLp (X k) 2 P) (hmean : ∀ k, (∫ ω, X k ω ∂P) = 0)
    (s : Finset ℕ) :
    (∫ ω, (∑ k ∈ s, X k ω) ^ 2 ∂P) = ∑ k ∈ s, Ch01.realVariance P (X k) := by
  have hm : Measurable (fun ω => ∑ k ∈ s, X k ω) :=
    Finset.measurable_sum _ (fun k _ => hX k)
  have hz : (∫ ω, ∑ k ∈ s, X k ω ∂P) = 0 := by
    rw [integral_finsetSum _ (fun k _ => (h2 k).integrable (by norm_num))]
    simp [hmean]
  calc
    _ = variance (fun ω => ∑ k ∈ s, X k ω) P := by
      rw [variance_eq_integral hm.aemeasurable, hz]
      simp
    _ = ∑ k ∈ s, variance (X k) P := by
      have he : (fun ω => ∑ k ∈ s, X k ω) = ∑ k ∈ s, X k := by ext ω; simp
      rw [he]
      exact IndepFun.variance_sum (fun k _ => h2 k)
        (fun i _ j _ hij => hI.indepFun hij)
    _ = _ := Finset.sum_congr rfl fun k _ => variance_eq_integral (hX k).aemeasurable

lemma variance_nonneg (P : Measure Ω) (Y : Ω → ℝ) : 0 ≤ Ch01.realVariance P Y :=
  integral_nonneg (fun _ => sq_nonneg _)

lemma eLpNorm_one_nonneg (P : Measure Ω) (f : Ω → ℝ) (hf : Integrable f P)
    (hpos : ∀ ω, 0 ≤ f ω) : eLpNorm f 1 P = ENNReal.ofReal (∫ ω, f ω ∂P) := by
  rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hf]
  congr 1
  exact integral_congr_ae (ae_of_all _ (fun ω => Real.norm_of_nonneg (hpos ω)))


lemma second_moment_increment (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) (hI : iIndepFun X P)
    (h2 : ∀ k, MemLp (X k) 2 P) (hmean : ∀ k, (∫ ω, X k ω ∂P) = 0)
    {n m : ℕ} (hnm : n ≤ m) :
    (∫ ω, (partialSum X m ω - partialSum X n ω) ^ 2 ∂P) =
      (∑ k ∈ Finset.range m, Ch01.realVariance P (X k)) -
        ∑ k ∈ Finset.range n, Ch01.realVariance P (X k) := by
  have he (ω : Ω) : partialSum X m ω - partialSum X n ω =
      ∑ k ∈ Finset.Ico n m, X k ω := by
    exact (Finset.sum_Ico_eq_sub _ hnm).symm
  simp_rw [he]
  rw [second_moment_sum P X hX hI h2 hmean, Finset.sum_Ico_eq_sub _ hnm]

/-- The finite variance sum bounds the first moments of all partial sums. -/
lemma partialSum_l1_bound (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) (hI : iIndepFun X P)
    (h2 : ∀ k, MemLp (X k) 2 P) (hmean : ∀ k, (∫ ω, X k ω ∂P) = 0)
    (hs : Summable (fun k => Ch01.realVariance P (X k))) (n : ℕ) :
    eLpNorm (partialSum X n) 1 P ≤
      ENNReal.ofReal ((∑' k, Ch01.realVariance P (X k)) + 1) := by
  have hLp := partialSum_memLp P X h2 n
  rw [eLpNorm_one_eq_lintegral_enorm hLp.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm (hLp.integrable (by norm_num))]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∫ ω, ‖partialSum X n ω‖ ∂P) ≤ ∫ ω, (partialSum X n ω) ^ 2 + 1 ∂P := by
      apply integral_mono (hLp.integrable (by norm_num)).norm
        (hLp.integrable_sq.add (integrable_const 1))
      intro ω
      change ‖partialSum X n ω‖ ≤ (partialSum X n ω) ^ 2 + 1
      rw [Real.norm_eq_abs]
      nlinarith [sq_nonneg (|partialSum X n ω| - 1), sq_abs (partialSum X n ω)]
    _ = (∑ k ∈ Finset.range n, Ch01.realVariance P (X k)) + 1 := by
      rw [integral_add hLp.integrable_sq (integrable_const 1), integral_const]
      simp only [probReal_univ, one_smul]
      rw [show (∫ ω, (partialSum X n ω) ^ 2 ∂P) = _ from
        second_moment_sum P X hX hI h2 hmean (Finset.range n)]
    _ ≤ _ := add_le_add (hs.sum_le_tsum _ (fun k _ => variance_nonneg P (X k))) le_rfl

/-- Fatou passes the finite increment estimate to the same almost sure limit. -/
lemma limit_error_bound (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) (hI : iIndepFun X P)
    (h2 : ∀ k, MemLp (X k) 2 P) (hmean : ∀ k, (∫ ω, X k ω ∂P) = 0)
    (hs : Summable (fun k => Ch01.realVariance P (X k)))
    (Z : Ω → ℝ) (hZ : Measurable Z)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun m => partialSum X m ω) atTop (𝓝 (Z ω))) (n : ℕ) :
    eLpNorm (fun ω => (Z ω - partialSum X n ω) ^ 2) 1 P ≤
      ENNReal.ofReal ((∑' k, Ch01.realVariance P (X k)) -
        ∑ k ∈ Finset.range n, Ch01.realVariance P (X k)) := by
  apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop)
    (f := fun m ω => (partialSum X m ω - partialSum X n ω) ^ 2)
  · filter_upwards [eventually_ge_atTop n] with m hnm
    rw [eLpNorm_one_nonneg P (fun ω => (partialSum X m ω - partialSum X n ω) ^ 2)
      ((partialSum_memLp P X h2 m).sub (partialSum_memLp P X h2 n)).integrable_sq
      (fun _ => sq_nonneg _), second_moment_increment P X hX hI h2 hmean hnm]
    exact ENNReal.ofReal_le_ofReal (sub_le_sub_right
      (hs.sum_le_tsum _ (fun k _ => variance_nonneg P (X k))) _)
  · intro m
    exact (((partialSum_measurable X hX m).sub (partialSum_measurable X hX n)).pow_const 2).aestronglyMeasurable
  · exact ((hZ.sub (partialSum_measurable X hX n)).pow_const 2).aestronglyMeasurable
  · filter_upwards [hconv] with ω hω
    exact (hω.sub tendsto_const_nhds).pow 2

end VarianceSeries

/-- Independent centered real variables with summable variances have one
measurable L² limit for their ordered partial sums, almost surely and in L². -/
theorem summable_variance_series :
    Specs.ProbabilityFoundations.Ch08.SummableVarianceSeries.summableVarianceSeriesType := by
  intro Ω mΩ P hP X hX hI h2 hmean hs
  change Summable (fun k => Ch01.realVariance P (X k)) at hs
  have hind : iIndepFun X P := (Ch02.independentRandomElements_iff_iIndepFun P X).mp hI
  let T : ℝ := ∑' k, Ch01.realVariance P (X k)
  have hT : 0 ≤ T := tsum_nonneg (fun k => VarianceSeries.variance_nonneg P (X k))
  let R : ℝ≥0 := ⟨T + 1, by positivity⟩
  have hmart := VarianceSeries.partialSum_martingale P X hX hind h2 hmean
  have hbdd (n : ℕ) : eLpNorm (VarianceSeries.partialSum X n) 1 P ≤ R := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact VarianceSeries.partialSum_l1_bound P X hX hind h2 hmean hs n
  let Z : Ω → ℝ := (VarianceSeries.past X hX).limitProcess (VarianceSeries.partialSum X) P
  have hZ : Measurable Z := (VarianceSeries.past X hX).stronglyMeasurable_limit_process'.measurable
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => VarianceSeries.partialSum X n ω) atTop (𝓝 (Z ω)) :=
    hmart.submartingale.ae_tendsto_limitProcess hbdd
  have herr := VarianceSeries.limit_error_bound P X hX hind h2 hmean hs Z hZ hconv
  have hZsq : Integrable (fun ω => Z ω ^ 2) P := by
    have hb0 := herr 0
    simp only [VarianceSeries.partialSum, Finset.range_zero, Finset.sum_empty, sub_zero] at hb0
    exact memLp_one_iff_integrable.mp (hb0.trans_lt ENNReal.ofReal_lt_top)
  have hZ2 : MemLp Z 2 P := (memLp_two_iff_integrable_sq hZ.aestronglyMeasurable).mpr hZsq
  refine ⟨Z, hZ, hZ2, hconv, ?_⟩
  have herror (n : ℕ) : (∫ ω, |VarianceSeries.partialSum X n ω - Z ω| ^ 2 ∂P) ≤
      T - ∑ k ∈ Finset.range n, Ch01.realVariance P (X k) := by
    have hb := herr n
    rw [VarianceSeries.eLpNorm_one_nonneg P (fun ω => (Z ω - VarianceSeries.partialSum X n ω) ^ 2)
      (hZ2.sub (VarianceSeries.partialSum_memLp P X h2 n)).integrable_sq
      (fun _ => sq_nonneg _)] at hb
    have hn : 0 ≤ (∫ ω, (Z ω - VarianceSeries.partialSum X n ω) ^ 2 ∂P) :=
      integral_nonneg (fun ω => sq_nonneg _)
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rw [ENNReal.toReal_ofReal hn, ENNReal.toReal_ofReal
      (sub_nonneg.mpr (hs.sum_le_tsum _ (fun k _ => VarianceSeries.variance_nonneg P (X k))))] at ht
    simpa only [sq_abs, sub_sq_comm] using ht
  have htail : Tendsto (fun n => T - ∑ k ∈ Finset.range n, Ch01.realVariance P (X k))
      atTop (𝓝 0) := by
    simpa only [T, sub_self] using
      (tendsto_const_nhds (x := T) (f := atTop)).sub hs.hasSum.tendsto_sum_nat
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
    (fun n => integral_nonneg (fun ω => sq_nonneg _)) herror

end ProbabilityFoundations.Ch08
