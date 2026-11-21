import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch08.SummableVarianceSeries
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch08.KroneckerLemma
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch08.KolmogorovVarianceCriterion

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace ProbabilityFoundations.Ch08

/-- Kolmogorov's variance criterion for arbitrary positive nondecreasing
weights diverging to infinity. No identical distribution is required. -/
theorem kolmogorov_variance_criterion :
    Specs.ProbabilityFoundations.Ch08.KolmogorovVarianceCriterion.varianceCriterionType := by
  intro Ω mΩ P hP X b hX hI h2 hb hm ht hs
  change Summable (fun k => Ch01.realVariance P (X k) / b (k + 1) ^ 2) at hs
  let Y : ℕ → Ω → ℝ := fun k ω => (X k ω - ∫ t, X k t ∂P) / b (k + 1)
  have hY (k : ℕ) : Measurable (Y k) :=
    ((hX k).sub measurable_const).div_const _
  have hY2 (k : ℕ) : MemLp (Y k) 2 P :=
    by
      simpa only [Y, div_eq_mul_inv, Pi.sub_apply] using
        ((h2 k).sub (memLp_const (∫ t, X k t ∂P))).mul_const (b (k + 1))⁻¹
  have hYmean (k : ℕ) : (∫ ω, Y k ω ∂P) = 0 := by
    dsimp [Y]
    rw [integral_div, integral_sub ((h2 k).integrable (by norm_num)) (integrable_const _)]
    simp
  have hYI : Ch02.IndependentRandomElements P Y := by
    apply (Ch02.independentRandomElements_iff_iIndepFun P Y).mpr
    exact ((Ch02.independentRandomElements_iff_iIndepFun P X).mp hI).comp
      (fun k x => (x - ∫ t, X k t ∂P) / b (k + 1))
      (fun k => (measurable_id.sub measurable_const).div_const _)
  have hvar (k : ℕ) : Ch01.realVariance P (Y k) =
      Ch01.realVariance P (X k) / b (k + 1) ^ 2 := by
    unfold Ch01.realVariance Ch01.realExpectation
    rw [hYmean]
    simp only [sub_zero]
    simp_rw [Y, div_pow]
    rw [integral_div]
  have hYs : Summable (fun k => Ch01.realVariance P (Y k)) := by
    simpa only [hvar] using hs
  obtain ⟨Z, _, _, hconv, _⟩ := summable_variance_series P Y hY hYI hY2 hYmean hYs
  filter_upwards [hconv] with ω hω
  have hk := kroneckerLemma (fun n => X (n - 1) ω - ∫ t, X (n - 1) t ∂P)
    b hb hm ht
  apply hk
  exact ⟨Z ω, by simpa [Y] using hω⟩

/-- The usual normalized strong law under summability of Var(X_k)/k². -/
theorem normalized_variance_strong_law :
    Specs.ProbabilityFoundations.Ch08.KolmogorovVarianceCriterion.normalizedVarianceStrongLawType := by
  intro Ω mΩ P hP X hX hI h2 hs
  have h := kolmogorov_variance_criterion P X (fun n => (n : ℝ)) hX hI h2
    (fun n hn => by exact_mod_cast hn)
    (fun i _ j _ hij => Nat.cast_le.mpr hij) tendsto_natCast_atTop_atTop hs
  filter_upwards [h] with ω hω
  convert hω using 1
  funext n
  rw [integral_finsetSum _ (fun k _ => (h2 k).integrable (by norm_num)),
    Finset.sum_sub_distrib]
  simp [div_eq_mul_inv, mul_comm]

end ProbabilityFoundations.Ch08
